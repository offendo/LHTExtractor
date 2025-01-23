import pandas as pd
import json
import re
import sys
from tqdm import tqdm
from argparse import ArgumentParser
from multiprocessing import Pool

from dataclasses import dataclass
from pathlib import Path

@dataclass
class Namespace:
    name: str
    start: int
    end: int | None = None

    @classmethod
    def from_nodes(cls, start_node: dict, end_node: dict | None = None):
        name = start_node['node']['info']['command']['stx']['stx']
        start = start_node['node']['info']['command']['stx']['start']['line']
        if end_node:
            end = end_node['node']['info']['command']['stx']['start']['line']
        else:
            end = sys.maxsize
        return cls(name, start, end)

class Section(Namespace):
    ...

@dataclass
class TracedFile:
    module: str
    imports: list[str]
    imported_modules: list[str]
    info_tree: list[dict]
    decl_data: list[dict]
    tactic_theorems: list[dict]
    namespaces: list[Namespace]

    @classmethod
    def from_file(cls, file: Path):
        with open(file, 'r') as f:
            data = json.load(f)

        thms = [t for t in data['declData'] if t['declKind'] == 'theorem']
        tactic_theorems = [t for t in thms if re.search(r":=\s*by", t['source']) is not None]

        return cls(
            module=data['moduleName'],
            imports=data['imports'],
            imported_modules=data['modules'],
            info_tree=data['infoJson'],
            decl_data=data['declData'],
            tactic_theorems=tactic_theorems,
            namespaces=TracedFile.get_namespaces(data['infoJson'])
        )

    @staticmethod
    def get_namespaces(info_tree: list[dict]):
        # For the newly declared namespaces, they are closeable, so we have to find the appropriate `end ...` indicator.
        new_namespaces = {
            node['node']['info']['command']['stx']['stx'].replace('namespace', '', 1).strip().split('.')[-1]: node 
            for node in info_tree 
            if node['node']['info']['command']['elaborator'] == 'Lean.Elab.Command.elabNamespace'
        }
        ends = {
            node['node']['info']['command']['stx']['stx'].replace('end', '', 1).strip().split('.')[-1]: node 
            for node in info_tree 
            if node['node']['info']['command']['elaborator'] == 'Lean.Elab.Command.elabEnd'
            and node['node']['info']['command']['stx']['stx'] != 'end' # don't include things that are just 'end'
        }
        namespaces = [Namespace.from_nodes(node, ends[name]) for name, node in new_namespaces.items() if name in ends]

        # Get a list of the ones that are just `open ...`
        opens_unfiltered = [Namespace.from_nodes(node) for node in info_tree if node['node']['info']['command']['elaborator'] == 'Lean.Elab.Command.elabOpen']

        # Now, loop through the namespace...end and section...end blocks, and see if this open falls inside one of them.
        # If it does, update the end index of the "open" to the end index of the block
        section_starts = {
            node['node']['info']['command']['stx']['stx'].replace('section', '', 1).strip().split('.')[-1]: node 
            for node in info_tree if node['node']['info']['command']['elaborator'] == 'Lean.Elab.Command.elabSection'
            and node['node']['info']['command']['stx']['stx'] != 'section' # don't include things that are just 'section'
        }
        sections = [Section.from_nodes(node, ends[name]) for name, node in section_starts.items() if name and not name.startswith('--') and name in ends]
        opens = []
        for op in opens_unfiltered:
            new_open = op
            block_size = sys.maxsize
            for sec in sections + namespaces:
                if (sec.start < op.start < sec.end) and (sec.end - sec.start < block_size):
                    new_open = Namespace(op.name, op.start, sec.end)
            opens.append(new_open)

        # Return a list of 
        return opens + namespaces

    
    def get_open_namespaces(self, thm: dict):
        (sline, scol), (eline, ecol) = thm['sourceRange']
        opens = []
        for ns in self.namespaces:
            if ns.start < sline < ns.end:
                opens.append(ns.name)
        return opens

    def format_theorems(self):
        # imports = '\n'.join([f'import {imp}' for imp in file.imports])
        imports = f"import {self.module}"
        theorems = {}
        for thm in self.tactic_theorems:
            src = thm['source']
            proof = re.split(r":=\s*by", src, maxsplit=1)[1]
    
            # Get the open namespaces, and replace any declarations ('namespace') with an 'open')
            open_namespaces = '\n'.join([ns.replace('namespace', 'open') for ns in self.get_open_namespaces(thm)])
            anonymous = re.split(r"(?:}\s+|[^,]\s+)", thm['signature'], maxsplit=1)[1]
            statement = f"theorem generated {anonymous}"
            theorems[thm['declName']] = f"{imports}\n\n{open_namespaces}\n\n{statement} := by\n{proof}"
        return theorems


if __name__ == "__main__":
    parser = ArgumentParser("extract")

    parser.add_argument("--extraction_dir", type=str, required=True, help="path to results from LeanHyperTree")
    parser.add_argument("--output_dir", type=str, required=True, help="output directory")
    parser.add_argument("--jobs", "-j", type=int, default=1, help="number of jobs")
    
    args = parser.parse_args()

    Path(args.output_dir).mkdir(exist_ok=True, parents=True)

    # Fodder for multiprocessing pool
    def extract_file(path: Path):
        trace = TracedFile.from_file(path)
        for name, thm in trace.format_theorems().items():
            output_name = Path(args.output_dir, path.with_name(f"{path.stem}-{name}.lean").relative_to(args.extraction_dir))
            Path(output_name).parent.mkdir(parents=True, exist_ok=True)
            with open(output_name, 'w') as f:
                f.write(thm)

    pbar = tqdm(Path(args.extraction_dir).rglob('*.json'))
    with Pool(args.jobs) as pool:
        pool.map(extract_file, pbar)
