import pandas as pd
import json
import re
import sys
import time
from collections import deque
from tqdm import tqdm
from argparse import ArgumentParser
from multiprocessing import Pool

from dataclasses import dataclass
from pathlib import Path

@dataclass
class Namespace:
    kind: str
    name: str
    start: int
    end: int | None = None

    @classmethod
    def from_nodes(cls, start_node: dict, end_node: dict | None = None):
        # Remove 'scoped', which might cause problems but idk
        name = start_node['node']['info']['command']['stx']['stx'].replace('scoped', '')
        start = start_node['node']['info']['command']['stx']['start']['line']
        if end_node:
            end = end_node['node']['info']['command']['stx']['start']['line']
        else:
            end = sys.maxsize
        return cls(name, start, end)

    def __iter__(self):
        yield from (self.kind, self.name, self.start)

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
        namespaces = []
        sections = []
        stack = deque([])

        for node in info_tree:
            command = node['node']['info']['command']
            # Step one, get rid of the comments
            stx = command['stx']['stx'].split('--')[0].split('/-')[0]
            match command['elaborator']:
                # namespaces must have an associated name, so you can't just have `namespace...end`
                # However, you can have `namespace Apple.Banana.Cherry...end Cherry...end Banana...end Apple`
                # which essentially defines three nested namespaces at once. You can also close multiple at 
                # once, e.g., namespace Apple.Banana.Cherry...end Cherry...end Apple.Banana.
                case 'Lean.Elab.Command.elabNamespace':
                    names = stx.replace('namespace', '', 1).strip().split('.')
                    start = command['stx']['start']['line']
                    for i, n in enumerate(names):
                        stack.append(("namespace", n, start + (i / 100))) # add 1/100 to keep the hierarchy
                case 'Lean.Elab.Command.elabSection' | 'Lean.Elab.Command.elabNonComputableSection':
                    names = stx.replace('section', '', 1).replace('noncomputable', '', 1).strip().split('.')
                    start = command['stx']['start']['line']
                    # Sections sometimes have no name. Just push it on the stack anyway
                    if len(names) == 0:
                        stack.append(("", start))
                    for n in names:
                        stack.append(("noncomputable section" if 'noncomputable' in stx else 'section', n, start))
                case 'Lean.Elab.Command.elabOpen':
                    names = re.split(r"[\. ]", stx.replace('open', '', 1).replace('scoped', '', 1).strip())
                    start = command['stx']['start']['line']
                    for i, n in enumerate(names):
                        if 'scoped' in stx:
                            stack.append(("open scoped", n, start + (i / 100))) # add 1/100 to keep the hierarchy
                        else:
                            stack.append(("open", n, start + (i / 100))) # add 1/100 to keep the hierarchy
                case 'Lean.Elab.Command.elabEnd':
                    # Finally, we've come to the end of a block. Now we need to keep popping from the stack until we reach the corresponding open.
                    names = stx.replace('end', '', 1).strip().split('.')
                    end = command['stx']['start']['line']
                    if len(names) == 0:
                        names = [""]

                    # Loop through the names in reverse, checking to see if we've found a match at each pop
                    counter = 0
                    for n in names[::-1]:
                        while stack:
                            kind, name, start = stack.pop()
                            if kind == 'open':
                                namespaces.append(Namespace(kind, name, start, end))
                                counter += 1
                            elif kind == 'open scoped':
                                namespaces.append(Namespace(kind, name, start, end))
                                counter += 1
                            elif kind == 'section' or kind == 'noncomputable section':
                                # We've found the opener for this name, can continue with the loop
                                if name == n:
                                    sections.append(Section(kind, name, start, end))
                                    break
                                else:
                                    raise Exception(f"Found malformed block at: {kind}\t{name}!={n}\t{start}\t{end}\n\n{stack}")
                            elif kind == 'namespace':
                                # We've found the opener for this name, can continue with the loop
                                if name == n:
                                    namespaces.append(Namespace(kind, name, start, end))
                                    break
                                else:
                                    # Normally this would be impossible, but turns out some sections can be started as a sub-block of another. E.g., "... in section...end"
                                    # So it's probably the "end" block of one of those sections. For now, just put the namespace back on the stack and keep going
                                    stack.append((kind, name, start))
                                    for i in range(counter):
                                        stack.append(tuple(namespaces.pop()))
                                    break
        # Add on all the remaining unclosed namespaces/opens
        for kind,name,start in stack:
            if kind in {'open', 'open scoped', 'namespace'}:
                namespaces.append(Namespace(kind, name, start, sys.maxsize))
        return sorted(namespaces, key=lambda x: x.start)

    
    def get_open_namespaces(self, thm: dict):
        (sline, scol), (eline, ecol) = thm['sourceRange']
        opens = []
        for ns in sorted(self.namespaces, key=lambda x: x.start):
            if ns.start < sline < ns.end:
                opens.append(f"{ns.kind} {ns.name}")
        return list(opens)

    def format_theorems(self):
        imports = '\n'.join([f'import {imp}' for imp in self.imports])
        imports += f"\nimport {self.module}"
        theorems = {}
        for thm in self.tactic_theorems:
            # Get the open namespaces, and replace any declarations ('namespace') with an 'open')
            open_namespaces = '\n'.join([ns.replace('namespace', 'open') for ns in self.get_open_namespaces(thm)])

            src = thm['source']
            signature = thm['signature']
            proof = re.split(r":=\s*by", src, maxsplit=1)[1]
            anonymous = re.split(r"(?:}\s+|[^,]\s+)", signature,  maxsplit=1)[1]
            statement = f"theorem thm {anonymous}"
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
            clean_name = name.replace("'", "_p")
            clean_path = path.stem.replace("'", "_p")
            output_name = Path(args.output_dir, path.with_name(f"{clean_path}-{clean_name}.lean").relative_to(args.extraction_dir))
            Path(output_name).parent.mkdir(parents=True, exist_ok=True)
            with open(output_name, 'w') as f:
                f.write(thm)

    pbar = tqdm(list(Path(args.extraction_dir).rglob('*.json')))
    with Pool(args.jobs) as pool:
        pool.map(extract_file, pbar)
