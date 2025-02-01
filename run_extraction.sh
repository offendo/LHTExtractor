#!/bin/bash

LEAN_VERSION="v4.14.0-rc1"
JOBS=32
LHT_OUTPUT_DIR=$(pwd)/LHTExtractions
LEAN_OUTPUT_DIR=$(pwd)/Theorems

# Step 1. clone mathlib
echo "Cloning Mathlib4 for Lean version $LEAN_VERSION"
git clone --depth 1 --branch $LEAN_VERSION git@github.com:leanprover-community/mathlib4.git

# Step 2. run LHT in parallel
# Make all the directories needed first
cd mathlib4
find Mathlib -iname "*.lean" -exec dirname {} \; \
        | parallel --bar \
            --jobs $JOBS \
            mkdir -p $LHT_OUTPUT_DIR/{}

# Now run the LHT tool
find Mathlib/ -iname "*.lean" \
        | parallel --bar \
            --jobs $JOBS \
            lake env ../LeanHyperTree/.lake/build/bin/leanhypertree -i {} -o $LHT_OUTPUT_DIR/{.}.json
cd ..

# Step 3. run python extraction tool
python src/extract/extract.py \
        --jobs $JOBS \
        --extraction_dir $LHT_OUTPUT_DIR \
        --output_dir $LEAN_OUTPUT_DIR

# Step 4. run REPL on all the lean files
find $LEAN_OUTPUT_DIR "*.lean" \
        | parallel --bar \
             --jobs $JOBS \
             " echo '{\"path\": \"{}\", \"allTactics\": true }' | lake env repl > {.}.json "


