#!/bin/bash

# This runs bab.debug in fuzz mode on each seed, to check whether the seed
# passes or fails. Before starting, make sure bab.debug is built (run "make debug")
# and make sure the Isabelle oracle is built (see isabelle/README.md).

# Arrays to store results
declare -a succeeded=()
declare -a failed=()

# Process each seed file
for file in seeds/*.b; do

    # Run bab.debug fuzz with the file, with hard-coded max-status for now
    ../build/bab.debug fuzz -r dummy-package --main-file $file --oracle ../isabelle/export/Babylon.CodeExport/code/export1/Main --max-status 3

    # Check exit status
    if [ $? -eq 0 ]; then
        succeeded+=("$file")
    else
        failed+=("$file")
    fi
done

# Print report
echo ""
echo "========================================"
echo "EXECUTION REPORT"
echo "========================================"
echo ""

echo "SUCCEEDED (${#succeeded[@]} files):"
if [ ${#succeeded[@]} -eq 0 ]; then
    echo "  (none)"
else
    for file in "${succeeded[@]}"; do
        echo "  ✓ $file"
    done
fi

echo ""
echo "FAILED (${#failed[@]} files):"
if [ ${#failed[@]} -eq 0 ]; then
    echo "  (none)"
else
    for file in "${failed[@]}"; do
        echo "  ✗ $file"
    done
fi

echo ""
echo "========================================"
echo "Total: $((${#succeeded[@]} + ${#failed[@]})) files (${#succeeded[@]} succeeded, ${#failed[@]} failed)"
echo "========================================"
