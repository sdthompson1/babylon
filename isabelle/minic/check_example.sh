#!/bin/bash

# C-level validation of the hand-written MiniC examples (DESIGN.md, section 11).
#
# For each example program NAME (default: all of them):
#   1. Main --minic NAME prints the program to NAME.c and writes the stdout
#      that the MiniC interpreter computes for it to NAME.expected;
#   2. NAME.c is compiled with gcc -std=c99 -Wall -Wextra -pedantic -Werror
#      (and also with -std=c11 and -std=c17), at -O0 and -O2;
#   3. it is linked against the C support code, run, and its stdout and exit
#      status are compared with the interpreter's.
#
# The support code: "example" is linked against test/test-support-0.1/src/Test.c
# (whose alloc_array/free_array are void functions that always succeed);
# "example_array" is linked against packages/coretypes/src/Array.c (whose
# alloc_array returns a bool) plus Test.c with its own alloc_*_array and
# free_*_array renamed away, because both files define those symbols.
#
# Usage, from the root of the repository, after building the Isabelle
# compiler (see CLAUDE.md / isabelle/README.md):
#
#   ./isabelle/minic/check_example.sh [NAME ...]
#
# Exit status 0 if every check passes.

set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
MAIN="$ROOT/isabelle/export/Babylon.CodeExport/code/export1/Main"
TEST_C="$ROOT/test/test-support-0.1/src/Test.c"
ARRAY_C="$ROOT/packages/coretypes/src/Array.c"
WORK="${TMPDIR:-/tmp}/minic-check"
CC="${CC:-gcc}"

if ! [ -x "$MAIN" ]; then
    echo "$MAIN not found; build the Isabelle compiler first."
    exit 1
fi

mkdir -p "$WORK"
NAMES=("$@")
if [ ${#NAMES[@]} -eq 0 ]; then
    NAMES=(example example_array)
fi

FAILED=0

fail() {
    echo "FAILED: $*"
    FAILED=1
}

for NAME in "${NAMES[@]}"; do
    C="$WORK/$NAME.c"
    EXPECTED="$WORK/$NAME.expected"
    rm -f "$C" "$EXPECTED"
    if ! "$MAIN" --minic "$NAME" "$C" "$EXPECTED"; then
        fail "$NAME: Main --minic"
        continue
    fi

    # The support objects (compiled without -Werror: they are not ours).
    SUPPORT=()
    case $NAME in
        example_array)
            $CC -std=c99 -O2 -c -o "$WORK/Array.o" "$ARRAY_C" || { fail "$NAME: compiling Array.c"; continue; }
            RENAME=()
            for F in alloc_array free_array alloc_2d_array free_2d_array alloc_3d_array free_3d_array; do
                RENAME+=("-D$F=test_$F")
            done
            $CC -std=c99 -O2 "${RENAME[@]}" -c -o "$WORK/Test_renamed.o" "$TEST_C" \
                || { fail "$NAME: compiling Test.c"; continue; }
            SUPPORT=("$WORK/Array.o" "$WORK/Test_renamed.o")
            ;;
        *)
            $CC -std=c99 -O2 -c -o "$WORK/Test.o" "$TEST_C" || { fail "$NAME: compiling Test.c"; continue; }
            SUPPORT=("$WORK/Test.o")
            ;;
    esac

    for STD in c99 c11 c17; do
        for OPT in -O0 -O2; do
            EXE="$WORK/$NAME-$STD$OPT"
            if ! $CC -std=$STD $OPT -Wall -Wextra -pedantic -Werror -o "$EXE" "$C" "${SUPPORT[@]}"; then
                fail "$NAME: gcc -std=$STD $OPT"
                continue
            fi
            "$EXE" > "$EXE.out"
            STATUS=$?
            if [ $STATUS -ne 0 ]; then
                fail "$NAME ($STD $OPT): exit status $STATUS"
            fi
            if ! cmp -s "$EXE.out" "$EXPECTED"; then
                fail "$NAME ($STD $OPT): output differs from the interpreter's"
                diff "$EXPECTED" "$EXE.out"
            fi
        done
    done
    echo "$NAME: done (see $WORK)"
done

if [ $FAILED -eq 0 ]; then
    echo "All checks passed."
fi
exit $FAILED
