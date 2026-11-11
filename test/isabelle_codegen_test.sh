#!/bin/bash

# End-to-end test of the Isabelle compiler's code generator
# (isabelle/minic/DESIGN.md, section 11).
#
# For every test program in test/cases/codegen (single .b files, and the
# multi.txt directories with Main.b as the root, exactly as
# isabelle_test.sh enumerates them), and for each way of printing the
# MiniC MS_Uninit statement (memset and omit, see DESIGN.md 11.2):
#
#   1. the Isabelle compiler (Main -o) compiles the program, together with
#      test/test-support-0.1/src/Test.b, to a single .c file;
#   2. the .c file is compiled with gcc -std=c99 -Wall -Wextra -pedantic
#      -Werror plus the -Wno-... flags of test/config/babylon/babylon.toml
#      (which the C compiler's own tests need too) and the three unused-name
#      warnings disabled (see NOWARN below), at -O0 and at -O2, and
#      linked against test/test-support-0.1/src/Test.c; in the omit mode
#      gcc's uninitialised-use warnings are disabled (a variant's unused
#      payload bytes are copied without ever being written, which is what
#      the memset mode exists to avoid);
#   3. the executable is run; it must exit with status 0, print nothing
#      on stderr, and print on stdout exactly the test's .output file with
#      the // comments stripped (as run_test in test/run_tests.sh does).
#
# Usage, from the root of the repository, after building the Isabelle
# compiler (see CLAUDE.md / isabelle/README.md):
#
#   ./test/isabelle_codegen_test.sh [FILTER]
#
# FILTER restricts the run to the tests whose path contains it. The files
# of each test are left in $TMPDIR/isabelle-codegen-test (default
# /tmp/isabelle-codegen-test) for inspection. Exit status 0 if every test
# passes.

set -u

MAIN="isabelle/export/Babylon.CodeExport/code/export1/Main"
CASES_DIR="test/cases/codegen"
TEST_MODULE="test/test-support-0.1/src/Test.b"
TEST_C="test/test-support-0.1/src/Test.c"
WORK="${TMPDIR:-/tmp}/isabelle-codegen-test"
CC="${CC:-gcc}"
TIMEOUT=120
# The -Wno-... flags of babylon.toml, plus the three unused-name warnings:
# the generator declares a MiniC variable for every Core local and
# parameter, whether or not it is ever read (the elaborator's call@@tmp of
# a procedure call, a shadowed let variable, the tag of a match whose arms
# are all wildcards, a parameter the Babylon function ignores), and it does
# no dead-variable analysis (DESIGN.md 11.3).
NOWARN=(-Wno-overflow -Wno-div-by-zero -Wno-stringop-overread
        -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-parameter)

FILTER=${1:-}

if ! [ -d $CASES_DIR ]; then
    echo "This script must be run from the root directory of the distribution (as in: ./test/isabelle_codegen_test.sh)."
    exit 1
fi

if ! [ -x $MAIN ]; then
    echo "$MAIN not found; please build the Isabelle compiler first."
    exit 1
fi

mkdir -p "$WORK"
rm -f "$WORK"/*

NUM_PASS=0
FAILED=()

fail() {
    echo "FAILED: $*"
}

# Compile the support code once (not with -Werror: it is not ours).
if ! $CC -std=c99 -O2 -c -o "$WORK/Test.o" "$TEST_C"; then
    echo "Cannot compile $TEST_C"
    exit 1
fi

run_test()
{
    # $1 is the test name (path of the root .b file), $2 the .output file;
    # remaining args are the files to give to Main (root module first).
    local name=$1
    local output=$2
    shift 2
    local base
    base=$(basename "$name" .b)
    local ok=1
    local mode

    sed -e 's# *//.*##' "$output" > "$WORK/$base.expected"

    for mode in memset omit; do
        local c="$WORK/$base-$mode.c"
        if ! timeout $TIMEOUT $MAIN "--uninit=$mode" -o "$c" "$@" "$TEST_MODULE" > "$WORK/$base-$mode.compiler.out" 2>&1; then
            fail "$name ($mode): the Isabelle compiler failed:"
            cat "$WORK/$base-$mode.compiler.out"
            ok=0
            continue
        fi
        local warn=(-Wall -Wextra -pedantic -Werror "${NOWARN[@]}")
        if [ "$mode" = omit ]; then
            warn+=(-Wno-uninitialized -Wno-maybe-uninitialized)
        fi
        local opt
        for opt in -O0 -O2; do
            local exe="$WORK/$base-$mode$opt"
            if ! $CC -std=c99 $opt "${warn[@]}" -o "$exe" "$c" "$WORK/Test.o" > "$exe.gcc.out" 2>&1; then
                fail "$name ($mode, $opt): gcc failed:"
                head -20 "$exe.gcc.out"
                ok=0
                continue
            fi
            timeout $TIMEOUT "$exe" > "$exe.stdout" 2> "$exe.stderr"
            local status=$?
            if [ $status -ne 0 ]; then
                fail "$name ($mode, $opt): exit status $status"
                ok=0
            fi
            if [ -s "$exe.stderr" ]; then
                fail "$name ($mode, $opt): stderr is not empty:"
                head -5 "$exe.stderr"
                ok=0
            fi
            if ! diff -u "$WORK/$base.expected" "$exe.stdout" > "$exe.diff"; then
                fail "$name ($mode, $opt): stdout differs from $output:"
                head -20 "$exe.diff"
                ok=0
            fi
        done
    done

    if [ $ok -eq 1 ]; then
        NUM_PASS=$((NUM_PASS + 1))
    else
        FAILED+=("$name")
    fi
}

run_dir()
{
    local dir=$1
    if [ -e $dir/multi.txt ]; then
        local root=$dir/Main.b
        if [[ $root =~ $FILTER ]]; then
            local others=()
            local f name
            for f in $(find $dir -name '*.b' ! -path $root | sort); do
                name=${f#$dir/}
                name=${name%.b}
                others+=("${name//\//.}=$f")
            done
            run_test $root $dir/Main.output $root "${others[@]}"
        fi
    else
        local f
        for f in $dir/*; do
            if [[ -f $f && $f == *.b && $f =~ $FILTER ]]; then
                run_test $f ${f%.b}.output $f
            elif [ -d $f ]; then
                run_dir $f
            fi
        done
    fi
}

run_dir $CASES_DIR

echo
echo "${NUM_PASS} tests passed, ${#FAILED[@]} failed."
if [ ${#FAILED[@]} -ne 0 ]; then
    echo "Failed tests:"
    for t in "${FAILED[@]}"; do
        echo "  $t"
    done
    exit 1
fi
