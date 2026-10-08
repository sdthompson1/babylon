#!/bin/bash

# Simple test script for the Isabelle compiler.
#
# Runs the Isabelle compiler on the test cases in the directories listed
# below, and checks only its success/failure status (not its output).
#
# - codegen, parser, renamer, typechecker: the compiler should succeed if
#   the test has no .errors file, and fail if it does.
# - verifier: the Isabelle compiler has no verifier yet, so it should
#   succeed on every test.
#
# Tests that don't behave as expected are listed at the end.
#
# Usage: ./test/isabelle_test.sh [FILTER]
#   (run from the root directory; FILTER restricts to tests whose path
#   contains FILTER)

MAIN="isabelle/export/Babylon.CodeExport/code/export1/Main"
CASES_DIR="test/cases"
TEST_MODULE="test/isabelle_support/Test.b"
TIMEOUT=60

FILTER=$1

if ! [ -d $CASES_DIR ]
then
    echo "This script must be run from the root directory of the distribution (as in: ./test/isabelle_test.sh)."
    exit 1
fi

if ! [ -x $MAIN ]
then
    echo "$MAIN not found; please build the Isabelle compiler first."
    exit 1
fi

NUM_PASS=0
UNEXPECTED=()

run_test()
{
    # $1 is the test name (path of the root .b file)
    # $2 is "pass" if the compiler is expected to succeed, "fail" otherwise
    # Remaining args are the files to give to Main (root module first)
    local name=$1
    local expected=$2
    shift 2

    timeout $TIMEOUT $MAIN "$@" "$TEST_MODULE" >/dev/null 2>&1
    local status=$?

    local actual
    case $status in
        0) actual=pass ;;
        1) actual=fail ;;
        124) actual="timeout" ;;
        *) actual="crash (exit status $status)" ;;
    esac

    if [ "$actual" == "$expected" ]
    then
        NUM_PASS=$((NUM_PASS + 1))
    else
        echo "UNEXPECTED: $name: expected $expected, got $actual"
        UNEXPECTED+=("$name")
    fi
}

expected_result()
{
    # $1 is the category (top-level directory name)
    # $2 is the root .b file path
    if [ "$1" == "verifier" ] || ! [ -e "${2%.b}.errors" ]
    then
        echo pass
    else
        echo fail
    fi
}

run_dir()
{
    # $1 is the category, $2 is the directory
    local category=$1
    local dir=$2

    if [ -e $dir/multi.txt ]
    then
        # Multi-module test: Main.b is the root, all other .b files
        # (including those in subdirectories) are supplied as well.
        # Each of these is named explicitly according to its path
        # relative to $dir, e.g. $dir/A/B/C.b is module A.B.C.
        local root=$dir/Main.b
        if [[ $root =~ $FILTER ]]
        then
            local others=()
            local f name
            for f in $(find $dir -name '*.b' ! -path $root | sort)
            do
                name=${f#$dir/}
                name=${name%.b}
                others+=("${name//\//.}=$f")
            done
            run_test $root $(expected_result $category $root) $root "${others[@]}"
        fi
    else
        local f
        for f in $dir/*
        do
            if [[ -f $f && $f == *.b && $f =~ $FILTER ]]
            then
                run_test $f $(expected_result $category $f) $f
            elif [ -d $f ]
            then
                run_dir $category $f
            fi
        done
    fi
}

for category in codegen parser renamer typechecker verifier
do
    run_dir $category $CASES_DIR/$category
done

echo
echo "${NUM_PASS} tests behaved as expected, ${#UNEXPECTED[@]} did not."
if [ ${#UNEXPECTED[@]} -ne 0 ]
then
    echo "Unexpected results:"
    for t in "${UNEXPECTED[@]}"
    do
        echo "  $t"
    done
    exit 1
fi
