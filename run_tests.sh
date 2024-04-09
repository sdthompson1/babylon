#!/bin/bash

COMPILER="build/babylon"
CC="gcc -g -Wno-overflow -Wno-div-by-zero test/test_support.c"

TEST_MODULE="test/Test.b"
CASES_DIR="test/cases"
SEQUENCE_TESTS_DIR="test/sequence"

OUT_DIR="test/output_tmp"

PROG_EXT="b"

# this might need to be increased on slow machines:
TIMEOUT=5

check_file_empty()
{
    if [ -s $OUT_DIR/$1 ]
    then
        echo "$1 not empty:"
        cat $OUT_DIR/$1
        return 1
    fi
    return 0
}

filter_valgrind()
{
    if [[ $VALGRIND == "v" ]]
    then
        # Check for valgrind success
        grep "ERROR SUMMARY: 0 errors from 0 contexts" $1 >/dev/null
        if [[ $? != 0 ]]
        then
            echo "Valgrind errors found"
            cat $1
            return 1
        fi

        # Delete valgrind lines from the file (making backup first)
        cp $1 $1.valgrind
        sed -E -i "/^==[0-9]+==/d" $1
    fi
    return 0
}

run_test()
{
    # $1 is the test folder name
    # $2 is the root .b file name (including extension)
    # Remaining args are the complete list of .b files to copy
    folder=$1
    root_module=$2
    shift 2

    echo $folder/$root_module

    # Remove previous contents of output folder, if any
    rm -f $OUT_DIR/* || return 1

    # Link the source-code (.b) file(s) into place
    for filename in $@
    do
        ln -s $(pwd)/$folder/$filename $OUT_DIR/ || return 1
    done
    ln -s $(pwd)/$TEST_MODULE $OUT_DIR/ || return 1


    # Verify the root module (and all submodules)
    # (cd into the directory so that the error messages don't include the full path!)
    pushd $OUT_DIR >/dev/null
    $COMPILER --verify-all --verify-continue --quiet --verify-timeout $TIMEOUT --main $root_module >verifier_stdout.txt 2>verifier_stderr.txt
    verifier_result=$?
    popd >/dev/null

    # Stdout should be empty
    check_file_empty verifier_stdout.txt || return 1

    # Compare actual and expected results
    expected_err_file=$folder/${root_module%."$PROG_EXT"}.errors
    if [ -a $expected_err_file ]
    then
        # Expecting failure
        # Copy in the "expected stderr" file, removing "//" comments (and any whitespace
        # before the "//")
        sed -e 's# *//.*##' $expected_err_file >$OUT_DIR/verifier_stderr.expected || return 1

        # Diff
        filter_valgrind $OUT_DIR/verifier_stderr.txt || return 1
        diff -u $OUT_DIR/verifier_stderr.expected $OUT_DIR/verifier_stderr.txt || return 1

        expected_verifier_result=1

    else
        # Expecting success
        # stderr should be empty
        filter_valgrind $OUT_DIR/verifier_stderr.txt || return 1
        check_file_empty verifier_stderr.txt || return 1

        expected_verifier_result=0
    fi

    # Check verifier result code is as expected
    if [ $verifier_result -ne $expected_verifier_result ]
    then
        echo "Verifier result code of $verifier_result was unexpected"
        return 1
    fi

    # If verifier failure was expected then this is as far as we go.
    if [ $verifier_result -ne 0 ]
    then
        return 0
    fi


    # Compile root module -- creates .c file(s).
    $COMPILER --compile --main $OUT_DIR/$root_module >$OUT_DIR/compiler_stdout.txt 2>$OUT_DIR/compiler_stderr.txt
    compiler_result=$?

    # Stdout and stderr from the compiler should be empty, and
    # result should be zero.
    check_file_empty compiler_stdout.txt || return 1
    filter_valgrind $OUT_DIR/compiler_stderr.txt || return 1
    check_file_empty compiler_stderr.txt || return 1
    if [ $compiler_result -ne 0 ]
    then
        echo "Compiler gave nonzero exit status"
        return 1
    fi

    # Use gcc to link the .c files and test_support.c, making an executable file
    $CC $OUT_DIR/*.c -o $OUT_DIR/test_binary || return 1

    # Run the compiled executable, capture stdout and stderr
    # (If it doesn't return zero status then that is a test failure)
    $OUT_DIR/test_binary >$OUT_DIR/prog_stdout.txt 2>$OUT_DIR/prog_stderr.txt || return 1

    # Stderr from the compiled program should be empty
    check_file_empty prog_stderr.txt || return 1

    # Copy the "expected" output file to OUT_DIR, removing "//" comments
    sed -e 's# *//.*##' $folder/${root_module%."$PROG_EXT"}.output >$OUT_DIR/prog_stdout.expected || return 1

    # Compare expected and actual output.
    diff -u $OUT_DIR/prog_stdout.expected $OUT_DIR/prog_stdout.txt || return 1


    return 0
}

run_main_tests()
{
    # $1 is the test directory ($CASES_DIR or a subdirectory)
    # $2 is a pattern (might be empty)

    if [ -a $1/multi.txt ]
    then
        modules=""
        for i in $1/*.$PROG_EXT
        do
            modules+=" $(basename $i)"
        done
        if [[ $1/Main.$PROG_EXT =~ $2 ]]
        then
            run_test $1 Main.$PROG_EXT $modules || return 1
        fi
    else
        for i in $(ls $1)
        do
            if [[ -f $1/$i && $i == *".$PROG_EXT" && $1/$i =~ $2 ]]
            then
                run_test $1 $i $i || return 1
            elif [ -d $1/$i ]
            then
                run_main_tests $1/$i $2 || return 1
            fi
        done
    fi
    return 0
}

run_sequence_tests()
{
    # This runs a sequence of verification problems to check that the
    # babylon.cache file is working as intended.

    # Remove previous contents of output folder, if any
    rm -f $OUT_DIR/* || return 1

    # For each test in the sequence
    for i in $SEQUENCE_TESTS_DIR/*
    do
        echo $i/Main.b

        # Run the compiler, putting output into $OUT_DIR
        $COMPILER --verify-all --verify-timeout $TIMEOUT $i/Main.b -o $OUT_DIR >$OUT_DIR/verifier_stdout.txt 2>$OUT_DIR/verifier_stderr.txt

        # Clip out reports of which prover succeeded, like "(z3,
        # 0.1s)", and also messages like "(cached)", as these may vary
        # on different machines (due to differences in timing, number
        # of parallel solvers allowed to run, or just different
        # solvers being used).
        sed -i -E -e 's/ \([^()]*, [0-9]+\.[0-9]s\)//g' $OUT_DIR/verifier_stderr.txt
        sed -i -E -e 's/ \(cached\)//g' $OUT_DIR/verifier_stderr.txt

        # All these tests should succeed
        if [ $? -ne 0 ]
        then
            echo "Verifier failed (unexpectedly)"
            return 1
        fi

        # Stdout should be empty
        check_file_empty $OUT_DIR/verifier_stdout.txt || return 1

        # Stderr should match expected
        filter_valgrind $OUT_DIR/verifier_stderr.txt || return 1
        diff -u $i/expected.txt $OUT_DIR/verifier_stderr.txt || return 1
    done

    return 0
}

function run_all_tests()
{
    run_main_tests $1 $2 || return 1

    if [[ -z $2 ]] || [[ $2 == sequence ]] || [[ $2 == seq ]]
    then
        run_sequence_tests || return 1
    fi

    return 0
}


COMPILER=$(pwd)/$COMPILER

# "-v" option invokes Valgrind on each run. (Note -v must come first!)
getopts "v" VALGRIND
if [[ $VALGRIND == "v" ]]
then
    COMPILER="valgrind --leak-check=full --num-callers=40 $COMPILER"
    echo "Running tests using Valgrind..."
fi
shift $((OPTIND-1))

mkdir -p $OUT_DIR

if run_all_tests $CASES_DIR $1
then
    if [ -z $1 ]
    then
        if [[ $VALGRIND == "v" ]]
        then
            echo "All tests passed, no Valgrind errors found"
        else
            echo "All tests passed!"
        fi
    else
        if [[ $VALGRIND == "v" ]]
        then
            echo "Done (Valgrind)"
        else
            echo "Done"
        fi
    fi
else
    echo "TESTS FAILED"
fi
