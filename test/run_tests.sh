#!/bin/bash

COMPILER="build/bab"

CASES_DIR="test/cases"
SEQUENCE_TESTS_DIR="test/sequence"
PACKAGE_TESTS_DIR="test/package_tests"

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
    if [ $VALGRIND -eq 1 ]
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

filter_zlib_version()
{
    # This is an attempt to make the 'system_package_failure' and
    # 'system_package_success' tests independent of the installed
    # zlib version.
    sed -i "s/version of zlib is.*$/version of zlib is/g" $1
}

write_package_file()
{
    template_file=$1
    root_module=$2
    cp test/$template_file $OUT_DIR/package.toml
    sed -i -e "s/MODULE_NAME/${root_module%.$PROG_EXT}/g" $OUT_DIR/package.toml
}

run_test()
{
    # $1 is the test folder name
    # $2 is the root .b file name (including extension)
    # Remaining args are the complete list of files or folders to symlink
    # into $OUT_DIR.
    folder=$1
    root_module=$2
    shift 2

    echo $folder/$root_module

    # Remove previous contents of output folder, if any
    rm -fr $OUT_DIR/* || return 1

    # Make the package.toml file
    write_package_file package_template.toml $root_module

    # Make the src directory, and link the source-code file(s) into place
    mkdir $OUT_DIR/src
    for filename in $@
    do
        ln -s $(pwd)/$folder/$filename $OUT_DIR/src/ || return 1
    done


    # Verify the test module (and any imports)
    # (cd into the directory so that the error messages don't include the full path!)
    pushd $OUT_DIR >/dev/null
    XDG_CONFIG_HOME=../config $COMPILER verify --continue --quiet --timeout $TIMEOUT --package-path .. >verifier_stdout.txt 2>verifier_stderr.txt
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


    # Compile the package, creates $OUT_DIR/build/bin/test-binary
    XDG_CONFIG_HOME=test/config $COMPILER compile --root $OUT_DIR --package-path test >$OUT_DIR/compiler_stdout.txt 2>$OUT_DIR/compiler_stderr.txt
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

    # Run the compiled executable, capture stdout and stderr
    # (If it doesn't return zero status then that is a test failure)
    $OUT_DIR/build/bin/test-binary >$OUT_DIR/prog_stdout.txt 2>$OUT_DIR/prog_stderr.txt || return 1

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
        input_files=""
        for i in $1/*
        do
            input_files+=" $(basename $i)"
        done
        if [[ $1/Main.$PROG_EXT =~ $2 ]]
        then
            run_test $1 Main.$PROG_EXT $input_files || return 1
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
    rm -fr $OUT_DIR/* || return 1

    # Make a package.toml file
    write_package_file sequence/sequence_test.toml Main
    mkdir $OUT_DIR/src

    # For each test in the sequence
    for i in $SEQUENCE_TESTS_DIR/??
    do
        echo $i/Main.$PROG_EXT

        # Run the compiler, putting output into $OUT_DIR
        rm -f $OUT_DIR/src/*.$PROG_EXT
        for bfile in $i/*.$PROG_EXT
        do
            ln -s ../../../$bfile $OUT_DIR/src/
        done
        XDG_CONFIG_HOME=test/config $COMPILER verify --timeout $TIMEOUT -r $OUT_DIR -p test >$OUT_DIR/verifier_stdout.txt 2>$OUT_DIR/verifier_stderr.txt

        # Clip out reports of which prover succeeded, like "(z3,
        # 0.1s)", and also messages like "(cached)" (in certain
        # cases), as these may vary on different machines (due to
        # differences in timing, number of parallel solvers allowed to
        # run, or just different solvers being used).
        sed -i -E -e 's/ \([^()]*, [0-9]+\.[0-9]s\)//g' $OUT_DIR/verifier_stderr.txt
        sed -i -E -e 's/^Checking(.*) \(cached\)$/Checking\1/g' $OUT_DIR/verifier_stderr.txt
        sed -i -E -e "s/ \\([^()]* returned '[a-z]+'\\)//g" $OUT_DIR/verifier_stderr.txt

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

function run_package_tests()
{
    for i in $(ls $PACKAGE_TESTS_DIR)
    do
        echo "$PACKAGE_TESTS_DIR/$i"

        rm -rf $OUT_DIR/* || return 1
        cp -r $PACKAGE_TESTS_DIR/$i/* $OUT_DIR/ || return 1

        # Verify
        XDG_CONFIG_HOME=test/config $COMPILER verify --quiet -p $OUT_DIR -p test/ -r $OUT_DIR/root >$OUT_DIR/verifier_stdout.txt 2>$OUT_DIR/verifier_stderr.txt
        verifier_result=$?
        cp $OUT_DIR/verifier_stderr.txt $OUT_DIR/verifier_stderr_unfiltered.txt
        filter_valgrind $OUT_DIR/verifier_stderr.txt || return 1
        filter_zlib_version $OUT_DIR/verifier_stderr.txt || return 1

        if [ -a $OUT_DIR/verifier_stderr.expected ]
        then
            diff -u $OUT_DIR/verifier_stderr.expected $OUT_DIR/verifier_stderr.txt || return 1
            expected_verifier_result=1
        else
            check_file_empty verifier_stdout.txt || return 1
            check_file_empty verifier_stderr.txt || return 1
            expected_verifier_result=0
        fi
        if [ $verifier_result -ne $expected_verifier_result ]
        then
            echo "Verifier gave nonzero exit status"
            return 1
        fi
        if [ $verifier_result -ne 0 ]
        then
            continue
        fi

        # Compile
        XDG_CONFIG_HOME=test/config $COMPILER compile -p $OUT_DIR -p test -r $OUT_DIR/root >$OUT_DIR/compiler_stdout.txt 2>$OUT_DIR/compiler_stderr.txt
        compiler_result=$?
        filter_valgrind $OUT_DIR/compiler_stderr.txt || return 1

        check_file_empty compiler_stdout.txt || return 1
        check_file_empty compiler_stderr.txt || return 1
        if [ $compiler_result -ne 0 ]
        then
            echo "Compiler gave nonzero exit status"
            return 1
        fi

        # Run
        $OUT_DIR/root/build/bin/root >$OUT_DIR/prog_stdout.txt 2>$OUT_DIR/prog_stderr.txt || return 1
        check_file_empty $OUT_DIR/prog_stderr.txt || return 1
        cp $OUT_DIR/prog_stdout.txt $OUT_DIR/prog_stdout_unfiltered.txt
        filter_zlib_version $OUT_DIR/prog_stdout.txt || return 1
        diff -u $OUT_DIR/prog_stdout.expected $OUT_DIR/prog_stdout.txt || return 1

    done

    return 0
}

print_usage()
{
    echo "Usage: run_tests.sh [OPTIONS] [FILTER]"
    echo "  -m: runs main tests"
    echo "  -s: runs sequence tests"
    echo "  -p: runs package tests"
    echo "  -c NAME: uses NAME as the compiler executable"
    echo "  -v: run the compiler using Valgrind"
    echo "  FILTER: if specified, runs only tests including FILTER in the name (only works for -m currently)"
}

read_options()
{
    if ! [ -d $CASES_DIR ]
    then
        echo "This script must be run from the root directory of the distribution (as in: ./test/run_tests.sh)."
        return 1
    fi

    VALGRIND=0
    MAIN=0
    SEQ=0
    PKG=0

    local OPTIND

    while getopts "vmspc:" opt; do
        case $opt in
            v)
                VALGRIND=1
                echo "Running tests using Valgrind..."
                ;;
            m)
                MAIN=1
                ;;
            s)
                SEQ=1
                ;;
            p)
                PKG=1
                ;;
            c)
                COMPILER=$OPTARG
                ;;
            *)
                print_usage
                return 1
                ;;
        esac
    done

    shift $(($OPTIND - 1))
    FILTER=$1

    if [ $MAIN -eq 0 ] && [ $SEQ -eq 0 ] && [ $PKG -eq 0 ]
    then
        echo "No tests specified; please use one of -m, -s or -p"
        print_usage
        return 1
    fi

    COMPILER=$(pwd)/$COMPILER
    if [ $VALGRIND -eq 1 ]
    then
        COMPILER="valgrind --leak-check=full --num-callers=40 $COMPILER"
    fi

    return 0
}

if read_options "$@"
then
    mkdir -p $OUT_DIR

    ERROR=0

    if [ $MAIN -ne 0 ]
    then
        run_main_tests $CASES_DIR $FILTER
        ERROR=$?
    fi

    if [ $SEQ -ne 0 ] && [ $ERROR -eq 0 ]
    then
        run_sequence_tests
        ERROR=$?
    fi

    if [ $PKG -ne 0 ] && [ $ERROR -eq 0 ]
    then
        run_package_tests
        ERROR=$?
    fi

    if [ $ERROR -ne 0 ]
    then
        echo "TESTS FAILED"
        false   # set nonzero exit status for the script
    else
        if [ $VALGRIND -eq 0 ]
        then
            echo "Done"
        else
            echo "Done (Valgrind)"
        fi
    fi

else
    # Failed to read options
    false
fi
