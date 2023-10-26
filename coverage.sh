#!/bin/bash
mkdir -p gcov
rm gcov/*.gcov build/src/*.gcda -f
MODE=cov ./Shakefile || exit 1
pushd gcov
ln -sf ../src .
ln -sf ../test .
ln -sf ../build .
../run_tests.sh || exit 1
gcov -o ../build/src ../src/*.c
popd
