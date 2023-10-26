#!/bin/bash
pushd gcov
gcov -o ../build/src ../src/*.c
popd
