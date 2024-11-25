#!/bin/bash

# This script can be run after `make cover` or `make incr-cover`
# to find code lines that have been modified or added since the
# latest commit, but are not covered by the tests.

# Explanation:
# - Run git blame.
# - Look for '^00000000' which indicates the line isn't checked in yet.
# - Use cut to get the line numbers which have been modified.
# - Use sed to change that into a pattern which looks for ##### (which is gcov's
#   way of saying that the line is uncovered) followed by the line number followed
#   by a colon.
# - Use grep to look for such lines in the gcov file.
# - Finally exclude "fatal_error" lines as we generally aren't interested in these.

for i in src/*.c; do
    echo $i
    git blame $i |grep '^00000000' -n |cut -f1 -d: |sed 's/^/#####:[ ]*/g' |sed 's/$/:/g' |grep -f - gcov/${i#src/}.gcov |grep -v fatal_error
done
