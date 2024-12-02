#!/bin/bash

# This script will confirm that all the packages in this folder
# can be compiled and verified using the Babylon compiler
# (which is assumed to exist at ../build/bab).

# If a "PACKAGENAME/build" folder does not already exist for
# each package then it will be created.

COMPILER="../build/bab"

make_package()
{
    # $1 is the package folder
    package=$1

    echo "### $package"

    # Compile the package
    $COMPILER compile -p . -r $package || return 1

    # Verify the package
    $COMPILER verify -p . -r $package || return 1

    return 0
}

make_all_packages()
{
    for pkg in $(ls -d */)
    do
        if ! make_package $pkg
        then
            return 1
        fi
    done
    return 0
}

if make_all_packages
then
    echo "Done"
else
    echo "BUILD FAILED"
fi
