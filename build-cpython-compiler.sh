#!/bin/sh
#
# Clone and build reference CPython3.5 bytecode compiler with peephole
# optimization disabled, to run testsuite.
#

set -ex

git clone --depth 1 https://github.com/pfalcon/cpython -b 3.5-noopt
cd cpython
./Build-nopeephole.sh
cd ..
ln -sf cpython/BUILD-py3.5-nopeephole/python3.5-nopeephole .
