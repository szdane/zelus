#!/usr/bin/env bash
set -euo pipefail
dune clean 
./configure
dune build @install
dune install
cd verification_examples/
cd watertank/
# make clean
make sim

echo "All done "
