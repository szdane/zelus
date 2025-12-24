#!/usr/bin/env bash
set -euo pipefail
dune clean 
./configure
dune build @install
dune install
cd marvelus_examples/
cd takeoff/
# make clean
make sim

echo "All done "
