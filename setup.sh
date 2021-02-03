#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

# This script attempts to install the required software
# to check our proofs.

# Check for opam.

if ! command -v opam >/dev/null ; then
  echo "You are missing opam, the OCaml package manager."
  echo "You can install it via the following command:"
  echo "  sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
  echo "There are other ways of installing it, documented here:"
  echo "  https://opam.ocaml.org/doc/Install.html"
  exit 1
fi

echo "Updating our local copy of the opam package database."
echo "This can take a few minutes..."
opam update

if [ -d _opam ] ; then
  echo "There is already a local opam switch in the current directory."
  echo "If it is OK to remove it, please type:"
  echo "  opam switch remove ."
  echo "then run ./setup.sh again."
  exit 1
fi

echo "Creating a local opam switch in the current directory."
echo "This will take a while (perhaps over 10 minutes)..."

export OPAMYES=true

opam switch create \
  --no-install \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
  . ocaml-base-compiler.4.11.1

eval $(opam env)

echo "Updating our local copy of the opam package database (again)..."
opam update

echo "Installing Coq and the necessary Coq libraries."
echo "This will take a while (perhaps over 10 minutes)..."

opam pin add -n coq 8.13.0
make build-dep

echo "Now compiling the Coq proofs."
echo "This can take a few minutes..."

make all -j 8
