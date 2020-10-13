# Hazel - A Separation Logic for Effect Hanlders

## Instructions

  To compile our proofs, you need `opam`, the OCaml package manager.
    (A recent version of `opam` is recommended; we use 2.0.6.)

  Once you have `opam`, please type:

    ./setup.sh

  This should create a "local opam switch" in the current directory, install
  the *specific* versions of Coq, stdpp, and Iris that we need, then
  compile our proofs.

## Troubleshooting

  In case you need to know, information on the specific versions of
  Stdpp and Iris that we need can be found in the file `opam`. This
  development is known to compile with Coq 8.11.2.

  `opam` may complain that the repository `iris-dev` already exists
  with a different URL. If this happens, please type

    opam repo remove iris-dev --all

  then try `./setup.sh` again. (You will later need to re-declare
  the `iris-dev` repository. Sorry about that.)
