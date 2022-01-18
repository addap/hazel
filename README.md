# Hazel - A Separation Logic for Effect Handlers

This repository contains the Coq formalization of the following papers:

- [*Verifying a minimalist reverse-mode AD library*]
  (http://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-verifying-rmad.pdf) (Submitted to LMCS)  
  Paulo Emílio de Vilhena and François Pottier  
  To see how the paper compares to the
  formalization consult the page [LMCS-RMAD.md](papers/LMCS-RMAD.md).

- [*A Separation Logic for effect handlers*]
  (http://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf) (POPL 2021)  
  Paulo Emílio de Vilhena and François Pottier  
  To see how the paper compares to the
  formalization consult the page [POPL21-sleh.md](papers/POPL21-sleh.md).


## Installation

To build the Hazel project you can follow the
instructions in the file [INSTALL.md](../INSTALL.md).

These instructions show you how to create a separate opam switch with the
necessary packages to build the project, thus keeping your previous
switches clean.

Alternatively, you can install the packages by yourself
according to their versions as listed in the file [opam](../opam).


## Repository Structure

### Preliminaries

 - [theories/lib.v](theories/lib.v): General definitions and lemmas.

### Language

 - [theories/lang.v](theories/lang.v): Definition of the HH programming language.
 - [theories/notation.v](theories/notation.v): Syntactic sugar for common
   constructs of the language.

### Protocols

 - [theories/ieff.v](theories/ieff.v): Definition of protocols and
   auxiliary operators.
 - [theories/protocol_agreement.v](theories/protocol_agreement.v): Introduction and
   study of the protocol agreement judgement.
   + Ordering: `iEff_le` is a pre order relation on protocols.

### Reasoning Rules / Logic

 - [theories/weakestpre.v](theories/weakestpre.v): Definition of the weakest
   precondition and proof of usual reasoning rules.
 - [theories/heap.v](theories/heap.v): Proof of the reasoning rules for
   operations manipulating the heap.
 - [theories/shallow_handler.v](theories/shallow_handler.v): Reasoning rule for shallow handlers.
 - [theories/deep_handler.v](theories/deep_handler.v): Reasoning rule for deep handlers.
 - [theories/adequacy.v](theories/adequacy.v): Adequacy theorem.

### Libraries

 - [theories/list_lib.v](theories/list_lib.v): Interface of a library for
   manipulating lists.
 - [theories/queue_lib.v](theories/queue_lib.v): Interface of a library for
    manipulating queues.

### Case studies

 - [theories/cascade.v](theories/cascade.v): Verification of a program that
   uses effect handlers to perform *control inversion*.
 - [theories/state.v](theories/state.v): Verification of a program that
   implements a single *mutable cell* by combining parameter passing style
   and handlers.
 - [theories/exceptions.v](theories/exceptions.v): Reasoning rules for
   *exception handlers* as a special case of effect handlers.
 - [theories/scheduler.v](theories/scheduler.v): Verification of a library for
   *asynchronous computation*.
 - [theories/shallow_as_deep.v](theories/shallow_as_deep.v): Verified encoding
   of shallow handlers using deep handlers.
 - [theories/ml_references.v](theories/ml_references.v): Verification of an
   intricate implementation of ML-like references using effect handlers and
   the ability to generate fresh effect names.
 - [theories/auto_diff.v](theories/auto_diff.v): Verification of a
   minimalist reverse-mode AD library.
