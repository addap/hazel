# Hazel - A Separation Logic for Effect Handlers

This repository contains the Coq formalization of the following papers:

- [*Verifying a minimalist reverse-mode AD library*](http://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-verifying-rmad.pdf) (Submitted to LMCS)  
  Paulo Emílio de Vilhena and François Pottier  
  To see how the paper compares to the
  formalization consult the page [LMCS-RMAD.md](papers/LMCS-RMAD.md).

- [*A Separation Logic for effect handlers*](http://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf) (POPL 2021)  
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

 - [lib/lib.v](theories/lib/lib.v): General definitions and lemmas.

### Language

 - [language/syntax.v](theories/language/syntax.v): Definition of the
   `eff_lang` programming language.
 - [language/notation.v](theories/language/notation.v): Syntactic sugar
   for common constructs of the language.
 - [language/semantics.v](theories/language/semantics.v): Small-step
   operational semantics of `eff_lang`.
 - [language/neutral_contexts.v](theories/language/neutral_contexts.v):
   Definition of _neutral contexts_, evaluation contexts without handler frames.
 - [language/properties.v](theories/language/properties.v): General
   facts about `eff_lang`.
 - [language/iris_language.v](theories/language/iris_language.v): Proof
   that `eff_lang` is a language in the Iris sense (i.e., it satisfies the
   `Language` type class) and is thus endowed of a default notion of weakest
   precondition.
 - [language/eff_lang.v](theories/language/eff_lang.v): Gathering of
   files from this subdirectory.


### Program Logic

 - [program_logic/protocols.v](theories/program_logic/protocols.v): Theory of
   protocols. It includes the definition of the domain of protocols, protocol
   operators, protocol ordering, notions of protocol monotonicity, the upward
   closure and properties.
 - [program_logic/weakest_precondition.v](theories/program_logic/weakest_precondition.v):
   Definition of our customized notion of weakest precondition, `EWP`, which
   is well-suited for reasoning about programs that might perform effects.
 - [program_logic/basic_reasoning_rules.v](theories/program_logic/basic_reasoning_rules.v):
   Statement and proof that `EWP` enjoys standard reasoning rules from Separation Logic,
   such as the bind rule, the monotonicity rule, and the frame rule; and non-standard ones,
   such as the rules for performing effects.
 - [program_logic/state_reasoning.v](theories/program_logic/state_reasoning.v):
   Reasoning rules for heap-manipulating programs.
 - [program_logic/shallow_handler_reasoning.v](theories/program_logic/shallow_handler_reasoning.v):
   Reasoning rule for installing a shallow handler.
 - [program_logic/tactics.v](theories/program_logic/tactics.v): A set of tactics
   that automate "symbolic execution" and applications of the bind rule.
 - [program_logic/deep_handler_reasoning.v](theories/program_logic/deep_handler_reasoning.v):
   Reasoning rule for installing a deep handler.
 - [program_logic/reasoning_rules.v](theories/program_logic/reasoning_rules.v):
   Gathering of most files from this subdirectory.
 - [program_logic/adequacy.v](theories/program_logic/adequacy.v): Proof that
   reasoning in terms of `EWP` is sound.


### Case studies

  - [case_studies/iteration.v](theories/case_studies/iteration.v): Introduction
    of tools to specify iteration in the presence of effects. Specification
    of higher-order iteration methods and lazy sequences.
  - [case_studies/callcc.v](theories/case_studies/callcc.v): Implementation of
    `callcc` and `throw` using multi-shot continuations; statement and proof
    of reasoning rules for this encoding; and verification of programs
    exploiting `callcc`/`throw`, including Delbianco and Nanevski's `inc3`
    and Filinski's `shift`/`reset`.
  - [case_studies/control_inversion.v](theories/case_studies/control_inversion.v):
    Verification of two implementations of `invert`: a function that transforms
    iteration methods into lazy sequences. The first implementation is based on
    effect handlers and the second one is based on `callcc`.
  - [case_studies/shallow_as_deep.v](theories/case_studies/shallow_as_deep.v):
    Verification of the encoding of shallow handlers using deep handlers.
  - [case_studies/exceptions.v](theories/case_studies/exceptions.v):
    Verification of the encoding of exceptions using effect handlers.
  - [case_studies/state.v](theories/case_studies/state.v): Verification of the
    implementation of a mutable cell using effect handlers in _state-passing
    style_.
  - [case_studies/shift_reset.v](theories/case_studies/shift_reset.v):
    Reasoning rules for an effect-handler--based encoding of `shift` and `reset`.
  - [case_studies/asynchronous_computation.v](theories/case_studies/asynchronous_computation.v):
    Verification of a library for _asynchronous computation_.
  - [case_studies/automatic_differentiation.v](theories/case_studies/automatic_differentiation.v):
    Verification of a minimalist _reverse-mode automatic differentiation_ library.
