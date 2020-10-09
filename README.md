# Hazel - A Separation Logic for Effect Handlers

This repository formalizes in Coq the contents of the homonym paper. To browse
the project with ease, please take a look at the list of theories below.

## Preliminaries

 - [theories/lib.v](theories/lib.v): General definitions and lemmas.

## Language

 - [theories/lang.v](theories/lang.v): Definition of the programming language
   (named `eff_lang` here).
   + Syntax: the syntax is implied by the definition of `expr`, the type of
     expressions.
   + Evaluation contexts: `ectxi` is the type of shallow contexts and `ectx`,
     the type of deep contexts. (`ectx` is isomorphic to `list ectxi`.)
   + Semantics: `head_step` is the head step reduction relation and `prim_step`
     is its closure under evaluation contexts.
   + Neutral contexts: a shallow context is neutral when it satisfies the
     predicate `NeutralEctxi`. A neutral deep context, `NeutralEctx`, is then
     simply defined as a list of neutral shallow contexts.
 - [theories/notation.v](theories/notation.v): Syntactic sugar for commom
   constructs of the language.

## Protocols

 - [theories/ieff.v](theories/ieff.v): Definition of effect protocols and
   auxiliary operators.
   + Domain: the space `iEff` described in the paper is defined here. It is the
     application of the functor `ieff` to `iProp`.
   + Protocols: empty protocols are constructed via `iEff_done`, while nonempty
     ones are constructed via `iEff_cons`.
   + Notation: the protocol `end` is denoted by `Done` in the development. For a
     nonempty protocol
       `! x_1 .. x_n (v) { P }. ? y_1 .. y_2 (u) { Q }`
     we also use another notation:
       `>> x_1 .. x_n >> ! v { P }. << y_1 .. y_2 << ? u { Q }`.

## Reasoning Rules / Logic

 - [theories/weakestpre.v](theories/weakestpre.v): Definition of the weakest
   precondition and proof of usual reasoning rules.
   + Weakest precondition: it is defined here as the fixpoint of the operator
     `ewp_pre`.
   + Notation: the statement `ewp e < Ψ > { Φ }` is denoted by
     `EWP e <| Ψ |> {{ Φ }}` in the development.
   + Rules: some of the reasoning rules mentioned in the paper are (Val)
    `ewp_value`, (End) `ewp_Done`, (Wand) `ewp_strong_mono`, (Do) `ewp_eff`,
    (Bind) `ewp_bind`, (Try-With-Shallow) `ewp_try_with`.
 - [theories/deep_handler.v](theories/deep_handler.v): Proof of the reasoning
   rule for deep handlers.
   + Deep handler judgement: it is defined in the development under the name
     `is_deep_handler`.
   + Rules: the reasoning rule (Try-With-Deep) is proved here, it is the lemma
     `ewp_try_with_deep`.
 - [theories/heap.v](theories/heap.v): Proof of the reasoning rules for
   manipulating the heap.
 - [theories/adequacy.v](theories/adequacy.v): Proof that `ewp e < Done > { Φ }`
   implies `wp e { Φ }`.

## Libraries

 - [theories/list_lib.v](theories/list_lib.v): Interface of a library for
   manipulating lists.
 - [theories/queue_lib.v](theories/queue_lib.v): Interface of a library for
    manipulating queues.

## Case studies

 - [theories/cascade.v](theories/cascade.v): control inversion (case study from
    section 5).
 - [theories/state.v](theories/state.v): single mutable cell by parameter
   passing style (not included in the paper).
 - [theories/exceptions.v](theories/exceptions.v): exceptions (not included in
   the paper).
 - [theories/scheduler.v](theories/scheduler.v): verification of an asynchronous
   library (case study from section 6).
 - [theories/shallow_handler.v](theories/shallow_handler.v): verified encoding
   of shallow handlers using deep handlers.

