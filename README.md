# Hazel - A Separation Logic for Effect Handlers

This repository formalizes in Coq the contents of the homonym paper.
To browse the project, please take a look at the list of theories below.

## Preliminaries

 - [theories/lib.v](theories/lib.v): General definitions and lemmas.

## Language

 - [theories/lang.v](theories/lang.v): Definition of the programming language.
   + Syntax: `expr` is the type of expressions.
   + Evaluation contexts: `ectxi` is the type of shallow evaluation contexts
     and `ectx`, the type of deep evaluation contexts.
   + Semantics: `head_step` is the head step reduction relation and `prim_step`
     is its closure under evaluation contexts.
   + Neutral contexts: a evaluation context is neutral when it does not
     catch an effect. The predicate `NeutralEctxi` holds for neutral shallow
     contexts and `NeutralEctx`, for deep contexts.
 - [theories/notation.v](theories/notation.v): Syntactic sugar for common
   constructs of the language.

## Protocols

 - [theories/ieff.v](theories/ieff.v): Definition of effect protocols and
   auxiliary operators.
   + Domain: `iEff Σ` is the type of protocols.
   + Protocols: `iEff_bottom` is the empty protocol and `iEff_sum` denotes
     the sum over protocols.
 - [theories/protocol_agreement.v](theories/protocol_agreement.v): Introduction and
   study of the protocol agreement judgement.
   + Ordering: `iEff_le` is a pre order relation on protocols.

## Reasoning Rules / Logic

 - [theories/weakestpre.v](theories/weakestpre.v): Definition of the weakest
   precondition and proof of usual reasoning rules.
   + Weakest precondition: `ewp` is defined as the fixpoint of the operator `ewp_pre`.
   + Rules: some of the reasoning rules mentioned in the paper are (Val)
    `ewp_value`, (Wand) `ewp_strong_mono`, (Do) `ewp_eff`, (Bind) `ewp_bind`.
 - [theories/heap.v](theories/heap.v): Proof of the reasoning rules for
   operations manipulating the heap.
 - [theories/shallow_handler.v](theories/shallow_handler.v): Reasoning rule for shallow handlers.
   + Shallow handler judgement: the `shallow_handler` judgement is defined here.
   + Rules: proof of the reasoning rule `ewp_try_with` (Try-With-Shallow) for shallow handlers.
 - [theories/deep_handler.v](theories/deep_handler.v): Reasoning rule for deep handlers.
   + Deep handler judgement: the `deep_handler` judgement is defined here.
   + Rules: proof of the reasoning rule `ewp_deep_try_with` (Try-With-Deep) for deep handlers.
 - [theories/adequacy.v](theories/adequacy.v): Adequacy theorem.

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
 - [theories/scheduler.v](theories/scheduler.v): verification of a library for
   asynchronous computation (case study from section 6).
 - [theories/shallow_as_deep.v](theories/shallow_as_deep.v): verified encoding
   of shallow handlers using deep handlers (not included in the paper).

## Notation

|                            | Paper                                           | Coq mechanization                                              |
|----------------------------|-------------------------------------------------|----------------------------------------------------------------|
| Typical protocol           | `! x (v) {P}.`<br/>`? y (w) {Q}`                | `>>.. x >> ! v {{ P }};`<br/>`<<.. y << ! w {{ Q }}`           |
| Empty protocol             | `⊥`                                             | `⊥`                                                            |
| Protocol sum               | `Ψ₁ + Ψ₂`                                       | `Ψ₁ <+> Ψ₂`                                                    |
| Protocol marker            | `f # Ψ`                                         | `f #> Ψ`                                                       |
| Interpretation             | `Ψ allows do v {Φ}`                             | `protocol_agreement v Ψ Φ`                                     |
| Subsumption                | `Ψ₁ ⊑ Ψ₂`                                       | `Ψ₁ ⊑ Ψ₂`                                                      |
| Weakest precondition       | `ewp e ⟨Ψ⟩ {Φ}`                                 | `EWP e @ E <\| Ψ \|> {{ Φ }}`                                  |
| Active effect              | `§(N)[do v]`                                    | `Eff v N`                                                      |
| Do construct               | `do e`                                          | `Do e` or `do: e`                                              |
| Shallow handler construct  | `shallow-try e with h \| r`                     | `TryWith e h r`                                                |
| Shallow handler judgement  | `shallow-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}`        | `shallow_handler E h r Ψ Ψ Ψ' Φ Φ'`                            |
| Deep handler construct     | `deep-try e with h \| r`                        | `try: e with effect h \| return r end`                         |
| Deep handler judgement     | `deep-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}`           | `deep_handler E h r Ψ Ψ' Φ Φ'`                                 |

