A Separation Logic for effect handlers
======================================

## Paper-Formalization Correspondence

### Section 2 - Syntax and semantics of HH

Both the syntax and the operational semantics of HH are defined
in the file [theories/lang.v](theories/lang.v).
There, you will find the following definitions:

  + **Syntax.** `expr` is the type of expressions.

  + **Evaluation contexts.** `ectx_item` is the type of shallow evaluation contexts
    and `ectx`, the type of deep evaluation contexts.

  + **Semantics.** `head_step` is the head step reduction relation and `prim_step`
    is its closure under evaluation contexts.

  + **Neutral contexts.** a evaluation context is neutral when it does not
    catch an effect. The predicate `NeutralEctxi` holds for neutral shallow
    contexts and `NeutralEctx`, for deep contexts.

The selected heap step reduction rules shown in the paper
are named in the formalization as follows:

| Paper | Coq formalization |
|-------|-------------------|
| R1    | `DoS`             |
| R2    | `AppREffS`        |
| R3    | `AppLEffS`        |
| R4    | `TryWithEffS`     |
| R5    | `TryWithRetS`     |
| R6    | `ContS`           |


### Section 3 - Protocols and specifications

In the file [theories/ieff.v](theories/ieff.v), you will find all the
definitions from Figure 4 except for the definition of the *allows-do*
assertion. Namely, you will find the following definitions:

  + **Protocol domain.** `iEff Σ` is the type of protocols.

  + **Empty Protocol.** `iEff_bottom` is the empty protocol and `iEff_sum` is the
     protocol sum operation.

The *allows-do* assertion is named `protocol_agreement` in the formalization.
It is defined in the file [theories/protocol_agreement.v](theories/protocol_agreement.v).
There, you will also find the definition of the preorder relation on protocols, `iEff_le`,
as well as the formal statement of the rules from Figure 3. These rules are named
in the formalization as follows:

| Paper | Coq formalization                                       |
|-------|---------------------------------------------------------|
| A1    | `protocol_agreement_tele`                               |
| A2    | `protocol_agreement_bottom`                             |
| A3    | `protocol_agreement_sum_`(`elim`\|`intro_l`\|`intro_r`) |
| A4    | `protocol_agreement_marker_`(`elim`\|`intro`)           |
| A5    | `protocol_agreement_mono`                               |


### Section 4 - A Separation Logic for HH

The *extended weakest precondition* (*ewp*) is defined in the file
[theories/weakestpre.v](theories/weakestpre.v) as the fixpoint of the
operator `ewp_pre`.

The predicate *shallow-handler* from the paper corresponds to the
definition `shallow_handler` from [theories/shallow_handler.v](theories/shallow_handler.v)

The predicate *deep-handler* from the paper corresponds to the
definition `deep_handler` from [theories/deep_handler.v](theories/deep_handler.v)

The selected reasoning rules from Figure 6 are named in the formalization as follows:

| Paper            | Coq formalization                                       |
|------------------|---------------------------------------------------------|
| Value            | `ewp_value`                                             |
| Do               | No formal equivalent; the closest lemma is `ewp_eff`    |
| Monotonicity     | `ewp_strong_mono`                                       |
| Bind             | `ewp_bind`                                              |
| Bind-Pure        | `ewp_pure_bind`                                         |
| Try-With-Shallow | `ewp_try_with`                                          |
| Try-With-Deep    | `ewp_deep_try_with`                                     |


### Section 5 & 6 - Case studies

The case study from Section 5 is formalized in the file [theories/cascade.v](theories/cascade.v)

The case study from Section 6 is formalized in the file [theories/scheduler.v](theories/scheduler.v)


## Notation

The following table shows how the notation introduced in the paper compares
to the one introduced in the Coq formalization.


|                            | Paper                                           | Coq formalization                                              |
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
| Continuation construct     | `(λ N)^l`                                       | `ContV N l`                                                    |
| Shallow handler construct  | `shallow-try e with h \| r`                     | `TryWith e h r`                                                |
| Shallow handler judgement  | `shallow-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}`        | `shallow_handler E h r Ψ Ψ Ψ' Φ Φ'`                            |
| Deep handler construct     | `deep-try e with h \| r`                        | `try: e with effect h \| return r end`                         |
| Deep handler judgement     | `deep-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}`           | `deep_handler E h r Ψ Ψ' Φ Φ'`                                 |
