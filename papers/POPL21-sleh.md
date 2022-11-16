A Separation Logic for Effect Handlers
======================================

## Paper-Formalization Correspondence

### Section 2 - Syntax and semantics of `HH`

The `HH` calculus can be seen as a subset of the language `eff_lang`
whose syntax is defined in [syntax.v](../theories/language/syntax.v)
and whose small-step operational semantics is defined in
[semantics.v](../theories/language/semantics.v)

The selected heap step reduction rules shown in the paper
are named in the formalization as follows:

| Paper | Coq formalization |
|-------|-------------------|
| R1    | `DoS`             |
| R2    | `AppREffS`        |
| R3    | `AppLEffS`        |
| R4    | `TryWithOSEffS`   |
| R5    | `TryWithRetS`     |
| R6    | `ContS`           |


### Section 3 - Protocols and specifications

In the file [protocols.v](../theories/program_logic/protocols.v), you shall find all the
definitions from Figure 4. Namely, you shall find the following definitions:

  + **Protocol domain.** `iEff Σ` is the type of protocols.

  + **Protocol operators.** `iEff_bottom` is the empty protocol and `iEff_sum` is the
     protocol sum operation.

In the formalization, the `allows-do` assertion corresponds to the partially applied
term `upcl OS`, called the _upward closure_. It is defined also in the file
[protocols.v](../theories/program_logic/protocols.v). There, you shall also find the
definition of the ordering relation on protocols, `iEff_le`, as well as the formal
statement of the rules from Figure 3 under the following names:

| Paper | Coq formalization                         |
|-------|-------------------------------------------|
| A1    | `upcl_tele`                               |
| A2    | `upcl_bottom`                             |
| A3    | `upcl_sum_`(`elim`\|`intro_l`\|`intro_r`) |
| A4    | `upcl_marker_`(`elim`\|`intro`)           |
| A5    | `upcl_mono_prot`                          |


### Section 4 - A Separation Logic for HH

The _extended weakest precondition_ (*ewp*) is the specialization of the weakest
precondition `EWP e <| Ψ1 |> {| Ψ2 |} {{ Φ }}`, defined in the theory
[weakest_precondition.v](../theories/program_logic/weakest_precondition.v), to the case
where `Ψ2` is the empty protocol.

The *shallow-handler* judgment from the paper corresponds to the
definition `shallow_handler` from
[shallow_handler_reasoning.v](../theories/program_logic/shallow_handler_reasoning.v)

The *deep-handler* judgment from the paper corresponds to the
definition `deep_handler` from
[deep_handler_reasoning.v](../theories/program_logic/deep_handler_reasoning.v)

The selected reasoning rules from Figure 6 are named in the formalization as follows:

| Paper            | Coq formalization    |
|------------------|----------------------|
| Value            | `ewp_value`          |
| Do               | `ewp_do_os`          |
| Monotonicity     | `ewp_mono`           |
| Bind             | `ewp_bind`           |
| Bind-Pure        | `ewp_pure_bind`      |
| Try-With-Shallow | `ewp_try_with`       |
| Try-With-Deep    | `ewp_deep_try_with`  |


### Section 5 & 6 - Case studies

The case study from Section 5 is formalized in the file
[control_inversion.v](../theories/case_studies/control_inversion.v)

The case study from Section 6 is formalized in the file
[asynchronous_computation.v](../theories/case_studies/asynchronous_computation.v)


## Notation

The following table shows how the notation introduced in the paper compares
to the one introduced in the Coq formalization.

|                           | Paper                                    | Coq formalization                                         |
|---------------------------|------------------------------------------|-----------------------------------------------------------|
| Typical protocol          | `! x (v) {P}.`<br/>`? y (w) {Q}`         | `>>.. x >> ! v {{ P }};`<br/>`<<.. y << ! w {{ Q }} @ OS` |
| Empty protocol            | `⊥`                                      | `⊥`                                                       |
| Protocol sum              | `Ψ₁ + Ψ₂`                                | `Ψ₁ <+> Ψ₂`                                               |
| Protocol marker           | `f # Ψ`                                  | `f #> Ψ`                                                  |
| Interpretation            | `Ψ allows do v {Φ}`                      | `iEff_car (upcl OS Ψ) v Φ`                                |
| Subsumption               | `Ψ₁ ⊑ Ψ₂`                                | `Ψ₁ ⊑ Ψ₂`                                                 |
| Weakest precondition      | `ewp_E e ⟨Ψ⟩ {Φ}`                        | `EWP e @ E <\| Ψ \|> {{ Φ }}`                             |
| Active effect             | `§(N)[do v]`                             | `Eff OS v N`                                              |
| Do construct              | `do e`                                   | `Do OS e` or `do: e`                                      |
| Continuation construct    | `(λ N)^l`                                | `ContV N l`                                               |
| Shallow-handler construct | `shallow-try e with h \| r`              | `shallow-try: e with effect h \| return r end`            |
| Shallow-handler judgment  | `shallow-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}` | `shallow_handler E Ψ ⊥ Φ h r Ψ' ⊥ Φ'`                     |
| Deep-handler construct    | `deep-try e with h \| r`                 | `deep-try: e with effect h \| return r end`               |
| Deep-handler judgment     | `deep-handler ⟨Ψ⟩{Φ} h \| r ⟨Ψ'⟩{Φ'}`    | `deep_handler E Ψ ⊥ Φ h r Ψ' ⊥ Φ'`                        |
