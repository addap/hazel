Verifying a minimalist reverse-mode AD library
==============================================

You have read the paper *Verifying a minimalist reverse-mode AD library*
and now you wish to study its formalization? Then this page might help you!

## Installation

To build the Hazel project you can follow the
instructions in the file [INSTALL.md](../INSTALL.md).

These instructions show you how to create a separate opam switch with the
necessary packages to build the project, thus keeping your previous
switches clean.

Alternatively, you can install the packages by yourself
according to their versions as listed in the file [opam](../opam).


## Relevant files

There are three files in the repository that are relevant to the paper:

1. The OCaml interface of the library [ad.mli](../src/ad.mli).

2. The OCaml implementation of the library [ad.ml](../src/ad.ml).

   There you will find the version of OCaml to compile the program.

3. The Coq formalization of the results in the paper [auto_diff.v](../theories/auto_diff.v).


The other files of the project are related to the design of Hazel
and to its application to case studies.
These files might be interesting for those willing to dive deeper
into the entrails of the logic, but they are not necessary for
understanding the theory .


## Link between paper and formalization

### Main result

The main result of the paper, Statement 5.1, is Definition
`hh_diff_spec` in the formalization. The proof of this statement
is the Theorem `hh_diff_correct`.


### Notation

Here is how the notation found in the formalization
compares to the notation introduced in the paper:

|                                        | Paper                 | Coq formalization                     |
|----------------------------------------|-----------------------|---------------------------------------|
| Definition 4.1 (Expressions)           | `Exp`<sub>`I`</sub>   | `Expr I`                              |
| Definition 4.2 (Expression Evaluation) | `〚E〛`<sub>`ρ`</sub>  | `eval (emap ρ E)`                     |
| Definition 4.3 (Partial Derivative)    | `∂ E / ∂ j (ρ)`       | `∂ E ./ ∂ j  .at ρ` or `diffₑ ϱ E j`  |
| Definition 4.4 (Symbolic Derivative)   | `E'`                  | `∂ E ./ ∂ tt .at (λ _, Xₑ)`           |
| Definition 4.5 (Bindings; contexts)    | `let u = a op b`      | `(u, (a, op, b))`                     |
| Definition 4.6 (Filling)               | `K[y]`                | `Let K .in y` or `filling K y`        |
| Definition 4.7 (Context Evaluation)    | `ρ{K}`                | `ρ.{[K]}` or `extension ρ K`          |
| Definition 5.2 (isExp)                 | `e isExp E`           | `IsExp e E`                           |
| Figure 6                               | `isNumDict`           | `numSpec`                             |
| Representation predicate               | `n isNum r`           | `implements n r`                      |
| Definition 5.4 (isSubExp)              | `u isSubExp E`        | `represents u E`                      |
| Definition 5.5 (Protocol)              | `Ψ'`                  | `AD`                                  |
| Definition 5.6 (Forward Invariant)     | `ForwardInv K`        | `forward_inv K`                       |
| Definition 5.7 (Backward Invariant)    | `BackwardInv K₁ K₂ y` | `backward_inv K₁ K₂ y`                |
