(* lib.v

   This theory is dedicated to general definitions and lemmas.
*)

From stdpp Require Import base.


Class DecRange `{Equiv A, Equiv B} (f : A → B) :=
  dec_range b : {a | b ≡ f a} + {∀ a, b ≢ f a}.

Class Marker `{Equiv A, Equiv B} (f : A → B) := {
  marker_inj : Inj (≡) (≡) f;
  marker_dec_range : DecRange f;
}.

Class DisjRange {A} `{Equiv B} (f g : A → B) : Prop :=
  disj_range a a' : f a ≢ g a'.

Lemma marker_dec_range' `{Equiv A, Equiv B, !Symmetric (≡@{B}), !Transitive (≡@{B})}
  (f : A → B) {Hf: Marker f} b :
  {a | b ≡ f a ∧ ∀ a', b ≡ f a' → a ≡ a'} + {∀ a, b ≢ f a}.
Proof.
  case (marker_dec_range b) as [(a & Ha)|Hb]; [left|right; apply Hb].
  exists a. split; [apply Ha|]. intros a' Ha'.
  apply marker_inj. transitivity b.
  { symmetry. apply Ha. } { apply Ha'. }
Qed.

Global Instance compose_marker
  `{Equiv A, Equiv B, Equiv C, !Symmetric (≡@{C}), !Transitive (≡@{C})}
  (f : A → B) {Hf: Marker f}
  (g : B → C) {Hg: Marker g} {Hg': Proper ((≡) ==> (≡)) g} :
    Marker (g ∘ f).
Proof.
  split; [|intro c].
  - apply (compose_inj _ (≡)); apply marker_inj.
  - case (marker_dec_range' g c) as [(b & [Hb Hb'])|Hc  ];[
    case (marker_dec_range    b) as [(a &  Ha)     |Hb''] |].
    { left. exists a. transitivity (g b). apply Hb. apply Hg'. apply Ha. }
    { right. intros a Hc. apply (Hb'' a). apply Hb'. apply Hc. }
    { right. intros a. apply Hc. }
Qed.

Lemma DisjRange_comm {A} `{Equiv B, !Symmetric (≡@{B})}
  (f g : A → B) {Hfg: DisjRange f g} : DisjRange g f.
Proof. intros a a' Heq. apply (disj_range a' a). symmetry. apply Heq. Qed.

Global Instance compose_disj_range {A B} `{Equiv C}
  (f g : B → C) {Hfg: DisjRange f g} (h h' : A → B) : DisjRange (f ∘ h) (g ∘ h').
Proof. intros a a'. simpl. apply disj_range. Qed.
