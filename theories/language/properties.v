(* properties.v *)

(* This file collects general facts about [eff_lang] and its
   related definitions. *)

From lib Require Export lib.
From language Require Import syntax.

(* ========================================================================== *)
(** * Markers. *)

(* We prove that [InjLV] and [InjRV] form a pair of markers with
   disjoint range. *)

Instance InjLV_inj : Inj (=) (=) InjLV.
Proof. intros ??. by inversion 1. Qed.
Instance InjRV_inj : Inj (=) (=) InjRV.
Proof. intros ??. by inversion 1. Qed.

Instance InjLV_dec_range : DecRange InjLV.
Proof. intros v. case v; try (right; by inversion 1); left; by exists v0. Qed.
Instance InjRV_dec_range : DecRange InjRV.
Proof. intros v. case v; try (right; by inversion 1); left; by exists v0. Qed.

Lemma InjLV_case v : {w | v = InjLV w} + {∀ w, v ≠ InjLV w}.
Proof. by apply dec_range. Qed.
Lemma InjRV_case v : {w | v = InjRV w} + {∀ w, v ≠ InjRV w}.
Proof. by apply dec_range. Qed.

Instance InjLV_marker : Marker InjLV.
Proof. split. { by apply InjLV_inj. } { by apply InjLV_dec_range. } Qed.
Instance InjRV_marker : Marker InjRV.
Proof. split. { by apply InjRV_inj. } { by apply InjRV_dec_range. } Qed.

Instance InjLV_InjRV_disj_range : DisjRange InjLV InjRV.
Proof. by intros ?. Qed.
Instance InjRV_InjLV_disj_range : DisjRange InjRV InjLV.
Proof. by intros ?. Qed.
