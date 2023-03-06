Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.


Reserved Notation "|[ A ]|" (at level 5, A at next level).

Fixpoint styp2ttyp (A: typ) : ttyp := ttyp_base
where "|[ A ]|" := (styp2ttyp A).

Notation "|| A ||" := (type2index A) (at level 1, A at next level). (* too high *)

(* Properties of translation (to type index) functions *)
(* Lemma tindex_trans_arrow : forall A B, *)
(*     || (typ_arrow A B) || = ti_arrow || B ||. *)
(* Admitted. *)
(* Lemma tindex_trans_rcd : forall l A, *)
(*     || (typ_rcd l A) || = ti_rcd l || A ||. *)
(* Admitted. *)

(* Properties of translation (to target type) functions *)

Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Admitted.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> ~ toplike A -> exists B, |[A]| = ttyp_rcd ||A|| B ttyp_top /\ wf_typ B.
Admitted.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd ||typ_base|| ttyp_base ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop_arrow : forall A A',
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_arrow A' A)]| = ttyp_rcd (ti_arrow || A ||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Admitted.

Lemma ttyp_trans_rcd : forall l A,
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_rcd l A)]| = ttyp_rcd (ti_rcd l || A ||) |[A]| ttyp_top.
Admitted.

Lemma ttyp_trans_and : forall A B C,
    concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C.
Admitted.

(* Properties about type translation *)
Lemma concat_source_intersection : forall A B,
    concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Admitted.

Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Admitted.
