Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.


(* Source types to type indexes *)
Notation "|| A ||" := (type2index A) (at level 50, A at next level). (* 1 is too high *)


(* Concatenate two record types without any checking *)

Fixpoint ttyp_concat_simpl (A: ttyp) (B: ttyp) :=
  match A with
  | ttyp_top => B
  | ttyp_rcd l At Bt => ttyp_rcd l At (ttyp_concat_simpl Bt B)
  | _ => ttyp_top
  end.

Lemma lookup_concat_simpl : forall i A B T,
    Tlookup i A = Some T ->
    Tlookup i (ttyp_concat_simpl A B) = Tlookup i A.
Proof.
  introv LK. gen i T B.
  induction A; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H0.
    subst. simpl. case_if*.
  - simpl. case_if*.
Qed.


Lemma lookup_concat_simpl_none : forall i A B,
    Tlookup i A = None -> rec_typ A ->
    Tlookup i (ttyp_concat_simpl A B) = Tlookup i B.
Proof.
  introv LK HR. gen i B.
  induction A; intros; simpl; try solve_by_invert; eauto.
  - inverts* HR. inverts LK. case_if.
    forwards* Heq: IHA2.
Qed.

Lemma rcd_typ_concat_simpl : forall T1 T2,
    rec_typ T1 -> rec_typ T2 ->
    rec_typ (ttyp_concat_simpl T1 T2).
Proof with eauto.
  introv WF1 WF2.
  induction WF1...
  - simpl...
Qed.

(* Source types to target types *)

Reserved Notation "[[ A ]]" (at level 5, A at next level).

Fixpoint styp2ttyp_raw (A: typ) : ttyp :=
  match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_bot
  | typ_base =>  ttyp_base
  | typ_arrow B1 B2 => ttyp_arrow ([[ B1 ]]) ([[ B2 ]])
  | _ => ttyp_top (* for rcd and intersections *)
  end
where "[[ A ]]" := (styp2ttyp_raw A).

Reserved Notation "|[ A ]|" (at level 5, A at next level).

Fixpoint styp2ttyp (A: typ) : ttyp :=
  match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_rcd (|| A ||) [[ A ]] ttyp_top
  | typ_base => ttyp_rcd (|| A ||) [[ A ]] ttyp_top
  | typ_arrow B1 B2 => ttyp_rcd (|| A ||) [[ A ]] ttyp_top
  | typ_rcd l A' => ttyp_rcd (|| A ||) (|[ A' ]|) ttyp_top
  | typ_and A1 A2 => ttyp_concat_simpl (|[ A1 ]|) (|[ A2 ]|)
  end
where "|[ A ]|" := (styp2ttyp A).

(* Fixpoint styp2ttyp (A: typ) : ttyp := *)
(*   match A with *)
(*   | typ_top => ttyp_top *)
(*   | typ_bot => ttyp_rcd (|| A ||) ttyp_bot ttyp_top *)
(*   | typ_base => ttyp_rcd (|| A ||) ttyp_base ttyp_top *)
(*   | typ_arrow B1 B2 => ttyp_rcd (|| A ||) (ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)) ttyp_top *)
(*   | typ_rcd l A' => ttyp_rcd (|| A ||) (|[ A' ]|) ttyp_top *)
(*   | typ_and A1 A2 => ttyp_concat_simpl (|[ A1 ]|) (|[ A2 ]|) *)
(*   end *)
(* where "|[ A ]|" := (styp2ttyp A). *)


(* Properties of translation (to type index) functions *)
(* Lemma tindex_trans_arrow : forall A B, *)
(*     || (typ_arrow A B) || = ti_arrow || B ||. *)
(* Admitted. *)
(* Lemma tindex_trans_rcd : forall l A, *)
(*     || (typ_rcd l A) || = ti_rcd l || A ||. *)
(* Admitted. *)

(* Properties of translation (to target type) functions *)

#[local] Hint Constructors wf_typ : core.


Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Proof with eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl...
Qed.

Lemma lookup_concat_simpl_none : forall i A B,
    Tlookup l |[A]| = Some  -> rec_typ A ->
    Tlookup i (ttyp_concat_simpl A B) = Tlookup i B.
Proof.
  introv LK HR. gen i B.
  induction A; intros; simpl; try solve_by_invert; eauto.
  - inverts* HR. inverts LK. case_if.
    forwards* Heq: IHA2.
Qed.


Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Proof with intuition eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl...
  - lets HR1: translate_to_record_types A1.
    lets HR2: translate_to_record_types A2.
    induction* HR1.
    + inverts* IHA1.
      simpl...
      * forwards* Heq: lookup_concat_simpl H.
        rewrite H in Heq...
      * forwards* Heq: lookup_concat_simpl_none |[ A2 ]| H...
        rewrite H in Heq...
        applys* WF_Rcd...
Admitted.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> ~ toplike A -> exists B, |[A]| = (ttyp_rcd (||A||) B ttyp_top) /\ wf_typ B.
Admitted.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd (||typ_base||) ttyp_base ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop_arrow : forall A A',
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_arrow A' A)]| = ttyp_rcd (||typ_arrow A' A||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Admitted.

Lemma ttyp_trans_rcd : forall l A,
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_rcd l A)]| = ttyp_rcd (||(typ_rcd l A)||) |[A]| ttyp_top.
Admitted.

Lemma ttyp_trans_and : forall A B C,
    concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C.
Admitted.

(* Properties about type translation *)
Lemma concat_source_intersection : forall A B,
    concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Admitted.
