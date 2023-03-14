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


Reserved Notation "|[ A ]|" (at level 5, A at next level).

Fixpoint styp2ttyp (A: typ) : ttyp :=
  match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_rcd (|| A ||) ttyp_bot ttyp_top
  | typ_base => ttyp_rcd (|| A ||) ttyp_base ttyp_top
  | typ_arrow B1 B2 => ttyp_rcd (|| A ||) ( ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)) ttyp_top
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

Definition styp2ttyp_raw (A: typ) : ttyp :=
  match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_bot
  | typ_base =>  ttyp_base
  | typ_arrow B1 B2 => ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)
  | typ_rcd l A' => |[ A' ]|
  | _ => ttyp_top (* for intersections *)
  end.

Notation "[[ A ]]" := (styp2ttyp_raw A) (at level 5, A at next level).


Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Proof with eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl...
Qed.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Admitted.


Lemma eqindextype_complete : forall A B,
    || A || = || B || -> eqIndTyp A B.
Proof with eauto.
  introv H.
  (* -> direction ? *)
Admitted.


Lemma eqindextype_sound : forall A B,
    eqIndTyp A B -> || A || = || B ||.
Proof with eauto.
  introv H. induction* H.
    + rewrite* IHeqIndTyp1.
    + simpl.
Admitted.

Lemma TEI_symm : forall A B,
    eqIndTypTarget A B -> eqIndTypTarget B A.
Proof with eauto.
  introv H. Admitted.
  (* indTypSize (size_typ A + size_typ B). induction* H. *)
  (* destruct* H. applys TEI_comm. *)
(* Qed. *)

Lemma TEI_trans : forall A B C,
    eqIndTypTarget A B -> eqIndTypTarget B C -> eqIndTypTarget A C.
Admitted.

Lemma eqIndTypTarget_concat_comm : forall A B,
    rec_typ A -> rec_typ B ->
    eqIndTypTarget (ttyp_concat_simpl A B) (ttyp_concat_simpl B A).
Proof with eauto.
  introv HA HB. gen B.
  induction* HA; intros; induction* HB; simpl...
  - simpl in IHHB.
    applys TEI_trans. applys TEI_rcd. admit.
(* applys TEI_refl. applys* IHHA. *)
(*     applys TEI_trans. simpl. apply TEI_comm. admit. *)
(*     applys TEI_rcd. applys TEI_refl. *)
(*     applys TEI_trans. applys TEI_rcd. *)
(*     2: applys TEI_symm; applys* IHHA. 2: applys* IHHB. *)
    (* eauto. *)
Admitted.

Lemma ttyp_concat_simpl_assoc : forall A B C,
    rec_typ A -> rec_typ B -> rec_typ C ->
    (ttyp_concat_simpl (ttyp_concat_simpl A B) C) = ttyp_concat_simpl A (ttyp_concat_simpl B C).
Proof with simpl in *; eauto.
  introv HRA HRB HRC.
  induction HRA...
  rewrite IHHRA...
Qed.


Lemma eqIndTypTarget_ttyp_concat_simpl : forall A1 A2 B1 B2,
    eqIndTypTarget A1 A2 -> eqIndTypTarget B1 B2 ->
    eqIndTypTarget (ttyp_concat_simpl A1 B1) (ttyp_concat_simpl A2 B2).
Proof with eauto using translate_to_record_types.
  introv HEA HEB. gen B1 B2.
  induction HEA; intros.
  - induction* At. simpl... admit.
  - applys TEI_trans.
    + forwards*: IHHEA1. + forwards*: IHHEA2.
  - applys* TEI_symm. admit.
  - simpl... admit.
  - admit.
  (* - simpl... applys TEI_trans. applys TEI_comm. applys H. applys* TEI_rcd. applys* TEI_rcd. *)
    (* induction* Ct. simpl... *)

  (* - simpl... applys TEI_trans. applys TEI_dup. applys* TEI_rcd. applys* TEI_rcd. *)
    (* induction* Ct. simpl... *)
Admitted.
(* Qed. *)

#[local] Hint Resolve TEI_symm : core.
Lemma translate_eqv : forall A B,
    eqIndTyp A B -> eqIndTypTarget |[ A ]| |[ B ]|.
Proof with eauto using translate_to_record_types.
  introv HE. lets HE': HE. induction* HE'.
  - forwards Heq: eqindextype_sound HE.
    (* unfolds styp2ttyp. rewrite Heq. simpl... *)
Admitted.
(*   - forwards Heq: eqindextype_sound HE. *)
(*     unfolds styp2ttyp. rewrite Heq. simpl... *)
(*   - simpl. forwards*: IHHE'. *)
(*     applys* eqIndTypTarget_ttyp_concat_simpl. (* label conflict checking *) *)
(*   - simpl. forwards Heq: eqindextype_sound HE. *)
(*     applys eqIndTypTarget_concat_comm... *)
(*   - simpl. rewrite* ttyp_concat_simpl_assoc... *)
(*   - simpl. rewrite* ttyp_trans_ord_top. *)
(*   - simpl. forwards*: IHHE'. (* dedup or not dedup *) admit. *)
(* Admitted. *)

#[local] Hint Constructors wf_typ : core.



(* Lemma lookup_concat_simpl_none : forall i A B, *)
(*     Tlookup l |[A]| = Some  -> rec_typ A -> *)
(*                     Tlookup i (ttyp_concat_simpl A B) = Tlookup i B. *)
(* Proof. *)
(*   introv LK HR. gen i B. *)
(*   induction A; intros; simpl; try solve_by_invert; eauto. *)
(*   - inverts* HR. inverts LK. case_if. *)
(*     forwards* Heq: IHA2. *)
(* Qed. *)


Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Proof with intuition eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl...
  - lets HR1: translate_to_record_types A1.
    lets HR2: translate_to_record_types A2.
    induction* HR1.
    + inverts* IHA1.
      forwards* HW: IHHR1.
      simpl...
      * forwards* Heq: lookup_concat_simpl H.
        rewrite H in Heq...
      * forwards* Heq: lookup_concat_simpl_none |[ A2 ]| H...
        applys WF_Rcd. 1-3: eauto...
Admitted.


Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> ~ toplike A -> exists B, |[A]| = (ttyp_rcd (||A||) B ttyp_top) /\ wf_typ B.
Admitted.

Lemma ttyp_trans_base :
|[typ_base]| = ttyp_rcd (||typ_base||) ttyp_base ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop_arrow : forall A' A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
|[(typ_arrow A' A)]| = ttyp_rcd (||typ_arrow A' A||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Admitted.

Lemma ttyp_trans_rcd : forall l A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
|[(typ_rcd l A)]| = ttyp_rcd (||(typ_rcd l A)||) |[A]| ttyp_top.
Admitted.

(* Lemma ttyp_trans_and : forall A B C, *)
(*     concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C. *)
(* Admitted. *)

(* Properties about type translation *)
Lemma concat_source_intersection : forall A B,
    concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Admitted.



Lemma eqIndTypTarget_wf_typ : forall A B,
    eqIndTypTarget A B -> wf_typ A -> wf_typ B.
Proof.
Admitted.

Lemma eqIndTypTarget_rec_typ : forall A B,
    eqIndTypTarget A B -> rec_typ A -> rec_typ B.
Proof.
Admitted.

Lemma eqIndTypTarget_lookup_none : forall A B l,
    eqIndTypTarget A B -> Tlookup l A = None -> Tlookup l B = None.
Proof.
Admitted.

Lemma eqIndTypTarget_lookup_some : forall A B l C,
    eqIndTypTarget A B -> Tlookup l A = Some C ->
    exists C', eqIndTypTarget C C' /\ Tlookup l B = Some C'.
Proof.
Admitted.

Lemma eqIndTypTarget_concat_typ : forall A B C A' B',
    concat_typ A B C -> eqIndTypTarget A A' -> eqIndTypTarget B B' ->
    exists C', concat_typ A' B' C' /\ eqIndTypTarget C C'.
Proof.
Admitted.

Lemma eqIndTypTarget_arrow_inv : forall A B C,
    eqIndTypTarget (ttyp_arrow A B) C -> exists C1 C2, C = ttyp_arrow C1 C2.
Proof with eauto.
  introv HE. inductions HE...
  (* - forwards* (?&?&?): IHHE1. subst*. *)
  (*   forwards* (?&?&?): IHHE2. *)
Admitted.

Lemma eqIndTypTarget_rcd_inv : forall l A B C1 C2,
    eqIndTypTarget (ttyp_rcd l A B) (ttyp_rcd l C1 C2) -> A = C1.
Proof with eauto.
  introv HE. inductions HE...
Admitted.

Lemma eqIndTypTarget_arrow_inv_1 : forall A B C1 C2,
    eqIndTypTarget (ttyp_arrow A B) (ttyp_arrow C1 C2) -> eqIndTypTarget A C1.
Proof with eauto.
  introv HE. inductions HE...
Admitted.

Lemma eqIndTypTarget_arrow_inv_2 : forall A B C1 C2,
    eqIndTypTarget (ttyp_arrow A B) (ttyp_arrow C1 C2) -> eqIndTypTarget B C2.
Proof with eauto.
  introv HE. inductions HE...
Admitted.
