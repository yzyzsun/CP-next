Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.

Lemma TEI_dup : forall (ll:tindex) (At Bt Ct Ct' At':ttyp),
     rec_typ Ct ->
      (   (  Tlookup  ll   Ct  = Some  At'   /\  eqIndTypTarget At' At )    \/   Tlookup  ll   Ct  = None  )  ->
     eqIndTypTarget At Bt ->
     eqIndTypTarget (ttyp_rcd ll Bt  (ttyp_rcd ll At Ct) ) Ct' ->
     eqIndTypTarget (ttyp_rcd ll At  (ttyp_rcd ll Bt Ct) ) Ct'.
Admitted.

Lemma lookup_wf_typ_1 : forall l T At l',
    Tlookup l' (ttyp_rcd l T At) = Tlookup l' At \/ l = l'.
Proof.
  introv. simpl. case_if*.
Qed.

Lemma lookup_wf_typ_2 : forall l T At Bt,
    wf_typ (ttyp_rcd l T At) -> Tlookup l At = Some Bt -> eqIndTypTarget Bt T.
Proof.
  introv WF LK. inverts WF. destruct H5.
  all: rewrite LK in H; inverts* H.
  inverts* H0.
Qed.


Lemma wf_typ_look_up_wf : forall l At Bt,
    Tlookup l At = Some Bt -> wf_typ At -> wf_typ Bt.
Proof with eauto.
  introv Heq WF. gen l Bt.
  induction WF; intros; try solve_by_invert.
  inverts Heq. case_if*.
  - inverts* H2.
Qed.

Ltac unify_lookup :=
      destruct_disj; destruct_conj;
      repeat lazymatch goal with
    | |- Some _ = Some _  => try reflexivity
    | H : Some _ = None |- _ => inverts H
    | H : Some _ = Some _ |- _ => inverts H
    | H1 : ?A = Some _ , H2 : ?A = Some _ |- _ => rewrite H1 in H2
    | H1 : ?A = Some _ , H2 : ?A = None |- _ => rewrite H1 in H2
    | H : Tlookup ?l (ttyp_rcd ?l ?A ?C) = _ |- _ =>
        simpl in H; case_if
    | H : Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ |- _ =>
        let Heq := fresh "Heq" in
        lets [Heq|Heq]: lookup_wf_typ_1 l A C r;
        [ rewrite Heq in H; clear Heq | subst ]
    | H: ?l <> ?r |- Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
    | H: ?r <> ?l |- Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
    | |- Tlookup ?l (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
        end.


Ltac destruct_lookup H :=
      match type of H with
    | Tlookup ?l (ttyp_rcd ?l ?A ?C) = _  =>
        simpl in H; case_if
    | Tlookup ?r (ttyp_rcd ?l ?A ?C) = _  =>
        let Heq := fresh "Heq" in
        lets [Heq|Heq]: lookup_wf_typ_1 l A C r;
        [ rewrite Heq in H; clear Heq | subst ]
      end.


(* TEI eqIndTypTarget *)
#[local] Hint Unfold Tlookup : core.

Lemma wf_rcd_lookup : forall i T Ti,
  wf_typ T ->
  Tlookup i T = Some Ti ->
  wf_typ Ti.
Proof.
  introv WF LK.
  gen i Ti.
  induction WF; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H2.
Qed.

Lemma rcd_typ_concat_1 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T1.
Proof.
  introv CT. induction* CT.
Qed.

Lemma rcd_typ_concat_2 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T2.
Proof.
  introv CT. induction* CT.
Qed.

Lemma rcd_typ_concat_3 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T3.
Proof.
  introv CT. induction* CT.
Qed.

Lemma lookup_concat_typ : forall i A B C T,
    Tlookup i A = Some T ->
    concat_typ A B C ->
    Tlookup i C = Tlookup i A.
Proof.
  introv LK CC. gen i T B C.
  induction A; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H0. inverts* CC.
    subst. unfolds. case_if*.
  - inverts* CC.
    forwards~ : IHA2 H0 H6.
    unfolds. case_if*.
Qed.


Lemma lookup_concat_typ_none : forall i A B C,
    Tlookup i A = None ->
    concat_typ A B C ->
    Tlookup i C = Tlookup i B.
Proof.
  introv LK CC. gen i B C.
  induction A; intros; inverts* CC.
  - inverts* LK; case_if.
    forwards* Heq: IHA2 H0 H5.
    rewrite <- Heq.
    unfolds. case_if*.
Qed.

Ltac lookup_concat l HC :=
  match type of HC with
  | concat_typ ?A ?B ?C => let Heq := fresh "Heq" in
                           match goal with
                           | H: Tlookup l A = Some _ |- _ =>
                               forwards Heq: lookup_concat_typ H HC;
                               rewrite H in Heq
                           | H: Tlookup l A = None, H2: Tlookup l B = _ |- _ =>
                               forwards Heq: lookup_concat_typ_none H HC;
                               rewrite H2 in Heq
                           end
  end.

Lemma eqIndTypTarget_rec_typ : forall A B,
    eqIndTypTarget A B -> rec_typ B -> rec_typ A.
Proof with eauto.
  introv HE HR. gen A. inductions HR; intros; inverts* HE.
Qed.

Lemma eqIndTypTarget_rec_typ_2 : forall A B,
    eqIndTypTarget A B -> rec_typ A -> rec_typ B.
Proof with eauto.
  introv HE. induction HE; intros... inverts* H.
Qed.

Lemma TEI_refl : forall At,
    wf_typ At -> eqIndTypTarget At At.
Proof with eauto.
  introv WF. induction* WF.
Qed.

Lemma eqIndTypTarget_arrow_inv : forall A B C,
    eqIndTypTarget (ttyp_arrow A B) C -> exists C1 C2, C = ttyp_arrow C1 C2.
Proof with eauto.
  introv HE. inductions HE...
Qed.


Lemma eqIndTypTarget_arrow_inv_1 : forall A B C1 C2,
    eqIndTypTarget (ttyp_arrow A B) (ttyp_arrow C1 C2) -> eqIndTypTarget A C1.
Proof with eauto.
  introv HE. inductions HE...
Qed.


Lemma eqIndTypTarget_arrow_inv_2 : forall A B C1 C2,
    eqIndTypTarget (ttyp_arrow A B) (ttyp_arrow C1 C2) -> eqIndTypTarget B C2.
Proof with eauto.
  introv HE. inductions HE...
Qed.


Lemma eqIndTypTarget_arrow_inv_3 : forall A B C,
    eqIndTypTarget C (ttyp_arrow A B) -> exists C1 C2, C = ttyp_arrow C1 C2.
Proof with eauto; try solve_by_invert.
  introv HE. inductions HE...
  - forwards* (?&?&?): IHHE...
Qed.

Lemma TEI_symm : forall A B,
    eqIndTypTarget A B -> eqIndTypTarget B A.
Proof with eauto.
  introv HE. induction* HE.
  (* - applys TEI_comm. inverts IHHE. *)
  (*   unify_lookup. inverts H12. Print TEI_refl. *)

Admitted.
  (* indTypSize (size_typ A + size_typ B). induction* H. *)
  (* destruct* H. applys TEI_comm. *)
(* Qed. *)

Lemma TEI_cons : forall l A B A' B',
    eqIndTypTarget A A' -> eqIndTypTarget B B' ->
    wf_typ (ttyp_rcd l A B) -> wf_typ (ttyp_rcd l A' B') ->
    eqIndTypTarget (ttyp_rcd l A B) (ttyp_rcd l A' B').
Proof with eauto using eqIndTypTarget_rec_typ, TEI_symm.
  introv HEa HEb HWa HWb.
  inverts HWa. inverts HWb. econstructor...
Qed.

Lemma TEI_trans : forall A B C,
    eqIndTypTarget A B -> eqIndTypTarget B C -> eqIndTypTarget A C.
Proof with eauto.
  introv HEa HEb. induction* HEa.

    (* apply TEI_symm in H0. forwards(?&?&?): eqIndTypTarget_arrow_inv_3 H0. subst. *)
    (* forwards : eqIndTypTarget_arrow_inv_1 H0. forwards : eqIndTypTarget_arrow_inv_2 H0. *)
    (* apply TEI_symm in H0. forwards(?&?&?): eqIndTypTarget_arrow_inv_3 H0. subst. *)
    (* forwards : eqIndTypTarget_arrow_inv_1 H0. forwards : eqIndTypTarget_arrow_inv_2 H0. *)
Admitted.

Lemma eqindtyptarget_wf_typ_1 : forall At Bt,
    eqIndTypTarget At Bt -> wf_typ At.
Proof with eauto.
  introv HS. induction* HS.
  - inverts* IHHS. inverts H7. inverts H8.
    unify_lookup.
    +
      econstructor...
      left; split; unify_lookup; tassumption.
    +
      econstructor...
      left; split; unify_lookup; tassumption.
    +
      econstructor...
      right; unify_lookup; tassumption.
    +
      econstructor...
      right; unify_lookup; tassumption.
  (* - inverts* IHHS2. inverts H5. inverts H6. *)
  (*   unify_lookup. *)
  (*   econstructor... econstructor... *)
  (*   left; split*. eauto using TEI_trans. *)
  (*   left; split. unify_lookup. eauto using TEI_trans, TEI_symm. *)
  (*   econstructor... *)
  (*   left; split. unify_lookup. eauto using TEI_trans, TEI_symm. *)
      (*   Unshelve. all: eauto. *)
      Unshelve. all: eauto.
Qed.

Lemma eqindtyptarget_wf_typ_2 : forall At Bt,
    eqIndTypTarget At Bt -> wf_typ Bt.
Proof.
  introv H. apply TEI_symm in H. eauto using eqindtyptarget_wf_typ_1.
Qed.

Lemma wf_rcd_concat : forall T1 T2 T3,
    wf_typ T1 -> wf_typ T2 ->
    rec_typ T1 -> rec_typ T2 ->
    concat_typ T1 T2 T3 ->
    wf_typ T3.
Proof with eauto using rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv WF1 WF2 RT1 RT2 CT.
  induction* CT.
  - inverts* WF1. inverts* RT1...
    destruct H6 as [(?&?)|?].
    + forwards* Heq: lookup_concat_typ H0 CT.
      rewrite H0 in Heq... intuition eauto; econstructor...
    + forwards* Heq: lookup_concat_typ_none H0 CT.
      destruct H as [(H'&?) | H']; rewrite H' in Heq; econstructor...
      Unshelve. all: eauto.
Qed.

Lemma eqindtyptarget_concat_1 : forall T A B C,
    concat_typ A B C -> eqIndTypTarget T A -> wf_typ B -> rec_typ B ->
    exists C', concat_typ T B C' /\ eqIndTypTarget C' C.
Proof with eauto using TEI_symm, TEI_refl, TEI_trans.
  introv HC HE HW HR. gen B C.
  induction HE; intros; try solve_by_invert.
  - exists. split*. forwards*: wf_rcd_concat HC.
    eauto...
  - inverts HC. forwards~ (?&?&?): IHHE2 H9.
    destruct_conj. exists. split.
    econstructor. { destruct H8 as [(?&?)|?]. intuition eauto... right*. }
    eassumption. applys~ TEI_cons.
    all: unify_lookup.
    all: econstructor.
    all: eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2,
        wf_rcd_concat, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
    all: try lookup_concat ll H9; try lookup_concat ll H3...
  - forwards* (?&?&?): IHHE. inverts H3. inverts H11.
    exists. split.
    all: unify_lookup; lookup_concat ll1 H12; lookup_concat ll2 H12;
      econstructor...
    all: eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2,
        wf_rcd_concat, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  (* - forwards* (?&?&?): IHHE2. inverts keep H1. inverts H9. *)
  (*   unify_lookup; lookup_concat ll H11... *)
  (*   all: exists; split. *)
  (*   1,3,5,7: econstructor; try solve [right*]; try solve [left*]. *)
  (*   1-4: econstructor; try solve [right*]; try solve [left*]... *)
  (*   all: applys TEI_dup H2. *)
  (*   all: try solve [right*]; try solve [left*]... *)
  (*   all: eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2, *)
  (*       wf_rcd_concat, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3. *)
    Unshelve. all: econstructor.
Qed.


Lemma eqIndTypTarget_lookup_none : forall A B l,
    eqIndTypTarget A B -> Tlookup l A = None -> Tlookup l B = None.
Proof.
Admitted.

Lemma eqIndTypTarget_lookup_some : forall A B l C,
    eqIndTypTarget A B -> Tlookup l A = Some C ->
    exists C', eqIndTypTarget C C' /\ Tlookup l B = Some C'.
Proof.
Admitted.

Ltac lookup_eq l HE :=
  match type of HE with
  | eqIndTypTarget ?A ?B => let Heq := fresh "Heq" in
                            match goal with
                            | H: Tlookup l A = Some _ |- _ =>
                                forwards (?&?&Heq): eqIndTypTarget_lookup_some HE H
                            (* rewrite H in Heq *)
                            | H: Tlookup l A = None|- _ =>
                                forwards Heq: eqIndTypTarget_lookup_none HE H
                            | H: Tlookup l B = Some _ |- _ =>
                                apply TEI_symm in HE;
                                forwards (?&?&Heq): eqIndTypTarget_lookup_some HE H
                            (* rewrite H in Heq *)
                            | H: Tlookup l B = None|- _ =>
                                apply TEI_symm in HE;
                                forwards Heq: eqIndTypTarget_lookup_none HE H
                            end
  end.


Lemma eqindtyptarget_concat_2 : forall T A B C,
    concat_typ A B C -> eqIndTypTarget T B -> wf_typ A -> rec_typ A ->
    exists C', concat_typ A T C' /\ eqIndTypTarget C' C.
Proof with eauto using TEI_symm, TEI_refl, TEI_trans,
    rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv HC HE HW HR. gen B C T.
  induction HR; intros.
  - inverts HC. exists. split.
    econstructor. eauto using TEI_symm, eqIndTypTarget_rec_typ.
    eauto.
  - inverts HC. inverts HW. forwards~ (?&?&?): IHHR H5 HE.
    unify_lookup; try lookup_eq ll HE; try lookup_concat ll H5; try lookup_eq ll H0.
    + exists. split. econstructor... applys TEI_cons...
      { econstructor... applys wf_rcd_concat H...
        eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
      { econstructor... eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
    + exists. split. econstructor... applys TEI_cons...
      { econstructor... applys wf_rcd_concat H...
        eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
      { econstructor... eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
    + exists. split. econstructor... applys TEI_cons...
      { econstructor... applys wf_rcd_concat H...
        eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
      { econstructor... eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
    + exists. split. econstructor... applys TEI_cons...
      { econstructor... applys wf_rcd_concat H...
        eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
      { econstructor... eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2. }
      Unshelve. all: econstructor.
Qed.

Lemma eqindtyptarget_concat : forall T1 T2 A1 A2 B,
    eqIndTypTarget T1 A1 -> eqIndTypTarget T2 A2 -> concat_typ A1 A2 B ->
    exists C, concat_typ T1 T2 C /\ eqIndTypTarget C B.
Proof with eauto using TEI_symm, TEI_refl, TEI_trans,
    eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2,
    rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv HE1 HE2 HC.
  forwards (?&?&?): eqindtyptarget_concat_1 HC HE1...
  forwards (?&?&?): eqindtyptarget_concat_2 H HE2...
Qed.


(* Lemma eqIndTypTarget_rcd_inv : forall l A B C1 C2, *)
(*     eqIndTypTarget (ttyp_rcd l A B) (ttyp_rcd l C1 C2) -> eqIndTypTarget A C1. *)
(* Proof with eauto. *)
(*   introv HE. inductions HE... *)
(*   - applys IHHE. *)
(* Admitted. *)


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
  | typ_bot => ttyp_bot
  | typ_base =>  ttyp_base
  | typ_arrow B1 B2 => ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)
  | typ_rcd l A' => |[ A' ]|
  | _ => ttyp_top (* for top and intersections *)
  end.

Notation "[[ A ]]" := (styp2ttyp_raw A) (at level 5, A at next level).

Lemma translate_types : forall A,
    A = typ_top \/ exists A1 A2, A = typ_and A1 A2 \/ |[ A ]| = ttyp_rcd (|| A ||) ([[ A ]]) ttyp_top.
Proof with eauto.
  introv. induction* A.
  Unshelve. all: econstructor.
Qed.

Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Proof with eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl...
Qed.

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
      * forwards* Heq: lookup_concat_simpl H0.
        rewrite H0 in Heq...
      * forwards* Heq: lookup_concat_simpl_none |[ A2 ]| H...
        applys* WF_Rcd. eauto...
Admitted.

Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> ~ toplike A -> exists B, |[A]| = (ttyp_rcd (||A||) B ttyp_top) /\ wf_typ B.
Proof with eauto using ttyp_trans_wf.
  introv HO HT. induction* HO;
    try solve [exfalso; applys* HT].
  - exists. split*. simpl...
  - forwards (?&?&?): IHHO. introv HB. applys* HT.
    exists. simpl. split*. econstructor...
  - forwards (?&?&?): IHHO. introv HB. applys* HT.
    exists. simpl. split*...
Qed.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd (||typ_base||) ttyp_base ttyp_top.
Proof with eauto.
  introv. simpl...
Qed.

Lemma ttyp_trans_ord_ntop_arrow : forall A' A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_arrow A' A)]| = ttyp_rcd (||typ_arrow A' A||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Proof with eauto.
  introv. simpl...
Qed.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Proof with simpl; eauto.
  introv HT. induction HT...
  - rewrite IHHT1. rewrite IHHT2...
  - rewrite IHHT...
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




Lemma ttyp_trans_rcd : forall l A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
|[(typ_rcd l A)]| = ttyp_rcd (||(typ_rcd l A)||) |[A]| ttyp_top.
Admitted.

(* Lemma ttyp_trans_and : forall A B C, *)
(*     concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C. *)
(* Admitted. *)


Lemma eqIndTypTarget_concat_typ : forall A B C A' B',
    concat_typ A B C -> eqIndTypTarget A A' -> eqIndTypTarget B B' ->
    exists C', concat_typ A' B' C' /\ eqIndTypTarget C C'.
Proof.
Admitted.

Fixpoint context_trans (G:ctx) : tctx :=
  match G with
  | [] => []
  | (x, A) :: l => (x, |[A]|) :: (context_trans l)
  end.

Notation "||[ G ]||" := (context_trans G) (at level 1, G at next level).


Lemma elaboration_wf_ctx : forall G,
    uniq G  -> wf_ctx ||[G]||.
Admitted.



(* Properties about type translation *)
Lemma concat_source_intersection : forall A B,
    concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Admitted.


Lemma eqIndTypTarget_ttyp_concat_simpl : forall A1 A2 B1 B2,
    eqIndTypTarget A1 A2 -> eqIndTypTarget B1 B2 ->
    eqIndTypTarget (ttyp_concat_simpl A1 B1) (ttyp_concat_simpl A2 B2).
Proof with eauto using translate_to_record_types.
  introv HEA HEB. gen B1 B2.
  induction HEA; intros.
  1-3: simpl...
  - applys TEI_trans.
    + forwards*: IHHEA1. + forwards*: IHHEA2.
  - applys* TEI_symm. admit.
  - simpl... admit.
(*   - admit. *)
(*   (* - simpl... applys TEI_trans. applys TEI_comm. applys H. applys* TEI_rcd. applys* TEI_rcd. *) *)
(*     (* induction* Ct. simpl... *) *)

(*   (* - simpl... applys TEI_trans. applys TEI_dup. applys* TEI_rcd. applys* TEI_rcd. *) *)
(*     (* induction* Ct. simpl... *) *)
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

Definition subtype_wrt_lookup At Bt :=
  rec_typ At /\ rec_typ Bt /\ wf_typ At /\ wf_typ Bt /\ forall l B, Tlookup l Bt = Some B -> exists A, Tlookup l At = Some A /\ eqIndTypTarget A B.


Lemma subtypespec_refl : forall At,
    rec_typ At -> wf_typ At -> subtype_wrt_lookup At At.
Proof.
  introv HR HW. induction* HW; try solve_by_invert.
  all: unfolds; splits*; introv HL; try solve_by_invert.
  exists. split*. eauto using TEI_refl, wf_typ_look_up_wf.
Qed.

Lemma subtypespec_trans : forall At Bt Ct,
    subtype_wrt_lookup At Bt -> subtype_wrt_lookup Bt Ct ->
    subtype_wrt_lookup At Ct.
Proof with eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2.
  introv HA HB. unfold subtype_wrt_lookup in *.
  destruct_conj.
  splits... introv HL.
  forwards* (?&?&?): H3. forwards* (?&?&?): H8.
  intuition eauto using TEI_trans.
Qed.


Lemma subtypespec_andl : forall A B, subtype_wrt_lookup |[typ_and A B]| |[A]|.
Admitted.

Lemma subtypespec_andr : forall A B, subtype_wrt_lookup |[typ_and A B]| |[B]|.
Admitted.
