Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Require Import StructTact.StringOrders.
Import IfNotations.
Require Export syntax_ott.
Require Export Infrastructure.

Lemma TEI_dup : forall (ll:string) (At Bt Ct Ct' At':ttyp),
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

Lemma lookup_wf_typ_3 : forall l T At l',
    l = l' -> Tlookup l (ttyp_rcd l' T At) = Some T.
Proof.
  introv HE. subst. simpl. case_if*.
Qed.

Lemma wf_typ_look_up_wf : forall l At Bt,
    Tlookup l At = Some Bt -> wf_typ At -> wf_typ Bt.
Proof with eauto.
  introv Heq WF. gen l Bt.
  induction WF; intros; try solve_by_invert.
  inverts Heq. case_if*.
  - inverts* H2.
Qed.

#[local] Hint Resolve lookup_wf_typ_2 lookup_wf_typ_3 wf_typ_look_up_wf : core.

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
(* #[local] Hint Unfold Tlookup : core. *)

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
    all: unify_lookup; lookup_concat l1 H12; lookup_concat l2 H12;
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


(* Properties of translation (to target type) functions *)

Definition styp2ttyp_raw (A: typ) : ttyp :=
  if (check_toplike A) then ttyp_top
  else match A with
  | typ_bot => ttyp_bot
  | typ_base =>  ttyp_base
  | typ_arrow B1 B2 => ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)
  | typ_rcd l A' => |[ A' ]|
  | _ => ttyp_top (* for top and intersections *)
  end.

Notation "[[ A ]]" := (styp2ttyp_raw A) (at level 5, A at next level).

(* Lemma translate_types : forall A, *)
(*     check_toplike A = false -> (exists A1 A2, A = typ_and A1 A2) \/ |[ A ]| = ttyp_rcd (|| A ||) ([[ A ]]) ttyp_top. *)
(* Proof with eauto. *)
(*   introv HC. induction* A; simpl in HC; try discriminate. *)
(*   - right*. simpl. case_if*. reflexivity. forwards* [(?&?&IH)|IH]: IHA2. forwards* [(?&?&IH')|IH']: IH. *)

(*     s . right. exists*. right. simpl. *)
(*   Unshelve. all: econstructor. *)
(* Qed. *)

Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Proof with eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl; try case_if; simpl...
Qed.

Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Proof with intuition eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl; repeat case_if; simpl...
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
    ord A -> check_toplike A = false -> exists B, |[A]| = (ttyp_rcd (||A||) B ttyp_top) /\ wf_typ B.
Proof with eauto using ttyp_trans_wf.
  introv HO HT. induction* HO;
    try solve [simpl in HT; discriminate].
  - exists. split*. simpl...
  - simpl in HT. forwards* (?&?&?): IHHO.
    exists. simpl. case_if. split*. econstructor...
  - simpl in HT. forwards* (?&?&?): IHHO.
    exists. simpl. case_if. split*...
Qed.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd (||typ_base||) ttyp_base ttyp_top.
Proof with eauto.
  introv. simpl...
Qed.

Lemma ttyp_trans_ord_ntop_arrow : forall A' A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    check_toplike A = false -> |[(typ_arrow A' A)]| = ttyp_rcd (||typ_arrow A' A||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Proof with eauto.
  introv HT. simpl in HT. simpl. case_if*.
Qed.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Proof with simpl; eauto.
  introv HT.
  (* - rewrite IHHT1. rewrite IHHT2... *)
  (* - rewrite IHHT... *)
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
  | nil => nil
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
  Unshelve. eauto.
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

(* originally in source5 *)

(* Properties on merge *)
Locate merge.
Module Import NSort := Sort NTTLB.
Lemma merge_empty : forall l,
    merge nil l = l.
Proof.
  introv. induction* l.
Qed.

Lemma merge_empty_r : forall l,
    merge l nil = l.
Proof.
  introv. induction* l.
Qed.

#[local] Hint Rewrite merge_empty merge_empty_r : merge.

Lemma merge_cons : forall a l b r,
    merge (a::l) (b::r) =
      if if proj1_sig (string_compare_lex a b) is Gt then false else true then a :: merge l (b::r) else b :: merge (a::l) r.
Proof with eauto.
  introv. induction* l; destruct (proj1_sig (string_compare_lex a b)); autorewrite with merge...
Qed.

#[local] Hint Rewrite merge_cons : merge.


(** * Multisets *)
From Coq Require Import FunctionalExtensionality.
Definition multiset := string -> nat.

(** The [empty] multiset has multiplicity [0] for every value. *)

Definition empty : multiset :=
  fun x => 0.

(** Multiset [singleton v] contains only [v], and exactly once. *)

Definition singleton (v: string) : multiset :=
  fun x => if x =? v then 1 else 0.

(** The union of two multisets is their _pointwise_ sum. *)

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.

Lemma union_assoc: forall a b c : multiset,
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfolds. eauto using Nat.add_assoc.
Qed.

Lemma union_comm: forall a b : multiset,
   union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfolds. eauto using Nat.add_comm.
Qed.

Lemma union_swap : forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros.
  extensionality x.
  unfolds. lia.
Qed.


Fixpoint contents (al: list string) : multiset :=
  match al with
  | nil => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

Lemma contents_inv : forall a bl,
    contents (a :: bl) = union (singleton a) (contents bl).
Proof.
  introv. eauto.
Qed.

Ltac indListSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : list _ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

(* prove merge is a permutation *)
Theorem merge_contents: forall a b,
    union (contents a) (contents b) = contents (merge a b).
Proof.
  intros. extensionality x. indListSize (length a + length b).
  destruct a; destruct b; autorewrite with merge.
  (* induction a; induction b; autorewrite with merge. *)
  1-3: unfolds; simple*.
  case_if.
  - simpl. unfold union. rewrite <- IH.
    unfold union. rewrite (contents_inv s0 b). unfold union.
    all: simpl in *; lia.
  - repeat rewrite (contents_inv s0 _). unfold union. rewrite <- IH.
    { unfold union. lia. }
    simpl in *; lia.
Qed.


Require Import Ascii.
Lemma ascii_compare_refl : forall t : ascii, (t ?= t)%char = Eq.
Proof.
  intro t. destruct t.
  unfold Ascii.compare; simpl. rewrite* BinNat.N.compare_refl.
Qed.

Lemma string_compare_refl : forall s1 : string, (s1 ?= s1) = Eq.
Proof.
  intros. induction* s1.
  simpl. rewrite IHs1. rewrite* ascii_compare_refl.
Qed.

Check NTTLB.leb_trans.
(* Lemma new_leb_string_transitive : forall s1 s2 s3 : string, *)
(*   (s1 <=? s2) = true -> (s2 <=? s3) = true -> (s1 <=? s3) = true. *)
(* Proof. *)
(*   intros s1 s2 s3 H1 H2. *)
(*   pose proof NTTLB.leb_trans. unfolds in H. applys H. *)
(*   unfolds. unfolds in H1. unfolds in H2. *)
(*   destruct (s1 ?= s2) eqn:E1; try discriminate; *)
(*     destruct (s2 ?= s3) eqn:E2; try discriminate. *)
(*   all: try apply String_as_OT.cmp_eq in E1. *)
(*   all: try apply String_as_OT.cmp_eq in E2. *)
(*   all: subst*. *)
(*   1: now rewrite* string_compare_refl. *)
(*   1: now rewrite* E2. *)
(*   1: now rewrite* E1. *)
(*   Print NTTLB. *)
(*   forwards: NTTLB.lt_trans s1 s2 s3. *)
(*   unfolds. *)
(*   all: try apply String_as_OT.cmp_lt in E1. *)
(*   all: try apply String_as_OT.cmp_lt in E2. *)
(*   all: try forwards H: String_as_OT.lt_trans E1 E2. *)
(*   all: try rewrite <- String_as_OT.cmp_lt in H. *)
(*   1: rewrite* H; simpl. *)

(* Qed. *)

(* no duplication sorted *)

Definition sorted := Sorted lex_lt.

Theorem sorted_unique : forall (l1 l2 : list string),
    sorted l1 -> sorted l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  introv HS1 HS2 HP.
  applys* Sort_In_eq lex_lt.
  applys lex_lt_trans.
  applys lex_lt_not_eq.
  split; introv HI;
    eauto using Permutation_sym, Permutation_in.
Qed.

Theorem merge_comm : forall (l1 l2 : list string),
    sorted l1 -> sorted l2 ->
    merge l1 l2 = merge l2 l1.
    (* nodup string_dec (merge l1 l2) = nodup string_dec (merge l2 l1). *)
Proof.
  introv HS1 HS2.
  applys* Sort_In_eq lex_lt.
  admit.
  applys lex_lt_not_eq.
  admit. admit.
  admit.
  (* - lets HP: Permuted_merge. *)
  (*   split; introv HI; applys nodup_In; apply nodup_In in HI; *)
  (*     applys Permutation_in HP. *)
  (*   all: applys in_app_iff; applys or_comm; applys in_app_iff. *)
  (*   all: applys Permutation_in HI; applys* Permutation_sym HP. *)
Admitted.

(* Search Sorted. *)
(* Admitted. *)
(*   Search Permutation. *)
(*   admit. admit. *)
(*   - lets HP: Permuted_merge. *)
(*     split; introv HI; applys nodup_In; apply nodup_In in HI; *)
(*       applys Permutation_in HP. *)
(*     all: applys in_app_iff; applys or_comm; applys in_app_iff. *)
(*     all: applys Permutation_in HI; applys* Permutation_sym HP. *)
(* Admitted. *)

(*     nodup string_dec (merge l1 l2) = nodup string_dec (merge l3 ++ l4). *)

Check Sorted_merge.

Lemma In_merge : forall y l r,
    In y (merge l r) <-> In y l \/ In y r.
Proof.
Admitted.

(* Lemma HdRel_lt : forall a y l, *)
(*     HdRel lex_lt a l -> In y l -> lex_lt a y. *)
(* Proof with eauto with bool. *)
(*   introv HR HI. gen a y. induction l; intros... *)
(*   - inverts HI. *)
(*   - Print HdRel. inverts HR. forwards: IHl H0. inverts HI. Print HdRel. *)
(*   applys* SortA_InfA_InA l. 4: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. *)

Lemma HdRel_nodup : forall a l,
    Sorted NOTF.le l -> HdRel lex_lt a l -> HdRel lex_lt a (nodup string_dec l).
Proof with eauto.
  introv HS HR.
  applys In_InfA. introv HI. apply nodup_In in HI.
  induction l.
  - inverts HI.
  - apply in_inv in HI. destruct HI.
    + subst*. inverts* HR.
    + inverts HS. inverts HR.
      forwards*: IHl.
      inverts* H3. constructor.
      destruct H0. now applys* lex_lt_trans.
      now subst*.
Qed.

Lemma le_trans : forall s0 s1 s2 : string, NOTF.le s0 s1 -> NOTF.le s1 s2 -> NOTF.le s0 s2.
Admitted.

Lemma HdRel_nodup_le : forall a l,
    Sorted NOTF.le l -> HdRel NOTF.le a l -> HdRel lex_lt a (nodup string_dec l).
Proof with eauto.
  introv HS HR. gen a. induction l; intros.
  - simpl...
  - inverts HS. inverts HR.
    simpl. case_if*.
    + applys* IHl.
      inverts* H2. constructor...
      eauto using le_trans.
    + constructor...
Abort. (* incorrect: a may be in l *)
Check lex_lt_trans.  Check NTTLB.leb_trans.

Lemma sorted_nodup_aux : forall l,
    sorted (nodup string_dec l) -> Sorted NOTF.le l.
Abort. (* incorrect *)

Lemma sorted_nodup : forall l,
    Sorted NOTF.le l -> sorted (nodup string_dec l).
Proof with eauto.
  introv HS. induction* l.
  - simpl... econstructor...
  - inverts HS. forwards*: IHl.
    simpl. case_if.
    + apply H.
    + econstructor... destruct l...
      * simpl...
      * applys* HdRel_nodup.
        inverts H2. inverts* H3.
        exfalso. applys C. applys in_eq.
Qed.

(* Lemma HdRel_nodup : forall a l, *)
(*         HdRel NOTF.le a l -> In b l -> lex_lt a b. *)
(*         Search (Sorted). *)
(*         inverts H2. inverts H3. econstructor. *)
(*     fold nodup. *)
(*     ; econstructor. *)
(*     + forwards: IHl HS. constructor*. *)
(*       clear HS IHl. *)
(*       induction* l. *)
(*       apply in_inv in C. destruct C. *)
(*       * subst*. constructor*. right*. *)
(*       * constructor. inverts H. *)
(*         Search Sorted. *)


(*         Search HdRel. applys* IHl. *)


(*       Search (Sorted _ _ -> HdRel _ _ _). *)

(*        HS : Sorted NOTF.le l *)
(*   HR : HdRel lex_lt a l *)
(*   y : string *)
(*   HI : In y l *)
(*   ============================ *)
(*   lex_lt a y *)


(*       Search (Sorted). *)

Lemma HdRel_relax : forall a l,
    HdRel lex_lt a l -> HdRel NOTF.le a l.
Proof with eauto.
  introv HS. induction* HS. constructor...
  left*.
Qed.

Lemma sorted_relax : forall l,
    sorted l -> Sorted NOTF.le l.
Proof with eauto.
  introv HS. induction* HS.
  destruct H... constructor... constructor...
  left*.
Qed.

#[local] Hint Constructors Sorted HdRel : core.
#[local] Hint Resolve HdRel_relax sorted_relax : core.

Lemma test : forall a l r,
    HdRel NOTF.le a l -> HdRel NOTF.le a r -> HdRel NOTF.le a (merge l r).
Admitted.

Lemma merge_sorted : forall l r,
    sorted l -> sorted r -> Sorted NOTF.le (merge l r).
Proof with eauto using sorted_relax.
  introv HSl HSr. gen r.
  induction HSl; intros; autorewrite with merge...
  - induction HSr...
    + autorewrite with merge.
      constructor...
    + destruct (string_compare_lex a a0) eqn:HE. destruct c.
      * subst*. simpl. rewrite HE. simpl...
        econstructor. applys IHHSl...
        econstructor... applys test...
        econstructor... right*.
      * simpl. rewrite HE. simpl...
        forwards* IH: IHHSl (a0 :: l0)...
        all: econstructor...
        applys test...
      * simpl. rewrite HE. simpl...
        econstructor... applys test (a :: l) l0...
Qed.

Lemma merge_sorted_dedup: forall l r,
    sorted l -> sorted r -> sorted (nodup string_dec (merge l r)).
Proof with eauto using sorted_nodup, sorted_relax.
  introv HSl HSr.
  forwards: merge_sorted HSl HSr...
Qed.
(*   induction HSl; intros; autorewrite with merge... *)
(*   - induction HSr... *)
(*     + autorewrite with merge. simpl. case_if... *)
(*       constructor... applys sorted_nodup... *)
(*       applys HdRel_nodup... *)
(*     + forwards* IH: IHHSl (a0 :: l0)... *)
(*       econstructor... *)
(*       simpl. case_if... simpl. case_if... *)
(*       econstructor... applys HdRel_nodup... *)


(*       econstructor... *)
(*     + simpl. case_if*. *)
(*       constructor*. applys* HdRel_nodup. applys* sorted_relax. *)
(*   - induction HSr... *)
(*     + autorewrite with merge. simpl. case_if... *)
(* eauto using sorted_nodup *)
(*     + autorewrite with merge. repeat case_if... *)
(*       fold nodup.sorted_relax applys* SortA_InfA_InA. *)
(*       sorted (nodup *)
(*       autorewrite with merge. *)
(*       constructor. *)
(*     + forwards* HSP: IHHSl l0. *)
(*       autorewrite with merge. case_if... *)
(*       * case_if in C. forwards* HSP': IHHSl (a0 :: l0). *)
(*         all: constructor... *)
(*         applys In_InfA. introv HI. forwards [HI'|HI']: In_merge HI. *)
(*         ** applys* SortA_InfA_InA l. 4: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. *)
(*         ** applys* SortA_InfA_InA (a0 :: l0). 5: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. constructor... *)
(*            Search (Proper (eq ==> eq ==> iff) lex_lt). *)
(*         eauto. *)
(*         Search (InA). *)
(*         Search Sorted. *)
(*         lets: InfA_app. *)
(*         Search HdRel. SortA_InfA_InA. *)
(*         case_if... *)
(*       * case_if... *)
(*         ** lets* HSP: IHHSl (y0 :: l0). forwards*: HSP. *)
(*            case_if... *)
(*         ** simpl in IHHSr. case_if... *)
(* Qed. *)


(* Theorem merge_comm : forall (l1 l2 : list string), *)
(*   Sorted lex_lt l1 -> Sorted lex_lt l2 -> merge l1 l2 = merge l2 l1. *)
(* Proof. *)
(*   introv HS1 HS2. *)
(*   lets: SortA_equivlistA_eqlistA. *)
(*   Print StrictOrder. *)

(*   Search (Sorted). *)
(*   Search (lex_lt). *)
(*   pose proof NTTLB.leb_trans. unfold Transitive in H. Print NOTF. Search le. *)
(*   assert (forall x y, proj1_sig (string_compare_lex x y) = Lt -> *)
(*                       lex_lt x y). eauto. *)
(*   pose proof NOTF.compare_spec. intros. forwards: H0 x y. *)
(*   destruct H2; try discriminate. eauto. *)
(*   intros. destruct H1. destruct H2. Search NTTLB.leb. *)
(*   Search CompareSpec. *)
(*   NTTLB.leb_le: *)
(*   forall x y : string, *)
(*   is_true (NTTLB.leb x y) <-> (fun x0 y0 : string => lex_lt x0 y0 \/ x0 = y0) x y *)
(* Admitted. *)

(* } *)
Open Scope string_scope.

(* Properties of type translation *)
Lemma foldl_append_singleton_list : forall T,
    list_string_2_string [T] = T.
Proof.
  introv. simpl. eauto.
Qed.

Lemma check_toplike_sound_complete : forall A,
    toplike A <-> check_toplike A = true.
Proof.
  split; introv HT.
  - induction HT; simple*.
    rewrite IHHT1. rewrite* IHHT2.
  - induction* A.
    all: simpl in HT; try discriminate.
    forwards* (?&?): andb_prop_elim (check_toplike A1) (check_toplike A2).
    eauto with bool.
    constructor; intuition eauto using Is_true_eq_true.
Qed.

Lemma type2list_arrow : forall A B,
  ~ toplike B ->
  stype2string (typ_arrow A B) = [ ( "(" ++ (stype2string A) ++ "->" ++ (stype2string B) ++ ")" ) ].
Proof.
  introv NT.
  simpl. case_if*. apply check_toplike_sound_complete in C. intuition eauto.
Qed.

Lemma index_arrow_inv : forall A B,
    toplike B \/ || typ_arrow A B || = [ "(" ++ || A || ++ "->" ++ || B || ++ ")" ].
Proof.
  introv. destruct (check_toplike B) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma index_rcd_inv : forall l A,
    toplike A \/ || typ_rcd l A || = [ "{" ++  l ++ "=>" ++ || A || ++ "}" ].
Proof.
  introv. destruct (check_toplike A) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma stype2string_toplike : forall A,
    toplike A -> || A || = nil.
Proof with eauto.
  introv HT. apply check_toplike_sound_complete in HT.
  destruct A; simpl in HT; try discriminate; simpl...
  all: rewrite* HT.
Qed.

Lemma stype2string_and : forall A B : typ,
    || typ_and A B || = nodup string_dec (merge (stype2string A) (stype2string B)).
Proof.
  introv. simpl.
  destruct (check_toplike A) eqn:HA. destruct (check_toplike B) eqn:HB.
  all: try apply check_toplike_sound_complete in HA.
  all: try apply check_toplike_sound_complete in HB.
  all: try ( rewrite (stype2string_toplike A); [ | eassumption] ).
  all: try ( rewrite (stype2string_toplike B); [ | eassumption] ).
  all: autorewrite with merge; simpl; eauto.
Qed.


Lemma eqIndTyp_toplike : forall A B,
    eqIndTyp A B -> toplike A <-> toplike B.
Proof with eauto.
  introv HE. induction* HE.
  all: try solve [split; intro H; intuition eauto].
  all: try solve [split; intro H; econstructor; inverts H; intuition eauto].
  all: try solve [split; intro H; econstructor; inverts H; try inverts H3; try inverts H2; intuition eauto].
  all: try solve [split; intro H'; eauto; inverts H'; intuition eauto].
Qed.

(* Lemma test : forall A B, *)
(*     ||A|| = ||B|| -> type2tlist A = type2tlist B. *)
(* Proof with intuition eauto. *)
(*   introv HE. unfold stype2string in HE. rewrite HE. *)
Lemma typeindex_sorted: forall A,
    sorted (|| A ||).
Proof with eauto.
  introv. induction* A; simpl...
  all: unfolds...
  all: try econstructor...
  - case_if...
    econstructor...
  - case_if... applys* merge_sorted_dedup.
  - case_if...
    econstructor...
Qed.

Lemma typeindex_nodup: forall A,
    NoDup (|| A ||).
Proof with eauto.
  introv. induction* A; simpl...
Admitted.

 Lemma merge_double_nodup : forall l,
     nodup string_dec (merge l l) = nodup string_dec l.
 Admitted.

 Lemma typeindex_nodup_elim : forall A,
     nodup string_dec (|| A ||) = || A ||.
Proof with eauto.
  introv. applys nodup_fixed_point. applys typeindex_nodup.
Qed.

#[local] Hint Rewrite typeindex_nodup_elim : merge.
#[local] Hint Resolve typeindex_sorted : core.

Lemma eqIndTyp_sound : forall A B,
    eqIndTyp A B -> || A || = || B ||.
Proof with eauto using typeindex_nodup, NoDup_nodup, merge_sorted_dedup.
  introv HE. induction* HE.
  - rewrite* IHHE1.
  - lets [|]: index_arrow_inv A1 B1;
      lets [|]: index_arrow_inv A2 B2.
    2: forwards (HT2&?): eqIndTyp_toplike HE2;
       forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE2;
       forwards H': HT2 H0.
    1-3: repeat rewrite stype2string_toplike...
    rewrite H; rewrite H0; rewrite IHHE1; rewrite IHHE2...
  - lets [|]: index_rcd_inv A;
      lets [|]: index_rcd_inv B.
    2: forwards (HT2&?): eqIndTyp_toplike HE;
    forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE;
    forwards H': HT2 H0.
    1-3: repeat rewrite stype2string_toplike...
    rewrite H; rewrite H0; rewrite IHHE...
  - repeat rewrite stype2string_and. rewrite IHHE...
  - repeat rewrite stype2string_and. rewrite* merge_comm.
  - repeat rewrite stype2string_and.
    applys sorted_unique...
    applys* NoDup_Permutation... split; introv HI.
    all: apply nodup_In; applys In_merge.
    all: repeat apply nodup_In in HI; try apply In_merge in HI.
    all: intuition eauto; repeat apply nodup_In in H; try apply In_merge in H; intuition eauto.
    1-2: left; apply nodup_In; applys In_merge...
    1-2: right; apply nodup_In; applys In_merge...
  - rewrite stype2string_toplike...
  - rewrite stype2string_and. rewrite stype2string_toplike...
    autorewrite with merge...
  - applys sorted_unique...
    repeat rewrite stype2string_and.
    rewrite IHHE.
    applys* NoDup_Permutation... split; introv HI.
    + rewrite* merge_double_nodup in HI.
      rewrite* typeindex_nodup_elim in HI.
    + rewrite* merge_double_nodup.
      rewrite* typeindex_nodup_elim.
      Unshelve. eauto.
Qed.

Lemma nodup_empty_inv : forall l,
    nodup string_dec l = nil -> l = nil.
Proof.
  introv HE. induction* l.
  simpl in HE. case_if.
  exfalso. forwards~: IHl. subst. inverts C.
Qed.

Lemma merge_empty_inv : forall l r,
    merge l r = nil -> l = nil /\ r = nil.
Proof.
  introv HE. destruct* l; destruct* r.
  simpl in HE. case_if.
Qed.

Lemma stype2string_toplike_complete : forall A,
    || A || = nil -> toplike A.
Proof with eauto.
  introv HT. apply check_toplike_sound_complete.
  induction A; simpl in HT; try discriminate; try case_if; simpl...
  apply nodup_empty_inv in HT.
  forwards (?&?): merge_empty_inv HT.
  forwards~: IHA1. forwards~: IHA2. rewrite H1. rewrite* H2.
Qed.

Lemma stype2string_single_and_inv : forall a A B,
    [ a ] = || typ_and A B || -> ([ a ] = || A || \/ [ a ] = || B ||) /\ (nil = || A || \/ nil = || B ||).
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE.
  rewrite stype2string_and in HE. gen a B.
  induction (|| A ||); intros.
  - autorewrite with merge in HE...
  - Search nodup. induction (|| B ||).
    + autorewrite with merge in HE...
Admitted.

Lemma eqIndTyp_complete : forall A B,
    || A || = || B || -> eqIndTyp A B.
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE. gen B.
  induction A; intros.
  - forwards*: stype2string_toplike_complete B...
  - simpl in HE. induction B...
    all: try solve [simpl in HE; try case_if; try discriminate].
    forwards ([|]&[|]): stype2string_single_and_inv HE.
    all: try forwards: IHB1 H. all: try forwards: IHB1 H0.
    admit.
    forwards*: stype2string_toplike_complete B2...
    applys EI_trans H1. applys EI_trans EI_comm.
    applys EI_trans EI_and. applys EI_symm EI_topelim.
    applys* EI_symm EI_top.
    admit. admit.
  - admit.
  - admit.
  - (* and case ??? : 1)either toplike 2) destruct B || normalize *) admit.
  - admit.
Admitted.

Lemma eqIndTyp_sound_target : forall A B,
    eqIndTyp A B -> eqIndTypTarget |[A]| |[B]|.
Proof.
  introv HE. induction HE.
  - (* refl *) admit.
  - (* trans *) admit.
  - (* symm *) admit.
  - (* arrow congurence *) admit.
  - (* rcd; needs property about eqindtyp *)
    simpl. case_if; case_if. 1-3: admit.
    admit.
  - (* list; needs property about eqindtyp ? *)
    simpl. admit.
  - (* list swap ? *) admit.
  - (* assoc *) admit.
  - apply check_toplike_sound_complete in H.
    simpl. (* toplike |[ A ]| ttyp_top *) admit.
  - admit.
  - (* double *) admit.
Admitted.

(* after deduplication is the same permutation *)

(*   flattern a tree to a list? *)

(*   generate sets from list / tree? *)


(*   f (A & B) = f(C) *)

(*                 f(A) = f(B) --> |[ A ]| ~ |[ B ]| *)

(*   label->type *)


(*            (A & B) & C *)

(*         \y. ( \x. (\r. A | r) (\r. B | r) x ) ((\r.C|r) y) *)

Definition eqIndTyp A B := sub A B. (* forall C, sub A C -> sub B C. *)

Lemma sub_andl_inv : forall A B C,
    sub (typ_and A B) C <-> sub A C \/ sub B C.
Admitted.


Lemma eqIndTyp_complete_alt : forall A B,
    || A || = || B || -> eqIndTyp A B.
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE. gen B.
  induction A; intros.
  - forwards*: stype2string_toplike_complete B... admit. (* toplike super top *)
  - (* bot sub all *) admit.
  - simpl in HE. induction B...
    all: try solve [simpl in HE; try case_if; try discriminate].
    + (* refl *) admit.
    + forwards ([|]&[|]): stype2string_single_and_inv HE.
      (* stype2string_toplike_complete *)
      all: try forwards: IHB1 H. all: try forwards: IHB1 H0.
      all: admit.
      (* forwards*: stype2string_toplike_complete B2... *)
      (* applys EI_trans H1. applys EI_trans EI_comm. *)
      (* applys EI_trans EI_and. applys EI_symm EI_topelim. *)
      (* applys* EI_symm EI_top. *)
  - (* arrow *)
    simpl in HE. case_if.
    + admit.
      (* stype2string_toplike_complete *)
    + induction B...
      all: try solve [simpl in HE; try case_if; try discriminate].
      * (* arrow *)
        simpl in HE. case_if.
        injection HE. intro HEq.
        Search (_ ++ _ = _ ++ _). (* better use an inductive type as a label *)
        assert (|| A1 || = || B1 ||) by admit. assert (|| A2 || = || B2 ||) by admit.
        forwards*: IHA1. forwards*: IHA2.
        (* contravariant problem *)
        Restart.
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE. indTypSize (size_typ A + size_typ B).
  destruct A; intros.
  - forwards*: stype2string_toplike_complete B... admit. (* toplike super top *)
  - (* bot sub all *) admit.
  - simpl in HE. destruct B...
    all: try solve [simpl in HE; try case_if; try discriminate].
    + (* refl *) admit.
    + forwards ([|]&[|]): stype2string_single_and_inv HE.
      (* stype2string_toplike_complete *)
      all: try forwards: IHB1 H. all: try forwards: IHB1 H0.
      all: admit.
      (* forwards*: stype2string_toplike_complete B2... *)
      (* applys EI_trans H1. applys EI_trans EI_comm. *)
      (* applys EI_trans EI_and. applys EI_symm EI_topelim. *)
      (* applys* EI_symm EI_top. *)
  - (* arrow *)
    simpl in HE. case_if.
    + admit.
      (* stype2string_toplike_complete *)
    + induction B...
      all: try solve [simpl in HE; try case_if; try discriminate].
      * (* arrow *) clear IHB1 IHB2.
        simpl in HE. case_if.
        injection HE. intro HEq.
        Search (_ ++ _ = _ ++ _). (* better use an inductive type as a label *)
        assert (|| B1 || = || A1 ||) by admit. assert (|| A2 || = || B2 ||) by admit.
        forwards*: IH H. elia. forwards*: IH H0. elia.
        applys* S_arr. admit. admit.
      * (* and *)
        forwards ([|]&[|]): stype2string_single_and_inv HE.
        simpl in HE. rewrite <- H0 in HE.
        case_if in HE.
        assert (Heq: nodup string_dec (syntax_ott.NSort.merge nil (|| B2 ||)) = || B2 ||) by admit.
        rewrite Heq in HE. forwards: IHB2 HE. elia.
        forwards*: stype2string_toplike_complete B1.
        admit. admit. admit. admit.
  - destruct B.
    + admit. (* top *)
    + admit. (* single *)
    + admit. (* single *)
    + admit. (* single *)
    + (* prove (typ_and A1 A2) <: B1 *)
      (* prove (typ_and A1 A2) <: B2 *)
      assert (incl (|| A1 ||) (|| typ_and A1 A2 ||)).
      assert (incl (|| A2 ||) (|| typ_and A1 A2 ||)).
      all: admit.
    + admit. (* single *)
  - admit.
Admitted.

Lemma incl_single: forall (x y : string), incl [x] [y] -> x = y.
Proof.
        introv HI.
        apply incl_Forall_in_iff in HI.
        apply Forall_inv in HI.
        apply in_one_iff in HI. eauto.
Qed.
Lemma incl_eq : forall (l1 l2 : list string), l1 = l2 -> incl l1 l2.
Proof.
  introv Heq. rewrite Heq. applys* incl_refl.
Qed.

Lemma eqIndTyp_complete_alt_gen : forall A B,
    incl (|| B ||) (|| A ||) -> sub A B.
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE. indTypSize (size_typ A + size_typ B).
  destruct A; intros.
  - forwards*: stype2string_toplike_complete B... admit. (* toplike super top *)
  - (* bot sub all *) eauto. admit.
  - simpl in HE. Search incl. destruct B...
    all: try solve [simpl in HE; try case_if; forwards: incl_single HE; try discriminate].
    + simpl in HE. case_if. admit.
      forwards: incl_single HE. discriminate.
    + admit.
    + admit.
  - (* arrow *)
    simpl in HE. case_if.
    + admit.
      (* stype2string_toplike_complete *)
    + destruct B...
      all: try solve [simpl in HE; try case_if; try discriminate].
      3: {
        (* arrow *)
        simpl in HE. case_if. admit.
        forwards: incl_single HE.
        injection H. intro HEq.
        Search (_ ++ _ = _ ++ _). (* better use an inductive type as a label *)
        assert (|| B1 || = || A1 ||) by admit. assert (|| A2 || = || B2 ||) by admit.
        assert (|| A1 || = || B1 ||) by admit. assert (|| B2 || = || A2 ||) by admit.
        forwards: IH B1 A1; eauto using incl_eq. elia.
        forwards: IH A1 B1; eauto using incl_eq. elia.
        forwards: IH A2 B2; eauto using incl_eq. elia.
        forwards: IH B2 A2; eauto using incl_eq. elia.
      }
      3: { (* and *) admit.
           (* forwards ([|]&[|]): stype2string_single_and_inv HE. *)
           (* simpl in HE. rewrite <- H0 in HE. *)
           (* case_if in HE. *)
           (* assert (Heq: nodup string_dec (syntax_ott.NSort.merge nil (|| B2 ||)) = || B2 ||) by admit. *)
           (* rewrite Heq in HE. forwards: IHB2 HE. elia. *)
           (* forwards*: stype2string_toplike_complete B1. *)
      }
      admit. admit. admit.
  - simpl in HE. case_if. admit.
    assert (incl (nodup string_dec (syntax_ott.NSort.merge (|| A1 ||) (|| A2 ||))) ((|| A1 ||) ++ (|| A2 ||))). {
      applys nodup_incl string_dec.
      Search (incl). admit.
    }
    forwards: incl_tran HE H.
  (*   + admit. (* top *) *)
  (*   + admit. (* single *) *)
  (*   + admit. (* single *) *)
  (*   + admit. (* single *) *)
  (*   + (* prove (typ_and A1 A2) <: B1 *) *)
  (*     (* prove (typ_and A1 A2) <: B2 *) *)
  (*     assert (incl (|| A1 ||) (|| typ_and A1 A2 ||)). *)
  (*     assert (incl (|| A2 ||) (|| typ_and A1 A2 ||)). *)
  (*     all: admit. *)
  (*   + admit. (* single *) *)
  (* - admit. *)
    Restart.
  introv HE. indTypSize (size_typ A + size_typ B).
  destruct B; intros; eauto.
  - simpl in HE.
    apply incl_Forall_in_iff in HE.
    apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + case_if.
       assert (incl (nodup string_dec (syntax_ott.NSort.merge (|| A1 ||) (|| A2 ||))) ((|| A1 ||) ++ (|| A2 ||))). {
      applys nodup_incl string_dec.
      Search (incl). admit.
    }
    forwards Hia: In_incl HE H.
       forwards [|]: in_app_or Hia.
       assert (incl (||typ_bot||) (||A1||)). admit.
       forwards: IH H1. elia.
       eauto.
       admit.
  - admit.
  - simpl in HE; try case_if. admit.
    try apply incl_Forall_in_iff in HE.
    try apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + admit. (* arrow vs arrow *)
    + (* similar *)
      admit.
  - assert (incl (|| B1 ||)(|| typ_and B1 B2 ||)). {
      simpl. case_if. admit.
      assert (incl ((|| B1 ||) ++ (|| B2 ||)) (syntax_ott.NSort.merge (|| B1 ||) (|| B2 ||))) by admit.
      applys nodup_incl.
      applys incl_tran H. applys incl_appl. applys incl_refl.
    }
    assert (incl (|| B2 ||)(|| typ_and B1 B2 ||)) by admit.
    forwards: incl_tran H HE. forwards: incl_tran H0 HE.
    forwards*: IH A B1. elia. forwards*: IH A B2. elia.
  - admit.
Admitted.

(* (incl (nodup string_dec (syntax_ott.nsort.merge (|| a1 ||) (|| a2 ||))) ((|| a1 ||) ++ (|| a2 ||))) *)
(* incl ((|| b1 ||) ++ (|| b2 ||)) (syntax_ott.nsort.merge (|| b1 ||) (|| b2 ||)) *)

Lemma incl_eq_tindex: forall A B,
  incl (||A||) (||B||) -> incl (||B||) (||A||) -> ||A|| = ||B||.
Admitted.

Lemma eqIndTyp_sound_alt_gen : forall A B,
    sub A B -> incl (|| B ||) (|| A ||).
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HS.
  induction HS; try solve [simpl; eauto using incl_refl].
  - rewrite* stype2string_toplike. applys incl_nil.
  - simpl. case_if. applys incl_nil.
    case_if. admit.
    applys incl_eq.
    forwards*: incl_eq_tindex A1 B1. forwards*: incl_eq_tindex A2 B2.
    rewrite H. rewrite H0...
  - applys incl_tran IHHS.
    simpl. case_if. admit.
    assert (incl ((|| A1 ||) ++ (|| A2 ||)) (nodup string_dec (syntax_ott.NSort.merge (|| A1 ||) (|| A2 ||)))) by admit.
    applys incl_tran H.
    applys incl_appl. applys incl_refl.
  - admit.
  - simpl. case_if. applys incl_nil.
    assert (incl (nodup string_dec (syntax_ott.NSort.merge (|| A2 ||) (|| A3 ||))) ((|| A2 ||) ++ (|| A3 ||))) by admit.
    applys incl_tran H.
    applys* incl_app.
Admitted.

Corollary eqIndTyp_sound_alt : forall B A,
    sub B A -> sub A B -> (|| B ||) = (|| A ||).
Proof.
  introv HS1 HS2.
  apply eqIndTyp_sound_alt_gen in HS1.
  apply eqIndTyp_sound_alt_gen in HS2.
  (* dedup sort unique *)
Admitted.

Definition target_typ_with_same_index At Bt := exists A B, || A || = || B ||
                                                           /\ |[ A ]| = At
                                                           /\ |[ B ]| = Bt.

Lemma target_typ_with_same_index_refl : forall At,
    target_typ_with_same_index At At.
Admitted.
#[local] Hint Resolve target_typ_with_same_index_refl : core.

(* ? directly use list in target language *)
(* ? use a relation for type translation in target language *)

(* refine subtypespec *)
Inductive subTarget : ttyp -> ttyp -> Prop :=
 | ST_refl : forall At,
     subTarget At At
| ST_arrow : forall At Bt At' Bt',
    subTarget At At' -> subTarget At' At -> subTarget Bt Bt' -> subTarget Bt' Bt -> subTarget (ttyp_arrow At Bt) (ttyp_arrow At' Bt')
 | ST_rcd : forall At Bt,
     (forall l Ct, Tlookup l At = Some Ct -> exists Ct', Tlookup l Bt = Some Ct' /\ subTarget Ct' Ct) ->
     subTarget Bt At.

#[local] Hint Constructors subTarget : core.

Lemma ST_top: forall A, subTarget |[ A ]| ttyp_top. Admitted.

Lemma ST_trans: forall A B C, subTarget A B -> subTarget B C -> subTarget A C. Admitted.

Lemma ST_andl : forall A B, subTarget |[ (typ_and A B) ]| |[ A ]|. Admitted.

Lemma ST_andr : forall A B, subTarget |[ (typ_and A B) ]| |[ B ]|. Admitted.

Lemma ST_inv : forall A B,
    subTarget |[ A ]| |[ B ]| -> forall l Ct, Tlookup l |[ B ]| = Some Ct -> exists Ct', Tlookup l |[ A ]| = Some Ct' /\ subTarget Ct' Ct. Admitted.

#[local] Hint Resolve ST_top ST_andl ST_andr : core.

Lemma lookup_sub : forall A B,
    sub A B -> subTarget |[A]| |[B]|.
Proof.
  introv HS.
  induction HS; try solve [simpl; eauto].
  - rewrite* (ttyp_trans_ord_top B)...
  - simpl. case_if*. admit.
    simpl. case_if*. admit.
    +
      rewrite* (eqIndTyp_sound_alt A1 B1). rewrite* (eqIndTyp_sound_alt A2 B2).
      applys ST_rcd. introv HL. simpl in HL. case_if*.
      subst. exists. split*. injection HL. intro HE. subst*.
  - applys* ST_trans IHHS.
  - applys* ST_trans IHHS.
  - simpl. case_if*.
    + applys ST_rcd. introv HL.
      remember (Tlookup l |[A2]|). destruct o.
      * forwards* (?&?&?): ST_inv IHHS1.
        forwards* : lookup_concat_simpl (|[ A2 ]|) (|[ A3 ]|).
        rewrite HL in H1. rewrite <- Heqo in H1. injection H1. intro Heq. subst*.
      * forwards* (?&?&?): ST_inv IHHS2.
        forwards* : lookup_concat_simpl_none (|[ A2 ]|) (|[ A3 ]|). admit.
        rewrite* HL in H.
Admitted.

(* Lemma lookup_sub : forall A B, *)
(*     sub B A -> *)
(*     forall l Ct, Tlookup l |[A]| = Some Ct -> exists Ct', Tlookup l |[B]| = Some Ct' *)
(*     (* /\ sub C C' /\ sub C' C  % not 1-1 mapping *) *)
(*     /\ target_typ_with_same_index Ct Ct'. *)
(* Proof with simpl in *; try discriminate. *)
(*   introv HS. *)
(*   induction HS; introv HL. *)
(*   - simpl in HL. case_if. *)
(*     exists. simpl. split*. *)
(*     case_if*. *)
(*   - rewrite* ttyp_trans_ord_top in HL... *)
(*   - simpl in *. case_if*. *)
(*   - simpl in HL. case_if*. *)
(*     simpl. case_if*. *)
(*     + (* contradiction *) admit. *)
(*     + simpl in HL. case_if*. subst. *)
(*       rewrite* (eqIndTyp_sound_alt A1 B1). rewrite* (eqIndTyp_sound_alt A2 B2). *)
(*       exists*. split. applys* lookup_wf_typ_3. *)
(*       injection HL. intro HE. rewrite <- HE. *)
(*       unfolds. exists* (typ_arrow B1 B2) (typ_arrow A1 A2). *)
(*       splits; simpl; try rewrite C0; try rewrite C. *)
(*       rewrite* (eqIndTyp_sound_alt A1 B1). rewrite* (eqIndTyp_sound_alt A2 B2). *)
(*       simpl. all: admit. *)
(*   - admit. *)
  -

    forwards: stype2string_toplike H.
    rewrite H0 in HL.


sub A B -> sub B A ->
Print subtype_wrt_lookup.

Definition lookup_none A B: forall l, Tlookup l A = None -> Tlookup l B = None.

Definition subtype_wrt_lookup_relax At Bt :=
  rec_typ At /\ rec_typ Bt /\ wf_typ At /\ wf_typ Bt /\ forall l B, Tlookup l Bt = Some B -> exists A, Tlookup l At = Some A /\ subtype_wrt_lookup_relax A B.

Lemma eqind_sound_target : forall A B,
    ||A|| = ||B|| -> subtype_wrt_lookup |[A]| |[B]|.
Proof.
  introv HE.
  (* incl_eq *)
  (* eqIndTyp_complete_alt_gen *)

(*     - use sub to replace eqindex *)

(*     new equality *)
(*     A&B = C if tolist A ++ tolist B .. C *)

(*                  1) manually prove; equality up to permutation *)
(*                                       2) *)

(* tolist A *)
