Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Translation.
Require Export Target.
(* Require Export Source3. *)


(* Type safety *)
(** The key is to prove the lookup label does exists in the record *)
(** To prove type safety, we need to translate typing contexts / types
 \ x : A . e : B  => A->B ~> \ x . |e| ??? **)

#[local] Hint Resolve target_typing_wf_1 target_typing_wf_2 ttyp_trans_wf : core.
#[local] Hint Unfold Tlookup : core.

(* Definition subtype_wrt_lookup A B := *)
(*   A = B \/ (exists ll At Bt, B = ttyp_rcd ll At Bt /\ forall l C, Tlookup l B = Some C -> Tlookup l A = Some C). *)
(* (* maybe too strict? *) *)
(* (* exists A', Tlookup l A = Some A' /\ A' ~= C ? *) *)

(* Notation "A <: B" := (subtype_wrt_lookup A B) (at level 70). (* too high *) *)

(* Lemma subtype_wrt_lookup_refl : forall A, *)
(*     subtype_wrt_lookup A A. *)
(* Admitted. *)

(* #[local] Hint Resolve subtype_wrt_lookup_refl : core. *)

(* Lemma subtype_wrt_lookup_same : forall A B l C, *)
(*     A <: B -> Tlookup l B = Some C -> Tlookup l A = Some C. *)
(* Proof. *)
(*   introv HS HL. *)
(*   destruct* HS. *)
(*   rewrite* H. *)
(* Qed. *)

(* Lemma elaboration_intersection_left : forall G e dirflag A B t, *)
(*     elaboration G e dirflag (typ_and A B) t *)
(*     -> exists C, elaboration G e dirflag C t /\ |[C]| <: |[A]|. *)
(* Admitted. *)

(* Lemma elaboration_intersection_right : forall G e dirflag A B t, *)
(*     elaboration G e dirflag (typ_and A B) t *)
(*     -> exists C, elaboration G e dirflag C t /\ |[C]| <: |[B]|. *)
(* Admitted. *)

(* Lemma elaboration_allows_nondeterministic_lookup : forall G e dirflag A t ll Bt, *)
(*     elaboration G e dirflag A t *)
(*     -> contained_by_rec_typ |[A]| ll Bt *)
(*     -> exists E, target_typing E (texp_proj t ll) Bt. *)
(* Admitted. *)

(* Inductive texp_behave_like_styp : texp -> typ -> Prop := *)
(* | tb_inter : forall t B1 B2, *)
(*     texp_behave_like_styp t B1 -> texp_behave_like_styp t B2 -> texp_behave_like_styp t (t_and B1 B2) *)
(* | tb_ => exists E C, target_typing E t C /\ C <: A *)
(*   end. *)

(* Definition texp_behave_like_styp t A := *)
(*   forall ll Bt, contained_by_rec_typ |[A]| ll Bt *)
(*   -> exists E At, target_typing E t At /\ Tlookup ll At = Some Bt. *)

(* Lemma texp_behave_like_styp_intersection : forall t A B, *)
(*     texp_behave_like_styp t (typ_and A B) -> texp_behave_like_styp t A /\ texp_behave_like_styp t B. *)
(* Admitted. *)

(* Axiom source_trans_intersection_expose_both : forall G e dirflag A B t, *)
(*     elaboration G e dirflag (typ_and A B) t -> *)
(*     exists E A' B', target_typing E t A' /\ A' <: |[A]| /\ *)
(*                   target_typing E t B' /\ B' <: |[B]|. *)


Definition target_flex_typing E t At := exists Bt, target_typing E t Bt /\ SubtypeTarget Bt At.


Lemma TS_andl : forall A B, SubtypeTarget |[typ_and A B]| |[A]|.
Admitted.

Lemma TS_andr : forall A B, SubtypeTarget |[typ_and A B]| |[B]|.
Admitted.

Lemma TS_eq : forall A B C, SubtypeTarget A B -> eqIndTypTarget A C -> SubtypeTarget C B.
Admitted.


Lemma subtype_wf_typ_1 : forall At Bt,
    SubtypeTarget At Bt -> wf_typ At.
Proof with eauto.
  introv HS. induction* HS.
Qed.

Lemma subtype_wf_typ_2 : forall At Bt,
    SubtypeTarget At Bt -> wf_typ Bt.
Proof with intuition eauto.
  introv HS. induction* HS.
  destruct H1 as [(?&?)|?]...
Qed.

#[local] Hint Resolve subtype_wf_typ_1 subtype_wf_typ_2 : core.

Lemma subtype_wrt_lookup_same : forall A B l C,
    SubtypeTarget A B -> Tlookup l B = Some C ->
    exists C', Tlookup l A = Some C' /\ SubtypeTarget C' C.
Proof with intuition eauto using wf_typ_look_up_wf.
  introv HS HL. gen C.
  induction* HS; intros; inverts HL.
  - exists...
  - case_if*.
    + inverts H3. subst*.
    + forwards* (?&?&?): IHHS2.
Qed.

Lemma TS_trans : forall A B C, SubtypeTarget A B -> SubtypeTarget B C -> SubtypeTarget A C.
Proof.
  introv HSA HSB. gen A.
  induction* HSB; intros.
  - inverts* HSA.
  - forwards* (?&?&?): subtype_wrt_lookup_same H0.
Qed.


Lemma lookup_wf_typ_1 : forall l T At l',
    Tlookup l' (ttyp_rcd l T At) = Tlookup l' At \/ l = l'.
Proof.
  introv. simpl. case_if*.
Qed.

Lemma lookup_wf_typ_2 : forall l T At Bt,
    wf_typ (ttyp_rcd l T At) -> Tlookup l At = Some Bt -> eqIndTypTarget T Bt.
Proof.
  introv WF LK. inverts WF. destruct H5.
  all: rewrite LK in H; inverts* H.
Qed.


Lemma eqindtyptarget_wf_typ_1 : forall At Bt,
    eqIndTypTarget At Bt -> wf_typ At.
Proof with eauto.
  introv HS. induction* HS.
Qed.

Lemma subtype_complete : forall At Bt,
    eqIndTypTarget At Bt -> SubtypeTarget At Bt.
Proof with eauto using eqIndTypTarget_rec_typ, TS_trans.
  (* introv HRa HWa HRb HWb HE. *)
  introv HE. induction* HE...
  (* forwards*: IHHE1. forwards*: IHHE2... applys TS_trans. *)
  - applys TS_rcd...
    { simpl. case_if*. }
    admit.
  - applys TS_trans IHHE. applys* TS_rcd.
    { simpl. case_if*. case_if*. }
    applys* TS_rcd.
    { simpl. case_if*. }
    admit.
  - applys TS_trans IHHE2. applys* TS_rcd.
    { simpl. case_if*. }
    applys* TS_rcd.
    { simpl. case_if*. }
    admit.
Admitted.

Lemma subtype_wide : forall l T At Bt,
    (forall l Ct, Tlookup l At = Some Ct -> eqIndTypTarget T Ct) ->
    rec_typ At -> SubtypeTarget At Bt ->
    SubtypeTarget (ttyp_rcd l T At) Bt.
Proof with try reflexivity.
  introv WF HR ST. gen At l T.
  induction* Bt; intros; try solve [inverts ST; inverts HR; solve_by_invert].
  inverts ST.
  - (* refl *) forwards* [Heq|Heq]: lookup_wf_typ_1.
    + applys TS_rcd.
      2: { rewrite* Heq.
           simpl. case_if*. }
      3: { applys* IHBt2. applys* IHBt2.
           inverts* HR. introv LK.
           + subst*. forwards: lookup_wf_typ_2 WF. simpl. case_if*.
      applys TS_rcd.
      { simpl. case_if*. }
      { applys* subtype_complete. }
      { applys* IHBt2. applys* IHBt2. inverts* WF. inverts* HR. }
  - (* rcd *) forwards* [Heq|Heq]: lookup_wf_typ_1.
    + applys TS_rcd. rewrite* Heq. eauto.
      applys* IHBt2.
    + subst*. forwards*: lookup_wf_typ_2 WF.
      applys TS_rcd.
      { simpl. case_if*. }
      { applys* TS_trans Bt. applys* subtype_complete. }
      { applys* IHBt2. }
Qed.

(* Lemma subtype_refl : forall At, *)
(*     rec_typ At -> wf_typ At -> SubtypeTarget At At. *)
(* Proof. *)
(*   introv HR HW. induction* HW; try solve_by_invert. *)
(*   - inverts HR. *)
(*     applys* TS_rcd. *)
(*     simpl. case_if*. *)
(*     applys* subtype_wide. *)
(* Qed. *)


(* Lemma subtype_wrt_lookup_same : forall A B l C, *)
(*     wf_typ A ->  wf_typ B -> SubtypeTarget A B -> Tlookup l B = Some C -> *)
(*     exists C', Tlookup l A = Some C' /\ SubtypeTarget C' C. *)
(* Proof. *)
(*   introv WFA WFB HS HL. gen C. *)
(*   induction* HS; intros; inverts* HL. *)
(*   - case_if*. *)
(*     + inverts H1. subst*. *)
(*     + forwards* (?&?&?): IHHS2. *)
(*       inverts* WFB. *)
(* Qed. *)

(* properties of flex_typing *)

Lemma target_flex_typing_wf : forall E t A,
    target_flex_typing E t A -> uniq E. Admitted.
(* Proof with eauto using target_typing_wf_1; destruct_uniq; solve_uniq. *)
(*   introv H. *)
(*   induction* H. *)
(* Qed. *)


Lemma target_flex_typing_wf_2 : forall E t A,
    target_flex_typing E t A -> wf_ctx E.  Admitted.
(* Proof with eauto using target_typing_wf_2, context_wf_inv_1, context_wf_inv_2. *)
(*   introv H. induction* H. *)
(* Qed. *)

#[local] Hint Resolve target_flex_typing_wf target_flex_typing_wf_2 : core.

#[local] Hint Constructors target_typing : core.

(** flex_typing relaxes target typing **)
Lemma flex_typing_property0 : forall E t A,
    target_typing E t |[A]| -> target_flex_typing E t |[A]|.  Admitted.
(* Proof. *)
(*   introv H. *)
(*   applys* TFTyping_Orig. *)
(* Qed. *)

(** design 1 **)
(** every lookup can be separately typed; p3 can be proved **)
(** but this (p1) does not hold: forall A B, Gt |- t : A&B -> Gt |- t <= A and Gt |- t <= B *)
(* Lemma flex_typing_property3 : forall E t At ll Ct, *)
(*     target_flex_typing E t At -> Tlookup ll At = Some Ct -> *)
(*     exists Bt, target_typing E t Bt /\ Tlookup ll Bt = Some Ct. *)
(* Proof. *)
(*   introv HT HL. gen ll Ct. *)
(*   induction HT; intros. *)
(*   - eauto. *)
(*   - solve_by_invert. *)
(*   - inverts HL. case_if. exists* At. *)
(*     inverts H2. subst*. *)
(*   - inverts HL. case_if. *)
(*     + inverts H0. subst. *)
(*       forwards*: IHHT1 ll Ct. case_if*. *)
(*     + forwards (?&?&?): IHHT2 H0. *)
(*       exists* x. rewrite* H0. *)
(*   - exists* At. *)
(*     forwards* (?&?&?): IHHT ll At. case_if*. *)
(* Qed. *)

(** design 2 **)
(* the part provided to cosub is not typed but eqind *)
(* Lemma cosub_well_typed : forall E t1 A B t2, *)
(*     cosub t1 A B t2 -> target_flex_typing E t1 |[A]| -> *)
(*     exists Bt', target_typing E t2 Bt' /\ eqIndTypTarget |[B]| Bt'. *)
(* Lemma flex_typing_property3 : forall E t At ll Ct, *)
(*     target_flex_typing E t At -> Tlookup ll At = Some Ct -> *)
(*     exists Bt Ct', target_typing E t Bt /\ Tlookup ll Bt = Some Ct' /\ eqIndTypTarget Ct Ct'. *)
(* Proof. Admitted. *)
(*   introv HT HL. gen ll Ct. *)
(*   induction HT; intros. *)
(*   - eauto. *)
(*   - solve_by_invert. *)
(*   - inverts HL. case_if. exists* At. *)
(*     inverts H2. subst*. *)
(*   - inverts HL. case_if. *)
(*     + inverts H0. subst. *)
(*       forwards*: IHHT1 ll Ct. case_if*. *)
(*     + forwards (?&?&?): IHHT2 H0. *)
(*       exists* x. rewrite* H0. *)
(*   - exists* At. *)
(*     forwards* (?&?&?): IHHT ll At. case_if*. *)
(* Qed. *)

(** design 3 **)
(* target_flex_typing E t At -> eqIndTypTarget At Bt -> target_flex_typing E t Bt. *)


(** flex_typing on well-typed terms only **)
Lemma flex_typing_wt : forall E t A,
    target_flex_typing E t A -> exists B, target_typing E t B.
Proof.
  introv HT. induction* HT.
  (* - forwards* (?&?&?): flex_typing_property3 ll At HT. *)
  (*   simpl. case_if*. *)
Qed.


(** top is the supertype in flex_typing  **)
(* Lemma flex_typing_top : forall E t A, *)
(*     target_flex_typing E t A -> target_flex_typing E t ttyp_top. *)
(* Proof. *)
(*   introv H. forwards*: flex_typing_wt H. *)
(* Qed. *)


(* Lemma flex_typing_property2 : forall E t At Bt, *)
(*     target_flex_typing E t At -> rec_typ Bt -> wf_typ Bt -> *)
(*     (forall ll Ct, Tlookup ll Bt = Some Ct -> exists Ct', Tlookup ll At = Some Ct' /\ eqIndTypTarget Ct Ct') -> *)
(*     target_flex_typing E t Bt. *)
(* Proof with eauto using flex_typing_top. *)
(*   introv HT HR HW HL. induction* HR... *)
(*   - forwards (?&Heq&?): HL ll. simpl. case_if*. *)
(*     applys* TFTyping_Cons. *)
(*     + forwards (?&?&?): flex_typing_property3 HT Heq. *)
(*       applys* TFTyping_Part. *)
(*     + applys IHHR. inverts* HW. *)
(*       introv LKB. applys HL. *)
(*       simpl. case_if*. subst*. *)
(*       * inverts HW. destruct H5. *)
(*         ** rewrite <- LKB. rewrite H. *)



(* Lemma flex_typing_property1 : forall E t ll At Ct, *)
(*     target_flex_typing E t (ttyp_rcd ll At Ct) -> rec_typ Ct -> *)
(*     target_flex_typing E t Ct. *)
(* Proof with eauto using flex_typing_top. *)
(*   introv HT HC. induction HC. *)
(*   - auto... *)
(*   - *)

(* Lemma flex_typing_property1 : forall E t C A B, *)
(*     target_flex_typing E t C -> *)
(*     concat_typ A B C -> *)
(*     target_flex_typing E t A /\ target_flex_typing E t B. *)
(* Proof with eauto using flex_typing_top. *)
(*   introv TC HC. induction HC. *)
(*   - split... *)
(*   - forwards (?&?&?): flex_typing_property3 ll TC. *)
(*     simpl. case_if*. split. *)
(*     + applys TFTyping_Cons. applys* TFTyping_Part. *)


(*   gen B C. *)
(*   induction A; intros; inverts HC... *)
(*   - split. *)
(*     + applys TFTyping_Cons. *)
(*   gen A B. *)
(*   induction C; intros; inverts HC... *)
(*   - clear IHC1. *)
(*     forwards: IHC2 H5. *)
(*   induction TC; intros; inverts HC... *)
(*   - forwards HW: target_typing_wf_typ H. inverts HW. *)
(*   gen B C. *)
(*   indTypSize (size_typ A). *)
(*   induction A; intros; inverts HC... *)
(*   - clear IHA1. forwards: IHA2 H5. destruct H. inverts* TC. split. *)

(*     + rewrite <- x0... *)
(*     + rewrite x... *)
(*   - split*. *)
(* Qed. *)


(* Lemma flex_typing_property1 : forall E t A B, *)
(*     target_flex_typing E t |[typ_and A B]| -> *)
(*     target_flex_typing E t |[A]| /\ target_flex_typing E t |[B]|. *)
(* Proof with eauto using flex_typing_top. *)
(*   introv H. *)
(*   lets HC: concat_source_intersection A B. *)
(*   inductions HC... *)
(*   - split. *)
(*     + rewrite <- x0... *)
(*     + rewrite x... *)
(*   - *)
(* Admitted. *)


(* (* non-deterministic lookup works *) *)
(* Lemma flex_typing_property2 : forall E t At Bt ll, *)
(*     target_flex_typing E t At -> contained_by_rec_typ At ll Bt -> *)
(*     target_typing E (texp_proj t ll) Bt. *)
(* Admitted. *)


(* (* every non-deterministic lookup can be separately typed *) *)
(* Lemma flex_typing_property3_alter : forall E t At ll Ct, *)
(*     target_flex_typing E t At -> contained_by_rec_typ At ll Ct -> *)
(*     exists Bt, target_typing E t Bt /\ Tlookup ll Bt = Some Ct. *)
(* Admitted. *)

Lemma comerge_split : forall t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> spl B A1 A2.
Proof.
  introv H.
  induction* H.
  - apply Sp_arrow.
    pick fresh x. applys* H0.
Qed.


(* new property: same label means same type *)
Lemma comerge_well_typed : forall E t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> target_typing E t1 |[A1]| -> target_typing E t2 |[A2]|
  -> target_typing E t |[B]|.
Proof with elia; try tassumption; eauto using target_typing_wf_1, target_typing_wf_2, TEI_refl.
  introv HC HTa HTb. gen E t1 t2 t B.
  indTypSize (size_typ A1 + size_typ A2). inverts HC.
  - applys* TTyping_RcdMerge HTa HTb.
    1,2: applys* translate_to_record_types.
    applys* concat_source_intersection.
  - (* abs *)
    rewrite ttyp_trans_ord_ntop_arrow...
    applys* TTyping_RcdCons.
    pick fresh x and apply TTyping_Abs...
    lets* Hc: H x.
    forwards: IH ( ( x, |[ A ]| ) :: E) Hc...
    1-2: applys TTyping_App...
    2,4: econstructor...
    1-2: applys TTyping_RcdProj...
    1,3: rewrite_env ( [ (x, |[ A ]|) ] ++  E); applys target_weakening_simpl.
    1,4: eassumption.
    1-4: simpl...
    all: rewrite ttyp_trans_ord_ntop_arrow...
    all: unfold Tlookup...
    all: case_if...
  - (* rcd *)
    rewrite ttyp_trans_rcd... applys* TTyping_RcdCons...
    forwards: IH E H...
    all: applys TTyping_RcdProj...
    all: rewrite ttyp_trans_rcd...
    all: unfold Tlookup...
    all: case_if...
Qed.


Lemma eqIndTypTarget_arrow_inv_3 : forall A B C,
    eqIndTypTarget C (ttyp_arrow A B) -> exists C1 C2, C = ttyp_arrow C1 C2.
Proof with eauto.
  introv HE. inductions HE...
  - forwards* (?&?&?): IHHE1. subst*.
    forwards* (?&?&?): IHHE2.
Admitted.


Lemma cosub_well_typed : forall E t1 A B t2 At,
    cosub t1 A B t2 -> target_typing E t1 At -> SubtypeTarget At |[A]| ->
    exists Bt', target_typing E t2 Bt' /\ eqIndTypTarget |[B]| Bt'.
Proof with elia; eauto using translate_to_record_types, target_typing_wf_1, target_typing_wf_2.
  introv HS HT ST. gen At t1 t2 E.
  indTypSize (size_typ A + size_typ B). inverts HS.
  - (* top *)
    forwards* EQ: ttyp_trans_ord_top B. rewrite EQ. exists. split...
  - (* bot *)
    lets* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ...
    exists. split. applys TTyping_RcdCons.
    3,6: applys TEI_refl. all: eauto.
    pick fresh y and apply TTyping_Fix.
    unfold open_texp_wrt_texp. simpl. applys TTyping_Var... applys TEI_refl.
  - (* base *)
    rewrite ttyp_trans_base...
    lets (?&?&?): subtype_wrt_lookup_same (|| typ_base ||) ST.
    (* lets (?&?&?&?&?): flex_typing_property3 (|| typ_base ||) HT. *)
    rewrite ttyp_trans_base. simpl...
    exists. split.
    applys TTyping_RcdCons. 4: applys TTyping_RcdProj H0.
    all: eauto...
  - (* arrow *)
    rewrite ttyp_trans_ord_ntop_arrow...
    lets (?&?&Eq): subtype_wrt_lookup_same (|| (typ_arrow A1 A2) ||) ST.
    (* lets* (?&?&?&?&?): flex_typing_property3 (|| (typ_arrow A1 A2) ||) HT. *)
    rewrite ttyp_trans_ord_ntop_arrow... simpl. case_if...
    forwards (?&?&Heq): eqIndTypTarget_arrow_inv_3 Eq. subst.
    forwards : eqIndTypTarget_arrow_inv_1 Eq.
    exists. split. applys TTyping_RcdCons.
    4: {
    pick fresh y and apply TTyping_Abs.
    lets* (HS1 & HS2): H1 y.
    lets (?&?&?): IH HS1 ((y, |[ B1 ]|) :: E)...
    { applys* subtype_refl... }
    { econstructor... }
    (* { applys flex_typing_property0. econstructor... } *)
    forwards: IH HS2...
    2: { (* applys flex_typing_property0... *)
      applys TTyping_App.
      rewrite_env ([ (y, |[ B1 ]|) ] ++ E).
      applys target_weakening_simpl...
      2: { applys* TEI_trans H3 H5. }
      eauto.
    }
    forwards *: eqIndTypTarget_arrow_inv_2 Eq.
                            applys TTyping_RcdProj HT.
lets (?&?&?): subtype_wrt_lookup_same (|| (typ_arrow A1 A2) ||) ST.
simpl. case_if*. rewrite ttyp_trans_ord_ntop_arrow...
destruct_uniq...

  - (* rcd *)
    rewrite ttyp_trans_rcd... applys* TTyping_RcdCons...
    forwards: IH H1 E...
    applys* flex_typing_property0.
    lets* (?&?&?): flex_typing_property3 (|| (typ_rcd l0 A0) ||) HT.
    rewrite ttyp_trans_rcd.
    unfold Tlookup. case_if...
  - (* and *)
    forwards* (?&?): flex_typing_property1 HT.
    applys* IH H0. elia.
  - (* and *)
    forwards* (?&?): flex_typing_property1 HT.
    applys* IH H0. elia.
  - (* comerge *)
    forwards*: IH H0. elia.
    forwards*: IH H1. elia.
    applys* comerge_well_typed H2.
Qed.


Lemma cosub_well_typed_relax : forall E t1 A B t2,
    cosub t1 A B t2 -> target_typing E t1 |[A]| -> target_typing E t2 |[B]|.
Proof.
  eauto using cosub_well_typed.
Qed.

(* (* previous aborted proof with the def of texp_behave_like_styp *) *)
(* Lemma cosub_well_typed : forall E t1 A A' B t2, *)
(*     cosub t1 A B t2 -> target_typing E t1 A' -> A' <: |[A]| -> target_typing E t2 |[B]|. *)
(* Proof with elia; eauto. *)
(*   introv HS HT. gen t1 t2 E A'. *)
(*   indTypSize (size_typ A + size_typ B). inverts HS. *)
(*   - (* top *) *)
(*     forwards* EQ: ttyp_trans_ord_top B. rewrite EQ... *)
(*   - (* bot *) *)
(*     forwards* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ... *)
(*     applys* TTyping_RcdCons... *)
(*     pick fresh y and apply TTyping_Fix... *)
(*     unfold open_texp_wrt_texp. simpl. applys TTyping_Var... *)
(*   - (* base *) *)
(*     rewrite ttyp_trans_base... *)
(*     applys* TTyping_RcdCons... applys* TTyping_RcdProj. *)
(*     forwards*: subtype_wrt_lookup_same H. rewrite ttyp_trans_base... *)
(*   - (* arrow *) *)
(*     rewrite ttyp_trans_ord_ntop_arrow... *)
(*     applys* TTyping_RcdCons... *)
(*     pick fresh y and apply TTyping_Abs. applys* ttyp_trans_wf. *)
(*     forwards* (HS1 & HS2): H2 y. *)
(*     forwards: IH HS1 ((y, |[ B1 ]|) :: E)... *)
(*     forwards: IH HS2... *)
(*     applys TTyping_App... applys TTyping_RcdProj... *)
(*     rewrite_env ([ (y, |[ B1 ]|) ] ++ E). *)
(*     { eauto using target_weakening_simpl. } *)
(*     forwards*: subtype_wrt_lookup_same H... *)
(*     rewrite ttyp_trans_ord_ntop_arrow... *)
(*     unfold Tlookup... case_if... *)
(*   - (* rcd *) *)
(*     rewrite ttyp_trans_rcd... applys* TTyping_RcdCons... *)
(*     forwards: IH H2 E... applys TTyping_RcdProj... *)
(*     forwards*: subtype_wrt_lookup_same H... *)
(*     rewrite ttyp_trans_rcd. *)
(*     unfold Tlookup. case_if... *)
(*   - (* and *) *)


Fixpoint context_trans (G:ctx) : tctx :=
  match G with
  | [] => []
  | (x, A) :: l => (x, |[A]|) :: (context_trans l)
  end.

Notation "||[ G ]||" := (context_trans G) (at level 1, G at next level).

Lemma ctx_trans_preserves_binds : forall x A G,
    binds x A G -> binds x |[A]| ||[G]||.
Proof.
  introv HB.
  induction* G.
  inverts HB.
  - applys in_eq.
  - destruct a. simpl. right.
    applys* IHG.
Qed.

Lemma ctx_trans_preserves_dom : forall G,
    dom ||[G]|| = dom G.
Proof.
  introv. induction* G. destruct a.
  simpl. rewrite* IHG.
Qed.

Lemma ctx_trans_preserves_uniq : forall G,
    uniq G -> uniq ||[G]||.
Proof.
  introv HU.
  induction HU; simpl; constructor*.
  rewrite* ctx_trans_preserves_dom.
Qed.

Lemma toplike_appdist_inv : forall A B C,
    appdist A (typ_arrow B C) -> toplike A -> toplike C.
Proof.
  introv HA HT. inductions HA.
  all: inverts* HT.
Qed.

Lemma distapp_well_typed_app : forall A B C G t1 t2 B' t3,
    appdist A (typ_arrow B C) -> target_flex_typing ||[ G ]|| t1 |[A]| ->
    target_flex_typing ||[ G ]|| t2 |[B']| -> distapp t1 A (tvl_exp t2) B' t3 ->
    target_typing ||[ G ]|| t3 |[C]|.
Proof with eauto using target_typing_wf_1.
  introv HA HTa HTb HD. gen t1 t2 t3 B'.
  inductions HA; intros; inverts HD...
  - rewrite* ttyp_trans_ord_top.
    inverts* H4.
  - applys* TTyping_App.
    forwards* (?&?&?): flex_typing_property3 (|| (typ_arrow B C) ||) HTa.
    rewrite ttyp_trans_ord_ntop_arrow.
    simpl. case_if...
    applys * cosub_well_typed.
  - rewrite* ttyp_trans_ord_top.
  - rewrite* ttyp_trans_ord_top.
    inverts H4. constructor; applys* toplike_appdist_inv.
  - forwards* (?&?): flex_typing_property1 HTa.
    forwards*: IHHA1 HTb. forwards*: IHHA2 HTb.
    applys* TTyping_RcdMerge H1 H2.
    all: eauto using concat_source_intersection, translate_to_record_types.
Qed.


Lemma distapp_well_typed_proj : forall A l B G t1 t3 C,
    appdist A (typ_rcd l B) -> target_typing ||[ G ]|| t1 |[A]| ->
    distapp t1 A (tvl_la l) C t3 ->
    target_typing ||[ G ]|| t3 |[B]|.
Proof with eauto using target_typing_wf_1.
  introv HA HT HD.
  inductions HA; inverts HD...
  - rewrite ttyp_trans_rcd in HT...
    applys* TTyping_RcdProj.
    simpl. case_if...
Qed.

(** via styp2ttyp to convert type *)
Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t ->
    target_typing ||[ G ]|| t |[A]|.
Proof with eauto using translate_to_record_types, target_typing_wf_1, ctx_trans_preserves_uniq.
  introv HT.
  induction HT...
  - rewrite* ttyp_trans_ord_top.
    applys TTyping_RcdNil...
  - rewrite* ttyp_trans_ord_top.
    applys TTyping_RcdNil...
  - rewrite* ttyp_trans_ord_top.
  - (* base *)
    rewrite* ttyp_trans_base.
    applys TTyping_RcdCons...
  - (* var *)
    apply ctx_trans_preserves_binds in H0...
  - (* abs *)
    rewrite ttyp_trans_ord_ntop_arrow...
    applys TTyping_RcdCons...
  - (* app *)
    applys* distapp_well_typed_app.
  - (* rcd *)
    rewrite ttyp_trans_rcd...
  - (* proj *)
    applys* distapp_well_typed_proj.
  - (* merge *)
    lets HC: concat_source_intersection A B.
    applys TTyping_RcdMerge IHHT1 IHHT2...
  - (* subsumption *)
    applys * cosub_well_typed_relax.
Qed.

  (* H : disjoint A B *)
  (* IHHT1 : target_typing ||[ G ]|| t1 |[ A ]| *)
  (* IHHT2 : target_typing ||[ G ]|| t2 |[ B ]| *)
  (* HC : concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]| *)
  (* ============================ *)
  (* target_typing ||[ G ]|| (texp_concat t1 t2) |[ (typ_and A B) ]| *)
