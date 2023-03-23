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


(* Definition target_flex_typing E t At := exists Bt, target_typing E t Bt /\ SubtypeTarget Bt At. *)


(* Lemma TS_andl : forall A B, SubtypeTarget |[typ_and A B]| |[A]|. *)
(* Admitted. *)

(* Lemma TS_andr : forall A B, SubtypeTarget |[typ_and A B]| |[B]|. *)
(* Admitted. *)

(* Lemma TS_eq : forall A B C, SubtypeTarget A B -> eqIndTypTarget A C -> SubtypeTarget C B. *)
(* Admitted. *)


(* Lemma subtype_wf_typ_1 : forall At Bt, *)
(*     SubtypeTarget At Bt -> wf_typ At. *)
(* Proof with eauto. *)
(*   introv HS. induction* HS. *)
(* Qed. *)

(* Lemma subtype_wf_typ_2 : forall At Bt, *)
(*     SubtypeTarget At Bt -> wf_typ Bt. *)
(* Proof with intuition eauto. *)
(*   introv HS. induction* HS. *)
(* Qed. *)

(* #[local] Hint Resolve subtype_wf_typ_1 subtype_wf_typ_2 : core. *)

(* Lemma subtype_wrt_lookup_same : forall A B l C, *)
(*     SubtypeTarget A B -> Tlookup l B = Some C -> *)
(*     exists C', Tlookup l A = Some C' /\ SubtypeTarget C' C. *)
(* Proof with intuition eauto using wf_typ_look_up_wf. *)
(*   introv HS HL. gen C. *)
(*   induction* HS; intros; inverts HL. *)
(*   - exists... *)
(*   - case_if*. *)
(*     + inverts H3. subst*. *)
(*     + forwards* (?&?&?): IHHS2. *)
(* Qed. *)

(* Lemma TS_trans : forall A B C, SubtypeTarget A B -> SubtypeTarget B C -> SubtypeTarget A C. *)
(* Proof. *)
(*   introv HSA HSB. gen A. *)
(*   induction* HSB; intros. *)
(*   - inverts* HSA. *)
(*   - forwards* (?&?&?): subtype_wrt_lookup_same H0. *)
(* Qed. *)



Lemma eqindtyptarget_subtypespec : forall At Bt,
    eqIndTypTarget At Bt ->
    rec_typ At -> rec_typ Bt ->
    subtype_wrt_lookup At Bt.
    (* Tlookup l At = Some A -> exists B, Tlookup l Bt = Some B /\ eqIndTypTarget A B. *)
Proof with eauto using TEI_trans, eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2.
  introv HE HRA HRB. unfolds. splits... introv HL. gen l B.
  induction* HE; intros; try solve_by_invert.
  - inverts HRA. inverts HRB.
    destruct (tindex_eq_dec l ll).
    + subst*. destruct_lookup HL. inverts HL.
      exists; split*. simpl. case_if*.
    + destruct_lookup HL.
      * forwards~ (?&?&?): IHHE2 HL.
        exists. split. simpl. case_if*. eauto.
      * intuition eauto.
  - inverts HRA. inverts H4.
    destruct (tindex_eq_dec l ll1).
    + destruct (tindex_eq_dec l ll2).
      * subst. intuition eauto.
      * subst. clear H0 H1.
        forwards~ (?&?&?): IHHE ll1 HL.
        unify_lookup.
        exists; simpl; repeat case_if*.
    + destruct (tindex_eq_dec l ll2).
      * subst. clear H0 H1.
        forwards~ (?&?&?): IHHE ll2 HL.
        unify_lookup.
        exists; simpl; repeat case_if*.
      * subst. clear H0 H1.
        forwards~ (?&?&?): IHHE l HL.
        unify_lookup.
        exists; simpl; repeat case_if*.
  - inverts HRA. inverts H2.
    forwards~ (?&?&?): IHHE2 l HL.
    destruct (tindex_eq_dec l ll).
    + subst.
      destruct_lookup H1. inverts H1.
      exists; splits; simpl; repeat case_if...
    + destruct_lookup H1. inverts H1.
      exists; splits; simpl; repeat case_if...
      intuition eauto.
Qed.


Lemma subtypespec_wrt_lookup_same : forall A B l C,
    subtype_wrt_lookup A B -> Tlookup l B = Some C ->
    exists C', Tlookup l A = Some C' /\ eqIndTypTarget C' C.
Proof with intuition eauto using  eqindtyptarget_wf_typ_1, wf_typ_look_up_wf.
  introv HS HL. unfold subtype_wrt_lookup in HS.
  intuition eauto.
  (* apply H4 in HL. destruct_conj. *)
  (* exists... applys~ eqindtyptarget_subtypespec. *)
Qed.

(* Lemma subtype_refl : forall At, *)
(*     rec_typ At -> wf_typ At -> SubtypeTarget At At. *)
(* Proof. *)
(*   introv HR HW. induction* HW; try solve_by_invert. *)
(* Qed. *)

(* Lemma subtype_complete : forall At Bt, *)
(*     eqIndTypTarget At Bt -> SubtypeTarget At Bt. *)
(* Proof with eauto using eqIndTypTarget_rec_typ, TS_trans. *)
(*   (* introv HRa HWa HRb HWb HE. *) *)
(*   introv HE. induction* HE... *)
(*   (* forwards*: IHHE1. forwards*: IHHE2... applys TS_trans. *) *)
(*   - applys TS_rcd... unify_lookup. *)
(*     applys TS_trans IHHE2. *)
(*     unify_lookup. Abort. *)
(* all: econstructor. *)
(*     { simpl. case_if*. } *)
(*     admit. *)
(*   - applys TS_trans IHHE. applys* TS_rcd. *)
(*     { simpl. case_if*. case_if*. } *)
(*     applys* TS_rcd. *)
(*     { simpl. case_if*. } *)
(*     admit. *)
(*   - applys TS_trans IHHE2. applys* TS_rcd. *)
(*     { simpl. case_if*. } *)
(*     applys* TS_rcd. *)
(*     { simpl. case_if*. } *)
(*     admit. *)
(* Admitted. *)

(* Lemma subtype_wide : forall l T At Bt, *)
(*     (forall l Ct, Tlookup l At = Some Ct -> eqIndTypTarget T Ct) -> *)
(*     rec_typ At -> SubtypeTarget At Bt -> *)
(*     SubtypeTarget (ttyp_rcd l T At) Bt. *)
(* Proof with try reflexivity. *)
(*   introv WF HR ST. gen At l T. *)
(*   induction* Bt; intros; try solve [inverts ST; inverts HR; solve_by_invert]. *)
(*   inverts ST. *)
(*   - (* refl *) forwards* [Heq|Heq]: lookup_wf_typ_1. *)
(*     + applys TS_rcd. *)
(*       2: { rewrite* Heq. *)
(*            simpl. case_if*. } *)
(*       3: { applys* IHBt2. applys* IHBt2. *)
(*            inverts* HR. introv LK. *)
(*            + subst*. forwards: lookup_wf_typ_2 WF. simpl. case_if*. *)
(*       applys TS_rcd. *)
(*       { simpl. case_if*. } *)
(*       { applys* subtype_complete. } *)
(*       { applys* IHBt2. applys* IHBt2. inverts* WF. inverts* HR. } *)
(*   - (* rcd *) forwards* [Heq|Heq]: lookup_wf_typ_1. *)
(*     + applys TS_rcd. rewrite* Heq. eauto. *)
(*       applys* IHBt2. *)
(*     + subst*. forwards*: lookup_wf_typ_2 WF. *)
(*       applys TS_rcd. *)
(*       { simpl. case_if*. } *)
(*       { applys* TS_trans Bt. applys* subtype_complete. } *)
(*       { applys* IHBt2. } *)
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

(* Lemma target_flex_typing_wf : forall E t A, *)
(*     target_flex_typing E t A -> uniq E. Admitted. *)
(* (* Proof with eauto using target_typing_wf_1; destruct_uniq; solve_uniq. *) *)
(* (*   introv H. *) *)
(* (*   induction* H. *) *)
(* (* Qed. *) *)


(* Lemma target_flex_typing_wf_2 : forall E t A, *)
(*     target_flex_typing E t A -> wf_ctx E.  Admitted. *)
(* (* Proof with eauto using target_typing_wf_2, context_wf_inv_1, context_wf_inv_2. *) *)
(* (*   introv H. induction* H. *) *)
(* (* Qed. *) *)

(* #[local] Hint Resolve target_flex_typing_wf target_flex_typing_wf_2 : core. *)

(* #[local] Hint Constructors target_typing : core. *)

(* (** flex_typing relaxes target typing **) *)
(* Lemma flex_typing_property0 : forall E t A, *)
(*     target_typing E t |[A]| -> target_flex_typing E t |[A]|.  Admitted. *)
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
(* Lemma flex_typing_wt : forall E t A, *)
(*     target_flex_typing E t A -> exists B, target_typing E t B. *)
(* Proof. *)
(*   introv HT. induction* HT. *)
(*   (* - forwards* (?&?&?): flex_typing_property3 ll At HT. *) *)
(*   (*   simpl. case_if*. *) *)
(* Qed. *)


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

(* Lemma comerge_split : forall t1 A1 t B t2 A2, *)
(*     comerge t1 A1 B t2 A2 t -> spl B A1 A2. *)
(* Proof. *)
(*   introv H. *)
(*   induction* H. *)
(*   - apply Sp_arrow. *)
(*     pick fresh x. applys* H0. *)
(* Qed. *)

(* Lemma eqIndTypTarget_top_inv : forall C, *)
(*     eqIndTypTarget C ttyp_top -> C = ttyp_top. *)
(* Proof with eauto; try solve_by_invert. *)
(*   introv HE. inductions HE... *)
(*   - forwards* : IHHE... *)
(*   - forwards* : IHHE2... *)
(* Qed. *)

Lemma TEI_cons : forall l A B A' B',
    eqIndTypTarget A A' -> eqIndTypTarget B B' ->
    wf_typ (ttyp_rcd l A B) -> wf_typ (ttyp_rcd l A' B') ->
    eqIndTypTarget (ttyp_rcd l A B) (ttyp_rcd l A' B').
Proof with eauto using eqIndTypTarget_rec_typ, TEI_symm.
  introv HEa HEb HWa HWb.
  inverts HWa. inverts HWb. econstructor...
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
  - forwards* (?&?&?): IHHE2. inverts keep H1. inverts H9.
    unify_lookup; lookup_concat ll H11...
    all: exists; split.
    1,3,5,7: econstructor; try solve [right*]; try solve [left*].
    1-4: econstructor; try solve [right*]; try solve [left*]...
    all: applys TEI_dup H2.
    all: try solve [right*]; try solve [left*]...
    all: eauto using eqindtyptarget_wf_typ_1, eqindtyptarget_wf_typ_2,
        wf_rcd_concat, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
    Unshelve. all: econstructor.
Qed.


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


Lemma eqIndTypTarget_arrow_inv_3 : forall A B C,
    eqIndTypTarget C (ttyp_arrow A B) -> exists C1 C2, C = ttyp_arrow C1 C2.
Proof with eauto; try solve_by_invert.
  introv HE. inductions HE...
  - forwards* (?&?&?): IHHE...
  - forwards* (?&?&?): IHHE2...
Qed.

(* new property: same label means same type *)
Lemma comerge_well_typed : forall E t1 A1 t B t2 A2 T1 T2,
    comerge t1 A1 B t2 A2 t ->
    target_typing E t1 T1 -> eqIndTypTarget T1 |[A1]| ->
    target_typing E t2 T2 -> eqIndTypTarget T2 |[A2]| ->
    exists T, target_typing E t T /\ eqIndTypTarget T |[B]|.
Proof with elia; try tassumption; eauto using target_typing_wf_1, target_typing_wf_2, TEI_refl, TEI_symm.
  introv HC HTa Eqa HTb Eqb. gen E t1 t2 t B T1 T2.
  indTypSize (size_typ A1 + size_typ A2). inverts HC.
  - forwards (?&?&?): eqindtyptarget_concat Eqa Eqb.
    applys* concat_source_intersection.
    exists. split.
    applys* TTyping_RcdMerge HTa HTb.
    all: now eauto using eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
  - (* abs *)
    apply TEI_symm in Eqa, Eqb.
    lets (?&?&?): eqIndTypTarget_lookup_some (|| typ_arrow A B1 ||) Eqa.
    2: lets (?&?&?): eqIndTypTarget_lookup_some (|| typ_arrow A B2 ||) Eqb.
    1-2: rewrite ttyp_trans_ord_ntop_arrow; simpl; case_if*.
    apply TEI_symm in H0. forwards(?&?&?): eqIndTypTarget_arrow_inv_3 H0. subst.
    forwards : eqIndTypTarget_arrow_inv_1 H0. forwards : eqIndTypTarget_arrow_inv_2 H0.
    apply TEI_symm in H2. forwards(?&?&?): eqIndTypTarget_arrow_inv_3 H2. subst.
    forwards : eqIndTypTarget_arrow_inv_1 H2. forwards : eqIndTypTarget_arrow_inv_2 H2.

    pick fresh y. lets Hc: H y.
    lets (?&?&?): IH ( ( y, |[ A ]| ) :: E) Hc. elia. now eauto.
    1,3: applys TTyping_App.
    2,5: econstructor...
    1,3: applys TTyping_RcdProj.
    1,3: rewrite_env ( [ (y, |[ A ]|) ] ++  E); applys target_weakening_simpl; try eassumption.
    1-6: eauto; eassumption.
    1-4: simpl...
    exists. split. applys* TTyping_RcdCons.
    pick fresh z and apply TTyping_Abs... forwards* : subst_var_typing H8.
    all: eauto.
    econstructor...
  - (* rcd *)
    apply TEI_symm in Eqa, Eqb.
    lets (?&?&?): eqIndTypTarget_lookup_some (|| typ_rcd l0 A0 ||) Eqa.
    2: lets (?&?&?): eqIndTypTarget_lookup_some (|| typ_rcd l0 A3 ||) Eqb.
    1-2: rewrite ttyp_trans_rcd... 1-2: simpl; case_if*.
    lets (?&?&?): IH E H...
    exists. split. applys* TTyping_RcdCons...
    econstructor...
    Unshelve. all: econstructor.
Qed.


Lemma cosub_well_typed : forall E t1 A B t2 At,
    cosub t1 A B t2 -> target_typing E t1 At -> subtype_wrt_lookup At |[A]| ->
    exists Bt', target_typing E t2 Bt' /\ eqIndTypTarget Bt' |[B]|.
Proof with elia; eauto using TEI_symm, translate_to_record_types, target_typing_wf_1, target_typing_wf_2, target_typing_wf_typ, subtypespec_refl, subtypespec_trans.
  introv HS HT ST. gen At t1 t2 E.
  indTypSize (size_typ A + size_typ B). inverts HS.
  - (* top *)
    forwards* EQ: ttyp_trans_ord_top B. rewrite EQ. exists. split...
  - (* bot *)
    lets* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ...
    exists. split. applys TTyping_RcdCons.
    5: applys TEI_refl. 2: right.
    all: eauto.
    pick fresh y and apply TTyping_Fix.
    unfold open_texp_wrt_texp. simpl. applys TTyping_Var... applys~ TEI_refl.
  - (* base *)
    rewrite ttyp_trans_base...
    lets (?&?&?): subtypespec_wrt_lookup_same (|| typ_base ||) ST.
    (* lets (?&?&?&?&?): flex_typing_property3 (|| typ_base ||) HT. *)
    rewrite ttyp_trans_base. simpl...
    exists. split.
    applys TTyping_RcdCons. 3: applys TTyping_RcdProj H0.
    all: eauto...
  - (* arrow *)
    lets (?&?&Eq): subtypespec_wrt_lookup_same (|| (typ_arrow A1 A2) ||) ST.
    (* lets* (?&?&?&?&?): flex_typing_property3 (|| (typ_arrow A1 A2) ||) HT. *)
    rewrite ttyp_trans_ord_ntop_arrow... simpl. case_if...
    forwards (?&?&Heq): eqIndTypTarget_arrow_inv_3 Eq. subst.
    forwards : eqIndTypTarget_arrow_inv_1 Eq.
    forwards *: eqIndTypTarget_arrow_inv_2 Eq.

    pick fresh y.
    lets* (HS1 & HS2): H1 y.
    lets (?&?&?): IH HS1 ((y, |[ B1 ]|) :: E)...
    { econstructor... }
    (* { applys flex_typing_property0. econstructor... } *)
    lets (?&?&?): IH HS2. elia.
    2: { (* applys flex_typing_property0... *)
      applys TTyping_App.
      rewrite_env ([ (y, |[ B1 ]|) ] ++ E).
      applys TTyping_RcdProj H2.
      applys target_weakening_simpl...
      tassumption.
      eauto using TEI_trans, TEI_symm.
      }
      applys* eqindtyptarget_subtypespec.
      applys eqIndTypTarget_rec_typ. applys TEI_symm H4.
      1-2: eauto using translate_to_record_types.

      exists. split. applys TTyping_RcdCons.
      3: {
        pick fresh z and apply TTyping_Abs.
        forwards* : subst_var_typing H7.
        solve_notin.
      }
      3: eauto.
      2: right*.
      1: now eauto.
      rewrite ttyp_trans_ord_ntop_arrow...
      econstructor... econstructor... applys TEI_refl...
  - (* rcd *)
    lets (?&?&Eq): subtypespec_wrt_lookup_same (|| typ_rcd l0 A0 ||) ST.
    rewrite ttyp_trans_rcd... simpl. case_if*.
    forwards* (?&?&?): IH H1 E... applys* eqindtyptarget_subtypespec...
    applys eqIndTypTarget_rec_typ. applys TEI_symm Eq. applys* translate_to_record_types.
    exists. split.
    applys* TTyping_RcdCons...
    econstructor...
  - (* and *)
    (* forwards*: TEI_refl (|[ A0 ]|)... *)
    (* forwards*: eqindtyptarget_subtypespec (|[ A0 ]|)... *)
    applys* IH H0 HT... applys subtypespec_trans ST subtypespec_andl.
  - (* and *)
    applys* IH H0 HT... applys subtypespec_trans ST subtypespec_andr.
  - (* comerge *)
    forwards* (?&?&Eq1): IH H0. elia.
    forwards* (?&?&Eq2): IH H1. elia.
    forwards(?&?&?): comerge_well_typed H2; try eassumption.
    exists. split*...
    Unshelve. all: econstructor.
Qed.

(* Lemma cosub_well_typed : forall E t1 A B t2 At, *)
(*     cosub t1 A B t2 -> target_typing E t1 At -> SubtypeTarget At |[A]| -> *)
(*     exists Bt', target_typing E t2 Bt' /\ eqIndTypTarget |[B]| Bt'. *)
(* Proof with elia; eauto using TEI_symm, translate_to_record_types, target_typing_wf_1, target_typing_wf_2. *)
(*   introv HS HT ST. gen At t1 t2 E. *)
(*   indTypSize (size_typ A + size_typ B). inverts HS. *)
(*   - (* top *) *)
(*     forwards* EQ: ttyp_trans_ord_top B. rewrite EQ. exists. split... *)
(*   - (* bot *) *)
(*     lets* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ... *)
(*     exists. split. applys TTyping_RcdCons. *)
(*     5: applys TEI_refl. 2: right. *)
(*     all: eauto. *)
(*     pick fresh y and apply TTyping_Fix. *)
(*     unfold open_texp_wrt_texp. simpl. applys TTyping_Var... applys~ TEI_refl. *)
(*   - (* base *) *)
(*     rewrite ttyp_trans_base... *)
(*     lets (?&?&?): subtype_wrt_lookup_same (|| typ_base ||) ST. *)
(*     (* lets (?&?&?&?&?): flex_typing_property3 (|| typ_base ||) HT. *) *)
(*     rewrite ttyp_trans_base. simpl... *)
(*     exists. split. *)
(*     applys TTyping_RcdCons. 3: applys TTyping_RcdProj H0. *)
(*     all: eauto... econstructor... *)
(*   - (* arrow *) *)
(*     rewrite ttyp_trans_ord_ntop_arrow... *)
(*     lets (?&?&Eq): subtype_wrt_lookup_same (|| (typ_arrow A1 A2) ||) ST. *)
(*     (* lets* (?&?&?&?&?): flex_typing_property3 (|| (typ_arrow A1 A2) ||) HT. *) *)
(*     rewrite ttyp_trans_ord_ntop_arrow... simpl. case_if... *)
(*     forwards (?&?&Heq): eqIndTypTarget_arrow_inv_3 Eq. subst. *)
(*     forwards : eqIndTypTarget_arrow_inv_1 Eq. *)
(*     exists. split. applys TTyping_RcdCons. *)
(*     4: { *)
(*     pick fresh y and apply TTyping_Abs. *)
(*     lets* (HS1 & HS2): H1 y. *)
(*     lets (?&?&?): IH HS1 ((y, |[ B1 ]|) :: E)... *)
(*     { applys* subtype_refl... } *)
(*     { econstructor... } *)
(*     (* { applys flex_typing_property0. econstructor... } *) *)
(*     forwards: IH HS2... *)
(*     2: { (* applys flex_typing_property0... *) *)
(*       applys TTyping_App. *)
(*       rewrite_env ([ (y, |[ B1 ]|) ] ++ E). *)
(*       applys target_weakening_simpl... *)
(*       2: { applys* TEI_trans H3 H5. } *)
(*       eauto. *)
(*     } *)
(*     forwards *: eqIndTypTarget_arrow_inv_2 Eq. *)
(*                             applys TTyping_RcdProj HT. *)
(* lets (?&?&?): subtype_wrt_lookup_same (|| (typ_arrow A1 A2) ||) ST. *)
(* simpl. case_if*. rewrite ttyp_trans_ord_ntop_arrow... *)
(* destruct_uniq... *)

(*   - (* rcd *) *)
(*     rewrite ttyp_trans_rcd... applys* TTyping_RcdCons... *)
(*     forwards: IH H1 E... *)
(*     applys* flex_typing_property0. *)
(*     lets* (?&?&?): flex_typing_property3 (|| (typ_rcd l0 A0) ||) HT. *)
(*     rewrite ttyp_trans_rcd. *)
(*     unfold Tlookup. case_if... *)
(*   - (* and *) *)
(*     forwards* (?&?): flex_typing_property1 HT. *)
(*     applys* IH H0. elia. *)
(*   - (* and *) *)
(*     forwards* (?&?): flex_typing_property1 HT. *)
(*     applys* IH H0. elia. *)
(*   - (* comerge *) *)
(*     forwards*: IH H0. elia. *)
(*     forwards*: IH H1. elia. *)
(*     applys* comerge_well_typed H2. *)
(* Qed. *)


Lemma cosub_well_typed_relax : forall E t1 A B t2 A',
    cosub t1 A B t2 -> target_typing E t1 A' -> eqIndTypTarget A' |[A]| ->
    exists B', target_typing E t2 B' /\ eqIndTypTarget B' |[B]|.
Proof.
  intuition eauto. applys* cosub_well_typed.
  applys* eqindtyptarget_subtypespec;
    eauto using eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
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

Lemma toplike_appdist_inv : forall A B C T t1 t2 t3,
    distapp t1 A t2 T t3 (typ_arrow B C) -> toplike A -> toplike C.
Proof.
  introv HA HT. inductions HA.
  all: inverts* HT. now inverts* H2.
Qed.

Lemma distapp_well_typed_app : forall A B C G t1 t2 t3 A' B',
    distapp t1 A t2 B t3 C ->
    target_typing ||[ G ]|| t1 A' -> subtype_wrt_lookup A' |[A]| ->
    target_typing ||[ G ]|| t2 B' -> subtype_wrt_lookup B' |[B]| ->
    exists C', target_typing ||[ G ]|| t3 C' /\ eqIndTypTarget C' |[C]|.
Proof with eauto using target_typing_wf_1, eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
  introv HA HTa HEa HTb HEb. gen A' B'.
  inductions HA; intros.
  - rewrite* ttyp_trans_ord_top.
  - forwards* (?&?&?): cosub_well_typed H0.
    lets (?&?&?): subtypespec_wrt_lookup_same (|| (typ_arrow A B) ||) HEa.
    rewrite ttyp_trans_ord_ntop_arrow. simpl. case_if...
    forwards(?&?&?): eqIndTypTarget_arrow_inv_3 H4. subst.
    forwards: eqIndTypTarget_arrow_inv_1 H4. forwards : eqIndTypTarget_arrow_inv_2 H4.
    exists. split. applys TTyping_App.
    econstructor. 1-3: now eauto.
    all: eauto using TEI_trans, TEI_symm.
  - forwards* (?&?&?): IHHA1 HTb. eauto using subtypespec_andl, subtypespec_trans.
    forwards* (?&?&?): IHHA2 HTb. eauto using subtypespec_andr, subtypespec_trans.
    forwards* (?&?&?): eqindtyptarget_concat H0 H2.
    applys* concat_source_intersection.
    exists. split. applys* TTyping_RcdMerge H H1.
    all: eauto using eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
Qed.


Lemma distapp_well_typed_proj : forall A l t1 t3 C G A',
    proj t1 A l t3 C -> target_typing ||[ G ]|| t1 A' -> subtype_wrt_lookup A' |[A]| ->
    exists C', target_typing ||[ G ]|| t3 C' /\ eqIndTypTarget C' |[C]|.
Proof with eauto using target_typing_wf_1.
  introv HA HT HS.
  inductions HA...
  - rewrite* ttyp_trans_ord_top.
  - lets (?&?&?): subtypespec_wrt_lookup_same (|| typ_rcd l A ||) HS.
    simpl. case_if...
    exists. split. applys* TTyping_RcdProj. now eauto.
  - rewrite* ttyp_trans_ord_top.
  - forwards* (?&?&?): IHHA1 HT. eauto using subtypespec_andl, subtypespec_trans.
    forwards* (?&?&?): IHHA2 HT. eauto using subtypespec_andr, subtypespec_trans.
    forwards* (?&?&?): eqindtyptarget_concat H0 H2.
    applys* concat_source_intersection.
    exists. split. applys* TTyping_RcdMerge H H1.
    all: eauto using eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
Qed.

(** via styp2ttyp to convert type *)
Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t ->
    exists A', target_typing ||[ G ]|| t A' /\  eqIndTypTarget A' |[A]|.
Proof with eauto using elaboration_wf_ctx, translate_to_record_types, target_typing_wf_1, ctx_trans_preserves_uniq, TEI_refl, TEI_symm, TEI_trans, eqindtyptarget_subtypespec.
  introv HT.
  induction HT...
  - rewrite* ttyp_trans_ord_top.
    exists. split. applys TTyping_RcdNil... eauto using TEI_refl.
  - rewrite* ttyp_trans_ord_top.
    exists. split. applys TTyping_RcdNil... eauto using TEI_refl.
  - rewrite* ttyp_trans_ord_top.
  - (* base *)
    rewrite* ttyp_trans_base.
    exists. split. applys TTyping_RcdCons.
    4: eauto...
    all: eauto...
  - (* var *)
    apply ctx_trans_preserves_binds in H0...
    exists. split*. econstructor... applys TEI_refl. eauto using target_context_binds_wf.
  - (* fix *)
    pick fresh x. forwards~ (?&?&?): H0 x.
    exists. split. remember ||[ G ]||. pick fresh y and apply TTyping_Fix.
    applys subst_var_typing H1...
    all: eauto.
  - (* abs *)
    pick fresh x. forwards~ (?&?&?): H0 x.
    forwards: target_typing_wf_2 H1. inverts H3.
    forwards: target_typing_wf_1 H1. inverts H3.
    rewrite ttyp_trans_ord_ntop_arrow...
    exists. split. applys TTyping_RcdCons.
    4: eauto...
    3: { remember ||[ G ]||.
         pick fresh y and apply TTyping_Abs.
         applys subst_var_typing H1.
         all: eauto.
    }
    3: econstructor.
    all: eauto.
    econstructor...
  - (* app *)
    destruct_conj. applys* distapp_well_typed_app...
    all: eauto using eqindtyptarget_subtypespec, eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
  - (* rcd *)
    rewrite ttyp_trans_rcd...
    destruct_conj. exists. split. applys TTyping_RcdCons H.
    3: eauto. all: eauto.
  - (* proj *)
    destruct_conj. applys* distapp_well_typed_proj.
    all: eauto using eqindtyptarget_subtypespec, eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
  - (* merge *)
    destruct_conj.
    lets HC: concat_source_intersection A B.
    forwards* (?&?&?): eqindtyptarget_concat HC.
    exists. split.
    applys TTyping_RcdMerge H2 H0...
    all: eauto using eqindtyptarget_subtypespec, eqIndTypTarget_rec_typ, TEI_symm, translate_to_record_types.
  - (* subsumption *)
    destruct_conj. forwards* (?&?&?): cosub_well_typed_relax H.
    Unshelve. all: econstructor.
Qed.
