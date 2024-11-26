Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Translation.
Require Export TargetTypeSafety.

(* Type safety *)
(** The key is to prove the lookup label does exists in the record *)
(** To prove type safety, we need to translate typing contexts / types *)

#[local] Hint Resolve target_typing_wf_1 target_typing_wf_2 ttyp_trans_wf : core.
#[local] Hint Unfold Tlookup : core.

Fixpoint context_trans (G:ctx) : tctx :=
  match G with
  | nil => nil
  | (x, A) :: l => (x, |[A]|) :: (context_trans l)
  end.

Notation "||[ G ]||" := (context_trans G) (at level 1, G at next level).


Lemma elaboration_wf_ctx : forall G,
    uniq G  -> wf_ctx ||[G]||.
Proof with eauto using ttyp_trans_wf.
  introv HU. induction* G.
  simpl... destruct a... econstructor...
  inverts~ HU.
Qed.

Open Scope list.

Lemma comerge_split : forall t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> spl B A1 A2.
Proof.
  introv HC. induction* HC; pick fresh x; forwards: H2 x.
  all: eauto.
Qed.

Lemma comerge_toplike_l : forall t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> toplike B -> toplike A1.
Proof.
  introv HC HT. applys split_toplike_l HT. applys* comerge_split.
Qed.

Lemma comerge_toplike_r : forall t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> toplike B -> toplike A2.
Proof.
  introv HC HT. applys split_toplike_r HT. applys* comerge_split.
Qed.

Lemma comerge_well_typed : forall E t1 A1 t B t2 A2 T1 T2,
    comerge t1 A1 B t2 A2 t ->
    target_typing E t1 T1 -> subTarget T1 |[A1]| -> subTarget |[A1]| T1 ->
    target_typing E t2 T2 -> subTarget T2 |[A2]| -> subTarget |[A2]| T2 ->
    exists T, target_typing E t T /\ subTarget T |[B]| /\ subTarget |[B]| T.
Proof with elia; try tassumption;
intuition eauto using target_typing_wf_1, target_typing_wf_2,
  target_typing_wf_typ, ST_refl, ST_trans, ST_toplike, ST_top,
  translate_to_record_types, subTarget_rec_typ, ttyp_trans_wf.

  introv HC HTa Eqa Eqa' HTb Eqb Eqb'. gen E t1 t2 t B T1 T2.
  indTypSize (size_typ A1 + size_typ A2). inverts HC.
  - exists. splits;
      try rewrite ttyp_trans_ord_top; try rewrite* <- check_toplike_sound_complete...
  - forwards (?&?&?): ST_concat Eqa' Eqb'.
    applys* concat_source_intersection...
    1-4: auto... intuition eauto using target_typing_wf_typ.
    exists. split.
    applys* TTyping_RcdMerge HTa HTb.
    all: eauto...
  - (* abs *)
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B1 ||) Eqa. simpl. case_if*.
    { rewrite* <- check_toplike_sound_complete in C. contradiction. }
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B1 ||) Eqa'. eassumption.
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B2 ||) Eqb. simpl; case_if*.
    { rewrite* <- check_toplike_sound_complete in C. contradiction. }
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B2 ||) Eqb'. eassumption.
    forwards* (?&?&?&?&?&?&?): ST_arrow_inv H3. subst*.
    forwards* (?&?&?&?&?&?&?): ST_arrow_inv H7. subst*.

    pick fresh y. lets Hc: H1 y.
    lets (?&?&?): IH ( ( y, |[ A ]| ) :: E) Hc. elia. now eauto.
    1,4: applys TTyping_App.
    3,6: split.
    1,7: applys TTyping_RcdProj.
    1,3: rewrite_env ( [ (y, |[ A ]|) ] ++  E); applys target_weakening_simpl; try eassumption.
    all: try eassumption.
    5,6: econstructor...
    all: auto...
    exists. split. applys* TTyping_RcdCons.
    pick fresh z and apply TTyping_Abs... forwards* : subst_var_typing.
    all: eauto. split...
    simpl. case_if*. now applys* ST_top_2. now applys* ST_rcd_2.
    simpl. case_if*. {
      exfalso. applys H. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_l.
    }
    now applys* ST_rcd_2.
  - (* abs *)
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B1 ||) Eqa. simpl. case_if*.
    { rewrite* <- check_toplike_sound_complete in C. contradiction. }
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B1 ||) Eqa'. eassumption.
    forwards* (?&?&?&?&?&?&?): ST_arrow_inv H4. subst*.

    pick fresh y. lets Hc: H2 y.
    lets (?&?&?): IH ( ( y, |[ A ]| ) :: E) Hc. elia. now eauto.
    1: applys TTyping_App. 6: econstructor...
    3: split.
    1: applys TTyping_RcdProj.
    1: rewrite_env ( [ (y, |[ A ]|) ] ++  E); applys target_weakening_simpl; try eassumption.
    all: try eassumption.
    3: econstructor...
    all: auto...
    exists. split. applys* TTyping_RcdCons.
    pick fresh z and apply TTyping_Abs... forwards* : subst_var_typing.
    all: eauto. split.
    simpl. case_if*. now applys* ST_top_2. now applys* ST_rcd_2.
    simpl. case_if*. {
      exfalso. applys H0. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_l.
    }
    now applys* ST_rcd_2.
  - (* abs *)
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B2 ||) Eqb. simpl; case_if*.
    { rewrite* <- check_toplike_sound_complete in C. contradiction. }
    lets (?&?&?): lookup_ST_sub (|| typ_arrow A B2 ||) Eqb'. eassumption.
    forwards* (?&?&?&?&?&?&?): ST_arrow_inv H4. subst*.

    pick fresh y. lets Hc: H2 y.
    lets (?&?&?): IH ( ( y, |[ A ]| ) :: E) Hc. elia. now eauto.
    4: applys TTyping_App. 1: econstructor...
    5: split.
    3: applys TTyping_RcdProj.
    3: rewrite_env ( [ (y, |[ A ]|) ] ++  E); applys target_weakening_simpl; try eassumption.
    all: try eassumption.
    5: econstructor...
    all: auto...
    exists. split. applys* TTyping_RcdCons.
    pick fresh z and apply TTyping_Abs... forwards* : subst_var_typing.
    all: eauto. split.
    simpl. case_if*. {
      exfalso. applys H1. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    }
    now applys* ST_rcd_2.
    simpl. case_if*.  {
      exfalso. applys H1. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    } now applys* ST_rcd_2.
  - (* rcd *)
    assert (Tlookup (|| typ_rcd l0 A0 ||) |[ (typ_rcd l0 A0) ]| = Some |[A0]|).
    { simpl. case_if*.
      - rewrite* <- check_toplike_sound_complete in C. contradiction.
    }
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A0 ||) Eqa.
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A0 ||) Eqa'. unify_lookup.
    assert (Tlookup (|| typ_rcd l0 A3 ||) |[ (typ_rcd l0 A3) ]| = Some |[A3]|).
    { simpl. case_if*.
      - rewrite* <- check_toplike_sound_complete in C. contradiction.
    }
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A3 ||) Eqb.
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A3 ||) Eqb'. unify_lookup.

    lets (?&?&?&?): IH E H1. elia. econstructor...
    3: econstructor... 1-4 : auto...
    exists. splits. applys* TTyping_RcdCons...
    simpl. case_if*. now applys* ST_top_2. now applys* ST_rcd_2.
    simpl. case_if*. {
      exfalso. applys H. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_l.
    }
    now applys* ST_rcd_2.
  - (* rcd *)
    assert (Tlookup (|| typ_rcd l0 A0 ||) |[ (typ_rcd l0 A0) ]| = Some |[A0]|).
    { simpl. case_if*.
      - rewrite* <- check_toplike_sound_complete in C. contradiction.
    }
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A0 ||) Eqa.
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A0 ||) Eqa'. unify_lookup.

    lets (?&?&?&?): IH E H2. elia. econstructor...
    3: econstructor... 1-4 : auto...
    exists. splits. applys* TTyping_RcdCons...
    simpl. case_if*. now applys* ST_top_2. now applys* ST_rcd_2.
    simpl. case_if*. {
      exfalso. applys H0. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_l.
    }
    now applys* ST_rcd_2.
  - (* rcd *)
    assert (Tlookup (|| typ_rcd l0 A3 ||) |[ (typ_rcd l0 A3) ]| = Some |[A3]|).
    { simpl. case_if*.
      - rewrite* <- check_toplike_sound_complete in C. contradiction.
    }
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A3 ||) Eqb.
    lets* (?&?&?): lookup_ST_sub (|| typ_rcd l0 A3 ||) Eqb'. unify_lookup.

    lets (?&?&?&?): IH E H2. elia. econstructor...
    3: econstructor... 1-4 : auto...
    exists. splits. applys* TTyping_RcdCons...
    simpl. case_if*. now applys* ST_top_2. now applys* ST_rcd_2.
    simpl. case_if*. {
      exfalso. applys H1. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    }
    now applys* ST_rcd_2.
    Unshelve. all: eauto.
Qed.

Lemma check_toplike_false_2 : forall B,
    ~ toplike B -> check_toplike B = false.
Proof.
  introv TL. remember (check_toplike B). destruct* b.
  exfalso. applys TL. rewrite* check_toplike_sound_complete.
Qed.

#[local] Hint Resolve check_toplike_false_2 : core.

Lemma split_toplike : forall A B C,
    spl A B C -> toplike B -> toplike C -> toplike A.
Proof.
  introv HS HT1 HT2.
  induction* HS.
  all: inverts HT1; inverts* HT2.
Qed.

Lemma cosub_not_toplike : forall t1 t2 A B,
    cosub t1 A B t2 -> ~ toplike B -> ~ toplike A.
Proof.
  introv HC HT HTA. applys HT. clear HT. gen t1 t2.
  indTypSize (size_typ A + size_typ B).
  inverts HC. 1-7: inverts~ HTA.
  - pick fresh x; try lets (?&?&?): H1 x. intuition eauto.
    forwards*: IH H4. elia.
  - forwards*: IH H1. elia.
  - forwards*: IH H0. elia.
  - forwards*: IH H0. elia.
  - forwards*: IH H0. elia. forwards*: IH H1. elia.
    eauto using split_toplike.
Qed.

(** *********************************** *)
#[local] Hint Constructors esub : core.

Lemma esub_is_term_erased_cosub_1 : forall A B,
    (exists t1 t2, cosub t1 A B t2) -> esub A B.
Proof with elia.
  intros. destruct_conj. gen x x0.
  indTypSize (size_typ A + size_typ B).
  destruct* H.
  + { pick fresh x.
      forwards* (?&Hx1&Hx2): H1 x.
      forwards: IH Hx1... forwards: IH Hx2... applys* ES_Arrow. }
  + { forwards: IH H1... eauto. }
  + { forwards: IH H0... eauto. }
  + { forwards: IH H0... eauto. }
  + { forwards: IH H0... forwards: IH H1... eauto. }
Qed.

Lemma comerge_lc_texp : forall t1 A B t2 C t3,
    comerge t1 A B t2 C t3 -> lc_texp t3.
Proof with elia.
  introv HC. gen t1 t2 t3 A B.
  indTypSize (size_typ C).
  destruct* HC.
  - { econstructor. pick fresh x. forwards* Hx: H1 x.
      forwards: IH Hx...
      applys* lc_texp_abs_exists. eauto. }
  - { econstructor. pick fresh x. forwards* Hx: H2 x.
      forwards: IH Hx...
      applys* lc_texp_abs_exists. eauto. }
  - { econstructor. pick fresh x. forwards* Hx: H2 x.
      forwards: IH Hx...
      applys* lc_texp_abs_exists. eauto. }
  - repeat econstructor; forwards~: IH HC...
  - repeat econstructor; forwards~: IH HC...
  - repeat econstructor; forwards~: IH HC...
Qed.

Lemma comerge_lc_texp_1 : forall t1 A t2 B C t3,
    comerge t1 A B t2 C t3 -> lc_texp t1.
Proof with elia.
  introv HC. gen t1 t2 t3 A C.
  indTypSize (size_typ B). inverts* HC.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H1... inverts H2. inverts ~H5.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H2... inverts H3. inverts ~H6.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H1... inverts~ H2.
  - forwards: IH H2... inverts~ H3.
Qed.

Lemma comerge_lc_texp_2 : forall t1 A t2 B C t3,
    comerge t1 A B t2 C t3 -> lc_texp t2.
Proof with elia.
  introv HC. gen t1 t2 t3 A C.
  indTypSize (size_typ B). inverts* HC.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H1... inverts H2. inverts ~H5.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H2... inverts H3. inverts ~H6.
  - pick fresh x. instantiate_cofinites_with x.
    forwards: IH H1... inverts~ H2.
  - forwards: IH H2... inverts~ H3.
Qed.


Lemma cosub_lc_texp : forall A B t1 t2,
    cosub t1 A B t2 -> lc_texp t2.
Proof with elia.
  introv HC. gen t1 t2.
  indTypSize (size_typ A + size_typ B).
  destruct* HC.
  2: { econstructor. pick fresh x. forwards* (?& Hx): H1 x.
       forwards: IH Hx...
       applys* lc_texp_abs_exists. eauto. }
  all: repeat econstructor.
  all: try forwards~: IH HC...
  eauto using comerge_lc_texp.
Qed.

Lemma toplike_dec : forall A, { toplike A } + { ~ toplike A }.
Proof.
  introv.
  remember (check_toplike A) as P. destruct P.
  - left*. applys* check_toplike_sound_complete.
  - right*. lets*: check_toplike_false A.
Qed.


Notation "[ z ~~> u ] t" := (subst_texp u z t) (at level 0).
Notation "[ x ~=> y ] t" := (subst_texp (texp_var_f y) x t) (at level 0).
Notation "t ^-^ u"       := (open_texp_wrt_texp t u) (at level 67).
Notation "t -^ x"        := (open_texp_wrt_texp t (texp_var_f x))(at level 67).

#[local] Hint Resolve subst_texp_lc_texp comerge_lc_texp comerge_lc_texp_1 comerge_lc_texp_2 : core.

Ltac simp_eq Eq :=
  let Heq := fresh "Heq" in
  assert (Heq: Eq) by default_simp ; rewrite Heq.

Ltac simp_eq_in Eq H :=
  let Heq := fresh "Heq" in
  assert (Heq: Eq) by default_simp ; rewrite Heq in H.

Lemma comerge_rename : forall t1 t2 t3 A B C x y,
    (* y `notin` ((fv_texp t1) `union` (fv_texp t2)) -> *)
    comerge t1 B A t2 C t3 ->
    comerge ([ x ~=> y ] t1) B A ([ x ~=> y ] t2) C ([ x ~=> y ] t3).
Proof with try solve_notin.
  introv HC. gen x y.
  induction HC; intros.
  1-2: default_simp.
  5: {
    applys~ M_RcdL.
    forwards: IHHC x y...  }
  5: {
    applys~ M_RcdR.
    forwards: IHHC x y...  }
  4: {
    simp_eq ([x ~=> y] (texp_cons (|| typ_rcd l A ||) t texp_nil) = (texp_cons (|| typ_rcd l A ||) ([x ~=> y] t) texp_nil) ).
    applys~ M_Rcd.
    forwards: IHHC x y...
  }
  3: {
    remember (|| typ_arrow A B1 ||) as l1.
    remember (|| typ_arrow A B2 ||) as l2.
    remember (|| typ_arrow A B ||) as l.
    simp_eq ([x ~=> y] (texp_cons l (texp_abs t) texp_nil) =  texp_cons l (texp_abs ([x ~=> y] t)) texp_nil).
    rewrite Heql.
    applys* M_ArrowR ((L \u {{x}} \u {{y}})).
    intros z Fr_z.
    forwards: H3 z x y...
    rewrite~ subst_texp_open_texp_wrt_texp in H4.
    simp_eq_in ([x ~=> y] (texp_var_f z) = texp_var_f z) H4.
    rewrite <- Heql2. case_if*. { subst. solve_notin. }
  }
  2: {
    remember (|| typ_arrow A B1 ||) as l1.
    remember (|| typ_arrow A B2 ||) as l2.
    remember (|| typ_arrow A B ||) as l.
    simp_eq ([x ~=> y] (texp_cons l (texp_abs t) texp_nil) =  texp_cons l (texp_abs ([x ~=> y] t)) texp_nil).
    rewrite Heql.
    applys* M_ArrowL ((L \u {{x}} \u {{y}})).
    intros z Fr_z.
    forwards: H3 z x y...
    rewrite~ subst_texp_open_texp_wrt_texp in H4.
    simp_eq_in ([x ~=> y] (texp_var_f z) = texp_var_f z) H4.
    rewrite <- Heql1. case_if*. { subst. solve_notin. }
  }
  1: {
    remember (|| typ_arrow A B1 ||) as l1.
    remember (|| typ_arrow A B2 ||) as l2.
    remember (|| typ_arrow A B ||) as l.
    simp_eq ([x ~=> y] (texp_cons l (texp_abs t) texp_nil) =  texp_cons l (texp_abs ([x ~=> y] t)) texp_nil).
    rewrite Heql.
    applys* M_Arrow ((L \u {{x}} \u {{y}})).
    intros z Fr_z.
    forwards: H2 z x y...
    rewrite~ subst_texp_open_texp_wrt_texp in H3.
    simp_eq_in ([x ~=> y] (texp_var_f z) = texp_var_f z) H3.
    rewrite <- Heql1. rewrite <- Heql2. case_if*. { subst. solve_notin. }
  }
Qed.

Lemma fv_texp_comerge : forall t1 t2 t3 A B C,
    comerge t1 A C t2 B t3 -> (fv_texp t3) [<=] (fv_texp t1) \u (fv_texp t2).
Proof with simpl; try fsetdec.
  introv HC. induction* HC...
  - instantiate_cofinites.
    pose proof fv_texp_open_texp_wrt_texp_lower t (texp_var_f x).
    simpl in H2...
  - instantiate_cofinites.
    pose proof fv_texp_open_texp_wrt_texp_lower t (texp_var_f x).
    simpl in H3...
  - instantiate_cofinites.
    pose proof fv_texp_open_texp_wrt_texp_lower t (texp_var_f x).
    simpl in H3...
Qed.

Lemma cosub_rename : forall t1 t2 A B x y,
    (* y `notin` ((fv_texp t1) `union` (fv_texp t2)) -> *)
    cosub t1 A B t2 ->
    cosub ([ x ~=> y ] t1) A B ([ x ~=> y ] t2).
Proof with elia; try solve_notin.
  introv HC. gen x y t1 t2. indTypSize (size_typ A + size_typ B).
  destruct* HC.
  7: {
    forwards: comerge_rename x y H0...
    forwards: IH HC1... forwards: IH HC2...
    eauto.
  }
  5, 6 : forwards: IH x y HC...
  2: {
    simp_eq ([x ~=> y] (texp_cons (|| typ_base ||) (texp_proj t (|| typ_base ||)) texp_nil) = (texp_cons (|| typ_base ||) (texp_proj ([x ~=> y] t) (|| typ_base || )) texp_nil)).
    eauto. }
  1: {
    simp_eq ([x ~=> y] (texp_cons (|| B ||) (texp_fixpoint (texp_var_b 0)) texp_nil) = (texp_cons (|| B ||) (texp_fixpoint (texp_var_b 0)) texp_nil)).
    eauto.
  }
  2: { (* rcd *)
    forwards: IH HC...
    simp_eq_in ( [x ~=> y] (texp_proj t (|| typ_rcd l A ||)) =  (texp_proj ([x ~=> y] t) (|| typ_rcd l A ||)) ) H1.
    simp_eq ( [x ~=> y] (texp_cons (|| typ_rcd l B ||) t2 texp_nil) = (texp_cons (|| typ_rcd l B ||) ([x ~=> y] t2) texp_nil)) .
    eauto.
  }
  1: { (* arrow *)
    simp_eq ( [x ~=> y] (texp_cons (|| typ_arrow B1 B2 ||) (texp_abs t2) texp_nil) = (texp_cons (|| typ_arrow B1 B2 ||) (texp_abs [x ~=> y] t2) texp_nil) ).
    applys~ S_Arrow (L \u {{x}}). intros z Fr.
    remember (|| typ_arrow A1 A2 ||) as l2.
    forwards* (?&?&?): H1 z.
    forwards: IH x y H2...
    simp_eq_in ([x ~=> y] (texp_var_f z) = texp_var_f z) H4.
    forwards: IH x y H3...
    simp_eq_in ([x ~=> y] (texp_app (texp_proj t l2) x0) = texp_app (texp_proj ([x ~=> y] t) l2) ([x ~=> y] x0)) H5.
    exists*. split*.
    rewrite~ subst_texp_open_texp_wrt_texp in H5.
    simp_eq_in ([x ~=> y] (texp_var_f z) = texp_var_f z) H5.
    eauto.
  }
Qed.

Theorem spl_sound_to_comerge : forall A B C t u,
    spl A B C -> lc_texp t -> lc_texp u -> exists z, comerge t B A u C z.
Proof with try fsetdec; elia.
  introv HS HL1 HL2. gen t u. induction HS; intros.
  - forwards* [?|?]: toplike_dec (typ_and A B).
  - forwards* [?|?]: toplike_dec (typ_arrow A B1);
      forwards* [?|?]: toplike_dec (typ_arrow A B2).
    + destruct_conj. forwards*: split_toplike (typ_arrow A B).
    + pick fresh y.
      remember (|| typ_arrow A B2 ||) as l1.
      forwards* (tt&HL): IHHS texp_nil (texp_app (texp_proj u l1) (texp_var_f y)).
      rewrite <- (open_texp_wrt_texp_close_texp_wrt_texp tt y) in HL.
      exists. applys* M_ArrowR ((fv_texp (texp_var_f y)) `union` (fv_texp tt) `union` (fv_texp t)`union` (fv_texp u) `union` (fv_texp tt)) (close_texp_wrt_texp y tt). inverts~ t0.
      introv Fr_x.
      forwards* HC: comerge_rename y x HL.
      rewrite <- Heql1.
      rewrite~ subst_texp_open_texp_wrt_texp in HC.
      assert (Heq: [y ~=> x] (texp_var_f y) = texp_var_f x).
      { default_simp. }
      rewrite Heq in HC.
      assert (Heq': [y ~=> x] texp_nil = texp_nil).
      { default_simp. }
      rewrite Heq' in HC.
      assert (Heq2: [y ~=> x] (texp_app (texp_proj u l1) (texp_var_f y)) = (texp_app (texp_proj u l1) (texp_var_f x))).
      { default_simp. rewrite* subst_texp_fresh_eq. }
      rewrite Heq2 in HC.
      assert (Heq3: [y ~=> x] (close_texp_wrt_texp y tt) = (close_texp_wrt_texp y tt)). {
        apply subst_texp_fresh_eq...
        rewrite fv_texp_close_texp_wrt_texp. eauto.
      }
      rewrite Heq3 in HC. simpl in HC. now auto.
    + pick fresh y.
      remember (|| typ_arrow A B1 ||) as l1.
      forwards* (tt&HL): IHHS (texp_app (texp_proj t l1) (texp_var_f y)) texp_nil .
      rewrite <- (open_texp_wrt_texp_close_texp_wrt_texp tt y) in HL.
      exists. applys* M_ArrowL ((fv_texp (texp_var_f y)) `union` (fv_texp tt) `union` (fv_texp t)`union` (fv_texp u) `union` (fv_texp tt)) (close_texp_wrt_texp y tt). inverts~ t0.
      introv Fr_x.
      forwards* HC: comerge_rename y x HL.
      rewrite <- Heql1.
      rewrite~ subst_texp_open_texp_wrt_texp in HC.
      assert (Heq: [y ~=> x] (texp_var_f y) = texp_var_f x).
      { default_simp. }
      rewrite Heq in HC.
      assert (Heq': [y ~=> x] texp_nil = texp_nil).
      { default_simp. }
      rewrite Heq' in HC.
      assert (Heq2: [y ~=> x] (texp_app (texp_proj t l1) (texp_var_f y)) = (texp_app (texp_proj t l1) (texp_var_f x))).
      { default_simp. rewrite* subst_texp_fresh_eq. }
      rewrite Heq2 in HC.
      assert (Heq3: [y ~=> x] (close_texp_wrt_texp y tt) = (close_texp_wrt_texp y tt)). {
        apply subst_texp_fresh_eq...
        rewrite fv_texp_close_texp_wrt_texp. eauto.
      }
      rewrite Heq3 in HC. simpl in HC. now auto.
    + pick fresh y.
      remember (|| typ_arrow A B1 ||) as l1.
      remember (|| typ_arrow A B2 ||) as l2.
      forwards* (tt&HL): IHHS (texp_app (texp_proj t l1) (texp_var_f y)) (texp_app (texp_proj u l2) (texp_var_f y)) .
      rewrite <- (open_texp_wrt_texp_close_texp_wrt_texp tt y) in HL.
      exists. applys* M_Arrow ((fv_texp (texp_var_f y)) `union` (fv_texp tt) `union` (fv_texp t)`union` (fv_texp u) `union` (fv_texp tt)) (close_texp_wrt_texp y tt).
      introv Fr_x.
      forwards* HC: comerge_rename y x HL.
      rewrite <- Heql1. rewrite <- Heql2.
      rewrite~ subst_texp_open_texp_wrt_texp in HC.
      assert (Heq: [y ~=> x] (texp_var_f y) = texp_var_f x).
      { default_simp. }
      rewrite Heq in HC.
      assert (Heq2: [y ~=> x] (texp_app (texp_proj t l1) (texp_var_f y)) = (texp_app (texp_proj t l1) (texp_var_f x))).
      { default_simp. rewrite* subst_texp_fresh_eq. }
      rewrite Heq2 in HC.
      assert (Heq2': [y ~=> x] (texp_app (texp_proj u l2) (texp_var_f y)) = (texp_app (texp_proj u l2) (texp_var_f x))).
      { default_simp. rewrite* subst_texp_fresh_eq. }
      rewrite Heq2' in HC.
      assert (Heq3: [y ~=> x] (close_texp_wrt_texp y tt) = (close_texp_wrt_texp y tt)). {
        apply subst_texp_fresh_eq...
        rewrite fv_texp_close_texp_wrt_texp. eauto.
      }
      rewrite Heq3 in HC. simpl in HC. now auto.
  - forwards* [?|?]: toplike_dec (typ_rcd l B1);
      forwards* [?|?]: toplike_dec (typ_rcd l B2).
    + destruct_conj. forwards*: split_toplike (typ_rcd l B).
    + remember (|| typ_rcd l B2 ||) as l2.
      forwards~ (?&?): IHHS texp_nil (texp_proj u l2).
      exists. applys~ M_RcdR. inverts~ t0.
      rewrite <- Heql2. applys H.
    + remember (|| typ_rcd l B1 ||) as l1.
      forwards~ (?&?): IHHS (texp_proj t l1) texp_nil.
      exists. applys~ M_RcdL. inverts~ t0.
      rewrite <- Heql1. applys H.
    + remember (|| typ_rcd l B1 ||) as l1.
      remember (|| typ_rcd l B2 ||) as l2.
      forwards~ (?&?): IHHS (texp_proj t l1) (texp_proj u l2).
      exists. applys~ M_Rcd.
      rewrite <- Heql1. rewrite <- Heql2. applys H.
Qed.

#[local] Hint Immediate cosub_lc_texp : core.
Lemma esub_is_term_erased_cosub_2 : forall A B t1,
    esub A B -> lc_texp t1 -> (exists t2, cosub t1 A B t2).
Proof with try fsetdec; elia.
  introv HE HC. gen t1.
  indTypSize (size_typ A + size_typ B).
  destruct* HE.
  + exists. applys* S_Bot. pick fresh a. eauto.
  + pick fresh y.
    forwards* (tt&HC1): IH HE1 (texp_var_f y)...
    remember (|| typ_arrow A1 A2 ||) as l1.
    forwards* (t2'&HC2): IH HE2 (texp_app (texp_proj t1 l1) tt)...
    rewrite <- (open_texp_wrt_texp_close_texp_wrt_texp t2' y) in HC2.
    clear HE1 HE2 SizeInd.
    exists.
    applys* S_Arrow ((fv_texp (texp_var_f y)) `union` (fv_texp tt) `union` (fv_texp t1) `union` (fv_texp t2')) (close_texp_wrt_texp y t2').
    intros x Frx. rewrite <- Heql1. exists. split.
    * forwards*: cosub_rename y x HC1...
      assert (Heq: [y ~=> x] (texp_var_f y) = texp_var_f x).
      { default_simp. }
      rewrite Heq in H1. applys H1.
    * forwards*: cosub_rename y x HC2...
      rewrite subst_texp_open_texp_wrt_texp in H1.
      assert (Heq: [y ~=> x] (texp_var_f y) = texp_var_f x).
      { default_simp. }
      rewrite Heq in H1.
      ** assert (Heq2: [y ~=> x] (texp_app (texp_proj t1 l1) tt) = (texp_app (texp_proj t1 l1) [y ~=> x] (tt))).
         { default_simp. rewrite* subst_texp_fresh_eq. }
         rewrite Heq2 in H1.
         assert (Heq3: [y ~=> x] (close_texp_wrt_texp y t2') = (close_texp_wrt_texp y t2')). {
           apply subst_texp_fresh_eq...
           rewrite fv_texp_close_texp_wrt_texp. eauto.
         }
         rewrite Heq3 in H1. auto.
      ** eauto.
  + forwards (?&?): IH HE  (texp_proj t1 (|| typ_rcd l A ||))...
    all: eauto.
  + forwards (?&?): IH HE t1...
    all: eauto.
  + forwards (?&?): IH HE t1...
    all: eauto.
  + forwards* (?&?): IH HE1 t1...
    forwards* (?&?): IH HE2 t1...
    forwards* (?&?): spl_sound_to_comerge x x0 H.
Qed.

Theorem esub_is_term_erased_cosub : forall A B,
    esub A B <-> (forall t1, lc_texp t1 -> exists t2, cosub t1 A B t2).
Proof.
  introv. split.
  - intros. pose proof esub_is_term_erased_cosub_2. eauto.
  - intros. pose proof esub_is_term_erased_cosub_1. eauto.
Qed.

(* topLike specification eqv *)
Definition toplikeSpec A := esub typ_top A.

Theorem ord_or_spl : forall A,
    ord A \/ exists B C, spl A B C.
Proof.
  introv. induction* A.
  - inverts* IHA2.
  - inverts* IHA.
Qed.

Theorem toplike_spl : forall A B C,
    toplike A -> spl A B C -> toplike B /\ toplike C.
Proof.
  intros. gen B C. induction* H; intros; try solve_by_invert.
  - inverts* H1.
  - inverts* H0. forwards*: IHtoplike H5.
  - inverts* H0. forwards*: IHtoplike H5.
Qed.


Theorem toplike_spl_2 : forall A B C,
    spl A B C -> toplike B -> toplike C -> toplike A.
Proof.
  introv HS HT1 HT2. induction* HS.
  all: inverts HT1; inverts* HT2.
Qed.

Theorem toplike_spec_sound_and_complete: forall A,
    toplike A <-> toplikeSpec A.
Proof with try solve_by_invert; eauto.
  unfold toplikeSpec; split; intros.
  - indTypSize (size_typ A).
    forwards* [?| (?&?&?) ]: ord_or_spl A.
    forwards~ (?&?): toplike_spl H0.
    applys ES_Split H0; applys~ IH; elia.
  - indTypSize (size_typ A).
    inverts* H.
    forwards: IH H1. elia. forwards: IH H2. elia.
    eauto using toplike_spl_2.
Qed.

Corollary super_top_toplike : forall A,
    esub typ_top A -> toplike A.
Proof.
  intros. apply toplike_spec_sound_and_complete.
  eauto.
Qed.

Lemma toplike_covariance : forall A B,
    toplike A -> esub A B -> toplike B.
Proof with eauto using toplike_spec_sound_and_complete.
  introv HT HS.
  induction* HS...
  all: inverts* HT.
  all:  applys toplike_spl_2...
Qed.

Definition disjointSpec A B :=
  forall C, esub A C -> esub B C -> toplike C.

(* split *)
Lemma split_ord_false : forall T T1 T2,
    spl T T1 T2 -> ord T -> False.
Proof.
  introv s o. gen T1 T2.
  induction o; intros; inverts* s.
Qed.

#[local] Hint Resolve split_ord_false : FalseHd.

Lemma disjoint_rcd: forall A B l,
    disjoint (typ_rcd l A) (typ_rcd l B) -> disjoint A B.
Proof.
  introv H.
  inverts* H; intuition eauto.
  all: inverts* H0.
Qed.

#[export] Hint Immediate disjoint_rcd : core.

Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    forwards* (eq1&eq2): IHs1; split; congruence.
Qed.

Ltac split_unify :=
  repeat match goal with
    | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
        (progress forwards (?&?): split_unique H1 H2;
         subst; clear H2)
    | [ H: spl (typ_and _ _) _ _ |- _ ] => inverts H
    | [ H: spl (typ_arrow _ _) _ _ |- _ ] => inverts H
    | [ H: spl (typ_rcd _ _) _ _ |- _ ] => inverts H
    end;
  auto.


Theorem disjoint_soundness: forall A B,
    disjoint A B -> disjointSpec A B.
Proof with (solve_false; auto).
  intros A B Dis C S1 S2.
  indTypSize (size_typ A + size_typ B + size_typ C).

  forwards [?|(?&?&?)]: ord_or_spl C.
  - inverts Dis;
      try solve [applys* toplike_covariance];
      try solve [inverts S1; inverts S2; solve_false; auto]...
    + inverts S1...
      forwards: IH H6 S2; elia...
      forwards: IH H6 S2; elia...
    + inverts S2...
      forwards: IH S1 H6; elia...
      forwards: IH S1 H6; elia...
    + inverts S1; inverts S2...
      apply TL_arr.
      forwards: IH H0 H7 H12; elia...
    + inverts S1; inverts S2...
      apply TL_rcd.
      forwards: IH H0 H6 H9; elia...
  -
    inverts S1; inverts S2...
    split_unify.
    applys toplike_spl_2 H; applys* IH Dis; elia.
Qed.

(* generalize S_top *)
Lemma toplike_super_any : forall A B,
    toplike A -> esub B A.
Proof.
  introv TL. indTypSize (size_typ A).
  forwards* [?| (?&?&?) ]: ord_or_spl A.
  forwards (?&?): toplike_spl TL H.
  forwards*: IH x; elia.
  forwards*: IH x0; elia.
Qed.

(* generalize S_andl *)
Lemma sub_l_andl : forall A B C, esub A C -> esub (typ_and A B) C.
Proof.
  introv s. induction* s.
Qed.

(* generalize S_andr *)
Lemma sub_l_andr : forall A B C, esub B C -> esub (typ_and A B) C.
Proof.
  introv s. induction* s.
Qed.

(* generalize S_arr *)
Lemma sub_fun : forall A B C D,
    esub B D -> esub C A ->
    esub (typ_arrow A B) (typ_arrow C D).
Proof with eauto using toplike_dec.
  introv s. forwards: toplike_dec D.
  induction* s...
  all: destruct* H.
Qed.

(* generalize S_rcd *)
Lemma sub_rcd : forall A B l,
    esub A B -> esub (typ_rcd l A) (typ_rcd l B).
Proof with eauto using toplike_dec.
  introv s. forwards: toplike_dec B.
  induction* s...
  all: destruct* H.
Qed.

#[export]
  Hint Immediate toplike_super_any : core.
#[export]
  Hint Resolve sub_l_andl sub_l_andr sub_fun sub_rcd: core.


Lemma sub_refl : forall A,
    esub A A.
Proof.
  introv. induction* A.
  - forwards* [?|?]: toplike_dec typ_bot.
Qed.


Lemma sub_bot : forall A,
    esub typ_bot A.
Proof with eauto using toplike_dec.
  introv. forwards: toplike_dec A.
  indTypSize (size_typ A).
  forwards* [?| (?&?&?) ]: ord_or_spl A.
  all: destruct* H.
  - forwards: IH x... elia.
    forwards: IH x0... elia.
Qed.

#[local] Hint Resolve sub_refl sub_bot : core.

Fixpoint term_eq_dec (l1 l2 : label) : {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality.
Defined.

Theorem disjoint_completeness: forall A B,
    disjointSpec A B -> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  - gen B.
    induction A;
      introv H; auto.
    all: induction B; auto.
    + (* arr arr *)
      forwards* [?|?]: toplike_dec A2.
      forwards* [?|?]: toplike_dec B2.
      applys* D_ArrArr. applys* IHA2.
      intros.
      forwards: H (typ_arrow (typ_and A1 B1) C).
      1-2: applys* sub_fun.
      inverts~ H2.
    + (* rcd rcd *)
      case_eq (term_eq_dec l l0); intros; auto; subst.
      apply D_rcdEq. apply IHA. introv s1 s2.
      assert (TL: toplike (typ_rcd l0 C) ). {
        apply~ H.
      }
      inverts~ TL.
Qed.


Lemma cosub_well_typed : forall E t1 A B t2 At,
    cosub t1 A B t2 -> target_typing E t1 At -> subTarget At |[A]| ->
    exists Bt', target_typing E t2 Bt' /\ subTarget Bt' |[B]| /\ subTarget |[B]| Bt'.
Proof with elia; try tassumption;
intuition eauto using target_typing_wf_1, target_typing_wf_2,
  target_typing_wf_typ, ST_refl, ST_trans, ST_toplike, ST_top, ST_rcd_2,
  cosub_not_toplike,
  translate_to_record_types, subTarget_rec_typ.

  introv HS HT ST. gen At t1 t2 E.
  indTypSize (size_typ A + size_typ B). inverts HS.
  - (* top *)
    forwards* EQ: ttyp_trans_ord_top B. rewrite* <- check_toplike_sound_complete.
    exists. split...
  - (* bot *)
    lets* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ...
    exists. splits. applys TTyping_RcdCons.
    5: applys ST_refl. 2: right.
    all: eauto.
    pick fresh y and apply TTyping_Fix.
    unfold open_texp_wrt_texp. simpl. applys TTyping_Var... split; applys~ ST_refl.
  - (* base *)
    rewrite ttyp_trans_base...
    lets (?&?&?&?): lookup_ST_sub (|| typ_base ||) ST. simpl. reflexivity.
    exists. splits.
    applys TTyping_RcdCons. 3: applys TTyping_RcdProj H0.
    4: econstructor...
    all: eauto...
  - (* arrow *)
    pick fresh y.
    lets* (? & HS1 & HS2): H1 y.

    lets (?&?&Eq): lookup_ST_sub (|| (typ_arrow A1 A2) ||) ST.
    (* lets* (?&?&?&?&?): flex_typing_property3 (|| (typ_arrow A1 A2) ||) HT. *)
    rewrite ttyp_trans_ord_ntop_arrow. 2: eauto. simpl. case_if...
    applys check_toplike_false_2. applys* cosub_not_toplike.

    forwards (?&?&?&?&?&?&?): ST_arrow_inv Eq. subst.

    lets (?&?&?): IH HS1 ((y, |[ B1 ]|) :: E)...
    { econstructor... }
    lets (?&?&?): IH HS2. elia.
    2: { (* applys flex_typing_property0... *)
      applys TTyping_App.
      rewrite_env ([ (y, |[ B1 ]|) ] ++ E).
      applys TTyping_RcdProj H2.
      applys target_weakening_simpl...
      tassumption.
      split...
    }
    auto...
    exists. splits. applys TTyping_RcdCons.
    4: econstructor...
    3: {
      pick fresh z and apply TTyping_Abs.
      forwards* : subst_var_typing H8.
      solve_notin.
    }
    3: eauto.
    2: right*.
    1: now eauto.
    rewrite ttyp_trans_ord_ntop_arrow...
    simpl. case_if*. {
      exfalso. applys H0. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    }
    now applys* ST_rcd_2.
  - (* rcd *)
    lets (?&?&Eq&?): lookup_ST_sub (|| typ_rcd l0 A0 ||) ST.
    simpl. case_if*.
    { forwards*: cosub_not_toplike H1.
      apply check_toplike_sound_complete in C. contradiction. }

    forwards* (?&?&?): IH H1 E...
    exists. splits.
    applys* TTyping_RcdCons...

    simpl. case_if*. {
      exfalso. applys H0. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    }
    now applys* ST_rcd_2.

    simpl. case_if*. {
      exfalso. applys H0. rewrite <- check_toplike_sound_complete in C.
      eauto using comerge_toplike_r.
    }
    now applys* ST_rcd_2.
  - (* and *)
    applys* IH H0 HT...
    applys* ST_trans ST_andl.
  - (* and *)
    applys* IH H0 HT... applys* ST_trans ST_andr.
  - (* comerge *)
    forwards* (?&?&Eq1&?): IH H0. elia.
    forwards* (?&?&Eq2&?): IH H1. elia.
    forwards(?&?&?): comerge_well_typed H2; try eassumption.
    exists. split*...
    Unshelve. all: econstructor.
Qed.

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

Lemma toplike_appdist_inv : forall A C T t1 t2 t3,
    distapp t1 A t2 T t3 C -> toplike A -> toplike C.
Proof.
  introv HA HT. inductions HA.
  all: inverts* HT.
Qed.

Lemma toplike_appdist_inv_2 : forall A C T t1 t2 t3,
    distapp t1 A t2 T t3 C -> toplike C -> toplike A.
Proof.
  introv HA HT. inductions HA.
  all: inverts* HT.
Qed.

Lemma distapp_well_typed_app : forall A B C G t1 t2 t3 A' B',
    distapp t1 A t2 B t3 C ->
    target_typing ||[ G ]|| t1 A' -> subTarget A' |[A]| ->
    target_typing ||[ G ]|| t2 B' -> subTarget B' |[B]| ->
    exists C', target_typing ||[ G ]|| t3 C' /\ subTarget C' |[C]| /\ subTarget |[C]| C'.
Proof with intuition eauto using target_typing_wf_1, target_typing_wf_2,
    target_typing_wf_typ, ST_refl, ST_trans, ST_toplike, ST_top, ST_rcd_2,
    cosub_not_toplike, ttyp_trans_wf,
    translate_to_record_types, subTarget_rec_typ.

  introv HA HTa HEa HTb HEb. gen A' B'.
  inductions HA; intros.
  - rewrite* ttyp_trans_ord_top.
  - forwards* (?&?&?): cosub_well_typed H1.
    lets (?&?&?&?): lookup_ST_sub (|| (typ_arrow A B) ||) HEa.
    simpl. case_if*.
    { apply check_toplike_sound_complete in C0. contradiction. }
    forwards(?&?&?&?&?&?&?): ST_arrow_inv H5. subst.
    exists. splits. applys TTyping_App.
    econstructor. 1-3: now eauto. all: try split...
  - forwards* (?&?&?&?): IHHA1 HTb. eauto using ST_refl, ST_trans, ST_andl.
    forwards* (?&?&?&?): IHHA2 HTb. eauto using ST_refl, ST_trans, ST_andr.
    forwards*: concat_source_intersection...
    forwards* (?&?&?&?): ST_concat H6 H1 H4...
    exists. split. applys* TTyping_RcdMerge H0 H3.
    all: eauto...
Qed.


Lemma distapp_well_typed_proj : forall A l t1 t3 C G A',
    proj t1 A l t3 C -> target_typing ||[ G ]|| t1 A' ->
    subTarget A' |[A]| ->
    exists C', target_typing ||[ G ]|| t3 C' /\ subTarget C' |[C]| /\ subTarget |[C]| C'.
Proof with intuition eauto using target_typing_wf_1, target_typing_wf_2,
    target_typing_wf_typ, ST_refl, ST_trans, ST_toplike, ST_top, ST_rcd_2,
    cosub_not_toplike,
    translate_to_record_types, subTarget_rec_typ.

  introv HA HT HS. gen A'.
  inductions HA; intros...
  - rewrite* ttyp_trans_ord_top.
  - lets (?&?&?): lookup_ST_sub (|| typ_rcd l A ||) HS.
    simpl. case_if*.
    { apply check_toplike_sound_complete in C. contradiction. }
    exists. split. applys* TTyping_RcdProj. now eauto.
  - rewrite* ttyp_trans_ord_top.
  - forwards* (?&?&?): IHHA1 HT; eauto using ST_refl, ST_trans, ST_andl.
    forwards* (?&?&?): IHHA2 HT; eauto using ST_refl, ST_trans, ST_andr.
    forwards*: concat_source_intersection...
    forwards* (?&?&?&?): ST_concat H4 H5 H1...
    exists. split. applys* TTyping_RcdMerge H0 H2.
    all: eauto...
Qed.

Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t ->
    exists A', target_typing ||[ G ]|| t A' /\  subTarget A' |[A]| /\  subTarget |[A]| A'.
Proof with intuition eauto using target_typing_wf_1, target_typing_wf_2,
    target_typing_wf_typ, ST_refl, ST_trans, ST_toplike, ST_top, ST_rcd_2,
    cosub_not_toplike, ctx_trans_preserves_uniq, ttyp_trans_wf,
    translate_to_record_types, subTarget_rec_typ,  elaboration_wf_ctx.
  introv HT.
  induction HT...
  - rewrite* ttyp_trans_ord_top.
    exists. splits. applys TTyping_RcdNil... all: eauto using ST_refl...
  - rewrite* ttyp_trans_ord_top.
    exists. split. applys TTyping_RcdNil... all: eauto using ST_refl...
    rewrite* <- check_toplike_sound_complete.
  - rewrite* ttyp_trans_ord_top. rewrite* <- check_toplike_sound_complete.
  - (* base *)
    rewrite* ttyp_trans_base.
    exists. split. applys TTyping_RcdCons.
    4: eauto...
    all: eauto...
  - (* var *)
    apply ctx_trans_preserves_binds in H0...
    exists. split*. econstructor...
  - (* fix *)
    pick fresh x. forwards~ (?&?&?): H0 x.
    exists. split. remember ||[ G ]||. pick fresh y and apply TTyping_Fix.
    applys subst_var_typing H1.
    all: eauto...
  - (* abs *)
    pick fresh x. forwards~ (?&?&?&?): H1 x.
    forwards: target_typing_wf_2 H2. inverts H5.
    forwards: target_typing_wf_1 H2. inverts H5.
    rewrite ttyp_trans_ord_ntop_arrow...
    exists. split. applys TTyping_RcdCons.
    4: eauto...
    3: { remember ||[ G ]||.
         pick fresh y and apply TTyping_Abs.
         applys subst_var_typing H2.
         all: eauto.
    }
    3: econstructor.
    all: eauto...
  - (* app *)
    destruct_conj. applys* distapp_well_typed_app...
  - (* rcd *)
    rewrite ttyp_trans_rcd.
    destruct_conj. exists. split. applys* TTyping_RcdCons.
    splits. all: eauto...
  - (* proj *)
    destruct_conj. applys* distapp_well_typed_proj.
  - (* merge *)
    destruct_conj.
    lets HC: concat_source_intersection A B...
    forwards* (?&?&?): ST_concat HC...
    exists. split.
    applys TTyping_RcdMerge H3 H0...
    split...
  - (* subsumption *)
    destruct_conj. forwards* (?&?&?&?): cosub_well_typed H.
    Unshelve. all: econstructor.
Qed.
