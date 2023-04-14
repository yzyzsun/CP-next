Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Infrastructure.
Require Import Translation.


(* Standard properties of typing *)

Lemma target_typing_wf_1 : forall E t A,
    target_typing E t A -> uniq E.
Proof with eauto; destruct_uniq; solve_uniq.
  introv H.
  induction* H.
  - pick_fresh x. forwards*: H0 x...
  - pick_fresh x. forwards*: H0 x...
Qed.


Lemma context_wf_inv_1 : forall E G,
    wf_ctx (E ++ G) -> wf_ctx E.
Proof.
  introv HW. gen G. induction* E; intros.
  - simpl in HW. inverts* HW.
Qed.

Lemma context_wf_inv_2 : forall E G,
    wf_ctx (E ++ G) -> wf_ctx G.
Proof.
  introv HW. gen G. induction* E; intros.
  - simpl in HW. inverts* HW.
Qed.

Lemma context_wf_compose : forall E F,
    wf_ctx E -> wf_ctx F -> wf_ctx (E ++ F).
Proof with eauto using context_wf_inv_1, context_wf_inv_2.
  introv HW1 HW2.
  gen F. induction E; intros; simpl...
  inverts* HW1.
Qed.

Lemma target_typing_wf_2 : forall E t A,
    target_typing E t A -> wf_ctx E.
Proof with eauto using context_wf_inv_1, context_wf_inv_2.
  introv H.
  induction* H.
  all: instantiate_cofinites...
  all: inverts* H0.
Qed.

Lemma target_context_binds_wf : forall x At Gt,
    binds x At Gt -> wf_ctx Gt -> wf_typ At.
Proof.
  introv HB HW.
  induction Gt.
  - exfalso. applys* binds_nil_iff.
  - inverts* HB; inverts* HW.
    Unshelve. applys ttyp.
    all: eauto.
Qed.


Lemma target_typing_wf_typ : forall G t T,
    target_typing G t T -> wf_typ T.
Proof with eauto using target_typing_wf_2, target_context_binds_wf.
  intros Ga t T Htyp.
  induction* Htyp.
  - applys target_context_binds_wf; tassumption.
  - instantiate_cofinites...
  - instantiate_cofinites...
  - inverts* IHHtyp1.
  - intuition eauto using wf_typ_look_up_wf.
  - applys* wf_rcd_concat H.
Qed.

Lemma target_typing_lc_texp : forall G t T,
    target_typing G t T -> lc_texp t.
Proof with eauto.
  intros Ga t T Htyp.
  induction Htyp...
  all: pick fresh x...
Qed.

#[local] Hint Immediate target_typing_lc_texp : core.


Lemma lookup_field_in_value : forall v T i Ti,
    value v ->
    target_typing [] v T ->
    Tlookup i T = Some Ti ->
    exists ti, tlookup i v = Some ti /\ target_typing [] ti Ti.
Proof with try solve_by_invert.
  introv Val Typ LK.
  induction Typ; try solve_by_invert.
  - simpl in LK. simpl.
    case_if; inverts LK; subst*.
    + forwards~ : IHTyp2.
      inverts~ Val.
Qed.


Theorem progress : forall t T,
    target_typing [] t T ->
    value t \/ exists t', t >-> t'.
Proof with try solve_by_invert.
  introv Typ.
  inductions Typ...
  all: try solve [left*].
  all: try solve [right*].
  - (* abs *)
    left. eauto using target_typing_lc_texp.
  - (* fixpoint *)
    right. exists*. eauto using target_typing_lc_texp.
  - (* application *)
    forwards~ [?|(?&?)]: IHTyp1.
    2: { right; exists*. }
    forwards~ [?|(?&?)]: IHTyp2.
    2: { right; exists; eauto using target_typing_lc_texp. }
    inverts Typ1...
    { right; exists; eauto using target_typing_lc_texp. }
  - (* cons *)
    forwards~ [?|(?&?)]: IHTyp1; forwards~ [?|(?&?)]: IHTyp2.
    all: right; exists; eauto using target_typing_lc_texp.
  - (* proj *)
    forwards~ [?|(?&?)]: IHTyp.
    2: right; exists; eauto using target_typing_lc_texp.
    + forwards* (?&?&?): lookup_field_in_value Typ.
  - (* concat *)
    forwards~ [?|(?&?)]: IHTyp1; forwards~ [?|(?&?)]: IHTyp2.
    2-4: right; exists; eauto using target_typing_lc_texp.
    inverts Typ1...
    2: inverts H2.
    all: right; exists; eauto using target_typing_lc_texp.
Qed.

Lemma context_wf_compose_middle : forall E F G,
    wf_ctx (E ++ G) -> wf_ctx F -> wf_ctx (E ++ F ++ G).
Proof.
  introv WF1 WF2.
  lets: context_wf_inv_1 WF1.
  lets: context_wf_inv_2 WF1.
  eauto using context_wf_compose.
Qed.

Lemma target_weakening : forall G E F t T,
    target_typing (E ++ G) t T ->
    wf_ctx F ->
    uniq (E ++ F ++ G) ->
    target_typing (E ++ F ++ G) t T.
Proof with eauto using context_wf_compose_middle.
  introv Typ WF HU; gen F;
    inductions Typ; intros; autos...
    + (* abs *)
      pick fresh x and apply TTyping_Abs; eauto.
      rewrite_env (([(x, At)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* fix *)
      pick fresh x and apply TTyping_Fix...
      rewrite_env (([(x, Bt)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma target_weakening_simpl : forall E F e T,
    target_typing E e T ->
    uniq (F ++ E) -> wf_ctx F ->
    target_typing (F ++ E) e T.
Proof.
  intros.
  rewrite_env ( [] ++  (F ++ E)).
  applys* target_weakening.
Qed.

Lemma target_weakening_empty : forall G t T,
    uniq G -> wf_ctx G -> target_typing [] t T -> target_typing G t T.
Proof.
  introv Uni Wf Typ.
  rewrite_env ([]++G++[]).
  applys* target_weakening.
Qed.


Lemma substitution_preserves_typing : forall (E F : tctx) t u S T (z : atom),
    target_typing (F ++ [(z,S)] ++ E) t T ->
    target_typing E u S ->
    target_typing (F ++ E) ([z ~>> u] t) T.
Proof with eauto using context_wf_inv_1, context_wf_inv_2.
  introv Typ1 Typ2.
  lets T1: Typ1. inductions T1.
  all: assert (wf_ctx (F ++ E)) by
    ( lets HW: target_typing_wf_2 Typ1;
      lets W1: context_wf_inv_1 HW; lets W2: context_wf_inv_2 HW;
      lets W3: context_wf_inv_2 W2; applys* context_wf_compose ).
  all: simpl...
  - (* var *)
    simpl. case_if; subst.
    + forwards* : binds_mid_eq H1.
      subst. applys* target_weakening_simpl...
    + forwards* : binds_remove_mid H1...
  - (* abs *)
    pick fresh x and apply TTyping_Abs...
    rewrite subst_texp_open_texp_wrt_texp_var...
    forwards*: H0 x.
    rewrite_env (((x, At) :: F) ++ [(z, S)] ++ E)...
    rewrite_env (((x, At) :: F) ++ [(z, S)] ++ E)...
    eauto.
  - (* fixpoint *)
    pick fresh x and apply TTyping_Fix...
    rewrite_env (((x, Bt) :: F) ++ E).
    rewrite subst_texp_open_texp_wrt_texp_var...
Qed.


Lemma subst_var_typing : forall x A G t B y,
    target_typing ((x, A) :: G) (open_texp_wrt_texp t (texp_var_f x)) B ->
    x `notin` fv_texp t -> y `notin` (dom G `union` fv_texp t) ->
    target_typing ((y, A) :: G) (open_texp_wrt_texp t (texp_var_f y)) B.
Proof.
  introv HT HNx HNy.
  destruct (x == y); subst*.
  forwards HU: target_typing_wf_1 HT.
  rewrite (@subst_texp_intro x); eauto.
  rewrite_env ( [] ++ ( (y, A) :: G) ).
  applys* substitution_preserves_typing A.
  - rewrite_env ( [(x, A)] ++ [(y, A)] ++ G ).
    applys* target_weakening.
    + constructor*. lets HW: target_typing_wf_2 HT. applys* target_context_binds_wf HW.
    + destruct_uniq. solve_uniq.
  - constructor*; inverts* HU.
    lets HW: target_typing_wf_2 HT. inverts* HW.
Qed.

#[local] Hint Resolve ST_top ST_andl ST_andr : core.


Lemma substitution_preserves_typing_relax : forall E F t u S S' T z,
    target_typing (F ++ [(z,S)] ++ E) t T ->
    target_typing E u S' -> subTarget S S' -> subTarget S' S ->
    exists T', subTarget T T' /\ subTarget T' T /\target_typing (F ++ E) ([z ~>> u] t) T'.
Proof with eauto using target_context_binds_wf, context_wf_inv_1, context_wf_inv_2, subTarget_rec_typ.
  introv Typ1 Typ2 Eq1 Eq2.
  lets T1: Typ1. inductions T1.
  all: assert (wf_ctx (F ++ E)) by
    ( lets HW: target_typing_wf_2 Typ1;
      lets W1: context_wf_inv_1 HW; lets W2: context_wf_inv_2 HW;
      lets W3: context_wf_inv_2 W2; applys* context_wf_compose ).
  all: simpl...
  - (* var *)
    simpl. case_if; subst.
    + forwards* : binds_mid_eq H1.
      subst. exists S'. splits*. applys* target_weakening_simpl...
    + forwards* : binds_remove_mid H1.
  - (* abs *)
    pick fresh x. instantiate_cofinites...
    rewrite_env (((x, At) :: F) ++ [(z, S)] ++ E) in H...
    forwards* (T' & ? & HT): H0 H.
    forwards WFC: target_typing_wf_2 HT. inverts WFC.
    exists (ttyp_arrow At T'). splits*...
    pick fresh y and apply TTyping_Abs.
    rewrite_env ((x, At) :: F ++ E) in HT.
    rewrite <- subst_texp_open_texp_wrt_texp_var in HT...
    forwards* : subst_var_typing HT.
    applys* subst_texp_fresh_mutual; solve_notin.
    applys notin_union_3. solve_notin.
    applys* subst_texp_fresh_mutual; solve_notin.
  - (* fixpoint *)
    pick fresh x. instantiate_cofinites...
    rewrite_env (((x, Bt) :: F) ++ [(z, S)] ++ E) in H...
    forwards* (T' & ? & HT): H0 H.
    exists T'. splits*.
    pick fresh y and apply TTyping_Fix.
    rewrite_env ((x, Bt) :: F ++ E) in HT.
    rewrite <- subst_texp_open_texp_wrt_texp_var in HT...
    forwards* : subst_var_typing HT.
    applys* subst_texp_fresh_mutual; solve_notin.
    applys notin_union_3. solve_notin.
    applys* subst_texp_fresh_mutual; solve_notin. intuition eauto.
    all: eauto using ST_trans.
  - (* app *)
    forwards* (? & ? & He & HT1): IHT1_1. forwards* (? & ? & ? & HT2): IHT1_2.
    forwards* (?&?&?&?&?&?&?): ST_arrow_inv He. subst*.
    exists. splits; try eassumption.
    applys* TTyping_App HT1 HT2. split; intuition eauto using ST_trans.
  - (* cons *)
    forwards* (? & ? & He & HT1): IHT1_1. forwards* (? & ? & ? & HT2): IHT1_2.
    destruct* H0.
    + forwards* (?&?&?&Heq): lookup_ST_eq_some Bt x0.
      exists. splits. 3: econstructor; try apply HT1; try apply HT2...
      1,2: applys~ ST_rcd_2...
      left. splits... 1-2: intuition eauto using ST_trans.
    + forwards* Heq: lookup_eq Bt.
      exists. splits.  3: econstructor; try apply HT1; try apply HT2...
      1,2: applys~ ST_rcd_2...
  - (* proj *)
    forwards* (? & He & ? & HT1): IHT1.
    forwards* (?&?&?&Heq): lookup_ST_eq_some He.
  - (* merge *)
    forwards* (? & He & ? & HT1): IHT1_1. forwards* (? & ? & ? & HT2): IHT1_2.
    forwards* (T & HC & ? & ?): ST_concat H1. 1-2: eauto using target_typing_wf_typ.
    exists T. splits*.
    applys* TTyping_RcdMerge HT1 HT2...
    Unshelve. all: eauto.
Qed.


Theorem preservation : forall t' t T,
    target_typing [] t T ->
    t >-> t' ->
    exists T', subTarget T T' /\ subTarget T' T /\ target_typing [] t' T'.
Proof with intuition eauto using target_context_binds_wf, context_wf_inv_1, context_wf_inv_2, subTarget_rec_typ,
    rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3, target_typing_wf_typ.
  introv Typ Red. gen t'.
  inductions Typ; intros;
    try solve [inverts* Red].
  - inverts Red.
    pick fresh x. forwards*: H x.
    rewrite* (subst_texp_intro x).
    assert (Heq: [] = @app (atom * ttyp) [] []) by eauto.
    rewrite Heq.
    applys* substitution_preserves_typing_relax.
  - (* app *)
    inverts* Red.
    + forwards* (?&?&?&?): IHTyp1;
      forwards* (?&?&?&?&?&?&?): ST_arrow_inv; try tassumption; subst; exists; eauto.
      splits; eauto using ST_trans.
      econstructor; try tassumption. splits; intuition eauto using ST_trans.
    + forwards* (?&?&?&?): IHTyp2.
      exists. splits. 3: econstructor... all: eauto using ST_refl, ST_trans.
    + inverts* Typ1; try solve_by_invert.
      pick fresh x. forwards*: H5 x.
      rewrite* (subst_texp_intro x).
      assert (Heq: [] = @app (atom * ttyp) [] []) by eauto.
      rewrite Heq.
      applys* substitution_preserves_typing_relax.
  - (* cons *)
    inverts* Red.
    + forwards* (?&?&?): IHTyp1. destruct H0 as [(?&?)|?].
      *
        exists. splits.
        3: applys* TTyping_RcdCons H2 Typ2.
        1-2: applys ST_rcd_2.
        all: intuition eauto using ST_refl, ST_trans.
      *
        exists. splits.
        3: applys* TTyping_RcdCons H2 Typ2.
        all: intuition eauto using ST_rcd_2, ST_refl, ST_trans.
    + forwards* (?&?&?&?): IHTyp2. destruct H0 as [(?&?)|?].
      * forwards* (?&?&?&?): lookup_ST_eq_some l H0.
        exists. splits.
        3: applys* TTyping_RcdCons Typ1 H3. 4: left; splits*.
        1-2: applys ST_rcd_2.
        4,7,9: auto... all: intuition eauto using ST_rcd_2, ST_refl, ST_trans.
        all: auto...
      * forwards* Heq: lookup_eq l H0.
        exists. splits.
        3: applys* TTyping_RcdCons Typ1 H3...
        all: applys ST_rcd_2; intuition eauto using ST_rcd_2, ST_refl, ST_trans...
  - (* proj *)
    inverts* Red.
    + forwards* (?&?&?): IHTyp.
      forwards* (?&?&?): lookup_ST_eq_some l H0.
    + exists; eauto.
      forwards* (?&?&?): lookup_field_in_value H.
      assert (x=t'). {
        rewrite H0 in H4. inverts~ H4.
      } subst~.
  - (* merge *)
    inverts* Red.
    + forwards* (?&?&?): IHTyp1.
      forwards (T'&?&?): ST_concat H1; try tassumption; eauto...
      forwards* (?&?&?&?): H7.
      exists* T'. splits. 3: applys* TTyping_RcdMerge Typ2 H5.
      all: intuition eauto using ST_rcd_2, ST_refl, ST_trans...
    + forwards* (?&?&?): IHTyp2.
      forwards (T'&?&?): ST_concat H1; try tassumption; eauto...
      exists* T'. splits. 3: applys* TTyping_RcdMerge Typ1 H5.
      all: intuition eauto using ST_rcd_2, ST_refl, ST_trans...
    + inverts Typ1. inverts* H1...
    + inverts Typ1. inverts~ H1.
      destruct H10 as [(?&?)|?].
      * forwards* Heq: lookup_concat_typ H15. rewrite H1 in Heq.
        exists. splits.
        3: { econstructor. 3: eassumption.
             3: econstructor. 5-7: eassumption.
             2: left; rewrite* Heq...
             all: eauto...
        }
        all: intuition eauto using ST_rcd_2, ST_refl, ST_trans...
      * forwards* LKC: lookup_concat_typ_none.
        destruct H14 as [(Heq&?)|Heq]; rewrite Heq in LKC.
        ** exists. splits.
           3: { econstructor. 3: eassumption.
             3: econstructor. 5-7: eassumption.
             2: left; rewrite* LKC...
             all: eauto...
           }
        all: intuition eauto using ST_rcd_2, ST_refl, ST_trans...
        ** exists. splits.
           3: { econstructor. 3: eassumption.
             3: econstructor. 5-7: eassumption.
             2: right; rewrite* LKC...
             all: eauto...
           }
        all: intuition eauto using ST_rcd_2, ST_refl, ST_trans...
    Unshelve. all: eauto.
Qed.
