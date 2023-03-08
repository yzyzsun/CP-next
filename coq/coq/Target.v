Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Infrastructure.


Lemma eqIndTypTarget_refl : forall T,
    eqIndTypTarget T T.
Proof.
Admitted.

#[local] Hint Resolve eqIndTypTarget_refl : core.

Lemma wf_rcd_lookup : forall i T Ti,
  wf_typ T ->
  Tlookup i T = Some Ti ->
  wf_typ Ti.
Proof.
  introv WF LK.
  gen i Ti.
  induction WF; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H3.
Qed.

Lemma rcd_typ_concat : forall T1 T2 T3,
    rec_typ T1 -> rec_typ T2 ->
    concat_typ T1 T2 T3 ->
    rec_typ T3.
Proof.
  introv WF1 WF2 CT.
  induction* CT.
  - inverts* WF1.
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


Lemma wf_rcd_concat : forall T1 T2 T3,
    wf_typ T1 -> wf_typ T2 ->
    rec_typ T1 -> rec_typ T2 ->
    concat_typ T1 T2 T3 ->
    wf_typ T3.
Proof with eauto using rcd_typ_concat.
  introv WF1 WF2 RT1 RT2 CT.
  induction* CT.
  - inverts* WF1. inverts* RT1...
    destruct H6.
    + forwards* Heq: lookup_concat_typ H0 CT.
      rewrite H0 in Heq...
    + forwards* Heq: lookup_concat_typ_none H0 CT.
      destruct H as [H' | H']; rewrite H' in Heq...
Qed.


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

Lemma wf_typ_look_up_wf : forall l At Bt,
    Tlookup l At = Some Bt -> wf_typ At -> wf_typ Bt.
Proof with eauto.
  introv Heq WF. gen l Bt.
  induction WF; intros; try solve_by_invert.
  inverts Heq. case_if*.
  - inverts* H3.
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
  - eauto using wf_typ_look_up_wf.
  - applys* wf_rcd_concat H1.
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
      pick fresh x and apply TTyping_Fix.
      rewrite_env (([(x, At)] ++ E) ++ F ++ G).
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
    rewrite_env (((x, At) :: F) ++ E).
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


Lemma substitution_preserves_typing_relax : forall E F t u S S' T z,
    target_typing (F ++ [(z,S)] ++ E) t T ->
    target_typing E u S' -> eqIndTypTarget S S' ->
    exists T', eqIndTypTarget T T' /\ target_typing (F ++ E) ([z ~>> u] t) T'.
Proof with eauto using context_wf_inv_1, context_wf_inv_2.
  introv Typ1 Typ2 Eq.
  lets T1: Typ1. inductions T1.
  all: assert (wf_ctx (F ++ E)) by
    ( lets HW: target_typing_wf_2 Typ1;
      lets W1: context_wf_inv_1 HW; lets W2: context_wf_inv_2 HW;
      lets W3: context_wf_inv_2 W2; applys* context_wf_compose ).
  all: simpl...
  - (* var *)
    simpl. case_if; subst.
    + forwards* : binds_mid_eq H1.
      subst. exists S'. split*. applys* target_weakening_simpl...
    + forwards* : binds_remove_mid H1.
  - (* abs *)
    pick fresh x. instantiate_cofinites...
    rewrite_env (((x, At) :: F) ++ [(z, S)] ++ E) in H...
    forwards* (T' & ? & HT): H0 H.
    exists (ttyp_arrow At T'). split*.
    pick fresh y and apply TTyping_Abs.
    rewrite_env ((x, At) :: F ++ E) in HT.
    rewrite <- subst_texp_open_texp_wrt_texp_var in HT...
    forwards* : subst_var_typing HT.
    applys* subst_texp_fresh_mutual; solve_notin.
    applys notin_union_3. solve_notin.
    applys* subst_texp_fresh_mutual; solve_notin.
  - Abort.

  - (* fixpoint *)
    pick fresh x and apply TTyping_Fix...
    rewrite_env (((x, At) :: F) ++ E).
    rewrite subst_texp_open_texp_wrt_texp_var...
    applys* H0.
    eauto.


    exists. split.
    eapply (Typ_abs (union L (singleton z))); eauto.
    intros.
    forwards~(?&?&?): H0 x.
    rewrite_env (([(x, A)] ++ F) ++ [(z, S)] ++ E).
    reflexivity.
    (* lc_e_abs_exists *)
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply subsub2sub in H3.
    forwards*: Typing_chk_sub H2 H3.
    auto.
Qed.


Theorem preservation : forall t t' T,
    target_typing [] t T ->
    t >-> t' ->
    exists T', eqIndTypTarget T T' /\ target_typing [] t' T'.
Proof with eauto using rcd_typ_concat.
  introv Typ Red. gen t'.
  inductions Typ; intros;
    try solve [inverts* Red].
  - inverts Red.
    pick fresh x. forwards*: H x.
    rewrite* (subst_texp_intro x).
    assert (Heq: [] = @app (atom * ttyp) [] []) by eauto.
    rewrite Heq.
    applys* substitution_preserves_typing.
  - (* app *)
    inverts* Red.
    + inverts* Typ1.
      pick fresh x. forwards*: H6 x.
      rewrite* (subst_texp_intro x).
      assert (Heq: [] = @app (atom * ttyp) [] []) by eauto.
      rewrite Heq.
      applys* substitution_preserves_typing.
  - (* proj *)
    inverts* Red.
    forwards* (?&?&?): lookup_field_in_value H.
    assert (x=t'). {
      rewrite H0 in H4. inverts~ H4.
    }
    subst~.
  - (* cons *)
    inverts* Red.
    + inverts Typ1. inverts~ H1.
    + inverts Typ1. inverts~ H1.
      destruct H9.
      * applys* TTyping_RcdCons...
        forwards*: lookup_concat_typ. left. rewrite* H2.
      * applys* TTyping_RcdCons...
        forwards*: lookup_concat_typ_none.
        rewrite H2.
        destruct H15 as [Heq|Heq]; rewrite Heq; eauto.
Qed.
