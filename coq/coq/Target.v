Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Infrastructure.


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
  - pick_fresh x. forwards*: H1 x...
  - pick_fresh x. forwards*: H0 x...
Qed.

Lemma target_typing_wf_2 : forall G t T,
   target_typing G t T -> wf_typ T.
Proof with eauto.
  intros Ga t T Htyp.
  induction Htyp...
  all: pick fresh x...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
  - applys* wf_rcd_concat At Bt Ct.
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

Lemma target_weakening : forall G E F t T,
    target_typing (E ++ G) t T ->
    uniq (E ++ F ++ G) ->
    target_typing (E ++ F ++ G) t T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply TTyping_Abs; eauto.
      rewrite_env (([(x, At)] ++ E) ++ F ++ G).
      apply~ H1.
      solve_uniq.
    + (* fix *)
      pick fresh x and apply TTyping_Fix.
      rewrite_env (([(x, At)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma target_weakening_simpl : forall E F e T,
    target_typing E e T ->
    uniq (F ++ E) ->
    target_typing (F ++ E) e T.
Proof.
  intros.
  rewrite_env ( [] ++  (F ++ E)).
  applys* target_weakening.
Qed.


Lemma target_weakening_empty : forall G t T,
    uniq G -> target_typing [] t T -> target_typing G t T.
Proof.
  introv Uni Typ.
  rewrite_env ([]++G++[]).
  applys* target_weakening.
Qed.



Lemma substitution_preserves_typing : forall (E F : tctx) t u S T (z : atom),
    target_typing (F ++ [(z,S)] ++ E) t T ->
    target_typing E u S ->
    target_typing (F ++ E) ([z ~>> u] t) T.
Proof with eauto.
  introv Typ1 Typ2.
  inductions Typ1.
  all: simpl...
  - (* var *)
    simpl. case_if; subst.
    + forwards* : binds_mid_eq H1.
      subst. applys* target_weakening_simpl.
    + forwards* : binds_remove_mid H1.
  - (* abs *)
    pick fresh x and apply TTyping_Abs...
    rewrite_env (((x, At) :: F) ++ E).
    rewrite subst_texp_open_texp_wrt_texp_var...
    applys* H1.
    eauto.
  - (* fixpoint *)
    pick fresh x and apply TTyping_Fix...
    rewrite_env (((x, At) :: F) ++ E).
    rewrite subst_texp_open_texp_wrt_texp_var...
    applys* H0.
    eauto.
Qed.


Theorem preservation : forall t t' T,
    target_typing [] t T ->
    t >-> t' ->
    target_typing [] t' T.
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
      destruct H10.
      * applys* TTyping_RcdCons...
        forwards*: lookup_concat_typ. left. rewrite* H2.
      * applys* TTyping_RcdCons...
        forwards*: lookup_concat_typ_none.
        destruct H14 as [Heq|Heq]; rewrite <- Heq; eauto.
Qed.
