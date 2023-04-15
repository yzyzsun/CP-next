Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Infrastructure.


(* Lookup *)

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

#[export] Hint Resolve lookup_wf_typ_3 wf_typ_look_up_wf : core.

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

Lemma lookup_wf_typ_1 : forall l T At l',
    Tlookup l' (ttyp_rcd l T At) = Tlookup l' At \/ l = l'.
Proof.
  introv. simpl. case_if*.
Qed.


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

Lemma Tlookup_dec : forall l A,
  (exists B, Tlookup l A = Some B) \/ Tlookup l A = None.
Proof.
  introv. remember (Tlookup l A). destruct* o.
Qed.

Ltac case_lookup l A := lets [(?&?)|?]: Tlookup_dec l A.

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
    | H1: Tlookup _ ?A = Some _ , H2: ?A = ttyp_top |- _ => rewrite H2 in H1; discriminate
    end.

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

Lemma lookup_ST_sub : forall A B l A',
    subTarget B A ->
    Tlookup l A = Some A' -> exists B', Tlookup l B = Some B' /\ subTarget B' A' /\ subTarget A' B'.
Proof.
  introv HSA HLA. gen l A'.
  induction* HSA; intros; unify_lookup; intuition eauto.
Qed.

Lemma lookup_ST_eq_some : forall A B l A',
    subTarget A B -> subTarget B A ->
    Tlookup l A = Some A' -> exists B', Tlookup l B = Some B' /\
                                          subTarget A' B' /\ subTarget B' A'.
Proof.
  intros. forwards* (?&?&?): lookup_ST_sub A B.
Qed.

Lemma lookup_eq : forall A B,
    subTarget A B -> subTarget B A -> forall l, Tlookup l A = None -> Tlookup l B = None.
Proof.
  introv HS HR.
  induction* HS.
  - introv HL. remember (Tlookup l At). destruct* o.
    forwards* (?&?&?): H1 l. rewrite HL in H2. discriminate.
Qed.

Ltac lookup_eq l HE :=
  match type of HE with
  | subTarget ?A ?B => let Heq1 := fresh "Heq1" in
                       let Heq2 := fresh "Heq2" in
                            match goal with
                            | H: Tlookup l A = Some _ |- _ =>
                                forwards (?&?&Heq1&Heq2): lookup_ST_eq_some HE H
                            | H: Tlookup l A = None |- _ =>
                                forwards: lookup_ST_eq_some HE H
                            end
  end.

(* Width Subtyping *)
Lemma ST_trans: forall A B C, subTarget A B -> subTarget B C -> subTarget A C.
Proof with try simpl in *; discriminate.
  introv HA HB.
  indTypSize (size_ttyp A + size_ttyp B + size_ttyp C).
  destruct* HA; inverts* HB; try solve [inverts H]; try solve [inverts H0].
  - econstructor; eauto. all: applys* IH; elia.
  - applys~ ST_rcd. intros.
    forwards~ (?&?&?&?): H4 H5. forwards~ (?&?&?&?): H1 H6.
    exists x0. splits*.  all: applys* IH; elia.
Qed.

Lemma ST_arrow_inv : forall x A B,
    subTarget x (ttyp_arrow A B) -> exists C D, x = ttyp_arrow C D /\
                                                  subTarget A C /\ subTarget C A /\
                                                  subTarget B D /\ subTarget D B.
Proof.
  introv HS. inverts* HS. inverts H.
Qed.

Lemma subTarget_rec_typ : forall A B,
    subTarget A B -> rec_typ A -> rec_typ B.
Proof.
  introv HS HR. induction~ HS. inverts HR.
Qed.

Lemma ST_rcd_inv : forall A B,
    subTarget A B -> rec_typ A ->
    forall l Ct, Tlookup l B = Some Ct ->
                 exists Ct', Tlookup l A = Some Ct' /\ subTarget Ct' Ct /\ subTarget Ct Ct'.
Proof.
  introv HS HA. forwards* HB: subTarget_rec_typ HA. inverts* HS.
  - introv HL. forwards*: H1 HL.
Qed.

Lemma ST_rcd_2 : forall A B C D l, subTarget A B -> subTarget B A -> subTarget C D -> subTarget D C
                                 -> rec_typ C -> rec_typ D
                                 -> subTarget (ttyp_rcd l A C) (ttyp_rcd l B D).
Proof with unify_lookup; intuition eauto.
  introv HSa HSb HSc HSd HRc HRd. applys* ST_rcd.
  introv HL. simpl. case_if*.
  - subst*. exists. split*. simpl in HL. case_if.
    inverts* HL.
  - simpl in HL. case_if. forwards*: ST_rcd_inv HSc.
Qed.

Lemma ST_top_inv : forall A, subTarget ttyp_top A -> A = ttyp_top.
Proof.
  introv HS. inverts* HS.
  destruct* H.
  forwards* (?&?&?): H1 l.
  simpl in H2. discriminate.
Qed.

Lemma ST_refl : forall A, subTarget A A.
Proof.
  introv. induction* A.
Qed.


Lemma ST_top_2: forall A, rec_typ A -> subTarget A ttyp_top.
Proof with simpl in *; discriminate.
  introv HR. applys* ST_rcd.
  intros...
Qed.

Lemma split_toplike_l : forall A1 A2 B,
    spl B A1 A2 -> toplike B -> toplike A1.
Proof.
  introv HC HT. induction* HC; inverts~ HT.
Qed.


Lemma split_toplike_r : forall A1 A2 B,
    spl B A1 A2 -> toplike B -> toplike A2.
Proof.
  introv HC HT. induction* HC; inverts~ HT.
Qed.

Lemma lookup_concat_both : forall At Bt Ct A B l,
    concat_typ At Bt Ct -> Tlookup l At = Some A -> Tlookup l Bt = Some B -> subTarget A B /\ subTarget B A.
Proof.
  introv HC HLa HLb. gen Bt A B Ct.
  induction At; intros; simpl in HC; try solve [inverts HLa].
  - simpl in HLa. case_if.
    + subst*. inverts HLa. inverts HC. intuition eauto; unify_lookup; eauto.
    + inverts HC. forwards*: IHAt2.
Qed.

Lemma concat_typ_exists : forall A B,
    rec_typ A -> rec_typ B -> wf_typ A -> wf_typ B ->
    (forall l A' B', Tlookup l A = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A') ->
    concat_typ A B (ttyp_concat_simpl A B).
Proof with intuition eauto using ST_trans.
  introv HRa HRb. gen B.
  induction HRa; intros; try solve [simpl; intuition eauto].
  simpl. case_lookup l B.
  + forwards(?&?): H1 l H2. simpl. case_if*.
    assert ((forall (l : String.string) (A' B' : ttyp),
                Tlookup l Bt = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A')). {
      intros. case_eq (string_eq_dec l l0); intros; subst.
      - forwards: H1 l0. simpl. case_if*. eauto. inverts H. destruct H15; unify_lookup...
      - forwards: H1 l0. simpl. case_if*. eauto. eauto.
    }
    econstructor... applys IHHRa...
    inverts~ H.
   + assert ((forall (l : String.string) (A' B' : ttyp),
                Tlookup l Bt = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A')). {
      intros. case_eq (string_eq_dec l l0); intros; subst.
      - forwards: H1 l0. simpl. case_if*. eauto. inverts H. destruct H13; unify_lookup...
      - forwards: H1 l0. simpl. case_if*. eauto. eauto.
     }
     econstructor... applys IHHRa...
     inverts~ H.
     Unshelve. all: eauto.
Qed.

Lemma ST_concat : forall At Bt Ct At' Bt',
    concat_typ At Bt Ct -> subTarget At At' -> subTarget At' At -> subTarget Bt Bt' -> subTarget Bt' Bt ->
    wf_typ At' -> wf_typ Bt' ->
    exists Ct', concat_typ At' Bt' Ct' /\ subTarget Ct Ct' /\ subTarget Ct' Ct.
Proof with eauto using ST_trans, subTarget_rec_typ, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv HC HSa HSa' HSb HSb' Wa Wb.
  forwards HRa: rcd_typ_concat_1 HC. forwards HRb: rcd_typ_concat_2 HC.
  forwards: concat_typ_exists At' Bt'...
  - intros. forwards (?&?&?): ST_rcd_inv HSa... forwards (?&?&?): ST_rcd_inv HSa'...
    forwards (?&?&?): ST_rcd_inv HSb... forwards (?&?&?): ST_rcd_inv HSb'... unify_lookup.
    forwards (?&?): lookup_concat_both l HC... split...
  - exists. splits*.
    { applys ST_rcd... introv HL.
    case_lookup l At'.
    + forwards*: lookup_concat_typ H. rewrite H1 in HL. rewrite H0 in HL. inverts HL.
    forwards (?&?&?): ST_rcd_inv HSa...
    forwards*: lookup_concat_typ HC. rewrite H2 in H4.
    exists. split*.
    + forwards*: lookup_concat_typ_none H. rewrite H1 in HL.
    forwards (?&?&?): ST_rcd_inv HSb...
    case_lookup l At.
    * forwards*: lookup_concat_both HC.
      forwards*: lookup_concat_typ HC. rewrite H4 in H6.
      exists. split. eauto. intuition eauto...
    * forwards*: lookup_concat_typ_none HC. rewrite H2 in H5.
      exists. split*... }
        { applys ST_rcd... introv HL.
    case_lookup l At.
    + forwards*: lookup_concat_typ HC. rewrite H1 in HL. rewrite H0 in HL. inverts HL.
    forwards (?&?&?): ST_rcd_inv HSa'...
    forwards*: lookup_concat_typ H. rewrite H2 in H4.
    exists. split*.
    + forwards*: lookup_concat_typ_none HC. rewrite H1 in HL.
    forwards (?&?&?): ST_rcd_inv HSb'...
    case_lookup l At'.
    * forwards*: lookup_concat_both H.
      forwards*: lookup_concat_typ H. rewrite H4 in H6.
      exists. split. eauto. intuition eauto...
    * forwards*: lookup_concat_typ_none H. rewrite H2 in H5.
      exists. split*... }
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


Lemma target_typing_wf_typ : forall G t T,
    target_typing G t T -> wf_typ T.
Proof with eauto using target_typing_wf_2, target_context_binds_wf.
  intros Ga t T Htyp.
  induction* Htyp.
  - applys target_context_binds_wf; tassumption.
  - instantiate_cofinites...
  - instantiate_cofinites...
  - inverts* IHHtyp1.
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



Lemma substitution_preserves_typing_relax : forall E F t u S S' T z,
    target_typing (F ++ [(z,S)] ++ E) t T ->
    target_typing E u S' -> subTarget S S' -> subTarget S' S ->
    exists T', subTarget T T' /\ subTarget T' T /\ target_typing (F ++ E) ([z ~>> u] t) T'.
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
    + forwards* (?&?&?&Heq): lookup_ST_sub Bt x0.
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
