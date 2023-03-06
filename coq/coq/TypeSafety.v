Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.
(* Require Export Source3. *)


Reserved Notation "|[ A ]|" (at level 5, A at next level).

Fixpoint styp2ttyp (A: typ) : ttyp := ttyp_base
where "|[ A ]|" := (styp2ttyp A).

Notation "|| A ||" := (type2index A) (at level 1, A at next level). (* too high *)

(* Properties of translation (to type index) functions *)
Lemma tindex_trans_arrow : forall A B,
    || (typ_arrow A B) || = ti_arrow || B ||.
Admitted.
Lemma tindex_trans_rcd : forall l A,
    || (typ_rcd l A) || = ti_rcd l || A ||.
Admitted.

(* Properties of translation (to target type) functions *)

Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Admitted.

(* Typ-TopAbs requires no ord *)
Lemma ttyp_trans_ord_top : forall A,
    toplike A -> |[A]| = ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> ~ toplike A -> exists B, |[A]| = ttyp_rcd ||A|| B ttyp_top /\ wf_typ B.
Admitted.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd ||typ_base|| ttyp_base ttyp_top.
Admitted.

Lemma ttyp_trans_ord_ntop_arrow : forall A A',
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_arrow A' A)]| = ttyp_rcd (ti_arrow || A ||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Admitted.

Lemma ttyp_trans_rcd : forall l A,
    (* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    |[(typ_rcd l A)]| = ttyp_rcd (ti_rcd l || A ||) |[A]| ttyp_top.
Admitted.

Lemma ttyp_trans_and : forall A B C,
    concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C.
Admitted.

(* Standard properties of typing *)

Lemma target_typing_wf : forall E t A,
    target_typing E t A -> uniq E.
Proof with eauto; destruct_uniq; solve_uniq.
  introv H.
  induction* H.
  - pick_fresh x. forwards*: H1 x...
  - pick_fresh x. forwards*: H0 x...
Qed.


(* proved in TG *)
Lemma target_weakening_simpl : forall E F e T,
    target_typing E e T ->
    uniq (F ++ E) ->
    target_typing (F ++ E) e T.
Admitted.

(* Auxiliary tactics *)

Lemma spl_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min_mutual); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ |- _ ] =>
           ( lets (?&?): spl_decrease_size H; clear H)
    end.

Ltac elia :=
  try solve [pose proof (size_typ_min_mutual);
             spl_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

(* Type safety *)
(** The key is to prove the lookup label does exists in the record *)
(** To prove type safety, we need to translate typing contexts / types
 \ x : A . e : B  => A->B ~> \ x . |e| ??? **)

#[local] Hint Resolve target_typing_wf ttyp_trans_wf : core.
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

(* properties of  flex_typing *)

Lemma target_flex_typing_wf : forall E t A,
    target_flex_typing E t A -> uniq E.
Proof with eauto using target_typing_wf; destruct_uniq; solve_uniq.
  introv H.
  induction* H.
Qed.

#[local] Hint Resolve target_flex_typing_wf : core.

Lemma flex_typing_property0 : forall E t A,
    target_typing E t |[A]| ->
    target_flex_typing E t |[A]|.
Admitted.

Lemma flex_typing_property1 : forall E t A B,
    target_flex_typing E t |[typ_and A B]| ->
    target_flex_typing E t |[A]| /\ target_flex_typing E t |[B]|.
Admitted.

(* non-deterministic lookup works *)
Lemma flex_typing_property2 : forall E t At Bt ll,
    target_flex_typing E t At -> contained_by_rec_typ At ll Bt ->
    target_typing E (texp_proj t ll) Bt.
Admitted.

(* every lookup can be separately typed *)
Lemma flex_typing_property3 : forall E t At ll Ct,
    target_flex_typing E t At -> Tlookup ll At = Some Ct ->
    exists Bt, target_typing E t Bt /\ Tlookup ll Bt = Some Ct.
Admitted.

(* every non-deterministic lookup can be separately typed *)
Lemma flex_typing_property3_alter : forall E t At ll Ct,
    target_flex_typing E t At -> contained_by_rec_typ At ll Ct ->
    exists Bt, target_typing E t Bt /\ Tlookup ll Bt = Some Ct.
Admitted.

Lemma comerge_split : forall t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> spl B A1 A2.
Proof.
  introv H.
  induction* H.
  - apply Sp_arrow.
    pick fresh x. applys* H0.
Qed.

(* Properties about type translation *)
Lemma concat_source_intersection : forall A B,
    concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Admitted.

Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Admitted.

(* new property: same label means same type *)
Lemma comerge_well_typed : forall E t1 A1 t B t2 A2,
    comerge t1 A1 B t2 A2 t -> target_typing E t1 |[A1]| -> target_typing E t2 |[A2]|
  -> target_typing E t |[B]|.
Proof with elia; eauto.
  introv HC HTa HTb. gen E t1 t2 t B.
  indTypSize (size_typ A1 + size_typ A2). inverts HC.
  - applys* TTyping_RcdMerge HTa HTb.
    1,2: applys* translate_to_record_types.
    applys* concat_source_intersection.
  - (* abs *)
    rewrite ttyp_trans_ord_ntop_arrow...
    applys* TTyping_RcdCons.
    pick fresh x and apply TTyping_Abs...
    forwards* Hc: H x.
    forwards: IH ((x, |[ A ]|) :: E) Hc...
    1-2: applys TTyping_App...
    1-2: applys TTyping_RcdProj...
    1,3: rewrite_env ( [ (x, |[ A ]|) ] ++  E); applys target_weakening_simpl.
    1,3: eassumption.
    1,2: simpl...
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


Lemma cosub_well_typed : forall E t1 A B t2,
    cosub t1 A B t2 -> target_flex_typing E t1 |[A]| -> target_typing E t2 |[B]|.
Proof with elia; eauto.
  introv HS HT. gen t1 t2 E.
  indTypSize (size_typ A + size_typ B). inverts HS.
  - (* top *)
    forwards* EQ: ttyp_trans_ord_top B. rewrite EQ...
  - (* bot *)
    forwards* (?&EQ&WF): ttyp_trans_ord_ntop B. rewrite EQ...
    applys* TTyping_RcdCons...
    pick fresh y and apply TTyping_Fix...
    unfold open_texp_wrt_texp. simpl. applys TTyping_Var...
  - (* base *)
    rewrite ttyp_trans_base...
    applys* TTyping_RcdCons...
    forwards* (?&?&?): flex_typing_property3 (|| typ_base ||) HT. rewrite ttyp_trans_base.
    simpl...
  - (* arrow *)
    rewrite ttyp_trans_ord_ntop_arrow...
    applys* TTyping_RcdCons...
    pick fresh y and apply TTyping_Abs. applys* ttyp_trans_wf.
    forwards* (HS1 & HS2): H1 y.
    forwards: IH HS1 ((y, |[ B1 ]|) :: E)...
    { applys* flex_typing_property0. }
    forwards: IH HS2...
    { applys flex_typing_property0.
      applys TTyping_App...
      rewrite_env ([ (y, |[ B1 ]|) ] ++ E).
      applys target_weakening_simpl.
      forwards* (?&?&?): flex_typing_property3 (|| (typ_arrow A1 A2) ||) HT.
      rewrite ttyp_trans_ord_ntop_arrow...
      unfold Tlookup... case_if...
      destruct_uniq...
    }
  - (* rcd *)
    rewrite ttyp_trans_rcd... applys* TTyping_RcdCons...
    forwards: IH H1 E...
    applys* flex_typing_property0.
    forwards* (?&?&?): flex_typing_property3 (|| (typ_rcd l0 A0) ||) HT.
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
Admitted.

Lemma distapp_well_typed_app : forall A B C G t1 t2 t3,
    appdist A (typ_arrow B C) -> target_flex_typing ||[ G ]|| t1 |[A]| ->
    target_flex_typing ||[ G ]|| t2 |[B]| -> distapp t1 A (tvl_exp t2) t3 ->
    target_typing ||[ G ]|| t3 |[C]|.
Proof with eauto using target_typing_wf.
  introv HA HTa HTb HD. gen t1 t2.
  inductions HA; intros; inverts HD...
  - rewrite* ttyp_trans_ord_top.
    inverts* H4.
  - applys* TTyping_App.
    forwards* (?&?&?): flex_typing_property3 (|| (typ_arrow B C) ||) HTa.
    rewrite ttyp_trans_ord_ntop_arrow.
    simpl. case_if...
    Admitted.
  (* - rewrite* ttyp_trans_ord_top... *)
  (* - rewrite* ttyp_trans_ord_top. *)
  (*   inverts H4. eauto using toplike_appdist_inv. *)
  (* - forwards* (HTa1 & HTa2): flex_typing_property1 HTa. *)
  (*   forwards* (HTb1 & HTb2): flex_typing_property1 HTb. *)
  (*   forwards: IHHA2 HTa2 HTb2; try reflexivity. *)


Lemma distapp_well_typed_proj : forall A l B G t1 t3,
    appdist A (typ_rcd l B) -> target_typing ||[ G ]|| t1 |[A]| ->
    distapp t1 A (tvl_la l) t3 ->
    target_typing ||[ G ]|| t3 |[B]|.
Proof with eauto using target_typing_wf.
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
Proof with eauto using translate_to_record_types, target_typing_wf, ctx_trans_preserves_uniq.
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
