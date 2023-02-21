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

Lemma ttyp_trans_ord_top : forall A,
    ord A -> toplike A -> |[A]| = ttyp_top.
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
Admitted.

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

Definition subtype_wrt_lookup A B :=
  A = B \/ (exists ll At Bt, B = ttyp_rcd ll At Bt /\ forall l C, Tlookup l B = Some C -> Tlookup l A = Some C).
(* maybe too strict? *)
(* exists A', Tlookup l A = Some A' /\ A' ~= C ? *)

Notation "A <: B" := (subtype_wrt_lookup A B) (at level 70). (* too high *)

Lemma subtype_wrt_lookup_refl : forall A,
    subtype_wrt_lookup A A.
Admitted.

#[local] Hint Resolve subtype_wrt_lookup_refl : core.

Lemma subtype_wrt_lookup_same : forall A B l C,
    A <: B -> Tlookup l B = Some C -> Tlookup l A = Some C.
Proof.
  introv HS HL.
  destruct* HS.
  rewrite* H.
Qed.

Lemma elaboration_intersection_left : forall G e dirflag A B t,
    elaboration G e dirflag (typ_and A B) t
    -> exists C, elaboration G e dirflag C t /\ |[C]| <: |[A]|.
Admitted.

Lemma elaboration_intersection_right : forall G e dirflag A B t,
    elaboration G e dirflag (typ_and A B) t
    -> exists C, elaboration G e dirflag C t /\ |[C]| <: |[B]|.
Admitted.

Lemma elaboration_allows_nondeterministic_lookup : forall G e dirflag A t ll Bt,
    elaboration G e dirflag A t
    -> contained_by_rec_typ |[A]| ll Bt
    -> exists E, target_typing E (texp_proj t ll) Bt.
Admitted.

(* Inductive texp_behave_like_styp : texp -> typ -> Prop := *)
(* | tb_inter : forall t B1 B2, *)
(*     texp_behave_like_styp t B1 -> texp_behave_like_styp t B2 -> texp_behave_like_styp t (t_and B1 B2) *)
(* | tb_ => exists E C, target_typing E t C /\ C <: A *)
(*   end. *)

Definition texp_behave_like_styp t A :=
  forall ll Bt, contained_by_rec_typ |[A]| ll Bt
  -> exists E At, target_typing E t At /\ Tlookup ll At = Some Bt.

Lemma texp_behave_like_styp_intersection : forall t A B,
    texp_behave_like_styp t (typ_and A B) -> texp_behave_like_styp t A /\ texp_behave_like_styp t B.
Admitted.

(* Axiom source_trans_intersection_expose_both : forall G e dirflag A B t, *)
(*     elaboration G e dirflag (typ_and A B) t -> *)
(*     exists E A' B', target_typing E t A' /\ A' <: |[A]| /\ *)
(*                   target_typing E t B' /\ B' <: |[B]|. *)

Lemma cosub_well_typed : forall E t1 A A' B t2,
    cosub t1 A B t2 -> target_typing E t1 A' -> A' <: |[A]| -> target_typing E t2 |[B]|.
Proof with elia; eauto.
  introv HS HT. gen t1 t2 E A'.
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
    applys* TTyping_RcdCons... applys* TTyping_RcdProj.
    forwards*: subtype_wrt_lookup_same H. rewrite ttyp_trans_base...
  - (* arrow *)
    rewrite ttyp_trans_ord_ntop_arrow...
    applys* TTyping_RcdCons...
    pick fresh y and apply TTyping_Abs. applys* ttyp_trans_wf.
    forwards* (HS1 & HS2): H2 y.
    forwards: IH HS1 ((y, |[ B1 ]|) :: E)...
    forwards: IH HS2...
    applys TTyping_App... applys TTyping_RcdProj...
    rewrite_env ([ (y, |[ B1 ]|) ] ++ E).
    { eauto using target_weakening_simpl. }
    forwards*: subtype_wrt_lookup_same H...
    rewrite ttyp_trans_ord_ntop_arrow...
    unfold Tlookup... case_if...
  - (* rcd *)
    rewrite ttyp_trans_rcd... applys* TTyping_RcdCons...
    forwards: IH H2 E... applys TTyping_RcdProj...
    forwards*: subtype_wrt_lookup_same H...
    rewrite ttyp_trans_rcd.
    unfold Tlookup. case_if...
  - (* and *)



(** via styp2ttyp to convert type *)
Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t ->
    texp_behave_like_styp t A.
    (* exists E T, target_typing E t T. *)
Abort.
