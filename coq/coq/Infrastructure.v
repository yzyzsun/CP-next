Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Export rules_inf.
Require Export rules_inf2.


Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

Notation "G ||- t : T" := (target_typing G t T) (at level 40, t custom stlc, T custom stlc_ty at level 0).

Notation " ||- T" := (wf_typ T) (at level 40, T custom stlc_ty at level 0).

Notation "t '>->' t'" := (target_step t t') (at level 40).


Notation "[ z ~>> u ] e" := (subst_texp u z e) (at level 0).
Notation "G |- t : At" := (target_typing G t At) (at level 200). (* >= 200 or Ltac will be affected*)
Notation "At > Ct < Bt" := (concat_typ At Bt Ct) (at level 40).
Notation "( t1 ,, t2 )" := (texp_concat t1 t2) (at level 201).  (* > 200 or Proof commands will be affected*)
Notation "{ ll => t1 ; t2 }" := (texp_cons ll t1 t2) (at level 40).
Notation "{ ll : At ; Bt }" := (ttyp_rcd ll At Bt) (at level 40).


(*********************** Locally nameless related defns ***********************)

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C:= gather_atoms_with (fun x : exp => fv_exp x) in
  let D := gather_atoms_with (fun x : texp => fv_texp x) in
  let E := gather_atoms_with (fun x : tvl => fv_tvl x) in
  let F := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let G := gather_atoms_with (fun x : list (var * ttyp) => dom x) in
  let H := gather_atoms_with (fun x : ctx => dom x) in
  let H' := gather_atoms_with (fun x : tctx => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G  `union` H `union` H').


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


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
