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
