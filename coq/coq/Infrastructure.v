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
Notation "G |- t : At" := (target_typing G t At)  (at level 201, t custom stlc, At custom stlc_ty at level 200). (* > 200 or Ltac will be affected*)
Notation "At > Ct < Bt" := (concat_typ At Bt Ct) (at level 40).
Notation "( t1 ,, t2 )" := (texp_concat t1 t2) (at level 201).  (* > 200 or Proof commands will be affected*)
(* Notation "{ ll => t1 ; t2 }" := (texp_cons ll t1 t2) (at level 80). *)
(* Notation "{ ll : At ; Bt }" := (ttyp_rcd ll At Bt) (at level 80). *)


(*********************** Locally nameless related defns ***********************)

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C:= gather_atoms_with (fun x : exp => fv_exp x) in
  let D := gather_atoms_with (fun x : texp => fv_texp x) in
  (* let E := gather_atoms_with (fun x : label => fv_label x) in *)
  let F := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let G := gather_atoms_with (fun x : list (var * ttyp) => dom x) in
  let H := gather_atoms_with (fun x : ctx => dom x) in
  let H' := gather_atoms_with (fun x : tctx => dom x) in
  constr:(A `union` B `union` C `union` D `union` F `union` G  `union` H `union` H').


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

(* Ltac elia := *)
(*   try solve [pose proof (size_typ_min_mutual); *)
(*              spl_size; simpl in *; try lia]. *)

(* Ltac indTypSize s := *)
(*   assert (SizeInd: exists i, s < i) by eauto; *)
(*   destruct SizeInd as [i SizeInd]; *)
(*   repeat match goal with | [ h : typ |- _ ] => (gen h) end; *)
(*   induction i as [|i IH]; [ *)
(*     intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end *)
(*   | intros ]. *)

Lemma lookup_decrease_size: forall l A C,
    Tlookup l A = Some C -> size_ttyp C < size_ttyp A.
Proof with (pose proof (size_ttyp_min_mutual); simpl in *; try case_if; try discriminate; try lia).
  introv H. gen l C.
  induction A; intros; simpl in *; eauto...
  - injection H. intro HE. subst*...
  - forwards: IHA2 H...
Qed.

Ltac lookup_size :=
  try repeat match goal with
         | [ H: Tlookup _ _ = Some _ |- _ ] =>
           ( lets : lookup_decrease_size H; clear H)
    end.

Ltac elia :=
  try solve [pose proof (size_typ_min_mutual);
             pose proof (size_ttyp_min_mutual);
             spl_size; lookup_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  repeat match goal with | [ h : ttyp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].


(* try any assumption *)
Ltac tassumption := match goal with | H : _ |-_=> apply H end.

(* try solve the goal by contradiction *)
Create HintDb FalseHd.
Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    | exists _, _ => destruct H
    end
         end.

(* Ltac from Alvin *)
Ltac detect_fresh_var_and_do t :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => t x
  | _ =>
    let x := fresh "x" in
    pick fresh x; t x
  end.

Ltac instantiate_cofinite_with H X :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : X `notin` L) by solve_notin;
    specialize (H X H1); clear H1
  end.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
  | H : forall X : var , _ |- _ =>
    specialize (H X)
         end;
  destruct_conj.

Ltac instantiate_cofinites :=
  detect_fresh_var_and_do instantiate_cofinites_with.

Ltac applys_and_instantiate_cofinites_with H x :=
  applys H x; try solve_notin; instantiate_cofinites_with x.

Ltac pick_fresh_applys_and_instantiate_cofinites H :=
  let X:= fresh in
  pick fresh X; applys_and_instantiate_cofinites_with H X.

Ltac detect_fresh_var_and_apply H :=
  let f x := applys_and_instantiate_cofinites_with H x in
  detect_fresh_var_and_do f.


Ltac destruct_disj :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ \/ _ => destruct H
    end
    end.
