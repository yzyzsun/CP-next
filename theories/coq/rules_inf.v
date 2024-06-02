Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntax_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : var) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_top => exp_top
    | exp_base b1 => exp_base b1
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_abs A1 e2 B1 => exp_abs A1 (close_exp_wrt_exp_rec (S n1) x1 e2) B1
    | exp_fixpoint A1 e2 => exp_fixpoint A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_merge e2 e3 => exp_merge (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | exp_rcd l1 e2 => exp_rcd l1 (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_proj e2 l1 => exp_proj (close_exp_wrt_exp_rec n1 x1 e2) l1
  end.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_top => 1
    | typ_bot => 1
    | typ_base => 1
    | typ_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | typ_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | typ_rcd l1 A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_top => 1
    | exp_base b1 => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs A1 e2 B1 => 1 + (size_typ A1) + (size_exp e2) + (size_typ B1)
    | exp_fixpoint A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | exp_rcd l1 e2 => 1 + (size_exp e2)
    | exp_proj e2 l1 => 1 + (size_exp e2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_top : forall n1,
    degree_exp_wrt_exp n1 (exp_top)
  | degree_wrt_exp_exp_base : forall n1 b1,
    degree_exp_wrt_exp n1 (exp_base b1)
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 A1 e1 B1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs A1 e1 B1)
  | degree_wrt_exp_exp_fixpoint : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_fixpoint A1 e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_merge : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_merge e1 e2)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1)
  | degree_wrt_exp_exp_rcd : forall n1 l1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_rcd l1 e1)
  | degree_wrt_exp_exp_proj : forall n1 e1 l1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_proj e1 l1).

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_top :
    lc_set_exp (exp_top)
  | lc_set_exp_base : forall b1,
    lc_set_exp (exp_base b1)
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall A1 e1 B1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs A1 e1 B1)
  | lc_set_exp_fixpoint : forall A1 e1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_fixpoint A1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_merge : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_merge e1 e2)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_exp (exp_anno e1 A1)
  | lc_set_exp_rcd : forall l1 e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_rcd l1 e1)
  | lc_set_exp_proj : forall e1 l1,
    lc_set_exp e1 ->
    lc_set_exp (exp_proj e1 l1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors lc_exp : core lngen.

Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_exp_of_lc_exp in J1; clear H
          end).

Lemma lc_exp_abs_exists :
forall x1 A1 e1 B1,
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs A1 e1 B1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_fixpoint_exists :
forall x1 A1 e1,
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_fixpoint A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_exp (exp_abs _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

Hint Extern 1 (lc_exp (exp_fixpoint _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_fixpoint_exists x1) : core.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_exp_abs_2 :
forall A1 e1 B1,
  lc_exp (exp_abs A1 e1 B1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_abs_2 : lngen.

Lemma lc_body_exp_fixpoint_2 :
forall A1 e1,
  lc_exp (exp_fixpoint A1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_fixpoint_2 : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp e2 `union` fv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_esubst_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (esubst_exp e2 x1 e1) [=] fv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_esubst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (esubst_exp e2 x1 e1) [=] fv_exp e1.
Proof.
pose proof fv_exp_esubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_esubst_exp_fresh : lngen.
Hint Rewrite fv_exp_esubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_esubst_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (esubst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_esubst_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (esubst_exp e2 x1 e1).
Proof.
pose proof fv_exp_esubst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_esubst_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_esubst_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (esubst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_esubst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (esubst_exp e2 x1 e1).
Proof.
pose proof fv_exp_esubst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_esubst_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_esubst_exp_upper_mutual :
(forall e1 e2 x1,
  fv_exp (esubst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_esubst_exp_upper :
forall e1 e2 x1,
  fv_exp (esubst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_esubst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_esubst_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma esubst_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  esubst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (esubst_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  esubst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (esubst_exp e1 x1 e2).
Proof.
pose proof esubst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_close_exp_wrt_exp_rec : lngen.

Lemma esubst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  esubst_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (esubst_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma esubst_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (esubst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (esubst_exp e2 x1 e1).
Proof.
pose proof esubst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma esubst_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  esubst_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  esubst_exp e1 x1 e2 = e2.
Proof.
pose proof esubst_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_fresh_eq : lngen.
Hint Rewrite esubst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma esubst_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (esubst_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (esubst_exp e1 x1 e2).
Proof.
pose proof esubst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_fresh_same : lngen.

(* begin hide *)

Lemma esubst_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (esubst_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (esubst_exp e1 x2 e2).
Proof.
pose proof esubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_fresh : lngen.

Lemma esubst_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (esubst_exp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve esubst_exp_lc_exp : lngen.

(* begin hide *)

Lemma esubst_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  esubst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (esubst_exp e1 x1 e2) (esubst_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma esubst_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  esubst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (esubst_exp e1 x1 e2) (esubst_exp e1 x1 e3).
Proof.
pose proof esubst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma esubst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  esubst_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (esubst_exp e1 x1 e3) (esubst_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_open_exp_wrt_exp : lngen.

Lemma esubst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (esubst_exp e1 x1 e2) (exp_var_f x2) = esubst_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite esubst_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma esubst_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  esubst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma esubst_exp_spec_rec :
forall e1 e2 x1 n1,
  esubst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof esubst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_spec_rec : lngen.

(* end hide *)

Lemma esubst_exp_spec :
forall e1 e2 x1,
  esubst_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_spec : lngen.

(* begin hide *)

Lemma esubst_exp_esubst_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  esubst_exp e2 x1 (esubst_exp e3 x2 e1) = esubst_exp (esubst_exp e2 x1 e3) x2 (esubst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_esubst_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  esubst_exp e2 x1 (esubst_exp e3 x2 e1) = esubst_exp (esubst_exp e2 x1 e3) x2 (esubst_exp e2 x1 e1).
Proof.
pose proof esubst_exp_esubst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_esubst_exp : lngen.

(* begin hide *)

Lemma esubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  esubst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (esubst_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma esubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  esubst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (esubst_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof esubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma esubst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  esubst_exp e1 x1 e2 = close_exp_wrt_exp x2 (esubst_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma esubst_exp_exp_abs :
forall x2 A1 e2 B1 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  esubst_exp e1 x1 (exp_abs A1 e2 B1) = exp_abs (A1) (close_exp_wrt_exp x2 (esubst_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))) (B1).
Proof.
default_simp.
Qed.

Hint Resolve esubst_exp_exp_abs : lngen.

Lemma esubst_exp_exp_fixpoint :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  esubst_exp e1 x1 (exp_fixpoint A1 e2) = exp_fixpoint (A1) (close_exp_wrt_exp x2 (esubst_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve esubst_exp_exp_fixpoint : lngen.

(* begin hide *)

Lemma esubst_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = esubst_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma esubst_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = esubst_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof esubst_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve esubst_exp_intro_rec : lngen.
Hint Rewrite esubst_exp_intro_rec using solve [auto] : lngen.

Lemma esubst_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e1 e2 = esubst_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve esubst_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
