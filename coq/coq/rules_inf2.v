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

Scheme tindex_ind' := Induction for tindex Sort Prop.

Definition tindex_mutind :=
  fun H1 =>
  tindex_ind' H1.

Scheme tindex_rec' := Induction for tindex Sort Set.

Definition tindex_mutrec :=
  fun H1 =>
  tindex_rec' H1.

Scheme ttyp_ind' := Induction for ttyp Sort Prop.

Definition ttyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  ttyp_ind' H1 H2 H3 H4 H5 H6.

Scheme ttyp_rec' := Induction for ttyp Sort Set.

Definition ttyp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  ttyp_rec' H1 H2 H3 H4 H5 H6.

Scheme texp_ind' := Induction for texp Sort Prop.

Definition texp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  texp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme texp_rec' := Induction for texp Sort Set.

Definition texp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  texp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_texp_wrt_texp_rec (n1 : nat) (x1 : var) (t1 : texp) {struct t1} : texp :=
  match t1 with
    | texp_var_f x2 => if (x1 == x2) then (texp_var_b n1) else (texp_var_f x2)
    | texp_var_b n2 => if (lt_ge_dec n2 n1) then (texp_var_b n2) else (texp_var_b (S n2))
    | texp_base b1 => texp_base b1
    | texp_abs t2 => texp_abs (close_texp_wrt_texp_rec (S n1) x1 t2)
    | texp_fixpoint t2 => texp_fixpoint (close_texp_wrt_texp_rec (S n1) x1 t2)
    | texp_app t2 t3 => texp_app (close_texp_wrt_texp_rec n1 x1 t2) (close_texp_wrt_texp_rec n1 x1 t3)
    | texp_nil => texp_nil
    | texp_cons ll1 t2 t3 => texp_cons ll1 (close_texp_wrt_texp_rec n1 x1 t2) (close_texp_wrt_texp_rec n1 x1 t3)
    | texp_proj t2 ll1 => texp_proj (close_texp_wrt_texp_rec n1 x1 t2) ll1
    | texp_concat t2 t3 => texp_concat (close_texp_wrt_texp_rec n1 x1 t2) (close_texp_wrt_texp_rec n1 x1 t3)
  end.

Definition close_texp_wrt_texp x1 t1 := close_texp_wrt_texp_rec 0 x1 t1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_ttyp (At1 : ttyp) {struct At1} : nat :=
  match At1 with
    | ttyp_top => 1
    | ttyp_bot => 1
    | ttyp_base => 1
    | ttyp_arrow At2 Bt1 => 1 + (size_ttyp At2) + (size_ttyp Bt1)
    | ttyp_rcd ll1 At2 Bt1 => 1 + (size_tindex ll1) + (size_ttyp At2) + (size_ttyp Bt1)
  end.

Fixpoint size_texp (t1 : texp) {struct t1} : nat :=
  match t1 with
    | texp_var_f x1 => 1
    | texp_var_b n1 => 1
    | texp_base b1 => 1
    | texp_abs t2 => 1 + (size_texp t2)
    | texp_fixpoint t2 => 1 + (size_texp t2)
    | texp_app t2 t3 => 1 + (size_texp t2) + (size_texp t3)
    | texp_nil => 1
    | texp_cons ll1 t2 t3 => 1 + (size_tindex ll1) + (size_texp t2) + (size_texp t3)
    | texp_proj t2 ll1 => 1 + (size_texp t2) + (size_tindex ll1)
    | texp_concat t2 t3 => 1 + (size_texp t2) + (size_texp t3)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_texp_wrt_texp : nat -> texp -> Prop :=
  | degree_wrt_texp_texp_var_f : forall n1 x1,
    degree_texp_wrt_texp n1 (texp_var_f x1)
  | degree_wrt_texp_texp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_texp_wrt_texp n1 (texp_var_b n2)
  | degree_wrt_texp_texp_base : forall n1 b1,
    degree_texp_wrt_texp n1 (texp_base b1)
  | degree_wrt_texp_texp_abs : forall n1 t1,
    degree_texp_wrt_texp (S n1) t1 ->
    degree_texp_wrt_texp n1 (texp_abs t1)
  | degree_wrt_texp_texp_fixpoint : forall n1 t1,
    degree_texp_wrt_texp (S n1) t1 ->
    degree_texp_wrt_texp n1 (texp_fixpoint t1)
  | degree_wrt_texp_texp_app : forall n1 t1 t2,
    degree_texp_wrt_texp n1 t1 ->
    degree_texp_wrt_texp n1 t2 ->
    degree_texp_wrt_texp n1 (texp_app t1 t2)
  | degree_wrt_texp_texp_nil : forall n1,
    degree_texp_wrt_texp n1 (texp_nil)
  | degree_wrt_texp_texp_cons : forall n1 ll1 t1 t2,
    degree_texp_wrt_texp n1 t1 ->
    degree_texp_wrt_texp n1 t2 ->
    degree_texp_wrt_texp n1 (texp_cons ll1 t1 t2)
  | degree_wrt_texp_texp_proj : forall n1 t1 ll1,
    degree_texp_wrt_texp n1 t1 ->
    degree_texp_wrt_texp n1 (texp_proj t1 ll1)
  | degree_wrt_texp_texp_concat : forall n1 t1 t2,
    degree_texp_wrt_texp n1 t1 ->
    degree_texp_wrt_texp n1 t2 ->
    degree_texp_wrt_texp n1 (texp_concat t1 t2).

Scheme degree_texp_wrt_texp_ind' := Induction for degree_texp_wrt_texp Sort Prop.

Definition degree_texp_wrt_texp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_texp_wrt_texp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors degree_texp_wrt_texp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_texp : texp -> Set :=
  | lc_set_texp_var_f : forall x1,
    lc_set_texp (texp_var_f x1)
  | lc_set_texp_base : forall b1,
    lc_set_texp (texp_base b1)
  | lc_set_texp_abs : forall t1,
    (forall x1 : var, lc_set_texp (open_texp_wrt_texp t1 (texp_var_f x1))) ->
    lc_set_texp (texp_abs t1)
  | lc_set_texp_fixpoint : forall t1,
    (forall x1 : var, lc_set_texp (open_texp_wrt_texp t1 (texp_var_f x1))) ->
    lc_set_texp (texp_fixpoint t1)
  | lc_set_texp_app : forall t1 t2,
    lc_set_texp t1 ->
    lc_set_texp t2 ->
    lc_set_texp (texp_app t1 t2)
  | lc_set_texp_nil :
    lc_set_texp (texp_nil)
  | lc_set_texp_cons : forall ll1 t1 t2,
    lc_set_texp t1 ->
    lc_set_texp t2 ->
    lc_set_texp (texp_cons ll1 t1 t2)
  | lc_set_texp_proj : forall t1 ll1,
    lc_set_texp t1 ->
    lc_set_texp (texp_proj t1 ll1)
  | lc_set_texp_concat : forall t1 t2,
    lc_set_texp t1 ->
    lc_set_texp t2 ->
    lc_set_texp (texp_concat t1 t2).

Scheme lc_texp_ind' := Induction for lc_texp Sort Prop.

Definition lc_texp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_texp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_texp_ind' := Induction for lc_set_texp Sort Prop.

Definition lc_set_texp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_texp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_texp_rec' := Induction for lc_set_texp Sort Set.

Definition lc_set_texp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_texp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors lc_texp : core lngen.

Hint Constructors lc_set_texp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_texp_wrt_texp t1 := forall x1, lc_texp (open_texp_wrt_texp t1 (texp_var_f x1)).

Hint Unfold body_texp_wrt_texp : core.


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

Lemma size_tindex_min_mutual :
(forall ll1, 1 <= size_tindex ll1).
Proof.
apply_mutual_ind tindex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_tindex_min :
forall ll1, 1 <= size_tindex ll1.
Proof.
pose proof size_tindex_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_tindex_min : lngen.

(* begin hide *)

Lemma size_ttyp_min_mutual :
(forall At1, 1 <= size_ttyp At1).
Proof.
apply_mutual_ind ttyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ttyp_min :
forall At1, 1 <= size_ttyp At1.
Proof.
pose proof size_ttyp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_ttyp_min : lngen.

(* begin hide *)

Lemma size_texp_min_mutual :
(forall t1, 1 <= size_texp t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_texp_min :
forall t1, 1 <= size_texp t1.
Proof.
pose proof size_texp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_texp_min : lngen.

(* begin hide *)

Lemma size_texp_close_texp_wrt_texp_rec_mutual :
(forall t1 x1 n1,
  size_texp (close_texp_wrt_texp_rec n1 x1 t1) = size_texp t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_texp_close_texp_wrt_texp_rec :
forall t1 x1 n1,
  size_texp (close_texp_wrt_texp_rec n1 x1 t1) = size_texp t1.
Proof.
pose proof size_texp_close_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_texp_close_texp_wrt_texp_rec : lngen.
Hint Rewrite size_texp_close_texp_wrt_texp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_texp_close_texp_wrt_texp :
forall t1 x1,
  size_texp (close_texp_wrt_texp x1 t1) = size_texp t1.
Proof.
unfold close_texp_wrt_texp; default_simp.
Qed.

Hint Resolve size_texp_close_texp_wrt_texp : lngen.
Hint Rewrite size_texp_close_texp_wrt_texp using solve [auto] : lngen.

(* begin hide *)

Lemma size_texp_open_texp_wrt_texp_rec_mutual :
(forall t1 t2 n1,
  size_texp t1 <= size_texp (open_texp_wrt_texp_rec n1 t2 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_texp_open_texp_wrt_texp_rec :
forall t1 t2 n1,
  size_texp t1 <= size_texp (open_texp_wrt_texp_rec n1 t2 t1).
Proof.
pose proof size_texp_open_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_texp_open_texp_wrt_texp_rec : lngen.

(* end hide *)

Lemma size_texp_open_texp_wrt_texp :
forall t1 t2,
  size_texp t1 <= size_texp (open_texp_wrt_texp t1 t2).
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve size_texp_open_texp_wrt_texp : lngen.

(* begin hide *)

Lemma size_texp_open_texp_wrt_texp_rec_var_mutual :
(forall t1 x1 n1,
  size_texp (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1) = size_texp t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_texp_open_texp_wrt_texp_rec_var :
forall t1 x1 n1,
  size_texp (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1) = size_texp t1.
Proof.
pose proof size_texp_open_texp_wrt_texp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_texp_open_texp_wrt_texp_rec_var : lngen.
Hint Rewrite size_texp_open_texp_wrt_texp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_texp_open_texp_wrt_texp_var :
forall t1 x1,
  size_texp (open_texp_wrt_texp t1 (texp_var_f x1)) = size_texp t1.
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve size_texp_open_texp_wrt_texp_var : lngen.
Hint Rewrite size_texp_open_texp_wrt_texp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_texp_wrt_texp_S_mutual :
(forall n1 t1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp (S n1) t1).
Proof.
apply_mutual_ind degree_texp_wrt_texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_texp_wrt_texp_S :
forall n1 t1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp (S n1) t1.
Proof.
pose proof degree_texp_wrt_texp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_texp_wrt_texp_S : lngen.

Lemma degree_texp_wrt_texp_O :
forall n1 t1,
  degree_texp_wrt_texp O t1 ->
  degree_texp_wrt_texp n1 t1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_texp_wrt_texp_O : lngen.

(* begin hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp_rec_mutual :
(forall t1 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp (S n1) (close_texp_wrt_texp_rec n1 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp_rec :
forall t1 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp (S n1) (close_texp_wrt_texp_rec n1 x1 t1).
Proof.
pose proof degree_texp_wrt_texp_close_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_texp_wrt_texp_close_texp_wrt_texp_rec : lngen.

(* end hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp :
forall t1 x1,
  degree_texp_wrt_texp 0 t1 ->
  degree_texp_wrt_texp 1 (close_texp_wrt_texp x1 t1).
Proof.
unfold close_texp_wrt_texp; default_simp.
Qed.

Hint Resolve degree_texp_wrt_texp_close_texp_wrt_texp : lngen.

(* begin hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp_rec_inv_mutual :
(forall t1 x1 n1,
  degree_texp_wrt_texp (S n1) (close_texp_wrt_texp_rec n1 x1 t1) ->
  degree_texp_wrt_texp n1 t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp_rec_inv :
forall t1 x1 n1,
  degree_texp_wrt_texp (S n1) (close_texp_wrt_texp_rec n1 x1 t1) ->
  degree_texp_wrt_texp n1 t1.
Proof.
pose proof degree_texp_wrt_texp_close_texp_wrt_texp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_texp_wrt_texp_close_texp_wrt_texp_rec_inv : lngen.

(* end hide *)

Lemma degree_texp_wrt_texp_close_texp_wrt_texp_inv :
forall t1 x1,
  degree_texp_wrt_texp 1 (close_texp_wrt_texp x1 t1) ->
  degree_texp_wrt_texp 0 t1.
Proof.
unfold close_texp_wrt_texp; eauto with lngen.
Qed.

Hint Immediate degree_texp_wrt_texp_close_texp_wrt_texp_inv : lngen.

(* begin hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp_rec_mutual :
(forall t1 t2 n1,
  degree_texp_wrt_texp (S n1) t1 ->
  degree_texp_wrt_texp n1 t2 ->
  degree_texp_wrt_texp n1 (open_texp_wrt_texp_rec n1 t2 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp_rec :
forall t1 t2 n1,
  degree_texp_wrt_texp (S n1) t1 ->
  degree_texp_wrt_texp n1 t2 ->
  degree_texp_wrt_texp n1 (open_texp_wrt_texp_rec n1 t2 t1).
Proof.
pose proof degree_texp_wrt_texp_open_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_texp_wrt_texp_open_texp_wrt_texp_rec : lngen.

(* end hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp :
forall t1 t2,
  degree_texp_wrt_texp 1 t1 ->
  degree_texp_wrt_texp 0 t2 ->
  degree_texp_wrt_texp 0 (open_texp_wrt_texp t1 t2).
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve degree_texp_wrt_texp_open_texp_wrt_texp : lngen.

(* begin hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp_rec_inv_mutual :
(forall t1 t2 n1,
  degree_texp_wrt_texp n1 (open_texp_wrt_texp_rec n1 t2 t1) ->
  degree_texp_wrt_texp (S n1) t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp_rec_inv :
forall t1 t2 n1,
  degree_texp_wrt_texp n1 (open_texp_wrt_texp_rec n1 t2 t1) ->
  degree_texp_wrt_texp (S n1) t1.
Proof.
pose proof degree_texp_wrt_texp_open_texp_wrt_texp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_texp_wrt_texp_open_texp_wrt_texp_rec_inv : lngen.

(* end hide *)

Lemma degree_texp_wrt_texp_open_texp_wrt_texp_inv :
forall t1 t2,
  degree_texp_wrt_texp 0 (open_texp_wrt_texp t1 t2) ->
  degree_texp_wrt_texp 1 t1.
Proof.
unfold open_texp_wrt_texp; eauto with lngen.
Qed.

Hint Immediate degree_texp_wrt_texp_open_texp_wrt_texp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_texp_wrt_texp_rec_inj_mutual :
(forall t1 t2 x1 n1,
  close_texp_wrt_texp_rec n1 x1 t1 = close_texp_wrt_texp_rec n1 x1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind texp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_texp_wrt_texp_rec_inj :
forall t1 t2 x1 n1,
  close_texp_wrt_texp_rec n1 x1 t1 = close_texp_wrt_texp_rec n1 x1 t2 ->
  t1 = t2.
Proof.
pose proof close_texp_wrt_texp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_texp_wrt_texp_rec_inj : lngen.

(* end hide *)

Lemma close_texp_wrt_texp_inj :
forall t1 t2 x1,
  close_texp_wrt_texp x1 t1 = close_texp_wrt_texp x1 t2 ->
  t1 = t2.
Proof.
unfold close_texp_wrt_texp; eauto with lngen.
Qed.

Hint Immediate close_texp_wrt_texp_inj : lngen.

(* begin hide *)

Lemma close_texp_wrt_texp_rec_open_texp_wrt_texp_rec_mutual :
(forall t1 x1 n1,
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp_rec n1 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1) = t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_texp_wrt_texp_rec_open_texp_wrt_texp_rec :
forall t1 x1 n1,
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp_rec n1 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1) = t1.
Proof.
pose proof close_texp_wrt_texp_rec_open_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_texp_wrt_texp_rec_open_texp_wrt_texp_rec : lngen.
Hint Rewrite close_texp_wrt_texp_rec_open_texp_wrt_texp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_texp_wrt_texp_open_texp_wrt_texp :
forall t1 x1,
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp x1 (open_texp_wrt_texp t1 (texp_var_f x1)) = t1.
Proof.
unfold close_texp_wrt_texp; unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve close_texp_wrt_texp_open_texp_wrt_texp : lngen.
Hint Rewrite close_texp_wrt_texp_open_texp_wrt_texp using solve [auto] : lngen.

(* begin hide *)

Lemma open_texp_wrt_texp_rec_close_texp_wrt_texp_rec_mutual :
(forall t1 x1 n1,
  open_texp_wrt_texp_rec n1 (texp_var_f x1) (close_texp_wrt_texp_rec n1 x1 t1) = t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_texp_wrt_texp_rec_close_texp_wrt_texp_rec :
forall t1 x1 n1,
  open_texp_wrt_texp_rec n1 (texp_var_f x1) (close_texp_wrt_texp_rec n1 x1 t1) = t1.
Proof.
pose proof open_texp_wrt_texp_rec_close_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_texp_wrt_texp_rec_close_texp_wrt_texp_rec : lngen.
Hint Rewrite open_texp_wrt_texp_rec_close_texp_wrt_texp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_texp_wrt_texp_close_texp_wrt_texp :
forall t1 x1,
  open_texp_wrt_texp (close_texp_wrt_texp x1 t1) (texp_var_f x1) = t1.
Proof.
unfold close_texp_wrt_texp; unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve open_texp_wrt_texp_close_texp_wrt_texp : lngen.
Hint Rewrite open_texp_wrt_texp_close_texp_wrt_texp using solve [auto] : lngen.

(* begin hide *)

Lemma open_texp_wrt_texp_rec_inj_mutual :
(forall t2 t1 x1 n1,
  x1 `notin` fv_texp t2 ->
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp_rec n1 (texp_var_f x1) t2 = open_texp_wrt_texp_rec n1 (texp_var_f x1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind texp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_texp_wrt_texp_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_texp t2 ->
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp_rec n1 (texp_var_f x1) t2 = open_texp_wrt_texp_rec n1 (texp_var_f x1) t1 ->
  t2 = t1.
Proof.
pose proof open_texp_wrt_texp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_texp_wrt_texp_rec_inj : lngen.

(* end hide *)

Lemma open_texp_wrt_texp_inj :
forall t2 t1 x1,
  x1 `notin` fv_texp t2 ->
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp t2 (texp_var_f x1) = open_texp_wrt_texp t1 (texp_var_f x1) ->
  t2 = t1.
Proof.
unfold open_texp_wrt_texp; eauto with lngen.
Qed.

Hint Immediate open_texp_wrt_texp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_texp_wrt_texp_of_lc_texp_mutual :
(forall t1,
  lc_texp t1 ->
  degree_texp_wrt_texp 0 t1).
Proof.
apply_mutual_ind lc_texp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_texp_wrt_texp_of_lc_texp :
forall t1,
  lc_texp t1 ->
  degree_texp_wrt_texp 0 t1.
Proof.
pose proof degree_texp_wrt_texp_of_lc_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_texp_wrt_texp_of_lc_texp : lngen.

(* begin hide *)

Lemma lc_texp_of_degree_size_mutual :
forall i1,
(forall t1,
  size_texp t1 = i1 ->
  degree_texp_wrt_texp 0 t1 ->
  lc_texp t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind texp_mutind;
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

Lemma lc_texp_of_degree :
forall t1,
  degree_texp_wrt_texp 0 t1 ->
  lc_texp t1.
Proof.
intros t1; intros;
pose proof (lc_texp_of_degree_size_mutual (size_texp t1));
intuition eauto.
Qed.

Hint Resolve lc_texp_of_degree : lngen.

Ltac tindex_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac ttyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac texp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_texp_wrt_texp_of_lc_texp in J1; clear H
          end).

Lemma lc_texp_abs_exists :
forall x1 t1,
  lc_texp (open_texp_wrt_texp t1 (texp_var_f x1)) ->
  lc_texp (texp_abs t1).
Proof.
intros; texp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_texp_fixpoint_exists :
forall x1 t1,
  lc_texp (open_texp_wrt_texp t1 (texp_var_f x1)) ->
  lc_texp (texp_fixpoint t1).
Proof.
intros; texp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_texp (texp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_texp_abs_exists x1) : core.

Hint Extern 1 (lc_texp (texp_fixpoint _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_texp_fixpoint_exists x1) : core.

Lemma lc_body_texp_wrt_texp :
forall t1 t2,
  body_texp_wrt_texp t1 ->
  lc_texp t2 ->
  lc_texp (open_texp_wrt_texp t1 t2).
Proof.
unfold body_texp_wrt_texp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
texp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_texp_wrt_texp : lngen.

Lemma lc_body_texp_abs_1 :
forall t1,
  lc_texp (texp_abs t1) ->
  body_texp_wrt_texp t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_texp_abs_1 : lngen.

Lemma lc_body_texp_fixpoint_1 :
forall t1,
  lc_texp (texp_fixpoint t1) ->
  body_texp_wrt_texp t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_texp_fixpoint_1 : lngen.

(* begin hide *)

Lemma lc_texp_unique_mutual :
(forall t1 (proof2 proof3 : lc_texp t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_texp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_texp_unique :
forall t1 (proof2 proof3 : lc_texp t1), proof2 = proof3.
Proof.
pose proof lc_texp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_texp_unique : lngen.

(* begin hide *)

Lemma lc_texp_of_lc_set_texp_mutual :
(forall t1, lc_set_texp t1 -> lc_texp t1).
Proof.
apply_mutual_ind lc_set_texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_texp_of_lc_set_texp :
forall t1, lc_set_texp t1 -> lc_texp t1.
Proof.
pose proof lc_texp_of_lc_set_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_texp_of_lc_set_texp : lngen.

(* begin hide *)

Lemma lc_set_texp_of_lc_texp_size_mutual :
forall i1,
(forall t1,
  size_texp t1 = i1 ->
  lc_texp t1 ->
  lc_set_texp t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind texp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_tindex_of_lc_tindex
 | apply lc_set_texp_of_lc_texp];
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

Lemma lc_set_texp_of_lc_texp :
forall t1,
  lc_texp t1 ->
  lc_set_texp t1.
Proof.
intros t1; intros;
pose proof (lc_set_texp_of_lc_texp_size_mutual (size_texp t1));
intuition eauto.
Qed.

Hint Resolve lc_set_texp_of_lc_texp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_texp_wrt_texp_rec_degree_texp_wrt_texp_mutual :
(forall t1 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp_rec n1 x1 t1 = t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_texp_wrt_texp_rec_degree_texp_wrt_texp :
forall t1 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp_rec n1 x1 t1 = t1.
Proof.
pose proof close_texp_wrt_texp_rec_degree_texp_wrt_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_texp_wrt_texp_rec_degree_texp_wrt_texp : lngen.
Hint Rewrite close_texp_wrt_texp_rec_degree_texp_wrt_texp using solve [auto] : lngen.

(* end hide *)

Lemma close_texp_wrt_texp_lc_texp :
forall t1 x1,
  lc_texp t1 ->
  x1 `notin` fv_texp t1 ->
  close_texp_wrt_texp x1 t1 = t1.
Proof.
unfold close_texp_wrt_texp; default_simp.
Qed.

Hint Resolve close_texp_wrt_texp_lc_texp : lngen.
Hint Rewrite close_texp_wrt_texp_lc_texp using solve [auto] : lngen.

(* begin hide *)

Lemma open_texp_wrt_texp_rec_degree_texp_wrt_texp_mutual :
(forall t2 t1 n1,
  degree_texp_wrt_texp n1 t2 ->
  open_texp_wrt_texp_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_texp_wrt_texp_rec_degree_texp_wrt_texp :
forall t2 t1 n1,
  degree_texp_wrt_texp n1 t2 ->
  open_texp_wrt_texp_rec n1 t1 t2 = t2.
Proof.
pose proof open_texp_wrt_texp_rec_degree_texp_wrt_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_texp_wrt_texp_rec_degree_texp_wrt_texp : lngen.
Hint Rewrite open_texp_wrt_texp_rec_degree_texp_wrt_texp using solve [auto] : lngen.

(* end hide *)

Lemma open_texp_wrt_texp_lc_texp :
forall t2 t1,
  lc_texp t2 ->
  open_texp_wrt_texp t2 t1 = t2.
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve open_texp_wrt_texp_lc_texp : lngen.
Hint Rewrite open_texp_wrt_texp_lc_texp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_texp_close_texp_wrt_texp_rec_mutual :
(forall t1 x1 n1,
  fv_texp (close_texp_wrt_texp_rec n1 x1 t1) [=] remove x1 (fv_texp t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_texp_close_texp_wrt_texp_rec :
forall t1 x1 n1,
  fv_texp (close_texp_wrt_texp_rec n1 x1 t1) [=] remove x1 (fv_texp t1).
Proof.
pose proof fv_texp_close_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_close_texp_wrt_texp_rec : lngen.
Hint Rewrite fv_texp_close_texp_wrt_texp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_texp_close_texp_wrt_texp :
forall t1 x1,
  fv_texp (close_texp_wrt_texp x1 t1) [=] remove x1 (fv_texp t1).
Proof.
unfold close_texp_wrt_texp; default_simp.
Qed.

Hint Resolve fv_texp_close_texp_wrt_texp : lngen.
Hint Rewrite fv_texp_close_texp_wrt_texp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_texp_open_texp_wrt_texp_rec_lower_mutual :
(forall t1 t2 n1,
  fv_texp t1 [<=] fv_texp (open_texp_wrt_texp_rec n1 t2 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_texp_open_texp_wrt_texp_rec_lower :
forall t1 t2 n1,
  fv_texp t1 [<=] fv_texp (open_texp_wrt_texp_rec n1 t2 t1).
Proof.
pose proof fv_texp_open_texp_wrt_texp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_open_texp_wrt_texp_rec_lower : lngen.

(* end hide *)

Lemma fv_texp_open_texp_wrt_texp_lower :
forall t1 t2,
  fv_texp t1 [<=] fv_texp (open_texp_wrt_texp t1 t2).
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve fv_texp_open_texp_wrt_texp_lower : lngen.

(* begin hide *)

Lemma fv_texp_open_texp_wrt_texp_rec_upper_mutual :
(forall t1 t2 n1,
  fv_texp (open_texp_wrt_texp_rec n1 t2 t1) [<=] fv_texp t2 `union` fv_texp t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_texp_open_texp_wrt_texp_rec_upper :
forall t1 t2 n1,
  fv_texp (open_texp_wrt_texp_rec n1 t2 t1) [<=] fv_texp t2 `union` fv_texp t1.
Proof.
pose proof fv_texp_open_texp_wrt_texp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_open_texp_wrt_texp_rec_upper : lngen.

(* end hide *)

Lemma fv_texp_open_texp_wrt_texp_upper :
forall t1 t2,
  fv_texp (open_texp_wrt_texp t1 t2) [<=] fv_texp t2 `union` fv_texp t1.
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve fv_texp_open_texp_wrt_texp_upper : lngen.

(* begin hide *)

Lemma fv_texp_subst_texp_fresh_mutual :
(forall t1 t2 x1,
  x1 `notin` fv_texp t1 ->
  fv_texp (subst_texp t2 x1 t1) [=] fv_texp t1).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_texp_subst_texp_fresh :
forall t1 t2 x1,
  x1 `notin` fv_texp t1 ->
  fv_texp (subst_texp t2 x1 t1) [=] fv_texp t1.
Proof.
pose proof fv_texp_subst_texp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_subst_texp_fresh : lngen.
Hint Rewrite fv_texp_subst_texp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_texp_subst_texp_lower_mutual :
(forall t1 t2 x1,
  remove x1 (fv_texp t1) [<=] fv_texp (subst_texp t2 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_texp_subst_texp_lower :
forall t1 t2 x1,
  remove x1 (fv_texp t1) [<=] fv_texp (subst_texp t2 x1 t1).
Proof.
pose proof fv_texp_subst_texp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_subst_texp_lower : lngen.

(* begin hide *)

Lemma fv_texp_subst_texp_notin_mutual :
(forall t1 t2 x1 x2,
  x2 `notin` fv_texp t1 ->
  x2 `notin` fv_texp t2 ->
  x2 `notin` fv_texp (subst_texp t2 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_texp_subst_texp_notin :
forall t1 t2 x1 x2,
  x2 `notin` fv_texp t1 ->
  x2 `notin` fv_texp t2 ->
  x2 `notin` fv_texp (subst_texp t2 x1 t1).
Proof.
pose proof fv_texp_subst_texp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_subst_texp_notin : lngen.

(* begin hide *)

Lemma fv_texp_subst_texp_upper_mutual :
(forall t1 t2 x1,
  fv_texp (subst_texp t2 x1 t1) [<=] fv_texp t2 `union` remove x1 (fv_texp t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_texp_subst_texp_upper :
forall t1 t2 x1,
  fv_texp (subst_texp t2 x1 t1) [<=] fv_texp t2 `union` remove x1 (fv_texp t1).
Proof.
pose proof fv_texp_subst_texp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_texp_subst_texp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_texp_close_texp_wrt_texp_rec_mutual :
(forall t2 t1 x1 x2 n1,
  degree_texp_wrt_texp n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_texp t1 ->
  subst_texp t1 x1 (close_texp_wrt_texp_rec n1 x2 t2) = close_texp_wrt_texp_rec n1 x2 (subst_texp t1 x1 t2)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_close_texp_wrt_texp_rec :
forall t2 t1 x1 x2 n1,
  degree_texp_wrt_texp n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_texp t1 ->
  subst_texp t1 x1 (close_texp_wrt_texp_rec n1 x2 t2) = close_texp_wrt_texp_rec n1 x2 (subst_texp t1 x1 t2).
Proof.
pose proof subst_texp_close_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_close_texp_wrt_texp_rec : lngen.

Lemma subst_texp_close_texp_wrt_texp :
forall t2 t1 x1 x2,
  lc_texp t1 ->  x1 <> x2 ->
  x2 `notin` fv_texp t1 ->
  subst_texp t1 x1 (close_texp_wrt_texp x2 t2) = close_texp_wrt_texp x2 (subst_texp t1 x1 t2).
Proof.
unfold close_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_close_texp_wrt_texp : lngen.

(* begin hide *)

Lemma subst_texp_degree_texp_wrt_texp_mutual :
(forall t1 t2 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp n1 t2 ->
  degree_texp_wrt_texp n1 (subst_texp t2 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_degree_texp_wrt_texp :
forall t1 t2 x1 n1,
  degree_texp_wrt_texp n1 t1 ->
  degree_texp_wrt_texp n1 t2 ->
  degree_texp_wrt_texp n1 (subst_texp t2 x1 t1).
Proof.
pose proof subst_texp_degree_texp_wrt_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_degree_texp_wrt_texp : lngen.

(* begin hide *)

Lemma subst_texp_fresh_eq_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_texp t2 ->
  subst_texp t1 x1 t2 = t2).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_fresh_eq :
forall t2 t1 x1,
  x1 `notin` fv_texp t2 ->
  subst_texp t1 x1 t2 = t2.
Proof.
pose proof subst_texp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_fresh_eq : lngen.
Hint Rewrite subst_texp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_texp_fresh_same_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_texp t1 ->
  x1 `notin` fv_texp (subst_texp t1 x1 t2)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_fresh_same :
forall t2 t1 x1,
  x1 `notin` fv_texp t1 ->
  x1 `notin` fv_texp (subst_texp t1 x1 t2).
Proof.
pose proof subst_texp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_fresh_same : lngen.

(* begin hide *)

Lemma subst_texp_fresh_mutual :
(forall t2 t1 x1 x2,
  x1 `notin` fv_texp t2 ->
  x1 `notin` fv_texp t1 ->
  x1 `notin` fv_texp (subst_texp t1 x2 t2)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_fresh :
forall t2 t1 x1 x2,
  x1 `notin` fv_texp t2 ->
  x1 `notin` fv_texp t1 ->
  x1 `notin` fv_texp (subst_texp t1 x2 t2).
Proof.
pose proof subst_texp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_fresh : lngen.

Lemma subst_texp_lc_texp :
forall t1 t2 x1,
  lc_texp t1 ->
  lc_texp t2 ->
  lc_texp (subst_texp t2 x1 t1).
Proof.
default_simp.
Qed.

Hint Resolve subst_texp_lc_texp : lngen.

(* begin hide *)

Lemma subst_texp_open_texp_wrt_texp_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_texp t1 ->
  subst_texp t1 x1 (open_texp_wrt_texp_rec n1 t2 t3) = open_texp_wrt_texp_rec n1 (subst_texp t1 x1 t2) (subst_texp t1 x1 t3)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_texp_open_texp_wrt_texp_rec :
forall t3 t1 t2 x1 n1,
  lc_texp t1 ->
  subst_texp t1 x1 (open_texp_wrt_texp_rec n1 t2 t3) = open_texp_wrt_texp_rec n1 (subst_texp t1 x1 t2) (subst_texp t1 x1 t3).
Proof.
pose proof subst_texp_open_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_open_texp_wrt_texp_rec : lngen.

(* end hide *)

Lemma subst_texp_open_texp_wrt_texp :
forall t3 t1 t2 x1,
  lc_texp t1 ->
  subst_texp t1 x1 (open_texp_wrt_texp t3 t2) = open_texp_wrt_texp (subst_texp t1 x1 t3) (subst_texp t1 x1 t2).
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_open_texp_wrt_texp : lngen.

Lemma subst_texp_open_texp_wrt_texp_var :
forall t2 t1 x1 x2,
  x1 <> x2 ->
  lc_texp t1 ->
  open_texp_wrt_texp (subst_texp t1 x1 t2) (texp_var_f x2) = subst_texp t1 x1 (open_texp_wrt_texp t2 (texp_var_f x2)).
Proof.
intros; rewrite subst_texp_open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_open_texp_wrt_texp_var : lngen.

(* begin hide *)

Lemma subst_texp_spec_rec_mutual :
(forall t1 t2 x1 n1,
  subst_texp t2 x1 t1 = open_texp_wrt_texp_rec n1 t2 (close_texp_wrt_texp_rec n1 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_texp_spec_rec :
forall t1 t2 x1 n1,
  subst_texp t2 x1 t1 = open_texp_wrt_texp_rec n1 t2 (close_texp_wrt_texp_rec n1 x1 t1).
Proof.
pose proof subst_texp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_spec_rec : lngen.

(* end hide *)

Lemma subst_texp_spec :
forall t1 t2 x1,
  subst_texp t2 x1 t1 = open_texp_wrt_texp (close_texp_wrt_texp x1 t1) t2.
Proof.
unfold close_texp_wrt_texp; unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_spec : lngen.

(* begin hide *)

Lemma subst_texp_subst_texp_mutual :
(forall t1 t2 t3 x2 x1,
  x2 `notin` fv_texp t2 ->
  x2 <> x1 ->
  subst_texp t2 x1 (subst_texp t3 x2 t1) = subst_texp (subst_texp t2 x1 t3) x2 (subst_texp t2 x1 t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_subst_texp :
forall t1 t2 t3 x2 x1,
  x2 `notin` fv_texp t2 ->
  x2 <> x1 ->
  subst_texp t2 x1 (subst_texp t3 x2 t1) = subst_texp (subst_texp t2 x1 t3) x2 (subst_texp t2 x1 t1).
Proof.
pose proof subst_texp_subst_texp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_subst_texp : lngen.

(* begin hide *)

Lemma subst_texp_close_texp_wrt_texp_rec_open_texp_wrt_texp_rec_mutual :
(forall t2 t1 x1 x2 n1,
  x2 `notin` fv_texp t2 ->
  x2 `notin` fv_texp t1 ->
  x2 <> x1 ->
  degree_texp_wrt_texp n1 t1 ->
  subst_texp t1 x1 t2 = close_texp_wrt_texp_rec n1 x2 (subst_texp t1 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x2) t2))).
Proof.
apply_mutual_ind texp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_texp_close_texp_wrt_texp_rec_open_texp_wrt_texp_rec :
forall t2 t1 x1 x2 n1,
  x2 `notin` fv_texp t2 ->
  x2 `notin` fv_texp t1 ->
  x2 <> x1 ->
  degree_texp_wrt_texp n1 t1 ->
  subst_texp t1 x1 t2 = close_texp_wrt_texp_rec n1 x2 (subst_texp t1 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x2) t2)).
Proof.
pose proof subst_texp_close_texp_wrt_texp_rec_open_texp_wrt_texp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_close_texp_wrt_texp_rec_open_texp_wrt_texp_rec : lngen.

(* end hide *)

Lemma subst_texp_close_texp_wrt_texp_open_texp_wrt_texp :
forall t2 t1 x1 x2,
  x2 `notin` fv_texp t2 ->
  x2 `notin` fv_texp t1 ->
  x2 <> x1 ->
  lc_texp t1 ->
  subst_texp t1 x1 t2 = close_texp_wrt_texp x2 (subst_texp t1 x1 (open_texp_wrt_texp t2 (texp_var_f x2))).
Proof.
unfold close_texp_wrt_texp; unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_close_texp_wrt_texp_open_texp_wrt_texp : lngen.

Lemma subst_texp_texp_abs :
forall x2 t2 t1 x1,
  lc_texp t1 ->
  x2 `notin` fv_texp t1 `union` fv_texp t2 `union` singleton x1 ->
  subst_texp t1 x1 (texp_abs t2) = texp_abs (close_texp_wrt_texp x2 (subst_texp t1 x1 (open_texp_wrt_texp t2 (texp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_texp_texp_abs : lngen.

Lemma subst_texp_texp_fixpoint :
forall x2 t2 t1 x1,
  lc_texp t1 ->
  x2 `notin` fv_texp t1 `union` fv_texp t2 `union` singleton x1 ->
  subst_texp t1 x1 (texp_fixpoint t2) = texp_fixpoint (close_texp_wrt_texp x2 (subst_texp t1 x1 (open_texp_wrt_texp t2 (texp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_texp_texp_fixpoint : lngen.

(* begin hide *)

Lemma subst_texp_intro_rec_mutual :
(forall t1 x1 t2 n1,
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp_rec n1 t2 t1 = subst_texp t2 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1)).
Proof.
apply_mutual_ind texp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_texp_intro_rec :
forall t1 x1 t2 n1,
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp_rec n1 t2 t1 = subst_texp t2 x1 (open_texp_wrt_texp_rec n1 (texp_var_f x1) t1).
Proof.
pose proof subst_texp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_texp_intro_rec : lngen.
Hint Rewrite subst_texp_intro_rec using solve [auto] : lngen.

Lemma subst_texp_intro :
forall x1 t1 t2,
  x1 `notin` fv_texp t1 ->
  open_texp_wrt_texp t1 t2 = subst_texp t2 x1 (open_texp_wrt_texp t1 (texp_var_f x1)).
Proof.
unfold open_texp_wrt_texp; default_simp.
Qed.

Hint Resolve subst_texp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
