Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.


(* Require Import StructTact.StringOrders. *)
(* Require Import StructTact.StructTactics. *)

(* convert type to type list which allows list of types inside *)
(* to flatten intersection types *)
Inductive tlist : Set :=
 | tl_bot : tlist
 | tl_base : tlist
 | tl_arrow (U:tlist) (T:tlist)
 | tl_rcd (l:label) (T:tlist)
 | tl_list (l:list tlist).

(* Fixpoint compare_tlist (x y : tlist) : bool := *)
(*   match x,y with *)
(*   | _, _ => true *)
(*   end. *)

(* Compute (sort compare_tlist []). *)


Fixpoint string_of_tlist (T: tlist) : string :=
  match T with
  | tl_list l => fold_left append (List.map string_of_tlist l) ""
  | tl_arrow U T => "(" ++ string_of_tlist U ++ "->" ++ string_of_tlist T ++ ")"
  | tl_rcd l T => "{" ++  l ++ "=>" ++ string_of_tlist T ++ "}"
  | tl_bot => "Bot"
  | tl_base => "Base"
  end.

Coercion string_of_tlist : tlist >-> string.

(* Notation "x <=? y" := ((string_of_tlist x) <=? (string_of_tlist y)) (at level 70). *)
(* Notation "x =? y" := ((string_of_tlist x) =? (string_of_tlist y)) (at level 70). *)

Check String_as_OT.cmp.

Import IfNotations.
Definition new_leb (s1 s2 : string) : bool :=
  if (String_as_OT.cmp s1 s2) is Gt then false else true.
Notation "x <==? y" := (new_leb x y) (at level 70).
(* match (String_as_OT.cmp x y) with | Gt => false | _ => true end *)

(* merge in merge sort *)
Fixpoint merge (l1 l2 : list string) {struct l1} : list string :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if a1 <==? a2 then
        a1 :: merge l1' l2
      else
        a2 :: merge_aux l2'
  end
  in merge_aux l2.


Fixpoint check_toplike (A : typ) :=
  match A with
  | typ_top => true
  | typ_bot => false
  | typ_base => false
  | typ_arrow _ B => check_toplike B
  | typ_rcd l B => check_toplike B
    | typ_and A B => (check_toplike B) && (check_toplike B)
  end.

(* filter toplike type out *)
(* Fixpoint check_toplike (T : tlist) := *)
(*   match T with *)
(*   | tl_bot => false *)
(*   | tl_base => false *)
(*   | tl_arrow _ B => check_toplike B *)
(*   | tl_rcd l B => check_toplike B *)
(*   | tl_list li => fold_left andb (List.map check_toplike li) true *)
(*   end. *)

(* Definition tlist2list (T: tlist) : list tlist := *)
(*   match T with *)
(*   | tl_list l => l *)
(*   | _ => [T] *)
(*   end. *)

(* Lemma check_toplike_sound_complete : forall A, *)
(*     toplike A <-> check_toplike (tl_list (type2tlist A)) = true. *)
(* Admitted. *)

(* Fixpoint check_non_toplike (T : tlist) := negb (check_toplike T). *)

(* Fixpoint tlist_filter (T: tlist) := *)
(*   match T with *)
(*   | tl_list l => tl_list (filter check_non_toplike (List.map tlist_filter l)) *)
(*   | tl_arrow U T => tl_arrow (tlist_filter U) (tlist_filter T) *)
(*   | tl_rcd l T => tl_rcd l (tlist_filter T) *)
(*   | _ => T *)
(*   end. *)

(* Fixpoint type2tlist (A: typ) : list tlist := *)
(*   if (check_toplike A) then [] *)
(*   else *)
(*     match A with *)
(*     | typ_top => [] *)
(*     | typ_bot => [tl_bot] *)
(*     | typ_base => [tl_base] *)
(*     | typ_arrow A1 A2 => [ tl_arrow (tl_list (type2tlist A1)) (tl_list (type2tlist A2)) ] *)
(*     | typ_rcd l A' => [tl_rcd l (tl_list (type2tlist A'))] *)
(*     | typ_and A1 A2 => merge (type2tlist A1) (type2tlist A2) *)
(*     end. *)

Open Scope string_scope.


Definition LS := list string.

Definition list_string_2_string (l : LS) : string :=
  fold_left append l "".

Coercion list_string_2_string : LS >-> string.

Fixpoint type2tlist (A: typ) : LS :=
  if (check_toplike A) then []
  else
    match A with
    | typ_top => []
    | typ_bot => [ "Bot" ]
    | typ_base => [ "Base" ]
    | typ_arrow A1 A2 => [ ( "(" ++ (type2tlist A1) ++ "->" ++ (type2tlist A2) ++ ")" ) ]
    | typ_rcd l A' => ["{" ++  l ++ "=>" ++ (type2tlist A') ++ "}"]
    | typ_and A1 A2 => merge (type2tlist A1) (type2tlist A2)
    end.

(* sort strings *)
(* (* TODO add deduplication *) *)
(* Check ("A" <=? "C"). *)
(* Fixpoint insert (i : string) (l : list string) := *)
(*   match l with *)
(*   | [] => [i] *)
(*   | h :: t => if i <=? h then i :: h :: t else h :: insert i t *)
(*  end. *)

(* Fixpoint sort (l : list string) : list string := *)
(*   match l with *)
(*   | [] => [] *)
(*   | h :: t => insert h (sort t) *)
(*   end. *)

Inductive sorted : list string -> Prop :=
| sorted_nil :
  sorted []
| sorted_1 : forall (x : string),
    sorted [x]
| sorted_cons : forall (x : string) (y : string) (l : list string),
    (x <==? y = true) -> sorted (y :: l) -> sorted (x :: y :: l).

(* Inductive sorted : list tlist -> Prop := *)
(* | sorted_nil : *)
(*   sorted [] *)
(* | sorted_1 : forall (x : tlist), *)
(*     sorted [x] *)
(* | sorted_cons : forall (x : tlist) (y : tlist) (l : list tlist), *)
(*     (x <=? y = true) -> sorted (y :: l) -> sorted (x :: y :: l). *)

(* Definition is_a_sorting_algorithm (f: list tlist -> list tlist) := forall al, *)
(*     Permutation al (f al) /\ sorted (f al). *)

(* Theorem insertion_sort_correct: *)
(*     is_a_sorting_algorithm sort. *)
(* Proof. Admitted. *)

(* Definition stype2string (A: typ) : string := *)
(*   string_of_tlist (tl_list (type2tlist A)). *)

Definition stype2string (A: typ) : string := type2tlist A.

Compute stype2string (typ_and (typ_and typ_base typ_base) typ_bot).
Compute stype2string (typ_and (typ_and typ_bot typ_base) typ_base).
Compute stype2string (typ_arrow (typ_and (typ_and typ_bot typ_base) typ_base) typ_bot).

Notation "|| A ||" := (stype2string A) (at level 50, A at next level). (* 1 is too high *)
(* Notation "| A |" := (tlist_filter (tl_list (type2tlist A))) (at level 50, A at next level). *)

(* Translate source type to target type *)
(* Inductive ttyp2 : Set := *)
(* (* | tt_top : ttyp2 (* tt_rcd [] *) *) *)
(* | tt_bot : ttyp2 *)
(* | tt_base : ttyp2 *)
(* | tt_arrow (T1:ttyp2) (T2:ttyp2) *)
(* | tt_list (l:list (string * ttyp2)) *)
(* . *)

(* Source types to target types *)
Inductive ttyp : Set :=  (*r types *)
 | ttyp_top : ttyp (*r top type *)
 | ttyp_bot : ttyp (*r bottom type *)
 | ttyp_base : ttyp (*r base type *)
 | ttyp_arrow (At:ttyp) (Bt:ttyp) (*r function types *)
 | ttyp_rcd (l:string) (At:ttyp) (Bt:ttyp) (*r record *).

Fixpoint ttyp_concat_simpl (A: ttyp) (B: ttyp) :=
  match A with
  | ttyp_top => B
  | ttyp_rcd l At Bt => ttyp_rcd l At (ttyp_concat_simpl Bt B)
  | _ => ttyp_top
  end.

Reserved Notation "|[ A ]|" (at level 5, A at next level).

Fixpoint styp2ttyp (A: typ) : ttyp :=
  match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_rcd (|| A ||) ttyp_bot ttyp_top
  | typ_base => ttyp_rcd (|| A ||) ttyp_base ttyp_top
  | typ_arrow B1 B2 => ttyp_rcd (|| A ||) ( ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)) ttyp_top
  | typ_rcd l A' => ttyp_rcd (|| A ||) (|[ A' ]|) ttyp_top
  | typ_and A1 A2 => ttyp_concat_simpl (|[ A1 ]|) (|[ A2 ]|)
  end
where "|[ A ]|" := (styp2ttyp A).

Compute (|[ typ_arrow typ_base (typ_and typ_base typ_base) ]|).

(* Properties on merge *)


(* Lemma sorted_merge1 : forall (x x1 x2 : tlist) (l1 l2 : list tlist), *)
(*     ((x <=? x1) = true) -> ((x <=? x2) = true) -> *)
(*     sorted (merge (x1::l1) (x2::l2)) -> *)
(*     sorted (x :: merge (x1::l1) (x2::l2)). *)
(* Proof. *)
(* Admitted. *)

Lemma merge_empty : forall l,
    merge [] l = l.
Proof.
  introv. induction* l.
Qed.

Lemma merge_empty_r : forall l,
    merge l [] = l.
Proof.
  introv. induction* l.
Qed.

#[local] Hint Rewrite merge_empty merge_empty_r : merge.

Lemma merge_cons : forall a l b r,
    merge (a::l) (b::r) = if a <==? b then a :: merge l (b::r) else b :: merge (a::l) r.
Proof with eauto.
  introv. induction* l; case_if; autorewrite with merge...
Qed.

#[local] Hint Rewrite merge_cons : merge.

#[local] Hint Constructors sorted : core.

Lemma leb_flip : forall (x x0 : string),
    (new_leb x x0) = false -> (new_leb x0 x) = true.
Proof with eauto.
  introv H.
  - forwards~ [|]: leb_total x x0; eauto with bool.
  (* - remember (x ?= x0) as Comp. destruct Comp. *)
  (*   all: unfolds; rewrite <- HeqComp... compare_antisym *)
  (* - Search (_ ?= _). *)
  (*    eauto with bool. *)
  (* - forwards~ [|]: leb_total x0 x. *)
  (*   + forwards~ [|]: leb_total x x0. admit. Check leb_total. *)
  (*     unfolds. Search (_ ?= _). *)
  (*     * forwards: leb_antisym H H1. subst. *)
Qed.

#[local] Hint Resolve leb_flip : core.

Lemma sorted_cons_inv : forall h l,
    sorted (h :: l) -> sorted l.
Proof with eauto.
  introv HS. inverts* HS.
Qed.

#[local] Hint Resolve sorted_cons_inv : core.

Lemma merge_sorted : forall l r,
    sorted l -> sorted r -> sorted (merge l r).
Proof with eauto with bool.
  introv HSl HSr. gen r.
  induction HSl; intros; autorewrite with merge...
  - induction HSr; autorewrite with merge...
    + case_if...
    + case_if... case_if... Print merge. Locate "<==?".
      unfold merge in IHHSr. case_if...
  - induction HSr...
    + autorewrite with merge. repeat case_if...
    + autorewrite with merge. repeat case_if...
      lets* HSP: IHHSl [x0]... forwards: HSP.
      * constructor.
      * case_if. econstructor...
    + autorewrite with merge. case_if...
      * lets* HSP: IHHSl (x0 :: y0 :: l0). forwards*: HSP.
        case_if...
      * case_if...
        ** lets* HSP: IHHSl (y0 :: l0). forwards*: HSP.
           case_if...
        ** simpl in IHHSr. case_if...
Qed.

(** * Multisets *)
From Coq Require Import FunctionalExtensionality.
Definition multiset := string -> nat.

(** The [empty] multiset has multiplicity [0] for every value. *)

Definition empty : multiset :=
  fun x => 0.

(** Multiset [singleton v] contains only [v], and exactly once. *)

Definition singleton (v: string) : multiset :=
  fun x => if x =? v then 1 else 0.

(** The union of two multisets is their _pointwise_ sum. *)

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.

Lemma union_assoc: forall a b c : multiset,
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfolds. eauto using Nat.add_assoc.
Qed.

Lemma union_comm: forall a b : multiset,
   union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfolds. eauto using Nat.add_comm.
Qed.

Lemma union_swap : forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros.
  extensionality x.
  unfolds. lia.
Qed.


Fixpoint contents (al: list string) : multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

Lemma contents_inv : forall a bl,
    contents (a :: bl) = union (singleton a) (contents bl).
Proof.
  introv. eauto.
Qed.

Ltac indListSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : list _ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

(* prove merge is a permutation *)
Theorem merge_contents: forall a b,
    union (contents a) (contents b) = contents (merge a b).
Proof.
  intros. extensionality x. indListSize (length a + length b).
  destruct a; destruct b; autorewrite with merge.
  (* induction a; induction b; autorewrite with merge. *)
  1-3: unfolds; simple*.
  case_if.
  - simpl. unfold union. rewrite <- IH.
    unfold union. rewrite (contents_inv s0 b). unfold union.
    all: simpl in *; lia.
  - repeat rewrite (contents_inv s0 _). unfold union. rewrite <- IH.
    { unfold union. lia. }
    simpl in *; lia.
Qed.


Lemma merge_length : forall (l1 l2 : list string),
    length (merge l1 l2) = length l1 + length l2.
Admitted.

Lemma leb_negb : forall (x x0 : string),
    (String.leb x x0) = negb (String.leb x0 x).
Proof with eauto.
  introv.
  forwards~ [|]: leb_total x x0; forwards~ [|]: leb_total x0 x;
    eauto with bool.
Abort.
Require Import Coq.Strings.Ascii. Search (Ascii.compare).
(* Lemma ascii_compare_refl : forall a : ascii, (Ascii.compare a a) = Eq. *)
(* Proof. *)
(*   induction a. *)
(*   unfold compare; simpl. *)
(*   unfold compare_bool. *)
(*   destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity. *)

(*   BinNat.N.compare *)
(*   unfold compare; simpl. *)
(*   repeat (destruct b0 eqn:Hb0; destruct b1 eqn:Hb1; destruct b2 eqn:Hb2; *)
(*           destruct b3 eqn:Hb3; destruct b4 eqn:Hb4; destruct b5 eqn:Hb5; *)
(*           destruct b6 eqn:Hb6; subst; simpl; auto). *)
(*   unfold BinNat.N.compare. simpl. *)
(*   destruct b0, b1, b2, b3, b4, b5, b6. repeat unfolds. simpl. *)
(*   reflexivity. *)
(* Qed. *)
Require Import Coq.Strings.Ascii.

Lemma ascii_compare_refl : forall t : ascii, (t ?= t)%char = Eq.
Proof.
  intro t. destruct t.
  unfold Ascii.compare; simpl. rewrite* BinNat.N.compare_refl.
Qed.

Lemma string_compare_refl : forall s1 : string, (s1 ?= s1) = Eq.
Proof.
  intros. induction* s1.
  simpl. rewrite IHs1. rewrite* ascii_compare_refl.
Qed.

(* Lemma string_leb_refl: forall x, *)
(*   (x <==? x) = true. *)
(* Proof. *)
(*   intros. unfolds. rewrite* string_compare_refl. *)
(* Qed. *)

(* #[local] Hint Rewrite string_leb_refl : core. *)

(* Lemma string_leb_refl_false: forall x, *)
(*   (x <=? x) = false -> False. *)
(* Proof. *)
(*   intros x H. *)
(*   rewrite string_leb_refl in H. discriminate H. *)
(* Qed. *)

Lemma new_leb_string_transitive : forall s1 s2 s3 : string,
  (s1 <==? s2) = true -> (s2 <==? s3) = true -> (s1 <==? s3) = true.
Proof.
  intros s1 s2 s3 H1 H2.
  unfolds. unfolds in H1. unfolds in H2.
  destruct (String_as_OT.cmp s1 s2) eqn:E1; try discriminate;
    destruct (String_as_OT.cmp s2 s3) eqn:E2; try discriminate.
  all: try apply String_as_OT.cmp_eq in E1.
  all: try apply String_as_OT.cmp_eq in E2.
  all: subst*.
  1: now rewrite* string_compare_refl.
  1: now rewrite* E2.
  1: now rewrite* E1.
  all: try apply String_as_OT.cmp_lt in E1.
  all: try apply String_as_OT.cmp_lt in E2.
  all: try forwards H: String_as_OT.lt_trans E1 E2.
  all: try rewrite <- String_as_OT.cmp_lt in H.
  all: now rewrite* H.
Qed.


Lemma leb_string_transitive : forall s1 s2 s3 : string,
  (s1 <=? s2) = true -> (s2 <=? s3) = true -> (s1 <=? s3) = true.
Proof.
  pose proof new_leb_string_transitive.
  eauto.
Qed.

Theorem merge_comm : forall (l1 l2 : list string),
  merge l1 l2 = merge l2 l1.
Proof.
  induction l1 as [| x1 l1' IHl1']; intros l2.
  - autorewrite with merge. reflexivity.
  - destruct l2 as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. unfold merge in IHl1'.
      destruct (x1 <=? x2) eqn:Heq1, (x2 <=? x1) eqn:Heq2.
      * forwards*: String.leb_antisym Heq1 Heq2. subst.
        unfold new_leb. rewrite string_compare_refl.
        rewrite IHl1'. reflexivity.
        apply leb_iff in Heq1. apply leb_iff in Heq2.
        destruct (x1 ?= x2) eqn:Hcmp; unfold string_le in Heq1, Heq2; rewrite Hcmp in Heq1, Heq2; simpl in Heq1, Heq2; try contradiction.
        subst x2. rewrite <- IHl1'. reflexivity.
      * apply leb_iff in Heq1. apply leb_iff_conv in Heq2.
        apply ltb_iff in Heq2. rewrite Heq2. rewrite <- IHl1'. reflexivity.
      * apply leb

(* Print NOTF. *)

  (* induction l1 as [| x1 l1' IHl1']; intros l2. *)
  (* - autorewrite with merge. reflexivity. *)
  (* - destruct l2 as [| x2 l2']. *)
  (*   + simpl. reflexivity. *)
  (*   + simpl. unfold merge in IHl1'. *)
  (*     destruct (x1 <=? x2) eqn:Heq1, (x2 <=? x1) eqn:Heq2. *)
  (*     * forwards*: String.leb_antisym Heq1 Heq2. subst. *)
  (*       unfold new_leb. rewrite string_compare_refl. *)
  (*       rewrite IHl1'. reflexivity. *)
  (*       apply leb_iff in Heq1. apply leb_iff in Heq2. *)
  (*       destruct (x1 ?= x2) eqn:Hcmp; unfold string_le in Heq1, Heq2; rewrite Hcmp in Heq1, Heq2; simpl in Heq1, Heq2; try contradiction. *)
  (*       subst x2. rewrite <- IHl1'. reflexivity. *)
  (*     * apply leb_iff in Heq1. apply leb_iff_conv in Heq2. *)
  (*       apply ltb_iff in Heq2. rewrite Heq2. rewrite <- IHl1'. reflexivity. *)
  (*     * apply leb *)

(* Theorem merge_comm_with_same_head: forall (x : string) (l1 l2 : list string), *)
(*   sorted (x :: l1) -> merge l1 (x :: l2) = x :: merge l1 l2. *)
(* Proof with eauto. *)
(*   introv HS. gen l2. induction l1; intros. *)
(*   - simpl. autorewrite with merge... *)
(*   - inverts HS. forwards: IHl1. *)
(*     { inverts* H3. constructor*. eauto using leb_string_transitive. } *)
(*       case_if; autorewrite with merge. *)
(*       * forwards*: String.leb_antisym x a. subst. *)
(*       simpl. rewrite H1. reflexivity. *)
(*   - discriminate Heq. *)
(* Qed. *)

(* Theorem merge_comm_with_same_head: forall (x : string) (l1 l2 : list string), *)
(*   merge (x :: l1) (x :: l2) = merge (x :: l2) (x :: l1). *)
(* Proof. *)
(*   intros x l1 l2. *)
(*   simpl. rewrite string_leb_refl. *)
(*   rewrite string_leb_refl. *)
(*   destruct (x <=? x) eqn:Heq. *)
(*   - reflexivity. *)
(*   - apply string_leb_refl_false in Heq. contradiction. *)
(* Qed. *)


Theorem merge_comm_with_same_head: forall (x : string) (l1 l2 : list string),
  sorted (x :: l1) -> merge l1 (x :: l2) = x :: merge l1 l2.
Proof with eauto.
  introv HS. gen l2. induction l1; intros.
  - simpl. autorewrite with merge...
  - inverts HS. forwards: IHl1.
    { inverts* H3. constructor*. eauto using leb_string_transitive. }
      case_if; autorewrite with merge.
      * forwards*: String.leb_antisym x a. subst.
      simpl. rewrite H1. reflexivity.
  - discriminate Heq.
Qed.

Theorem merge_comm_with_same_head: forall (x : string) (l1 l2 : list string),
  merge (x :: l1) (x :: l2) = merge (x :: l2) (x :: l1).
Proof.
  intros x l1 l2.
  simpl. rewrite string_leb_refl.
  rewrite string_leb_refl.
  destruct (x <=? x) eqn:Heq.
  - reflexivity.
  - apply string_leb_refl_false in Heq. contradiction.
Qed.

Lemma compare_leb_relation: forall (s1 s2: string),
  (s1 <=? s2) = true <-> s1 ?= s2 <> Gt.
Proof.
  intros.
  split.
  - intros H.
    destruct (string_dec s1 s2) as [Heq|Hneq].
    + rewrite Heq. clear H Heq s1. induction* s2; simpl; intuition eauto.
      * inverts H.
      * destruct a; unfold Char.leb in H. ; simpl in H. Check ( PositiveSet.lex ).
    + apply String.lt_gt_neq. eapply String.lt_le_trans with (y := s2); eauto.
      apply String.le_neq_lt. split; assumption.
  - intros H.
    apply String.leb_le.
    destruct (string_dec s1 s2) as [Heq|Hneq].
    + rewrite Heq. apply String.eq_le_refl.
    + apply String.neq_lt_gt in Hneq.
      destruct Hneq as [Hlt | Hgt].
      * apply String.lt_le_weak. assumption.
      * contradiction.
Qed.

Lemma
#[local] Hint Resolve leb_flip : core.

merge (x :: l1) (x :: l2) = merge (x :: l2) (x :: l1).
Theorem merge_comm : forall (l1 l2 : list string),
  merge l1 l2 = merge l2 l1.
Proof.
  induction l1 as [| x1 l1' IHl1']; intros l2.
  - autorewrite with merge. reflexivity.
  - destruct l2 as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. unfold merge in IHl1'.
      destruct (x1 <=? x2) eqn:Heq1, (x2 <=? x1) eqn:Heq2.
      * apply leb_antisym in Heq1. subst x1. forwards: IHl1' l2'. reflexivity.
      * rewrite <- IHl1'. reflexivity.
      * simpl. rewrite <- IHl1'. reflexivity.
      * rewrite <- IHl1'. reflexivity.
Qed.

leb_antisym

Theorem merge_comm : forall (l1 l2 : list string),
  merge l1 l2 = merge l2 l1.
Proof.
  induction l1 as [| x1 l1' IHl1']; intros l2.
  - simpl. reflexivity.
  - destruct l2 as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. unfold merge in IHl1'.
      destruct (x1 <=?


Definition string_le (s1 s2 : string) : Prop :=
  match s1 ?= s2 with
  | Lt => True
  | Eq => True
  | Gt => False
  end.

Lemma leb_iff : forall x y : string,
  (x <=? y) = true <-> string_le x y.
Proof.
  intros. unfold string_le.
  remember (x ?= y) as Comp.
  destruct Comp...
  destruct (x ?= y).
Admitted.

Lemma leb_iff_conv : forall x y : string,
  (x <=? y) = false <-> ~(string_le x y).
Proof.
  intros. unfold string_le.
  rewrite <- not_true_iff_false, leb_iff.
Admitted.

Lemma ltb_iff : forall x y : string,
  (x <? y) = true <-> ~ string_le y x.
Proof.
  intros. unfold string_le.
Admitted.
  (* rewrite ltb_compare. now destruct (x ?= y) eqn:Heq; try rewrite <- not_true_iff_false, eqb_compare. *)
Check String.ltb_antisym.
Theorem merge_comm : forall (l1 l2 : list string),
  merge l1 l2 = merge l2 l1.
Proof.
  induction l1 as [| x1 l1' IHl1']; intros l2.
  - autorewrite with merge. reflexivity.
  - destruct l2 as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. unfold merge in IHl1'.
      destruct (x1 <=? x2) eqn:Heq1, (x2 <=? x1) eqn:Heq2.
      * apply leb_iff in Heq1. apply leb_iff in Heq2.
        destruct (x1 ?= x2) eqn:Hcmp; unfold string_le in Heq1, Heq2; rewrite Hcmp in Heq1, Heq2; simpl in Heq1, Heq2; try contradiction.
        subst x2. rewrite <- IHl1'. reflexivity.
      * apply leb_iff in Heq1. apply leb_iff_conv in Heq2.
        apply ltb_iff in Heq2. rewrite Heq2. rewrite <- IHl1'. reflexivity.
      * apply leb


Theorem merge_comm : forall (l1 l2 : list string),
  merge l1 l2 = merge l2 l1.
Proof.
  induction l1 as [| x1 l1' IHl1']; intros l2.
  - autorewrite with merge. reflexivity.
  - destruct l2 as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. unfold merge in IHl1'.
      destruct (x1 <=? x2) eqn:Heq1, (x2 <=? x1) eqn:Heq2.
      *
        rewrite leb in Heq1, Heq2.
        assert (x1 = x2) by (apply String.le_antisym; assumption).
        subst x2. rewrite <- IHl1'. reflexivity.
      * rewrite String.leb_le in Heq1. rewrite String.leb_nle in Heq2.
        assert (x1 < x2) by (apply String.le_lteq; left; assumption).
        rewrite String.ltb_lt in H. rewrite H. rewrite <- IHl1'. reflexivity.
      * rewrite String.leb_le in Heq2. rewrite String.leb_nle in Heq1.
        assert (x2 < x1) by (apply String.le_lteq; left; assumption).
        rewrite String.ltb_lt in H. rewrite H.
        destruct l1'; simpl; rewrite <- IHl1'; reflexivity.
      * rewrite String.leb_nle in Heq1, Heq2.
        assert (x1 > x2) by (apply String.lt_le_trans with x2; assumption).
        rewrite String.ltb_antisym in Heq1.
        rewrite H, Heq1. reflexivity.

Lemma merge_comm : forall l r,
    merge l r = merge r l.
Proof with eauto with bool.
  introv. gen r. induction l; intros; induction r; autorewrite with merge...
  repeat case_if...
  - remember (a ?= a0) as Comp.
    destruct Comp...
    + forwards* Heq: compare_eq_iff a a0. subst.
      forwards Heq': IHl (a0::r). rewrite Heq'.
      Restart.

  induction l as [| x1 l1' IHl1']; intros r.
  - simpl. reflexivity.
  - destruct r as [| x2 l2'].
    + simpl. reflexivity.
    + simpl. destruct (str_ltb x1 x2) eqn:Heq1, (str_ltb x2 x1) eqn:Heq2.
      * unfold str_ltb in Heq1, Heq2.
        destruct (string_dec x1 x2); destruct (string_dec x2 x1); try discriminate.
        + subst. contradiction.
        + apply String.ltb_lt in e0. apply String.ltb_lt in e1.
          exfalso. apply (String.lt_not_gt x1 x2); assumption.
      * unfold str_ltb in Heq1, Heq2.


(* } *)
Open Scope string_scope.

(* Properties of type translation *)
Lemma foldl_append_singleton_list : forall T,
    string_of_tlist (tl_list [T]) = string_of_tlist T.
Proof.
  introv. simpl. eauto.
Qed.


Lemma type2list_arrow : forall A B,
  ~ toplike B ->
  type2tlist (typ_arrow A B) = [ tl_arrow (tl_list (type2tlist A)) (tl_list (type2tlist B)) ].
Proof.
  introv NT.
  simpl. case_if. admit.
  eauto.
Admitted.

Lemma index_arrow_inv : forall A B,
    toplike B \/ || typ_arrow A B || = "(" ++ || A || ++ "->" ++ || B || ++ ")".
Proof.
  introv.
  assert (HT: toplike B \/ ~ toplike B) by admit. destruct* HT.
  - right.
    assert (check_toplike B = false) by admit.
    unfold stype2string.
    remember ("(" ++
  string_of_tlist (tl_list (type2tlist A)) ++
  "->" ++
  string_of_tlist (tl_list (type2tlist B)) ++
  ")").
    rewrite~ type2list_arrow.
Admitted.

Lemma eqIndTyp_toplike : forall A B,
    eqIndTyp A B -> toplike A <-> toplike B.
Admitted.

Lemma eqIndTyp_sound : forall A B,
    eqIndTyp A B -> ||A|| = ||B||.
Proof with eauto.
  introv HE. induction HE.
  - rewrite* IHHE1.
  - rewrite* IHHE.
  - forwards [|]: index_arrow_inv A1 B1;
    forwards [|]: index_arrow_inv A2 B2.
    admit. admit. admit.
    rewrite H. rewrite H0.
    rewrite IHHE1. rewrite* IHHE2.
    (* assert (check_toplike B1 = false) by admit. *)
    (* assert (check_toplike B2 = false) by admit. *)
  - admit.
  - assert (forall A B, || typ_and A B || = string_of_tlist (tl_list (merge (type2tlist A) (type2tlist B)))) by admit.
    rewrite H. rewrite H.
    admit.
  - admit.
  - admit.
  - admit.
  - (* no dedup yet *) admit.
Admitted.

Fixpoint Tlookup (i:string) (T:ttyp) : option ttyp :=
  match T with
  | ttyp_rcd ti At Bt => if i =? ti then Some At else Tlookup i Bt
  | _ => None
  end.

Inductive rec_typ : ttyp -> Prop :=    (* defn rec_typ *)
 | RT_Nil :
     rec_typ ttyp_top
 | RT_Rcd : forall (ll:string) (At Bt:ttyp),
     rec_typ Bt ->
     rec_typ (ttyp_rcd ll At Bt).

Inductive eqIndTypTarget : ttyp -> ttyp -> Prop :=    (* defn eqIndTypTarget *)
 | TEI_top :
     eqIndTypTarget ttyp_top ttyp_top
 | TEI_bot :
     eqIndTypTarget ttyp_bot ttyp_bot
 | TEI_base :
     eqIndTypTarget ttyp_base ttyp_base
 | TEI_arrow : forall (At1 Bt1 At2 Bt2:ttyp),
     eqIndTypTarget At1 At2 ->
     eqIndTypTarget Bt1 Bt2 ->
     eqIndTypTarget (ttyp_arrow At1 Bt1) (ttyp_arrow At2 Bt2)
 | TEI_rcd : forall (ll:string) (At Ct Bt Ct' At' Bt':ttyp),
     rec_typ Ct ->
     rec_typ Ct' ->
      (   (  Tlookup  ll   Ct  = Some  At'   /\  eqIndTypTarget At' At )    \/   Tlookup  ll   Ct  = None  )  ->
      (   (  Tlookup  ll   Ct'  = Some  Bt'   /\  eqIndTypTarget Bt' Bt )    \/   Tlookup  ll   Ct'  = None  )  ->
     eqIndTypTarget At Bt ->
     eqIndTypTarget Ct Ct' ->
     eqIndTypTarget (ttyp_rcd ll At Ct) (ttyp_rcd ll Bt Ct')
 | TEI_comm : forall (ll1:string) (At:ttyp) (ll2:string) (Bt Ct Ct' At' Bt':ttyp),
     rec_typ Ct ->
      (   (  Tlookup  ll1   Ct  = Some  At'   /\  eqIndTypTarget At' At )    \/   Tlookup  ll1   Ct  = None  )  ->
      (   (  Tlookup  ll2   Ct  = Some  Bt'   /\  eqIndTypTarget Bt' Bt )    \/   Tlookup  ll2   Ct  = None  )  ->
      ll1  <>  ll2  ->
     eqIndTypTarget (ttyp_rcd ll2 Bt  (ttyp_rcd ll1 At Ct) ) Ct' ->
     eqIndTypTarget (ttyp_rcd ll1 At  (ttyp_rcd ll2 Bt Ct) ) Ct'
 | TEI_dup : forall (ll:string) (At Bt Ct Ct' At':ttyp),
     rec_typ Ct ->
      (   (  Tlookup  ll   Ct  = Some  At'   /\  eqIndTypTarget At' At )    \/   Tlookup  ll   Ct  = None  )  ->
     eqIndTypTarget At Bt ->
     eqIndTypTarget (ttyp_rcd ll Bt  (ttyp_rcd ll At Ct) ) Ct' ->
     eqIndTypTarget (ttyp_rcd ll At  (ttyp_rcd ll Bt Ct) ) Ct'.

Lemma eqIndTyp_sound_target : forall A B,
    eqIndTyp A B -> eqIndTypTarget |[A]| |[B]|.
Proof.
  introv HE. induction HE.
  - (* trans *) admit.
  - (* symm *) admit.
  - (* arrow congurence *) admit.
  - (* rcd; needs property about eqindtyp *) admit.
  - (* list; needs property about eqindtyp *) admit.
  - (* list swap *) admit.
Admitted.

Lemma index_string_mapping : forall A B,
    || A || = || B || <-> | A | = | B |.
Proof.
  split; introv H; gen B.
  - induction A; intros; simpl in H.
    + unfolds in H. unfolds. simpl.


Lemma eqIndTyp_sound_complete : forall A B,
    eqIndTyp A B <-> |[A]| = |[B]|.
Proof with eauto.
  split. introv HE.
  - induction HE.
    + rewrite* IHHE1.
    + rewrite* IHHE.
    + simpl
Abort.



Reserved Notation " [[ A ]]" (at level 80).
Fixpoint styp2ttyplist (A: typ) : list (string * ttyp2) :=
  match A with
  | typ_top => []
  | typ_bot => [ (|A|, tt_bot) ]
  | typ_base => [ (|A|, tt_base) ]
  | typ_arrow B1 B2 => [ (|A|, tt_arrow (tt_list ([[ B1 ]]))
                                            (tt_list ([[ B2 ]]))) ]
  | typ_rcd l A' => [ (|A|, tt_arrow (tt_list []) (tt_list ([[ A' ]]))) ]
  | typ_and A1 A2 => [[ A1 ]] ++ [[ A2 ]]
  end
where "[[ A ]]" := (styp2ttyplist A).

Fixpoint ttyp2ttyp (l: list (string * ttyp2)) : ttyp :=
  match l with
  | nil => ttyp_top
  | (s, t2) :: l' => ttyp_rcd (ti_string s) (ttyp2ttyp [t2]) (ttyp2ttyp l')
  end.
