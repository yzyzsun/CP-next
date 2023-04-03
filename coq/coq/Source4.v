Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Require Import StructTact.StringOrders.
(* Require Import StructTact.StructTactics. *)
Import IfNotations.
Require Export Infrastructure.

(* sort on strings *)
Print OTF_to_TTLB.
Print String_as_OT.
Print string_lex_as_OT.

Module NOTF := OT_to_Full string_lex_as_OT.
Module NTTLB := OTF_to_TTLB NOTF.
Module Import NSort := Sort NTTLB.

Compute merge ["A"; "E"] ["C"].
Check Sorted_merge.
Check Permuted_sort.
(* } *)

(* convert type to type list which allows list of types inside *)
(* to flatten intersection types *)
Inductive tlist : Set :=
 | tl_bot : tlist
 | tl_base : tlist
 | tl_arrow (U:tlist) (T:tlist)
 | tl_rcd (l:label) (T:tlist)
 | tl_list (l:list tlist).

Fixpoint string_of_tlist (T: tlist) : string :=
  match T with
  | tl_list l => fold_left append (List.map string_of_tlist l) ""
  | tl_arrow U T => "(" ++ string_of_tlist U ++ "->" ++ string_of_tlist T ++ ")"
  | tl_rcd l T => "{" ++  l ++ "=>" ++ string_of_tlist T ++ "}"
  | tl_bot => "Bot"
  | tl_base => "Base"
  end.

Coercion string_of_tlist : tlist >-> string.

Check string_lex_as_OT.compare.
Check ("A" <=? "B").
Check ("A" =? "B").
Check ("A" ?= "B").

Fixpoint check_toplike (A : typ) :=
  match A with
  | typ_top => true
  | typ_bot => false
  | typ_base => false
  | typ_arrow _ B => check_toplike B
  | typ_rcd l B => check_toplike B
  | typ_and A B => (check_toplike A) && (check_toplike B)
  end.

Lemma check_toplike_sound_complete : forall A,
    toplike A <-> check_toplike A = true.
Proof.
  split; introv HT.
  - induction HT; simple*.
    rewrite IHHT1. rewrite* IHHT2.
  - induction* A.
    all: simpl in HT; try discriminate.
    forwards* (?&?): andb_prop_elim (check_toplike A1) (check_toplike A2).
    eauto with bool.
    constructor; intuition eauto using Is_true_eq_true.
Qed.


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

Print LocallySorted.

Definition stype2string (A: typ) : string := type2tlist A.
Compute stype2string (typ_and (typ_and typ_base typ_base) typ_bot).
Compute stype2string (typ_and (typ_and typ_bot typ_base) typ_base).
Compute stype2string (typ_arrow (typ_and (typ_and typ_bot typ_base) typ_base) typ_bot).

Notation "|| A ||" := (stype2string A) (at level 50, A at next level). (* 1 is too high *)
(* -------------------------------------------------------------------------- *)

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
    merge (a::l) (b::r) =
      if if proj1_sig (string_compare_lex a b) is Gt then false else true then a :: merge l (b::r) else b :: merge (a::l) r.
Proof with eauto.
  introv. induction* l; destruct (proj1_sig (string_compare_lex a b)); autorewrite with merge...
Qed.

#[local] Hint Rewrite merge_cons : merge.


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

Print NOTF.
Print string_lex_as_OT.
Check NOTF.lt_strorder.

Require Import Ascii.
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

Check NTTLB.leb_trans.
(* Lemma new_leb_string_transitive : forall s1 s2 s3 : string, *)
(*   (s1 <=? s2) = true -> (s2 <=? s3) = true -> (s1 <=? s3) = true. *)
(* Proof. *)
(*   intros s1 s2 s3 H1 H2. *)
(*   pose proof NTTLB.leb_trans. unfolds in H. applys H. *)
(*   unfolds. unfolds in H1. unfolds in H2. *)
(*   destruct (s1 ?= s2) eqn:E1; try discriminate; *)
(*     destruct (s2 ?= s3) eqn:E2; try discriminate. *)
(*   all: try apply String_as_OT.cmp_eq in E1. *)
(*   all: try apply String_as_OT.cmp_eq in E2. *)
(*   all: subst*. *)
(*   1: now rewrite* string_compare_refl. *)
(*   1: now rewrite* E2. *)
(*   1: now rewrite* E1. *)
(*   Print NTTLB. *)
(*   forwards: NTTLB.lt_trans s1 s2 s3. *)
(*   unfolds. *)
(*   all: try apply String_as_OT.cmp_lt in E1. *)
(*   all: try apply String_as_OT.cmp_lt in E2. *)
(*   all: try forwards H: String_as_OT.lt_trans E1 E2. *)
(*   all: try rewrite <- String_as_OT.cmp_lt in H. *)
(*   1: rewrite* H; simpl. *)

(* Qed. *)

Theorem merge_comm : forall (l1 l2 : list string),
  Sorted NOTF.le l1 -> Sorted NOTF.le l2 -> merge l1 l2 = merge l2 l1.
Proof.
  introv HS1 HS2.
  applys* Sort_In_eq NOTF.le.
  pose proof NTTLB.leb_trans.
  pose proof NOTF.compare_spec.
Admitted.

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
  type2tlist (typ_arrow A B) = [ ( "(" ++ (type2tlist A) ++ "->" ++ (type2tlist B) ++ ")" ) ].
Proof.
  introv NT.
  simpl. case_if*. apply check_toplike_sound_complete in C. intuition eauto.
Qed.

Lemma index_arrow_inv : forall A B,
    toplike B \/ || typ_arrow A B || = "(" ++ || A || ++ "->" ++ || B || ++ ")".
Proof.
  introv. destruct (check_toplike B) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma index_rcd_inv : forall l A,
    toplike A \/ || typ_rcd l A || = "{" ++  l ++ "=>" ++ || A || ++ "}".
Proof.
  introv. destruct (check_toplike A) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma type2list_toplike : forall A,
    toplike A -> || A || = "".
Proof with eauto.
  introv HT. apply check_toplike_sound_complete in HT.
  destruct A; simpl in HT; try discriminate; simpl...
  - unfolds. unfolds. unfolds. simpl. rewrite* HT.
  - unfolds. unfolds. unfolds. simpl. rewrite* HT.
  - unfolds. unfolds. unfolds. simpl. rewrite* HT.
Qed.

Lemma type2list_and : forall A B : typ,
    || typ_and A B || = list_string_2_string (merge (type2tlist A) (type2tlist B)).

Admitted.

Lemma eqIndTyp_toplike : forall A B,
    eqIndTyp A B -> toplike A <-> toplike B.
Proof with eauto.
  introv HE. induction* HE.
  - split; intro H; intuition eauto.
  - split; intro H; intuition eauto.
  - split; intro H; econstructor; inverts H; intuition eauto.
  - split; intro H; econstructor; inverts H; intuition eauto.
  - split; intro H; econstructor; inverts H; intuition eauto.
  - split; intro H; econstructor; inverts H; intuition eauto.
  - split; intro H; econstructor; inverts H; try inverts H3; try inverts H2;
      intuition eauto.
  - split; intro H'; eauto; inverts H'; intuition eauto.
  - split; intro H; econstructor; inverts H; try inverts H3; try inverts H2;
      intuition eauto.
Qed.

(* Lemma test : forall A B, *)
(*     ||A|| = ||B|| -> type2tlist A = type2tlist B. *)
(* Proof with intuition eauto. *)
(*   introv HE. unfold stype2string in HE. rewrite HE. *)

Lemma eqIndTyp_sound : forall A B,
    eqIndTyp A B -> type2tlist A = type2tlist B.
Proof with eauto.
  introv HE. induction HE.
  - rewrite* IHHE1.
  - rewrite* IHHE.
  - forwards [|]: index_arrow_inv A1 B1;
      forwards [|]: index_arrow_inv A2 B2.
    2: forwards (HT2&?): eqIndTyp_toplike HE2;
       forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE2;
       forwards H': HT2 H0.
    1-3: repeat rewrite type2list_toplike...
    rewrite H; rewrite H0; rewrite IHHE1; rewrite IHHE2...
  - forwards [|]: index_rcd_inv A;
      forwards [|]: index_rcd_inv B.
    2: forwards (HT2&?): eqIndTyp_toplike HE;
    forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE;
    forwards H': HT2 H0.
    1-3: repeat rewrite type2list_toplike...
    rewrite H; rewrite H0; rewrite IHHE...
  - repeat rewrite type2list_and. rewrite IHHE...
    assert (forall A B, || typ_and A B || = list_string_2_string (merge (type2tlist A) (type2tlist B)) ) by admit.
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
