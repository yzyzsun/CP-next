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

(* dedup => fold_left append (nodup string_dec l) "". *)
Definition list_string_2_string (l : LS) : string :=
  fold_left append l "".

Coercion list_string_2_string : LS >-> string.

(* deduped *)
Fixpoint stype2string (A: typ) : LS :=
  if (check_toplike A) then []
  else
    match A with
    | typ_top => []
    | typ_bot => [ "Bot" ]
    | typ_base => [ "Base" ]
    | typ_arrow A1 A2 => [ ( "(" ++ (stype2string A1) ++ "->" ++ (stype2string A2) ++ ")" ) ]
    | typ_rcd l A' => ["{" ++  l ++ "=>" ++ (stype2string A') ++ "}"]
    | typ_and A1 A2 => nodup string_dec (merge (stype2string A1) (stype2string A2))
    end.

Print LocallySorted.

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

(* no duplication sorted *)

Definition sorted := Sorted lex_lt.

Theorem sorted_unique : forall (l1 l2 : list string),
    sorted l1 -> sorted l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  introv HS1 HS2 HP.
  applys* Sort_In_eq lex_lt.
  applys lex_lt_trans.
  applys lex_lt_not_eq.
  split; introv HI;
    eauto using Permutation_sym, Permutation_in.
Qed.

Theorem merge_comm : forall (l1 l2 : list string),
    sorted l1 -> sorted l2 ->
    merge l1 l2 = merge l2 l1.
    (* nodup string_dec (merge l1 l2) = nodup string_dec (merge l2 l1). *)
Proof.
  introv HS1 HS2.
  applys* Sort_In_eq lex_lt.
  admit.
  applys lex_lt_not_eq.
  admit. admit.
  admit.
  (* - lets HP: Permuted_merge. *)
  (*   split; introv HI; applys nodup_In; apply nodup_In in HI; *)
  (*     applys Permutation_in HP. *)
  (*   all: applys in_app_iff; applys or_comm; applys in_app_iff. *)
  (*   all: applys Permutation_in HI; applys* Permutation_sym HP. *)
Admitted.

(* Search Sorted. *)
(* Admitted. *)
(*   Search Permutation. *)
(*   admit. admit. *)
(*   - lets HP: Permuted_merge. *)
(*     split; introv HI; applys nodup_In; apply nodup_In in HI; *)
(*       applys Permutation_in HP. *)
(*     all: applys in_app_iff; applys or_comm; applys in_app_iff. *)
(*     all: applys Permutation_in HI; applys* Permutation_sym HP. *)
(* Admitted. *)

(*     nodup string_dec (merge l1 l2) = nodup string_dec (merge l3 ++ l4). *)

Check Sorted_merge.

Lemma In_merge : forall y l r,
    In y (merge l r) <-> In y l \/ In y r.
Proof.
Admitted.

(* Lemma HdRel_lt : forall a y l, *)
(*     HdRel lex_lt a l -> In y l -> lex_lt a y. *)
(* Proof with eauto with bool. *)
(*   introv HR HI. gen a y. induction l; intros... *)
(*   - inverts HI. *)
(*   - Print HdRel. inverts HR. forwards: IHl H0. inverts HI. Print HdRel. *)
(*   applys* SortA_InfA_InA l. 4: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. *)

Lemma HdRel_nodup : forall a l,
    Sorted NOTF.le l -> HdRel lex_lt a l -> HdRel lex_lt a (nodup string_dec l).
Proof with eauto.
  introv HS HR.
  applys In_InfA. introv HI. apply nodup_In in HI.
  induction l.
  - inverts HI.
  - apply in_inv in HI. destruct HI.
    + subst*. inverts* HR.
    + inverts HS. inverts HR.
      forwards*: IHl.
      inverts* H3. constructor.
      destruct H0. now applys* lex_lt_trans.
      now subst*.
Qed.

Lemma le_trans : forall s0 s1 s2 : string, NOTF.le s0 s1 -> NOTF.le s1 s2 -> NOTF.le s0 s2.
Admitted.

Lemma HdRel_nodup_le : forall a l,
    Sorted NOTF.le l -> HdRel NOTF.le a l -> HdRel lex_lt a (nodup string_dec l).
Proof with eauto.
  introv HS HR. gen a. induction l; intros.
  - simpl...
  - inverts HS. inverts HR.
    simpl. case_if*.
    + applys* IHl.
      inverts* H2. constructor...
      eauto using le_trans.
    + constructor...
Abort. (* incorrect: a may be in l *)
Check lex_lt_trans.  Check NTTLB.leb_trans.

Lemma sorted_nodup_aux : forall l,
    sorted (nodup string_dec l) -> Sorted NOTF.le l.
Abort. (* incorrect *)

Lemma sorted_nodup : forall l,
    Sorted NOTF.le l -> sorted (nodup string_dec l).
Proof with eauto.
  introv HS. induction* l.
  - simpl... econstructor...
  - inverts HS. forwards*: IHl.
    simpl. case_if.
    + apply H.
    + econstructor... destruct l...
      * simpl...
      * applys* HdRel_nodup.
        inverts H2. inverts* H3.
        exfalso. applys C. applys in_eq.
Qed.

(* Lemma HdRel_nodup : forall a l, *)
(*         HdRel NOTF.le a l -> In b l -> lex_lt a b. *)
(*         Search (Sorted). *)
(*         inverts H2. inverts H3. econstructor. *)
(*     fold nodup. *)
(*     ; econstructor. *)
(*     + forwards: IHl HS. constructor*. *)
(*       clear HS IHl. *)
(*       induction* l. *)
(*       apply in_inv in C. destruct C. *)
(*       * subst*. constructor*. right*. *)
(*       * constructor. inverts H. *)
(*         Search Sorted. *)


(*         Search HdRel. applys* IHl. *)


(*       Search (Sorted _ _ -> HdRel _ _ _). *)

(*        HS : Sorted NOTF.le l *)
(*   HR : HdRel lex_lt a l *)
(*   y : string *)
(*   HI : In y l *)
(*   ============================ *)
(*   lex_lt a y *)


(*       Search (Sorted). *)

Lemma HdRel_relax : forall a l,
    HdRel lex_lt a l -> HdRel NOTF.le a l.
Proof with eauto.
  introv HS. induction* HS. constructor...
  left*.
Qed.

Lemma sorted_relax : forall l,
    sorted l -> Sorted NOTF.le l.
Proof with eauto.
  introv HS. induction* HS.
  destruct H... constructor... constructor...
  left*.
Qed.

#[local] Hint Constructors Sorted HdRel : core.
#[local] Hint Resolve HdRel_relax sorted_relax : core.

Lemma test : forall a l r,
    HdRel NOTF.le a l -> HdRel NOTF.le a r -> HdRel NOTF.le a (merge l r).
Admitted.

Lemma merge_sorted : forall l r,
    sorted l -> sorted r -> Sorted NOTF.le (merge l r).
Proof with eauto using sorted_relax.
  introv HSl HSr. gen r.
  induction HSl; intros; autorewrite with merge...
  - induction HSr...
    + autorewrite with merge.
      constructor...
    + destruct (string_compare_lex a a0) eqn:HE. destruct c.
      * subst*. simpl. rewrite HE. simpl...
        econstructor. applys IHHSl...
        econstructor... applys test...
        econstructor... right*.
      * simpl. rewrite HE. simpl...
        forwards* IH: IHHSl (a0 :: l0)...
        all: econstructor...
        applys test...
      * simpl. rewrite HE. simpl...
        econstructor... applys test (a :: l) l0...
Qed.

Lemma merge_sorted_dedup: forall l r,
    sorted l -> sorted r -> sorted (nodup string_dec (merge l r)).
Proof with eauto using sorted_nodup, sorted_relax.
  introv HSl HSr.
  forwards: merge_sorted HSl HSr...
Qed.
(*   induction HSl; intros; autorewrite with merge... *)
(*   - induction HSr... *)
(*     + autorewrite with merge. simpl. case_if... *)
(*       constructor... applys sorted_nodup... *)
(*       applys HdRel_nodup... *)
(*     + forwards* IH: IHHSl (a0 :: l0)... *)
(*       econstructor... *)
(*       simpl. case_if... simpl. case_if... *)
(*       econstructor... applys HdRel_nodup... *)


(*       econstructor... *)
(*     + simpl. case_if*. *)
(*       constructor*. applys* HdRel_nodup. applys* sorted_relax. *)
(*   - induction HSr... *)
(*     + autorewrite with merge. simpl. case_if... *)
(* eauto using sorted_nodup *)
(*     + autorewrite with merge. repeat case_if... *)
(*       fold nodup.sorted_relax applys* SortA_InfA_InA. *)
(*       sorted (nodup *)
(*       autorewrite with merge. *)
(*       constructor. *)
(*     + forwards* HSP: IHHSl l0. *)
(*       autorewrite with merge. case_if... *)
(*       * case_if in C. forwards* HSP': IHHSl (a0 :: l0). *)
(*         all: constructor... *)
(*         applys In_InfA. introv HI. forwards [HI'|HI']: In_merge HI. *)
(*         ** applys* SortA_InfA_InA l. 4: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. *)
(*         ** applys* SortA_InfA_InA (a0 :: l0). 5: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. constructor... *)
(*            Search (Proper (eq ==> eq ==> iff) lex_lt). *)
(*         eauto. *)
(*         Search (InA). *)
(*         Search Sorted. *)
(*         lets: InfA_app. *)
(*         Search HdRel. SortA_InfA_InA. *)
(*         case_if... *)
(*       * case_if... *)
(*         ** lets* HSP: IHHSl (y0 :: l0). forwards*: HSP. *)
(*            case_if... *)
(*         ** simpl in IHHSr. case_if... *)
(* Qed. *)


(* Theorem merge_comm : forall (l1 l2 : list string), *)
(*   Sorted lex_lt l1 -> Sorted lex_lt l2 -> merge l1 l2 = merge l2 l1. *)
(* Proof. *)
(*   introv HS1 HS2. *)
(*   lets: SortA_equivlistA_eqlistA. *)
(*   Print StrictOrder. *)

(*   Search (Sorted). *)
(*   Search (lex_lt). *)
(*   pose proof NTTLB.leb_trans. unfold Transitive in H. Print NOTF. Search le. *)
(*   assert (forall x y, proj1_sig (string_compare_lex x y) = Lt -> *)
(*                       lex_lt x y). eauto. *)
(*   pose proof NOTF.compare_spec. intros. forwards: H0 x y. *)
(*   destruct H2; try discriminate. eauto. *)
(*   intros. destruct H1. destruct H2. Search NTTLB.leb. *)
(*   Search CompareSpec. *)
(*   NTTLB.leb_le: *)
(*   forall x y : string, *)
(*   is_true (NTTLB.leb x y) <-> (fun x0 y0 : string => lex_lt x0 y0 \/ x0 = y0) x y *)
(* Admitted. *)

(* } *)
Open Scope string_scope.

(* Properties of type translation *)
Lemma foldl_append_singleton_list : forall T,
    list_string_2_string [T] = T.
Proof.
  introv. simpl. eauto.
Qed.

Lemma type2list_arrow : forall A B,
  ~ toplike B ->
  stype2string (typ_arrow A B) = [ ( "(" ++ (stype2string A) ++ "->" ++ (stype2string B) ++ ")" ) ].
Proof.
  introv NT.
  simpl. case_if*. apply check_toplike_sound_complete in C. intuition eauto.
Qed.

Lemma index_arrow_inv : forall A B,
    toplike B \/ || typ_arrow A B || = [ "(" ++ || A || ++ "->" ++ || B || ++ ")" ].
Proof.
  introv. destruct (check_toplike B) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma index_rcd_inv : forall l A,
    toplike A \/ || typ_rcd l A || = [ "{" ++  l ++ "=>" ++ || A || ++ "}" ].
Proof.
  introv. destruct (check_toplike A) eqn:HE.
  { left. applys* check_toplike_sound_complete. }
  right. unfolds. simpl. case_if*.
Qed.

Lemma stype2string_toplike : forall A,
    toplike A -> || A || = [].
Proof with eauto.
  introv HT. apply check_toplike_sound_complete in HT.
  destruct A; simpl in HT; try discriminate; simpl...
  all: rewrite* HT.
Qed.

Lemma stype2string_and : forall A B : typ,
    || typ_and A B || = nodup string_dec (merge (stype2string A) (stype2string B)).
Proof.
  introv. simpl.
  destruct (check_toplike A) eqn:HA. destruct (check_toplike B) eqn:HB.
  all: try apply check_toplike_sound_complete in HA.
  all: try apply check_toplike_sound_complete in HB.
  all: try ( rewrite (stype2string_toplike A); [ | eassumption] ).
  all: try ( rewrite (stype2string_toplike B); [ | eassumption] ).
  all: autorewrite with merge; simpl; eauto.
Qed.


Lemma eqIndTyp_toplike : forall A B,
    eqIndTyp A B -> toplike A <-> toplike B.
Proof with eauto.
  introv HE. induction* HE.
  all: try solve [split; intro H; intuition eauto].
  all: try solve [split; intro H; econstructor; inverts H; intuition eauto].
  all: try solve [split; intro H; econstructor; inverts H; try inverts H3; try inverts H2; intuition eauto].
  all: try solve [split; intro H'; eauto; inverts H'; intuition eauto].
Qed.

(* Lemma test : forall A B, *)
(*     ||A|| = ||B|| -> type2tlist A = type2tlist B. *)
(* Proof with intuition eauto. *)
(*   introv HE. unfold stype2string in HE. rewrite HE. *)
Lemma typeindex_sorted: forall A,
    sorted (|| A ||).
Proof with eauto.
  introv. induction* A; simpl...
  all: unfolds...
  all: try econstructor...
  - case_if...
    econstructor...
  - case_if... applys* merge_sorted_dedup.
  - case_if...
    econstructor...
Qed.

Lemma typeindex_nodup: forall A,
    NoDup (|| A ||).
Proof with eauto.
  introv. induction* A; simpl...
Admitted.

 Lemma merge_double_nodup : forall l,
     nodup string_dec (merge l l) = nodup string_dec l.
 Admitted.

 Lemma typeindex_nodup_elim : forall A,
     nodup string_dec (|| A ||) = || A ||.
Proof with eauto.
  introv. applys nodup_fixed_point. applys typeindex_nodup.
Qed.

#[local] Hint Rewrite typeindex_nodup_elim : merge.
#[local] Hint Resolve typeindex_sorted : core.

Lemma eqIndTyp_sound : forall A B,
    eqIndTyp A B -> || A || = || B ||.
Proof with eauto using typeindex_nodup, NoDup_nodup, merge_sorted_dedup.
  introv HE. induction* HE.
  - rewrite* IHHE1.
  - lets [|]: index_arrow_inv A1 B1;
      lets [|]: index_arrow_inv A2 B2.
    2: forwards (HT2&?): eqIndTyp_toplike HE2;
       forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE2;
       forwards H': HT2 H0.
    1-3: repeat rewrite stype2string_toplike...
    rewrite H; rewrite H0; rewrite IHHE1; rewrite IHHE2...
  - lets [|]: index_rcd_inv A;
      lets [|]: index_rcd_inv B.
    2: forwards (HT2&?): eqIndTyp_toplike HE;
    forwards H': HT2 H.
    3: forwards (?&HT2): eqIndTyp_toplike HE;
    forwards H': HT2 H0.
    1-3: repeat rewrite stype2string_toplike...
    rewrite H; rewrite H0; rewrite IHHE...
  - repeat rewrite stype2string_and. rewrite IHHE...
  - repeat rewrite stype2string_and. rewrite* merge_comm.
  - repeat rewrite stype2string_and.
    applys sorted_unique...
    applys* NoDup_Permutation... split; introv HI.
    all: apply nodup_In; applys In_merge.
    all: repeat apply nodup_In in HI; try apply In_merge in HI.
    all: intuition eauto; repeat apply nodup_In in H; try apply In_merge in H; intuition eauto.
    1-2: left; apply nodup_In; applys In_merge...
    1-2: right; apply nodup_In; applys In_merge...
  - rewrite stype2string_toplike...
  - rewrite stype2string_and. rewrite stype2string_toplike...
    autorewrite with merge...
  - applys sorted_unique...
    repeat rewrite stype2string_and.
    rewrite IHHE.
    applys* NoDup_Permutation... split; introv HI.
    + rewrite* merge_double_nodup in HI.
      rewrite* typeindex_nodup_elim in HI.
    + rewrite* merge_double_nodup.
      rewrite* typeindex_nodup_elim.
      Unshelve. eauto.
Qed.

Lemma nodup_empty_inv : forall l,
    nodup string_dec l = [] -> l = [].
Proof.
  introv HE. induction* l.
  simpl in HE. case_if.
  exfalso. forwards~: IHl. subst. inverts C.
Qed.

Lemma merge_empty_inv : forall l r,
    merge l r = [] -> l = [] /\ r = [].
Proof.
  introv HE. destruct* l; destruct* r.
  simpl in HE. case_if.
Qed.

Lemma stype2string_toplike_complete : forall A,
    || A || = [] -> toplike A.
Proof with eauto.
  introv HT. apply check_toplike_sound_complete.
  induction A; simpl in HT; try discriminate; try case_if; simpl...
  apply nodup_empty_inv in HT.
  forwards (?&?): merge_empty_inv HT.
  forwards~: IHA1. forwards~: IHA2. rewrite H1. rewrite* H2.
Qed.

Lemma stype2string_single_and_inv : forall a A B,
    [ a ] = || typ_and A B || -> ([ a ] = || A || \/ [ a ] = || B ||) /\ ([ ] = || A || \/ [ ] = || B ||).
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE.
  rewrite stype2string_and in HE. gen a B.
  induction (|| A ||); intros.
  - autorewrite with merge in HE...
  - Search nodup. induction (|| B ||).
    + autorewrite with merge in HE...
Admitted.

Lemma eqIndTyp_complete : forall A B,
    || A || = || B || -> eqIndTyp A B.
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HE. gen B.
  induction A; intros.
  - forwards*: stype2string_toplike_complete B...
  - simpl in HE. induction B...
    all: try solve [simpl in HE; try case_if; try discriminate].
    forwards ([|]&[|]): stype2string_single_and_inv HE.
    all: try forwards: IHB1 H. all: try forwards: IHB1 H0.
    admit.
    forwards*: stype2string_toplike_complete B2...
    applys EI_trans H1. applys EI_trans EI_comm.
    applys EI_trans EI_and. applys EI_symm EI_topelim.
    applys* EI_symm EI_top.
    admit. admit.
  - admit.
  - admit.
  - (* and case ??? : 1)either toplike 2) destruct B || normalize *) admit.
  - admit.
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
     eqIndTypTarget (ttyp_rcd ll1 At  (ttyp_rcd ll2 Bt Ct) ) Ct'.


Lemma eqIndTyp_sound_target : forall A B,
    eqIndTyp A B -> eqIndTypTarget |[A]| |[B]|.
Proof.
  introv HE. induction HE.
  - (* refl *) admit.
  - (* trans *) admit.
  - (* symm *) admit.
  - (* arrow congurence *) admit.
  - (* rcd; needs property about eqindtyp *)
    simpl. case_if; case_if. 1-3: admit.
    admit.
  - (* list; needs property about eqindtyp ? *)
    simpl. admit.
  - (* list swap ? *) admit.
  - (* assoc *) admit.
  - apply check_toplike_sound_complete in H.
    simpl. (* toplike |[ A ]| ttyp_top *) admit.
  - admit.
  - (* double *) admit.
Admitted.

after deduplication is the same permutation

  flattern a tree to a list?

  generate sets from list / tree?


  f (A & B) = f(C)

                f(A) = f(B) --> |[ A ]| ~ |[ B ]|

  label->type


           (A & B) & C

        \y. ( \x. (\r. A | r) (\r. B | r) x ) ((\r.C|r) y)
