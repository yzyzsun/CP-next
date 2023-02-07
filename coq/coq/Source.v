Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.

(* convert type to type list which allows list of types inside *)
Inductive tlist : Set :=
 | tl_top : tlist
 | tl_bot : tlist
 | tl_base : tlist
 | tl_arrow (T:tlist)
 | tl_rcd (l:label) (T:tlist)
 | tl_list (l:list tlist).

(* (* convert type to a list of string is infeasible because there will be nested list *) *)
(* Fixpoint type2stringlist (A: typ) : list string := *)
(*   match A with *)
(*   | typ_top => ["Top"] *)
(*   | typ_bot => ["Bot"] *)
(*   | typ_base => ["Base"] *)
(*   | typ_arrow _ A' =>  ["->" ++ type2stringlist A'] *)
(*   | typ_rcd l A' => ["{" ++  l ++ ":" ++  type2string A' ++ "}"] *)
(*   | typ_and A1 A2 => (type2stringlist A1) ++ (type2stringlist A2) *)
(*   end. *)

Definition tlist2list (T: tlist) : list tlist :=
  match T with
  | tl_list l => l
  | _ => [T]
  end.

Fixpoint type2tlist (A: typ) : tlist :=
  match A with
  | typ_top => tl_top
  | typ_bot => tl_bot
  | typ_base => tl_base
  | typ_arrow _ A' => tl_arrow (type2tlist A')
  | typ_rcd l A' => tl_rcd l (type2tlist A')
  | typ_and A1 A2 => tl_list (tlist2list (type2tlist A1) ++ tlist2list (type2tlist A2))
  end.

(* (* flatten nested intersection types *) *)
(* Fixpoint flatten (A : typ) := *)
(*   match A with *)
(*   | typ_and A1 A2 => flatten A1 ++ flatten A2 *)
(*   | _ => [A] *)
(*   end. *)

(* (* filter toplike type out *) *)
(* Fixpoint check_non_toplike (A : typ) := true. *)
(* Lemma check_non_toplike_sound_complete : forall A, *)
(*     toplike A <-> check_non_toplike A = false. *)
(* Admitted. *)
(* Check (filter check_non_toplike). *)

(* (* FAILED TO COMPILE *) *)
(* (* convert type to string *) *)
(* Fixpoint type2string (A: typ) : string := *)
(*   match A with *)
(*   | typ_top => "Top" *)
(*   | typ_bot => "Bot" *)
(*   | typ_base => "Base" *)
(*   | typ_arrow _ A' =>  "->" ++ type2string A' *)
(*   | typ_rcd l A' => "{" ++  l ++ ":" ++  type2string A' ++ "}" *)
(*   | typ_and _ _ => fold_left append (sort (List.map type2string (filter check_non_toplike (flatten A)))) "" *)
(*   end. *)

(* filter toplike type out *)
Fixpoint check_non_toplike (T : tlist) := true.
Lemma check_non_toplike_sound_complete : forall A,
    toplike A <-> check_non_toplike (type2tlist A) = false.
Admitted.

Fixpoint tlist_filter (T: tlist) :=
  match T with
  | tl_list l => tl_list (filter check_non_toplike (List.map tlist_filter l))
  | tl_arrow T => tl_arrow (tlist_filter T)
  | tl_rcd l T => tl_rcd l (tlist_filter T)
  | _ => T
  end.

(* sort strings *)
(* TODO add deduplication *)
Check ("A" <=? "C").
Fixpoint insert (i : string) (l : list string) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
 end.

Fixpoint sort (l : list string) : list string :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_example :
  sort ["Base";"->Base";"{Base}"]
  = ["->Base"; "Base"; "{Base}"].
simpl. auto.
Qed.

Compute insert "Base" ["->Base";"{Base}"].

Inductive sorted : list string -> Prop :=
| sorted_nil :
  sorted []
| sorted_1 : forall (x : string),
    sorted [x]
| sorted_cons : forall (x : string) (y : string) (l : list string),
    (x <=? y = true) -> sorted (y :: l) -> sorted (x :: y :: l).

Check Permutation.
(* Check (LocallySorted (x <=? y = true)). *)

Definition is_a_sorting_algorithm (f: list string -> list string) := forall al,
    Permutation al (f al) /\ sorted (f al).

(* convert tlist to string *)
Check concat.
Check fold_left append ["A";"B"] "".

Fixpoint tlist2string (T: tlist) : string :=
  match T with
  | tl_list l => fold_left append (sort (List.map tlist2string l)) ""
  | tl_arrow T => "->" ++ tlist2string T
  | tl_rcd l T => "{" ++  l ++ ":" ++ tlist2string T ++ "}"
  | tl_top => "Top"
  | tl_bot => "Bot"
  | tl_base => "Base"
  end.

Definition stype2string (A: typ) : string :=
  tlist2string (tlist_filter (type2tlist A)).

Notation "| A |" := (stype2string A) (at level 40).

(* Properties of type translation *)
(** filter toplike, sort, deduplicate *)
Lemma eqIndTyp_sound_complete : forall A B,
    eqIndTyp A B <-> |A| = |B|.
Abort.

Definition equivalent A B := exists t1 t2 t3 t4, cosub t1 A B t2 /\ cosub t3 B A t4.

(** NOT TRUE **)
Lemma eqIndTyp_equivalent : forall A B,
    eqIndTyp A B -> equivalent A B.
Abort.
(** A1->B VS A2->B **)

(** NOT TRUE **)
Lemma equivalent_eqIndTyp : forall A B,
    equivalent A B -> eqIndTyp A B.
Abort.
(** A->B&C VS (A->B)&(A->C) **)

Definition eq_disjoint A B := forall C, disjoint A C <-> disjoint B C.

(** NOT TRUE **)
Lemma eqIndTyp_eq_disjoint : forall A B,
    eqIndTyp A B -> eq_disjoint A B.
Abort.
(** with the same example above *)

Lemma disjoint_type_no_eqInd : forall A B,
    eqIndTyp A B -> disjoint A B -> False.
Abort.

(* Translate source type to target type *)
Inductive ttyp2 : Set :=
(* | tt_top : ttyp2 (* tt_rcd [] *) *)
| tt_bot : ttyp2
| tt_base : ttyp2
| tt_arrow (T1:ttyp2) (T2:ttyp2)
| tt_list (l:list (string * ttyp2))
.

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

(* Type safety *)
(** The key is to prove the lookup label does exists in the record *)
(** To prove type safety, we need to translate typing contexts / types
 \ x : A . e : B  => A->B ~> \ x . |e| ??? **)

Lemma cosub_well_typed : forall E t1 A B t2,
    cosub t1 A B t2 -> target_typing E t1 [[A]] -> target_typing E t2 [[B]] .
Abort.
(* t1 is not always well-typed *)


(** via styp2ttyp to convert type *)
Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t -> exists E T, target_typing E t T.
Abort.
