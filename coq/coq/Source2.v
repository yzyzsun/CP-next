Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.

Inductive stype : Set :=
 | st_bot : stype
 | st_base : stype
 | st_arrow (T U:stype)
 | st_rcd (l:label) (T:stype)
 | st_list (l:list stype).


Definition stype2string (A: typ) : string :=
  tlist2string (tlist_filter (type2tlist A)).

Notation "| A |" := (stype2string A) (at level 40).

Fixpoint stype2ttyplist (A: stype) : list (string * ttyp2) :=
  match A with
  | st_bot => [ (|A|, tt_bot) ]
  | st_base => [ (|A|, tt_base) ]
  | st_arrow B1 B2 => [ (|A|, tt_arrow (tt_list ([[ B1 ]]))
                                            (tt_list ([[ B2 ]]))) ]
  | st_rcd l A' => [ (|A|, tt_arrow (tt_list []) (tt_list ([[ A' ]]))) ]
  | st_list A1 A2 => [[ A1 ]] ++ [[ A2 ]]
  end
where "[[ A ]]" := (styp2ttyplist A).

(* filter toplike type out *)
Fixpoint check_toplike (T : stype) :=
  match T with
  | st_bot => false
  | st_base => false
  | st_arrow A B => check_toplike B
  | st_rcd l B => check_toplike B
  | st_list li => fold_left andb (List.map check_toplike li) true
  end.

(* Lemma check_non_toplike_sound_complete : forall A, *)
(*     toplike A <-> check_toplike A = true. *)
(* Admitted. *)


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

(* convert type to string *)
Check concat.
Check fold_left append ["A";"B"] "".

Definition check_non_toplike T := negb (check_toplike T).

(* Definition filter_toplike_list (l: list stype) := *)
(*   match (filter check_non_toplike l) with *)
(*   | nil => "Top" *)
(*   | st_list l => st_list (filter check_non_toplike (List.map toplike_filter l)) *)
(*   | st_arrow T => tl_arrow (tlist_filter T) *)
(*   | st_rcd l T => tl_rcd l (tlist_filter T) *)
(*   | _ => T *)
(*   end. *)

Fixpoint stype2string (T: stype) : string :=
  match T with
  | st_list l => fold_left append (sort (List.map stype2string (filter check_non_toplike l))) ""
  | st_arrow U T => "->" ++ stype2string T
  | st_rcd l T => "{" ++  l ++ ":" ++ stype2string T ++ "}"
  | st_bot => "Bot"
  | st_base => "Base"
  end.

(* Error: *)
(* Recursive definition of stype2string is ill-formed. *)
(* In environment *)
(* stype2string : stype -> string *)
(* T : stype *)
(* l : list stype *)
(* map : list stype -> list string *)
(* l0 : list stype *)
(* a : stype *)
(* t : list stype *)
(* Recursive call to stype2string has principal argument equal to "a" instead of *)
(* "l". *)

Fixpoint toplike_filter (T: stype) :=
  match T with
  | st_list l => st_list (filter check_non_toplike (List.map toplike_filter l))
  | st_arrow T => tl_arrow (tlist_filter T)
  | st_rcd l T => tl_rcd l (tlist_filter T)
  | _ => T
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
