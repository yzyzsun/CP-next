Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Export Infrastructure.

(* convert type to type list which allows list of types inside *)
(* to flatten intersection types *)
Inductive tlist : Set :=
 | tl_bot : tlist
 | tl_base : tlist
 | tl_arrow (T:tlist)
 | tl_rcd (l:label) (T:tlist)
 | tl_list (l:list tlist).

Definition tlist2list (T: tlist) : list tlist :=
  match T with
  | tl_list l => l
  | _ => [T]
  end.

Fixpoint type2tlist (A: typ) : tlist :=
  match A with
  | typ_top => tl_list []
  | typ_bot => tl_bot
  | typ_base => tl_base
  | typ_arrow _ A' => tl_arrow (type2tlist A')
  | typ_rcd l A' => tl_rcd l (type2tlist A')
  | typ_and A1 A2 => tl_list (tlist2list (type2tlist A1) ++ tlist2list (type2tlist A2))
  end.

(* filter toplike type out *)
Fixpoint check_toplike (T : tlist) :=
  match T with
  | tl_bot => false
  | tl_base => false
  | tl_arrow B => check_toplike B
  | tl_rcd l B => check_toplike B
  | tl_list li => fold_left andb (List.map check_toplike li) true
  end.

Lemma check_toplike_sound_complete : forall A,
    toplike A <-> check_toplike (type2tlist A) = true.
Admitted.

Fixpoint check_non_toplike (T : tlist) := negb (check_toplike T).

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

Inductive sorted : list string -> Prop :=
| sorted_nil :
  sorted []
| sorted_1 : forall (x : string),
    sorted [x]
| sorted_cons : forall (x : string) (y : string) (l : list string),
    (x <=? y = true) -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f: list string -> list string) := forall al,
    Permutation al (f al) /\ sorted (f al).

Fixpoint tlist2string (T: tlist) : string :=
  match T with
  | tl_list l => fold_left append (sort (List.map tlist2string l)) ""
  | tl_arrow T => "->" ++ tlist2string T
  | tl_rcd l T => "{" ++  l ++ ":" ++ tlist2string T ++ "}"
  | tl_bot => "Bot"
  | tl_base => "Base"
  end.

Definition stype2string (A: typ) : string :=
  tlist2string (tlist_filter (type2tlist A)).

Notation "| A |" := (stype2string A) (at level 40).

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

Fixpoint ttyp2ttyp (l: list (string * ttyp2)) : ttyp :=
  match l with
  | nil => ttyp_top
  | (s, t2) :: l' => ttyp_rcd (ti_string s) (ttyp2ttyp [t2]) (ttyp2ttyp l')
  end.
