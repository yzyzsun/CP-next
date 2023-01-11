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

(* Properties of type translation *)
Definition equivalent A B := exists t1 t2 t3 t4, cosub t1 A B t2 /\ cosub t3 B A t4.


(* Notation "| A |" := (translate_type A) (at level 40). *)


Theorem elaboration_well_typed : forall G e dirflag A t,
    elaboration G e dirflag A t -> exists E T, target_typing E t T.
Abort.
