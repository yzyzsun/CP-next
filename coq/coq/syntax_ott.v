Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import List LibTactics Lia.

(* generated by Ott 0.33, locally-nameless lngen from: ../spec/rules.ott ../spec/target.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition lit : Set := nat.
Definition label : Set := string.

Inductive tindex : Set :=  (*r type index *)
 | ti_bot : tindex (*r bottom type *)
 | ti_base : tindex (*r base type *)
 | ti_arrow (A:tindex) (B:tindex) (*r function types *)
 | ti_rcd (l:label) (A:tindex) (*r record *)
 | ti_list (a:list tindex).

Section tindex_ind'.

  Variable P : tindex -> Prop.

  Hypothesis ti_bot_case : P ti_bot.

  Hypothesis ti_base_case : P ti_base.

  Hypothesis ti_arrow_case : forall (ti1 ti2 : tindex),
      P ti1 -> P ti2 -> P (ti_arrow ti1 ti2).

  Hypothesis ti_rcd_case : forall (l : label) (ti : tindex),
      P ti -> P (ti_rcd l ti).

  Hypothesis ti_list_case : forall (ls : list tindex),
      Forall P ls -> P (ti_list ls).

  Fixpoint tindex_ind' (ti : tindex) : P ti :=
    match ti with
    | ti_bot => ti_bot_case
    | ti_base => ti_base_case
    | ti_arrow ti1 ti2 => ti_arrow_case ti1 ti2 (tindex_ind' ti1) (tindex_ind' ti2)
    | ti_rcd l ti => ti_rcd_case l ti (tindex_ind' ti)
    | ti_list ls => ti_list_case ls
                      ((fix list_ti_list_ind (ls : list tindex) : Forall P ls :=
                          match ls with
                          | nil => Forall_nil _
                          | cons ti ls => Forall_cons _ (tindex_ind' ti) (list_ti_list_ind ls)
                          end) ls)
    end.

End tindex_ind'.

Section All.
  Variable T : Set.
  Variable P : T -> Set.

  Fixpoint All (ls : list T) : Set :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

Section tindex_rec'.

  Variable P : tindex -> Set.

  Hypothesis ti_bot_case : P ti_bot.

  Hypothesis ti_base_case : P ti_base.

  Hypothesis ti_arrow_case : forall (ti1 ti2 : tindex),
      P ti1 -> P ti2 -> P (ti_arrow ti1 ti2).

  Hypothesis ti_rcd_case : forall (l : label) (ti : tindex),
      P ti -> P (ti_rcd l ti).
  Search (list).

  Hypothesis ti_list_case : forall (ls : list tindex),
      Forall P ls -> P (ti_list ls).

  Fixpoint tindex_rec' (ti : tindex) : P ti :=
    match ti with
    | ti_bot => ti_bot_case
    | ti_base => ti_base_case
    | ti_arrow ti1 ti2 => ti_arrow_case ti1 ti2 (tindex_rec' ti1) (tindex_rec' ti2)
    | ti_rcd l ti => ti_rcd_case l ti (tindex_rec' ti)
    | ti_list ls => ti_list_case ls
                      ((fix list_ti_list_ind (ls : list tindex) : Forall P ls :=
                          match ls with
                          | nil => Forall_nil _
                          | cons ti ls => Forall_cons _ (tindex_rec' ti) (list_ti_list_ind ls)
                          end) ls)
    end.

End tindex_rec'.

Inductive typ : Set :=  (*r types *)
 | typ_top : typ (*r top type *)
 | typ_bot : typ (*r bottom type *)
 | typ_base : typ (*r base type *)
 | typ_arrow (A:typ) (B:typ) (*r function types *)
 | typ_and (A:typ) (B:typ) (*r intersection *)
 | typ_rcd (l:label) (A:typ) (*r record *).

Inductive ttyp : Set :=  (*r types *)
 | ttyp_top : ttyp (*r top type *)
 | ttyp_bot : ttyp (*r bottom type *)
 | ttyp_base : ttyp (*r base type *)
 | ttyp_arrow (At:ttyp) (Bt:ttyp) (*r function types *)
 | ttyp_rcd (ll:tindex) (At:ttyp) (Bt:ttyp) (*r record *).

Fixpoint check_toplike (A : typ) :=
  match A with
  | typ_top => true
  | typ_bot => false
  | typ_base => false
  | typ_arrow _ B => check_toplike B
  | typ_rcd l B => check_toplike B
  | typ_and A B => (check_toplike A) && (check_toplike B)
  end.

Require Import List.

Fixpoint size_tindex (A1 : tindex) {struct A1} : nat :=
  match A1 with
  | ti_bot => 1
  | ti_base => 1
  | ti_arrow A2 B1 => 1 + (size_tindex A2) + (size_tindex B1)
  | ti_rcd l1 A2 => 1 + (size_tindex A2)
  | ti_list a => fold_left Nat.add (map size_tindex a) 1
  end.

Lemma size_foldl_add : forall l n,
    fold_left Nat.add l n = fold_left Nat.add l 0 + n.
Proof.
  introv. gen n. induction* l; intros.
  pose proof IHl (n+a). pose proof IHl a.
  unfold fold_left in *. rewrite H. simpl. rewrite H0. simpl. lia.
Qed.

Lemma size_tindex_min : forall t, 1 <= size_tindex t.
Proof.
  introv. induction* t; simpl; try lia.
  pose proof (size_foldl_add (map size_tindex a) 1). lia.
Qed.

Lemma size_list_decrease : forall a l,
    size_tindex (ti_list l) < size_tindex (ti_list (a::l)).
Proof.
  introv. simpl.
  rewrite size_foldl_add.
  rewrite (size_foldl_add _ (S (size_tindex a))).
  pose proof size_tindex_min a. lia.
Qed.

Lemma tindex_dec : forall t1 t2 : tindex, {t1 = t2} + {t1 <> t2}.
Proof.
  introv.
  assert (SizeInd: exists i:nat, (size_tindex t1 + size_tindex t2)  < i) by eauto.
Restart.
(* indTypSize (size_tindex t1 + size_tindex t2). t1. *)
introv. pose proof tindex_rec'. ; intros; induction* t2.
  all: try solve [right; intro HF; inverts HF].
  - destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2); subst*.
    all: try solve [right; intro HF; applys n; inverts~ HF].
  - destruct (string_dec l l0); destruct (IHt1 t2); subst*.
    all: try solve [right; intro HF; applys n; inverts~ HF].
  - destruct a; destruct* a0.
    all: try solve [right; intro HF; inverts~ HF].

     decide equality. 1: repeat decide equality. solve_decision. decide equality. decide equality.
    induction l as [| x l IHl]; destruct l' as [| y l'].
    left; trivial.
    right; apply nil_cons.
    right; unfold not; intro HF; apply (nil_cons (sym_eq HF)).
    destruct (eqA_dec x y) as [xeqy|xneqy]; destruct (IHl l') as [leql'|lneql'];
      try (right; unfold not; intro HF; injection HF; intros; contradiction).
    rewrite xeqy; rewrite leql'; left; trivial.
Defined.

Fixpoint styp2typeindex (A: typ) : list tindex :=
  if (check_toplike A) then nil
  else
    match A with
    | typ_top => nil
    | typ_bot => [ ti_bot ]
    | typ_base => [ ti_base ]
    | typ_arrow A1 A2 => [ ti_arrow (stype2typeindex A1) (stype2typeindex A2) ]
    | typ_rcd l A' => [ ti_rcd  l (stype2typeindex A') ]
    | typ_and A1 A2 => nodup string_dec (merge (stype2string A1) (stype2string A2))
    end.

Inductive texp : Set :=  (*r target term *)
 | texp_var_b (_:nat) (*r variable *)
 | texp_var_f (x:var) (*r variable *)
 | texp_base (b:lit) (*r base value *)
 | texp_abs (t:texp) (*r abstractions *)
 | texp_fixpoint (t:texp) (*r fixpoint *)
 | texp_app (t1:texp) (t2:texp) (*r applications *)
 | texp_nil : texp (*r empty record *)
 | texp_cons (ll:tindex) (t1':texp) (t2:texp)
 | texp_proj (t1:texp) (ll:tindex) (*r projection *)
 | texp_concat (t1:texp) (t2:texp) (*r concatenation *).

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

Inductive exp : Set :=  (*r expressions *)
 | exp_top : exp (*r top value *)
 | exp_base (b:lit) (*r base literal *)
 | exp_var_b (_:nat) (*r variables *)
 | exp_var_f (x:var) (*r variables *)
 | exp_abs (A:typ) (e:exp) (B:typ) (*r abstractions *)
 | exp_fixpoint (A:typ) (e:exp) (*r fixpoint *)
 | exp_app (e1:exp) (e2:exp) (*r applications *)
 | exp_merge (e1:exp) (e2:exp) (*r merge *)
 | exp_anno (e:exp) (A:typ) (*r annotation *)
 | exp_rcd (l:label) (e:exp) (*r record *)
 | exp_proj (e:exp) (l:label) (*r projection *).

Definition tctx : Set := list ( atom * ttyp ).

Definition ctx : Set := list ( atom * typ ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_texp_wrt_texp_rec (k:nat) (t_5:texp) (t__6:texp) {struct t__6}: texp :=
  match t__6 with
  | (texp_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => texp_var_b nat
        | inleft (right _) => t_5
        | inright _ => texp_var_b (nat - 1)
      end
  | (texp_var_f x) => texp_var_f x
  | (texp_base b) => texp_base b
  | (texp_abs t) => texp_abs (open_texp_wrt_texp_rec (S k) t_5 t)
  | (texp_fixpoint t) => texp_fixpoint (open_texp_wrt_texp_rec (S k) t_5 t)
  | (texp_app t1 t2) => texp_app (open_texp_wrt_texp_rec k t_5 t1) (open_texp_wrt_texp_rec k t_5 t2)
  | texp_nil => texp_nil
  | (texp_cons ll t1' t2) => texp_cons ll (open_texp_wrt_texp_rec k t_5 t1') (open_texp_wrt_texp_rec k t_5 t2)
  | (texp_proj t1 ll) => texp_proj (open_texp_wrt_texp_rec k t_5 t1) ll
  | (texp_concat t1 t2) => texp_concat (open_texp_wrt_texp_rec k t_5 t1) (open_texp_wrt_texp_rec k t_5 t2)
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | exp_top => exp_top
  | (exp_base b) => exp_base b
  | (exp_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => exp_var_b nat
        | inleft (right _) => e_5
        | inright _ => exp_var_b (nat - 1)
      end
  | (exp_var_f x) => exp_var_f x
  | (exp_abs A e B) => exp_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
  | (exp_fixpoint A e) => exp_fixpoint A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_merge e1 e2) => exp_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_anno e A) => exp_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (exp_rcd l e) => exp_rcd l (open_exp_wrt_exp_rec k e_5 e)
  | (exp_proj e l) => exp_proj (open_exp_wrt_exp_rec k e_5 e) l
end.

Definition open_texp_wrt_texp t_5 t__6 := open_texp_wrt_texp_rec 0 t__6 t_5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_texp *)
Inductive lc_texp : texp -> Prop :=    (* defn lc_texp *)
 | lc_texp_var_f : forall (x:var),
     (lc_texp (texp_var_f x))
 | lc_texp_base : forall (b:lit),
     (lc_texp (texp_base b))
 | lc_texp_abs : forall (t:texp),
      ( forall x , lc_texp  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     (lc_texp (texp_abs t))
 | lc_texp_fixpoint : forall (t:texp),
      ( forall x , lc_texp  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     (lc_texp (texp_fixpoint t))
 | lc_texp_app : forall (t1 t2:texp),
     (lc_texp t1) ->
     (lc_texp t2) ->
     (lc_texp (texp_app t1 t2))
 | lc_texp_nil :
     (lc_texp texp_nil)
 | lc_texp_cons : forall (ll:tindex) (t1' t2:texp),
     (lc_texp t1') ->
     (lc_texp t2) ->
     (lc_texp (texp_cons ll t1' t2))
 | lc_texp_proj : forall (t1:texp) (ll:tindex),
     (lc_texp t1) ->
     (lc_texp (texp_proj t1 ll))
 | lc_texp_concat : forall (t1 t2:texp),
     (lc_texp t1) ->
     (lc_texp t2) ->
     (lc_texp (texp_concat t1 t2)).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_exp_top :
     (lc_exp exp_top)
 | lc_exp_base : forall (b:lit),
     (lc_exp (exp_base b))
 | lc_exp_var_f : forall (x:var),
     (lc_exp (exp_var_f x))
 | lc_exp_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_abs A e B))
 | lc_exp_fixpoint : forall (A:typ) (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_fixpoint A e))
 | lc_exp_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_app e1 e2))
 | lc_exp_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_merge e1 e2))
 | lc_exp_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (exp_anno e A))
 | lc_exp_rcd : forall (l:label) (e:exp),
     (lc_exp e) ->
     (lc_exp (exp_rcd l e))
 | lc_exp_proj : forall (e:exp) (l:label),
     (lc_exp e) ->
     (lc_exp (exp_proj e l)).
(** free variables *)
Fixpoint fv_texp (t_5:texp) : vars :=
  match t_5 with
  | (texp_var_b nat) => {}
  | (texp_var_f x) => {{x}}
  | (texp_base b) => {}
  | (texp_abs t) => (fv_texp t)
  | (texp_fixpoint t) => (fv_texp t)
  | (texp_app t1 t2) => (fv_texp t1) \u (fv_texp t2)
  | texp_nil => {}
  | (texp_cons ll t1' t2) => (fv_texp t1') \u (fv_texp t2)
  | (texp_proj t1 ll) => (fv_texp t1)
  | (texp_concat t1 t2) => (fv_texp t1) \u (fv_texp t2)
end.

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | exp_top => {}
  | (exp_base b) => {}
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {{x}}
  | (exp_abs A e B) => (fv_exp e)
  | (exp_fixpoint A e) => (fv_exp e)
  | (exp_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (exp_merge e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (exp_anno e A) => (fv_exp e)
  | (exp_rcd l e) => (fv_exp e)
  | (exp_proj e l) => (fv_exp e)
end.

(** substitutions *)
Fixpoint subst_texp (t_5:texp) (x5:var) (t__6:texp) {struct t__6} : texp :=
  match t__6 with
  | (texp_var_b nat) => texp_var_b nat
  | (texp_var_f x) => (if eq_var x x5 then t_5 else (texp_var_f x))
  | (texp_base b) => texp_base b
  | (texp_abs t) => texp_abs (subst_texp t_5 x5 t)
  | (texp_fixpoint t) => texp_fixpoint (subst_texp t_5 x5 t)
  | (texp_app t1 t2) => texp_app (subst_texp t_5 x5 t1) (subst_texp t_5 x5 t2)
  | texp_nil => texp_nil
  | (texp_cons ll t1' t2) => texp_cons ll (subst_texp t_5 x5 t1') (subst_texp t_5 x5 t2)
  | (texp_proj t1 ll) => texp_proj (subst_texp t_5 x5 t1) ll
  | (texp_concat t1 t2) => texp_concat (subst_texp t_5 x5 t1) (subst_texp t_5 x5 t2)
end.

Fixpoint esubst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | exp_top => exp_top
  | (exp_base b) => exp_base b
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => (if eq_var x x5 then e_5 else (exp_var_f x))
  | (exp_abs A e B) => exp_abs A (esubst_exp e_5 x5 e) B
  | (exp_fixpoint A e) => exp_fixpoint A (esubst_exp e_5 x5 e)
  | (exp_app e1 e2) => exp_app (esubst_exp e_5 x5 e1) (esubst_exp e_5 x5 e2)
  | (exp_merge e1 e2) => exp_merge (esubst_exp e_5 x5 e1) (esubst_exp e_5 x5 e2)
  | (exp_anno e A) => exp_anno (esubst_exp e_5 x5 e) A
  | (exp_rcd l e) => exp_rcd l (esubst_exp e_5 x5 e)
  | (exp_proj e l) => exp_proj (esubst_exp e_5 x5 e) l
end.

Fixpoint check_toplike (A : typ) :=
  match A with
  | typ_top => true
  | typ_bot => false
  | typ_base => false
  | typ_arrow _ B => check_toplike B
  | typ_rcd l B => check_toplike B
  | typ_and A B => (check_toplike A) && (check_toplike B)
  end.

Require Import Strings.String.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Require Import StructTact.StringOrders.

Module NOTF := OT_to_Full string_lex_as_OT.
Module NTTLB := OTF_to_TTLB NOTF.
Module Export NSort := Sort NTTLB.

Open Scope string_scope.

Definition LS := list string.

(* dedup => fold_left append (nodup string_dec l) "". *)
Definition list_string_2_string (l : LS) : string :=
  fold_left append l "".

Coercion list_string_2_string : LS >-> string.

Fixpoint stype2string (A: typ) : LS :=
  if (check_toplike A) then nil
  else
    match A with
    | typ_top => nil
    | typ_bot => [ "Bot" ]
    | typ_base => [ "Base" ]
    | typ_arrow A1 A2 => [ ( "(" ++ (stype2string A1) ++ "->" ++ (stype2string A2) ++ ")" ) ]
    | typ_rcd l A' => ["{" ++  l ++ "=>" ++ (stype2string A') ++ "}"]
    | typ_and A1 A2 => nodup string_dec (merge (stype2string A1) (stype2string A2))
    end.

Notation "|| A ||" := (stype2string A) (at level 50, A at next level). (* 1 is too high *)

Fixpoint ttyp_concat_simpl (A: ttyp) (B: ttyp) :=
  match A with
  | ttyp_top => B
  | ttyp_rcd l At Bt => ttyp_rcd l At (ttyp_concat_simpl Bt B)
  | _ => ttyp_top
  end.

Reserved Notation "|[ A ]|" (at level 5, A at next level).
Fixpoint styp2ttyp (A: typ) : ttyp :=
  if (check_toplike A) then ttyp_top
  else match A with
  | typ_top => ttyp_top
  | typ_bot => ttyp_rcd (|| A ||) ttyp_bot ttyp_top
  | typ_base => ttyp_rcd (|| A ||) ttyp_base ttyp_top
  | typ_arrow B1 B2 => ttyp_rcd (|| A ||) ( ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)) ttyp_top
  | typ_rcd l A' => ttyp_rcd (|| A ||) (|[ A' ]|) ttyp_top
  | typ_and A1 A2 => ttyp_concat_simpl (|[ A1 ]|) (|[ A2 ]|)
  end
where "|[ A ]|" := (styp2ttyp A).

Definition string_eq_dec : forall (x y : string), { x = y } + { x <> y }.
Proof.
  repeat decide equality.
Defined.

Fixpoint tlookup (i:string) (tr:texp) : option texp :=
  match tr with
  | texp_cons ti t tr' => if string_eq_dec i ti then Some t else tlookup i tr'
  | _ => None
  end.

Fixpoint Tlookup (i:string) (T:ttyp) : option ttyp :=
  match T with
  | ttyp_rcd ti At Bt => if string_eq_dec i ti then Some At else Tlookup i Bt
  | _ => None
  end.

Inductive subTarget : ttyp -> ttyp -> Prop :=
 | ST_refl : forall At,
     subTarget At At
| ST_arrow: forall At Bt At' Bt',
    subTarget At At' -> subTarget At' At -> subTarget Bt Bt' -> subTarget Bt' Bt -> subTarget (ttyp_arrow At Bt) (ttyp_arrow At' Bt')
 | ST_rcd : forall At Bt,
     rec_typ At -> rec_typ Bt ->
     (forall l Ct, Tlookup l At = Some Ct -> exists Ct', Tlookup l Bt = Some Ct' /\ subTarget Ct' Ct /\ subTarget Ct Ct') ->
     subTarget Bt At.

#[export] Hint Constructors subTarget : core.


(** definitions *)

(* defns TopLikeType *)
Inductive toplike : typ -> Prop :=    (* defn toplike *)
 | TL_top :
     toplike typ_top
 | TL_and : forall (A B:typ),
     toplike A ->
     toplike B ->
     toplike (typ_and A B)
 | TL_arr : forall (A B:typ),
     toplike B ->
     toplike (typ_arrow A B)
 | TL_rcd : forall (l:label) (B:typ),
     toplike B ->
     toplike (typ_rcd l B).

(* defns SplitType *)
Inductive spl : typ -> typ -> typ -> Prop :=    (* defn spl *)
 | Sp_and : forall (A B:typ),
     spl  (typ_and A B)   A   B
 | Sp_arrow : forall (A B B1 B2:typ),
     spl B B1 B2 ->
     spl  (typ_arrow A B)   (typ_arrow A B1)   (typ_arrow A B2)
 | Sp_rcd : forall (l:label) (B B1 B2:typ),
     spl B B1 B2 ->
     spl (typ_rcd l B) (typ_rcd l B1) (typ_rcd l B2).

(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
 | O_top :
     ord typ_top
 | O_int :
     ord typ_base
 | O_arrow : forall (A B:typ),
     ord B ->
     ord (typ_arrow A B)
 | O_rcd : forall (l:label) (B:typ),
     ord B ->
     ord (typ_rcd l B).

(* defns Disjoint *)
Inductive disjoint : typ -> typ -> Prop :=    (* defn disjoint *)
 | D_topL : forall (A:typ),
     disjoint typ_top A
 | D_topR : forall (A:typ),
     disjoint A typ_top
 | D_andL : forall (A1 A2 B:typ),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (typ_and A1 A2) B
 | D_andR : forall (A B1 B2:typ),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (typ_and B1 B2)
 | D_BaseArr : forall (A1 A2:typ),
     disjoint typ_base (typ_arrow A1 A2)
 | D_ArrBase : forall (A1 A2:typ),
     disjoint (typ_arrow A1 A2) typ_base
 | D_ArrArr : forall (A1 A2 B1 B2:typ),
     disjoint A2 B2 ->
     disjoint (typ_arrow A1 A2) (typ_arrow B1 B2)
 | D_rcdEq : forall (l:label) (A B:typ),
     disjoint A B ->
     disjoint (typ_rcd l A) (typ_rcd l B)
 | D_rcdNeq : forall (l1:label) (A:typ) (l2:label) (B:typ),
      l1  <>  l2  ->
     disjoint (typ_rcd l1 A) (typ_rcd l2 B)
 | D_BaseRcd : forall (l:label) (A:typ),
     disjoint typ_base (typ_rcd l A)
 | D_RcdBase : forall (l:label) (A:typ),
     disjoint (typ_rcd l A) typ_base
 | D_ArrRcd : forall (A1 A2:typ) (l:label) (A:typ),
     disjoint (typ_arrow A1 A2) (typ_rcd l A)
 | D_RcdArr : forall (l:label) (A A1 A2:typ),
     disjoint (typ_rcd l A) (typ_arrow A1 A2).

(* defns CoMerge *)
Inductive comerge : texp -> typ -> typ -> texp -> typ -> texp -> Prop :=    (* defn comerge *)
 | M_Top : forall (t1:texp) (A C:typ) (t2:texp) (B:typ),
     lc_texp t1 ->
     lc_texp t2 ->
     toplike C ->
     spl C A B ->
     comerge t1 A C t2 B texp_nil
 | M_And : forall (t1:texp) (A B:typ) (t2:texp),
     lc_texp t1 ->
     lc_texp t2 ->
      not ( toplike (typ_and A B) )  ->
     comerge t1 A (typ_and A B) t2 B (texp_concat t1 t2)
 | M_Arrow : forall (L:vars) (t1:texp) (A B1 B:typ) (t2:texp) (B2:typ) (t:texp),
      not ( toplike B1 )  ->
      not ( toplike B2 )  ->
      ( forall x , x \notin  L  -> comerge (texp_app  (texp_proj t1  (styp2typeindex ( (typ_arrow A B1) )) )  (texp_var_f x)) B1 B (texp_app  (texp_proj t2  (styp2typeindex ( (typ_arrow A B2) )) )  (texp_var_f x)) B2  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     comerge t1 (typ_arrow A B1) (typ_arrow A B) t2 (typ_arrow A B2)  (texp_cons   (styp2typeindex ( (typ_arrow A B) ))    (texp_abs t)  texp_nil)
 | M_ArrowL : forall (L:vars) (t1:texp) (A B1 B:typ) (t2:texp) (B2:typ) (t:texp),
     lc_texp t2 ->
      not ( toplike B1 )  ->
     toplike B2 ->
      ( forall x , x \notin  L  -> comerge (texp_app  (texp_proj t1  (styp2typeindex ( (typ_arrow A B1) )) )  (texp_var_f x)) B1 B texp_nil B2  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     comerge t1 (typ_arrow A B1) (typ_arrow A B) t2 (typ_arrow A B2)  (texp_cons   (styp2typeindex ( (typ_arrow A B) ))    (texp_abs t)  texp_nil)
 | M_ArrowR : forall (L:vars) (t1:texp) (A B1 B:typ) (t2:texp) (B2:typ) (t:texp),
     lc_texp t1 ->
     toplike B1 ->
      not ( toplike B2 )  ->
      ( forall x , x \notin  L  -> comerge texp_nil B1 B (texp_app  (texp_proj t2  (styp2typeindex ( (typ_arrow A B2) )) )  (texp_var_f x)) B2  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     comerge t1 (typ_arrow A B1) (typ_arrow A B) t2 (typ_arrow A B2)  (texp_cons   (styp2typeindex ( (typ_arrow A B) ))    (texp_abs t)  texp_nil)
 | M_Rcd : forall (t1:texp) (l:label) (A1 A:typ) (t2:texp) (A2:typ) (t:texp),
      not ( toplike A1 )  ->
      not ( toplike A2 )  ->
     comerge (texp_proj t1  (styp2typeindex ( (typ_rcd l A1) )) ) A1 A (texp_proj t2  (styp2typeindex ( (typ_rcd l A2) )) ) A2 t ->
     comerge t1 (typ_rcd l A1) (typ_rcd l A) t2 (typ_rcd l A2)  (texp_cons   (styp2typeindex ( (typ_rcd l A) ))    t  texp_nil)
 | M_RcdL : forall (t1:texp) (l:label) (A1 A:typ) (t2:texp) (A2:typ) (t:texp),
     lc_texp t2 ->
      not ( toplike A1 )  ->
     toplike A2 ->
     comerge (texp_proj t1  (styp2typeindex ( (typ_rcd l A1) )) ) A1 A texp_nil A2 t ->
     comerge t1 (typ_rcd l A1) (typ_rcd l A) t2 (typ_rcd l A2)  (texp_cons   (styp2typeindex ( (typ_rcd l A) ))    t  texp_nil)
 | M_RcdR : forall (t1:texp) (l:label) (A1 A:typ) (t2:texp) (A2:typ) (t:texp),
     lc_texp t1 ->
     toplike A1 ->
      not ( toplike A2 )  ->
     comerge texp_nil A1 A (texp_proj t2  (styp2typeindex ( (typ_rcd l A2) )) ) A2 t ->
     comerge t1 (typ_rcd l A1) (typ_rcd l A) t2 (typ_rcd l A2)  (texp_cons   (styp2typeindex ( (typ_rcd l A) ))    t  texp_nil) .

(* defns CoSubtyping *)
Inductive cosub : texp -> typ -> typ -> texp -> Prop :=    (* defn cosub *)
 | S_Top : forall (t:texp) (A B:typ),
     lc_texp t ->
     ord B ->
     toplike B ->
     cosub t A B texp_nil
 | S_Bot : forall (t:texp) (B:typ) (x:var),
     lc_texp t ->
     ord B ->
      not ( toplike B )  ->
     cosub t typ_bot B  (texp_cons   (styp2typeindex ( B ))    (texp_fixpoint (texp_var_b 0))  texp_nil)
 | S_Base : forall (t:texp),
     lc_texp t ->
     cosub t typ_base typ_base  (texp_cons   (styp2typeindex ( typ_base ))    (texp_proj t  (styp2typeindex ( typ_base )) )  texp_nil)
 | S_Arrow : forall (L:vars) (t:texp) (A1 A2 B1 B2:typ) (t2 t1:texp),
     ord B2 ->
      not ( toplike B2 )  ->
      ( forall x , x \notin  L  ->  ( cosub (texp_var_f x) B1 A1 t1  /\  cosub (texp_app  (texp_proj t  (styp2typeindex ( (typ_arrow A1 A2) )) )  t1) A2 B2  ( open_texp_wrt_texp t2 (texp_var_f x) )  )  )  ->
     cosub t (typ_arrow A1 A2) (typ_arrow B1 B2)  (texp_cons   (styp2typeindex ( (typ_arrow B1 B2) ))    (texp_abs t2)  texp_nil)
 | S_Rcd : forall (t:texp) (l:label) (A B:typ) (t2:texp),
     ord B ->
      not ( toplike B )  ->
     cosub (texp_proj t  (styp2typeindex ( (typ_rcd l A) )) ) A B t2 ->
     cosub t (typ_rcd l A) (typ_rcd l B)  (texp_cons   (styp2typeindex ( (typ_rcd l B) ))    t2  texp_nil)
 | S_AndL : forall (t:texp) (A B C:typ) (t':texp),
     ord C ->
     cosub t A C t' ->
     cosub t (typ_and A B) C t'
 | S_AndR : forall (t:texp) (A B C:typ) (t':texp),
     ord C ->
     cosub t B C t' ->
     cosub t (typ_and A B) C t'
 | S_Split : forall (t:texp) (A B:typ) (t3:texp) (B1 B2:typ) (t1 t2:texp),
     spl B B1 B2 ->
     cosub t A B1 t1 ->
     cosub t A B2 t2 ->
     comerge t1 B1 B t2 B2 t3 ->
     cosub t A B t3.

(* defns Subtyping *)
Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
 | S_z :
     sub typ_base typ_base
 | S_top : forall (A B:typ),
     toplike B ->
     sub A B
 | S_bot :
     sub typ_bot typ_bot
 | S_arr : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A1 B1 ->
     sub A2 B2 ->
     sub B2 A2 ->
     sub (typ_arrow A1 A2) (typ_arrow B1 B2)
 | S_rcd : forall (l:label) (A B:typ),
     sub A B ->
     sub B A ->
     sub (typ_rcd l A) (typ_rcd l B)
 | S_andl1 : forall (A1 A2 A3:typ),
     sub A1 A3 ->
     sub (typ_and A1 A2) A3
 | S_andl2 : forall (A1 A2 A3:typ),
     sub A2 A3 ->
     sub (typ_and A1 A2) A3
 | S_andr : forall (A1 A2 A3:typ),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (typ_and A2 A3).

(* defns Projection *)
Inductive proj : texp -> typ -> label -> texp -> typ -> Prop :=    (* defn proj *)
 | P_Top : forall (t1:texp) (A:typ) (l:label),
     lc_texp t1 ->
     toplike A ->
     proj t1 A l texp_nil typ_top
 | P_RcdEq : forall (t:texp) (l:label) (A:typ),
     lc_texp t ->
      not ( toplike A )  ->
     proj t (typ_rcd l A) l (texp_proj t  (styp2typeindex ( (typ_rcd l A) )) ) A
 | P_RcdNeq : forall (t:texp) (l1:label) (A:typ) (l2:label),
     lc_texp t ->
      not ( toplike A )  ->
      l1  <>  l2  ->
     proj t (typ_rcd l1 A) l2 texp_nil typ_top
 | P_And : forall (t1:texp) (A B:typ) (l:label) (t3 t4:texp) (A' B':typ),
     proj t1 A l t3 A' ->
     proj t1 B l t4 B' ->
     proj t1 (typ_and A B) l (texp_concat t3 t4) (typ_and A' B').

(* defns DistributiveApplication *)
Inductive distapp : texp -> typ -> texp -> typ -> texp -> typ -> Prop :=    (* defn distapp *)
 | A_Top : forall (t1:texp) (A:typ) (t2:texp) (B:typ),
     lc_texp t1 ->
     lc_texp t2 ->
     toplike A ->
     distapp t1 A t2 B texp_nil typ_top
 | A_Arrow : forall (t1:texp) (A B:typ) (t2:texp) (C:typ) (t3:texp),
     lc_texp t1 ->
      not ( toplike B )  ->
     cosub t2 C A t3 ->
     distapp t1 (typ_arrow A B) t2 C (texp_app  (texp_proj t1  (styp2typeindex ( (typ_arrow A B) )) )  t3) B
 | A_And : forall (t1:texp) (A B:typ) (t2:texp) (C:typ) (t3 t4:texp) (A' B':typ),
     distapp t1 A t2 C t3 A' ->
     distapp t1 B t2 C t4 B' ->
     distapp t1 (typ_and A B) t2 C (texp_concat t3 t4) (typ_and A' B').

(* defns Elaboration *)
Inductive elaboration : ctx -> exp -> dirflag -> typ -> texp -> Prop :=    (* defn elaboration *)
 | Ela_Top : forall (G:ctx),
      uniq  G  ->
     elaboration G exp_top Inf typ_top texp_nil
 | Ela_TopAbs : forall (G:ctx) (A:typ) (e:exp) (B:typ),
     lc_exp (exp_abs A e B) ->
      uniq  G  ->
     toplike B ->
     elaboration G (exp_abs A e B) Inf (typ_arrow A B) texp_nil
 | Ela_TopRcd : forall (G:ctx) (l:label) (e:exp) (A:typ) (t:texp),
     elaboration G e Inf A t ->
     toplike A ->
     elaboration G (exp_rcd l e) Inf (typ_rcd l A) texp_nil
 | Ela_Base : forall (G:ctx) (b:lit),
      uniq  G  ->
     elaboration G (exp_base b) Inf typ_base  (texp_cons   (styp2typeindex ( typ_base ))    (texp_base b)  texp_nil)
 | Ela_Var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     elaboration G (exp_var_f x) Inf A (texp_var_f x)
 | Ela_Fix : forall (L:vars) (G:ctx) (A:typ) (e:exp) (t:texp),
      ( forall x , x \notin  L  -> elaboration  (cons ( x , A )  G )   ( open_exp_wrt_exp e (exp_var_f x) )  Chk A  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     elaboration G (exp_fixpoint A e) Inf A (texp_fixpoint t)
 | Ela_Abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ) (t:texp),
      not ( toplike B )  ->
      ( forall x , x \notin  L  -> elaboration  (cons ( x , A )  G )   ( open_exp_wrt_exp e (exp_var_f x) )  Chk B  ( open_texp_wrt_texp t (texp_var_f x) )  )  ->
     elaboration G (exp_abs A e B) Inf (typ_arrow A B)  (texp_cons   (styp2typeindex ( (typ_arrow A B) ))    (texp_abs t)  texp_nil)
 | Ela_App : forall (G:ctx) (e1 e2:exp) (C:typ) (t3:texp) (A:typ) (t1:texp) (B':typ) (t2:texp),
     elaboration G e1 Inf A t1 ->
     elaboration G e2 Inf B' t2 ->
     distapp t1 A t2 B' t3 C ->
     elaboration G (exp_app e1 e2) Inf C t3
 | Ela_Rcd : forall (G:ctx) (l:label) (e:exp) (A:typ) (t:texp),
      not ( toplike A )  ->
     elaboration G e Inf A t ->
     elaboration G (exp_rcd l e) Inf (typ_rcd l A)  (texp_cons   (styp2typeindex ( (typ_rcd l A) ))    t  texp_nil)
 | Ela_Proj : forall (G:ctx) (e:exp) (l:label) (B:typ) (t2:texp) (A:typ) (t1:texp),
     elaboration G e Inf A t1 ->
     proj t1 A l t2 B ->
     elaboration G (exp_proj e l) Inf B t2
 | Ela_Merge : forall (G:ctx) (e1 e2:exp) (A B:typ) (t1 t2:texp),
     elaboration G e1 Inf A t1 ->
     elaboration G e2 Inf B t2 ->
     disjoint A B ->
     elaboration G (exp_merge e1 e2) Inf (typ_and A B) (texp_concat t1 t2)
 | Ela_Anno : forall (G:ctx) (e:exp) (A:typ) (t:texp),
     elaboration G e Chk A t ->
     elaboration G (exp_anno e A) Inf A t
 | Ela_Sub : forall (G:ctx) (e:exp) (B:typ) (t2:texp) (A:typ) (t1:texp),
     elaboration G e Inf A t1 ->
     cosub t1 A B t2 ->
     elaboration G e Chk B t2.

(* defns Values *)
Inductive value : texp -> Prop :=    (* defn value *)
 | value_unit :
     value texp_nil
 | value_lit : forall (b:lit),
     value (texp_base b)
 | value_abs : forall (t:texp),
     lc_texp (texp_abs t) ->
     value (texp_abs t)
 | value_merge : forall (ll:tindex) (tv1 tv2:texp),
     value tv1 ->
     value tv2 ->
     value (texp_cons ll tv1 tv2).

(* defns TargetStep *)
Inductive target_step : texp -> texp -> Prop :=    (* defn target_step *)
 | TS_Proj1 : forall (t:texp) (ll:tindex) (t':texp),
     target_step t t' ->
     target_step (texp_proj t ll) (texp_proj t' ll)
 | TS_AppL : forall (t t2 t':texp),
     lc_texp t2 ->
     target_step t t' ->
     target_step (texp_app t t2) (texp_app t' t2)
 | TS_AppR : forall (tv t t':texp),
     value tv ->
     target_step t t' ->
     target_step (texp_app tv t) (texp_app tv t')
 | TS_MergeL : forall (t t2 t':texp),
     lc_texp t2 ->
     target_step t t' ->
     target_step (texp_concat t t2) (texp_concat t' t2)
 | TS_MergeR : forall (tv t t':texp),
     value tv ->
     target_step t t' ->
     target_step (texp_concat tv t) (texp_concat tv t')
 | TS_RcdHead : forall (ll:tindex) (t t2 t':texp),
     lc_texp t2 ->
     target_step t t' ->
     target_step (texp_cons ll t t2) (texp_cons ll t' t2)
 | TS_RcdTail : forall (ll:tindex) (tv t t':texp),
     value tv ->
     target_step t t' ->
     target_step (texp_cons ll tv t) (texp_cons ll tv t')
 | TS_MergeEmpty : forall (tv:texp),
     value tv ->
     target_step (texp_concat texp_nil tv) tv
 | TS_MergeRcd : forall (ll:tindex) (tv1 tv2 tv3:texp),
     value tv1 ->
     value tv2 ->
     value tv3 ->
     target_step (texp_concat  (texp_cons ll tv1 tv2)  tv3) (texp_cons ll tv1  (texp_concat tv2 tv3) )
 | TS_ProjRcd : forall (tv:texp) (ll:tindex) (t:texp),
     value tv ->
      tlookup  ll   tv  = Some  t  ->
     target_step (texp_proj tv ll) t
 | TS_AppAbs : forall (t tv:texp),
     lc_texp (texp_abs t) ->
     lc_texp tv ->
     target_step (texp_app  (texp_abs t)  tv)  (open_texp_wrt_texp  t tv )
 | TS_Fixpoint : forall (t:texp),
     lc_texp (texp_fixpoint t) ->
     target_step (texp_fixpoint t)  (open_texp_wrt_texp  t (texp_fixpoint t) ) .

(* defns RecordTypes *)
Inductive rec_typ : ttyp -> Prop :=    (* defn rec_typ *)
 | RT_Nil :
     rec_typ ttyp_top
 | RT_Rcd : forall (ll:tindex) (At Bt:ttyp),
     rec_typ Bt ->
     rec_typ (ttyp_rcd ll At Bt).

(* defns ConcatTypes *)
Inductive concat_typ : ttyp -> ttyp -> ttyp -> Prop :=    (* defn concat_typ *)
 | CT_Nil : forall (Bt:ttyp),
     rec_typ Bt ->
     concat_typ ttyp_top Bt Bt
 | CT_Rcd : forall (ll:tindex) (At Bt1 Bt2 Ct At':ttyp),
      (   (  Tlookup  ll   Bt2  = Some  At'   /\   subTarget  At'   At  /\ subTarget  At   At'  )    \/   Tlookup  ll   Bt2  = None  )  ->
     concat_typ Bt1 Bt2 Ct ->
     concat_typ  (ttyp_rcd ll At Bt1)  Bt2 (ttyp_rcd ll At Ct).

(* defns ContainedByRecTyp *)
Inductive contained_by_rec_typ : ttyp -> tindex -> ttyp -> Prop :=    (* defn contained_by_rec_typ *)
 | CRT_Head : forall (ll1:tindex) (At Bt:ttyp),
     contained_by_rec_typ  (ttyp_rcd ll1 At Bt)  ll1 At
 | CRT_Tail : forall (ll1:tindex) (At Bt:ttyp) (ll2:tindex) (Ct:ttyp),
     contained_by_rec_typ Bt ll2 Ct ->
     contained_by_rec_typ  (ttyp_rcd ll1 At Bt)  ll2 Ct.

(* defns WelformedTypes *)
Inductive wf_typ : ttyp -> Prop :=    (* defn wf_typ *)
 | WF_Nil :
     wf_typ ttyp_top
 | WF_Bot :
     wf_typ ttyp_bot
 | WF_Base :
     wf_typ ttyp_base
 | WF_Rcd : forall (ll:tindex) (At Bt At':ttyp),
     wf_typ At ->
     wf_typ Bt ->
     rec_typ Bt ->
      (   (  Tlookup  ll   Bt  = Some  At'   /\   subTarget  At'   At  /\ subTarget  At   At'  )    \/   Tlookup  ll   Bt  = None  )  ->
     wf_typ (ttyp_rcd ll At Bt)
 | WF_Arrow : forall (At Bt:ttyp),
     wf_typ At ->
     wf_typ Bt ->
     wf_typ (ttyp_arrow At Bt).

(* defns WelformedCtx *)
Inductive wf_ctx : tctx -> Prop :=    (* defn wf_ctx *)
 | WFC_Nil :
     wf_ctx  nil
 | WFC_Cons : forall (Gt:tctx) (x:var) (At:ttyp),
     wf_typ At ->
     wf_ctx Gt ->
     wf_ctx  (cons ( x , At )  Gt ) .

(* defns TargetSubtype *)
Inductive SubtypeTarget : ttyp -> ttyp -> Prop :=    (* defn SubtypeTarget *)
 | TS_top : forall (At:ttyp),
     wf_typ At ->
     SubtypeTarget At ttyp_top
 | TS_refl : forall (At:ttyp),
     wf_typ At ->
     SubtypeTarget At At
 | TS_arrow : forall (At1 Bt1 At2 Bt2:ttyp),
     SubtypeTarget At1 At2 ->
     SubtypeTarget Bt1 Bt2 ->
     SubtypeTarget (ttyp_arrow At1 Bt1) (ttyp_arrow At2 Bt2)
 | TS_rcd : forall (Ct:ttyp) (ll:tindex) (At Ct' Bt At':ttyp),
     rec_typ Ct' ->
      Tlookup  ll   Ct  = Some  Bt  ->
     SubtypeTarget Bt At ->
      (   (  Tlookup  ll   Ct'  = Some  At'   /\   subTarget  At'   At  /\ subTarget  At   At'  )    \/   Tlookup  ll   Ct'  = None  )  ->
     SubtypeTarget Ct Ct' ->
     SubtypeTarget Ct (ttyp_rcd ll At Ct').

(* defns TargetTyping *)
Inductive target_typing : tctx -> texp -> ttyp -> Prop :=    (* defn target_typing *)
 | TTyping_Base : forall (Gt:tctx) (b:lit),
      uniq  Gt  ->
     wf_ctx Gt ->
     target_typing Gt (texp_base b) ttyp_base
 | TTyping_Var : forall (Gt:tctx) (x:var) (At:ttyp),
      uniq  Gt  ->
     wf_ctx Gt ->
      binds  x At Gt  ->
     target_typing Gt (texp_var_f x) At
 | TTyping_Abs : forall (L:vars) (Gt:tctx) (t:texp) (At Bt:ttyp),
      ( forall x , x \notin  L  -> target_typing  (cons ( x , At )  Gt )   ( open_texp_wrt_texp t (texp_var_f x) )  Bt )  ->
     target_typing Gt (texp_abs t) (ttyp_arrow At Bt)
 | TTyping_Fix : forall (L:vars) (Gt:tctx) (t:texp) (At Bt:ttyp),
      ( forall x , x \notin  L  -> target_typing  (cons ( x , Bt )  Gt )   ( open_texp_wrt_texp t (texp_var_f x) )  At )  ->
      subTarget  At   Bt  /\ subTarget  Bt   At  ->
     target_typing Gt (texp_fixpoint t) At
 | TTyping_App : forall (Gt:tctx) (t1 t2:texp) (Bt At At':ttyp),
     target_typing Gt t1 (ttyp_arrow At Bt) ->
     target_typing Gt t2 At' ->
      subTarget  At   At'  /\ subTarget  At'   At  ->
     target_typing Gt (texp_app t1 t2) Bt
 | TTyping_RcdNil : forall (Gt:tctx),
      uniq  Gt  ->
     wf_ctx Gt ->
     target_typing Gt texp_nil ttyp_top
 | TTyping_RcdCons : forall (Gt:tctx) (ll:tindex) (t1 t2:texp) (At Bt At':ttyp),
     rec_typ Bt ->
      (   (  Tlookup  ll   Bt  = Some  At'   /\   subTarget  At'   At  /\ subTarget  At   At'  )    \/   Tlookup  ll   Bt  = None  )  ->
     target_typing Gt t1 At ->
     target_typing Gt t2 Bt ->
     target_typing Gt  (texp_cons ll t1 t2)   (ttyp_rcd ll At Bt)
 | TTyping_RcdProj : forall (Gt:tctx) (t:texp) (ll:tindex) (Bt At:ttyp),
     target_typing Gt t At ->
      Tlookup  ll   At  = Some  Bt  ->
     target_typing Gt (texp_proj t ll) Bt
 | TTyping_RcdMerge : forall (Gt:tctx) (t1 t2:texp) (Ct At Bt:ttyp),
     rec_typ At ->
     rec_typ Bt ->
     target_typing Gt t1 At ->
     target_typing Gt t2 Bt ->
     concat_typ At Bt Ct ->
     target_typing Gt (texp_concat t1 t2) Ct.


(** infrastructure *)
Hint Constructors toplike spl ord disjoint comerge cosub sub proj distapp elaboration value target_step rec_typ concat_typ contained_by_rec_typ wf_typ wf_ctx SubtypeTarget target_typing lc_texp lc_exp : core.
