Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Import IfNotations.
(* Require Import StructTact.StringOrders. *)
Require Export syntax_ott.
Require Export Infrastructure.
Require Import TargetTypeSafety.


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

Lemma check_toplike_false : forall A,
    check_toplike A = false -> toplike A -> False.
Proof.
  introv HT1 HT2.
  induction HT2; simpl in *; solve_false.
  forwards* [?|?]: andb_false_elim HT1.
Qed.

#[export] Hint Resolve check_toplike_false : FalseHd.

(* Previous assumptions on the translation function *)
Lemma st_eq_arrow : forall A1 A2 B1 B2,
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_arrow A1 A2) || =  || (typ_arrow B1 B2) || -> || B1 || = || A1 || /\ || B2 || = || A2 ||.
Proof.
  introv HA HB Heq.
  unfold styp2tindex in Heq. unfold styp2tindex.
  repeat case_if;
    try rewrite <- check_toplike_sound_complete in *;
    try inverts C; try inverts C0; solve_false.
  inverts* Heq.
Qed.

Lemma st_eq_rcd : forall A2 B2 l l',
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_rcd l A2) || =  || (typ_rcd l' B2) || -> l = l' /\ || B2 || = || A2 ||.
Proof.
  introv HA HB Heq.
  unfold styp2tindex in Heq. unfold styp2tindex.
  repeat case_if;
    try rewrite <- check_toplike_sound_complete in *;
    try inverts C; try inverts C0; solve_false.
  inverts* Heq.
Qed.

(*
Lemma nodup_merge_ls_cons : forall a l1 l2,
    nodup tindex_dec (merge (a::l1) l2) = a :: (nodup tindex_dec (merge l1 l2))
    \/ nodup tindex_dec (merge (a::l1) l2) = nodup tindex_dec (merge l1 l2).
Proof.
  introv. gen a l1. induction l2; intros.
  - simpl. case_if*.
    + induction* l1.
    + induction* l1.
Abort.

Lemma nodup_merge_ls_inv_1 : forall l1 l2,
    l1 <> nil -> merge l1 l2 <> nil.
Proof with eauto.
  introv HN. destruct l1.
  - false HN...
  - destruct l2... unfold merge. case_if*.
    all: intro HF; false HF.
Qed.

Lemma nodup_merge_ls_inv_2 : forall l1 l2,
    l2 <> nil -> merge l1 l2 <> nil.
Proof with eauto.
  introv HN. destruct l2.
  - false HN...
  - destruct l1...
    applys nodup_merge_ls_inv_1.
    intro HF. false HF.
Qed.
*)

Lemma merge_cons_1 : forall a l1 l2,
    exists b ls, merge (a::l1) l2 = b :: ls.
Proof with eauto.
  introv.
  destruct l2; unfold merge...
  case_if...
Qed.

Lemma merge_cons_2 : forall a l1 l2,
    exists b ls, merge l1 (a::l2) = b :: ls.
Proof with eauto.
  introv.
  destruct l1; unfold merge...
  case_if...
Qed.

Lemma nodup_cons : forall b l,
    exists a ls, nodup tindex_dec (b::l) = a :: ls.
Proof with try solve [exists; jauto].
  induction l; intros...
  all: simpl; try case_if...
  - case_if... destruct C; subst...
    all: simpl in IHl; case_if*.
Qed.


Lemma nodup_merge_nil_inv : forall A B,
    nil = nodup tindex_dec (merge (styp2tindex A) (styp2tindex B))
    -> || A || = ti_list nil /\ || B || = ti_list nil.
Proof with try solve [ try (let HF := fresh "HF" in intro HF; false HF); jauto ].
  introv HE.
  remember (styp2tindex A) as l1.
  remember (styp2tindex B) as l2.
  destruct l1; destruct l2...
  - forwards (?&?&HM): merge_cons_2. rewrite HM in HE.
    forwards (?&?&HN): nodup_cons. rewrite HN in HE.
    false.
  - forwards (?&?&HM): merge_cons_1. rewrite HM in HE.
    forwards (?&?&HN): nodup_cons. rewrite HN in HE.
    false.
  - forwards (?&?&HM): merge_cons_2. rewrite HM in HE.
    forwards (?&?&HN): nodup_cons. rewrite HN in HE.
    false.
Qed.


Corollary st_eq_disjoint : forall A B,
    || A || = || B || -> disjoint A B -> toplike A /\ toplike B.
Proof with try solve_by_invert.
  introv HE HD.
  induction HD; simpl in HE; split*;
    applys* check_toplike_sound_complete;
    try induction* A; try solve [simpl in HE; try case_if; inverts* HE].
  all: simpl in HE; simpl;
    try destruct (check_toplike A);
    try destruct (check_toplike A1); try destruct (check_toplike A2); eauto; false.

  all: try solve [ false IHA1;
                   remember (nodup tindex_dec (merge (styp2tindex A1) (styp2tindex A2))) as l;
                   destruct l; simpl in HE;
                   try forwards (?&?): nodup_merge_nil_inv Heql; subst*; solve_by_invert ].

  all: try solve [ false IHA2;
                   remember (nodup tindex_dec (merge (styp2tindex A1) (styp2tindex A2))) as l;
                   destruct l; simpl in HE;
                   try forwards (?&?): nodup_merge_nil_inv Heql; subst*; solve_by_invert ].

  simpl in HE. Abort.

(* merge, sort *)
Lemma HdRel_relax : forall a l,
    HdRel ti_lex_lt a l -> HdRel NOTF.le a l.
Proof with eauto.
  introv HS. induction* HS. constructor...
  left*.
Qed.

Definition sorted := Sorted ti_lex_lt.

Theorem sorted_unique : forall (l1 l2 : list tindex),
    sorted l1 -> sorted l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  introv HS1 HS2 HP.
  applys* Sort_In_eq ti_lex_lt.
  applys ti_lex_lt_trans.
  applys ti_lex_lt_not_eq.
  split; introv HI;
    eauto using Permutation_sym, Permutation_in.
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

Lemma merge_empty : forall l,
    merge nil l = l.
Proof.
  introv. induction* l.
Qed.

Lemma merge_empty_r : forall l,
    merge l nil = l.
Proof.
  introv. induction* l.
Qed.

#[local] Hint Rewrite merge_empty merge_empty_r : merge.

Lemma merge_cons : forall a l b r,
    merge (a::l) (b::r) =
      if if proj1_sig (tindex_compare_lex a b) is Gt then false else true then a :: merge l (b::r) else b :: merge (a::l) r.
Proof with eauto.
  introv. induction* l; destruct (proj1_sig (tindex_compare_lex a b)); autorewrite with merge...
Qed.

#[local] Hint Rewrite merge_cons : merge.

Lemma test : forall a l r,
    HdRel NOTF.le a l -> HdRel NOTF.le a r -> HdRel NOTF.le a (merge l r).
Proof.
  introv HL HR. destruct l.
  - rewrite* merge_empty.
  - apply HdRel_inv in HL.
    destruct r.
    + rewrite* merge_empty_r.
    + apply HdRel_inv in HR.
      rewrite* merge_cons. case_if*.
Qed.

Lemma merge_sorted : forall l r,
    sorted l -> sorted r -> Sorted NOTF.le (merge l r).
Proof with eauto using sorted_relax.
  introv HSl HSr. gen r.
  induction HSl; intros; autorewrite with merge...
  - induction HSr...
    + autorewrite with merge.
      constructor...
    + destruct (tindex_compare_lex a a0) eqn:HE. destruct c.
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

Lemma HdRel_nodup : forall a l,
    Sorted NOTF.le l -> HdRel ti_lex_lt a l -> HdRel ti_lex_lt a (nodup tindex_dec l).
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
      destruct H0. now applys* ti_lex_lt_trans.
      now subst*.
Qed.

Lemma sorted_nodup : forall l,
    Sorted NOTF.le l -> sorted (nodup tindex_dec l).
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

Lemma merge_sorted_dedup: forall l r,
    sorted l -> sorted r -> sorted (nodup tindex_dec (merge l r)).
Proof with eauto using sorted_nodup, sorted_relax.
  introv HSl HSr.
  forwards: merge_sorted HSl HSr...
Qed.

(* record types *)
Lemma rcd_typ_concat_simpl : forall T1 T2,
    rec_typ T1 -> rec_typ T2 ->
    rec_typ (ttyp_concat_simpl T1 T2).
Proof with eauto.
  introv WF1 WF2.
  induction WF1...
  - simpl...
Qed.

Lemma translate_to_record_types : forall A,
    rec_typ |[ A ]|.
Proof with eauto using rcd_typ_concat_simpl.
  introv. induction A; simpl; try case_if; simpl...
Qed.

#[local] Hint Resolve translate_to_record_types : core.


#[local] Hint Resolve lookup_wf_typ_3 wf_typ_look_up_wf : core.


Lemma lookup_concat_simpl_destruct : forall l B1 B2,
    Tlookup l (ttyp_concat_simpl |[ B1 ]| |[ B2 ]|) = Tlookup l |[ B1 ]| \/
    Tlookup l (ttyp_concat_simpl |[ B1 ]| |[ B2 ]|) = Tlookup l |[ B2 ]|.
Proof.
  introv. remember (Tlookup l |[ B1 ]|). destruct o.
  - forwards* Heq: lookup_concat_simpl  (|[ B1 ]|) (|[ B2 ]|).
    rewrite Heq. rewrite* <- Heqo.
  - forwards* Heq: lookup_concat_simpl_none  (|[ B1 ]|) (|[ B2 ]|).
Qed.


Ltac destruct_lookup H :=
      match type of H with
    | Tlookup ?l (ttyp_rcd ?l ?A ?C) = _  =>
        simpl in H; case_if
    | Tlookup ?r (ttyp_rcd ?l ?A ?C) = _  =>
        let Heq := fresh "Heq" in
        lets [Heq|Heq]: lookup_wf_typ_1 l A C r;
        [ rewrite Heq in H; clear Heq | subst ]
      |  Tlookup _ (ttyp_concat_simpl |[ ?A ]| |[ ?B ]|) = _ =>
           let Heq := fresh "Heq" in
           lets [Heq|Heq]: lookup_concat_simpl_destruct A B;
           rewrite Heq in H
      end.



(* translate *)
From Ltac2 Require Ltac2.

(** magic from https://coq.discourse.group/t/force-application-of-fixpoint-to-its-argument/1190/8 **)
Module Ltac2Magic.
  Import Ltac2 Constr.

  Ltac2 reveal_fixpoint fn :=
    match Unsafe.kind fn with
    | Unsafe.Constant cst _ =>
      Std.eval_unfold [(Std.ConstRef cst, Std.AllOccurrences)] fn
    | _ => Control.throw Not_found
    end.

  Ltac2 unfold_fixpoint_once fn :=
    let fixpoint := reveal_fixpoint fn in
    match Unsafe.kind fixpoint with
    | Unsafe.Fix _ _ binders bodies =>
      let binder := Array.get binders 0 in
      let unbound_body := Array.get bodies 0 in
      let body := Unsafe.substnl [fn] 0 unbound_body in
      match Unsafe.check body with
      | Val b => b
      | Err error => Control.throw error
      end
    | _ => Control.throw Not_found
    end.

  Notation unfold_fixpoint_once fn :=
    ltac2:(let fn := Constr.pretype fn in
           let fn := unfold_fixpoint_once fn in exact $fn) (only parsing).
End Ltac2Magic.

Notation beta x :=
  ltac:(let x := (eval cbv beta in x) in exact x) (only parsing).

Lemma styp2ttyp_eqn : forall A,
    styp2ttyp A =
    beta((Ltac2Magic.unfold_fixpoint_once styp2ttyp) A).
Proof. intros; destruct A; reflexivity. Qed.

Lemma ttyp_trans_ord_top : forall A,
    check_toplike A = true -> |[A]| = ttyp_top.
Proof with simpl; eauto.
  introv HC.
  rewrite styp2ttyp_eqn. rewrite* HC.
Qed.

#[local] Hint Resolve ttyp_trans_ord_top : core.

(* Lemma foldl_append_singleton_list : forall T, *)
(*     list_string_2_string [T] = T. *)
(* Proof. *)
(*   introv. simpl. eauto. *)
(* Qed. *)

Lemma stype2string_toplike : forall A,
    check_toplike A = true -> (styp2tindex A) = nil.
Proof with eauto.
  introv HT.
  destruct A; simpl in HT; try discriminate; simpl...
  all: rewrite* HT.
Qed.

Lemma nodup_nil_rev : forall l : list tindex,
    nodup tindex_dec l = nil -> l = nil.
Proof.
  introv HE. induction* l.
  - simpl in HE. case_if*. forwards: IHl HE. subst.
    inverts C.
Qed.

Lemma list_app_nil_inv : forall l1 l2 : list tindex,
    (l1 ++ l2) %list = nil -> l1 = nil /\ l2 = nil.
Proof.
  introv HE. destruct l1; destruct* l2; try discriminate.
Qed.

Lemma stype2string_toplike_inv : forall A,
    (styp2tindex A) = nil -> check_toplike A = true.
Proof with eauto using Permutation_sym.
  introv HT.
  induction* A;  simpl in HT; try case_if; try discriminate; simpl...
  - inverts HT. apply nodup_nil_rev in H0.
    forwards: Permuted_merge (styp2tindex A1) (styp2tindex A2). rewrite H0 in H.
    forwards: Permutation_nil ((styp2tindex A1) ++ (styp2tindex A2))%list...
    forwards (?&?): list_app_nil_inv H1.
    forwards*: IHA1. forwards*: IHA2.
    rewrite H4. rewrite* H5.
Qed.

Lemma stype2string_and : forall A B : typ,
    styp2tindex (typ_and A B) = nodup tindex_dec (merge (styp2tindex A) (styp2tindex B)).
Proof.
  introv. simpl.
  destruct (check_toplike A) eqn:HA. destruct (check_toplike B) eqn:HB.
  all: try ( rewrite (stype2string_toplike A); [ | eassumption] ).
  all: try ( rewrite (stype2string_toplike B); [ | eassumption] ).
  all: autorewrite with merge; simpl; eauto.
Qed.

Lemma typeindex_sorted: forall A,
    sorted (styp2tindex A).
Proof with eauto.
  introv. induction* A; simpl...
  all: unfolds...
  all: try econstructor...
  - case_if...
  - case_if... applys* merge_sorted_dedup.
  - case_if...
Qed.

Lemma NoDup_single : forall (x:tindex), NoDup [x].
Proof.
  introv. applys NoDup_count_occ tindex_dec. intros.
  simpl. case_if*.
Qed.

Lemma typeindex_nodup: forall A,
    NoDup (styp2tindex A).
Proof with eauto using NoDup_nil, NoDup_single, NoDup_nodup.
  introv. destruct* A; simpl; try case_if*...
Qed.

Lemma nodup_empty_inv : forall l,
    nodup tindex_dec l = nil -> l = nil.
Proof.
  introv HE. induction* l.
  simpl in HE. case_if.
  exfalso. forwards~: IHl. subst. inverts C.
Qed.

Lemma merge_empty_inv : forall l r,
    merge l r = nil -> l = nil /\ r = nil.
Proof.
  introv HE. destruct* l; destruct* r.
  simpl in HE. case_if.
Qed.

Lemma stype2string_toplike_complete : forall A,
    styp2tindex A = nil -> toplike A.
Proof with eauto.
  introv HT. apply check_toplike_sound_complete.
  induction A; simpl in HT; try discriminate; try case_if; simpl...
  apply nodup_empty_inv in HT.
  forwards (?&?): merge_empty_inv HT.
  forwards~: IHA1. forwards~: IHA2. rewrite H1. rewrite* H2.
Qed.

(* refine subtype *)
Lemma S_refl : forall A, sub A A.
Proof.
  introv. induction* A.
Qed.

Lemma ST_top: forall A, subTarget |[ A ]| ttyp_top.
Proof with simpl in *; discriminate.
  introv. applys* ST_rcd.
  intros...
Qed.


Lemma ST_inv : forall A B,
    subTarget |[ A ]| |[ B ]| ->
    forall l Ct, Tlookup l |[ B ]| = Some Ct -> exists Ct', Tlookup l |[ A ]| = Some Ct' /\ subTarget Ct' Ct  /\ subTarget Ct Ct'.
Proof.
  introv HA.  inverts* HA.
  - introv HL. forwards*: H1 HL.
Qed.

Lemma ST_andl : forall A B, subTarget |[ (typ_and A B) ]| |[ A ]|.
Proof with unify_lookup; intuition eauto.
  introv. applys* ST_rcd.
  introv HL. simpl. case_if*. apply andb_prop in C...
  - forwards: ttyp_trans_ord_top H...
  - forwards: lookup_concat_simpl HL. rewrite H. rewrite HL...
Qed.

#[local] Hint Resolve ST_top ST_rcd_2 ST_refl ST_andl subTarget_rec_typ : core.

(* soundness of sub to type index translation function *)

Lemma incl_single: forall (x y : string), incl [x] [y] -> x = y.
Proof.
  introv HI.
  apply incl_Forall_in_iff in HI.
  apply Forall_inv in HI.
  apply in_one_iff in HI. eauto.
Qed.

Lemma incl_eq : forall (l1 l2 : list tindex), l1 = l2 -> incl l1 l2.
Proof.
  introv Heq. rewrite Heq. applys* incl_refl.
Qed.

Lemma incl_eq_tindex: forall A B,
    incl (styp2tindex A) (styp2tindex B) -> incl (styp2tindex B) (styp2tindex A)
    -> (styp2tindex A) = (styp2tindex B).
Proof with eauto using typeindex_nodup, typeindex_sorted.
  introv HA HB.
  forwards: NoDup_Permutation_bis HA...
  apply NoDup_incl_length in HB...
  applys sorted_unique...
Qed.

Lemma incl_nodup_merge : forall A1 A2,
    incl ((styp2tindex A1) ++ (styp2tindex A2)) (nodup tindex_dec (merge (styp2tindex A1) (styp2tindex A2))).
Proof.
  introv. apply nodup_incl.
  forwards: Permuted_merge (styp2tindex A1) (styp2tindex A2).
  applys incl_Forall_in_iff. applys Forall_forall. introv HI.
  applys Permutation_in H HI.
Qed.

Theorem nodup_incl2: forall {A: Type} (decA: forall x y: A, {x = y} + {x <> y}) (l1 l2: list A),
    incl l1 l2 -> incl (nodup decA l1) l2.
Proof.
  introv HI. applys incl_tran l1.
  applys nodup_incl. applys incl_refl. eauto.
Qed.

Lemma incl_nodup_merge_rev : forall A1 A2,
    incl (nodup tindex_dec (merge (styp2tindex A1) (styp2tindex A2))) ((styp2tindex A1) ++ (styp2tindex A2)).
Proof.
  introv. applys (nodup_incl2 tindex_dec).
  forwards: Permuted_merge (styp2tindex A1) (styp2tindex A2).
  applys incl_Forall_in_iff. applys Forall_forall. introv HI.
  apply Permutation_sym in H. applys Permutation_in H HI.
Qed.


Lemma eqIndTyp_complete_alt_gen : forall A B,
    incl (styp2tindex B) (styp2tindex A) -> sub A B.
Proof with eauto using incl_tran, incl_appl, incl_appr, incl_nil.
  introv HE. indTypSize (size_typ A + size_typ B).
  destruct B; intros; eauto.
  - simpl in HE.
    apply incl_Forall_in_iff in HE.
    apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert ( incl (styp2tindex typ_bot) (styp2tindex A1) ). {
          simpl. unfolds. intros. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
      * assert ( incl (styp2tindex typ_bot) (styp2tindex A2) ). {
          simpl. unfolds. intros. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
  - simpl in HE.
    apply incl_Forall_in_iff in HE.
    apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert ( incl (styp2tindex typ_base) (styp2tindex A1) ). {
          simpl. unfolds. intros. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
      * assert ( incl (styp2tindex typ_base) (styp2tindex A2) ). {
          simpl. unfolds. intros. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
  - simpl in HE; try case_if.
    { rewrite <- check_toplike_sound_complete in C... }
    try apply incl_Forall_in_iff in HE.
    try apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + (* arrow vs arrow *)
      simpl in HE. case_if.
      inverts* HE; try solve_by_invert.
      repeat (find_injection; intros).
      forwards: IH B1 A1; eauto using incl_eq. elia.
      forwards: IH A1 B1; eauto using incl_eq. elia.
      forwards: IH A2 B2; eauto using incl_eq. elia.
      forwards: IH B2 A2; eauto using incl_eq. elia.
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert ( incl (styp2tindex (typ_arrow B1 B2)) (styp2tindex A1) ). {
          simpl. unfolds. intros. case_if. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
      * assert ( incl (styp2tindex (typ_arrow B1 B2)) (styp2tindex A2) ). {
          simpl. unfolds. intros. case_if. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
  - assert (incl (styp2tindex B1) (styp2tindex (typ_and B1 B2))). {
      simpl. case_if. { forwards (?&?): andb_prop C. rewrite* stype2string_toplike. eauto...  }
      applys incl_tran. 2: applys incl_nodup_merge. applys incl_appl. applys incl_refl.
    }
    assert (incl (styp2tindex B2) (styp2tindex (typ_and B1 B2))). {
      simpl. case_if. { forwards (?&?): andb_prop C. rewrite* stype2string_toplike. eauto...  }
      applys incl_tran. 2: applys incl_nodup_merge. applys incl_appr. applys incl_refl.
    }
    forwards: incl_tran H HE. forwards: incl_tran H0 HE.
    forwards*: IH A B1. elia. forwards*: IH A B2. elia.
  - simpl in HE; try case_if.
    { rewrite <- check_toplike_sound_complete in C... }
    try apply incl_Forall_in_iff in HE.
    try apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert (incl (styp2tindex (typ_rcd l B)) (styp2tindex A1)). {
         simpl. unfolds. intros. case_if. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
      * assert (incl (styp2tindex (typ_rcd l B)) (styp2tindex A2)). {
         simpl. unfolds. intros. case_if. inverts* H0; try solve_by_invert.
        }
        forwards*: IH H0. elia.
    + simpl in HE. case_if. inverts* HE; try solve_by_invert.
      repeat (find_injection; intros). subst.
      forwards: IH B A; eauto using incl_eq. elia.
      forwards*: IH A B; eauto using incl_eq. elia.
Qed.

Corollary eqIndTyp_complete : forall A B,
    styp2tindex A = styp2tindex B -> sub A B /\ sub B A.
Proof with eauto using incl_refl.
  introv HE.
  split; applys eqIndTyp_complete_alt_gen.
  rewrite HE... rewrite <- HE...
Qed.

(* topLike specification eqv *)
Theorem toplike_super_top: forall A,
    toplike A <-> sub typ_top A.
Proof with eauto.
  split; intros H.
  - induction A...
  - inductions H...
Qed.

Corollary super_top_toplike : forall A,
    sub typ_top A -> toplike A.
Proof.
  intros. apply toplike_super_top.
  eauto.
Qed.

Lemma toplike_covariance : forall A B,
    toplike A -> sub A B -> toplike B.
Proof with eauto using toplike_super_top.
  introv HT HS.
  induction* HS...
  all: inverts* HT.
Qed.

Definition disjointSpec A B :=
  forall C, sub A C -> sub B C -> toplike C.

Lemma disjoint_andl_inv: forall A1 A2 B,
    disjoint (typ_and A1 A2) B -> disjoint A1 B /\ disjoint A2 B.
Proof.
  introv HD. inductions HD; eauto.
  all: try solve [inverts* H].
  - forwards*: IHHD1. forwards*: IHHD2.
Qed.

Lemma disjoint_andr_inv: forall B A1 A2,
    disjoint B (typ_and A1 A2) -> disjoint B A1 /\ disjoint B A2.
Proof.
  introv HD. inductions HD; eauto.
  all: try solve [inverts* H].
  - forwards*: IHHD1. forwards*: IHHD2.
Qed.

Lemma disjoint_symm: forall A B,
    disjoint B A -> disjoint A B.
Proof.
  introv HD. induction HD; eauto.
Qed.


Lemma disjoint_sub_conflict_1 : forall A B,
    disjoint A B -> sub A B -> toplike B.
Proof with try solve_by_invert; eauto using super_top_toplike.
  introv HD HS. induction HS...
  all: try solve [ inverts* HD ].
  all: try solve [ inverts* HD ; inverts* H ].
  - inverts* HD. inverts* H. false* H0.
  - forwards*: disjoint_andl_inv HD.
  - forwards*: disjoint_andl_inv HD.
  - forwards*: disjoint_andr_inv HD.
Qed.

Lemma disjoint_sub_conflict_2 : forall A B,
    disjoint B A -> sub A B -> toplike B.
Proof with eauto using disjoint_symm.
  introv HD HS.
  applys disjoint_sub_conflict_1 HS...
Qed.

Lemma disjoint_covariance : forall A B C,
    disjoint A B -> sub A C -> disjoint C B.
Proof with eauto using disjoint_symm.
  introv HD HS.
  gen A C. induction B; intros...
  - induction* HS;
      try forwards* (?&?): disjoint_andl_inv HD.
    + inverts* HD.
      eauto using toplike_covariance.
    + inverts* HD.
      eauto using toplike_covariance.
  - induction* HS;
      try forwards* (?&?): disjoint_andl_inv HD.
  - induction* HS;
      try forwards* (?&?): disjoint_andl_inv HD.
    inverts* HD.
    + eauto using toplike_covariance.
  - forwards* (?&?): disjoint_andr_inv HD.
  - induction* HS;
      try forwards* (?&?): disjoint_andl_inv HD.
    inverts* HD.
    + eauto using toplike_covariance.
Qed.

Theorem disjoint_soundness : forall A B,
    disjoint A B -> disjointSpec A B.
Proof.
  introv HD. unfold disjointSpec.
  intros.
  forwards HD1: disjoint_covariance HD H.
  forwards*: disjoint_sub_conflict_2 HD1.
Qed.

Theorem disjoint_completeness : forall A B,
    disjointSpec A B -> disjoint A B.
Proof.
  introv HD. unfold disjointSpec in HD.
  induction* A.
  - assert (toplike B).
    applys* HD. Search (sub typ_bot _).
  induction* B.


Corollary st_eq_disjoint : forall A B,
    || A || = || B || -> disjoint A B -> toplike A /\ toplike B.
Proof with try solve_by_invert.
  introv HE HD.
  forwards*: eqIndTyp_complete A B.
  - inverts* HE.
  - destruct H. split; eauto using disjoint_sub_conflict_1, disjoint_sub_conflict_2.
Qed.

Lemma eqIndTyp_sound_alt_gen : forall A B,
    sub A B -> incl (styp2tindex B) (styp2tindex A).
Proof with eauto using incl_nil, incl_nodup_merge, NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  introv HS.
  induction HS; try solve [simpl; eauto using incl_refl].
  - rewrite check_toplike_sound_complete in H. rewrite* stype2string_toplike...
  - simpl. case_if. applys incl_nil.
    case_if. {
      forwards*: stype2string_toplike A2...
      forwards*: incl_eq_tindex A2 B2. rewrite H0 in H.
      forwards*: stype2string_toplike_inv H. rewrite H1 in C. discriminate.
    }
    applys incl_eq.
    forwards*: incl_eq_tindex A1 B1. forwards*: incl_eq_tindex A2 B2.
    rewrite H. rewrite H0...
  - simpl. case_if. applys incl_nil.
    case_if. {
      forwards*: stype2string_toplike A...
      forwards*: incl_eq_tindex A B. rewrite H0 in H.
      forwards*: stype2string_toplike_inv H. rewrite H1 in C. discriminate.
    }
    applys incl_eq.
    forwards*: incl_eq_tindex A B.
    rewrite* H.
  - applys incl_tran IHHS.
    simpl. case_if.
    { forwards* (?&?): andb_prop C. rewrite* stype2string_toplike...  }
    applys incl_tran incl_nodup_merge...
    applys incl_appl. applys incl_refl.
  - applys incl_tran IHHS.
    simpl. case_if.
    { forwards* (?&?): andb_prop C. rewrite* stype2string_toplike...  }
    applys incl_tran incl_nodup_merge...
    applys incl_appr. applys incl_refl.
  - simpl. case_if. applys incl_nil.
    applys incl_tran incl_nodup_merge_rev.
    applys* incl_app.
Qed.

Corollary eqIndTyp_sound_alt : forall B A,
    sub B A -> sub A B -> styp2tindex B = styp2tindex A.
Proof.
  introv HS1 HS2.
  apply eqIndTyp_sound_alt_gen in HS1.
  apply eqIndTyp_sound_alt_gen in HS2.
  applys* incl_eq_tindex.
Qed.

(* sub target for eq index target *)

Lemma and_inversion : forall A B C,
    sub A (typ_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  inductions H; eauto.
  - inverts* H.
  - forwards*: IHsub B C.
  - forwards*: IHsub B C.
Qed.

Lemma toplike_sub: forall A B,
    toplike A -> sub A B -> toplike B.
Proof.
  introv TL S.
  induction S; inverts* TL. all: forwards~: IHS1.
Qed.

Lemma sub_eqv_toplike : forall A B,
    sub B A -> sub A B -> check_toplike B = check_toplike A.
Proof with try rewrite* <- check_toplike_sound_complete.
  introv HA HB. case_eq (check_toplike A == true); intros.
  - rewrite e...
    applys~ toplike_sub A.
    rewrite* check_toplike_sound_complete.
  - clear H. forwards: not_true_is_false n. rewrite H...
    apply not_true_is_false. intros HT.
    applys n...
    applys~ toplike_sub B.
    rewrite* check_toplike_sound_complete.
Qed.

Lemma Tlookup_eq : forall l l' A B,
    Tlookup l (ttyp_rcd l' A ttyp_top) = Some B -> l = l' /\ A = B.
Proof.
  introv HL. simpl in HL. case_if*. inverts* HL.
Qed.

(* Key property *)
Lemma sub_source2target_aux : forall A B l T T',
    (Tlookup l (|[ A ]|) = Some T -> Tlookup l (|[ B ]|) = Some T' -> subTarget T T') /\
    (sub A B -> subTarget |[A]| |[B]|).
Proof with try rewrite* <- check_toplike_sound_complete; simpl in *; try case_if; try discriminate; eauto using translate_to_record_types, rcd_typ_concat_simpl.
  introv. gen l. indTypSize (size_typ A + size_typ B).
  split.
  { destruct A; introv HA HB. 1-3: clear IH.
  - rewrite* (ttyp_trans_ord_top) in HA...
  - simpl in HA. case_if. inverts HA. rewrite C in HB.
    induction B...
    + inverts HB...
    + destruct_lookup HB. forwards*: IHB1. elia. forwards*: IHB2. elia.
  - (* base *) simpl in HA. case_if. inverts HA. rewrite C in HB.
    induction B...
    + inverts HB...
    + destruct_lookup HB. forwards*: IHB1. elia. forwards*: IHB2. elia.
  - (* arrow *) simpl in HA. case_if. inverts HA. case_if.
    rewrite C0 in HB.
    induction B...
    + forwards (?&?): Tlookup_eq HB. inverts H0. rewrite <- H1.
      inverts H. subst.
      forwards (HS1&HS2): eqIndTyp_complete H2. forwards (HS3&HS4): eqIndTyp_complete H3.
      forwards~ (_&HS1'): IH A1 B1. elia. forwards~: HS1'.
      forwards~ (_&HS2'): IH B1 A1. elia. forwards~: HS2'.
      forwards~ (_&HS3'): IH A2 B2. elia. forwards~: HS3'.
      forwards~ (_&HS4'): IH B2 A2. elia.
    + destruct_lookup HB. forwards*: IHB1. elia. forwards*: IHB2. elia.
  - (* and *) simpl in HA. case_if. destruct_lookup HA.
    + forwards* (?&_): IH A1 B. elia. + forwards* (?&_): IH A2 B. elia.
  - (* rcd *) simpl in HA. case_if. inverts HA. case_if.
    rewrite C0 in HB.
    induction B...
    + destruct_lookup HB. forwards*: IHB1. elia. forwards*: IHB2. elia.
    + forwards (?&?): Tlookup_eq HB. inverts H0. rewrite <- H1.
      inverts H.
      forwards (HS1&HS2): eqIndTyp_complete H3.
      forwards* (_&HS1'): IH A B. elia.
  }

  { introv HS.
    destruct HS. all: try solve [simpl; eauto].
    - rewrite* (ttyp_trans_ord_top B)...
    - simpl. case_if*; simpl; case_if*.
      { forwards* HSE: sub_eqv_toplike B2 A2. rewrite C0 in HSE. rewrite C in HSE. discriminate. }
      { forwards* HSE: sub_eqv_toplike B2 A2. rewrite C0 in HSE. rewrite C in HSE. discriminate. }
      +
        rewrite* (eqIndTyp_sound_alt A1 B1). rewrite* (eqIndTyp_sound_alt A2 B2).
        applys ST_rcd... introv HL. simpl in HL. case_if*.
        subst. exists. injection HL. intro HE. subst*...
        splits*; applys ST_arrow.
        all: applys IH; try eassumption; elia.
    - simpl. case_if*; simpl; case_if*.
      { forwards* HSE: sub_eqv_toplike B A. rewrite C0 in HSE. rewrite C in HSE. discriminate. }
      { forwards* HSE: sub_eqv_toplike B A. rewrite C0 in HSE. rewrite C in HSE. discriminate. }
      +
        rewrite* (eqIndTyp_sound_alt A B).
        applys ST_rcd... introv HL. simpl in HL. case_if*.
        subst. exists. injection HL. intro HE. subst*...
        splits*;
        forwards* (_&?): IH A B; elia.
        all: applys IH; try eassumption; elia.
    - forwards* (_&?): IH A1 A3. elia. applys* ST_trans.
    - forwards* (_&IHHS'): IH A2 A3. elia. forwards~ IHHS: IHHS'.
      applys* ST_trans IHHS. clear HS.
      { applys* ST_rcd.
        introv HL. simpl. case_if*. apply andb_prop in C; unify_lookup; intuition eauto.
        - forwards: ttyp_trans_ord_top H0; unify_lookup; intuition eauto.
        - remember (check_toplike A1). destruct b.
          + forwards*: ttyp_trans_ord_top A1; unify_lookup; intuition eauto.
            rewrite H. simpl; unify_lookup; intuition eauto.
          + remember (Tlookup l0 |[A1]|). destruct o.
            * forwards*: lookup_concat_simpl (|[ A1 ]|) (|[ A2 ]|). rewrite H.
              rewrite <- Heqo; unify_lookup. exists t. split.
              now eauto. splits.
              forwards (IH1&_): IH A1 A2; elia. applys* IH1.
              forwards (IH1&_): IH A2 A1; elia. applys* IH1.
            * forwards*: lookup_concat_simpl_none (|[ A1 ]|) (|[ A2 ]|). rewrite H.
              rewrite* HL.
      }
    - simpl. case_if*.
      forwards* (_&IHHS1'): IH A1 A2. elia. forwards~ IHHS1: IHHS1'. clear IHHS1'.
      forwards* (_&IHHS2'): IH A1 A3. elia. forwards~ IHHS2: IHHS2'. clear IHHS2'.
      + applys ST_rcd... introv HL.
        destruct_lookup HL.
        * forwards* (?&?&?): ST_inv IHHS1.
      * forwards* (?&?&?): ST_inv IHHS2.
  }
  Unshelve. all: econstructor.
Qed.

(* same label means same type in any translation *)
Lemma lookup_sub : forall A B l T T',
    Tlookup l (|[ A ]|) = Some T -> Tlookup l (|[ B ]|) = Some T' -> subTarget T T'.
Proof.
  introv. forwards (?&_): sub_source2target_aux. applys H.
Qed.

Lemma sub_source2target : forall A B,
    sub A B -> subTarget |[A]| |[B]|.
Proof.
  introv. forwards (_&?): sub_source2target_aux. applys H.
  Unshelve. all: econstructor.
Qed.

Lemma ST_andr : forall A B, subTarget |[ (typ_and A B) ]| |[ B ]|.
Proof with unify_lookup; intuition eauto.
  introv. applys* ST_rcd.
  introv HL. simpl. case_if*. apply andb_prop in C...
  - forwards: ttyp_trans_ord_top H0...
  - remember (check_toplike A). destruct b.
    + forwards*: ttyp_trans_ord_top A... rewrite H. simpl...
    + remember (Tlookup l |[A]|). destruct o.
      * forwards*: lookup_concat_simpl (|[ A ]|) (|[ B ]|). rewrite H.
        rewrite <- Heqo... exists*. splits*.
        all: applys* lookup_sub.
      * forwards*: lookup_concat_simpl_none (|[ A ]|) (|[ B ]|). rewrite H.
        rewrite* HL.
Qed.

Lemma ST_toplike : forall A,
    toplike A -> subTarget ttyp_top |[A]|.
Proof.
  introv TL. rewrite ttyp_trans_ord_top. applys ST_refl.
  rewrite* <- check_toplike_sound_complete.
Qed.

Lemma ttyp_concat_simpl_nils : forall A1 A2,
    |[ (typ_and A1 A2) ]| = ttyp_concat_simpl |[ A1 ]| |[ A2 ]|.
Proof.
  introv. simpl. case_if*.
  forwards (?&?): andb_prop C.
  apply ttyp_trans_ord_top in H. apply ttyp_trans_ord_top in H0.
  rewrite H. rewrite H0. eauto.
Qed.

Lemma concat_source_intersection : forall A B,
    wf_typ |[ A ]| -> wf_typ |[ B ]| -> concat_typ |[ A ]| |[ B ]| |[ (typ_and A B) ]|.
Proof with eauto using translate_to_record_types.
  introv HW1 HW2. forwards: concat_typ_exists (|[ A ]|) (|[ B ]|)...
  introv HLa HLb. intuition eauto using lookup_sub...
  rewrite ttyp_concat_simpl_nils...
Qed.

Lemma ttyp_concat_simpl_assoc : forall A B C,
    rec_typ A -> rec_typ B -> rec_typ C ->
    (ttyp_concat_simpl (ttyp_concat_simpl A B) C) = ttyp_concat_simpl A (ttyp_concat_simpl B C).
Proof with simpl in *; eauto.
  introv HRA HRB HRC.
  induction HRA...
  rewrite IHHRA...
Qed.


Lemma ttyp_trans_wf : forall A,
    wf_typ |[A]|.
Proof with intuition eauto using rcd_typ_concat_simpl, translate_to_record_types.
  introv.
  induction A; simpl; repeat case_if; simpl...
  - applys wf_rcd_concat IHA1 IHA2...
    rewrite <- ttyp_concat_simpl_nils.
    forwards*: concat_source_intersection IHA1 IHA2.
    Unshelve. all: econstructor.
Qed.

(* Properties of translation (to target type) functions *)

Lemma ttyp_trans_ord_ntop : forall A,
    ord A -> check_toplike A = false -> exists B, |[A]| = (ttyp_rcd (||A||) B ttyp_top) /\ wf_typ B.
Proof with eauto using ttyp_trans_wf.
  introv HO HT. induction* HO;
    try solve [simpl in HT; discriminate].
  - exists. split*. simpl...
  - simpl in HT. forwards* (?&?&?): IHHO.
    exists. simpl. case_if. split*. econstructor...
  - simpl in HT. forwards* (?&?&?): IHHO.
    exists. simpl. case_if. split*...
Qed.

Lemma ttyp_trans_base :
    |[typ_base]| = ttyp_rcd (||typ_base||) ttyp_base ttyp_top.
Proof with eauto.
  introv. simpl...
Qed.

Lemma ttyp_trans_ord_ntop_arrow : forall A' A,
(* ord A -> ~ toplike A -> *) (* S-arrow requires no precondition *)
    check_toplike A = false -> |[(typ_arrow A' A)]| = ttyp_rcd (||typ_arrow A' A||) (ttyp_arrow |[A']| |[A]|) ttyp_top.
Proof with eauto.
  introv HT. simpl in HT. simpl. case_if*.
Qed.


Lemma ttyp_trans_rcd : forall l A,
    ~ toplike A ->
|[(typ_rcd l A)]| = ttyp_rcd (||(typ_rcd l A)||) |[A]| ttyp_top.
Proof with eauto.
  introv HT. simpl in HT. simpl. case_if*.
  exfalso. apply HT. applys~ check_toplike_sound_complete.
Qed.
