Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Import IfNotations.
Require Import StructTact.StringOrders.
Require Export syntax_ott.
Require Export Infrastructure.
Require Import TargetTypeSafety.

(* Assumptions on the translation function *)
Lemma st_eq_arrow : forall A1 A2 B1 B2,
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_arrow A1 A2) || =  || (typ_arrow B1 B2) || -> || B1 || = || A1 || /\ || B2 || = || A2 ||.
Admitted.

Lemma st_eq_rcd : forall A2 B2 l l',
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_rcd l A2) || =  || (typ_rcd l' B2) || -> l = l' /\ || B2 || = || A2 ||.
Admitted.

(* merge, sort *)
Lemma HdRel_relax : forall a l,
    HdRel lex_lt a l -> HdRel NOTF.le a l.
Proof with eauto.
  introv HS. induction* HS. constructor...
  left*.
Qed.

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
      if if proj1_sig (string_compare_lex a b) is Gt then false else true then a :: merge l (b::r) else b :: merge (a::l) r.
Proof with eauto.
  introv. induction* l; destruct (proj1_sig (string_compare_lex a b)); autorewrite with merge...
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

Lemma merge_sorted_dedup: forall l r,
    sorted l -> sorted r -> sorted (nodup string_dec (merge l r)).
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

Lemma foldl_append_singleton_list : forall T,
    list_string_2_string [T] = T.
Proof.
  introv. simpl. eauto.
Qed.

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

Lemma stype2string_toplike : forall A,
    check_toplike A = true -> || A || = nil.
Proof with eauto.
  introv HT.
  destruct A; simpl in HT; try discriminate; simpl...
  all: rewrite* HT.
Qed.

Lemma nodup_nil_rev : forall l : list string,
    nodup string_dec l = nil -> l = nil.
Proof.
  introv HE. induction* l.
  - simpl in HE. case_if*. forwards: IHl HE. subst.
    inverts C.
Qed.

Lemma list_app_nil_inv : forall l1 l2 : list string,
    (l1 ++ l2) %list = nil -> l1 = nil /\ l2 = nil.
Proof.
  introv HE. destruct l1; destruct* l2; try discriminate.
Qed.

Lemma stype2string_toplike_inv : forall A,
    || A || = nil -> check_toplike A = true.
Proof with eauto using Permutation_sym.
  introv HT.
  induction* A;  simpl in HT; try case_if; try discriminate; simpl...
  - apply nodup_nil_rev in HT.
    forwards: Permuted_merge (|| A1 ||) (|| A2 ||). rewrite HT in H.
    forwards: Permutation_nil (|| A1 || ++ || A2 ||)%list...
    forwards (?&?): list_app_nil_inv H0.
    forwards*: IHA1. forwards*: IHA2. rewrite H3. rewrite* H4.
Qed.

Lemma stype2string_and : forall A B : typ,
    || typ_and A B || = nodup string_dec (merge (stype2string A) (stype2string B)).
Proof.
  introv. simpl.
  destruct (check_toplike A) eqn:HA. destruct (check_toplike B) eqn:HB.
  all: try ( rewrite (stype2string_toplike A); [ | eassumption] ).
  all: try ( rewrite (stype2string_toplike B); [ | eassumption] ).
  all: autorewrite with merge; simpl; eauto.
Qed.

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

Lemma NoDup_single : forall (x:string), NoDup [x].
Proof.
  introv. applys NoDup_count_occ string_dec. intros.
  simpl. case_if*.
Qed.

Lemma typeindex_nodup: forall A,
    NoDup (|| A ||).
Proof with eauto using NoDup_nil, NoDup_single, NoDup_nodup.
  introv. destruct* A; simpl; try case_if*...
Qed.


Lemma nodup_empty_inv : forall l,
    nodup string_dec l = nil -> l = nil.
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
    || A || = nil -> toplike A.
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

Lemma incl_eq : forall (l1 l2 : list string), l1 = l2 -> incl l1 l2.
Proof.
  introv Heq. rewrite Heq. applys* incl_refl.
Qed.

Lemma incl_eq_tindex: forall A B,
    incl (||A||) (||B||) -> incl (||B||) (||A||) -> ||A|| = ||B||.
Proof with eauto using typeindex_nodup, typeindex_sorted.
  introv HA HB.
  forwards: NoDup_Permutation_bis HA...
  apply NoDup_incl_length in HB...
  applys sorted_unique...
Qed.

Lemma incl_nodup_merge : forall A1 A2,
    incl ((|| A1 ||) ++ (|| A2 ||)) (nodup string_dec (merge (|| A1 ||) (|| A2 ||))).
Proof.
  introv. apply nodup_incl.
  forwards: Permuted_merge (|| A1 ||) (|| A2 ||).
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
    incl (nodup string_dec (merge (|| A1 ||) (|| A2 ||))) ((|| A1 ||) ++ (|| A2 ||)).
Proof.
  introv. applys (nodup_incl2 string_dec).
  forwards: Permuted_merge (|| A1 ||) (|| A2 ||).
  applys incl_Forall_in_iff. applys Forall_forall. introv HI.
  apply Permutation_sym in H. applys Permutation_in H HI.
Qed.

Lemma st_eq1 : forall A1 A2 B1 B2,
    check_toplike A2 = false -> check_toplike B2 = false ->
    || B1 || ++
        String (Ascii.Ascii true false true true false true false false)
          (String (Ascii.Ascii false true true true true true false false) (|| B2 || ++ ")")) =
        || A1 || ++
        String (Ascii.Ascii true false true true false true false false)
        (String (Ascii.Ascii false true true true true true false false) (|| A2 || ++ ")"))
    -> || B1 || = || A1 ||.
Proof.
  intros.
  forwards*: st_eq_arrow A1 A2 B1 B2.
  case_if*. case_if*. rewrite* H1.
Qed.

Lemma st_eq2 : forall A1 A2 B1 B2,
    check_toplike A2 = false -> check_toplike B2 = false ->
    || B1 || ++
        String (Ascii.Ascii true false true true false true false false)
          (String (Ascii.Ascii false true true true true true false false) (|| B2 || ++ ")")) =
        || A1 || ++
        String (Ascii.Ascii true false true true false true false false)
        (String (Ascii.Ascii false true true true true true false false) (|| A2 || ++ ")"))
      -> || B2 || = || A2 ||.
Proof.
  intros.
  forwards*: st_eq_arrow A1 A2 B1 B2.
  case_if*. case_if*. rewrite* H1.
Qed.

Lemma st_eq3 : forall A B l l0,
    check_toplike A = false -> check_toplike B = false ->
 l ++
        String (Ascii.Ascii true false true true true true false false)
          (String (Ascii.Ascii false true true true true true false false) (|| B || ++ "}")) =
        l0 ++
        String (Ascii.Ascii true false true true true true false false)
        (String (Ascii.Ascii false true true true true true false false) (|| A || ++ "}"))
        -> || B || = || A ||.
Proof.
  intros.
  forwards*: st_eq_rcd A B l0 l.
  case_if*. case_if*. rewrite* H1.
Qed.

Lemma st_eq4: forall A B l l0,
    check_toplike A = false -> check_toplike B = false ->
 l ++
        String (Ascii.Ascii true false true true true true false false)
          (String (Ascii.Ascii false true true true true true false false) (|| B || ++ "}")) =
        l0 ++
        String (Ascii.Ascii true false true true true true false false)
        (String (Ascii.Ascii false true true true true true false false) (|| A || ++ "}"))
        -> l = l0.
Proof.
  intros.
  forwards*: st_eq_rcd A B l0 l.
  case_if*. case_if*. rewrite* H1.
Qed.

Lemma eqIndTyp_complete_alt_gen : forall A B,
    incl (|| B ||) (|| A ||) -> sub A B.
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
      * assert (incl (||typ_bot||) (||A1||)). {
         simpl. unfolds. intros. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
      * assert (incl (||typ_bot||) (||A2||)). {
         simpl. unfolds. intros. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
  - simpl in HE.
    apply incl_Forall_in_iff in HE.
    apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert (incl (||typ_base||) (||A1||)). {
         simpl. unfolds. intros. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
      * assert (incl (||typ_base||) (||A2||)). {
         simpl. unfolds. intros. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
  - simpl in HE; try case_if.
    { rewrite <- check_toplike_sound_complete in C... }
    try apply incl_Forall_in_iff in HE.
    try apply Forall_inv in HE.
    destruct A; simpl in HE; try solve [try case_if; try destruct HE; try discriminate; intuition eauto; inverts H].
    + (* arrow vs arrow *)
      simpl in HE. case_if.
      rewrite in_one_iff in HE.
      injection HE. intro HEq.
      assert (|| B1 || = || A1 ||) by eauto using st_eq1.
      assert (|| A2 || = || B2 ||) by eauto using st_eq2.
      assert (|| A1 || = || B1 ||) by eauto using st_eq1.
      assert (|| B2 || = || A2 ||) by eauto using st_eq2.
      forwards: IH B1 A1; eauto using incl_eq. elia.
      forwards: IH A1 B1; eauto using incl_eq. elia.
      forwards: IH A2 B2; eauto using incl_eq. elia.
      forwards: IH B2 A2; eauto using incl_eq. elia.
    + case_if.
      forwards Hia: In_incl HE incl_nodup_merge_rev.
      forwards [|]: in_app_or Hia.
      * assert (incl (||typ_arrow B1 B2||) (||A1||)). {
         simpl. unfolds. intros. case_if. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
      * assert (incl (||typ_arrow B1 B2||) (||A2||)). {
         simpl. unfolds. intros. case_if. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
  - assert (incl (|| B1 ||)(|| typ_and B1 B2 ||)). {
      simpl. case_if. { forwards (?&?): andb_prop C. rewrite* stype2string_toplike. eauto...  }
      applys incl_tran. 2: applys incl_nodup_merge. applys incl_appl. applys incl_refl.
    }
    assert (incl (|| B2 ||)(|| typ_and B1 B2 ||)). {
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
      * assert (incl (||typ_rcd l B||) (||A1||)). {
         simpl. unfolds. intros. case_if. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
      * assert (incl (||typ_rcd l B||) (||A2||)). {
         simpl. unfolds. intros. case_if. rewrite in_one_iff in H0. subst*.
        }
        forwards*: IH H0. elia.
    + simpl in HE. case_if.
      rewrite in_one_iff in HE.
      injection HE. intro HEq.
      assert (|| B || = || A ||) by eauto using st_eq3. assert (|| A || = || B ||) by eauto using st_eq3.
      assert (l = l0) by eauto using st_eq4. subst.
      forwards: IH B A; eauto using incl_eq. elia.
      forwards*: IH A B; eauto using incl_eq. elia.
  Qed.

Corollary eqIndTyp_complete : forall A B,
    (|| A ||) = (|| B ||) -> sub A B /\ sub B A.
Proof with eauto using incl_refl.
  introv HE.
  split; applys eqIndTyp_complete_alt_gen.
  rewrite HE... rewrite <- HE...
Qed.

Lemma eqIndTyp_sound_alt_gen : forall A B,
    sub A B -> incl (|| B ||) (|| A ||).
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
    sub B A -> sub A B -> (|| B ||) = (|| A ||).
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
      inverts H.
      assert (HE1: || A1 || = || B1 ||) by eauto using st_eq1.
      assert (HE2: || A2 || = || B2 ||) by eauto using st_eq2.
      (* assert (HS: forall A B, sub A B -> subTarget |[A]| |[B]|) by admit. *)
      forwards (HS1&HS2): eqIndTyp_complete HE1. forwards (HS3&HS4): eqIndTyp_complete HE2.
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
      assert (HE1: || A || = || B ||) by eauto using st_eq3.
      (* assert (HS: forall A B, sub A B -> subTarget |[A]| |[B]|) by admit. *)
      forwards (HS1&HS2): eqIndTyp_complete HE1.
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
