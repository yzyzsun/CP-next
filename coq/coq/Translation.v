Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Arith Lia.
Require Import Strings.String.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders OrdersEx.
Require Import StructTact.StringOrders.
Import IfNotations.
Require Export syntax_ott.
Require Export Infrastructure.

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

Lemma lookup_concat_simpl : forall i A B T,
    Tlookup i A = Some T ->
    Tlookup i (ttyp_concat_simpl A B) = Tlookup i A.
Proof.
  introv LK. gen i T B.
  induction A; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H0.
    subst. simpl. case_if*.
  - simpl. case_if*.
Qed.


Lemma lookup_concat_simpl_none : forall i A B,
    Tlookup i A = None -> rec_typ A ->
    Tlookup i (ttyp_concat_simpl A B) = Tlookup i B.
Proof.
  introv LK HR. gen i B.
  induction A; intros; simpl; try solve_by_invert; eauto.
  - inverts* HR. inverts LK. case_if.
    forwards* Heq: IHA2.
Qed.

Lemma lookup_wf_typ_1 : forall l T At l',
    Tlookup l' (ttyp_rcd l T At) = Tlookup l' At \/ l = l'.
Proof.
  introv. simpl. case_if*.
Qed.

(* Lemma lookup_wf_typ_2 : forall l T At Bt, *)
(*     wf_typ (ttyp_rcd l T At) -> Tlookup l At = Some Bt -> eqIndTypTarget Bt T. *)
(* Proof. *)
(*   introv WF LK. inverts WF. destruct H5. *)
(*   all: rewrite LK in H; inverts* H. *)
(*   inverts* H0. *)
(* Qed. *)

Lemma lookup_wf_typ_3 : forall l T At l',
    l = l' -> Tlookup l (ttyp_rcd l' T At) = Some T.
Proof.
  introv HE. subst. simpl. case_if*.
Qed.

Lemma wf_typ_look_up_wf : forall l At Bt,
    Tlookup l At = Some Bt -> wf_typ At -> wf_typ Bt.
Proof with eauto.
  introv Heq WF. gen l Bt.
  induction WF; intros; try solve_by_invert.
  inverts Heq. case_if*.
  - inverts* H2.
Qed.

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

Lemma wf_rcd_lookup : forall i T Ti,
  wf_typ T ->
  Tlookup i T = Some Ti ->
  wf_typ Ti.
Proof.
  introv WF LK.
  gen i Ti.
  induction WF; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H2.
Qed.

Lemma Tlookup_dec : forall l A,
  (exists B, Tlookup l A = Some B) \/ Tlookup l A = None.
Proof.
  introv. remember (Tlookup l A). destruct* o.
Qed.

Ltac case_lookup l A := lets [(?&?)|?]: Tlookup_dec l A.

Ltac unify_lookup :=
  destruct_disj; destruct_conj;
  repeat lazymatch goal with
    | |- Some _ = Some _  => try reflexivity
    | H : Some _ = None |- _ => inverts H
    | H : Some _ = Some _ |- _ => inverts H
    | H1 : ?A = Some _ , H2 : ?A = Some _ |- _ => rewrite H1 in H2
    | H1 : ?A = Some _ , H2 : ?A = None |- _ => rewrite H1 in H2
    | H : Tlookup ?l (ttyp_rcd ?l ?A ?C) = _ |- _ =>
        simpl in H; case_if
    | H : Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ |- _ =>
        let Heq := fresh "Heq" in
        lets [Heq|Heq]: lookup_wf_typ_1 l A C r;
        [ rewrite Heq in H; clear Heq | subst ]
    | H: ?l <> ?r |- Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
    | H: ?r <> ?l |- Tlookup ?r (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
    | |- Tlookup ?l (ttyp_rcd ?l ?A ?C) = _ => simpl; case_if
    | H1: Tlookup _ ?A = Some _ , H2: ?A = ttyp_top |- _ => rewrite H2 in H1; discriminate
    end.

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



Lemma rcd_typ_concat_1 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T1.
Proof.
  introv CT. induction* CT.
Qed.

Lemma rcd_typ_concat_2 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T2.
Proof.
  introv CT. induction* CT.
Qed.

Lemma rcd_typ_concat_3 : forall T1 T2 T3,
    concat_typ T1 T2 T3 -> rec_typ T3.
Proof.
  introv CT. induction* CT.
Qed.

Lemma lookup_concat_typ : forall i A B C T,
    Tlookup i A = Some T ->
    concat_typ A B C ->
    Tlookup i C = Tlookup i A.
Proof.
  introv LK CC. gen i T B C.
  induction A; intros; simpl in LK; inverts LK.
  case_if*.
  - inverts* H0. inverts* CC.
    subst. unfolds. case_if*.
  - inverts* CC.
    forwards~ : IHA2 H0 H6.
    unfolds. case_if*.
Qed.


Lemma lookup_concat_typ_none : forall i A B C,
    Tlookup i A = None ->
    concat_typ A B C ->
    Tlookup i C = Tlookup i B.
Proof.
  introv LK CC. gen i B C.
  induction A; intros; inverts* CC.
  - inverts* LK; case_if.
    forwards* Heq: IHA2 H0 H5.
    rewrite <- Heq.
    unfolds. case_if*.
Qed.

Ltac lookup_concat l HC :=
  match type of HC with
  | concat_typ ?A ?B ?C => let Heq := fresh "Heq" in
                           match goal with
                           | H: Tlookup l A = Some _ |- _ =>
                               forwards Heq: lookup_concat_typ H HC;
                               rewrite H in Heq
                           | H: Tlookup l A = None, H2: Tlookup l B = _ |- _ =>
                               forwards Heq: lookup_concat_typ_none H HC;
                               rewrite H2 in Heq
                           end
  end.


Lemma wf_rcd_concat : forall T1 T2 T3,
    wf_typ T1 -> wf_typ T2 ->
    rec_typ T1 -> rec_typ T2 ->
    concat_typ T1 T2 T3 ->
    wf_typ T3.
Proof with eauto using rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv WF1 WF2 RT1 RT2 CT.
  induction* CT.
  - inverts* WF1. inverts* RT1...
    destruct H6 as [(?&?)|?].
    + forwards* Heq: lookup_concat_typ H0 CT.
      rewrite H0 in Heq... intuition eauto; econstructor...
    + forwards* Heq: lookup_concat_typ_none H0 CT.
      destruct H as [(H'&?) | H']; rewrite H' in Heq; econstructor...
      Unshelve. all: eauto.
Qed.



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
Lemma ST_top: forall A, subTarget |[ A ]| ttyp_top.
Proof with simpl in *; discriminate.
  introv. applys* ST_rcd.
  intros...
Qed.

Lemma ST_trans: forall A B C, subTarget A B -> subTarget B C -> subTarget A C.
Proof with try simpl in *; discriminate.
  introv HA HB.
  indTypSize (size_ttyp A + size_ttyp B + size_ttyp C).
  destruct* HA; inverts* HB; try solve [inverts H]; try solve [inverts H0].
  - econstructor; eauto. all: applys* IH; elia.
  - applys~ ST_rcd. intros.
    forwards~ (?&?&?&?): H4 H5. forwards~ (?&?&?&?): H1 H6.
    exists x0. splits*.  all: applys* IH; elia.
Qed.

Lemma ST_inv : forall A B,
    subTarget |[ A ]| |[ B ]| ->
    forall l Ct, Tlookup l |[ B ]| = Some Ct -> exists Ct', Tlookup l |[ A ]| = Some Ct' /\ subTarget Ct' Ct  /\ subTarget Ct Ct'.
Proof.
  introv HA.  inverts* HA.
  - introv HL. forwards*: H1 HL.
Qed.

Lemma ST_arrow_inv : forall x A B,
    subTarget x (ttyp_arrow A B) -> exists C D, x = ttyp_arrow C D /\
                                                  subTarget A C /\ subTarget C A /\
                                                  subTarget B D /\ subTarget D B.
Proof.
  introv HS. inverts* HS. inverts H.
Qed.

Lemma subTarget_rec_typ : forall A B,
    subTarget A B -> rec_typ A -> rec_typ B.
Proof.
  introv HS HR. induction~ HS. inverts HR.
Qed.

Lemma ST_rcd_inv : forall A B,
    subTarget A B -> rec_typ A ->
    forall l Ct, Tlookup l B = Some Ct ->
                 exists Ct', Tlookup l A = Some Ct' /\ subTarget Ct' Ct /\ subTarget Ct Ct'.
Proof.
  introv HS HA. forwards* HB: subTarget_rec_typ HA. inverts* HS.
  - introv HL. forwards*: H1 HL.
Qed.

Lemma ST_rcd_2 : forall A B C D l, subTarget A B -> subTarget B A -> subTarget C D -> subTarget D C
                                 -> rec_typ C -> rec_typ D
                                 -> subTarget (ttyp_rcd l A C) (ttyp_rcd l B D).
Proof with unify_lookup; intuition eauto.
  introv HSa HSb HSc HSd HRc HRd. applys* ST_rcd.
  introv HL. simpl. case_if*.
  - subst*. exists. split*. simpl in HL. case_if.
    inverts* HL.
  - simpl in HL. case_if. forwards*: ST_rcd_inv HSc.
Qed.

Lemma ST_top_inv : forall A, subTarget ttyp_top A -> A = ttyp_top.
Proof.
  introv HS. inverts* HS.
  destruct* H.
  forwards* (?&?&?): H1 l.
  simpl in H2. discriminate.
Qed.

Lemma ST_refl : forall A, subTarget A A.
Proof.
  introv. induction* A.
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

Lemma st_eq_arrow : forall A1 A2 B1 B2,
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_arrow A1 A2) || =  || (typ_arrow B1 B2) || -> || B1 || = || A1 || /\ || B2 || = || A2 ||.
Admitted.

Lemma st_eq_rcd : forall A2 B2 l l',
    check_toplike A2 = false -> check_toplike B2 = false ->
    || (typ_rcd l A2) || =  || (typ_rcd l' B2) || -> l = l' /\ || B2 || = || A2 ||.
Admitted.

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
(*   remember (check_toplike A2). remember (check_toplike B2). *)
(*   destruct b; destruct b0. *)
(*   - repeat rewrite* stype2string_toplike. *)
(*   - *)

(*   forwards*: st_eq_arrow A1 A2 B1 B2. *)
(*   case_if*. case_if*. *)
(* Admitted. *)

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
Proof with eauto using NoDup_nodup, merge_sorted_dedup, check_toplike_sound_complete.
  (* introv HE. indTypSize (size_typ A + size_typ B). *)
  (* destruct A; intros. *)
  (* - forwards*: stype2string_toplike_complete B... simpl in HE. *)
  (*   applys* incl_l_nil. *)
  (* - (* bot sub all *) eauto. admit. *)
  (* - simpl in HE. Search incl. destruct B... *)
  (*   all: try solve [simpl in HE; try case_if; forwards: incl_single HE; try discriminate]. *)
  (*   + simpl in HE. case_if. admit. *)
  (*     forwards: incl_single HE. discriminate. *)
  (*   + admit. *)
  (*   + admit. *)
  (* - (* arrow *) *)
  (*   simpl in HE. case_if. *)
  (*   + admit. *)
  (*     (* stype2string_toplike_complete *) *)
  (*   + destruct B... *)
  (*     all: try solve [simpl in HE; try case_if; try discriminate]. *)
  (*     3: { *)
  (*       (* arrow *) *)
  (*       simpl in HE. case_if. admit. *)
  (*       forwards: incl_single HE. *)
  (*       injection H. intro HEq. *)
  (*       Search (_ ++ _ = _ ++ _). (* better use an inductive type as a label *) *)
  (*       assert (|| B1 || = || A1 ||) by admit. assert (|| A2 || = || B2 ||) by admit. *)
  (*       assert (|| A1 || = || B1 ||) by admit. assert (|| B2 || = || A2 ||) by admit. *)
  (*       forwards: IH B1 A1; eauto using incl_eq. elia. *)
  (*       forwards: IH A1 B1; eauto using incl_eq. elia. *)
  (*       forwards: IH A2 B2; eauto using incl_eq. elia. *)
  (*       forwards: IH B2 A2; eauto using incl_eq. elia. *)
  (*     } *)
  (*     3: { (* and *) admit. *)
  (*          (* forwards ([|]&[|]): stype2string_single_and_inv HE. *) *)
  (*          (* simpl in HE. rewrite <- H0 in HE. *) *)
  (*          (* case_if in HE. *) *)
  (*          (* assert (Heq: nodup string_dec (syntax_ott.NSort.merge nil (|| B2 ||)) = || B2 ||) by admit. *) *)
  (*          (* rewrite Heq in HE. forwards: IHB2 HE. elia. *) *)
  (*          (* forwards*: stype2string_toplike_complete B1. *) *)
  (*     } *)
  (*     admit. admit. admit. *)
  (* - simpl in HE. case_if. admit. *)
  (*   assert (incl (nodup string_dec (syntax_ott.NSort.merge (|| A1 ||) (|| A2 ||))) ((|| A1 ||) ++ (|| A2 ||))). { *)
  (*     applys nodup_incl string_dec. *)
  (*     Search (incl). admit. *)
  (*   } *)
  (*   forwards: incl_tran HE H. *)
  (* (*   + admit. (* top *) *) *)
  (* (*   + admit. (* single *) *) *)
  (* (*   + admit. (* single *) *) *)
  (* (*   + admit. (* single *) *) *)
  (* (*   + (* prove (typ_and A1 A2) <: B1 *) *) *)
  (* (*     (* prove (typ_and A1 A2) <: B2 *) *) *)
  (* (*     assert (incl (|| A1 ||) (|| typ_and A1 A2 ||)). *) *)
  (* (*     assert (incl (|| A2 ||) (|| typ_and A1 A2 ||)). *) *)
  (* (*     all: admit. *) *)
  (* (*   + admit. (* single *) *) *)
  (* (* - admit. *) *)
  (*   Restart. *)
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
Lemma lookup_eq : forall A B,
    subTarget A B -> subTarget B A -> forall l, Tlookup l A = None -> Tlookup l B = None.
Proof.
  introv HS HR.
  induction* HS.
  - introv HL. remember (Tlookup l At). destruct* o.
    forwards* (?&?&?): H1 l. rewrite HL in H2. discriminate.
Qed.

Lemma lookup_ST_sub : forall A B l A',
    subTarget B A ->
    Tlookup l A = Some A' -> exists B', Tlookup l B = Some B' /\ subTarget B' A' /\ subTarget A' B'.
Proof.
  introv HSA HLA. gen l A'.
  induction* HSA; intros; unify_lookup; intuition eauto.
Qed.

Lemma lookup_ST_eq_some : forall A B l A',
    subTarget A B -> subTarget B A ->
    Tlookup l A = Some A' -> exists B', Tlookup l B = Some B' /\
                                          subTarget A' B' /\ subTarget B' A'.
Proof.
  intros. forwards* (?&?&?): lookup_ST_sub A B.
Qed.

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


(* Lemma sub_transtivity : forall B A C, *)
(*     sub A B -> sub B C -> sub A C. *)
(* Proof with eauto. *)
(*   introv S1 S2. gen A C. *)
(*   induction B; intros; *)
(*     try solve [inductions S2; eauto]. - inverts* S2. inverts* S1. *)
(*   - inductions S2... *)
(*     clear IHS2_1 IHS2_2. *)
(*     inductions S1... *)
(*     applys S_top. applys toplike_sub H... *)
(*   - forwards* (?&?): and_inversion S1. *)
(*     inductions S2... *)
(* Qed. *)


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

(* Lemma lookup_sub : forall A B l T T', *)
(*     Tlookup l (|[ A ]|) = Some T  -> *)
(*     Tlookup l (|[ B ]|) = Some T' -> subTarget T T'. *)
(* Proof with simpl in *; try case_if; try discriminate; eauto. *)
(*   introv HA HB. *)
(*   induction A. *)
(*   - rewrite* (ttyp_trans_ord_top) in HA... *)
(*   - simpl in HA. case_if. inverts HA. rewrite C in HB. *)
(*     induction B... *)
(*     + inverts HB... *)
(*     + destruct_lookup HB. forwards*: IHB1. forwards*: IHB2. *)
(*   - simpl in HA. case_if. inverts HA. rewrite C in HB. *)
(*     induction B... *)
(*     + inverts HB... *)
(*     + destruct_lookup HB. forwards*: IHB1. forwards*: IHB2. *)
(*   - clear IHA1 IHA2. simpl in HA. case_if. inverts HA. case_if. *)
(*     rewrite C0 in HB. *)
(*     induction B... *)
(*     + forwards (?&?): Tlookup_eq HB. inverts H0. rewrite <- H1. *)
(*       assert (HE1: || A1 || = || B1 ||) by admit. assert (HE2: || A2 || = || B2 ||) by admit. *)
(*       assert (HS: forall A B, sub A B -> subTarget |[A]| |[B]|) by admit. *)
(*       forwards (HS1&HS2): eqIndTyp_complete HE1. forwards (HS3&HS4): eqIndTyp_complete HE2. *)
(*       apply HS in HS1. apply HS in HS2. apply HS in HS3. apply HS in HS4... *)
(*     + destruct_lookup HB. forwards*: IHB1. forwards*: IHB2. *)
(*   - simpl in HA. case_if. destruct_lookup HA. *)
(*     + forwards~: IHA1. + forwards~: IHA2. *)
(*   - clear IHA. simpl in HA. case_if. inverts HA. case_if. *)
(*     rewrite C0 in HB. *)
(*     induction B... *)
(*     + destruct_lookup HB. forwards*: IHB1. forwards*: IHB2. *)
(*     + forwards (?&?): Tlookup_eq HB. inverts H0. rewrite <- H1. *)
(*       assert (HE1: || A || = || B ||) by admit. *)
(*       assert (HS: forall A B, sub A B -> subTarget |[A]| |[B]|) by admit. *)
(*       forwards (HS1&HS2): eqIndTyp_complete HE1. *)
(*       apply HS in HS1. apply HS in HS2... *)
(* Admitted. *)

(* (* Lemma lookup_sub : forall A B l T, *) *)
(* (*     sub A B -> *) *)
(* (*     Tlookup l (|[ B ]|) = Some T -> *) *)
(* (*     exists T', Tlookup l (|[ A ]|) = Some T' /\ subTarget T T'. *) *)
(* (* Proof with try rewrite* <- check_toplike_sound_complete. *) *)
(* (*   introv HS HL. *) *)
(* (*   induction HS; try solve [simpl; eauto]. *) *)
(* (*   - rewrite* (ttyp_trans_ord_top B) in HL... inverts HL. *) *)
(* (*   - simpl in HL. case_if. inverts HL. case_if. *) *)
(* (*     injection H0. intro HE. rewrite C0. *) *)
(* (*     exists*. split. simpl. case_if. *) *)
(* (*     { forwards* HSE: sub_eqv_toplike B2 A2. rewrite C1 in HSE. rewrite C in HSE. *) *)
(* (*       discriminate. } *) *)
(* (*     forwards*: eqIndTyp_sound_alt B1 A1. forwards*: eqIndTyp_sound_alt B2 A2. *) *)
(* (*     rewrite H. rewrite* H1. *) *)
(* (*     rewrite* <- HE. *) *)
(* (*   - simpl in HL. case_if. inverts HL. case_if. *) *)
(* (*     injection H0. intro HE. rewrite C0. *) *)
(* (*     exists*. split. simpl. case_if. *) *)
(* (*     { forwards* HSE: sub_eqv_toplike B A. rewrite C1 in HSE. rewrite C in HSE. *) *)
(* (*       discriminate. } *) *)
(* (*     forwards*: eqIndTyp_sound_alt B A. *) *)
(* (*     rewrite H. rewrite* <- HE. rewrite* <- HE. *) *)
(* (*     admit. *) *)
(* (*   - *) *)

(* (* REQUIRES ST_ANDR *) *)
(* Lemma sub_source2target : forall A B, *)
(*     sub A B -> subTarget |[A]| |[B]|. *)
(* Proof with try rewrite* <- check_toplike_sound_complete. *)
(*   introv HS. *)
(*   induction HS; try solve [simpl; eauto]. *)
(*   - rewrite* (ttyp_trans_ord_top B)... *)
(*   - simpl. case_if*. admit. *)
(*     simpl. case_if*. admit. *)
(*     + *)
(*       rewrite* (eqIndTyp_sound_alt A1 B1). rewrite* (eqIndTyp_sound_alt A2 B2). *)
(*       applys ST_rcd. introv HL. simpl in HL. case_if*. *)
(*       subst. exists. split*. injection HL. intro HE. subst*. *)
(*   - simpl. case_if*. admit. *)
(*     simpl. case_if*. admit. *)
(*     + *)
(*       rewrite* (eqIndTyp_sound_alt A B). *)
(*       applys ST_rcd. introv HL. simpl in HL. case_if*. *)
(*       subst. exists. split*. injection HL. intro HE. subst*. *)
(*   - applys* ST_trans IHHS. *)
(*   - applys* ST_trans IHHS. clear HS. *)
(*     { applys* ST_rcd. *)
(*       introv HL. simpl. case_if*. apply andb_prop in C; unify_lookup; intuition eauto. *)
(*       - forwards: ttyp_trans_ord_top H0; unify_lookup; intuition eauto. *)
(*       - remember (check_toplike A1). destruct b. *)
(*         + forwards*: ttyp_trans_ord_top A1; unify_lookup; intuition eauto. *)
(*           rewrite H. simpl; unify_lookup; intuition eauto. *)
(*         + remember (Tlookup l |[A1]|). destruct o. *)
(*           * forwards*: lookup_concat_simpl (|[ A1 ]|) (|[ A2 ]|). rewrite H. *)
(*             rewrite <- Heqo; unify_lookup; intuition eauto. exists*. split*. *)
(*             applys* lookup_sub. (* !!! *) *)
(*           * forwards*: lookup_concat_simpl_none (|[ A1 ]|) (|[ A2 ]|). rewrite H. *)
(*             rewrite* HL. *)
(*     } *)
(*   - simpl. case_if*. *)
(*     + applys ST_rcd. introv HL. *)
(*       remember (Tlookup l |[A2]|). destruct o. *)
(*       * forwards* (?&?&?): ST_inv IHHS1. *)
(*         forwards* : lookup_concat_simpl (|[ A2 ]|) (|[ A3 ]|). *)
(*         rewrite HL in H1. rewrite <- Heqo in H1. injection H1. intro Heq. subst*. *)
(*       * forwards* (?&?&?): ST_inv IHHS2. *)
(*         forwards* : lookup_concat_simpl_none (|[ A2 ]|) (|[ A3 ]|). *)
(*         rewrite* HL in H. *)
(* Admitted. *)


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

Lemma ST_top_2: forall A, rec_typ A -> subTarget A ttyp_top.
Proof with simpl in *; discriminate.
  introv HR. applys* ST_rcd.
  intros...
Qed.

Lemma split_toplike_l : forall A1 A2 B,
    spl B A1 A2 -> toplike B -> toplike A1.
Proof.
  introv HC HT. induction* HC; inverts~ HT.
Qed.


Lemma split_toplike_r : forall A1 A2 B,
    spl B A1 A2 -> toplike B -> toplike A2.
Proof.
  introv HC HT. induction* HC; inverts~ HT.
Qed.

Lemma ST_toplike : forall A,
    toplike A -> subTarget ttyp_top |[A]|.
Proof.
  introv TL. rewrite ttyp_trans_ord_top. applys ST_refl.
  rewrite* <- check_toplike_sound_complete.
Qed.

Lemma lookup_concat_both : forall At Bt Ct A B l,
    concat_typ At Bt Ct -> Tlookup l At = Some A -> Tlookup l Bt = Some B -> subTarget A B /\ subTarget B A.
Proof.
  introv HC HLa HLb. gen Bt A B Ct.
  induction At; intros; simpl in HC; try solve [inverts HLa].
  - simpl in HLa. case_if.
    + subst*. inverts HLa. inverts HC. intuition eauto; unify_lookup; eauto.
    + inverts HC. forwards*: IHAt2.
Qed.

Lemma concat_typ_exists : forall A B,
    rec_typ A -> rec_typ B -> wf_typ A -> wf_typ B ->
    (forall l A' B', Tlookup l A = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A') ->
    concat_typ A B (ttyp_concat_simpl A B).
Proof with intuition eauto using ST_trans.
  introv HRa HRb. gen B.
  induction HRa; intros; try solve [simpl; intuition eauto].
  simpl. case_lookup l B.
  + forwards(?&?): H1 l H2. simpl. case_if*.
    assert ((forall (l : String.string) (A' B' : ttyp),
                Tlookup l Bt = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A')). {
      intros. case_eq (string_eq_dec l l0); intros; subst.
      - forwards: H1 l0. simpl. case_if*. eauto. inverts H. destruct H15; unify_lookup...
      - forwards: H1 l0. simpl. case_if*. eauto. eauto.
    }
    econstructor... applys IHHRa...
    inverts~ H.
   + assert ((forall (l : String.string) (A' B' : ttyp),
                Tlookup l Bt = Some A' -> Tlookup l B = Some B' -> subTarget A' B' /\ subTarget B' A')). {
      intros. case_eq (string_eq_dec l l0); intros; subst.
      - forwards: H1 l0. simpl. case_if*. eauto. inverts H. destruct H13; unify_lookup...
      - forwards: H1 l0. simpl. case_if*. eauto. eauto.
     }
     econstructor... applys IHHRa...
     inverts~ H.
     Unshelve. all: eauto.
Qed.

Lemma ST_concat : forall At Bt Ct At' Bt',
    concat_typ At Bt Ct -> subTarget At At' -> subTarget At' At -> subTarget Bt Bt' -> subTarget Bt' Bt ->
    wf_typ At' -> wf_typ Bt' ->
    exists Ct', concat_typ At' Bt' Ct' /\ subTarget Ct Ct' /\ subTarget Ct' Ct.
Proof with eauto using ST_trans, subTarget_rec_typ, rcd_typ_concat_1, rcd_typ_concat_2, rcd_typ_concat_3.
  introv HC HSa HSa' HSb HSb' Wa Wb.
  forwards HRa: rcd_typ_concat_1 HC. forwards HRb: rcd_typ_concat_2 HC.
  (* gen Bt At' Bt' Ct. induction HRa; intros. *)
  (* - inverts HC. forwards: ST_top_inv HSa. subst. exists. split*... *)
  (* - inverts HC. forwards* (?&?&?): IHHRa HSb... *)
  forwards: concat_typ_exists At' Bt'...
  - intros. forwards (?&?&?): ST_rcd_inv HSa... forwards (?&?&?): ST_rcd_inv HSa'...
    forwards (?&?&?): ST_rcd_inv HSb... forwards (?&?&?): ST_rcd_inv HSb'... unify_lookup.
    forwards (?&?): lookup_concat_both l HC... split...
  - exists. splits*.
    { applys ST_rcd... introv HL.
    case_lookup l At'.
    + forwards*: lookup_concat_typ H. rewrite H1 in HL. rewrite H0 in HL. inverts HL.
    forwards (?&?&?): ST_rcd_inv HSa...
    forwards*: lookup_concat_typ HC. rewrite H2 in H4.
    exists. split*.
    + forwards*: lookup_concat_typ_none H. rewrite H1 in HL.
    forwards (?&?&?): ST_rcd_inv HSb...
    case_lookup l At.
    * forwards*: lookup_concat_both HC.
      forwards*: lookup_concat_typ HC. rewrite H4 in H6.
      exists. split. eauto. intuition eauto...
    * forwards*: lookup_concat_typ_none HC. rewrite H2 in H5.
      exists. split*... }
        { applys ST_rcd... introv HL.
    case_lookup l At.
    + forwards*: lookup_concat_typ HC. rewrite H1 in HL. rewrite H0 in HL. inverts HL.
    forwards (?&?&?): ST_rcd_inv HSa'...
    forwards*: lookup_concat_typ H. rewrite H2 in H4.
    exists. split*.
    + forwards*: lookup_concat_typ_none HC. rewrite H1 in HL.
    forwards (?&?&?): ST_rcd_inv HSb'...
    case_lookup l At'.
    * forwards*: lookup_concat_both H.
      forwards*: lookup_concat_typ H. rewrite H4 in H6.
      exists. split. eauto. intuition eauto...
    * forwards*: lookup_concat_typ_none H. rewrite H2 in H5.
      exists. split*... }
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

(* Lemma trans_head_inv : forall A x l At Bt, *)
(*    rec_typ x -> |[ A ]| = ttyp_concat_simpl x (ttyp_rcd l At Bt) -> exists C, |[C]| = ttyp_rcd l At ttyp_top. *)
(* Proof with simpl in *; try discriminate; intuition eauto. *)
(*   introv HRx HE. gen A l At Bt. *)
(*   induction HRx; intro A. *)
(*   + induction* A; intros; inverts~ HE. *)
(*   - exists typ_bot... *)
(*   - exists typ_base... *)
(*   - case_if. injection H0. intros. *)
(*     exists (typ_arrow A1 A2). rewrite <- H1. rewrite <- H2. simpl. case_if*. *)
(*   - case_if. forwards HR: translate_to_record_types A1. *)
(*     remember |[ A1 ]|. destruct HR; simpl in H0. *)
(*     * forwards (?&?): IHA2 H0... *)
(*     * injection H0. intros. subst. applys* IHA1... *)
(*   - case_if. injection H0. intros... *)
(*     exists (typ_rcd l A). rewrite <- H1. rewrite <- H2. simpl. case_if*. *)
(*     + *)

(*       Search (In). Print ttyp_concat_simpl. *)
(* Abort. *)
(* (*       Fixpoint tolist (A: ttyp) : list ttyp := *) *)
(* (*         match A with *) *)
(* (*         | ttyp_top => [] *) *)
(* (*         | ttyp_rcd l At Bt => [ttyp_rcd l At ttyp_top] ++ to list Bt *) *)
(* (*         | _ => ttyp_top *) *)
(* (*         end. *) *)

(* (*       define In a rcd *) *)
(* (*         In is decidable *) *)
(* (*         In A++B then either In A or In B *) *)


(* (*                        Define tolist *) *)
(* (*                        tolist A ++ B = tolist A ++ tolist B *) *)
(* (*                                          wf A -> all B In tolist A, wf B *) *)
(* (*                                                                       A = ()::A' -> In () A *) *)

(* (*   - destruct* HRx... *) *)
(* (*     destruct* HRx... all: inverts* H0... *) *)
(* (* Search ttyp_concat_simpl. *) *)
(* (* destruct Bt0 simpl in H3... *) *)
(* (* Qed. *) *)

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

Definition styp2ttyp_raw (A: typ) : ttyp :=
  if (check_toplike A) then ttyp_top
  else match A with
  | typ_bot => ttyp_bot
  | typ_base =>  ttyp_base
  | typ_arrow B1 B2 => ttyp_arrow (|[ B1 ]|) (|[ B2 ]|)
  | typ_rcd l A' => |[ A' ]|
  | _ => ttyp_top (* for top and intersections *)
  end.

Notation "[[ A ]]" := (styp2ttyp_raw A) (at level 5, A at next level).


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

(* Lemma ttyp_trans_and : forall A B C, *)
(*     concat_typ |[ A ]| |[ B ]| C -> |[ (typ_and A B) ]| = C. *)
(* Admitted. *)



Fixpoint context_trans (G:ctx) : tctx :=
  match G with
  | nil => nil
  | (x, A) :: l => (x, |[A]|) :: (context_trans l)
  end.

Notation "||[ G ]||" := (context_trans G) (at level 1, G at next level).


Lemma elaboration_wf_ctx : forall G,
    uniq G  -> wf_ctx ||[G]||.
Proof with eauto using ttyp_trans_wf.
  introv HU. induction* G.
  simpl... destruct a... econstructor...
  inverts~ HU.
  Qed.



Lemma S_refl : forall A, sub A A.
Proof.
  introv. induction* A.
Qed.


(* (** * Multisets *) *)
(* From Coq Require Import FunctionalExtensionality. *)
(* Definition multiset := string -> nat. *)

(* (** The [empty] multiset has multiplicity [0] for every value. *) *)

(* Definition empty : multiset := *)
(*   fun x => 0. *)

(* (** Multiset [singleton v] contains only [v], and exactly once. *) *)

(* Definition singleton (v: string) : multiset := *)
(*   fun x => if x =? v then 1 else 0. *)

(* (** The union of two multisets is their _pointwise_ sum. *) *)

(* Definition union (a b : multiset) : multiset := *)
(*   fun x => a x + b x. *)

(* Lemma union_assoc: forall a b c : multiset, *)
(*    union a (union b c) = union (union a b) c. *)
(* Proof. *)
(*   intros. *)
(*   extensionality x. *)
(*   unfolds. eauto using Nat.add_assoc. *)
(* Qed. *)

(* Lemma union_comm: forall a b : multiset, *)
(*    union a b = union b a. *)
(* Proof. *)
(*   intros. *)
(*   extensionality x. *)
(*   unfolds. eauto using Nat.add_comm. *)
(* Qed. *)

(* Lemma union_swap : forall a b c : multiset, *)
(*     union a (union b c) = union b (union a c). *)
(* Proof. *)
(*   intros. *)
(*   extensionality x. *)
(*   unfolds. lia. *)
(* Qed. *)


(* Fixpoint contents (al: list string) : multiset := *)
(*   match al with *)
(*   | nil => empty *)
(*   | a :: bl => union (singleton a) (contents bl) *)
(*   end. *)

(* Lemma contents_inv : forall a bl, *)
(*     contents (a :: bl) = union (singleton a) (contents bl). *)
(* Proof. *)
(*   introv. eauto. *)
(* Qed. *)

(* Ltac indListSize s := *)
(*   assert (SizeInd: exists i, s < i) by eauto; *)
(*   destruct SizeInd as [i SizeInd]; *)
(*   repeat match goal with | [ h : list _ |- _ ] => (gen h) end; *)
(*   induction i as [|i IH]; [ *)
(*     intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end *)
(*   | intros ]. *)

(* (* prove merge is a permutation *) *)
(* Theorem merge_contents: forall a b, *)
(*     union (contents a) (contents b) = contents (merge a b). *)
(* Proof. *)
(*   intros. extensionality x. indListSize (length a + length b). *)
(*   destruct a; destruct b; autorewrite with merge. *)
(*   (* induction a; induction b; autorewrite with merge. *) *)
(*   1-3: unfolds; simple*. *)
(*   case_if. *)
(*   - simpl. unfold union. rewrite <- IH. *)
(*     unfold union. rewrite (contents_inv s0 b). unfold union. *)
(*     all: simpl in *; lia. *)
(*   - repeat rewrite (contents_inv s0 _). unfold union. rewrite <- IH. *)
(*     { unfold union. lia. } *)
(*     simpl in *; lia. *)
(* Qed. *)


(* Require Import Ascii. *)
(* Lemma ascii_compare_refl : forall t : ascii, (t ?= t)%char = Eq. *)
(* Proof. *)
(*   intro t. destruct t. *)
(*   unfold Ascii.compare; simpl. rewrite* BinNat.N.compare_refl. *)
(* Qed. *)

(* Lemma string_compare_refl : forall s1 : string, (s1 ?= s1) = Eq. *)
(* Proof. *)
(*   intros. induction* s1. *)
(*   simpl. rewrite IHs1. rewrite* ascii_compare_refl. *)
(* Qed. *)

(* Check NTTLB.leb_trans. *)
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

(* Check Sorted_merge. *)

(* Lemma In_merge : forall y l r, *)
(*     In y (merge l r) <-> In y l \/ In y r. *)
(* Proof. *)
(* Admitted. *)

(* Lemma HdRel_lt : forall a y l, *)
(*     HdRel lex_lt a l -> In y l -> lex_lt a y. *)
(* Proof with eauto with bool. *)
(*   introv HR HI. gen a y. induction l; intros... *)
(*   - inverts HI. *)
(*   - Print HdRel. inverts HR. forwards: IHl H0. inverts HI. Print HdRel. *)
(*   applys* SortA_InfA_InA l. 4: now applys* InA_iff_In. *)
(*            eapply eq_equivalence. eapply lex_lt_strorder. *)
(*            eapply NOTF.lt_compat. *)

(* Lemma le_trans : forall s0 s1 s2 : string, NOTF.le s0 s1 -> NOTF.le s1 s2 -> NOTF.le s0 s2. *)
(* Admitted. *)

(* Lemma HdRel_nodup_le : forall a l, *)
(*     Sorted NOTF.le l -> HdRel NOTF.le a l -> HdRel lex_lt a (nodup string_dec l). *)
(* Proof with eauto. *)
(*   introv HS HR. gen a. induction l; intros. *)
(*   - simpl... *)
(*   - inverts HS. inverts HR. *)
(*     simpl. case_if*. *)
(*     + applys* IHl. *)
(*       inverts* H2. constructor... *)
(*       eauto using le_trans. *)
(*     + constructor... *)
(* Abort. (* incorrect: a may be in l *) *)
(* Check lex_lt_trans.  Check NTTLB.leb_trans. *)

(* Lemma sorted_nodup_aux : forall l, *)
(*     sorted (nodup string_dec l) -> Sorted NOTF.le l. *)
(* Abort. (* incorrect *) *)


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

(* Properties of type translation *)
(* Lemma type2list_arrow : forall A B, *)
(*   ~ toplike B -> *)
(*   stype2string (typ_arrow A B) = [ ( "(" ++ (stype2string A) ++ "->" ++ (stype2string B) ++ ")" ) ]. *)
(* Proof. *)
(*   introv NT. *)
(*   simpl. case_if*. apply check_toplike_sound_complete in C. intuition eauto. *)
(* Qed. *)

(* Lemma index_arrow_inv : forall A B, *)
(*     toplike B \/ || typ_arrow A B || = [ "(" ++ || A || ++ "->" ++ || B || ++ ")" ]. *)
(* Proof. *)
(*   introv. destruct (check_toplike B) eqn:HE. *)
(*   { left. applys* check_toplike_sound_complete. } *)
(*   right. unfolds. simpl. case_if*. *)
(* Qed. *)

(* Lemma index_rcd_inv : forall l A, *)
(*     toplike A \/ || typ_rcd l A || = [ "{" ++  l ++ "=>" ++ || A || ++ "}" ]. *)
(* Proof. *)
(*   introv. destruct (check_toplike A) eqn:HE. *)
(*   { left. applys* check_toplike_sound_complete. } *)
(*   right. unfolds. simpl. case_if*. *)
(* Qed. *)


(* Lemma eqIndTyp_toplike : forall A B, *)
(*     eqIndTyp A B -> toplike A <-> toplike B. *)
(* Proof with eauto. *)
(*   introv HE. induction* HE. *)
(*   all: try solve [split; intro H; intuition eauto]. *)
(*   all: try solve [split; intro H; econstructor; inverts H; intuition eauto]. *)
(*   all: try solve [split; intro H; econstructor; inverts H; try inverts H3; try inverts H2; intuition eauto]. *)
(*   all: try solve [split; intro H'; eauto; inverts H'; intuition eauto]. *)
(* Qed. *)

(* (* Lemma test : forall A B, *) *)
(* (*     ||A|| = ||B|| -> type2tlist A = type2tlist B. *) *)
(* (* Proof with intuition eauto. *) *)
(* (*   introv HE. unfold stype2string in HE. rewrite HE. *) *)


(*  Lemma merge_double_nodup : forall l, *)
(*      nodup string_dec (merge l l) = nodup string_dec l. *)
(*  Admitted. *)

(*  Lemma typeindex_nodup_elim : forall A, *)
(*      nodup string_dec (|| A ||) = || A ||. *)
(* Proof with eauto. *)
(*   introv. applys nodup_fixed_point. applys typeindex_nodup. *)
(* Qed. *)

(* #[local] Hint Rewrite typeindex_nodup_elim : merge. *)
(* #[local] Hint Resolve typeindex_sorted : core. *)
