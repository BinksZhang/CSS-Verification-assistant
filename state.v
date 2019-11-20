Require Import util Logic.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(*定义五元组来表示系统状态*)

(*Sv, Sb, Sf*)
Definition storeV := id -> nat.
Definition storeB := id -> nat.
Definition storeF := id -> list nat.

(*Hv,Hb因为可能对应不到值,所以用可选类型*)
Definition heapV := nat -> option nat.
Definition heapB := nat -> option nat.

(*定义空堆*)
Definition emp_heapV : heapV :=
  fun (n: nat) => None.

Definition emp_heapB : heapB :=
  fun (n: nat) => None.

(*定义命题 : 在堆的定义域中*)
Definition in_domV (l: nat) (hv: heapV) : Prop :=
  exists n, hv l = Some n.

Definition in_domB (l: nat) (hb: heapB) : Prop :=
  exists n, hb l = Some n.

(*定义命题 : 不在堆的定义域中*)
Definition not_in_domV (l: nat) (hv: heapV) : Prop :=
  hv l = None.

Definition not_in_domB (l: nat) (hb: heapB) : Prop :=
  hb l = None.

(*在定义域的(Some n) + 不在定义域的(None) 为全集*)
Theorem in_not_in_dec_V :
  forall l h, {in_domV l h} + {not_in_domV l h}.
Proof.
  intros l h.
  unfold in_domV, not_in_domV.
  destruct (h l).
  - left. exists n. auto.
  - right. auto.
Qed.

Theorem in_not_in_dec_B :
  forall l h, {in_domB l h} + {not_in_domB l h}.
Proof.
  intros l h.
  unfold in_domB, not_in_domB.
  destruct (h l).
  - left. exists n. auto.
  - right. auto.
Qed.

(*定义命题:两堆不相交*)
Definition disjointV (h1 h2: heapV) : Prop :=
  forall l, not_in_domV l h1 \/ not_in_domV l h2.

Definition disjointB (h1 h2: heapB) : Prop :=
  forall l, not_in_domB l h1 \/ not_in_domB l h2.

(*heap1 析取 heap2*)
Definition h_unionV (h1 h2: heapV) : heapV :=
  fun l =>
    if (in_not_in_dec_V l h1) then h1 l else h2 l.

Definition h_unionB (h1 h2: heapB) : heapB :=
  fun l =>
    if (in_not_in_dec_B l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subsetV (h1 h2: heapV) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.

Definition h_subsetB (h1 h2: heapB) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.


(* store update *)
Definition sV_update (s: storeV) (x: id) (n: nat) : storeV :=
  fun x' => if beq_id x x' then n else s x'.

Definition sB_update (s: storeB) (x: id) (n: nat) : storeB :=
  fun x' => if beq_id x x' then n else s x'.

Definition sF_update (s: storeF) (x: id) (nli: list nat) : storeF :=
  fun x' => if beq_id x x' then nli else s x'.

Notation "x '!sv->' v ';' m" := (sV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!sb->' v ';' m" := (sB_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!sf->' v ';' m" := (sF_update m x v)
            (at level 100, v at next level, right associativity).

(* heap update *)
Definition hV_update (h: heapV) (l: nat) (n: nat) : heapV :=
  fun l' => if beq_nat l l' then Some n else h l'.

Definition hB_update (h: heapB) (l: nat) (n: nat) : heapB :=
  fun l' => if beq_nat l l' then Some n else h l'.

Notation "x '!hv->' v ';' m" := (hV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!hb->' v ';' m" := (hB_update m x v)
            (at level 100, v at next level, right associativity).


(* heap remove *)
Definition hV_remove (h:heapV) (l:nat) : heapV :=
fun x => if beq_nat x l then None else h x.

Definition hB_remove (h:heapB) (l:nat) : heapB :=
fun x => if beq_nat x l then None else h x.

(****Some Lemma****)
Lemma sV_update_eq : forall storeV x v,
   (x !sv-> v ; storeV) x = v.
Proof.
  intros.
  unfold sV_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma sB_update_eq : forall storeB x v,
   (x !sb-> v ; storeB) x = v.
Proof.
  intros.
  unfold sB_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma sF_update_eq : forall storeF x v,
   (x !sf-> v ; storeF) x = v.
Proof.
  intros.
  unfold sF_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma hV_update_eq : forall heapV x v,
   (x !hv-> v ; heapV) x = Some v.
Proof.
  intros.
  unfold hV_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma hB_update_eq : forall heapB x v,
   (x !hb-> v ; heapB) x = Some v.
Proof.
  intros.
  unfold hB_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem hB_update_neq :forall hB x1 x2 v,
   x1 <> x2
->(x2 !hb-> v ; hB) x1 = hB x1.
Proof.
  intros.
  unfold hB_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sV_update_shadow : forall storeV x v1 v2,
  (x !sv-> v2 ; x !sv-> v1 ; storeV) = (x !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sB_update_shadow : forall storeB x v1 v2,
  (x !sb-> v2 ; x !sb-> v1 ; storeB) = (x !sb-> v2; storeB).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sB_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sF_update_shadow : forall storeF x v1 v2,
  (x !sf-> v2 ; x !sf-> v1 ; storeF) = (x !sf-> v2; storeF).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sF_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hV_update_shadow : forall heapV x v1 v2,
  (x !hv-> v2 ; x !hv-> v1 ; heapV) = (x !hv-> v2; heapV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hV_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hB_update_shadow : forall heapB x v1 v2,
  (x !hb-> v2 ; x !hb-> v1 ; heapB) = (x !hb-> v2; heapB).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hB_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

(*定义五元组*)
Definition state : Type := (storeV * storeB * storeF * heapV * heapB).

(*定义状态转换*)
Inductive ext_state : Type :=
|  St: state -> ext_state    (* normal state *)
| Abt: ext_state.            (* abort *)


