Require Import Omega.
Require Import Lia.
Require Import ssreflect.
Require Import ssrfun.
Require Import Coq.ssr.ssrbool.

Notation "a :: b" := (cons a b).
Notation "[]" := (nil).


(* Question 1 *)

Inductive DeBruijn :=
    | Var : nat -> DeBruijn
    | Lambda : DeBruijn -> DeBruijn
    | Application : DeBruijn -> DeBruijn -> DeBruijn.

Check Application (Lambda (Var 0)) (Lambda (Var 0)).

(* Question 2 *)

Fixpoint max_var_smaller_n_depth (t: DeBruijn) (n: nat) (depth: nat) : Prop :=
    match t with
    | Var v => v < n + depth
    | Lambda tp => max_var_smaller_n_depth tp n (depth + 1)
    | Application tp0 tp1 => (max_var_smaller_n_depth tp0 n depth) /\ (max_var_smaller_n_depth tp1 n depth)
    end.

Definition max_var_smaller_n (t: DeBruijn) (n: nat) : Prop := 
    max_var_smaller_n_depth t n 0.

Lemma heredite_0: forall (t: DeBruijn), forall (n: nat), forall (d: nat),
    (max_var_smaller_n_depth t n d) -> (max_var_smaller_n_depth t (n+1) d).
Proof.
    move => t.
    induction t.
    simpl. lia.
    simpl. intro n. intro d.
    apply IHt.
    intro n. intro d.
    simpl.
    case. intro H1. intro H2.
    split.
    apply IHt1. apply H1.
    apply IHt2. apply H2.
Qed.
    
Notation "C[ n ]( t )" := (max_var_smaller_n t n).

Lemma inutile_0 : forall (n: nat),
    n + 0 = n.
Proof.
    intro.
    lia.
Qed.

Lemma inutile_1 : forall (n: nat),
    S n = n + 1.
Proof.
    intro.
    lia.
Qed.

Lemma inutile_2 : forall (n: nat), forall (m: nat), forall (p: nat),
    n + m + p = n + (m + p).
Proof.
    intros.
    lia.
Qed.

Lemma heredite_1 : forall (t: DeBruijn), forall (n: nat),
    C[n](t) -> C[n + 1](t).
Proof.
    intros. apply heredite_0. exact H.
Qed.

Lemma heredite_2 : forall (t: DeBruijn), forall (n: nat), forall (m: nat),
    C[n](t) -> C[n + m](t).
Proof.
    intros.
    induction m.
    simpl. rewrite -> inutile_0. exact H.
    rewrite inutile_1. rewrite <- inutile_2.
    apply heredite_1 with (t := t) (n := n + m). exact IHm.
Qed. 

Lemma heredite_3 : forall (t: DeBruijn), forall (n: nat), forall (m: nat),
    n < m -> C[n](t) -> C[m](t).
Proof.
    intros.
    assert (n + (m - n) = m). lia.
    rewrite <- H1.
    apply heredite_2.
    exact H0.
Qed.

Definition closed (T: DeBruijn) :=
    C[0](T).

Notation "C( t )" := (closed t).

Theorem closed_universal : forall (t: DeBruijn),
    C(t) -> forall (n: nat), C[n](t).
Proof.
    intros.
    induction n.
    exact H.
    assert (n+1 = S n).
    lia.
    rewrite <- H0.
    apply heredite_1 with (t := t) (n := n).
    exact IHn.
Qed.


(* Question 3 *)

Fixpoint correct_free_variable_depth (t: DeBruijn) (depth: nat) :=
    match t with
    | Var n => if depth <=? n then Var (n + 1) else Var n
    | Lambda tp => Lambda (correct_free_variable_depth tp (depth + 1))
    | Application tp0 tp1 => Application (correct_free_variable_depth tp0 depth) (correct_free_variable_depth tp1 depth)
    end
.

Definition correct_free_variable (t: DeBruijn) :=
    correct_free_variable_depth t 0
.

Fixpoint substitution (t: DeBruijn) (index: nat) (u: DeBruijn) : DeBruijn :=
    match t with
    | Var n => if n =? index then u else (Var n)
    | Lambda tp => Lambda (substitution tp (index + 1) (correct_free_variable u))
    | Application tp0 tp1 => Application (substitution tp0 index u) (substitution tp1 index u)
    end
.

Notation "t [ y <- u ]" := (substitution t y u) (at level 0).

Lemma aux_0 : forall (n: nat), forall (n0: nat),
    C[n](Var n0) -> n > n0.
Proof.
    intros.
    induction n.
    unfold max_var_smaller_n in H.
    unfold max_var_smaller_n_depth in H.
    simpl in H. exact H.
    unfold max_var_smaller_n in H.
    unfold max_var_smaller_n_depth in H.
    unfold max_var_smaller_n in IHn.
    unfold max_var_smaller_n_depth in IHn.
    simpl in H. lia.
Qed.


(* Thanks a lot to Samuel Vivien! *)
Lemma aux_0_0 : forall (n: nat), forall (n0: nat),
    n > n0 -> (Nat.eqb n0 n) = false.
Proof.
    intros.
    destruct (PeanoNat.Nat.eqb_neq n0 n).
    apply H1.
    lia.
Qed.

Lemma aux_0_1 : forall (n: nat), forall (n0: nat), forall (u: DeBruijn),
    C[n](Var n0) -> (if n0 =? n then u else Var n0) = Var n0.
Proof.
    intros.
    rewrite aux_0_0. apply aux_0. exact H.
    reflexivity.
Qed.

Lemma aux_1_0 : forall (t: DeBruijn), forall (u: DeBruijn),
    u = t -> Lambda u = Lambda t.
Proof.
    intros.
    induction t.
    rewrite H. reflexivity. 
    rewrite <- H. reflexivity.
    rewrite <- H. reflexivity.
Qed.

Lemma aux_2_0 : forall (t: DeBruijn), forall (n: nat), forall (d: nat),
    max_var_smaller_n_depth t n (d + 1) -> max_var_smaller_n_depth t (n + 1) d.
Proof.
    intro. intro.
    induction t.
    simpl.
    lia.
    simpl.
    intro.
    apply IHt with (d := d + 1).
    simpl. case. case.
    simpl. split.
    apply IHt1 with (d := 0). simpl. exact a.
    apply IHt2 with (d := 0). simpl. exact b.
    split.
    destruct H.
    apply IHt1 with (d := S n0). exact H.
    destruct H.
    apply IHt2 with (d := S n0). exact H0.
Qed.

Lemma aux_2_1 : forall (t: DeBruijn), forall (n: nat), forall (d: nat),
    max_var_smaller_n_depth (Lambda t) n d -> max_var_smaller_n_depth t (n + 1) d.
Proof.
    intros.
    induction t.
    simpl. simpl in H.
    lia.
    simpl in H.
    simpl. apply aux_2_0. exact H.
    simpl. split.
    destruct H.
    apply aux_2_0. exact H.
    destruct H.
    apply aux_2_0. exact H0.
Qed.    

Lemma aux_2_2 : forall (t: DeBruijn), forall (n: nat),
    C[n](Lambda t) -> C[n + 1](t).
Proof.
    intros.
    simpl. apply aux_2_1. exact H.
Qed.

Lemma aux_3 : forall (t1: DeBruijn), forall (t2: DeBruijn), forall (n: nat),
    C[n](Application t1 t2) -> C[n](t1) /\ C[n](t2).
Proof.
    intros. 
    split. 
    unfold max_var_smaller_n. 
    unfold max_var_smaller_n in H.
    unfold max_var_smaller_n_depth in H.
    destruct H.
    fold max_var_smaller_n_depth in H.
    exact H.
    unfold max_var_smaller_n. 
    unfold max_var_smaller_n in H.
    unfold max_var_smaller_n_depth in H.
    destruct H.
    fold max_var_smaller_n_depth in H.
    exact H0.
Qed.

Theorem substitution_aux : forall (t: DeBruijn), forall (n: nat), 
    C[n](t) -> forall (u: DeBruijn), substitution t n u = t.
Proof.
    intro t. 
    induction t.
    simpl. intros. apply aux_0_1. exact H.
    simpl. intros. apply aux_1_0. 
    apply IHt with (n := n + 1). apply aux_2_2 with (t := t) (n := n). exact H.
    intros.
    simpl. apply aux_3 in H. 
    destruct H.
    rewrite IHt1. exact H.
    rewrite IHt2. exact H0.
    reflexivity.
Qed.

Theorem substitution_thm : forall (t: DeBruijn),
    closed t -> forall (u: DeBruijn), forall (n: nat), substitution t n u = t.
Proof.
    intros.
    apply substitution_aux.
    apply closed_universal.
    trivial.
Qed.

(* Question 4 *)

Fixpoint substitution_multiple_aux (t: DeBruijn) (base: nat) (index: nat) (terms: list DeBruijn) :=
    match terms with
    | [] => t
    | h :: q => substitution_multiple_aux (substitution t (base + index) h) base (index + 1) q
    end
.

Definition substitution_multiple (t: DeBruijn) (base: nat) (terms: list DeBruijn) :=
    substitution_multiple_aux t base 0 terms
.

Notation "t [ y <l- l ]" := (substitution_multiple t y l) (at level 0).

Theorem substitution_multiple_nil : forall (t: DeBruijn), forall (n: nat),
    t[n <l- []] = t.
Proof.
    intros.
    unfold substitution_multiple.
    unfold substitution_multiple_aux.
    reflexivity.
Qed.

Theorem substitution_multiple_semi_closed : forall (t: DeBruijn), forall (n: nat), 
    forall (terms: list DeBruijn),
    C[n](t) -> substitution_multiple t n terms = t.

