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
    | Application : DeBruijn -> DeBruijn -> DeBruijn
    | Protect : DeBruijn -> DeBruijn.

Check Application (Lambda (Var 0)) (Lambda (Var 0)).

Fixpoint deprotect (t: DeBruijn) :=
    match t with
    | Var n => Var n
    | Lambda tp => Lambda (deprotect tp)
    | Application tp1 tp2 => Application (deprotect tp1) (deprotect tp2)
    | Protect tp => deprotect tp
    end
.

(* Basically "detects" if a terms contains a protected subterm *)
Fixpoint protected (t: DeBruijn) : Prop :=
    match t with
    | Var n => False
    | Lambda tp => protected tp
    | Application tp1 tp2 => (protected tp1) \/ (protected tp2)
    | Protect tp => True
    end
.

(* This is a safe term, without any protected subterm *)
Notation "S( t )" := (~(protected t)).

Lemma protect_correctuion_aux_0_0 : 
    (False \/ False) = False.
Proof.
    admit.
Admitted.

Lemma destruct_false_or : forall (P: Prop), forall (Q: Prop),
    ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
    intuition.
Qed.
    

Lemma deprotect_correction : forall (t: DeBruijn),
    S(deprotect t).
Proof.
    intros.
    induction t.
    simpl. auto.
    simpl. exact IHt.
    simpl. apply <- destruct_false_or. split. exact IHt1. exact IHt2. 
    simpl. exact IHt.
Qed. 

Lemma lambda_equal : forall (t: DeBruijn), forall (u: DeBruijn),
    Lambda t = Lambda u -> t = u.
Proof.
    intro t. intro u.
    case. trivial.
Qed.

Theorem safe_deprotect : forall (t: DeBruijn),
    S(t) -> deprotect(t) = t.
Proof.
    induction t.
    simpl. reflexivity.
    simpl. assert (deprotect t =  t -> Lambda (deprotect t) = Lambda t).
    intro. rewrite H. reflexivity. intro. apply H. apply IHt. exact H0.
    simpl. intro. apply destruct_false_or in H. destruct H.
    assert (deprotect t1 = t1). apply IHt1. exact H.
    assert (deprotect t2 = t2). apply IHt2. exact H0.
    rewrite H1. rewrite H2. reflexivity.
    simpl. contradiction.
Qed.

(* Question 2 *)

Fixpoint max_var_smaller_n_depth (t: DeBruijn) (n: nat) (depth: nat) : Prop :=
    match t with
    | Var v => v < n + depth
    | Lambda tp => max_var_smaller_n_depth tp n (depth + 1)
    | Application tp0 tp1 => (max_var_smaller_n_depth tp0 n depth) /\ (max_var_smaller_n_depth tp1 n depth)
    | Protect tp => max_var_smaller_n_depth tp n depth
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
    simpl. intros.
    apply IHt. exact H.
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
    n <= m -> C[n](t) -> C[m](t).
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
(* TODO change this to a unique depth-shift. *)
Fixpoint correct_free_variable_depth (t: DeBruijn) (depth: nat) :=
    match t with
    | Var n => if depth <=? n then Var (n + 1) else Var n
    | Lambda tp => Lambda (correct_free_variable_depth tp (depth + 1))
    | Application tp0 tp1 => Application (correct_free_variable_depth tp0 depth) (correct_free_variable_depth tp1 depth)
    | Protect tp => Protect (correct_free_variable_depth tp depth)
    end
.

Definition correct_free_variable (t: DeBruijn) :=
    correct_free_variable_depth t 0
.

Fixpoint substitution (t: DeBruijn) (index: nat) (u: DeBruijn) : DeBruijn :=
    match t with
    | Var n => if n =? index then (Protect u) else (Var n)
    | Lambda tp => Lambda (substitution tp (index + 1) (correct_free_variable u))
    | Application tp0 tp1 => Application (substitution tp0 index u) (substitution tp1 index u)
    | Protect tp => Protect tp
    end
.

Notation "t [ y <- u ]" := (deprotect (substitution t y u)) (at level 0).

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
    rewrite H. reflexivity.
Qed.

Lemma aux_1_1 : forall (t1: DeBruijn), forall (t2: DeBruijn), forall (u1: DeBruijn), forall (u2: DeBruijn),
    t1 = u1 -> t2 = u2 -> Application t1 t2 = Application u1 u2.
Proof.
    intros.
    rewrite H. rewrite H0. reflexivity.
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
    simpl. exact IHt.
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
    simpl. apply IHt. simpl in H. simpl. exact H.
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

Lemma protect_aux_0 : forall (t: DeBruijn), forall (u: DeBruijn),
    t = u -> deprotect t = deprotect u.
Proof.
    intros.
    rewrite H. reflexivity.
Qed.

Theorem substitution_aux : forall (t: DeBruijn), forall (n: nat), 
    C[n](t) -> forall (u: DeBruijn), t[n <- u] = deprotect t.
Proof.
    intro t. 
    induction t.
    simpl. intros. 
    assert (forall (n: nat), deprotect (Var n) = Var n).
    simpl. reflexivity. rewrite <- H0. apply protect_aux_0.
    apply aux_0_1. exact H.
    simpl. intros. apply aux_1_0. 
    apply IHt with (n := n + 1). apply aux_2_2 with (t := t) (n := n). exact H.
    intros.
    simpl. apply aux_3 in H. 
    destruct H.
    rewrite IHt1. exact H.
    rewrite IHt2. exact H0.
    reflexivity.
    intros. simpl. reflexivity.
Qed.

Theorem substitution_thm_general : forall (t: DeBruijn),
    closed t -> forall (u: DeBruijn), forall (n: nat), t[n <- u] = deprotect t.
Proof.
    intros.
    apply substitution_aux.
    apply closed_universal.
    trivial.
Qed.

Theorem substitution_thm : forall (t: DeBruijn),
    C(t) -> S(t) -> forall (u: DeBruijn), forall (n: nat), t[n <- u] = t.
Proof.
    intro t. intro C. intro S.
    assert (deprotect t = t).
    apply safe_deprotect. exact S.
    pattern (t) at 2. rewrite <- H.
    apply substitution_thm_general.
    exact C.
Qed.


Theorem raw_substitution_aux : forall (t: DeBruijn), forall (n: nat), 
    C[n](t) -> forall (u: DeBruijn), substitution t n u = t.
Proof.
    intro t. 
    induction t.
    simpl. intros. 
    simpl. apply aux_0_1. exact H.

    move => n H u. simpl. apply aux_1_0. simpl.
    assert (C[n + 1](t)). apply aux_2_2. exact H. 
    apply (IHt (n + 1) H0 (correct_free_variable u)).
    move => n H u. simpl. apply aux_3 in H.
    destruct H.
    rewrite (IHt1 n H u).
    rewrite (IHt2 n H0 u).
    reflexivity.
    move => n C u.
    simpl. reflexivity.
Qed.

Theorem raw_substitution_thm_general : forall (t: DeBruijn),
    closed t -> forall (u: DeBruijn), forall (n: nat), substitution t n u = t.
Proof.
    intros.
    apply raw_substitution_aux.
    apply closed_universal.
    trivial.
Qed.

(* Question 4 *)

Fixpoint substitution_multiple_aux (t: DeBruijn) (offset: nat) (u: list DeBruijn) : DeBruijn :=
    match u with
    | [] => t
    | hd :: tl => 
    substitution (substitution_multiple_aux t (offset + 1) tl) (offset) hd
    end
.

Definition substitution_multiple (t: DeBruijn) (base: nat) (u: list DeBruijn) :=
    substitution_multiple_aux t base u.

Notation "t [ n <-- l ]" := (deprotect (substitution_multiple t n l)) (at level 0).

Theorem substitution_multiple_nil : forall (t: DeBruijn), forall (n: nat),
    S(t) -> t[n <-- []] = t.
Proof.
    intros.
    unfold substitution_multiple.
    unfold substitution_multiple_aux.
    apply safe_deprotect. exact H.
Qed.

Lemma substitution_multiple_one_step : forall (t: DeBruijn), forall (n: nat), 
    forall (u: DeBruijn), forall (terms: list DeBruijn),
    S(t) -> substitution_multiple t n (u :: terms) = 
        substitution (substitution_multiple t (n + 1) terms) n u.
Proof.
    intros.
    induction terms.
    unfold substitution_multiple.
    unfold substitution_multiple_aux.
    reflexivity.
    unfold substitution_multiple.
    unfold substitution_multiple_aux. simpl.
    assert (n + 1 + 1 = n + 2). lia. rewrite H0. reflexivity.
Qed.

Theorem substitution_multiple_C_0 : forall (t: DeBruijn), forall (n: nat),
    C[n](t) -> S(t) -> forall (u: list DeBruijn), forall (m: nat),
    m >= n -> substitution_multiple t m u = t.
Proof.
    move => t n C S.
    induction u.
    unfold substitution_multiple.
    move => m cmp.
    unfold substitution_multiple_aux. reflexivity.

    move => m cmp.
    rewrite (substitution_multiple_one_step t m a u S).

    assert (m + 1 >= n). lia.
    rewrite (IHu (m + 1) H).

    apply raw_substitution_aux. apply (heredite_3 t n m). lia. exact C.
Qed.

Theorem substitution_multiple_C_thm : forall (t: DeBruijn), forall (n: nat),
    C[n](t) -> S(t) -> forall (u: list DeBruijn), t[n <-- u] = t.
Proof.
    move => t n C S u.
    assert (n >= n). lia.
    rewrite (substitution_multiple_C_0 t n C S u n H). 
    apply safe_deprotect. exact S.
Qed.

Fixpoint C_multiple (u: list DeBruijn) (n: nat) : Prop :=
    match u with
    | [] => True
    | hd :: tl => (C[n](hd)) /\ (C_multiple tl n)
    end
.

Notation "Cm[ n ]( u )" := (C_multiple (List.tl u) n).

Lemma sub_preserves_equality : forall (t: DeBruijn), forall (u: DeBruijn), 
    forall (n: nat), forall (v: DeBruijn),
    t = u -> t[n <- v] = u[n <- v].
Proof.
    move => t u n v E.
    rewrite E.
    reflexivity.
Qed.

Lemma substitute_equal : forall (t: DeBruijn), forall (n: nat),
    S(t) -> t[n <- Var n] = t.
Proof.
    move => t.
    induction t.
    simpl. admit.
    simpl.
    move => n S. assert (correct_free_variable (Var n) = Var (n + 1)).
    unfold correct_free_variable. simpl. reflexivity. rewrite H.
    rewrite (IHt (n + 1)). exact S. reflexivity.
    move => n S.
    simpl. rewrite IHt1. 
    simpl in S. apply destruct_false_or in S.
    destruct S. exact H.
    simpl. rewrite IHt2.
    simpl in S. apply destruct_false_or in S.
    destruct S. exact H0. reflexivity.
    move => n. unfold protected.
    contradiction.
Admitted.

Lemma cm_add : forall (u: list DeBruijn), forall (n: nat), forall (a: DeBruijn),
    Cm[n](a::u) -> C_multiple u n.
Proof.
    move => u n a Cm.
    unfold C_multiple in Cm.
    unfold C_multiple.
    trivial.
Qed.

Lemma cm_completion : forall(u : list DeBruijn), forall(a: DeBruijn), forall (n: nat),
    Cm[n](u) -> C[n](List.hd (Var 0) u) -> Cm[n](a :: u).
Proof.
    move => u a n Cm C.
    induction u.
    trivial.
    simpl.
    split.
    simpl in C. exact C.
    apply (cm_add u n a0).
    exact Cm.
Qed.

Lemma list_prop_completion : forall (t: list DeBruijn), forall (a: DeBruijn),
    forall (f: DeBruijn -> Prop),
    (List.Forall f t) -> f a -> (List.Forall f (a :: t)).
Proof.
    move => t a f.
    intuition.
Qed.

Lemma cm_conversion : forall (u: list DeBruijn), forall(n: nat),
    C_multiple u n -> Cm[n](u).
Proof.
    move => u n.
    induction u.
    simpl. trivial.
    simpl. intuition.
Qed.

Lemma cm_truc : forall (u: list DeBruijn), forall (a: DeBruijn), forall (b: DeBruijn),
    forall (n: nat),
    Cm[n](a :: b :: u) -> C[n](b).
Proof.
    intros.
    unfold C_multiple in H. simpl in H.
    destruct H.
    exact H.
Qed.

Lemma cm_truc_2 : forall (u: list DeBruijn), forall (a: DeBruijn), forall (b: DeBruijn),
    forall (n: nat),
    Cm[n](a :: b :: u) -> Cm[n](u).
Proof.
    intros.
    unfold C_multiple in H. simpl in H.
    destruct H. apply (cm_conversion u n).
    fold C_multiple in H0.
    exact H0.
Qed.

Lemma cm_truc_3 : forall (u: list DeBruijn), forall (a: DeBruijn), forall (n: nat),
    Cm[n](a :: u) -> Cm[n](u).
Proof.
    induction u.
    simpl. intuition.
    move => a0 n.
    simpl. intuition.
Qed.

Lemma cm_meaning : forall (u: list DeBruijn), forall (n: nat),
    Cm[n](u) -> List.Forall (fun x => C[n](x)) (List.tl u).
Proof.
    move => u n Cm.
    induction u. simpl.
    intuition.
    
    simpl.
    induction u. intuition. 
    apply (list_prop_completion u a0 (max_var_smaller_n^~ n)).
    assert (Cm[n](u)). apply (cm_truc_2 u a a0 n). exact Cm.
    assert C[n](a0). apply (cm_truc u a a0 n). exact Cm.
    assert (Cm[n](a0::u)). apply (cm_truc_3 (a0::u) a n). exact Cm.
    apply IHu. exact H1. apply (cm_truc u a a0). exact Cm.
Qed.

Theorem substitution_multiple_C_1 : forall (t: DeBruijn), forall (n: nat),
    forall (terms: list DeBruijn),
    S(t) -> Cm[n](terms) -> t[n <-- terms] = (t[n+1 <-- List.tl terms])[n <- List.hd (Var n) terms].
Proof.
    move => t n terms S Cm.
    induction terms.
    simpl. rewrite (safe_deprotect t S).
    assert (t[n <- Var n] = t -> t = t[n <- Var n]). intuition.
    apply H.
    apply (substitute_equal t n S).

    simpl.


    (*apply (sub_preserves_equality 
        (substitution_multiple t (n + 1) terms)
        ((t) [n + 1 <-- terms]) 
        (n) 
        (a)).
    rename a into hd.*)

    
    
    

    
