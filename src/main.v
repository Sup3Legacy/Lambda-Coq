(* Question 1 *)

Inductive DeBruijn :=
    | Var : nat -> DeBruijn
    | Lambda : DeBruijn -> DeBruijn
    | Application : DeBruijn -> DeBruijn -> DeBruijn.

Check Application (Lambda (Var 0)) (Lambda (Var 0)).

(* Question 2 *)

Fixpoint max_var (t: DeBruijn) (c: nat) : nat :=
    match t with
    | Var n => n - c
    | Lambda tp => max_var tp (c + 1)
    | Application tp0 tp1 => max (max_var tp0 c) (max_var tp1 c)
    end.

Definition var_less_equal_n (T: DeBruijn) (n: nat) :=
    (max_var T 0) <= n.

Definition terme_clos (T: DeBruijn) :=
    var_less_equal_n T 0.

Fixpoint substitution (T: DeBruijn) (index: nat) (S: DeBruijn) :=
    match T with
    | Var n =>
        match (Nat.eqb index n) with 
        | true => S
        | false => Var n
        end
    | Lambda tp => Lambda (substitution tp index S)
    | Application tp0 tp1 => Application (substitution tp0 index S) (substitution tp1 index S)
    end.

Theorem substitution_clos: forall T: DeBruijn, 
    terme_clos T -> forall index: nat, forall S: DeBruijn, 
    (substitution T index S) = T.
Proof.
    intros.
    induction T.

Lemma recurrence_var_less: forall T: DeBruijn, forall n: nat,
    var_less_equal_n T n -> var_less_equal_n T (n + 1).
Proof.
    intro.
    intro.
    intro.
    destruct H.


