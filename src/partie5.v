Add LoadPath "." as CoqDirectory.
Load partie4.

Fixpoint tau_code (t: Instruction) : DeBruijn :=
    match t with
    | (Access n)=> Var n
    | (Push cp c) => Application (tau_code cp) (tau_code c)
    | Grab c => Lambda (tau_code c)
    end
.
(* τ((c0,e0).e)  =  [0←τ(c0)[0←τ(e0)],u1...un]oùτ(e) = [0←u1...un] *)

Fixpoint tau_environment_aux (e: Environment) : list DeBruijn :=
    match e with 
    | Stack (c_0, e_0) e_suite => 
        ((tau_code(c_0))[0 <-- (tau_environment_aux e_0)]) :: (tau_environment_aux e_suite)
    | Nil => []
    end 
.

Definition tau_environment : Environment -> DeBruijn -> DeBruijn :=
    fun e t => t[0 <-- (tau_environment_aux e)]
.

Fixpoint tau_aux (c: Instruction) (e: Environment) (s: Stack_type) : DeBruijn :=
    match s with
    | Stack (c_0, e_0) s_suite =>
        Application (tau_environment e (tau_code c)) (tau_aux c_0 e_0 s_suite)
    | Nil => tau_environment e (tau_code c)
    end
.

Definition tau : State -> DeBruijn :=
    (fun '(c, e, s) => tau_aux c e s)
.

Lemma protected_tau :
    forall (c: Instruction), S(tau_code c)
.
Proof.
    intro c.
    induction c.
    intuition.
    intuition.
    intuition.
    unfold tau_code in H. simpl in H. intuition.
Qed.

Theorem tau_comp_identity :
    forall (t: DeBruijn), tau (CompState t) = tau_code (Comp t)
.
Proof.
    intro t.
    induction t.
    trivial.
    simpl. unfold tau_environment.
    simpl. assert (S(tau_code (Comp t))). apply (protected_tau (Comp t)).
    rewrite safe_deprotect. exact H.
    reflexivity. simpl. 
    unfold tau_environment.
    assert (tau_environment_aux Nil = []). auto.
    rewrite H. rewrite (substitution_multiple_nil). 
    assert (S(tau_code (Comp t1))). apply (protected_tau (Comp t1)).
    assert (S(tau_code (Comp t2))). apply (protected_tau (Comp t2)).
    assert (S(tau_code (Comp t1)) /\ S(tau_code (Comp t2))). intuition.
    unfold protected. intuition. reflexivity.
    simpl. unfold tau_environment.
    intuition.
Qed.

Print substitution_multiple_commut.

Fixpoint stack_length (e: Environment) :=
    match e with
    | Nil => 0
    | Stack a suite => 1 + (stack_length suite)
    end 
.

Inductive correct_stack : Stack_type -> Prop :=
    | nil_correct : correct_stack Nil
    | correct_trans : forall (c_0: Instruction),
        forall (e_0: Environment), forall (e: Environment),
        (C[stack_length e_0](tau_code(c_0))) -> 
        correct_stack e_0 -> correct_stack e -> correct_stack (Stack (c_0, e_0) e)
.

Definition correct_state : State -> Prop :=
    fun '(c, e, s) => correct_stack (Stack (c, e) s)
.

Notation "CoS( s )" := (correct_state s).

Definition correct_option_state (t: StateOption) :=
    match t with
    | None => False
    | Some s => CoS(s)
    end
.

Notation "CoSo( s )" := (correct_option_state(s)).

Theorem correct_state_trans : forall (s1: State), forall (s2: State),
    CoS(s1) -> step_kirvine s1 = Some s2 -> CoS(s2)
.
Proof.
    move => s1 s2 CoS_s1 s1_s2_rel.
    induction s1.
    destruct a.
    unfold correct_state.
    unfold correct_state in CoS_s1.
    destruct s2. destruct p.
    pose (s1 := Stack(i, e) b).
    fold s1 in CoS_s1.
    induction s1.
    apply correct_trans.
    destruct step_kirvine in s1_s2_rel.
    contradict s1_s2_rel. intuition.
    

    

    