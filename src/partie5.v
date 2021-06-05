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

Lemma tau_comp_identity_wtf :
    forall (t: DeBruijn), tau (CompState t) = tau_code (Comp t)
.
Proof.
    intro t.
    induction t.
    trivial.
    
    simpl. unfold tau_environment.
    simpl. assert (S(tau_code (Comp t))). apply (protected_tau (Comp t)).
    rewrite safe_deprotect. exact H.
    reflexivity. 
    
    simpl. 
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

Theorem tau_compt_identity :
    forall (t: DeBruijn), S(t) -> tau(CompState t) = t
.
Proof.
    induction t.

    simpl.
    trivial.

    simpl. unfold tau_environment. simpl. move => S.
    assert (deprotect (tau_code (Comp t)) = tau_code (Comp t)).
    apply safe_deprotect. apply protected_tau. rewrite H.
    rewrite <- tau_comp_identity_wtf. rewrite IHt. exact S. reflexivity.

    move => S. simpl in S. apply destruct_false_or in S. destruct S.
    simpl. unfold tau_environment. simpl.
    assert (deprotect (tau_code (Comp t1)) = tau_code (Comp t1)).
    apply (safe_deprotect (tau_code (Comp t1))). apply protected_tau. rewrite H1.
    clear H1.
    assert (deprotect (tau_code (Comp t2)) = tau_code (Comp t2)).
    apply (safe_deprotect (tau_code (Comp t2))). apply protected_tau. rewrite H1.
    clear H1.
    rewrite <- tau_comp_identity_wtf. rewrite IHt1. exact H. 
    rewrite <- tau_comp_identity_wtf. rewrite IHt2. exact H0. reflexivity.

    intuition. simpl in H. contradiction H. trivial.
Qed.

Fixpoint stack_length (e: Environment) :=
    match e with
    | Nil => 0
    | Stack a suite => 1 + (stack_length suite)
    end 
.

Inductive correct_stack_old : Stack_type -> Prop :=
    | nil_correct : correct_stack_old Nil
    | correct_trans : forall (c_0: Instruction),
        forall (e_0: Environment), forall (e: Environment),
        (C[stack_length e_0](tau_code(c_0))) -> 
        correct_stack_old e_0 -> correct_stack_old e -> correct_stack_old (Stack (c_0, e_0) e)
.

Fixpoint correct_stack (s: Stack_type) :=
    match s with 
    | Nil => True
    | Stack (i, sp) spp =>
        C[stack_length sp](tau_code i) /\ correct_stack sp /\ correct_stack spp
    end
.

Print correct_stack.

Definition correct_state : State -> Prop :=
    fun '(c, e, s) => correct_stack (Stack (c, e) s)
.

Notation "CoS( s )" := (correct_state s).

Definition correct_option_state (t: StateOption) :=
    match t with
    | None => True
    | Some s => CoS(s)
    end
.

Notation "CoSo( s )" := (correct_option_state(s)).

(*
Lemma stupid_2: forall (P: Prop), forall (Q: Prop),
    P -> Q \/ P
.
Proof.
    intuition.
Qed.

Lemma stupid_3: forall (P: Prop), forall (Q: Prop),
    P -> Q -> Q /\ P
.
Proof.
    intuition.
Qed.

Lemma stupid_4: forall (s: State),
    CoS(s) -> CoSo(Some s)
.
Proof.
    intuition.
Qed.

Lemma stupid_5: forall (s: State), forall (r: State),
    Some s = Some r -> s = r
.
Proof.
    move => s r.
    case. trivial.
Qed.
*)

Lemma state_trans_aux : forall (s1: State),
    CoS(s1) -> CoSo(step_krivine s1)
.
Proof.
    move => s1 CoS_s1.
    destruct s1.
    destruct p.
    induction i.

    +   simpl. case_eq n.
        induction e.
        *   simpl. trivial.

        *   destruct p.
            simpl. simpl in CoS_s1.
            intuition.

        *   move => n0 prop.
            case_eq e.
            -   simpl. trivial.
            -   intuition.
                simpl. simpl in CoS_s1. intuition. unfold max_var_smaller_n.
                unfold max_var_smaller_n in H0. rewrite prop in H0. rewrite H in H0.
                simpl in H0. simpl. lia.
                rewrite H in H2.
                simpl in H2.
                intuition.

    +   simpl.
        case_eq s.
        -   simpl. intuition.
        
        -   intuition. simpl.
            simpl in CoS_s1.
            intuition.
            unfold max_var_smaller_n. unfold max_var_smaller_n in H0.
            rewrite (inutile_1 (stack_length e)).
            apply -> (aux_2_1 (tau_code i) (stack_length e) 0). exact H0.
            rewrite H in H3. simpl in H3.
            intuition.
            rewrite H in H3. simpl in H3.
            intuition.
            rewrite H in H3. simpl in H3.
            intuition.

    +   simpl. simpl in CoS_s1. intuition. unfold max_var_smaller_n in H.
        simpl in H.
        destruct H.
        exact H0.
        simpl in H.
        destruct H.
        exact H.
Qed.

Theorem state_trans : forall (s1 s2: State),
    CoS(s1) -> step_krivine s1 = Some s2 -> CoS(s2)
.
Proof.
    move => s1 s2 CoS1 eq.
    assert (CoSo(step_krivine s1)).
    apply (state_trans_aux s1 CoS1).
    rewrite eq in H.
    simpl in H. exact H.
Qed.


Theorem transition_beta : forall (s1 s2: State),
    CoS(s1) -> step_krivine s1 = Some s2 -> 
        (((tau s1) -b> (tau s2)) \/ ((tau s1) = (tau s2)))
.
Proof.
    intro s1; case s1; clear s1.
    intro p; case p; clear p.
    move => i e s.
    intro s2; case s2; clear s2.
    intro p; case p; clear p.
    move => i0 e0 s0.
    intro C. intro H.

    inversion H.

    case_eq i.
    intuition. rewrite H0 in H1.
    induction n.
    simpl.

    destruct s1.
    destruct p.
    induction i.
    induction e.
    induction s.
    intuition. simpl. simpl in H0.
    case_eq n. 
    intuition. rewrite H1 in H0. discriminate.
    intuition. rewrite H1 in H0. discriminate.
    intuition.
    simpl in H0.
    case_eq n. 
    intuition. rewrite H1 in H0. discriminate.
    intuition. rewrite H1 in H0. discriminate.

    intuition. simpl in H0. case_eq n.
    intuition. rewrite H1 in H0. assert ((a, b, s) = s2). admit.
    rewrite <- H2.
    simpl. rewrite H1 in H. simpl in H.

    induction s1. destruct a.
    induction b. 
    induction i.
    intuition.
    case_eq n.
    intuition.
    simpl in H0. rewrite H1 in H0. simpl.
    induction e.
    discriminate.
    simpl in IHe. destruct p.
    assert ((i, s, Nil) = s2). admit.
    rewrite <- H2. simpl. unfold tau_environment. simpl.
    
    assert ((substitution_multiple (Var 0) 1 (tau_environment_aux e)) = Var 0).
    apply (substitution_multiple_C_0 (Var 0) 1). unfold max_var_smaller_n. simpl. lia.
    unfold protected. intuition. lia.
    rewrite H3. simpl.
    assert (S((tau_code i) [0 <-- tau_environment_aux s])). apply deprotect_correction.
    
    assert (deprotect (tau_code i) [0 <-- tau_environment_aux s] =
    (tau_code i) [0 <-- tau_environment_aux s]). apply safe_deprotect.
    exact H4.
    rewrite H5. intuition.

    intuition. simpl.
    simpl in H0.
    rewrite H1 in H0.
    induction e. discriminate.
    destruct p. assert ((Access n0, e, Nil) = s2). admit.
    rewrite <- H2.
    case_eq e. intuition. rewrite H3 in IHe. simpl in IHe.
    simpl. unfold tau_environment. simpl. simpl in H. intuition.
    simpl. 

    
    
    
    
    simpl in CoS_s1. simpl in step. simpl in IHe.
    intuition.
    case_eq n. intuition. rewrite H3 in step.
    rewrite H3 in H0. destruct p. 
    unfold tau_environment. simpl. intuition. 


    induction i.
    *   simpl.
        induction s. simpl.
        +   induction e.
            -   simpl in step.
                intuition. unfold tau_environment. simpl.
                case_eq n. 
                intuition. rewrite H in step. 
                discriminate.

                intuition. rewrite H in step. discriminate.
            -   case_eq n.
                intuition. rewrite H in CoS_s1. simpl in CoS_s1.
                rewrite H in step. simpl in step. destruct p.
                rewrite H in IHe. simpl in IHe. intuition.
                
        
    
