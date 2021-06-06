Add LoadPath "." as CoqDirectory.
Load partie4.

(* 5.1 *)

(* Ces fonctions ont été pénbibles à faire. En effet, les conventions d'écriture
divergent entre le sujet et Coq. On s'est trompés plusieurs fois (inversions des termes en
compilant/décompilant des Applciation) *)
Fixpoint tau_code (t: Instruction) : DeBruijn :=
    match t with
    | (Access n)=> Var n
    | (Push cp c) => Application (tau_code c) (tau_code cp)
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

(* 5.2 *)

(* Pas mal *)
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

(* Lemme qui est apapremment utile, je ne me souviens plus trop *)
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

(* Théorème plutôt pas mal :
Il nous permet d'être sûr que notre définition de Comp et de Tau sont cohérentes
entre elles. Elles peuvent être fausses par rapport à la définition du sujet mais au
moins elles ont des erreurs qui font qu'elles sont cohérentes : la décompilation 
d'un code compilé retourne bien exactement le code de départ. *)
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

(* 5.3 *)

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

(* Ceci sert à définir le lemme `state_trans_aux` qui raisonen sur une option d'état.
En effet, pour simplifier ce lemme, on ne se donne pas de condition sur "est-ce que la fonction
`step_krivine` a renvoyé un état ou non". La distinction est faite dans le théorème après *)
Definition correct_option_state (t: StateOption) :=
    match t with
    | None => True
    | Some s => CoS(s)
    end
.

Notation "CoSo( s )" := (correct_option_state(s)).

(* Ceci a été un peu pénible à faire mais a finalement marché. *)
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
        exact H.
        simpl in H.
        destruct H.
        exact H0.
Qed.

(* Théorème de 5.3. Simple application du lemme précédent. *)
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

(* 5.4 *)
(* Il nous manquait encore quelques lemmes sur la substitution parallèle *)
Lemma substitution_multiple_lambda_aux : forall (t: DeBruijn), forall (u: list DeBruijn),
    (forall (n: nat),
    substitution_multiple_aux (Lambda t) n u = 
    Lambda (substitution_multiple_aux t (n + 1) u))
.
Proof.
    move => t u.
    induction u.
    move => n.
    simpl. reflexivity.
    simpl. simpl in IHu.
    move => n.
    assert ((substitution_multiple_aux (Lambda t) (n + 1) u) = 
        Lambda (substitution_multiple_aux t (n + 1 + 1) u)).
    exact (IHu (n + 1)).
    rewrite H. simpl. reflexivity.
Qed.

Lemma substitution_multiple_lambda : forall (t: DeBruijn), forall (u: list DeBruijn),
    (forall (n: nat),
    substitution_multiple (Lambda t) n u = 
    Lambda (substitution_multiple t (n + 1) u))
.
Proof.
    intuition.
    unfold substitution_multiple.
    exact (substitution_multiple_lambda_aux t u n).
Qed.

(* Lemme (pour une fois) pas si stupide que ça. La propriété n'était pas TOTALEMENT évidente 
(note de la rédaction: en fait si)*)
Lemma stupide : forall (t1 t2: DeBruijn), forall (u: list DeBruijn), forall (n: nat),
    substitution_multiple_aux (Application t1 t2) n u =
    Application (substitution_multiple_aux t1 n u)
                (substitution_multiple_aux t2 n u)
.
Proof.
    move => t1 t2 u.
    induction u.
    simpl. move => n. reflexivity.
    move => n.
    simpl.
    rewrite (IHu (n + 1)).
    remember (substitution
    (Application (substitution_multiple_aux t1 (n + 1) u)
       (substitution_multiple_aux t2 (n + 1) u)) n a) as temp.
    unfold substitution in Heqtemp.
    fold substitution in Heqtemp. rewrite Heqtemp. reflexivity.
Qed.

(* La preuve n'est pas menée jusqu'au bout. On a abandonné après pas mal de (~1000 lignes en tout)
tentatives infructueuses. Je suppose que notre définition bizarre des termes nous a encore
joué un tour.

NB : on a modifié, en concertation avec plusieurs autress groupes, la signature du théorème.
En effet, il s'avère que, dans certains cas, il n'y a pas une relation de beta-réduction
entre les deux termes mais une relation d'égalité! Nous l'avons bien pris en compte
lors de l'écriture de la signature du théorème.

Pour avoir un échantillon des tentatives infructueuses, Cf tout en bas du fichier *)
Theorem transition_beta : forall (s1: State),
    CoS(s1) -> forall (s2: State), (step_krivine s1 = Some s2 -> 
        (((tau s1) -b> (tau s2)) \/ ((tau s1) = (tau s2))))
.
Proof.
    move => s1 CoS1 s2 eqs2.
    destruct s1. destruct p.
    induction i.
    induction e.
    case_eq n.
    move => H.
    simpl in eqs2. rewrite H in eqs2.
    discriminate.
    intuition.
    simpl in eqs2. rewrite H in eqs2.
    discriminate.

    simpl.
    case_eq n.
    move => H.
    simpl in eqs2. rewrite H in eqs2.
    destruct p.
    assert ((i, s0, s) = s2).
    apply some_truc. exact eqs2.
    rewrite <- H0. simpl.
    right. 
    case_eq s.
    intuition. unfold tau_aux.
    simpl.
    unfold tau_environment. unfold substitution_multiple. simpl. 
    assert (substitution_multiple_aux (Var 0) 1 (tau_environment_aux e) = Var 0).
    apply (substitution_multiple_C_0 (Var 0) 1). unfold max_var_smaller_n. simpl. lia.
    simpl. intuition. lia.
    rewrite -> H2. simpl. unfold substitution_multiple. rewrite deprotect_involutive.
    reflexivity.
    
    intuition. simpl.
    assert ((tau_environment (Stack (i, s0) e) (Var 0)) =
        (tau_environment s0 (tau_code i))).
    unfold tau_environment. simpl.
    assert (substitution_multiple (Var 0) 1 (tau_environment_aux e) = Var 0).
    apply (substitution_multiple_C_0 (Var 0) 1). unfold max_var_smaller_n. simpl. lia.
    simpl. intuition. lia.
    rewrite H2. simpl. rewrite deprotect_involutive. reflexivity.
    rewrite H2. reflexivity.



    intuition.
    
    right.
    rewrite H in eqs2.
    destruct p. simpl in eqs2.
    assert ((Access n0, e, s) = s2).
    apply (some_truc). exact eqs2.
    rewrite <- H0. simpl. rewrite H in IHe.
    simpl in IHe. rewrite H in CoS1. simpl in CoS1. intuition.
    case_eq s.
    intuition.
    unfold tau_aux.
    simpl. unfold tau_environment.
    induction e.
    intuition.
    unfold correct_stack in H6. rewrite H7 in H5. rewrite H7 in H0.
    simpl in H1. contradict H1.
    assert ((~ (1 > S n0)) -> ~ C[ 1 ]( Var (S n0))).
    apply (Decidable.contrapositive (~ (1 > S n0))).
    unfold Decidable.decidable. lia.
    intuition. assert (~ (1 > S n0)). lia. intuition.

    destruct p.
    case_eq e.
    intuition.
    remember ((Var (S n0)) [0 <-- tau_environment_aux (Stack (i, s0) (Stack (i0, s1) Nil))]).
    admit.
    intuition.
    admit.
    intuition. unfold tau_aux.
    admit.

    left.
    assert (eqs2' := eqs2).
    simpl in eqs2.
    case_eq s.
    intuition.
    rewrite H in eqs2. discriminate.
    intuition. rewrite H in eqs2.
    assert ((i, Stack (a, b) e, s0) = s2).
    apply some_truc. exact eqs2.
    rewrite <- H0. rewrite <- H0 in IHi.
    unfold tau.
    unfold tau_aux.
    induction s0.
    simpl. unfold tau_environment.
    intuition. 
    (*remember (tau_environment_aux (Stack (a, b) e)) as H'.*)
    
    rewrite (substitution_multiple_lambda (tau_code i) (tau_environment_aux e) 0).
    simpl.
    remember (tau_code a) [0 <-- tau_environment_aux b] as truc.
    assert ((substitution_multiple (tau_code i) 1 (tau_environment_aux e))
        = (tau_code i)[1 <-- (tau_environment_aux e)]).
    admit.
    remember (tau_environment_aux e).
    rewrite H1. rewrite deprotect_involutive.
    apply Evaluation.
    
    intuition.
    destruct p. intuition.

    (* Marche à peu près jusque-là*)
    admit.

    (* Push *)

    simpl.
    assert (eqs2' := eqs2).
    simpl in eqs2.
    assert ((i2, e, Stack (i1, e) s) = s2).
    apply some_truc. exact eqs2.
    rewrite <- H. unfold tau.
    simpl.
    case_eq s.
    intuition.
    right.
    unfold tau_aux.
    remember (tau_code (Push i1 i2)) as temp.
    unfold tau_code in Heqtemp. fold tau_code in Heqtemp.
    rewrite Heqtemp. unfold tau_environment. 
    remember (((Application (tau_code i2) (tau_code i1)) [0 <-- tau_environment_aux e]))
        as temp2.
    unfold substitution_multiple in Heqtemp2.
    unfold substitution_multiple_aux in Heqtemp2.
    fold substitution_multiple_aux in Heqtemp2.
    rewrite Heqtemp2. unfold substitution_multiple.
    rewrite stupide.
    remember (deprotect
    (Application
       (substitution_multiple_aux (tau_code i2) 0 (tau_environment_aux e))
       (substitution_multiple_aux (tau_code i1) 0 (tau_environment_aux e))) )
       as temp3.
    unfold deprotect in Heqtemp3.
    fold deprotect in Heqtemp3.
    rewrite Heqtemp3. reflexivity.

    intuition.
    left.
    remember (tau_aux (Push i1 i2) e (Stack (a, b) s0)) as lol.
    unfold tau_aux in Heqlol.
    fold tau_aux in Heqlol.
    rewrite Heqlol.
    

    (* Fin? *)
    unfold substitution_multiple_aux.     

    
    simpl.
    admit.
Admitted.

(* 5.5 

On n'est pas arrivés jusque-là mais on a quelques idées.
Avec 5.3 et 5.4, on pourrait montrer sans trop de difficultés que la clôture transistive refléxive
associée à la transition d'états de Krivine correspond exactement à celle de la beta-reduction. 
Avec un peu plus de boulot, on pourrait peut-être montrer que si un terme est correct, 
alors la réduction est finie (ceci n'est qu'une hypothèse) et boucle ensuite sur le même terme.

*)
    
    (* Marche vaguement jusqu'ici *)
    
    (* Une partie des tentatives infructueuses pour la 5.4 *)
    (*
    simpl in CoS1. intuition.
    unfold max_var_smaller_n in H0.
    unfold max_var_smaller_n_depth in H0. destruct H0.
    fold max_var_smaller_n_depth in H0.
    fold max_var_smaller_n_depth in H1.
    simpl. intuition.
    assert ((tau (i1, e, s)) -b> (tau s2) \/ tau (i1, e, s) = tau s2).
    apply IHi1.
    simpl. intuition.
    assert ((tau (i2, e, s)) -b> (tau s2) \/ tau (i2, e, s) = tau s2).
    apply IHi2.
    simpl. intuition.

    



    rewrite substitution_multiple_C_2.
    simpl. intuition. admit.
    intuition. simpl.


    assert ((substitution (substitution_multiple (Var (S n0)) 2 (tau_environment_aux s1))
    1 (tau_code a) [0 <-- tau_environment_aux b])
        = (substitution_multiple (Var n0) 1 (tau_environment_aux s1))).
    
    
    apply aux_0.

    unfold tau_environment_aux.
    unfold substitution_multiple. simpl.
    rewrite (substitution_multiple_C_2). 
        simpl. intuition.
    simpl. admit.
    simpl.
    case_eq e.
    intuition.
    rewrite H8 in H6. simpl in H6. rewrite H8 in H2.
    

    (*
    Application (tau_environment (Stack (i, s0) e) (Var 0)) (tau_aux a b s1) =
    Application (tau_environment s0 (tau_code i)) (tau_aux a b s1)
    *)

    assert ((tau_environment (Stack (i, s0) e) (Var 0)) =
        (tau_environment s0 (tau_code i))).
    unfold tau_environment.
    simpl. assert ((substitution_multiple (Var 0) 1 (tau_environment_aux e)) = Var 0).
    apply (substitution_multiple_C_0 (Var 0) 1). unfold max_var_smaller_n. simpl. lia.
    simpl. intuition. lia.

    rewrite H3. simpl. rewrite deprotect_involutive. reflexivity.

    (*
    Application (tau_environment (Stack (i, s0) e) (Var 0)) (tau_aux a b s1) =
    Application (tau_environment s0 (tau_code i)) (tau_aux a b s1)
    *)

    

    intuition.
    destruct s1. destruct p.
    induction i.
    induction e.
    induction s. simpl in H.
    intuition.
    assert (~C[0](Var n)).
    assert (~(0 > n)). lia.
    assert (~(0 > n) -> ~C[0](Var n)).
    apply (Decidable.contrapositive (~C[0](Var n))). intuition. simpl.
    intuition. exact (H4 H2).
    contradiction.
    
    simpl. destruct p. simpl in H. simpl in H0.
    case_eq n. intuition. rewrite H1 in H0. discriminate.
    intuition. rewrite H4 in H0. discriminate.

    induction s.
    simpl. simpl in H. destruct p.
    simpl in H0. simpl in IHe.
    case_eq n.
    intuition.
    rewrite H1 in H0.
    rewrite H1 in H5. rewrite H1 in H2.
    apply aux_0 in H2.
    unfold tau_environment. assert ((i, s, Nil) = s2). apply some_truc. exact H0.
    rewrite <- H7. unfold tau. unfold tau_aux.





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
    simpl. rewrite H1 in H. simpl in H.some_truc

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
*)
        
    
