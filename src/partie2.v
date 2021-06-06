Add LoadPath "." as CoqDirectory.
Load partie1.

(* Globalement, cette partie a été très facile et rapide. C'est surtout quelques définitions
utiles pour la partie 5 *)

(* Définition inductive, assez basique *)
Inductive beta_reduction_one_step : DeBruijn -> DeBruijn -> Prop :=
    | Evaluation : forall (u v: DeBruijn),
        (beta_reduction_one_step (Application (Lambda u) v) (u[0 <- v]))
    | Context_r : forall (u v w: DeBruijn),
        (beta_reduction_one_step v w) -> 
            (beta_reduction_one_step (Application u v) (Application u w))
    | Context_l : forall (u v w: DeBruijn),
        (beta_reduction_one_step u v) -> 
            (beta_reduction_one_step (Application u w) (Application v w))
    | Context_lambda : forall (u v: DeBruijn),
        (beta_reduction_one_step u v) -> (beta_reduction_one_step (Lambda u) (Lambda v)) 
.

(* si t−→u et u−→∗v, alors t−→∗v *)

Inductive beta_reduction : DeBruijn -> DeBruijn -> Prop :=
    | beta_refl : forall (u: DeBruijn), beta_reduction u u
    | beta_trans : forall (t u v: DeBruijn),
        (beta_reduction_one_step t u) -> (beta_reduction u v) -> (beta_reduction t v)
.

(* Jolies notations, un peu de syntaxic sugar dans ce monde cruel*)
Notation "t -b> u" := (beta_reduction_one_step t u) (at level 0).
Notation "t -b>* u" := (beta_reduction t u) (at level 0).

(* Facile, rien à dire *)
Theorem context_l_star : forall (t u v: DeBruijn),
    t -b>* u -> (Application t v) -b>* (Application u v).
Proof.
    move => t u v.
    move => H.
    induction H.
    apply beta_refl.
    assert ((Application t v) -b> (Application u v)).
    apply Context_l. exact H.
    apply (beta_trans (Application t v) (Application u v) (Application v0 v) H1 IHbeta_reduction).
Qed.

(* Facile, rien à dire *)
Theorem context_r_star : forall (t u v: DeBruijn),
    u -b>* v -> (Application t u) -b>* (Application t v).
Proof.
    move => t u v.
    move => H.
    induction H.
    apply beta_refl.
    assert ((Application t t0) -b> (Application t u)).
    apply Context_r. exact H.
    apply (beta_trans (Application t t0) (Application t u) (Application t v) H1 IHbeta_reduction).
Qed.

(* Facile, rien à dire *)
Theorem context_lambda_star : forall (t u: DeBruijn),
    t -b>* u -> (Lambda t) -b>* (Lambda u).
Proof.
    move => t u.
    move => H.
    induction H.
    apply beta_refl.
    assert ((Lambda t) -b> (Lambda u)). apply Context_lambda. exact H.
    apply (beta_trans (Lambda t) (Lambda u) (Lambda v) H1 IHbeta_reduction).
Qed.

    
    