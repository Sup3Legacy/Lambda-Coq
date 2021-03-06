Add LoadPath "." as CoqDirectory.
Load partie2.

(* Cette partie met quelques notions en place, rien de très extravagant *)

(* Question 2 *)
(* NB : on a remplacé les blocs d(instruction par des listes chaînées directement
embedded dans les termes car Coq refusait de définir certains opérateurs de point fixe
car il n'arrivait pas à prouver leur terminaison *)
Inductive Instruction :=
    | Access : nat -> Instruction
    | Grab : Instruction -> Instruction
    | Push : Instruction -> Instruction -> Instruction
.
Inductive Stack_type : Type := 
    | Nil : Stack_type
    | Stack : (Instruction * Stack_type) -> Stack_type -> Stack_type
.

Definition Environment : Type := Stack_type.

Definition State : Type := (Instruction * Environment * Stack_type).

Inductive StateOption :=
    | None : StateOption
    | Some : State -> StateOption
.

(* Question 3 *)
Definition step_krivine (state: State) : StateOption :=
    match state with
    | ((Access 0), Stack (c0, e0) _, s) => Some ((c0, e0, s))
    | ((Access (S n)), Stack (_, _) e, s) => Some (((Access n), e, s))
    | ((Push cp c), e, s) => Some ((c, e, Stack (cp, e) s))
    | (Grab c, e, Stack (c0, e0) s) => Some (c, Stack (c0, e0) e, s)
    | _ => None
    end
.

Definition is_state (s: StateOption) :=
    match s with
    | None => False
    | Some _ => True
    end
.

(* Encore le même genre de lemme... *)
Lemma some_truc : forall (s1 s2: State), 
    Some s1 = Some s2 <-> s1 = s2
.
Proof.
    move => s1 s2.
    split.
    case. trivial.
    move => H.
    rewrite H. reflexivity.
Qed.