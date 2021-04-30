Add LoadPath "." as CoqDirectory.
Load partie2.

(* Question 2 *)
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
Definition step_kirvine (state: State) : StateOption :=
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
