Add LoadPath "." as CoqDirectory.
Load partie2.

(* Question 2 *)
Inductive Instruction :=
    | Access : nat -> Instruction
    | Grab : Instruction
    | Push : (list Instruction) -> Instruction
.
Inductive Stack_type : Type := 
    | Nil : Stack_type
    | Stack : ((list Instruction) * Stack_type) -> Stack_type -> Stack_type
.

Definition Environment : Type := Stack_type.

Definition State : Type := ((list Instruction) * Environment * Stack_type).

Inductive StateOption :=
    | None : StateOption
    | Some : State -> StateOption
.

(* Question 3 *)
Definition step_kirvine (state: State) : StateOption :=
    match state with
    | ((Access 0) :: _, Stack (c0, e0) _, s) => Some ((c0, e0, s))
    | ((Access (S n)) :: c, Stack (_, _) e, s) => Some (((Access n) :: c, e, s))
    | ((Push cp) :: c, e, s) => Some ((c, e, Stack (cp, e) s))
    | (Grab :: c, e, Stack (c0, e0) s) => Some (c, Stack (c0, e0) e, s)
    | _ => None
    end
.

