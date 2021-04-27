Inductive Instruction :=
    | Access : nat -> Instruction
    | Grab : Instruction
    | Push : Code -> Instruction
with Code :=
    | Code_List : list Instruction -> Code.

