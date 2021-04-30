Add LoadPath "." as CoqDirectory.
Load partie3.

Fixpoint Comp (t: DeBruijn) : Instruction :=
    match t with
    | Lambda t => Grab (Comp t)
    | Application tp1 tp2 => (Push (Comp tp1) (Comp tp2))
    | Var n => (Access n)
    | Protect tp => Comp tp
    end
.

Definition CompState (t: DeBruijn) : State :=
    (Comp t, Nil, Nil)
.
