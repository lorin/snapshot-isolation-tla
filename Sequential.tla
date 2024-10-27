---- MODULE Sequential ----
(**********************)
(* A sequential store *)
(**********************)

CONSTANTS Obj, Val, Ok, Flip, Flop

VARIABLES 
    (******************************)
    (* external visible variables *)
    (******************************)
    op, arg, rval,
    
    (**********************)
    (* internal variables *)
    (**********************)
    env, ff


TypeOk == /\ op \in {"r", "w"}
          /\ arg \in Obj \cup Obj \X Val
          /\ rval \in Val \cup {Ok} \cup SUBSET Obj
          /\ env \in [Obj -> Val]
          /\ ff \in {Flip, Flop}


Toggle(f) == CASE ff = Flip -> Flop
               [] ff = Flop -> Flip

Init == /\ op \in {"r", "w"}
        /\ arg \in Obj \cup Obj \X Val
        /\ rval \in Val \cup {Ok}
        /\ env \in [Obj -> Val]
        /\ ff \in {Flip, Flop}

Read(obj, val) == /\ val = env[obj]
                  /\ op' = "r"
                  /\ arg' = obj
                  /\ rval' = val
                  /\ ff' = Toggle(ff)
                  /\ UNCHANGED env

Write(obj, val) == /\ op' = "w"
                   /\ arg' = <<obj, val>>
                   /\ rval' = Ok
                   /\ env' = [env EXCEPT ![obj]=val]
                   /\ ff' = Toggle(ff)

Next == \E obj \in Obj, val \in Val: Read(obj, val) \/ Write(obj, val)

v == <<op, arg, rval, env, ff>>
Spec == Init /\ [][Next]_v

====