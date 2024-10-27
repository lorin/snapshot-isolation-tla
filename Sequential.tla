---- MODULE Sequential ----
(* A sequential store *)

CONSTANTS Obj, Val, Pred,
          Ok,
          Flip, Flop

VARIABLES 
    (* public variables *)
    op, arg, rval,
    
    (* internal variables *)
    env,
    eval, \* predicate evaluation
    ff


TypeOk == /\ op \in {"r", "w", "p"}
          /\ arg \in Obj \cup Obj \X Val \cup Pred
          /\ rval \in Val \cup {Ok} \cup SUBSET Obj
          /\ env \in [Obj -> Val]
          /\ eval \in [Pred -> [[Obj -> Val] -> SUBSET Obj]]
          /\ ff \in {Flip, Flop}


Toggle(f) == CASE ff = Flip -> Flop
               [] ff = Flop -> Flip

Init == /\ op \in {"r", "w"}
        /\ arg \in Obj \cup Obj \X Val
        /\ rval \in Val \cup {Ok}
        /\ env \in [Obj -> Val]
        /\ eval \in [Pred -> [[Obj -> Val] -> SUBSET Obj]]
        /\ ff \in {Flip, Flop}

Read(obj, val) == /\ val = env[obj]
                  /\ op' = "r"
                  /\ arg' = obj
                  /\ rval' = val
                  /\ ff' = Toggle(ff)
                  /\ UNCHANGED <<env, eval>>

Write(obj, val) == /\ op' = "w"
                   /\ arg' = <<obj, val>>
                   /\ rval' = Ok
                   /\ env' = [env EXCEPT ![obj]=val]
                   /\ ff' = Toggle(ff)
                   /\ UNCHANGED eval

PredRead(P, objs) == /\ op' = "p"
                     /\ arg' = P
                     /\ rval' = eval[P][env]
                     /\ ff' = Toggle(ff)
                     /\ UNCHANGED <<env, eval>>

Next == \/ \E obj \in Obj, val \in Val: Read(obj, val) \/ Write(obj, val)
        \/ \E P \in Pred, objs \in SUBSET Obj : PredRead(P, objs) 

v == <<op, arg, rval, env, eval, ff>>
Spec == Init /\ [][Next]_v

====