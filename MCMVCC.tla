---- MODULE MCMVCC ----
EXTENDS MVCC

Terminates == <> Done

Alias == [
    Deps |-> Deps,
    TCD |-> TC(Deps),
    stuck |-> {t \in Tr: <<t, t>> \in TC(Deps)}
]

(*************************************************)
(* True if transaction *t* modified object *obj* *)
(*************************************************)
Wrote(t, obj) == \E ver \in db[obj] : ver.tr = t

(*****************************************************************)
(* True if two transactions concurrently modified the same value *)
(*****************************************************************)
ConcurrentWrite == \E t1,t2 \in Tr:
                    /\ t1 # t2
                    /\ tstate[t1] = Committed
                    /\ tstate[t2] = Committed
                    /\ Concurrent(t1, t2)
                    /\ \E obj \in Obj : /\ Wrote(t1, obj) 
                                        /\ Wrote(t2, obj) 
                                        /\ Get(t1, obj) # Get(t2, obj)

NoConcurrentWrites == ~ ConcurrentWrite

(******************************************************************)
(* Any transaction that just started must have an id greater than *)
(* any other transaction so far                                   *)
(******************************************************************)
IdsIncreaseMonotically == 
    LET trs == {t \in Tr : t \in {Open, Committed, Aborted}} (* transactions with tids *)
        tids == {tid[t] : t \in trs }
    IN \A t \in Tr : op[t]="s" => \A tt \in trs \ {t} : \/ tid[t] > tid[tt]
                                                          \/ op[tt] = "s"


====