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
                                        /\ GetVal(t1, obj) # GetVal(t2, obj)

NoConcurrentWrites == ~ ConcurrentWrite

====