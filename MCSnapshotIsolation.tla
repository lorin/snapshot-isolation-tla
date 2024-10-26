---- MODULE MCSnapshotIsolation ----
EXTENDS SnapshotIsolation

Terminates == <> Done

(***************************************************************************)
(* Two transactions are concurrent if neither is the ancestor of the other *)
(***************************************************************************)
Concurrent(t1, t2) == /\ t1 \notin anc[t2]
                      /\ t2 \notin anc[t1]

(*************************************************)
(* True if transaction *t* modified object *obj* *)
(*************************************************)
Wrote(t, obj) == env[t][obj] # snap[t][obj]

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

NoConcurrentWrites == ~ ConcurrentWrite

====