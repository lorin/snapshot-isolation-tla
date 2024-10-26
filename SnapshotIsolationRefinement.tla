---- MODULE SnapshotIsolationRefinement ----
EXTENDS SnapshotIsolation, Naturals, Sequences

VARIABLES h, fateIsSet, canIssue, parity, reads, writes


TypeOkR == /\ TypeOk
           /\ h \in Seq([tr: Tr, op: {"r", "w", "c", "a"}, arg: Obj \cup Obj \X Val \cup {<<>>}, rval: Val \cup {Ok, Err}])
           /\ fateIsSet \in BOOLEAN
           /\ canIssue \in BOOLEAN
           /\ parity \in {0,1}
           /\ reads \in [Tr -> Obj]
           /\ writes \in [Tr -> Obj]


InitR == /\ Init
         /\ fateIsSet = FALSE
         /\ parity = 0
         /\ h = <<>>
         /\ canIssue = FALSE
         /\ reads = [t \in Tr |-> {}]
         /\ writes = [t \in Tr |-> IF t=T0 THEN Obj ELSE {}]

StartTransactionR(t) == /\ StartTransaction(t)
                        /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

BeginRdR(t, obj) == /\ BeginRd(t, obj)
                    /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

EndRdR(t, obj, val) == /\ EndRd(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"r", arg|->obj, rval|->val])
                       /\ reads' = IF obj \in writes THEN reads ELSE [reads EXCEPT ![t]=@ \cup {obj}] (* unwritten reads *)
                       /\ UNCHANGED <<fateIsSet, canIssue, parity, writes>>

BeginWrR(t, obj, val) == /\ BeginWr(t, obj, val)
                         /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

EndWrR(t, obj, val) == /\ EndWr(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"w", arg|-> <<obj, val>>, rval|->Ok])
                       /\ writes' = [writes EXCEPT ![t]=@ \cup {obj}]
                       /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads>>

AbortWrR(t, obj, val) == /\ AbortWr(t, obj,val)
                         /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Err])
                         /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

CommitR(t) == /\ Commit(t)
              /\ h' = Append(h, [tr|->t, op|->"c", arg|-> <<>>, rval|->Ok])
              /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

AbortR(t) == /\ Abort(t)
             /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Ok])
             /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

SetFate == /\ Done
           /\ fateIsSet = FALSE
           /\ fateIsSet' = TRUE

Issue == FALSE 

vv == <<op, arg, rval, tstate, tid, snap, env, anc, h, fateIsSet, canIssue, parity, reads, writes>>

TerminationR == /\ Done
                /\ Tail(h) = <<>>
                /\ UNCHANGED vv

NextR == \/ \E t \in Tr, obj \in Obj, val \in Val:
            \/ StartTransactionR(t)
            \/ BeginRdR(t, obj)
            \/ EndRdR(t, obj, val)
            \/ BeginWrR(t, obj, val)
            \/ EndWrR(t, obj, val)
            \/ AbortWrR(t, obj, val)
            \/ CommitR(t)
            \/ AbortR(t)
         \/ SetFate
         \/ Issue       
         \/ TerminationR

SpecR == InitR /\ [][NextR]_vv

====