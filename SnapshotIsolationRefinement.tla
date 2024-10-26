---- MODULE SnapshotIsolationRefinement ----
EXTENDS SnapshotIsolation, Naturals

VARIABLES h, fateIsSet, canIssue, parity



SetFate == /\ Done
           /\ fateIsSet = FALSE
           /\ fateIsSet' = TRUE

InitR == /\ Init
         /\ fateIsSet = FALSE
         /\ parity = 0
         /\ h = <<>>
         /\ canIssue = FALSE

StartTransactionR(t) == /\ StartTransaction(t)
                        /\ UNCHANGED <<h, fateIsSet, canIssue, parity>>

BeginRdR(t, obj) == /\ BeginRd(t, obj)
                    /\ UNCHANGED <<h, fateIsSet, canIssue, parity>>

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
         \/ Termination

SpecR == InitR /\ [][NextR]_vv

====