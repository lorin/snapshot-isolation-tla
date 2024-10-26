---- MODULE SnapshotIsolationRefinement ----
EXTENDS SnapshotIsolation, Naturals, Sequences, FiniteSets

CONSTANTS NULL

VARIABLES h, fateIsSet, canIssue, parity, reads, writes


TypeOkR == /\ TypeOk
           /\ h \in Seq([tr: Tr, op: {"r", "w", "c", "a"}, arg: Obj \cup Obj \X Val \cup {<<>>}, rval: Val \cup {Ok, Err}])
           /\ fateIsSet \in BOOLEAN
           /\ canIssue \in BOOLEAN
           /\ parity \in {0,1}
           /\ reads \in [Tr -> SUBSET Obj]
           /\ writes \in [Tr -> SUBSET Obj]


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
                       /\ reads' = IF obj \in writes[t] THEN reads ELSE [reads EXCEPT ![t]=@ \cup {obj}] (* unwritten reads *)
                       /\ UNCHANGED <<fateIsSet, canIssue, parity, writes>>

BeginWrR(t, obj, val) == /\ BeginWr(t, obj, val)
                         /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes>>

EndWrR(t, obj, val) == /\ EndWr(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"w", arg|-> <<obj, val>>, rval|->Ok])
                       /\ writes' = [writes EXCEPT ![t]=@ \cup {obj}]
                       /\ UNCHANGED <<fateIsSet, canIssue, parity, reads>>

AbortWrR(t, obj, val) == /\ AbortWr(t, obj,val)
                         /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Err])
                         /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes>>

CommitR(t) == /\ Commit(t)
              /\ h' = Append(h, [tr|->t, op|->"c", arg|-> <<>>, rval|->Ok])
              /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes>>

AbortR(t) == /\ Abort(t)
             /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Ok])
             /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes>>

SetFate == /\ Done
           /\ fateIsSet = FALSE
           /\ fateIsSet' = TRUE
           /\ UNCHANGED <<op, arg, rval, tstate, tid, snap, env, anc, h, canIssue, parity, reads, writes>>

(* Refinement transactions *)
TrR == Tr \ {T0}

(* Committed transactions *)
CT == {t \in TrR: tstate[t] = Committed}

N == Cardinality(CT) 

ord == IF ~fateIsSet THEN [to|->NULL, benv|->NULL]
       ELSE CHOOSE r \in [to:[1..N -> CT], benv:[1..N+1 -> [Obj -> Val]]]:
        /\ r.benv[1] = SnapInit                         (* first environment msut be the initialization *)
        /\ \A i,j \in 1..N : r.to[i] = r.to[j] => i = j (* to must be a total ordering *)
        /\ \A i \in 1..N : LET t == r.to[i] IN 
            /\ \A obj \in reads[t] : r.benv[i][obj] = snap[t][obj] (* all non-written reads have to be consistent with transaction's snapshot *)
            /\ \A obj \in writes[t] : r.benv[i+1][obj] = env[t][obj] (* all writes have to be conssitent with transaction's environment *)

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