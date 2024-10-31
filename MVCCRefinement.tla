---- MODULE MVCCRefinement ----
EXTENDS MVCC, Naturals, Sequences, FiniteSets, TLC

CONSTANTS NULL, Flip, Flop

VARIABLES h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar

(* Refinement transactions *)
TrR == Tr \ {T0}

(* Committed transactions *)
CT == {t \in TrR: tstate[t] = Committed}

N == Cardinality(CT)

TypeOkR == /\ TypeOk
           /\ \A i \in DOMAIN h : LET e == h[i] IN
                /\ e.tr \in TrR
                /\ e.op \in {"r", "w", "c", "a"}
                /\ e.arg \in CASE e.op = "r" -> Obj
                               [] e.op = "w" -> Obj \X Val
                               [] OTHER      -> { <<>> }

                /\ e.rval \in Val \cup {Ok, Err}
                /\ e.tstate \in [Tr -> {Unstarted, Open, Committed, Aborted}]
                /\ e.op \in {"r", "w"} => /\ DOMAIN e.wr \subseteq Obj
                                          /\ \A obj \in DOMAIN e.wr : e.wr[obj] \in Val

           /\ fateIsSet \in BOOLEAN
           /\ canIssue \in BOOLEAN
           /\ parity \in {0,1}
           /\ reads \in [Tr -> SUBSET Obj]
           /\ writes \in [Tr -> SUBSET Obj]
           /\ tenvBar \in [CT -> [Obj -> Val]] \cup {NULL}
           /\ ord \in [to: [1..N -> CT] \cup {NULL}, benv: [1..N+1 -> [Obj -> Val]] \cup {NULL}]

InitR == /\ Init
         /\ fateIsSet = FALSE
         /\ parity = 0
         /\ h = <<>>
         /\ canIssue = FALSE
         /\ reads = [t \in Tr |-> {}]
         /\ writes = [t \in Tr |-> IF t=T0 THEN Obj ELSE {}]
         /\ ord = [to|->NULL, benv|->NULL]
         /\ tenvBar = NULL

StartTransactionR(t) == /\ StartTransaction(t)
                        /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

BeginRdR(t, obj) == /\ BeginRd(t, obj)
                    /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

EndRdR(t, obj, val) == /\ EndRd(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"r", arg|->obj, rval|->val, tstate|->tstate, wr|->[o \in writes[t] |-> GetVal(t,o, vis[t])]])
                       /\ reads' = IF obj \in writes[t] THEN reads ELSE [reads EXCEPT ![t]=@ \cup {obj}] (* unwritten reads *)
                       /\ parity' = 1 - parity
                       /\ UNCHANGED <<fateIsSet, canIssue, writes, ord, tenvBar>>

BeginWrR(t, obj, val) == /\ BeginWr(t, obj, val)
                         /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

EndWrR(t, obj, val) == /\ EndWr(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"w", arg|-> <<obj, val>>, rval|->Ok, tstate|->tstate, wr|->[o \in writes[t] |-> GetVal(t, o, vis[t])]])
                       /\ writes' = [writes EXCEPT ![t]=@ \cup {obj}]
                       /\ parity' = 1 - parity
                       /\ UNCHANGED <<fateIsSet, canIssue, reads, ord, tenvBar>>

AbortWrR(t, obj, val) == /\ AbortWr(t, obj,val)
                         /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Err, tstate|->[tstate EXCEPT ![t]=Aborted]])
                         /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

CommitR(t) == /\ Commit(t)
              /\ h' = Append(h, [tr|->t, op|->"c", arg|-> <<>>, rval|->Ok, tstate|->[tstate EXCEPT ![t]=Committed]])
              /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

AbortR(t) == /\ Abort(t)
             /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Ok, tstate|->[tstate EXCEPT ![t]=Aborted]])
             /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

DetectDeadlockR == /\ DetectDeadlock
                   /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

(* Get the order in which this transactionruns *)
Ord(t) == CHOOSE i \in DOMAIN ord.to : ord.to[i] = t

SetFate == /\ Done
           /\ fateIsSet = FALSE
           /\ fateIsSet' = TRUE
           /\ ord' = CHOOSE r \in [to: [1..N -> CT], benv: [1..N+1 -> [Obj -> Val]]]:
                /\ r.benv[1] = SnapInit                         (* first environment msut be the initialization *)
                /\ \A i,j \in 1..N : r.to[i] = r.to[j] => i = j (* to must be a total ordering *)
                /\ \A i \in 1..N : LET t == r.to[i] IN
                    /\ \A obj \in reads[t] : r.benv[i][obj] = GetVal(t, obj, vis[t] \ {t}) (* all non-written reads have to be consistent with transaction's snapshot *)
                    /\ \A obj \in writes[t] : r.benv[i+1][obj] = GetVal(t, obj, vis[t]) (* all writes have to be consistent with transaction's environment *)
                    /\ \A obj \in Obj : (r.benv[i+1][obj] # r.benv[i][obj]) => obj \in writes[t] (* if a variable changed, there must be a corresponding write*)
           /\ tenvBar' = LET ordp == ord'
                             benv == ordp.benv
                             to == ordp.to IN
                [t \in CT |-> LET i == CHOOSE i \in DOMAIN to: to[i] = t IN benv[i]]
           /\ UNCHANGED <<op, arg, rval, db, vis, tstate, tid, deadlocked, h, canIssue, parity, reads, writes>>

Issue == /\ h # <<>>
         /\ fateIsSet
         /\ canIssue' = TRUE
         /\ h' = IF canIssue THEN Tail(h) ELSE h
         /\ h' # <<>>
         (* tenvBar' needs to reflect the state of the *next* head in the history, not the current head *)
         /\ tenvBar' = LET e == Head(h')
                           obj == e.arg[1]
                           val == e.arg[2]
                           t == e.tr
                       IN IF tstate[e.tr] = Committed /\ e.op = "w"
                          THEN [tenvBar EXCEPT ![t][obj]=val]
                          ELSE tenvBar
         /\ UNCHANGED <<op, arg, rval, db, vis, tstate, tid, deadlocked, fateIsSet, parity, reads, writes, ord>>

vv == <<op, arg, rval, db, vis, tstate, tid, deadlocked, h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

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
         \/ DetectDeadlockR
         \/ Issue
         \/ SetFate
         \/ TerminationR

SpecR == InitR /\ [][NextR]_vv

trBar == IF canIssue THEN Head(h).tr ELSE T0
opBar == IF canIssue THEN Head(h).op ELSE "r"
argBar == CASE canIssue /\ Head(h).arg = <<>> -> None
            [] canIssue /\ Head(h).arg # <<>> -> Head(h).arg
            [] OTHER -> CHOOSE obj \in Obj : TRUE
rvalBar == CASE canIssue /\ Head(h).rval # Err -> Head(h).rval
             [] canIssue /\ Head(h).rval = Err -> Ok
             [] OTHER                          -> V0
tstateBar == [t \in TrR |->
                LET s == Head(h).tstate[t] IN
                CASE ~canIssue                 -> Open
                  [] canIssue /\ s = Unstarted -> Open
                  [] canIssue /\ s = Open      -> Open
                  [] canIssue /\ s = Committed -> Committed
                  [] canIssue /\ s = Aborted   -> Aborted]

ffBar == LET Parity(hh) == Len(SelectSeq(hh, LAMBDA e: e.op \in {"r", "w"})) % 2
             p == Parity(h)
             opp == Head(h).op IN
    CASE ~canIssue              -> Flip
      [] canIssue /\ opp    \in {"r", "w"} /\ parity = p -> Flop
      [] canIssue /\ opp \notin {"r", "w"} /\ parity = p -> Flip
      [] canIssue /\ opp    \in {"r", "w"} /\ parity # p -> Flip
      [] canIssue /\ opp \notin {"r", "w"} /\ parity # p -> Flop

fateBar == IF ~fateIsSet THEN NULL
           ELSE [t \in TrR |-> tstate[t]]

Ser == INSTANCE SerializabilityD WITH
    Tr <- TrR,
    tr <- trBar,
    op <- opBar,
    arg <- argBar,
    rval <- rvalBar,
    tstate <- tstateBar,
    fate <- fateBar,
    to <- ord.to,
    tenv <- tenvBar,
    benv <- ord.benv,
    ff <- ffBar,
    Vinit <- V0

SerSpec == Ser!SpecD

====