---- MODULE SnapshotIsolationRefinement ----
EXTENDS SnapshotIsolation, Naturals, Sequences, FiniteSets

CONSTANTS Pred, NULL, Flip, Flop, Undefined

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
                /\ e.env \in [Tr -> [Obj -> Val]]
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
                       /\ h' = Append(h, [tr|->t, op|->"r", arg|->obj, rval|->val, env|->env, wr|->[o \in writes[t] |-> env[t][o]]])
                       /\ reads' = IF obj \in writes[t] THEN reads ELSE [reads EXCEPT ![t]=@ \cup {obj}] (* unwritten reads *)
                       /\ UNCHANGED <<fateIsSet, canIssue, parity, writes, ord, tenvBar>>

BeginWrR(t, obj, val) == /\ BeginWr(t, obj, val)
                         /\ UNCHANGED <<h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

EndWrR(t, obj, val) == /\ EndWr(t, obj, val)
                       /\ h' = Append(h, [tr|->t, op|->"w", arg|-> <<obj, val>>, rval|->Ok, env|->env, wr|->[o \in writes[t] |-> env[t][o]]])
                       /\ writes' = [writes EXCEPT ![t]=@ \cup {obj}]
                       /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, ord, tenvBar>>

AbortWrR(t, obj, val) == /\ AbortWr(t, obj,val)
                         /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Err])
                         /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

CommitR(t) == /\ Commit(t)
              /\ h' = Append(h, [tr|->t, op|->"c", arg|-> <<>>, rval|->Ok, env|->env])
              /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

AbortR(t) == /\ Abort(t)
             /\ h' = Append(h, [tr|->t, op|->"a", arg|-> <<>>, rval|->Ok, env|->env])
             /\ UNCHANGED <<fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

(* Get the order in which this transactionruns *)
Ord(t) == CHOOSE i \in DOMAIN ord.to : ord.to[i] = t

SetFate == /\ Done
           /\ fateIsSet = FALSE
           /\ fateIsSet' = TRUE
           /\ ord' = CHOOSE r \in [to: [1..N -> CT], benv: [1..N+1 -> [Obj -> Val]]]:
                /\ r.benv[1] = SnapInit                         (* first environment msut be the initialization *)
                /\ \A i,j \in 1..N : r.to[i] = r.to[j] => i = j (* to must be a total ordering *)
                /\ \A i \in 1..N : LET t == r.to[i] IN 
                    /\ \A obj \in reads[t] : r.benv[i][obj] = snap[t][obj] (* all non-written reads have to be consistent with transaction's snapshot *)
                    /\ \A obj \in writes[t] : r.benv[i+1][obj] = env[t][obj] (* all writes have to be conssitent with transaction's environment *)
           /\ tenvBar' = LET ordp == ord'
                             benv == ordp.benv
                             to == ordp.to IN
                [t \in CT |-> LET i == CHOOSE i \in DOMAIN to: to[i] = t IN benv[i]]
           /\ UNCHANGED <<op, arg, rval, tstate, tid, snap, env, anc, h, canIssue, parity, reads, writes>>

Issue == LET e == Head(h)
             Toggle(f) == IF f = Flip THEN Flop ELSE Flip
             t == e.tr
             obj == e.arg[1]
             val == e.arg[2] IN
         /\ fateIsSet
         /\ h # <<>>
         /\ canIssue' = TRUE
         /\ h' = IF canIssue THEN Tail(h) ELSE h
         /\ h' # <<>>        
         /\ tenvBar' = IF tstate[e.tr] = Committed /\ e.op = "w" THEN [tenvBar EXCEPT ![t][obj]=val]
                       ELSE tenvBar
         /\ UNCHANGED <<op, arg, rval, tstate, tid, snap, env, anc, fateIsSet, parity, reads, writes, ord>>

vv == <<op, arg, rval, tstate, tid, snap, env, anc, h, fateIsSet, canIssue, parity, reads, writes, ord, tenvBar>>

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

trBar == IF canIssue THEN Head(h).tr ELSE T0
opBar == IF canIssue THEN Head(h).op ELSE "r"
argBar == IF canIssue THEN Head(h).arg ELSE CHOOSE obj \in Obj : TRUE
rvalBar == IF canIssue THEN Head(h).rval ELSE V0
tstateBar == [t \in TrR |->
                LET s == Head(h).tstate[t] IN
                CASE ~canIssue                 -> Open
                  [] canIssue /\ s = Unstarted -> Open
                  [] canIssue /\ s = Open      -> Open
                  [] canIssue /\ s = Committed -> Committed]

ffBar == LET Parity(hh) == Len(SelectSeq(hh, LAMBDA e: e.op \in {"r", "w"})) % 2
             p == Parity(h)
             opp == Head(h).op IN
    CASE ~canIssue              -> Flip
      [] canIssue /\ opp \in {"r", "w"} /\ parity = p    -> Flop
      [] canIssue /\ opp \notin {"r", "w"} /\ parity = p -> Flip
      [] canIssue /\ opp \in {"r", "w"} /\ parity # p    -> Flip
      [] canIssue /\ opp \notin {"r", "w"} /\ parity # p -> Flop

fateBar == IF ~fateIsSet THEN NULL
           ELSE [t \in TrR |-> tstate[t]]

(* We don't implement predicate reads, so we choose just an arbitrary evaluation *)
evalBar == CHOOSE x \in [Pred -> [[Obj -> Val] -> SUBSET Obj]] : TRUE

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
    eval <- evalBar,
    ff <- ffBar,
    Vinit <- V0

SerSpec == Ser!SpecD

====