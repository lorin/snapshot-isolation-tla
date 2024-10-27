---- MODULE SerializabilityRefinement ----
EXTENDS Serializability, Sequences, TLC
(**
 * 1. Track the history
 * 2. When it's done, generate a proper sorted version of the history
 * 3. Do the mapping
 *)

VARIABLES h, henv, opBar, argBar, rvalBar, envBar, ffBar, serialized

vars == <<h, henv, opBar, argBar, rvalBar, envBar, ffBar, serialized>>
bars == <<opBar, argBar, rvalBar, envBar, ffBar, serialized>>


InitR == /\ Init
         /\ h = <<>>
         /\ henv = <<>>
         /\ opBar = op
         /\ argBar = arg
         /\ rvalBar = rval
         /\ envBar = benv[1]
         /\ ffBar = Flip
         /\ serialized = FALSE



TypeOkR == /\ h \in Seq([tr: Tr, op: {"r","w","p"}, arg: Arg])
           /\ henv \in Seq([Obj -> Val])
           /\ opBar \in Op
           /\ argBar \in Arg
           /\ rvalBar \in Rval
           /\ envBar \in [Obj -> Val]
           /\ ffBar \in {Flip, Flop}
           /\ serialized \in BOOLEAN

Commits(t) == fate[t] = Committed

CommitR(t) == Commit(t) /\ UNCHANGED vars
AbortR(t) == Abort(t) /\ UNCHANGED vars

ReadR(t, obj, val) == /\ Read(t, obj, val)
                      /\ h' = IF Commits(t) THEN Append(h, [tr|->t, op|->"r", arg|->arg', rval|->rval']) ELSE h
                      /\ henv' = IF Commits(t) THEN Append(henv, tenv'[t]) ELSE henv
                      /\ UNCHANGED bars

WriteR(t, obj, val) == /\ Write(t, obj, val)
                       /\ h' = IF Commits(t) THEN Append(h, [tr|->t, op|->"w", arg|->arg', rval|->rval']) ELSE h
                       /\ henv' = IF Commits(t) THEN Append(henv, tenv'[t]) ELSE henv
                       /\ UNCHANGED bars

SerializeHistory == 
    /\ Termination
    /\ ~serialized
    /\ LET N == Len(h)
           R == 1..N  
           perm == CHOOSE seq \in [R -> R] : 
           \A i, j \in R :
               LET si == seq[i]
                   sj == seq[j]
                   hi == h[si]
                   hj == h[sj] 
                   Ti == hi.tr
                   Tj == hj.tr IN 
                   (* must be 1:1 mapping *)
                   /\ si = sj => i = j 
                   (* preserve order within transaction *)
                   /\ (Ti=Tj /\ i<j) => si < sj  
                   /\ (Ti=Tj /\ i>j) => si > sj
                   (* respect transaction order *)
                   /\ Ord(Ti) < Ord(Tj) => i < j 
                   /\ Ord(Ti) > Ord(Tj) => i > j 
              IN /\ h' = [i \in R |-> h[perm[i]]]
                 /\ henv' = [i \in R |-> henv[perm[i]]]
     /\ serialized' = TRUE
     /\ UNCHANGED <<opBar, argBar, rvalBar, envBar, ffBar>>

(* Issue the commands to the refinement mapping *)

Issue == LET e == Head(h) IN
         /\ Termination
         /\ serialized
         /\ h # <<>>
         /\ opBar' = e.op
         /\ argBar' = e.arg
         /\ rvalBar' = e.rval
         /\ envBar' = Head(henv)
         /\ ffBar' = Toggle(ffBar)
         /\ h' = Tail(h)
         /\ henv' = Tail(henv)
         /\ UNCHANGED serialized

vr == <<h, henv, opBar, argBar, rvalBar, envBar, ffBar, serialized, tr, op, arg, rval, tstate, fate, to, tenv, benv, eval, ff>>

TerminationR == /\ Termination 
                /\ h = <<>>
                /\ UNCHANGED vr

NextR == \/ \E t \in Tr:
            \/ CommitR(t)
            \/ AbortR(t)
            \/ \E obj \in Obj, val \in Val:
                \/ ReadR(t, obj, val)
                \/ WriteR(t, obj, val)
        \/ SerializeHistory
        \/ Issue
        \/ TerminationR

LR == /\ L
      /\ WF_vr(SerializeHistory)
      /\ WF_vr(Issue)

SpecR == InitR /\ [][NextR]_vr /\ LR

Sequential == INSTANCE Sequential WITH 
    op <- opBar,
    arg <- argBar,
    rval <- rvalBar,
    env <- envBar,
    ff <- ffBar

SeqSpec == Sequential!Spec

THEOREM Spec => SeqSpec


====