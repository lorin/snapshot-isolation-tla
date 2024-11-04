---- MODULE SSI ----
(***********************************************************************)
(* Serializable Snapshot Isolation                                     *)
(*                                                                     *)
(* Based on the algorithm described in the paper:                      *)
(*                                                                     *)
(* Serializable Isolation for Snapshot Databases                       *)
(* Michael J. Cahill, Uwe Röhm, Alan D. Fekete, SIGMOD '08, June 2008. *)
(*                                                                     *)
(***********************************************************************)

EXTENDS MVCC

VARIABLES rds,  (* which transactions have performed reads on each object *)
          outc, (* transactions that have an outbound anti-dependency *)
          inc   (* transactions that have an inbound anti-dependency *)

TypeOkS == /\ rds \in [Obj -> SUBSET Tr]
           /\ outc \subseteq Tr
           /\ inc \subseteq Tr

InitS == /\ Init
         /\ rds = [obj \in Obj |-> {}]
         /\ inc = {}
         /\ outc = {}

BeginRdS(t, obj) ==
    LET isActiveWrite == (\E tw \in Tr \ {t}: ActiveWrite(tw, obj))
        tw == CHOOSE tw \in Tr \ {t} : ActiveWrite(tw, obj)
    IN /\ BeginRd(t, obj)
       /\ rds' = [rds EXCEPT ![obj]=@ \cup {t}]
       /\ inc' = IF isActiveWrite THEN inc \union {tw} ELSE inc
       /\ outc' = IF isActiveWrite THEN outc \union {t} ELSE outc
   
(************************************************************************)
(* True when transaction t creates a pivot transaction when reading obj *)
(************************************************************************)
ReadCreatesPivot(t, obj) ==
    LET vr == GetVer(obj, vis[t])
    IN /\ vr.tr # t (* reading our own write cannot create a pivot *)
       /\ \E vw \in db[obj] : /\ Concurrent(t, vw.tr)
                              /\ tstate[vw.tr] = Committed
                              /\ vw.tr \in outc

AbortRdS(t, obj) ==
       /\ op[t] = "r"
       /\ rval[t] = Busy
       /\ arg[t] = obj
       /\ ReadCreatesPivot(t, obj)
       /\ op' = [op EXCEPT ![t]="a"]
       /\ arg' = [arg EXCEPT ![t] = <<>>]
       /\ rval' = [rval EXCEPT ![t] = Err]
       /\ tr' = t
       /\ tstate' = [tstate EXCEPT ![t] = Aborted]
       /\ UNCHANGED <<db, vis, tid, deadlocked, rds, inc, outc>>

(*****************************************************)
(* object version v1 is newer than object version v2 *)
(*****************************************************)
Newer(v1, v2) == tid[v1.tr] > tid[v2.tr]

EndRdS(t, obj, val) ==
    LET ver == GetVer(obj, vis[t])
        Ab(w) == w.tr = Aborted
        newer == IF ver.tr # t THEN { w \in db[obj] : Newer(w, ver) /\ ~Ab(w) } ELSE {}
    IN 
       /\ EndRd(t, obj, val)
       /\ ~ReadCreatesPivot(t, obj)
       (* each later transaction that wrote has an inbound conflict *)
       /\ inc' = inc \cup {w.tr : w \in newer}
       (* if there are any newer versions, t has an outbound conflict *)
       /\ outc' = IF newer = {} THEN outc ELSE outc \cup {t}
       /\ UNCHANGED rds


(*
if there is a SIREAD lock(rl) on x
    with rl.owner is running
    or commit(rl.owner) > begin(T):
        if rl.owner is committed and rl.owner.inConflict:
            ABORT
*)
WriteCreatesPivot(t, obj) ==
       \E tt \in rds[obj] \ {t} :
        /\ \/ tstate[tt] = Open
           \/ tstate[tt] = Committed /\ Concurrent(t, tt)
        /\ tt \in inc

AbortWrS(t, obj) ==
    /\ \/ AbortWr(t, obj)
       \/ /\ op[t] = "w"
          /\ rval[t] = Busy
          /\ WriteCreatesPivot(t, obj)
          /\ op' = [op EXCEPT ![t] = "a"]
          /\ arg' = [arg EXCEPT ![t] = <<>>]
          /\ rval' = [rval EXCEPT ![t]=Err]
          /\ tr' = t
          /\ tstate' = [tstate EXCEPT ![t]=Aborted]
          /\ UNCHANGED <<db, deadlocked, tid, vis>>
    /\ UNCHANGED <<rds, inc, outc>>

EndWrS(t, obj, val) ==
        (* active transactions *)
    LET active == {u \in Tr \ {t}: tstate[u] = Open}
        (* active transactions that are reading obj *)
        ards == rds[obj] \cap active
    IN /\ EndWr(t, obj, val)
       /\ ~WriteCreatesPivot(t, obj)
       /\ outc' = outc \cup ards
       /\ inc' = IF ards = {} THEN inc ELSE inc \cup {t}
       /\ UNCHANGED rds

BeginCommit(t) == 
    /\ tstate[t] = Open
    /\ rval[t] # Busy
    /\ op' = [op EXCEPT ![t]="c"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t] = Busy]
    /\ tr' = t
    /\ UNCHANGED <<db, vis, tid, deadlocked, tstate, rds, outc, inc>>

AbortCommit(t) == 
    /\ op[t] = "c"
    /\ rval[t] = Busy
    /\ t \in inc \cap outc
    /\ op' = [op EXCEPT ![t] = "a"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Err]
    /\ tr' = t
    /\ tstate' = [tstate EXCEPT ![t]=Aborted]
    /\ UNCHANGED <<db, vis, tid, deadlocked, rds, outc, inc>>

EndCommit(t) ==
    /\ op[t] = "c"
    /\ rval[t] = Busy
    /\ t \notin inc \cap outc
    /\ op' = [op EXCEPT ![t]="c"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Ok]
    /\ tr' = t
    /\ tstate' = [tstate EXCEPT ![t] = Committed]
    /\ UNCHANGED <<db, vis, tid, deadlocked, rds, outc, inc>>

BeginWrS(t, obj, val) ==
    /\ BeginWr(t, obj, val)
    /\ UNCHANGED <<rds, outc, inc>>

AbortS(t) == Abort(t) /\ UNCHANGED <<rds, outc, inc>>
DetectDeadlockS == DetectDeadlock /\ UNCHANGED <<rds, outc, inc>>
TerminationS == Termination /\ UNCHANGED <<rds, outc, inc>>
StartTransactionS(t) == StartTransaction(t) /\ UNCHANGED <<rds, outc, inc>>

NextS == \/ \E t \in Tr, obj \in Obj, val \in Val:
            \/ StartTransactionS(t)
            \/ BeginRdS(t, obj)
            \/ AbortRdS(t, obj)
            \/ EndRdS(t, obj, val)
            \/ BeginWrS(t, obj, val)
            \/ AbortWrS(t, obj)
            \/ EndWrS(t, obj, val)
            \/ BeginCommit(t)
            \/ AbortCommit(t)
            \/ EndCommit(t)
            \/ AbortS(t)
        \/ DetectDeadlockS
        \/ TerminationS

vS == <<op, arg, rval, tr, db, tstate, tid, vis, deadlocked, rds, inc, outc>>

LS == /\ WF_vS(\E t \in Tr: \/ StartTransactionS(t)
                           \/ AbortCommit(t)
                           \/ EndCommit(t)
                           \/ AbortS(t))
      /\ WF_vS(\E t \in Tr, obj \in Obj : 
            \/ AbortRdS(t, obj) 
            \/ AbortWrS(t, obj))
      /\ WF_vS(\E t \in Tr, obj \in Obj, val \in Val : 
            \/ EndRdS(t, obj, val)
            \/ EndWrS(t, obj, val))
      /\ WF_vS(DetectDeadlockS)
      /\ SF_vS(\E t \in Tr: BeginCommit(t) \/ AbortS(t))


SpecS == InitS /\ [][NextS]_vS /\ LS

====