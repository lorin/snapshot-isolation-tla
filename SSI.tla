---- MODULE SSI ----
EXTENDS MVCC

(***************************)
(* rw dependency: Tr -> Tw *)
(* inbound: Tw (write)     *)
(* outbound: Tr (read)     *)
(***************************)

VARIABLES reads, inc, outc

TypeOkS == /\ reads \in [Obj -> SUBSET Tr]
           /\ inc \subseteq Tr
           /\ outc \subseteq Tr

InitS == /\ Init
         /\ reads = [obj \in Obj |-> {}]
         /\ inc = {}
         /\ outc = {}

BeginRdS(t, obj) ==
    LET isActiveWrite == (\E tw \in Tr : ActiveWrite(tw, obj))
        tw == CHOOSE tw \in Tr : ActiveWrite(tw, obj)
    IN /\ BeginRd(t, obj)
       /\ reads' = [reads EXCEPT ![obj]=@ \cup {t}]
       /\ inc' = IF isActiveWrite THEN inc \union {tw} ELSE inc
       /\ outc' = IF isActiveWrite THEN outc \union {t} ELSE outc
   
(*****************************************************)
(* object version v1 is newer than object version v2 *)
(*****************************************************)
Newer(v1, v2) == tid[v1.tr] > tid[v2.tr]

(************************************************************************)
(* True when transaction t creates a pivot transaction when reading obj *)
(************************************************************************)
ReadCreatesPivot(t, obj) ==
    LET vr == GetVer(obj, vis[t])
    IN 
    /\ vr.tr # t (* reading our own write cannot create a pivot *)
    /\ \E vw \in db[obj] : /\ Concurrent(vr.tr, vw.tr)
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
       /\ UNCHANGED <<db, vis, tid, deadlocked, reads, inc, outc>>

EndRdS(t, obj, val) ==
    LET ver == GetVer(obj, vis[t])
        newer == IF ver.tr # t THEN { w \in db[obj] : Newer(w, ver) /\ tstate[w] # Aborted} ELSE {}
    IN 
       /\ EndRd(t, obj, val)
       /\ ~ReadCreatesPivot(t, obj)
       (* each later transaction that wrote has an inbound conflict *)
       /\ inc' = inc \cup {w.tr : w \in newer}
       (* if there are any newer versions, t has an outbound conflict *)
       /\ outc' = IF newer = {} THEN outc ELSE outc \cup {t}
       /\ UNCHANGED reads


(*
if there is a SIREAD lock(rl) on x
    with rl.owner is running
    or commit(rl.owner) > begin(T):
        if rl.owner is committed and rl.owner.inConflict:
*)
WriteCreatesPivot(t, obj) ==
       \E tt \in reads[obj] \ {t} :
         \/ tstate[tt] = Open
         \/ tstate[tt] = Committed /\ Concurrent(t, tt)

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
    /\ UNCHANGED <<reads, inc, outc>>

EndWrS(t, obj, val) ==
        (* active transactions *)
    LET active == {u \in Tr: tstate[u] = Open}
        (* active transactions that are reading obj *)
        areads == reads[obj] \cap active
    IN /\ EndWr(t, obj, val)
       /\ ~WriteCreatesPivot(t, obj)
       /\ outc' = outc \cup areads
       /\ inc' = IF areads = {} THEN inc ELSE inc \cup {t}
       /\ UNCHANGED reads

BeginCommit(t) == 
    /\ tstate[t] = Open
    /\ rval[t] # Busy
    /\ op' = [op EXCEPT ![t]="c"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t] = Busy]
    /\ tr' = t
    /\ UNCHANGED <<db, vis, tid, deadlocked, tstate, reads, inc, outc>>

AbortCommit(t) == 
    /\ op[t] = "c"
    /\ rval[t] = Busy
    /\ t \in inc \cap outc
    /\ op' = [op EXCEPT ![t] = "a"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Err]
    /\ tr' = t
    /\ tstate' = [tstate EXCEPT ![t]=Aborted]
    /\ UNCHANGED <<db, vis, tid, deadlocked, reads, inc, outc>>

EndCommit(t) ==
    /\ op[t] = "c"
    /\ rval[t] = Busy
    /\ t \notin inc \cap outc
    /\ op' = [op EXCEPT ![t]="c"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Ok]
    /\ tr' = t
    /\ tstate' = [tstate EXCEPT ![t] = Committed]
    /\ UNCHANGED <<db, vis, tid, deadlocked, reads, inc, outc>>

BeginWrS(t, obj, val) ==
    /\ BeginWr(t, obj, val)
    /\ UNCHANGED <<reads, inc, outc>>

DetectDeadlockS == DetectDeadlock /\ UNCHANGED <<reads, inc, outc>>
TerminationS == Termination /\ UNCHANGED <<reads, inc, outc>>
StartTransactionS(t) == StartTransaction(t) /\ UNCHANGED <<reads, inc, outc>>

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
        \/ DetectDeadlockS
        \/ TerminationS

vS == <<op, arg, rval, tr, db, tstate, tid, vis, deadlocked, reads, inc, outc>>

SpecS == InitS /\ [][NextS]_vS

====