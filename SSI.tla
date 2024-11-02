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
         /\ reads = [t \in Tr |-> {}]
         /\ inc = {}
         /\ outc = {}

BeginRdS(t, obj) == 
    /\ BeginRd(t, obj)
    /\ reads' = [reads EXCEPT ![obj]=@ \cup {t}]
    /\ (\E tw \in Tr : ActiveWrite(tw, obj)) => 
        LET tw == CHOOSE tw \in Tr : ActiveWrite(tw, obj)
        IN /\ inc' = inc \union {tw}
           /\ outc' = outc \union {t}

(*****************************************************)
(* object version v1 is newer than object version v2 *)
(*****************************************************)
Newer(v1, v2) == tid[v1.tr] > tid[v2.tr]

(************************************************************************)
(* True when transaction t creates a pivot transaction when reading obj *)
(************************************************************************)
ReadCreatesPivot(t, obj) == 
    LET v1 == GetVer(obj, vis[t])
    IN \E v2 \in db[obj] : /\ Newer(v2, v1) 
                       /\ tstate[v2.tr] = Committed
                       /\ v2.tr \in outc

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
        newer == { w \in db[obj] : Newer(w, ver) /\ tstate[w] # Aborted}
    IN /\ ~ReadCreatesPivot(t, obj)
       /\ EndRd(t, obj, val)
       (* each later transaction that wrote has an inbound conflict *)
       /\ inc' = inc \cup {w.tr : w \in newer}
       (* if there are any newer versions, t has an outbound conflict *)
       /\ outc' = IF newer = {} THEN outc ELSE outc \cup {t}
       /\ UNCHANGED reads

AbortWrS(t, obj) == 
    \/ AbortWr(t, obj)
    \/ /\ op[t] = "w"
       /\ rval[t] = Busy
       /\ reads[obj] \ {t} # {}
       /\ \E tt \in reads[obj] \ {t} : 
            \/ tstate[tt] = Open
            \/ tstate[tt] = Committed /\ Concurrent(t, tt)
       /\ op' = [op EXCEPT ![t] = "a"]
       /\ arg' = [arg EXCEPT ![t] = <<>>]
       /\ rval' = [rval EXCEPT ![t]=Err]
       /\ tr' = t
       /\ tstate' = [tstate EXCEPT ![t]=Aborted]


NextS == \/ \E t \in Tr, obj \in Obj, val \in Val:
            \/ BeginRdS(t, obj)
            \/ EndRdS(t, obj, val)
            \/ AbortRdS(t, obj)
            \/ AbortWrS(t, obj)

SpecS == InitS

====