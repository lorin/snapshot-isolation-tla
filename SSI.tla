---- MODULE SSI ----
EXTENDS MVCC

VARIABLES reads, inc, outc


TypeOkS == /\ reads \in [Tr -> SUBSET Obj]
           /\ inc \subseteq Tr
           /\ outc \subseteq Tr

InitS == /\ Init
         /\ reads = [t \in Tr |-> {}]
         /\ inc = {}
         /\ outc = {}

BeginRdS(tr, obj) == 
    /\ BeginRd(tr, obj)
    /\ (\E tw \in Tr : ActiveWrite(tw, obj)) => 
        LET tw == CHOOSE tw \in Tr : ActiveWrite(tw, obj)
        IN /\ inc' = inc \union {tw}
           /\ outc' = outc \union {tr}

NextS == \/ \E t \in Tr, obj \in Obj, val \in Val:
            \/ BeginRdS(t, obj)

SpecS == InitS

====