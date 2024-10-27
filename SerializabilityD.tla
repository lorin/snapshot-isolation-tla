---- MODULE SerializabilityD ----
(*********************************************************************)
(* Delay the Serializability spec by one state to support refinement *)
(*********************************************************************)
EXTENDS Serializability

CONSTANT NULL

ASSUME T0 \notin Tr

Initialized == fate # NULL

InitD == /\ tr = T0
         /\ op = "r"
         /\ arg \in Obj
         /\ rval = Vinit
         /\ tstate = [t \in Tr |-> Open]
         /\ fate = NULL
         /\ to = NULL
         /\ benv = NULL
         /\ tenv = NULL
         /\ ff \in {Flip, Flop}

Predict == LET CTs == {t \in Tr : fate'[t] = Committed} IN
           /\ ~Initialized
           /\ fate' \in [Tr -> {Committed, Aborted}]
           /\ to' \in Orderings(CTs)
           /\ benv' \in [1..Cardinality(CTs)+1 -> [Obj -> Val]]
           /\ tenv' \in {f \in [CTs -> [Obj -> Val]] : \A t \in CTs: f[t] = benv'[Ord(t)']}
           /\ UNCHANGED <<tr, op, arg, rval, tstate, ff>>

NextD == \/ Predict
         \/ (Initialized /\ Next)


(* Note: skipping liveness for now *)
SpecD == InitD /\ [][NextD]_v 

====