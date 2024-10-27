---- MODULE SerializabilityDRefinement ----
(******************************************************)
(* Show that SerializabilityD refines Serializability *)
(******************************************************)

EXTENDS SerializabilityD

VARIABLES fateP, toP, benvP, tenvP

InitDR == LET CTs == {t \in Tr \ {T0}: fateP[t] = Committed} IN
          /\ fateP \in [Tr \ {T0} -> {Committed, Aborted}]
          /\ toP \in Orderings(CTs)
          /\ benvP \in [1..Cardinality(CTs)+1 -> [Obj -> Val]]
          /\ tenvP \in {f \in [CTs -> [Obj -> Val]] : \A t \in CTs: f[t] = benv'[Ord(t)']}

PredictR == /\ Predict
            /\ fate' = fateP
            /\ to' = toP
            /\ benv' = benvP
            /\ tenv' = tenvP

NextDR == \/ PredictR
          \/ /\ Initialized
             /\ Next
             /\ UNCHANGED <<fateP, toP, benvP, tenvP>>

vv == <<tr, op, arg, rval, tstate, fate, to, tenv, benv, ff, fateP, toP, benvP, tenvP>>

SpecDR == InitDR /\ [][NextDR]_v 

====