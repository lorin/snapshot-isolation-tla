---- MODULE SerializabilityDRefinement ----
(******************************************************)
(* Show that SerializabilityD refines Serializability *)
(******************************************************)

EXTENDS SerializabilityD

VARIABLES fateP, toP, benvP, tenvP


InitDR == LET CTs == {t \in Tr \ {T0}: fateP[t] = Committed} 
              OrdP(t) == CHOOSE i \in DOMAIN toP : toP[i] = t
          IN
          /\ InitD
          /\ fateP \in [Tr \ {T0} -> {Committed, Aborted}]
          /\ toP \in Orderings(CTs)
          /\ benvP \in [1..Cardinality(CTs)+1 -> [Obj -> Val]]
          /\ tenvP \in {f \in [CTs -> [Obj -> Val]] : \A t \in CTs: f[t] = benvP[OrdP(t)]}

PredictR == /\ Predict
            /\ fate' = fateP
            /\ to' = toP
            /\ benv' = benvP
            /\ tenv' = tenvP
            /\ UNCHANGED <<fateP, toP, benvP, tenvP>>

NextDR == \/ PredictR
          \/ /\ Initialized
             /\ Next
             /\ UNCHANGED <<fateP, toP, benvP, tenvP>>

vv == <<tr, op, arg, rval, tstate, fate, to, tenv, benv, ff, fateP, toP, benvP, tenvP>>

SpecDR == InitDR /\ [][NextDR]_vv

Ser == INSTANCE Serializability WITH 
    fate <- IF fate = NULL THEN fateP ELSE fate,
    to   <- IF to = NULL THEN toP ELSE to,
    tenv <- IF tenv = NULL THEN tenvP ELSE tenv,
    benv <- IF benv = NULL THEN benvP ELSE benv

SerSpec == Ser!Init /\ [][Ser!Next]_Ser!v 

THEOREM SpecDR => SerSpec

====