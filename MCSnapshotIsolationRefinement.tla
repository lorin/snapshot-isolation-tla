---- MODULE MCSnapshotIsolationRefinement ----
EXTENDS SnapshotIsolationRefinement

CONSTANTS Hmax

LimitHistory == Len(h) <= Hmax

CTs == {t \in Tr \ {T0}: fateBar[t] = Committed}

Alias == [
    toBar |-> ord.to,
    benvBar |-> ord.benv,
    trBar |-> trBar,
    opBar |-> opBar,
    argBar |-> argBar,
    rvalBar |-> rvalBar,
    tstateBar |-> tstateBar,
    tenvBar |-> tenvBar,
    fateBar |-> fateBar,
    evalBar |-> evalBar,
    ffBar |-> ffBar,
    Init |-> Ser!Init,
    Initialized |-> Ser!Initialized,
    Pfate |-> fateBar \in [Tr \ {T0} -> {Committed, Aborted}],
    Pto |-> ord.to \in Ser!Orderings(CTs),
    Pbenv |-> ord.benv \in [1..Cardinality(CTs)+1 -> [Obj -> Val]],
    Ptenv |-> tenvBar \in {f \in [Tr \ {T0} -> [Obj -> Val]] : \A t \in CTs: f[t] = ord.benv[Ord(t)]}
]

====