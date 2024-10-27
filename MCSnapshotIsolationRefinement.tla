---- MODULE MCSnapshotIsolationRefinement ----
EXTENDS SnapshotIsolationRefinement

CONSTANTS Hmax

LimitHistory == Len(h) <= Hmax

CTs == {t \in Tr \ {T0}: fateBar[t] = Committed}

Alias == [
    tstate |-> tstate,
    tstateBar |-> tstateBar,
    fateBar |-> fateBar,
    tenvBar |-> tenvBar,
    trBar |-> trBar,
    opBar |-> opBar,
    toBar |-> ord.to,
    argBar |-> argBar,
    rvalBar |-> rvalBar,
    benvBar |-> ord.benv,
    evalBar |-> evalBar,
    ffBar |-> ffBar,
    h |-> h,
    parity |-> parity,
    e |-> Head(h)
    (*
    Init |-> Ser!Init,
    Initialized |-> Ser!Initialized,
    Pfate |-> fateBar \in [Tr \ {T0} -> {Committed, Aborted}],
    Pto |-> ord.to \in Ser!Orderings(CTs),
    Pbenv |-> ord.benv \in [1..Cardinality(CTs)+1 -> [Obj -> Val]],
    Ptenv |-> tenvBar \in {f \in [Tr \ {T0} -> [Obj -> Val]] : \A t \in CTs: f[t] = ord.benv[Ord(t)]}
    *)
]

====