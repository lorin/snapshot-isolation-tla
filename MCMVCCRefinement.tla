---- MODULE MCMVCCRefinement ----
EXTENDS MVCCRefinement

CONSTANTS Hmax

LimitHistory == Len(h) <= Hmax

CTs == {t \in Tr \ {T0}: fateBar[t] = Committed}

Alias == [
    db |-> db,
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
    ffBar |-> ffBar,
    h |-> h

    (*
    Initialized |-> Ser!Initialized,

    tstateEqOpen |-> tstateBar[trBar] = Open,
    fateTCommitted |-> tstateBar[trBar] = Committed,
    tenvTrBar |-> tenvBar[trBar],
    trStart |-> ord.benv[Ord(trBar)],
    trEnd |-> ord.benv[Ord(trBar)+1]

    parity |-> parity,
    e |-> Head(h)
    Init |-> Ser!Init,
    Pfate |-> fateBar \in [Tr \ {T0} -> {Committed, Aborted}],
    Pto |-> ord.to \in Ser!Orderings(CTs),
    Pbenv |-> ord.benv \in [1..Cardinality(CTs)+1 -> [Obj -> Val]],
    Ptenv |-> tenvBar \in {f \in [Tr \ {T0} -> [Obj -> Val]] : \A t \in CTs: f[t] = ord.benv[Ord(t)]}
    *)
]

====