---- MODULE MCMVCCRefinement ----
EXTENDS MVCCRefinement

CONSTANTS Hmax

LimitHistory == Len(h) <= Hmax

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
]

====