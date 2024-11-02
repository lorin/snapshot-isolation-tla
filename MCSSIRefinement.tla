---- MODULE MCSSIRefinement ----
EXTENDS SSIRefinement

CONSTANTS Hmax

LimitHistory == Len(h) <= Hmax

====