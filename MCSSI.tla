---- MODULE MCSSI ----
EXTENDS SSI,TLC

Terminates == <> Done

NeverAbortsRead == ~ \E t \in Tr, obj \in Obj:
       /\ op[t] = "r"
       /\ rval[t] = Busy
       /\ arg[t] = obj
       /\ ReadCreatesPivot(t, obj)

NeverAbortsCommit == ~ \E t \in Tr:
    /\ op[t] = "c"
    /\ rval[t] = Busy
    /\ t \in inc \cap outc

NeverAbortsWrite == ~ \E t \in Tr:
    LET obj == arg[t][1]
    IN /\ op[t] = "w"
       /\ rval[t] = Busy
       /\ WriteCreatesPivot(t, obj)

DontWriteV0 == ~\E t \in Tr: (op[t] = "w" /\ arg[t][2] = V0)

Alias == [
    op|->op,
    rval|->rval,
    rds|->rds,
    tsate|->tstate,
    inc|->inc,
    dwv|-> ~ \E t \in Tr: (op[t] = "w" /\ arg[t][2] = V0)

    \* DontWriteV0|->DontWriteV0
]

Symmetry == Permutations(Tr) \cup Permutations(Obj) \cup Permutations(Val)


SpecSWOL == InitS /\ [][NextS]_vS

====