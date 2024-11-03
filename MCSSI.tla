---- MODULE MCSSI ----
EXTENDS SSI,TLC

Terminates == <> Done

NeverAbortsRead == ~ \E t \in Tr, obj \in Obj:
       /\ op[t] = "r"
       /\ rval[t] = Busy
       /\ arg[t] = obj
       /\ ReadCreatesPivot(t, obj)

Symmetry == Permutations(Tr) \cup Permutations(Obj) \cup Permutations(Val)

SpecSWOL == InitS /\ [][NextS]_vS

====