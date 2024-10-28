---- MODULE MCSerializability ----
EXTENDS Serializability

Op == {"r", "w", "c", "a"}
Arg == Obj \union (Obj \X Val) \union {None}
Rval == Val \union {Ok} \union SUBSET Obj

TypeOk == /\ tr \in Tr \union {T0}
          /\ op \in Op
          /\ arg \in Arg 
          /\ rval \in Rval
          /\ tstate \in [Tr -> {Open, Committed, Aborted}]
          /\ fate \in [Tr -> {Committed, Aborted}]
          /\ to \in Orderings(CT)
          /\ benv \in [1..N+1 -> [Obj -> Val]]
          /\ tenv \in [CT -> [Obj -> Val]]
          /\ ff \in {Flip, Flop}

====