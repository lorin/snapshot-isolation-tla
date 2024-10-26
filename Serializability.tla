---- MODULE Serializability ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Tr, Obj, Pred, Val,
          Undefined, 
          Open, Committed, Aborted,
          Ok,
          Flip, Flop,
          Vinit, 
          T0, None

(* To check refinement in TLC, we need to specify these as constants *)
\* T0 == CHOOSE t : t \notin Tr
\* None == CHOOSE v : v \notin Obj \union (Obj \X Val) \union Pred


VARIABLES 
          (********************************)
          (* external variables           *)
          (********************************)
          tr,   (* transaction *)
          op,   (* operation *)
          arg,  (* operation argument *)
          rval, (* operation return value *)

          (********************************)
          (* internal variables           *)
          (********************************)
          tstate, (* state of transaction (open, committed, aborted) *)
          fate,   (* the ultimate fate of each transaction: 
                     committed or aborted *)
          to,     (* transaction order: a sequence that indicates 
                    the commit order of committed transactions *)
          tenv,   (* value of variables for each transaction *)
          benv,   (* sequence: beginning state of the i'th transaction *)
          eval,   (* predicate evlauation *)
          ff      (* flip/flop *)

v == <<tr, op, arg, rval, tstate, fate, to, tenv, benv, eval, ff>>

(* committed transactions *)
CT == {t \in Tr: fate[t] = Committed}

N == Cardinality(CT)

(* Generate all permuted sequences of the set S *)
Orderings(S) == {seq \in [1..Cardinality(S) -> S] : \A i,j \in DOMAIN seq : seq[i] = seq[j] => i = j}

Op == {"r", "w", "p", "c", "a"}
Arg == Obj \union (Obj \X Val) \union Pred \union {None}
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
          /\ eval \in [Pred -> [[Obj -> Val] -> SUBSET Obj]]
          /\ ff \in {Flip, Flop}


(* the ordinal value (e.g., 1,2,3) of a committed transaction *)
Ord(t) == CHOOSE i \in DOMAIN to : to[i] = t


Toggle(f) == CASE f = Flip -> Flop
               [] f = Flop -> Flip

Init == /\ tr = T0
        /\ op = "r"
        /\ arg \in Obj
        /\ rval = Vinit
        /\ tstate = [t \in Tr |-> Open]
        /\ fate \in [Tr -> {Committed, Aborted}]
        /\ to \in Orderings(CT)
        /\ benv \in [1..N+1 -> [Obj -> Val]]
        /\ tenv \in {f \in [CT -> [Obj -> Val]] : \A t \in CT: f[t] = benv[Ord(t)]}
        /\ eval \in [Pred -> [[Obj -> Val] -> SUBSET Obj]]
        /\ ff \in {Flip, Flop}


Read(t, obj, val) == /\ tstate[t] = Open
                     /\ \/ fate[t] = Aborted (* for aborted commits, we don't care what the read value is *)
                        \/ fate[t] = Committed /\ val = tenv[t][obj] 
                     /\ tr' = t
                     /\ op' = "r"
                     /\ arg' = obj
                     /\ rval' = val
                     /\ ff' = Toggle(ff)
                     /\ UNCHANGED <<tstate, fate, to, tenv, benv, eval>>


PredRead(t, P) == /\ tstate[t] = Open
                  /\ tr' = t
                  /\ op' = "p"
                  /\ arg' = P
                  /\ rval' \in Obj
                  /\ fate[t] = Committed => rval' = eval[P][tenv[t]]
                  /\ ff' = Toggle(ff)
                  /\ UNCHANGED <<tstate, fate, to, tenv, benv, eval>>

Write(t, obj, val) == /\ tstate[t] = Open
                      /\ tr' = t
                      /\ op' = "w"
                      /\ arg' = <<obj, val>>
                      /\ rval' = Ok
                      /\ tenv' = IF fate[t] = Committed THEN [tenv EXCEPT ![t] = [@ EXCEPT ![obj]=val]] ELSE tenv
                      /\ ff' = Toggle(ff)
                      /\ UNCHANGED <<tstate, fate, to, benv, eval>>

Abort(t) == /\ tstate[t] = Open
            /\ fate[t] = Aborted
            /\ tr' = t
            /\ op' = "a"
            /\ arg' = None
            /\ rval' = Ok
            /\ tstate' = [tstate EXCEPT ![t]=Aborted]
            /\ UNCHANGED <<fate, to, tenv, benv, eval, ff>>

Commit(t) == /\ tstate[t] = Open
             /\ fate[t] = Committed
             /\ tenv[t] = benv[Ord(t)+1]
             /\ tr' = t
             /\ op' = "c"
             /\ arg' = None
             /\ rval' = Ok
             /\ tstate' = [tstate EXCEPT ![t]=Committed]
             /\ UNCHANGED <<fate, to, tenv, benv, eval, ff>>

(*******************************************************************************************)
(* Number of variables with the same values in environments e1 and e2                      *)
(*                                                                                         *)
(* A helper function for use in fairness properties.                                       *)
(*******************************************************************************************)
M(e1, e2) == Cardinality({obj \in Obj : e1[obj]=e2[obj]})

(*******************************************************************************************)
(* W(j,k) is true if there's a transaction t doing a write where:                          *)
(*  1. the number of variables in the 1st state that are equal to the expected values is j *)
(*  2. the number of variables in the 2nd state that are equal to the expected values is k *)
(*                                                                                         *)
(* A helper function for use in fairness properties.                                       *)
(*******************************************************************************************)
W(j, k) ==  \E t \in CT, obj \in Obj, val \in Val : 
            /\ Write(t, obj, val)
            /\ M(tenv[t],  benv[Ord(t)+1])=j
            /\ M(tenv'[t], benv[Ord(t)+1])=k

Termination == /\ \A t \in Tr: tstate[t] \in {Committed, Aborted}
               /\ UNCHANGED v

Next == \/ \E t \in Tr:
            \/ Commit(t)
            \/ Abort(t)
            \/ \E obj \in Obj, val \in Val:
                \/ Read(t, obj, val)
                \/ Write(t, obj, val)
            \/ \E P \in Pred: PredRead(t, P)
        \/ Termination

L == /\ SF_v(\E t \in Tr: Commit(t))
     /\ WF_v(\E t \in Tr: Abort(t))
     /\ WF_v(W(0, 1)) 
     /\ \A i \in 1..Cardinality(Obj)-1 : SF_v(W(i, i+1))

Spec == Init /\ [][Next]_v /\ L

====