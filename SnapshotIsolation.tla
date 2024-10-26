---- MODULE SnapshotIsolation ----

EXTENDS Naturals

CONSTANTS Tr, Obj, Val, T0, V0,
          Unstarted, Open, Committed, Aborted,
          Ok, Err,
          Busy

ASSUME V0 \in Val

None == CHOOSE n : n \notin Nat


VARIABLES 
    (**********************)
    (* external variables *)
    (**********************)
    op,   (* operation *)
    arg,  (* operation argument *)
    rval, (* operation return value *)


    (**********************)
    (* internal variables *)
    (**********************)
    tstate,    (* state of each transaction *)
    tid,       (* timestamp of each transaction *)
    snap,      (* database snapshot used by each transaction *)
    env,       (* environment of each transaction *)

    (**********************)
    (* history variables  *)
    (**********************)
    anc        (* ancestors of each transaction *)


SnapInit == [obj \in Obj |-> V0]

TypeOk == /\ op \in [Tr -> {"-", "s", "r", "w", "c", "a"}]
          /\ arg \in [Tr -> {<<>>} \union Obj \union Obj \X Val]
          /\ rval \in [Tr -> Val \union {Ok, Busy, Err}]
          /\ tid \in [Tr -> Nat \union {None}]
          /\ tstate \in [Tr -> {Unstarted, Open, Committed, Aborted}]
          /\ snap \in [Tr -> [Obj -> Val]]
          /\ env \in [Tr -> [Obj -> Val]]

Init == /\ op = [t \in Tr |-> "-"]
        /\ arg = [t \in Tr |-> <<>>]
        /\ rval = [t \in Tr |-> Ok]
        /\ tid = [t \in Tr |-> IF t=T0 THEN 0 ELSE None]
        /\ tstate = [t \in Tr |-> IF t=T0 THEN Committed ELSE Unstarted]
        /\ snap = [t \in Tr |-> SnapInit]
        /\ env = [t \in Tr |-> SnapInit]
        /\ anc       = [t \in Tr |-> {}]

(* Maximum value of a set *)
Max(S) == CHOOSE x \in S : \A y \in S \ {x} : x >= y

(* Latest committted transaction *)
LCT == CHOOSE t \in Tr : /\ tstate[t] = Committed 
                         /\ ~ \E tr \in Tr: /\ tstate[tr]=Committed 
                                            /\ tid[tr] > tid[t]

StartTransaction(t) == 
    LET tl == LCT
        mxid == Max({tid[tr] : tr \in Tr} \ {None}) (* maximum transaction id *)
    IN
    /\ tstate[t] = Unstarted
    /\ op' = [op EXCEPT ![t]="s"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Ok]
    /\ tstate' = [tstate EXCEPT ![t]=Open]
    /\ tid' = [tid EXCEPT ![t]=mxid+1]
    /\ snap' = [snap EXCEPT ![t]=env[tl]]
    /\ env' = [env EXCEPT ![t]=env[tl]]
    /\ anc' = [anc EXCEPT ![t]={tl} \union anc[tl]]

BeginRd(t, obj) == /\ tstate[t] = Open
                   /\ rval[t] # Busy
                   /\ op' = [op EXCEPT ![t]="r"]
                   /\ arg' = [arg EXCEPT ![t]=obj]
                   /\ rval' = [rval EXCEPT ![t]=Busy]
                   /\ UNCHANGED  <<tstate, tid, snap, env, anc>>

EndRd(t, obj, val) == /\ op[t] = "r"
                      /\ rval[t] = Busy
                      /\ val = env[t][obj]
                      /\ rval' = [rval EXCEPT ![t]=val]
                      /\ UNCHANGED <<op, arg, tstate, tid, snap, env, anc>>

BeginWr(t, obj, val) == /\ tstate[t] = Open
                        /\ rval[t] # Busy
                        /\ op' = [op EXCEPT ![t]="w"]
                        /\ arg' = [arg EXCEPT ![t] = <<obj, val>>]
                        /\ rval' = [rval EXCEPT ![t]=Busy]
                        /\ UNCHANGED  <<tstate, tid, snap, env, anc>>

(*******************************************************************)
(* True if transaction *t* is active and has modified object *obj* *)
(*******************************************************************)
ActiveWrite(t, obj) == /\ tstate[t] = Open
                       /\ env[t][obj] # snap[t][obj]

(***********************************************************************)
(* True if transaction *t* is committed and has modified object *obj* *)
(**********************************************************************)
CommittedWrite(t, obj) == /\ tstate[t] = Committed
                       /\ env[t][obj] # snap[t][obj]

(***************************************************************************)
(* Two transactions are concurrent if neither is the ancestor of the other *)
(***************************************************************************)
Concurrent(t1, t2) == /\ t1 \notin anc[t2]
                      /\ t2 \notin anc[t1]

(*********************************************************************************************************)
(* True if there is another transaction that has a write conflict with transaction *t* with object *obj* *)
(*********************************************************************************************************)
WriteConflict(t, obj) == \E tr \in Tr \{t} : CommittedWrite(tr, obj) /\ Concurrent(t, tr)

EndWr(t, obj, val) == /\ op[t] = "w"
                      /\ arg[t] = <<obj, val>>
                      /\ rval[t] = Busy
                      /\ ~ \E tr \in Tr \ {t} : \/ ActiveWrite(tr, obj)
                      /\ ~ WriteConflict(t, obj)
                      /\ env' = [env EXCEPT ![t][obj]=val]
                      /\ rval' = [rval EXCEPT ![t]=Ok]
                      /\ UNCHANGED  <<op, arg, tstate, tid, snap, anc>>


AbortWr(t, obj, val) == /\ op[t] = "w"
                        /\ rval[t] = Busy
                        /\ WriteConflict(t, obj)
                        /\ op' = [op EXCEPT ![t] = "a"]
                        /\ arg' = [arg EXCEPT ![t] = <<>>]
                        /\ rval' = [rval EXCEPT ![t]=Err]
                        /\ tstate' = [tstate EXCEPT ![t]=Aborted]
                      /\ UNCHANGED  <<tid, snap, anc, env>>

Abort(t) == /\ tstate[t] = Open
            /\ rval[t] # Busy
            /\ op' = [op EXCEPT ![t]="a"]
            /\ arg' = [arg EXCEPT ![t] = <<>>]
            /\ rval' = [rval EXCEPT ![t]=Ok]
            /\ tstate' = [tstate EXCEPT ![t]=Aborted]
            /\ UNCHANGED <<tid, snap, env, anc>>

Commit(t) == /\ tstate[t] = Open
             /\ rval[t] # Busy
             /\ tstate' = [tstate EXCEPT ![t] = Committed]
             /\ op' = [op EXCEPT ![t]="c"]
             /\ arg' = [arg EXCEPT ![t] = <<>>]
             /\ rval' = [rval EXCEPT ![t]=Ok]
             /\ tstate' = [tstate EXCEPT ![t] = Committed]
             /\ UNCHANGED <<tid, snap, env, anc>>

Done == \A t \in Tr: tstate[t] \in {Committed, Aborted}
v == <<op, arg, rval, tstate, tid, snap, env, anc>>

Termination == Done /\ UNCHANGED v

Next == \/ \E t \in Tr, obj \in Obj, val \in Val:
            \/ StartTransaction(t)
            \/ BeginRd(t, obj)
            \/ EndRd(t, obj, val)
            \/ BeginWr(t, obj, val)
            \/ EndWr(t, obj, val)
            \/ AbortWr(t, obj, val)
            \/ Commit(t)
            \/ Abort(t)
        \/ Termination

L == /\ WF_v(\E t \in Tr, obj \in Obj, val \in Val : 
                \/ EndRd(t, obj, val)
                \/ EndWr(t, obj, val)
                \/ AbortWr(t, obj, val))
     /\ WF_v(\E t \in Tr: \/ StartTransaction(t))
     /\ SF_v(\E t \in Tr: Commit(t) \/ Abort(t))

Spec == Init /\ [][Next]_v /\ L

====