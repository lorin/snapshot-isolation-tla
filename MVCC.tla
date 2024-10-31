---- MODULE MVCC ----

EXTENDS Naturals, TransitiveClosure

CONSTANTS Tr, Obj, Val, T0, V0,
          Unstarted, Open, Committed, Aborted,
          Ok, Err,
          Busy

ASSUME V0 \in Val

None == CHOOSE n : n \notin Nat


VARIABLES 
(********************************)
(* externally visible variables *)
(********************************)
    op,   (* operation *)
    arg,  (* operation argument *)
    rval, (* operation return value *)


    (**********************)
    (* internal variables *)
    (**********************)
    db,         (* database: contains object versions *)
    vis,        (* set of transactions visible to each transaction *)
    tstate,     (* state of each transaction *)
    tid,        (* transaction id: logical timestamp of each transaction *)
    deadlocked (* transactions that have deadlocked *)


SnapInit == [obj \in Obj |-> V0]

TypeOk == /\ op \in [Tr -> {"-", "s", "r", "w", "c", "a"}]
          /\ arg \in [Tr -> {<<>>} \union Obj \union Obj \X Val]
          /\ rval \in [Tr -> Val \union {Ok, Busy, Err}]
          /\ db \in [Obj -> SUBSET [val: Val, tr: Tr]]
          /\ vis \in [Tr -> SUBSET Tr]
          /\ tid \in [Tr -> Nat \union {None}]
          /\ tstate \in [Tr -> {Unstarted, Open, Committed, Aborted}]
          /\ deadlocked \subseteq Tr

Init == /\ op = [t \in Tr |-> "-"]
        /\ arg = [t \in Tr |-> <<>>]
        /\ rval = [t \in Tr |-> Ok]
        /\ db = [obj \in Obj |-> {[val|-> V0, tr|-> T0]}]
        /\ vis = [tr \in Tr |-> {}]
        /\ tid = [t \in Tr |-> IF t=T0 THEN 0 ELSE None]
        /\ tstate = [t \in Tr |-> IF t=T0 THEN Committed ELSE Unstarted]
        /\ deadlocked = {}

(* Maximum value of a set *)
Max(S) == CHOOSE x \in S : \A y \in S \ {x} : x >= y

StartTransaction(t) == 
    LET CTs == {tr \in Tr: /\ tstate[tr] = Committed}
        mxid == Max({tid[tr] : tr \in Tr} \ {None}) (* maximum transaction id *)
    IN
    /\ tstate[t] = Unstarted
    /\ op' = [op EXCEPT ![t]="s"]
    /\ arg' = [arg EXCEPT ![t] = <<>>]
    /\ rval' = [rval EXCEPT ![t]=Ok]
    /\ vis' = [vis EXCEPT ![t]=CTs \union {t}]
    /\ tid' = [tid EXCEPT ![t]=mxid+1]
    /\ tstate' = [tstate EXCEPT ![t]=Open]
    /\ UNCHANGED <<db, deadlocked>>

BeginRd(t, obj) == /\ tstate[t] = Open
                   /\ rval[t] # Busy
                   /\ op' = [op EXCEPT ![t]="r"]
                   /\ arg' = [arg EXCEPT ![t]=obj]
                   /\ rval' = [rval EXCEPT ![t]=Busy]
                   /\ UNCHANGED  <<db, vis, tstate, tid, deadlocked>>

(* Retrieve the value associated with the object for this tranaction *)
GetVal(t, obj, vist) == 
    LET ver == CHOOSE v \in db[obj] : 
        /\ v.tr \in vist
        /\ ~ \E vv \in db[obj] : /\ vv \in db[obj]
                               /\ vv.tr \in vist
                               /\ tid[vv.tr] > tid[v.tr]
     IN ver.val

EndRd(t, obj, val) == /\ op[t] = "r"
                      /\ rval[t] = Busy
                      /\ arg[t] = obj
                      /\ val = GetVal(t, obj, vis[t])
                      /\ rval' = [rval EXCEPT ![t]=val]
                      /\ UNCHANGED <<op, arg, db, db, vis, tstate, tid, deadlocked>>

BeginWr(t, obj, val) == /\ tstate[t] = Open
                        /\ rval[t] # Busy
                        /\ op' = [op EXCEPT ![t]="w"]
                        /\ arg' = [arg EXCEPT ![t] = <<obj, val>>]
                        /\ rval' = [rval EXCEPT ![t]=Busy]
                        /\ UNCHANGED  <<db, vis, tid, tstate, deadlocked>>

(*******************************************************************)
(* True if transaction *t* is active and has modified object *obj* *)
(*******************************************************************)
ActiveWrite(t, obj) == /\ tstate[t] = Open
                       /\ \E ver \in db[obj]: ver.tr = t

(*************************************)
(* Dependencies due to active writes *)
(*************************************)
Deps == {<<Ti, Tj>> \in Tr \X Tr :
            /\ Ti # Tj
            /\ tstate[Ti] = Open
            /\ op[Ti] = "w"
            /\ rval[Ti] = Busy
            /\ \E obj \in Obj: arg[Ti][1] = obj /\ ActiveWrite(Tj, obj) }


(************************************************************)
(* Detect if deadlock is currently occurring.               *)
(* This only fires if there are as-yet-undetected deadlocks *)
(************************************************************)
DetectDeadlock == LET TCD == TC(Deps)
                      stuck == {t \in Tr: <<t, t>> \in TCD} IN 
                  /\ stuck \ deadlocked # {} (* something is stuck that hasn't previously been captured as deadlocked *)
                  /\ deadlocked' = deadlocked \union stuck
                  /\ UNCHANGED <<op, arg, rval, db, vis, tstate, tid>>


(***********************************************************************)
(* True if transaction *t* is committed and has modified object *obj* *)
(**********************************************************************)
CommittedWrite(t, obj) == /\ tstate[t] = Committed
                          /\ \E ver \in db[obj]: ver.tr = t

(***********************************************************************)
(* Two transactions are concurrent if neither is visible to the other  *)
(***********************************************************************)
Concurrent(t1, t2) == /\ t1 \notin vis[t2]
                      /\ t2 \notin vis[t1]

(*********************************************************************************************************)
(* True if there is another transaction that has a write conflict with transaction *t* with object *obj* *)
(*********************************************************************************************************)
WriteConflict(t, obj) == \E tr \in Tr \{t} : CommittedWrite(tr, obj) /\ Concurrent(t, tr)

EndWr(t, obj, val) == LET oldwrites == {v \in db[obj] : v.tr=t}
                          ver == [val|->val, tr|->t]
                      IN
                      /\ op[t] = "w"
                      /\ arg[t] = <<obj, val>>
                      /\ rval[t] = Busy
                      /\ ~ \E tr \in Tr \ {t} : \/ ActiveWrite(tr, obj)
                      /\ ~ WriteConflict(t, obj)
                      /\ db' = [db EXCEPT ![obj]=(@ \ oldwrites) \union {ver}]
                      /\ rval' = [rval EXCEPT ![t]=Ok]
                      /\ UNCHANGED  <<op, arg, tstate, tid, vis, deadlocked>>

AbortWr(t, obj, val) == /\ op[t] = "w"
                        /\ rval[t] = Busy
                        /\ \/ WriteConflict(t, obj)
                           \/ t \in deadlocked
                        /\ op' = [op EXCEPT ![t] = "a"]
                        /\ arg' = [arg EXCEPT ![t] = <<>>]
                        /\ rval' = [rval EXCEPT ![t]=Err]
                        /\ tstate' = [tstate EXCEPT ![t]=Aborted]
                      /\ UNCHANGED  <<db, vis, tid, deadlocked>>

Abort(t) == /\ tstate[t] = Open
            /\ rval[t] # Busy
            /\ op' = [op EXCEPT ![t]="a"]
            /\ arg' = [arg EXCEPT ![t] = <<>>]
            /\ rval' = [rval EXCEPT ![t]=Ok]
            /\ tstate' = [tstate EXCEPT ![t]=Aborted]
            /\ UNCHANGED <<db, vis, tid, deadlocked>>

Commit(t) == /\ tstate[t] = Open
             /\ rval[t] # Busy
             /\ tstate' = [tstate EXCEPT ![t] = Committed]
             /\ op' = [op EXCEPT ![t]="c"]
             /\ arg' = [arg EXCEPT ![t] = <<>>]
             /\ rval' = [rval EXCEPT ![t]=Ok]
             /\ tstate' = [tstate EXCEPT ![t] = Committed]
             /\ UNCHANGED <<db, vis, tid, deadlocked>>

Done == \A t \in Tr: tstate[t] \in {Committed, Aborted}
v == <<op, arg, rval, db, tstate, tid, vis, deadlocked>>

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
        \/ DetectDeadlock
        \/ Termination

L == /\ WF_v(\E t \in Tr, obj \in Obj, val \in Val : 
                \/ EndRd(t, obj, val)
                \/ EndWr(t, obj, val)
                \/ AbortWr(t, obj, val))
     /\ WF_v(\E t \in Tr: \/ StartTransaction(t))
     /\ SF_v(\E t \in Tr: Commit(t) \/ Abort(t))
     /\ WF_v(DetectDeadlock)

Spec == Init /\ [][Next]_v /\ L

====