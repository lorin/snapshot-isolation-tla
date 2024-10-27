---- MODULE MCSequential ----
EXTENDS Sequential, Sequences, Naturals, TLC

VARIABLES h

CONSTANTS Hmax

InitH == /\ Init
         /\ h = <<>>

ReadH(obj, val) == /\ Read(obj, val)
                   /\ h' = Append(h, [op|->"r", obj|->obj, val|->val])

WriteH(obj, val) == /\ Write(obj, val)
                    /\ h' = Append(h, [op|->"w", obj|->obj, val|->val])


NextH == \/ \E obj \in Obj, val \in Val: ReadH(obj, val) \/ WriteH(obj, val)

vh == <<op, arg, rval, env, ff, h>>
SpecH == InitH /\ [][NextH]_vh

(******************************)
(* The set of writes to *obj* *)
(******************************)
Wr(obj) == LET evt == {h[i] : i \in DOMAIN h} IN 
    {e \in evt : e.op="w" /\ e.obj=obj}

(**************************************)
(* Most recent value written to *obj* *)
(**************************************)
MRW(obj) == LET i == CHOOSE i \in DOMAIN h : 
    /\ h[i].op = "w" 
    /\ h[i].obj = obj
    /\ ~ \E j \in DOMAIN h : /\ h[j].op = "w"
                             /\ h[j].obj = obj
                             /\ j > i IN
    h[i].val

(********************************************************************************************)
(* If an object was previously written, the read should correspond to the most recent write *)
(********************************************************************************************)
ReadLastWrite == op = "r" => 
        LET obj == arg
            val == rval IN 
         Wr(obj) # {} => MRW(obj) = val

(****************************************************************************)
(* Successive reads without intervening writes should return the same value *)
(****************************************************************************)
SuccessiveReads == LET obj == arg 
                       val == rval
                       IsRd(k, o) == h[k].op = "r" /\ h[k].obj = o
                       IsWr(k, o) == h[k].op = "w" /\ h[k].obj = o 
                       NoWrRd(i, o) ==  IsRd(i, o) /\ ~ \E j \in i+1..Len(h)-1 : IsWr(j, o) 
                       j == CHOOSE j \in 1..Len(h)-1 : NoWrRd(j, obj) IN
                    (op = "r" /\ \E i \in 1..Len(h)-1 : NoWrRd(i, obj)) => rval = h[j].val


Symmetry == Permutations(Obj) \cup Permutations(Val)

MaxHistory == Len(h) <= Hmax

====