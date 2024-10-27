---- MODULE TransitiveClosure ----
(******************************************************************************************************************)
(* Source: https://github.com/tlaplus/Examples/blob/master/specifications/TransitiveClosure/TransitiveClosure.tla *)
(******************************************************************************************************************)

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

R ** T == LET SR == Support(R)
              ST == Support(T)
          IN  {<<r, t>> \in SR \X ST : 
                \E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}

RECURSIVE TC(_)
TC(R) == LET RR == R ** R
          IN  IF RR \subseteq R THEN R ELSE TC(R \cup RR)


====