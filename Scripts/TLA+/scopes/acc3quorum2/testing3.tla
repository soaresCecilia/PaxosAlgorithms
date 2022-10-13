-------------------------------- MODULE testing3 -------------------------------
EXTENDS Paxos, TLC, FiniteSets
-----------------------------------------------------------------------------
CONSTANTS a1, a2, a3  \* acceptors
CONSTANTS v1, v2, v3      \* Values

MCAcceptor == {a1, a2, a3} \* {a1, a2, a3}
MCValue    == {v1, v2, v3} \* {v1, v2}
MCMaxBallot == 2
MCBallot == 0..MCMaxBallot
MCSymmetry == Permutations(MCAcceptor) \cup Permutations(MCValue)
MCQuorum == {{a1, a2}, {a1, a2, a3}} \* {{a1, a2, a3}, {a2,a3}}


(***************************************************************************)
(* For checking safety.                                                    *)
(***************************************************************************)
MCSafety   == [](Cardinality(V!chosen) <= 1)
=============================================================================