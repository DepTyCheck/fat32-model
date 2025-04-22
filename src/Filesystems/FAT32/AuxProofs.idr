module Filesystems.FAT32.AuxProofs

import Algebra.Solver.Semiring

%default total
%ambiguity_depth 5

export
0 eqPrf1 : (a, b, c, d : Nat) -> (a + b * (c + d)) + c + d = a + (1 + b) * (c + d)
eqPrf1 a b c d = solveNat [a, b, c, d] 
    ((a .+ b .* (c .+. d)) +. c +. d)
    (a .+ (1 +. b) * (c .+. d))

export
0 eqPrf2 : (a, b, c, d : Nat) -> (c + d) + (a + b * (c + d)) = a + (1 + b) * (c + d)
eqPrf2 a b c d = solveNat [a, b, c, d] 
    ((c .+. d) + (a .+ b .* (c .+. d)))
    (a .+ (1 +. b) * (c .+. d))

export
0 eqPrf3 : (a, b, c, d : Nat) -> (a + b * (c + d)) + (c + d) = a + (1 + b) * (c + d)
eqPrf3 a b c d = solveNat [a, b, c, d] 
    ((a .+ b .* (c .+. d)) + (c .+. d))
    (a .+ (1 +. b) * (c .+. d))
