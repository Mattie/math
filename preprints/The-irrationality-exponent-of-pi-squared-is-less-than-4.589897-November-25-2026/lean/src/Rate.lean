import Lean

/-!
# A rational certificate for the saving from six prime intervals

`intervalLower` sums the first twelve periods exactly and bounds the rest
through period one million using twelve rising-factorial terms. `FiniteRate`
proves the telescoping inequality. `RateBridge.lowerRate_le` applies it to
these six intervals, turning the arithmetic check here into a lower bound
for their combined contribution.
-/

namespace PrimeNumerator.Rate

def rising (x : Rat) : Nat → Rat
  | 0 => 1
  | j+1 => rising x j * (x + j)

def intervalLower (a b : Rat) : Rat :=
  ((List.range 12).map fun i =>
    let t : Rat := (i+1 : Nat)
    1/(t+a) - 1/(t+b)).sum +
  ((List.range 12).map fun i =>
    let j := i+1
    ((rising (1-a) j - rising (1-b) j) / j) *
      (1/rising 14 j - 1/rising 1000002 j)).sum

def lowerRate : Rat :=
  intervalLower (1/8) (2/13) + intervalLower (2/9) (3/13) +
  intervalLower (3/10) (4/13) + intervalLower (3/8) (5/13) +
  intervalLower (4/9) (6/13) + intervalLower (8/9) (12/13)

def gap : Rat := 62636575 / 1000000
def height : Rat := 38168733 / 1000000 +
  143297092558247390159 / 13110552000000000000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem rounded_measure :
    gap / (gap - height + 10868226 / 100000000) < 4589897 / 1000000 := by
  decide +kernel

theorem twelve_term_certificate : (10868226 : Rat) / 100000000 < lowerRate := by
  decide +kernel

#print axioms rounded_measure
#print axioms twelve_term_certificate

end PrimeNumerator.Rate
