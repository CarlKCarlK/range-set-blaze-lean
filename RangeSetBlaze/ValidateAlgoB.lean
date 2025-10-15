import RangeSetBlaze
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoB

namespace RangeSetBlaze

open IntRange
open scoped IntRange.NR

-- Core spec check (re-exports the simp lemma ensures Algo B meets the spec)
example (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd s r).toSet = s.toSet ∪ r.toSet := by
  simpa using internalAdd_toSet s r

def rA : IntRange := ⟨0, 2⟩
def rB : IntRange := ⟨3, 5⟩     -- touches rA
def rC : IntRange := ⟨10, 12⟩   -- separate

def S0 : RangeSetBlaze :=
  let nrA : NR := ⟨rA, by decide⟩
  ⟨[nrA], by
    simpa using
      List.pairwise_singleton (R := (· ≺ ·)) (a := nrA)⟩

-- After inserting a touching range, union spec holds.
example : (internalAdd S0 rB).toSet = S0.toSet ∪ rB.toSet := by
  simpa using internalAdd_toSet S0 rB

-- After inserting a disjoint range, union spec still holds.
example : (internalAdd S0 rC).toSet = S0.toSet ∪ rC.toSet := by
  simpa using internalAdd_toSet S0 rC

end RangeSetBlaze
