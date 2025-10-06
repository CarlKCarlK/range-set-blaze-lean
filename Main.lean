import RangeSetBlaze.Basic

open IntRange
open IntRange.NR
open RangeSetBlaze

/-! Helpers to build small examples. -/

def ir (lo hi : Int) : IntRange :=
  { lo := lo, hi := hi }

def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨ir lo hi, h⟩

def baseSet : RangeSetBlaze :=
  let r1 : NR := mkNR 0 2 (by decide)
  let r2 : NR := mkNR 5 7 (by decide)
  ⟨[r1, r2],
    by
      refine List.pairwise_cons.2 ?_
      refine And.intro ?_ ?_
      · intro y hy
        rcases hy with rfl | hy'
        · change r1.val.hi + 1 < r2.val.lo
          decide
        · cases hy'
      · simpa using List.pairwise_singleton (r := (· ≺ ·)) (a := r2)⟩

def addTouch : RangeSetBlaze := internalAddA baseSet (ir 3 4)
def addOverlap : RangeSetBlaze := internalAddA baseSet (ir 2 6)
def addLeft : RangeSetBlaze := internalAddA baseSet (ir (-5) (-3))
def addEmpty : RangeSetBlaze := internalAddA baseSet (ir 10 5)

def samplePoints : List Int :=
  [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

#eval samplePoints.filter (fun i => decide (i ∈ baseSet.toSet))
#eval samplePoints.filter (fun i => decide (i ∈ addTouch.toSet))
#eval samplePoints.filter (fun i => decide (i ∈ addOverlap.toSet))
#eval samplePoints.filter (fun i => decide (i ∈ addLeft.toSet))
#eval samplePoints.filter (fun i => decide (i ∈ addEmpty.toSet))

example : 4 ∈ addTouch.toSet := by decide
example : -4 ∈ addLeft.toSet := by decide
