import RangeSetBlaze.Basic

open IntRange
open IntRange.NR
open RangeSetBlaze
open scoped IntRange.NR   -- bring ≺ into scope

/-! Helpers to build small examples. -/

def ir (lo hi : Int) : IntRange :=
  { lo := lo, hi := hi }

def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨ir lo hi, h⟩

open Classical

def baseSet : RangeSetBlaze :=
  let r1 : NR := mkNR 0 2 (by decide)
  let r2 : NR := mkNR 5 7 (by decide)
  ⟨[r1, r2],
    by
      refine List.pairwise_cons.2 ?_
      refine And.intro ?_ ?_
      · intro y hy
        have hy' : y = r2 := by
          simpa using hy
        subst hy'
        change r1.val.hi + 1 < r2.val.lo
        decide
      · exact List.pairwise_singleton (R := (· ≺ ·)) (a := r2)⟩

def addTouch   : RangeSetBlaze := internalAddA baseSet (ir 3 4)
def addOverlap : RangeSetBlaze := internalAddA baseSet (ir 2 6)
def addLeft    : RangeSetBlaze := internalAddA baseSet (ir (-5) (-3))
def addEmpty   : RangeSetBlaze := internalAddA baseSet (ir 10 5)

namespace RangeSetBlaze

/-- Boolean membership check for demo purposes. -/
def contains (s : RangeSetBlaze) (x : Int) : Bool :=
  s.ranges.any (fun r => decide (r.val.lo ≤ x ∧ x ≤ r.val.hi))

end RangeSetBlaze

open RangeSetBlaze (contains)

def samplePoints : List Int :=
  [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

#eval! samplePoints.filter (fun i => contains baseSet i)
#eval! samplePoints.filter (fun i => contains addTouch i)
#eval! samplePoints.filter (fun i => contains addOverlap i)
#eval! samplePoints.filter (fun i => contains addLeft i)
#eval! samplePoints.filter (fun i => contains addEmpty i)

example : 4 ∈ addTouch.toSet := by
  have hEq := RangeSetBlaze.internalAddA_toSet baseSet (ir 3 4)
  have hUnion :
      4 ∈ baseSet.toSet ∪ (ir 3 4).toSet := by
    have : 4 ∈ baseSet.toSet ∨ 4 ∈ (ir 3 4).toSet :=
      Or.inr (by simp [ir, IntRange.mem_toSet_iff])
    simpa [Set.mem_union] using this
  have hGoal :
      4 ∈ (internalAddA baseSet (ir 3 4)).toSet :=
    hEq.symm ▸ hUnion
  simpa [addTouch] using hGoal

example : -4 ∈ addLeft.toSet := by
  have hEq := RangeSetBlaze.internalAddA_toSet baseSet (ir (-5) (-3))
  have hUnion :
      -4 ∈ baseSet.toSet ∪ (ir (-5) (-3)).toSet := by
    have :
        -4 ∈ baseSet.toSet ∨ -4 ∈ (ir (-5) (-3)).toSet :=
      Or.inr (by simp [ir, IntRange.mem_toSet_iff])
    simpa [Set.mem_union] using this
  have hGoal :
      -4 ∈ (internalAddA baseSet (ir (-5) (-3))).toSet :=
    hEq.symm ▸ hUnion
  simpa [addLeft] using hGoal

def demoScenarios :
    List (String × RangeSetBlaze) :=
  [("baseSet", baseSet),
   ("addTouch", addTouch),
   ("addOverlap", addOverlap),
   ("addLeft", addLeft),
   ("addEmpty", addEmpty)]

def main : IO Unit := do
  IO.println "RangeSetBlaze sample membership:"
  for (label, rs) in demoScenarios do
    let hits := samplePoints.filter (fun i => contains rs i)
    IO.println s!"  {label}: {hits}"
