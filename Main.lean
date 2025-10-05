import RangeSetBlaze.Basic

open IntRange

-- Example ranges as specified
def r1 : IntRange := ⟨101, 102⟩
def r2 : IntRange := ⟨400, 402⟩
def r3 : IntRange := ⟨404, 405⟩
def e : IntRange := ⟨10, 5⟩  -- empty range

-- Proof that e is empty
example : e.empty := by decide

-- Proof that e.toSet is the empty set
example : e.toSet = (∅ : Set Int) := by
  have : e.hi < e.lo := by decide
  simpa [IntRange.toSet] using IntRange.toSet_eq_empty_of_hi_lt_lo this

-- Alternative: simp can solve this directly
example : e.toSet = (∅ : Set Int) := by
  simp [IntRange.toSet, e]

-- Proof that r1 precedes r2
example : r1 ≺ r2 := by
  unfold IntRange.before r1 r2
  decide

-- Proof that r2 precedes r3
example : r2 ≺ r3 := by
  unfold IntRange.before r2 r3
  decide

-- Construct a valid RangeList with r1, r2, r3
def validRangeList : RangeList where
  ranges := [r1, r2, r3]
  all_nonempty := by
    intro r hr
    cases hr with
    | head => unfold IntRange.nonempty r1; decide
    | tail _ hr' =>
      cases hr' with
      | head => unfold IntRange.nonempty r2; decide
      | tail _ hr'' =>
        cases hr'' with
        | head => unfold IntRange.nonempty r3; decide
        | tail _ hr''' => cases hr'''
  pairwise_gaps := by
    simp [r1, r2, r3, IntRange.before]

-- Example of ranges that are NOT properly separated (touching, no gap)
def touchingRange1 : IntRange := ⟨1, 5⟩
def touchingRange2 : IntRange := ⟨6, 10⟩  -- touches but doesn't precede

-- This would fail the chain requirement because touchingRange1 does NOT precede touchingRange2
example : ¬(touchingRange1 ≺ touchingRange2) := by
  unfold IntRange.before touchingRange1 touchingRange2
  decide

-- Example of overlapping ranges
def overlapping1 : IntRange := ⟨1, 8⟩
def overlapping2 : IntRange := ⟨5, 12⟩

example : ¬(overlapping1 ≺ overlapping2) := by
  unfold IntRange.before overlapping1 overlapping2
  decide

def main : IO Unit := do
  IO.println "RangeList - Idiomatic Lean 4 with Mathlib"
  IO.println "=========================================="
  IO.println ""
  IO.println s!"r1 (nonempty): {repr r1}"
  IO.println s!"r2 (nonempty): {repr r2}"
  IO.println s!"r3 (nonempty): {repr r3}"
  IO.println s!"e (empty): {repr e}"
  IO.println ""
  IO.println s!"r1 ≺ r2: {decide (r1 ≺ r2)}"
  IO.println s!"r2 ≺ r3: {decide (r2 ≺ r3)}"
  IO.println ""
  IO.println s!"Valid RangeList: {repr validRangeList.ranges}"
  IO.println ""
  IO.println s!"Touching ranges (no gap): {repr touchingRange1} and {repr touchingRange2}"
  IO.println s!"touchingRange1 ≺ touchingRange2: {decide (touchingRange1 ≺ touchingRange2)}"
  IO.println ""
  IO.println s!"Overlapping ranges: {repr overlapping1} and {repr overlapping2}"
  IO.println s!"overlapping1 ≺ overlapping2: {decide (overlapping1 ≺ overlapping2)}"
  IO.println ""
  IO.println "✓ All examples demonstrate idiomatic Lean 4 with mathlib!"
