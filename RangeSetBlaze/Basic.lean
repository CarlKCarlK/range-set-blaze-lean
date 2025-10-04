import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

/-- An inclusive range of integers with fields `lo` and `hi`.
    The range is empty when `hi < lo`. -/
structure IntRange where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace IntRange

/-- View a range as a set of integers. -/
def toSet (r : IntRange) : Set Int :=
  if r.hi < r.lo then ∅ else {x : Int | r.lo ≤ x ∧ x ≤ r.hi}

/-- A range is empty when hi < lo. -/
def isEmpty (r : IntRange) : Bool :=
  r.hi < r.lo

/-- Lemma: The set view is empty when hi < lo. -/
lemma toSet_empty_of_hi_lt_lo {r : IntRange} (h : r.hi < r.lo) : r.toSet = ∅ := by
  unfold toSet
  simp [h]

/-- Two ranges are disjoint (≺) if one comes strictly before the other with at least a one-integer gap.
    This is the opposite of touching or overlapping. -/
def disjoint (r1 r2 : IntRange) : Prop :=
  r1.hi + 1 < r2.lo

instance (r1 r2 : IntRange) : Decidable (disjoint r1 r2) :=
  inferInstanceAs (Decidable (r1.hi + 1 < r2.lo))

scoped infixl:50 " ≺ " => IntRange.disjoint

/-- Check if a range is non-empty. -/
def isNonEmpty (r : IntRange) : Bool :=
  r.lo ≤ r.hi

end IntRange

/-- A list of non-empty ranges that are sorted and disjoint. -/
structure RangeSetBlaze where
  ranges : List IntRange
  sorted_disjoint : ∀ i j (hi : i < ranges.length) (hj : j < ranges.length),
    i < j → IntRange.disjoint (ranges.get ⟨i, hi⟩) (ranges.get ⟨j, hj⟩)
  non_empty : ∀ i (h : i < ranges.length), (ranges.get ⟨i, h⟩).isNonEmpty

namespace RangeSetBlaze

/-- Convert a RangeSetBlaze to a set by taking the union of all its ranges. -/
def toSet (rsb : RangeSetBlaze) : Set Int :=
  rsb.ranges.foldl (fun acc r => acc ∪ r.toSet) ∅

/-- Helper function to check if two ranges are disjoint. -/
def areDisjoint (r1 r2 : IntRange) : Bool :=
  r1.hi + 1 < r2.lo

/-- Helper function to check if a list of ranges is sorted and disjoint. -/
def checkSortedDisjoint (ranges : List IntRange) : Bool :=
  let rec check (i : Nat) : Bool :=
    if h : i + 1 < ranges.length then
      let r1 := ranges.get ⟨i, by omega⟩
      let r2 := ranges.get ⟨i + 1, h⟩
      if areDisjoint r1 r2 then
        check (i + 1)
      else
        false
    else
      true
  check 0

/-- Helper function to check if all ranges are non-empty. -/
def checkNonEmpty (ranges : List IntRange) : Bool :=
  ranges.all (fun r => r.isNonEmpty)

end RangeSetBlaze

def hello := "world"
