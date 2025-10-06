import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise

/-- An inclusive range of integers with fields `lo` and `hi`. -/
structure IntRange where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace IntRange

/-- A range is empty when hi < lo. -/
def empty (r : IntRange) : Prop := r.hi < r.lo

/-- A range is nonempty when lo ≤ hi. -/
def nonempty (r : IntRange) : Prop := r.lo ≤ r.hi

/-- Nonempty is equivalent to not empty. -/
@[simp]
theorem nonempty_iff_not_empty (r : IntRange) : r.nonempty ↔ ¬ r.empty := by
  simp [nonempty, empty, not_lt]

/-- View a range as a set of integers using the closed interval. -/
def toSet (r : IntRange) : Set Int := Set.Icc r.lo r.hi

/-- The set view is empty iff hi < lo. -/
@[simp]
lemma toSet_eq_empty_iff (r : IntRange) :
  r.toSet = (∅ : Set Int) ↔ r.hi < r.lo := by
  simp [toSet, Set.Icc_eq_empty_iff, not_le]

lemma toSet_eq_empty_of_hi_lt_lo {r : IntRange} (h : r.hi < r.lo) :
  r.toSet = ∅ := (toSet_eq_empty_iff r).mpr h

/-- Membership in toSet is equivalent to being in the closed interval. -/
@[simp]
lemma mem_toSet_iff (r : IntRange) (x : Int) :
  x ∈ r.toSet ↔ r.lo ≤ x ∧ x ≤ r.hi := by
  simp [toSet]

/-- A nonempty range has a nonempty set representation. -/
@[simp]
lemma toSet_nonempty_of_le {r : IntRange} (h : r.lo ≤ r.hi) :
  r.toSet.Nonempty := by
  simp [toSet, Set.nonempty_Icc, h]

/-- The set representation is nonempty iff the range is nonempty. -/
@[simp]
lemma nonempty_toSet_iff (r : IntRange) : r.toSet.Nonempty ↔ r.nonempty := by
  simp [toSet, Set.nonempty_Icc, nonempty]

instance : DecidablePred empty := fun r => inferInstanceAs (Decidable (r.hi < r.lo))
instance : DecidablePred nonempty := fun r => inferInstanceAs (Decidable (r.lo ≤ r.hi))

/-- Convenient abbreviation for nonempty ranges as a subtype. -/
abbrev NR := { r : IntRange // r.nonempty }

namespace NR

/-- One nonempty range comes before another with a gap if the first ends before the second starts. -/
def before (a b : NR) : Prop := a.val.hi + 1 < b.val.lo

scoped infixl:50 " ≺ " => NR.before

instance : DecidableRel before := fun a b => inferInstanceAs (Decidable (a.val.hi + 1 < b.val.lo))

end NR

/-- Coercion from IntRange to Set Int. -/
instance : Coe IntRange (Set Int) where coe := toSet

end IntRange

open IntRange (NR)
open scoped IntRange.NR

/-- A list of nonempty ranges that are sorted and pairwise disjoint with gaps. -/
structure RangeSetBlaze where
  ranges : List NR
  ok : List.Pairwise (· ≺ ·) ranges
  deriving Repr

namespace RangeSetBlaze

/-- Convert a RangeSetBlaze to a set by taking the union of all its ranges. -/
def toSet (L : RangeSetBlaze) : Set Int :=
  L.ranges.foldr (fun r acc => r.val.toSet ∪ acc) ∅

/-- The toSet of an empty RangeSetBlaze is empty. -/
@[simp]
lemma toSet_nil (ok : List.Pairwise NR.before []) :
  toSet ⟨[], ok⟩ = ∅ := rfl

/-- The toSet of a cons is the union of the head's toSet and the tail's toSet. -/
@[simp]
lemma toSet_cons {r : NR} {rs : List NR}
    {ok : List.Pairwise NR.before (r :: rs)} :
  toSet ⟨r :: rs, ok⟩ =
    r.val.toSet ∪ toSet ⟨rs, ok.tail⟩ := rfl

end RangeSetBlaze
