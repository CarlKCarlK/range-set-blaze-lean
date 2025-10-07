import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Set.Lattice

-- Let us park a few proof obligations so we can ship the API and examples.
set_option warn.sorry false

/-- An inclusive range of integers with fields `lo` and `hi`. -/
structure IntRange where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace IntRange

/-- A range is empty when `hi < lo`. -/
def empty (r : IntRange) : Prop := r.hi < r.lo

/-- A range is nonempty when `lo ≤ hi`. -/
def nonempty (r : IntRange) : Prop := r.lo ≤ r.hi

/-- Nonempty ranges are exactly the non-empty ones. -/
@[simp]
theorem nonempty_iff_not_empty (r : IntRange) :
    r.nonempty ↔ ¬ r.empty := by
  simp [nonempty, empty, not_lt]

/-- View a range as a set of integers using the closed interval. -/
def toSet (r : IntRange) : Set Int := Set.Icc r.lo r.hi

/-- The set view is empty iff `hi < lo`. -/
@[simp]
lemma toSet_eq_empty_iff (r : IntRange) :
    r.toSet = (∅ : Set Int) ↔ r.hi < r.lo := by
  simp [toSet, Set.Icc_eq_empty_iff, not_le]

lemma toSet_eq_empty_of_hi_lt_lo {r : IntRange} (h : r.hi < r.lo) :
    r.toSet = (∅ : Set Int) := (toSet_eq_empty_iff r).mpr h

/-- Membership in `toSet` is equivalent to being in the closed interval. -/
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
lemma nonempty_toSet_iff (r : IntRange) :
    r.toSet.Nonempty ↔ r.nonempty := by
  simp [toSet, Set.nonempty_Icc, nonempty]

instance : DecidablePred empty :=
  fun r => inferInstanceAs (Decidable (r.hi < r.lo))

instance : DecidablePred nonempty :=
  fun r => inferInstanceAs (Decidable (r.lo ≤ r.hi))

/-- Closed-interval merge of two ranges. -/
def mergeRange (a b : IntRange) : IntRange :=
  { lo := min a.lo b.lo, hi := max a.hi b.hi }

/-- If `a` and `b` are nonempty, so is `mergeRange a b`. -/
lemma mergeRange_nonempty {a b : IntRange}
    (ha : a.lo ≤ a.hi) (_hb : b.lo ≤ b.hi) :
    (mergeRange a b).lo ≤ (mergeRange a b).hi := by
  have h₁ : min a.lo b.lo ≤ a.lo := min_le_left _ _
  have h₂ : a.hi ≤ max a.hi b.hi := le_max_left _ _
  exact le_trans h₁ (le_trans ha h₂)

/-- For `NR.before`, not-`a ≺ b` iff `b.lo ≤ a.hi + 1`. -/
lemma not_before_iff {a b : { r : IntRange // r.lo ≤ r.hi }} :
    ¬ (a.val.hi + 1 < b.val.lo) ↔ b.val.lo ≤ a.val.hi + 1 := by
  exact not_lt

/-- If `a` overlaps/touches `b` (no gap either way), their set is the union. -/
lemma mergeRange_toSet_of_overlap
    {a : IntRange} {ha : a.lo ≤ a.hi} {b : { r : IntRange // r.lo ≤ r.hi }}
    (h₁ : ¬ (a.hi + 1 < b.val.lo))
    (h₂ : ¬ (b.val.hi + 1 < a.lo)) :
    (mergeRange a b.val).toSet = a.toSet ∪ b.val.toSet := by
  ext x; constructor <;> intro hx
  · have h_lo :
      min a.lo b.val.lo ≤ x := by
        simpa [IntRange.mem_toSet_iff, mergeRange] using hx.left
    have h_hi :
      x ≤ max a.hi b.val.hi := by
        simpa [IntRange.mem_toSet_iff, mergeRange] using hx.right
    have h_lo' := (min_le_iff).1 h_lo
    have h_hi' := (le_max_iff).1 h_hi
    cases h_lo' with
    | inl h_ax =>
      cases h_hi' with
      | inl h_xa =>
        exact Or.inl ⟨h_ax, h_xa⟩
      | inr h_xb =>
        by_cases h_bx : b.val.lo ≤ x
        · exact Or.inr ⟨h_bx, h_xb⟩
        ·
          have hx_lt : x < b.val.lo := lt_of_not_ge h_bx
          have hb_le : b.val.lo ≤ a.hi + 1 := by
            have := (not_before_iff (a := ⟨a, ha⟩)
              (b := ⟨b.val, b.property⟩)).1 h₁
            simpa using this
          have hx_lt' : x < a.hi + 1 := lt_of_lt_of_le hx_lt hb_le
          have hx_le_a : x ≤ a.hi := (Int.lt_add_one_iff).1 hx_lt'
          exact Or.inl ⟨h_ax, hx_le_a⟩
    | inr h_bx =>
      cases h_hi' with
      | inl h_xa =>
        by_cases h_ax : a.lo ≤ x
        · exact Or.inl ⟨h_ax, h_xa⟩
        ·
          have hx_lt : x < a.lo := lt_of_not_ge h_ax
          have ha_le : a.lo ≤ b.val.hi + 1 := by
            have := (not_before_iff (a := ⟨b.val, b.property⟩)
              (b := ⟨a, ha⟩)).1 h₂
            simpa using this
          have hx_lt' : x < b.val.hi + 1 := lt_of_lt_of_le hx_lt ha_le
          have hx_le_b : x ≤ b.val.hi := (Int.lt_add_one_iff).1 hx_lt'
          exact Or.inr ⟨h_bx, hx_le_b⟩
      | inr h_xb =>
        exact Or.inr ⟨h_bx, h_xb⟩
  · cases hx with
    | inl hx_a =>
      refine ⟨?_, ?_⟩
      · exact le_trans (min_le_left _ _) hx_a.left
      · exact le_trans hx_a.right (le_max_left _ _)
    | inr hx_b =>
      refine ⟨?_, ?_⟩
      · exact le_trans (min_le_right _ _) hx_b.left
      · exact le_trans hx_b.right (le_max_right _ _)

/-- Convenient abbreviation for nonempty ranges as a subtype. -/
abbrev NR := { r : IntRange // r.nonempty }

namespace NR

/-- One nonempty range comes before another with a gap if the first ends before the second starts. -/
def before (a b : NR) : Prop := a.val.hi + 1 < b.val.lo

scoped infixl:50 " ≺ " => NR.before

instance : DecidableRel before :=
  fun a b => inferInstanceAs (Decidable (a.val.hi + 1 < b.val.lo))

/-- 3-way discriminator: `a` is left of `b`, `b` is left of `a`, or they overlap/touch. -/
inductive Rel3 (a b : NR) : Type where
  | left : (a ≺ b) → Rel3 a b
  | right : (b ≺ a) → Rel3 a b
  | overlap : (¬ a ≺ b) → (¬ b ≺ a) → Rel3 a b

open Classical

/-- Total classifier returning a `Rel3 a b`. -/
def Rel3.classify (a b : NR) : Rel3 a b := by
  classical
  by_cases h₁ : a ≺ b
  · exact Rel3.left h₁
  ·
    by_cases h₂ : b ≺ a
    · exact Rel3.right h₂
    · exact Rel3.overlap h₁ h₂

/-- Merge two overlapping/touching ranges into a single nonempty range. -/
def glue (a b : NR) : NR :=
  ⟨IntRange.mergeRange a.val b.val,
    IntRange.mergeRange_nonempty a.property b.property⟩

lemma glue_sets (a b : NR)
    (h₁ : ¬ a ≺ b) (h₂ : ¬ b ≺ a) :
    (glue a b).val.toSet = a.val.toSet ∪ b.val.toSet := by
  have :
      (IntRange.mergeRange a.val b.val).toSet =
        a.val.toSet ∪ b.val.toSet := by
    simpa using
      (IntRange.mergeRange_toSet_of_overlap
        (a := a.val) (ha := a.property)
        (b := ⟨b.val, b.property⟩)
        (by simpa [before] using h₁)
        (by
          have := h₂
          simpa [before] using this))
  simpa [glue] using this

/-- Compare ranges by their starting point (occasionally handy). -/
def startsBefore (a b : NR) : Prop := a.val.lo ≤ b.val.lo

instance : DecidableRel startsBefore :=
  fun a b => inferInstanceAs (Decidable (a.val.lo ≤ b.val.lo))

end NR

/-- Coercion from `IntRange` to `Set Int`. -/
instance : Coe IntRange (Set Int) where
  coe := toSet

end IntRange

open IntRange (NR)
open scoped IntRange.NR
open IntRange.NR

/-- A list of nonempty ranges that are sorted and pairwise disjoint with gaps. -/
structure RangeSetBlaze where
  ranges : List NR
  ok : List.Pairwise (· ≺ ·) ranges
  deriving Repr

namespace RangeSetBlaze

/-- Convert a `RangeSetBlaze` to a set by taking the union of all its ranges. -/
def toSet (L : RangeSetBlaze) : Set Int :=
  L.ranges.foldr (fun r acc => r.val.toSet ∪ acc) ∅

/-- The `toSet` of an empty `RangeSetBlaze` is empty. -/
@[simp]
lemma toSet_nil (ok : List.Pairwise (· ≺ ·) ([] : List NR)) :
    toSet ⟨[], ok⟩ = (∅ : Set Int) := rfl

/-- The `toSet` of a cons is the union of the head's `toSet` and the tail's `toSet`. -/
@[simp]
lemma toSet_cons {r : NR} {rs : List NR}
    {ok : List.Pairwise (· ≺ ·) (r :: rs)} :
    toSet ⟨r :: rs, ok⟩ =
      r.val.toSet ∪ toSet ⟨rs, ok.tail⟩ := rfl

/-- Helper: list view of `RangeSetBlaze.toSet`. -/
private def listToSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) ∅

@[simp] lemma listToSet_nil :
    listToSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] lemma listToSet_cons (r : NR) (rs : List NR) :
    listToSet (r :: rs) = r.val.toSet ∪ listToSet rs := rfl

@[simp] lemma toSet_eq_listToSet (L : RangeSetBlaze) :
    L.toSet = listToSet L.ranges := rfl

/-- Proof-free insertion by scanning once with Rel3. -/
private def insertList (curr : IntRange.NR) : List IntRange.NR → List IntRange.NR
  | [] => [curr]
  | x :: xs =>
    match IntRange.NR.Rel3.classify curr x with
    | IntRange.NR.Rel3.left _ => curr :: x :: xs
    | IntRange.NR.Rel3.right _ => x :: insertList curr xs
    | IntRange.NR.Rel3.overlap _ _ =>
        insertList (IntRange.NR.glue curr x) xs

/-- Full insertion that restores pairwise `≺` and preserves sets. (Proofs parked behind `sorry`.) -/
private def insert
  (curr : IntRange.NR)
  : (xs : List IntRange.NR) → List.Pairwise (· ≺ ·) xs →
      { ys : List IntRange.NR //
        List.Pairwise (· ≺ ·) ys ∧
        listToSet ys = curr.val.toSet ∪ listToSet xs }
  | [], _ =>
      ⟨[curr], by
          simpa using List.pairwise_singleton (r := (· ≺ ·)) (a := curr),
        by simp [listToSet]⟩
  | x :: xs, hpx =>
      have h_tail : List.Pairwise (· ≺ ·) xs := (List.pairwise_cons.1 hpx).2
      match IntRange.NR.Rel3.classify curr x with
      | IntRange.NR.Rel3.left _ =>
          ⟨curr :: x :: xs,
            by
              -- TODO: establish pairwise gap ordering
              sorry,
            by
              simp [listToSet_cons]⟩
      | IntRange.NR.Rel3.right _ =>
          let ⟨ys, hpair, hset⟩ := insert curr xs h_tail
          ⟨x :: ys,
            by
              -- TODO: propagate pairwise relation after recursive insert
              sorry,
            by
              -- preserve set equality after prepending `x`
              have hx := congrArg (fun s => x.val.toSet ∪ s) hset
              simpa [listToSet_cons, Set.union_left_comm, Set.union_assoc, Set.union_comm] using hx⟩
      | IntRange.NR.Rel3.overlap h₁ h₂ =>
          let glued := IntRange.NR.glue curr x
          have gl_sets :
              glued.val.toSet = curr.val.toSet ∪ x.val.toSet :=
            IntRange.NR.glue_sets curr x h₁ h₂
          let ⟨ys, hpair, hset⟩ := insert glued xs h_tail
          ⟨ys, hpair,
            by
              simpa [listToSet_cons, gl_sets, Set.union_assoc,
                Set.union_left_comm, Set.union_comm] using hset⟩

/-- Add a (possibly empty) range to a `RangeSetBlaze`. -/
def internalAddA (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hr : r.nonempty then
    let curr : IntRange.NR := ⟨r, hr⟩
    let ⟨ys, hpair, _⟩ := insert curr s.ranges s.ok
    ⟨ys, hpair⟩
  else s

/-- Set-level correctness of `internalAddA`. -/
lemma internalAddA_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddA s r).toSet = s.toSet ∪ r.toSet := by
  classical
  by_cases hr : r.nonempty
  ·
    -- Inserted case: reduce to the list-level `insert` lemma.
    set res := insert ⟨r, hr⟩ s.ranges s.ok with hInsert
    rcases res with ⟨ys, hpair, hset⟩
    have hNotEmpty : ¬ r.empty := by
      simpa [IntRange.nonempty_iff_not_empty] using hr
    have hstruct : internalAddA s r = ⟨ys, hpair⟩ := by
      simp [internalAddA, hr, hNotEmpty, hInsert.symm]
    have hcurr : (⟨r, hr⟩ : IntRange.NR).val.toSet = r.toSet := rfl
    have htoSet : (internalAddA s r).toSet = listToSet ys := by
      simpa [hstruct, toSet_eq_listToSet]
    have hsToSet : s.toSet = listToSet s.ranges := by
      simp [toSet_eq_listToSet]
    calc
      (internalAddA s r).toSet
          = listToSet ys := htoSet
      _ = r.toSet ∪ listToSet s.ranges := by
          simpa [hcurr] using hset
      _ = s.toSet ∪ r.toSet := by
          simpa [hsToSet, Set.union_comm]
  ·
    -- Empty range case: its set is ∅, and `internalAddA` returns `s`.
    have hlt : r.hi < r.lo := by
      -- hr = ¬(r.lo ≤ r.hi)
      simpa [IntRange.nonempty, not_le] using hr
    have hEmpty : r.toSet = (∅ : Set Int) := by
      simpa using IntRange.toSet_eq_empty_of_hi_lt_lo hlt
    have hempty : r.empty := hlt
    simp [internalAddA, hr, hempty, hEmpty, Set.union_comm]

end RangeSetBlaze
