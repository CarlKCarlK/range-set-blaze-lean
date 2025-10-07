import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

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
lemma before_trans {a b c : NR} (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c := by
  -- a.hi + 1 < b.lo  and  b.hi + 1 < c.lo  ⇒  a.hi + 1 < c.lo
  unfold NR.before at *
  -- a.hi + 1 < b.lo ≤ b.hi
  have h1 : a.val.hi + 1 ≤ b.val.hi := (lt_of_lt_of_le hab b.property).le
  -- b.hi ≤ b.hi + 1
  have h2 : b.val.hi ≤ b.val.hi + 1 := by
    have : (0 : Int) ≤ 1 := by decide
    calc
      b.val.hi = b.val.hi + 0 := by simp
      _ ≤ b.val.hi + 1 := add_le_add_left this _
  -- hence b.hi < c.lo
  have h3 : b.val.hi < c.val.lo := lt_of_le_of_lt h2 hbc
  -- chain: a.hi + 1 ≤ b.hi < c.lo
  exact lt_of_le_of_lt h1 h3

lemma before_glue_of_before {z a b : NR}
    (hza : z ≺ a) (hzb : z ≺ b) :
    z ≺ IntRange.NR.glue a b := by
  -- Need z.hi + 1 < min a.lo b.lo; both inequalities are available.
  unfold NR.before at *
  have hmin : z.val.hi + 1 < min a.val.lo b.val.lo := lt_min hza hzb
  simpa [IntRange.NR.glue, IntRange.mergeRange] using hmin

private def insert
  (curr : IntRange.NR)
  : (xs : List IntRange.NR) → List.Pairwise (· ≺ ·) xs →
      { ys : List IntRange.NR //
        List.Pairwise (· ≺ ·) ys ∧
        listToSet ys = curr.val.toSet ∪ listToSet xs ∧
        ∀ {z : IntRange.NR},
          (∀ y ∈ xs, z ≺ y) → z ≺ curr →
          ∀ y ∈ ys, z ≺ y }
  | [], _ =>
      ⟨[curr], by
          exact List.pairwise_singleton (R := (· ≺ ·)) (a := curr),
        by simp [listToSet],
        by
          intro z _ hzc y hy
          have hy' : y = curr := List.mem_singleton.mp hy
          simpa [hy'] using hzc⟩
  | x :: xs, hpx =>
      have hx_tail : ∀ y ∈ xs, x ≺ y := (List.pairwise_cons.1 hpx).1
      have h_tail : List.Pairwise (· ≺ ·) xs := (List.pairwise_cons.1 hpx).2
      match IntRange.NR.Rel3.classify curr x with
      | IntRange.NR.Rel3.left hcx =>
          let hcurr_tail : ∀ y ∈ xs, curr ≺ y :=
            by
              intro y hy
              exact before_trans hcx (hx_tail y hy)
          let pair : List.Pairwise (· ≺ ·) (curr :: x :: xs) :=
            List.pairwise_cons.2
              ⟨by
                  intro y hy
                  rcases List.mem_cons.1 hy with hy | hy
                  · simpa [hy] using hcx
                  · exact hcurr_tail y hy,
                hpx⟩
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ curr :: x :: xs, z ≺ y :=
            by
              intro z hzxs hzc y hy
              rcases List.mem_cons.1 hy with hy | hy
              · simpa [hy] using hzc
              · exact hzxs y hy
          ⟨curr :: x :: xs, pair, by simp [listToSet_cons], mono⟩
      | IntRange.NR.Rel3.right hxc =>
          let ⟨ys, hpair, hset, hmon⟩ := insert curr xs h_tail
          let hx_all : ∀ y ∈ ys, x ≺ y :=
            hmon
              (by
                intro y hy
                exact hx_tail y hy)
              hxc
          let pair : List.Pairwise (· ≺ ·) (x :: ys) :=
            List.pairwise_cons.2 ⟨hx_all, hpair⟩
          let setEq :
              listToSet (x :: ys) = curr.val.toSet ∪ listToSet (x :: xs) :=
            by
              have := congrArg (fun s => x.val.toSet ∪ s) hset
              simpa [listToSet_cons, Set.union_left_comm, Set.union_assoc, Set.union_comm] using this
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ x :: ys, z ≺ y :=
            by
              intro z hzxs hzc y hy
              rcases List.mem_cons.1 hy with hy | hy
              · simpa [hy] using hzxs x (by simp)
              · have hz_tail : ∀ w ∈ xs, z ≺ w := by
                  intro w hw
                  exact hzxs w (List.mem_cons_of_mem _ hw)
                exact hmon hz_tail hzc y hy
          ⟨x :: ys, pair, setEq, mono⟩
      | IntRange.NR.Rel3.overlap h₁ h₂ =>
          let glued := IntRange.NR.glue curr x
          have gl_sets : glued.val.toSet = curr.val.toSet ∪ x.val.toSet :=
            IntRange.NR.glue_sets curr x h₁ h₂
          let ⟨ys, hpair, hset, hmon⟩ := insert glued xs h_tail
          let setEq :
              listToSet ys = curr.val.toSet ∪ listToSet (x :: xs) :=
            by
              simpa [listToSet_cons, gl_sets, Set.union_assoc,
                Set.union_left_comm, Set.union_comm] using hset
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ ys, z ≺ y :=
            by
              intro z hzxs hzc y hy
              have hz_tail : ∀ w ∈ xs, z ≺ w := by
                intro w hw
                exact hzxs w (List.mem_cons_of_mem _ hw)
              have hzx : z ≺ x := hzxs x (by simp)
              have hzg : z ≺ glued := before_glue_of_before hzc hzx
              exact hmon hz_tail hzg y hy
          ⟨ys, hpair, setEq, mono⟩

open Classical

/-- The output list of `insert curr xs ok`. -/
 def insertYs (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs) : List IntRange.NR :=
  (insert curr xs ok).1

/-- Pairwise invariant re-established by `insert`. -/
private lemma insert_pairwise_aux
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    List.Pairwise (· ≺ ·) (insert curr xs ok).1 := by
  rcases insert curr xs ok with ⟨ys, hpair, hset, hmon⟩
  simpa using hpair

/-- Pairwise invariant re-established by `insert`. -/
lemma insert_pairwise
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    List.Pairwise (· ≺ ·) (insertYs curr xs ok) := by
  simpa [insertYs] using insert_pairwise_aux curr xs ok

private lemma insert_sets_aux
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    listToSet (insert curr xs ok).1 =
      curr.val.toSet ∪ listToSet xs := by
  rcases insert curr xs ok with ⟨ys, hpair, hset, hmon⟩
  simpa using hset

/-- Set equality spec for `insert`. -/
lemma insert_sets
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    listToSet (insertYs curr xs ok) =
      curr.val.toSet ∪ listToSet xs := by
  simpa [insertYs] using insert_sets_aux curr xs ok

private lemma insert_monotone_aux
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs)
    {z : IntRange.NR}
    (hz_tail : ∀ y ∈ xs, z ≺ y)
    (hzc : z ≺ curr) :
    ∀ y ∈ (insert curr xs ok).1, z ≺ y := by
  rcases insert curr xs ok with ⟨ys, hpair, hset, hmon⟩
  simpa using hmon hz_tail hzc

/-- Monotonicity witness exposed as a lemma:
if `z` was before every element of the old tail and before `curr`,
then `z` is before every element of the new list. -/
lemma insert_monotone
    (curr : IntRange.NR) (xs : List IntRange.NR)
    (ok : List.Pairwise (· ≺ ·) xs)
    {z : IntRange.NR}
    (hz_tail : ∀ y ∈ xs, z ≺ y)
    (hzc : z ≺ curr) :
    ∀ y ∈ insertYs curr xs ok, z ≺ y := by
  simpa [insertYs] using insert_monotone_aux curr xs ok hz_tail hzc

/-- Add a (possibly empty) range to a `RangeSetBlaze`. -/
def internalAddA (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hr : r.nonempty then
    let curr : IntRange.NR := ⟨r, hr⟩
    let ⟨ys, hpair, _, _⟩ := insert curr s.ranges s.ok
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
    rcases res with ⟨ys, hpair, hset, hmon⟩
    have hNotEmpty : ¬ r.empty := by
      simpa [IntRange.nonempty_iff_not_empty] using hr
    have hstruct : internalAddA s r = ⟨ys, hpair⟩ := by
      simp [internalAddA, hNotEmpty, hInsert.symm]
    have hcurr : (⟨r, hr⟩ : IntRange.NR).val.toSet = r.toSet := rfl
    have htoSet : (internalAddA s r).toSet = listToSet ys := by
      simp [hstruct, toSet_eq_listToSet]
    have hsToSet : s.toSet = listToSet s.ranges := by
      simp [toSet_eq_listToSet]
    calc
      (internalAddA s r).toSet
          = listToSet ys := htoSet
      _ = r.toSet ∪ listToSet s.ranges := by
          simpa [hcurr] using hset
      _ = s.toSet ∪ r.toSet := by
          rw [hsToSet.symm, Set.union_comm]
  ·
    -- Empty range case: its set is ∅, and `internalAddA` returns `s`.
    have hlt : r.hi < r.lo := by
      -- hr = ¬(r.lo ≤ r.hi)
      simpa [IntRange.nonempty, not_le] using hr
    have hEmpty : r.toSet = (∅ : Set Int) := by
      simpa using IntRange.toSet_eq_empty_of_hi_lt_lo hlt
    have hempty : r.empty := hlt
    simp [internalAddA, hempty, hEmpty, Set.union_comm]

end RangeSetBlaze
