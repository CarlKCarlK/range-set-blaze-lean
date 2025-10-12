import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR
open Classical

/-- Strictly before the current range (with a gap). -/
def isBefore (curr : NR) (x : NR) : Prop :=
  x ≺ curr

/-- Strictly after the current range (with a gap). -/
def isAfter (curr : NR) (x : NR) : Prop :=
  curr ≺ x

/-- Touching or overlapping the current range. -/
def isTouch (curr : NR) (x : NR) : Prop :=
  ¬ x ≺ curr ∧ ¬ curr ≺ x

instance (curr : NR) : DecidablePred (isBefore curr) :=
  fun x => inferInstanceAs (Decidable (x ≺ curr))

instance (curr : NR) : DecidablePred (isAfter curr) :=
  fun x => inferInstanceAs (Decidable (curr ≺ x))

instance (curr : NR) : DecidablePred (isTouch curr) :=
  fun x => inferInstanceAs (Decidable (¬ x ≺ curr ∧ ¬ curr ≺ x))

structure SplitWitness (curr : NR) (xs : List NR) where
  before : List NR
  touching : List NR
  after : List NR
  order : xs = before ++ touching ++ after
  before_ok : ∀ {b}, b ∈ before → isBefore curr b
  touch_ok : ∀ {t}, t ∈ touching → isTouch curr t
  after_ok : ∀ {a}, a ∈ after → isAfter curr a

/-- Partition `xs` into the ranges before, touching, and after `curr`. -/
def splitRanges (curr : NR) (xs : List NR) : SplitWitness curr xs := by
  classical
  -- TODO: fill by combining `takeWhile` / `dropWhile` lemmas.
  exact sorry

/-- Fold `NR.glue` across a list, starting from `curr`. -/
def glueMany (curr : NR) (ts : List NR) : NR :=
  ts.foldl (fun acc t => NR.glue acc t) curr

/-- Set view of a list of ranges. -/
def listSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) (∅ : Set Int)

@[simp] lemma listSet_nil : listSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] lemma listSet_cons (r : NR) (rs : List NR) :
    listSet (r :: rs) = r.val.toSet ∪ listSet rs := rfl

@[simp] lemma toSet_eq_listSet (s : RangeSetBlaze) :
    s.toSet = listSet s.ranges := rfl

lemma touch_after_glue_step
    (curr x y : NR)
    (hx : isTouch curr x)
    (hy : isTouch curr y) :
    isTouch (NR.glue curr x) y := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have : y.val.hi + 1 < curr.val.lo :=
      lt_of_lt_of_le h (min_le_left _ _)
    exact hy₁ this
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have hmax :
        curr.val.hi + 1 ≤ max curr.val.hi x.val.hi + 1 :=
      add_le_add_right (le_max_left _ _) _
    have : curr.val.hi + 1 < y.val.lo := lt_of_le_of_lt hmax h
    exact hy₂ this

lemma glueMany_sets_touching
    (curr : NR) (ts : List NR)
    (htouch : ∀ t ∈ ts, isTouch curr t) :
    (glueMany curr ts).val.toSet =
      curr.val.toSet ∪ listSet ts := by
  classical
  induction ts generalizing curr with
  | nil =>
      simp [glueMany, listSet_nil]
  | cons t ts ih =>
      have htouch_t : isTouch curr t := htouch _ (by simp)
      have htouch_tail : ∀ u ∈ ts, isTouch curr u := by
        intro u hu; exact htouch u (by simp [hu])
      have hglue :
          (NR.glue curr t).val.toSet =
            curr.val.toSet ∪ t.val.toSet :=
        NR.glue_sets curr t htouch_t.2 htouch_t.1
      have htouch_tail' :
          ∀ u ∈ ts, isTouch (NR.glue curr t) u := by
        intro u hu
        exact touch_after_glue_step curr t u htouch_t (htouch_tail u hu)
      have ih' := ih (NR.glue curr t) htouch_tail'
      simp [glueMany, List.foldl] at ih'
      calc
        (glueMany curr (t :: ts)).val.toSet
            = (glueMany (NR.glue curr t) ts).val.toSet := by
              simp [glueMany, List.foldl]
        _ = (NR.glue curr t).val.toSet ∪ listSet ts := ih'
        _ = (curr.val.toSet ∪ t.val.toSet) ∪ listSet ts := by
              simpa [hglue, Set.union_left_comm, Set.union_assoc,
                Set.union_comm]
        _ = curr.val.toSet ∪ (t.val.toSet ∪ listSet ts) := by
              simp [Set.union_left_comm, Set.union_assoc]
        _ = curr.val.toSet ∪ listSet (t :: ts) := by
              simp [listSet_cons, Set.union_left_comm, Set.union_assoc]

lemma listSet_append (xs ys : List NR) :
    listSet (xs ++ ys) = listSet xs ∪ listSet ys := by
  induction xs with
  | nil =>
      simp [listSet_nil]
  | cons x xs ih =>
      simp [listSet_cons, List.cons_append, Set.union_left_comm,
        Set.union_assoc, ih]

/-- Rebuild the list by gluing the touching block. -/
def buildSplit (curr : NR) (before touching after : List NR) :
    List NR :=
  before ++ [glueMany curr touching] ++ after

lemma buildSplit_sets
    (curr : NR) {xs before touching after}
    (hx : xs = before ++ touching ++ after)
    (ht : ∀ t ∈ touching, isTouch curr t) :
    listSet (buildSplit curr before touching after) =
      curr.val.toSet ∪
        (listSet touching ∪ listSet before ∪ listSet after) := by
  classical
  subst hx
  simp [buildSplit, listSet_append, listSet_cons,
    glueMany_sets_touching curr touching ht, Set.union_left_comm,
    Set.union_assoc, Set.union_comm]

/-- New insertion algorithm reusing the existing `insert`. -/
def internalAddB (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  internalAddA s r

lemma internalAddB_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddB s r).toSet = s.toSet ∪ r.toSet := by
  classical
  simpa [internalAddB] using internalAddA_toSet s r

lemma internalAddB_agrees_with_split_sets
    (s : RangeSetBlaze) (r : IntRange) (hr : r.nonempty) :
    let curr : NR := ⟨r, hr⟩
    let w := splitRanges curr s.ranges
    listSet (buildSplit curr w.before w.touching w.after) =
      (internalAddB s r).toSet := by
  classical
  set curr : NR := ⟨r, hr⟩
  let w := splitRanges curr s.ranges
  have hsplit :
      listSet s.ranges =
        listSet w.before ∪ listSet w.touching ∪ listSet w.after := by
    simpa [w.order, listSet_append, Set.union_left_comm,
      Set.union_assoc, Set.union_comm]
  have hcurr : curr.val.toSet = r.toSet := rfl
  have hs : s.toSet = listSet s.ranges := toSet_eq_listSet s
  have hbuild :
      listSet (buildSplit curr w.before w.touching w.after) =
        curr.val.toSet ∪
          (listSet w.touching ∪ listSet w.before ∪ listSet w.after) :=
    buildSplit_sets (curr := curr) (xs := s.ranges)
      (before := w.before) (touching := w.touching) (after := w.after)
      w.order
      (by
        intro t ht
        exact w.touch_ok ht)
  calc
    listSet (buildSplit curr w.before w.touching w.after)
        = curr.val.toSet ∪
            (listSet w.touching ∪ listSet w.before ∪ listSet w.after) :=
            hbuild
    _ = listSet s.ranges ∪ r.toSet := by
        simp [hcurr, hsplit, Set.union_left_comm, Set.union_comm,
          Set.union_assoc]
    _ = s.toSet ∪ r.toSet := by
        rw [hs]
    _ = (internalAddB s r).toSet := by
        simpa using (internalAddB_toSet s r).symm

end RangeSetBlaze
