import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-
`Algo C` reimplementation that mirrors the production Rust insertion logic
while operating directly on the `NR` and `RangeSetBlaze` structures.

STATUS: Migrating away from unsafe constructors. Core invariant proofs COMPLETE!

COMPLETED (Session 10):
- ok_deleteExtraNRs: COMPLETE with hstop gap precondition
- ok_deleteExtraNRs_loop: COMPLETE (strong version requiring Pairwise (current :: pending))
- ok_deleteExtraNRs_loop_weak: COMPLETE (weak version requiring only Pairwise pending)
- ok_internalAdd2NRs: COMPLETE with gap hypothesis (either before = [] or last has gap < start)
- all_before_strict_before_start: Helper to propagate gap to all elements

COMPLETED (Session 11):
- Fixed unused variable warning in ok_deleteExtraNRs
- Created internalAdd2_safe: Safe wrapper using ok_internalAdd2NRs with fromNRs
- Moved internalAddC definition to after internalAdd2_safe (line 1134)
- **Proved span_le_empty_implies_lt_empty**: Bridging lemma showing (≤ start) empty → (< start) empty
- **Explored predicate unification** (Increment 8): Requires ~15-20 proof sections to be rewritten
- **Created internalAdd2_safe_from_le** (Increment 9): Wrapper accepting (≤) gaps and converting to (<)
- **Wired into internalAddC** (Increment 9): Both `none` and `some prev with gap` branches now use safe constructor

Current status: 3 sorrys (was 2)
- Line 60: mkNRUnsafe (intentional, to be eliminated)
- Line 67: fromNRsUnsafe (intentional, to be eliminated)
- Line ~1207: internalAdd2_safe_from_le conversion (new, needs proof)
- Line ~1241: getLast? = some prev → getLast hne = prev (new, small lemma needed)

The gap hypothesis in ok_internalAdd2NRs matches the actual call sites in internalAddC:
  - none case: before = [] (gap holds vacuously) ✅ WIRED
  - some prev with gap: prev.val.hi + 1 < start (gap provided directly) ✅ WIRED (with sorry)

NEXT STEPS:

**Immediate (to get back to 2 sorrys):**
1. Prove getLast? = some x → getLast hne = x (simple List lemma)
2. Prove (≤) last with gap → (<) last with gap in internalAdd2_safe_from_le
   - Key insight: prev.hi + 1 < start implies prev.lo < start
   - Need to show prev is in the (<) split and is its last element

**Then:**
3. Fix broken proofs in internalAddC_correct (they reference old internalAdd2 calls)
4. Consider making extend-prev branch safe too (uses fromNRsUnsafe currently)

Current unsafe constructors (to eventually remove):
- mkNRUnsafe (line 39): Creates NR without proof
- fromNRsUnsafe (line 46): Creates RangeSetBlaze without Pairwise proof
-/

private def mkNRUnsafe (lo hi : Int) : NR :=
  Subtype.mk { lo := lo, hi := hi } (by sorry)

private def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

/-- DEPRECATED: Use `fromNRs` with explicit invariant proof instead. -/
private def fromNRsUnsafe (xs : List NR) : RangeSetBlaze :=
  { ranges := xs, ok := by sorry }

/-- Safe constructor when you already have the invariant. -/
private def fromNRs (xs : List NR)
  (hok : List.Pairwise NR.before xs) : RangeSetBlaze :=
  { ranges := xs, ok := hok }

-- NEW: top-level version of the previous nested `loop`
private def deleteExtraNRs_loop (current : NR) (pending : List NR) : Prod NR (List NR) :=
  match pending with
  | [] => (current, [])
  | next :: pendingTail =>
      if decide (next.val.lo ≤ current.val.hi + 1) then
        let newLo := current.val.lo
        let newHi := max current.val.hi next.val.hi
        have hcurr' : current.val.lo ≤ current.val.hi := current.property
        have hmax'  : current.val.hi ≤ newHi := le_max_left _ _
        have hmerged : newLo ≤ newHi := le_trans hcurr' hmax'
        let merged := mkNR newLo newHi hmerged
        deleteExtraNRs_loop merged pendingTail
      else
        (current, next :: pendingTail)

@[simp] private lemma deleteExtraNRs_loop_nil (current : NR) :
    deleteExtraNRs_loop current [] = (current, []) := rfl

@[simp] private lemma deleteExtraNRs_loop_cons_merge
    (current next : NR) (tail : List NR)
    (h : next.val.lo ≤ current.val.hi + 1) :
  deleteExtraNRs_loop current (next :: tail)
    =
  deleteExtraNRs_loop
    (mkNR current.val.lo (max current.val.hi next.val.hi)
      (by
        have hc : current.val.lo ≤ current.val.hi := current.property
        exact le_trans hc (le_max_left _ _)))
    tail := by
  simp [deleteExtraNRs_loop, h]

@[simp] private lemma deleteExtraNRs_loop_cons_noMerge
    (current next : NR) (tail : List NR)
    (h : ¬ next.val.lo ≤ current.val.hi + 1) :
  deleteExtraNRs_loop current (next :: tail) = (current, next :: tail) := by
  simp [deleteExtraNRs_loop, h]

/-- If two ordered ranges touch or overlap, their union equals the single
closed interval that stretches to the larger upper end. -/
private lemma union_touch_eq_Icc_max
    (lo₁ hi₁ lo₂ hi₂ : Int)
    (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
    (h_order : lo₁ ≤ lo₂)
    (h_touch : ¬ (hi₁ + 1 < lo₂)) :
    Set.Icc lo₁ hi₁ ∪ Set.Icc lo₂ hi₂ =
      Set.Icc lo₁ (max hi₁ hi₂) := by
  classical
  apply Set.ext
  intro x
  constructor
  · intro hx
    have _ := h₁
    have _ := h₂
    rcases hx with hx₁ | hx₂
    · rcases hx₁ with ⟨hx_lo, hx_hi⟩
      exact ⟨hx_lo, le_trans hx_hi (le_max_left _ _)⟩
    · rcases hx₂ with ⟨hx_lo, hx_hi⟩
      have hx_lo' : lo₁ ≤ x := le_trans h_order hx_lo
      have hx_hi' : x ≤ max hi₁ hi₂ := le_trans hx_hi (le_max_right _ _)
      exact ⟨hx_lo', hx_hi'⟩
  · intro hx
    rcases hx with ⟨hx_lo, hx_hi⟩
    by_cases hx_le : x ≤ hi₁
    · left
      exact ⟨hx_lo, hx_le⟩
    · have hx_gt : hi₁ < x := lt_of_not_ge hx_le
      have hx_add : hi₁ + 1 ≤ x := (Int.add_one_le_iff).2 hx_gt
      have h_lo₂ : lo₂ ≤ x := le_trans (le_of_not_gt h_touch) hx_add
      have hx_le_hi₂ : x ≤ hi₂ := by
        have h_or := (le_max_iff).1 hx_hi
        exact h_or.resolve_left hx_le
      right
      exact ⟨h_lo₂, hx_le_hi₂⟩

/-- Set-level description of a single merge step inside `deleteExtraNRs`. -/
private lemma merge_step_sets
    (current next : NR)
    (horder : current.val.lo ≤ next.val.lo)
    (htouch : ¬ (current.val.hi + 1 < next.val.lo)) :
    current.val.toSet ∪ next.val.toSet =
      (mkNR current.val.lo (max current.val.hi next.val.hi)
        (by
          have hc : current.val.lo ≤ current.val.hi := current.property
          have : current.val.hi ≤ max current.val.hi next.val.hi :=
            le_max_left _ _
          exact le_trans hc this)).val.toSet := by
  classical
  have h₁ : current.val.lo ≤ current.val.hi := current.property
  have h₂ : next.val.lo ≤ next.val.hi := next.property
  have h_union :=
    union_touch_eq_Icc_max current.val.lo current.val.hi
      next.val.lo next.val.hi h₁ h₂ horder htouch
  simpa [IntRange.toSet, mkNR] using h_union

private def deleteExtraNRs (xs : List NR) (start stop : Int) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let rest := split.snd
  match rest with
  | [] => xs
  | curr :: tail =>
      let initialHi := max curr.val.hi stop
      have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
      have hmax : curr.val.hi ≤ initialHi := le_max_left _ _
      have hinit : curr.val.lo ≤ initialHi := le_trans hcurr hmax
      let initial := mkNR curr.val.lo initialHi hinit
      let result := deleteExtraNRs_loop initial tail
      before ++ (result.fst :: result.snd)

private def internalAdd2NRs (xs : List NR) (start stop : Int)
    (h : start ≤ stop) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let after := split.snd
  let inserted := mkNR start stop h
  deleteExtraNRs (before ++ (inserted :: after)) start stop

def delete_extra (s : RangeSetBlaze) (internalRange : IntRange) :
    RangeSetBlaze :=
  let start := internalRange.lo
  let stop := internalRange.hi
  fromNRsUnsafe (deleteExtraNRs s.ranges start stop)

def internalAdd2 (s : RangeSetBlaze) (internalRange : IntRange) :
    RangeSetBlaze :=
  let start := internalRange.lo
  let stop := internalRange.hi
  if h : stop < start then
    s
  else
    let hle : start ≤ stop := not_lt.mp h
    fromNRsUnsafe (internalAdd2NRs s.ranges start stop hle)

open Classical
open IntRange

/-- Pack endpoints as a nonempty range. -/
private def mkNR' (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

/-- Local list-based view of the union of ranges. -/
private def listSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) (∅ : Set Int)

@[simp] private lemma listSet_nil :
    listSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] private lemma listSet_cons (r : NR) (rs : List NR) :
    listSet (r :: rs) = r.val.toSet ∪ listSet rs := rfl

@[simp] private lemma listSet_append (xs ys : List NR) :
    listSet (xs ++ ys) = listSet xs ∪ listSet ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Set.union_left_comm, Set.union_comm]

private lemma takeWhile_append_of_all {α : Type _} (p : α → Bool)
    (l : List α) (x : α) (xs : List α)
    (hall : ∀ y ∈ l, p y = true) (hx : p x = false) :
    (l ++ x :: xs).takeWhile p = l := by
  induction l with
  | nil =>
      simp [hx]
  | cons y ys ih =>
      have hy : p y = true := hall y (by simp)
      have hys : ∀ z ∈ ys, p z = true := by
        intro z hz
        exact hall z (by simp [hz])
      simp [hy, ih hys]

private lemma dropWhile_append_of_all {α : Type _} (p : α → Bool)
    (l : List α) (x : α) (xs : List α)
    (hall : ∀ y ∈ l, p y = true) (hx : p x = false) :
    (l ++ x :: xs).dropWhile p = x :: xs := by
  induction l with
  | nil =>
      simp [hx]
  | cons y ys ih =>
      have hy : p y = true := hall y (by simp)
      have hys : ∀ z ∈ ys, p z = true := by
        intro z hz
        exact hall z (by simp [hz])
      simp [hy, ih hys]

private def loLE (a b : NR) : Prop :=
  a.val.lo ≤ b.val.lo

/-- If ranges satisfy `Pairwise before`, they also satisfy `IsChain loLE`.
The `before` relation (no gap/overlap) implies `lo` ordering. -/
private lemma pairwise_before_implies_chain_loLE (xs : List NR)
    (h : List.Pairwise NR.before xs) :
    List.IsChain loLE xs := by
  induction xs with
  | nil => constructor
  | cons x xs ih =>
      cases xs with
      | nil => constructor
      | cons y ys =>
          cases h with
          | cons hxy hrest =>
              have hchain_tail : List.IsChain loLE (y :: ys) := by
                exact ih hrest
              constructor
              · unfold loLE NR.before at *
                have : x.val.hi + 1 < y.val.lo := hxy y (by simp)
                have : x.val.hi < y.val.lo := by linarith
                have : x.val.lo ≤ x.val.hi := x.property
                linarith
              · exact hchain_tail

private lemma mem_takeWhile_satisfies {α : Type _} (p : α → Bool) (xs : List α) (x : α)
    (h : x ∈ xs.takeWhile p) : p x = true := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
      cases hpy : p y with
      | false => simp [List.takeWhile, hpy] at h
      | true =>
          simp [List.takeWhile, hpy] at h
          cases h with
          | inl heq => subst heq; exact hpy
          | inr htail => exact ih htail

/-- If a list satisfies Pairwise and we decompose it as `pfx ++ [lastElem]`,
then every element in pfx satisfies the pairwise relation with `lastElem`. -/
private lemma pairwise_prefix_last {α : Type _} (R : α → α → Prop)
    (pfx : List α) (lastElem : α)
    (h : List.Pairwise R (pfx ++ [lastElem])) :
    ∀ x ∈ pfx, R x lastElem := by
  intro x hx
  induction pfx with
  | nil => cases hx
  | cons y ys ih =>
      simp at hx
      cases hx with
      | inl heq =>
          subst heq
          cases h with
          | cons hy _ =>
              exact hy lastElem (by simp)
      | inr htail =>
          cases h with
          | cons _ hrest =>
              exact ih hrest htail

/-- Extract Pairwise on the left part of an append. -/
private lemma pairwise_append_left {α : Type _} (R : α → α → Prop)
    (xs ys : List α) (h : List.Pairwise R (xs ++ ys)) :
    List.Pairwise R xs := by
  induction xs generalizing ys with
  | nil => constructor
  | cons x xs' ih =>
      cases h with
      | cons hx hrest =>
          constructor
          · intro y hy
            exact hx y (by simp [hy])
          · exact ih ys hrest

/-- Extract the cross-product property from Pairwise on an append. -/
private lemma pairwise_append_cross {α : Type _} (R : α → α → Prop)
    (xs ys : List α) (h : List.Pairwise R (xs ++ ys)) :
    ∀ x ∈ xs, ∀ y ∈ ys, R x y := by
  induction xs generalizing ys with
  | nil => intros; contradiction
  | cons x xs' ih =>
      cases h with
      | cons hx hrest =>
          intro a ha y hy
          simp at ha
          cases ha with
          | inl heq =>
              rw [heq]
              exact hx y (by simp [hy])
          | inr hmem => exact ih ys hrest a hmem y hy

/-- Construct Pairwise on an append when left is Pairwise, right is Pairwise,
and all elements of left relate to all elements of right. -/
private lemma pairwise_append {α : Type _} (R : α → α → Prop)
    (xs ys : List α)
    (hxs : List.Pairwise R xs)
    (hys : List.Pairwise R ys)
    (hcross : ∀ x ∈ xs, ∀ y ∈ ys, R x y) :
    List.Pairwise R (xs ++ ys) := by
  induction xs with
  | nil => exact hys
  | cons x xs' ih =>
      cases hxs with
      | cons hx_xs' hxs' =>
          constructor
          · intro y hy
            simp at hy
            cases hy with
            | inl hmem => exact hx_xs' y hmem
            | inr hmem => exact hcross x (by simp) y hmem
          · exact ih hxs' (fun x' hx' y hy => hcross x' (by simp [hx']) y hy)

private lemma nr_mem_ranges_subset_listSet : ∀ (ranges : List NR) (nr : NR),
    nr ∈ ranges → nr.val.toSet ⊆ listSet ranges
  | [], _, h => by cases h
  | x :: xs, nr, h => by
      simp [List.mem_cons] at h
      rw [listSet_cons]
      cases h with
      | inl heq =>
          subst heq
          exact Set.subset_union_left
      | inr htail =>
          exact Set.subset_union_of_subset_right (nr_mem_ranges_subset_listSet xs nr htail) _

private lemma chain_head_le_all_tail
    (y : NR) (ys : List NR)
    (hchain : List.IsChain loLE (y :: ys)) :
    ∀ z ∈ ys, y.val.lo ≤ z.val.lo := by
  revert y
  induction ys with
  | nil =>
      intro y _ z hz
      cases hz
  | cons a ys ih =>
      intro y hchain z hz
      have h_y_le_a : y.val.lo ≤ a.val.lo := by
        have := List.IsChain.rel_head hchain
        exact this
      have htail : List.IsChain loLE (a :: ys) :=
        List.IsChain.tail hchain
      have hz_cases : z = a ∨ z ∈ ys := by
        simp only [List.mem_cons] at hz
        exact hz
      cases hz_cases with
      | inl hz_eq =>
          subst hz_eq
          exact h_y_le_a
      | inr hz_mem =>
          have h_a_le_z : a.val.lo ≤ z.val.lo :=
            ih _ htail _ hz_mem
          exact le_trans h_y_le_a h_a_le_z

private lemma span_suffix_all_ge_start_of_chain
    (xs : List NR) (start : Int)
    (hchain : List.IsChain loLE xs) :
    let p : NR → Bool := fun nr => decide (nr.val.lo < start)
    let split := List.span p xs
    ∀ nr ∈ split.snd, start ≤ nr.val.lo := by
  classical
  intro p split
  have h_span : split = (xs.takeWhile p, xs.dropWhile p) :=
    List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
  have h_take : split.fst = xs.takeWhile p := by
    exact congrArg Prod.fst h_span
  have h_drop : split.snd = xs.dropWhile p := by
    exact congrArg Prod.snd h_span
  have h_decomp : split.fst ++ split.snd = xs := by
    have := List.takeWhile_append_dropWhile (p := p) (l := xs)
    rw [h_take, h_drop]
    exact this
  intro nr hmem
  have hchain_append :
      List.IsChain loLE (split.fst ++ split.snd) := by
    rw [h_decomp]
    exact hchain
  have hchain_suffix :
      List.IsChain loLE split.snd :=
    List.IsChain.right_of_append (l₁ := split.fst)
      (l₂ := split.snd) hchain_append
  cases hA : split.snd with
  | nil =>
      rw [hA] at hmem
      cases hmem
  | cons y ys =>
      have hmem_cons : nr = y ∨ nr ∈ ys := by
        rw [hA] at hmem
        simp at hmem
        exact hmem
      have hy_head? :
          (xs.dropWhile p).head? = some y := by
        have : split.snd.head? = some y := by
          rw [hA]
          rfl
        rw [← h_drop]
        exact this
      have hy_false : p y = false := by
        have := List.head?_dropWhile_not (p := p) (l := xs)
        rw [hy_head?] at this
        simp at this
        exact this
      have hy_not_lt : ¬ y.val.lo < start := by
        intro hy_lt
        have hcontra : p y = true := by
          unfold p
          simp [hy_lt]
        rw [hcontra] at hy_false
        contradiction
      have h_start_le_y : start ≤ y.val.lo :=
        not_lt.mp hy_not_lt
      have hchain_after : List.IsChain loLE (y :: ys) := by
        rw [hA] at hchain_suffix
        exact hchain_suffix
      cases hmem_cons with
      | inl hnr =>
          subst hnr
          exact h_start_le_y
      | inr htail =>
          have h_y_le_nr :
              y.val.lo ≤ nr.val.lo :=
            chain_head_le_all_tail y ys hchain_after nr htail
          exact le_trans h_start_le_y h_y_le_nr

/-- Splice lemma assuming the input list is chain-sorted by `lo`. -/
lemma deleteExtraNRs_loop_sets
    (start : Int) :
    ∀ (pending : List NR) (current : NR),
      current.val.lo = start →
      (∀ nr ∈ pending, start ≤ nr.val.lo) →
      listSet
          (let res := deleteExtraNRs_loop current pending;
            res.fst :: res.snd)
        =
          current.val.toSet ∪ listSet pending := by
  intro pending current hcurlo hpend
  induction pending generalizing current with
  | nil =>
      simp [deleteExtraNRs_loop, listSet_cons, listSet_nil, Set.union_comm]
  | cons next tail ih =>
      dsimp [deleteExtraNRs_loop]
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- merge branch
        have horder : current.val.lo ≤ next.val.lo := by
          have : start ≤ next.val.lo := hpend next (by simp)
          simpa [hcurlo] using this
        have htouch : ¬ (current.val.hi + 1 < next.val.lo) :=
          not_lt.mpr hmerge
        have hpend' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr hmem
          exact hpend nr (by simp [hmem])
        set merged :=
          mkNR current.val.lo (max current.val.hi next.val.hi)
            (by
              have hc : current.val.lo ≤ current.val.hi := current.property
              exact le_trans hc (le_max_left _ _)) with hmerged_def
        have hcurlo' : merged.val.lo = start := by
          simp [hmerged_def, mkNR, hcurlo]
        have hrec :=
          ih merged hcurlo' hpend'
        have hmerged_toSet :
            merged.val.toSet = current.val.toSet ∪ next.val.toSet := by
          simpa [hmerged_def] using
            (merge_step_sets current next horder htouch).symm
        have hstep :
            deleteExtraNRs_loop current (next :: tail)
              =
            deleteExtraNRs_loop merged tail := by
          simpa [hmerged_def] using
            (deleteExtraNRs_loop_cons_merge current next tail hmerge)
        have hloop_simplified :
            listSet
                ((deleteExtraNRs_loop current (next :: tail)).fst ::
                  (deleteExtraNRs_loop current (next :: tail)).snd)
              =
                merged.val.toSet ∪ listSet tail := by
          simpa [hstep] using hrec
        calc
          listSet
              (let res := deleteExtraNRs_loop current (next :: tail);
                res.fst :: res.snd)
              =
                merged.val.toSet ∪ listSet tail := hloop_simplified
          _ = (current.val.toSet ∪ next.val.toSet) ∪ listSet tail := by
                simp [hmerged_toSet]
          _ = current.val.toSet ∪ listSet (next :: tail) := by
                simp [listSet_cons, Set.union_left_comm, Set.union_assoc,
                  Set.union_comm]
      · -- no-merge branch
        have hmerge' : ¬ next.val.lo ≤ current.val.hi + 1 := hmerge
        have hloop_eq :
            deleteExtraNRs_loop current (next :: tail)
              = (current, next :: tail) := by
          simpa using deleteExtraNRs_loop_cons_noMerge current next tail hmerge'
        simp [hmerge, listSet_cons, Set.union_left_comm]

/-- Helper: deleteExtraNRs_loop preserves the property that result.fst.lo = start
and all elements in result.snd have lo ≥ start. -/
private lemma deleteExtraNRs_loop_lo_ge
    (start : Int)
    (current : NR) (pending : List NR)
    (hlo : current.val.lo = start)
    (hge : ∀ nr ∈ pending, start ≤ nr.val.lo) :
    let res := deleteExtraNRs_loop current pending
    res.fst.val.lo = start ∧ ∀ nr ∈ res.snd, start ≤ nr.val.lo := by
  induction pending generalizing current with
  | nil =>
      simp
      exact hlo
  | cons next tail ih =>
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- Merge case
        set merged := mkNR current.val.lo (max current.val.hi next.val.hi)
          (by have := current.property; exact le_trans this (le_max_left _ _))
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          deleteExtraNRs_loop merged tail := by
          simpa using deleteExtraNRs_loop_cons_merge current next tail hmerge
        rw [h_loop_eq]
        apply ih merged
        · simp [merged, mkNR, hlo]
        · intro nr hmem
          exact hge nr (by simp [hmem])
      · -- No merge case
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          (current, next :: tail) := by
          simpa using deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        rw [h_loop_eq]
        simp
        constructor
        · exact hlo
        · constructor
          · exact hge next (by simp)
          · intro a ha hmem
            exact hge ⟨a, nonempty_iff_not_empty a |>.mpr ha⟩ (by simp [hmem])

/-- Invariant preservation: `deleteExtraNRs_loop` maintains `Pairwise NR.before`.
- Base case (nil): trivial, loop returns `(current, [])`.
- Inductive case (cons next tail):
  * If merge (next.lo ≤ current.hi + 1):
    - Construct merged range from current.lo to max current.hi next.hi
    - Need to show: if Pairwise on (current :: next :: tail), then Pairwise on (merged :: tail)
    - Key: merged.lo = current.lo, and merged.hi ≥ next.hi
    - For any z ∈ tail: next ≺ z implies merged ≺ z (since merged.hi ≤ max current.hi next.hi and max ≤ next.hi in this direction doesn't help, but next ≺ z means next.hi + 1 < z.lo, and since we're merging, current.hi ≈ next.hi)
    - Apply IH to (merged, tail)
  * If no merge:
    - Loop returns (current, next :: tail), which is exactly the input Pairwise structure
-/
private lemma ok_deleteExtraNRs_loop
    (start : Int)
    (current : NR) (pending : List NR)
    (hlo : current.val.lo = start)
    (hge : ∀ nr ∈ pending, start ≤ nr.val.lo)
    (hpw : List.Pairwise NR.before (current :: pending)) :
    List.Pairwise NR.before
      (let res := deleteExtraNRs_loop current pending;
        res.fst :: res.snd) := by
  induction pending generalizing current with
  | nil =>
      simp
  | cons next tail ih =>
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- Merge case
        set merged := mkNR current.val.lo (max current.val.hi next.val.hi)
          (by have := current.property; exact le_trans this (le_max_left _ _))

        -- The loop will recursively process (merged, tail)
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          deleteExtraNRs_loop merged tail := by
          simpa using deleteExtraNRs_loop_cons_merge current next tail hmerge

        rw [h_loop_eq]

        -- Apply IH: need to show Pairwise on (merged :: tail)
        apply ih merged
        · -- merged.lo = start
          simp [merged, mkNR, hlo]
        · -- ∀ nr ∈ tail, start ≤ nr.lo
          intro nr hmem
          exact hge nr (by simp [hmem])
        · -- Pairwise on (merged :: tail)
          -- Extract the structure of hpw: Pairwise (current :: next :: tail)
          cases hpw with
          | cons h_current_rest hpw_rest =>
              -- h_current_rest: ∀ b ∈ (next :: tail), current ≺ b
              -- hpw_rest: Pairwise (next :: tail)
              cases hpw_rest with
              | cons h_next_tail hpw_tail =>
                  -- h_next_tail: ∀ b ∈ tail, next ≺ b
                  -- hpw_tail: Pairwise tail
                  constructor
                  · -- Show: ∀ z ∈ tail, merged ≺ z
                    intro z hz
                    unfold NR.before at *
                    -- We have: next ≺ z, i.e., next.hi + 1 < z.lo
                    have h_next_z : next.val.hi + 1 < z.val.lo := h_next_tail z hz
                    -- merged.hi = max current.hi next.hi
                    have h_merged_hi : merged.val.hi = max current.val.hi next.val.hi := by
                      simp [merged, mkNR]
                    rw [h_merged_hi]
                    -- Need: max current.hi next.hi + 1 < z.lo
                    -- We know both: current ≺ z and next ≺ z
                    have h_current_z : current.val.hi + 1 < z.val.lo :=
                      h_current_rest z (by simp [hz])
                    -- So max current.hi next.hi < z.lo - 1, hence max + 1 < z.lo
                    have : max current.val.hi next.val.hi < z.val.lo := by omega
                    omega
                  · exact hpw_tail
      · -- No merge case
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) =
                          (current, next :: tail) := by
          simpa using deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        simp [h_loop_eq, hpw]

/-- Weak variant: we only assume `Pairwise pending` and `start ≤ lo` on `pending`.
It shows the loop output is `Pairwise`, even if `current` may overlap `pending.head`. -/
private lemma ok_deleteExtraNRs_loop_weak
    (start : Int)
    (current : NR) (pending : List NR)
    (hlo  : current.val.lo = start)
    (hge  : ∀ nr ∈ pending, start ≤ nr.val.lo)
    (hpwP : List.Pairwise NR.before pending) :
    List.Pairwise NR.before
      (let res := deleteExtraNRs_loop current pending; res.fst :: res.snd) := by
  induction pending generalizing current with
  | nil =>
      simp [deleteExtraNRs_loop]
  | cons next tail ih =>
      by_cases hmerge : next.val.lo ≤ current.val.hi + 1
      · -- MERGE: recurse on (merged, tail)
        set merged :=
          mkNR current.val.lo (max current.val.hi next.val.hi)
            (by have := current.property; exact le_trans this (le_max_left _ _))
        have hge' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
          intro nr h; exact hge nr (by simp [h])
        have hpw_tail : List.Pairwise NR.before tail := by
          cases hpwP with
          | cons _ htail => exact htail
        have hmerged_lo : merged.val.lo = start := by
          simp [merged, mkNR, hlo]
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) = deleteExtraNRs_loop merged tail := by
          exact deleteExtraNRs_loop_cons_merge current next tail hmerge
        simp only [h_loop_eq]
        exact ih merged hmerged_lo hge' hpw_tail
      · -- NO MERGE: loop returns (current, next :: tail)
        have h_loop_eq : deleteExtraNRs_loop current (next :: tail) = (current, next :: tail) := by
          exact deleteExtraNRs_loop_cons_noMerge current next tail hmerge
        simp only [h_loop_eq]
        -- we need: current ≺ next and for all z∈tail, current ≺ z
        have h_head : NR.before current next := by
          unfold NR.before; simpa using (not_le.mp hmerge)
        -- For z ∈ tail, use chain order from `Pairwise pending`
        have hchain : List.IsChain loLE (next :: tail) :=
          pairwise_before_implies_chain_loLE (next :: tail) (by
            cases hpwP with
            | cons hx htail => exact List.Pairwise.cons hx htail)
        have hnext_le : ∀ z ∈ tail, next.val.lo ≤ z.val.lo :=
          chain_head_le_all_tail next tail hchain
        have h_current_tail : ∀ z ∈ tail, NR.before current z := by
          intro z hz
          have : current.val.hi + 1 < next.val.lo := by simpa [NR.before] using h_head
          have : current.val.hi + 1 < z.val.lo := lt_of_lt_of_le this (hnext_le z hz)
          simpa [NR.before] using this
        have hpw_tail : List.Pairwise NR.before tail := by
          cases hpwP with
          | cons _ htail => exact htail
        -- Construct Pairwise (current :: next :: tail)
        constructor
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact h_head
          · exact h_current_tail b hb
        · constructor
          · intro b hb
            cases hpwP with
            | cons hx _ => exact hx b hb
          · exact hpw_tail

/-- If dropWhile returns a non-empty list, the first element doesn't satisfy the predicate. -/
private lemma dropWhile_head_not_satisfies {α : Type _} (p : α → Bool) (xs : List α) (x : α) (xs' : List α)
    (h : xs.dropWhile p = x :: xs') :
    p x = false := by
  induction xs with
  | nil =>
      simp [List.dropWhile] at h
  | cons y ys ih =>
      simp [List.dropWhile] at h
      split at h
      · -- p y = true, so y is dropped, recurse
        exact ih h
      · -- p y = false, so dropWhile returns y :: ys
        rename_i h_not
        cases h
        exact h_not

/-- If `before` is nonempty and its last element is strictly before `start`,
then every element of `before` is strictly before `start`. -/
private lemma all_before_strict_before_start
    (before : List NR) (start : Int)
    (hpair : List.Pairwise NR.before before)
    (hne : before ≠ [])
    (hlast : (before.getLast hne).val.hi + 1 < start) :
    ∀ x ∈ before, x.val.hi + 1 < start := by
  -- every x ∈ (dropLast before) satisfies x ≺ last(before)
  have h_all : ∀ x ∈ List.dropLast before, NR.before x (before.getLast hne) := by
    -- pairwise on (dropLast before ++ [last])
    have : List.Pairwise NR.before (List.dropLast before ++ [before.getLast hne]) := by
      -- standard: before = dropLast before ++ [getLast before]
      have := List.dropLast_append_getLast hne
      -- rewrite pairwise along equality
      simpa [this] using hpair
    -- extract cross-product from append
    exact pairwise_prefix_last NR.before (List.dropLast before) (before.getLast hne) this
  -- now any x ∈ before is either the last or in dropLast
  intro x hx
  by_cases hdrop : x ∈ List.dropLast before
  · have hx_before_last := h_all x hdrop
    -- x ≺ last ⇒ x.hi + 1 < last.lo, and last.lo ≤ last.hi + 1 < start
    unfold NR.before at hx_before_last
    have last_lo_lt_start : (before.getLast hne).val.lo < start := by
      have : (before.getLast hne).val.lo ≤ (before.getLast hne).val.hi := (before.getLast hne).property
      calc (before.getLast hne).val.lo
        _ ≤ (before.getLast hne).val.hi := this
        _ < (before.getLast hne).val.hi + 1 := by omega
        _ < start := hlast
    exact lt_trans hx_before_last last_lo_lt_start
  · -- x is not in dropLast, so x must be the last
    have heq : x = before.getLast hne := by
      have : before = List.dropLast before ++ [before.getLast hne] := (List.dropLast_append_getLast hne).symm
      rw [this] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · contradiction
      · exact hx
    subst heq
    exact hlast

/-- Lemma for internalAdd2NRs: inserting [start,stop] into a Pairwise list maintains Pairwise.
This version requires a gap hypothesis: either before is empty, or the last element of before
is strictly before start. This matches the actual call sites in internalAddC. -/
private lemma ok_internalAdd2NRs (xs : List NR) (start stop : Int) (h_le : start ≤ stop)
    (hpw : List.Pairwise NR.before xs)
    (hgap : let split := List.span (fun nr => decide (nr.val.lo < start)) xs
            let before := split.fst
            before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start) :
    let split := List.span (fun nr => decide (nr.val.lo < start)) xs
    let before := split.fst
    let after := split.snd
    let inserted := mkNR start stop h_le
    let ys := before ++ inserted :: after
    List.Pairwise NR.before (deleteExtraNRs ys start stop) := by
  intro split before after inserted ys

  -- Set up the predicate
  set p : NR → Bool := (fun nr => decide (nr.val.lo < start)) with hp

  -- Properties of before: all elements satisfy p (i.e., nr.lo < start)
  have h_before_all : ∀ nr ∈ before, p nr = true := by
    intro nr hmem
    -- before = xs.takeWhile p
    have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
    have : before = xs.takeWhile p := by
      have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
      simp [split, before] at this ⊢
      exact this.1
    rw [this] at hmem
    exact List.mem_takeWhile_imp hmem

  -- inserted doesn't satisfy p (inserted.lo = start, so not < start)
  have h_inserted_false : p inserted = false := by
    simp only [p, decide_eq_false_iff_not, not_lt]
    show start ≤ inserted.val.lo
    simp [inserted, mkNR]

  -- Span of ys gives back (before, inserted :: after)
  have h_span_ys : List.span p ys = (before, inserted :: after) := by
    have htake : ys.takeWhile p = before :=
      takeWhile_append_of_all p before inserted after h_before_all h_inserted_false
    have hdrop : ys.dropWhile p = inserted :: after :=
      dropWhile_append_of_all p before inserted after h_before_all h_inserted_false
    simp [List.span_eq_takeWhile_dropWhile, htake, hdrop]

  -- Now analyze deleteExtraNRs on ys
  unfold deleteExtraNRs

  -- The span in deleteExtraNRs uses the exact same predicate
  have h_span_match :
    List.span (fun nr => decide (nr.val.lo < start)) ys = (before, inserted :: after) := by
    convert h_span_ys using 1

  -- Simplify using the span result
  simp only [h_span_match]

  -- Now we have: before ++ (deleteExtraNRs_loop initial after).fst :: (deleteExtraNRs_loop initial after).snd
  -- where initial = mkNR inserted.lo (max inserted.hi stop) = mkNR start (max stop stop) = mkNR start stop

  -- Simplify initial to show it equals inserted
  have h_initial_eq :
    let curr := inserted
    let initialHi := max curr.val.hi stop
    mkNR curr.val.lo initialHi (by
      have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
      have hmax : curr.val.hi ≤ initialHi := le_max_left _ _
      exact le_trans hcurr hmax) = mkNR start stop h_le := by
    have : max stop stop = stop := max_self stop
    simp only [inserted, mkNR, this]

  -- Set up for applying ok_deleteExtraNRs_loop
  set curr := inserted
  set initialHi := max curr.val.hi stop
  have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
  have hmax_prop : curr.val.hi ≤ initialHi := le_max_left _ _
  set initial := mkNR curr.val.lo initialHi (le_trans hcurr hmax_prop)
  set result := deleteExtraNRs_loop initial after

  -- Need to prove: before ++ (result.fst :: result.snd) is Pairwise

  -- Step 1: Get Pairwise on before (from xs)
  have hpw_before : List.Pairwise NR.before before := by
    have h_xs_decomp : xs = before ++ after := by
      have := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
      calc xs
        _ = xs.takeWhile p ++ xs.dropWhile p := by
          exact (List.takeWhile_append_dropWhile (p := p) (l := xs)).symm
        _ = before ++ after := by
          have h1 : before = xs.takeWhile p := by
            have : split = (xs.takeWhile p, xs.dropWhile p) := this
            simp [split, before] at this ⊢
            exact this.1
          have h2 : after = xs.dropWhile p := by
            have : split = (xs.takeWhile p, xs.dropWhile p) :=
              List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
            simp [split, after] at this ⊢
            exact this.2
          rw [h1, h2]
    rw [h_xs_decomp] at hpw
    exact pairwise_append_left NR.before before after hpw

  -- Step 2: Extract Pairwise on after
  have hpw_after : List.Pairwise NR.before after := by
    have h_xs_decomp : xs = before ++ after := by
      have := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
      calc xs
        _ = xs.takeWhile p ++ xs.dropWhile p := by
          exact (List.takeWhile_append_dropWhile (p := p) (l := xs)).symm
        _ = before ++ after := by
          have h1 : before = xs.takeWhile p := by
            have : split = (xs.takeWhile p, xs.dropWhile p) := this
            simp [split, before] at this ⊢
            exact this.1
          have h2 : after = xs.dropWhile p := by
            have : split = (xs.takeWhile p, xs.dropWhile p) :=
              List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
            simp [split, after] at this ⊢
            exact this.2
          rw [h1, h2]
    rw [h_xs_decomp] at hpw
    -- Extract Pairwise on after
    revert hpw
    induction before with
    | nil => intro hpw; exact hpw
    | cons x xs ih =>
        intro hpw
        cases hpw with
        | cons _ hrest => exact ih hrest

  -- Step 3: Apply ok_deleteExtraNRs_loop_weak to get Pairwise on (result.fst :: result.snd)
  -- The weak version only requires Pairwise on `after`, not on (initial :: after)
  have hpw_result : List.Pairwise NR.before (result.fst :: result.snd) := by
    have h_initial_lo : initial.val.lo = start := by
      simp [initial, curr, inserted, mkNR]
    have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
      intro nr hnr
      have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
      have : after = xs.dropWhile p := by
        have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
        simp [split, after] at this ⊢
        exact this.2
      rw [this] at hnr
      by_cases h_empty : xs.dropWhile p = []
      · rw [h_empty] at hnr; cases hnr
      · have ⟨first, rest, h_cons⟩ := List.exists_cons_of_ne_nil h_empty
        rw [h_cons] at hnr
        have h_first_ge : start ≤ first.val.lo := by
          have h_first_head : (xs.dropWhile p).head? = some first := by rw [h_cons]; rfl
          have := List.head?_dropWhile_not (p := p) (l := xs)
          rw [h_first_head] at this
          simp at this
          simp only [p, decide_eq_false_iff_not, not_lt] at this
          exact this
        have h_chain : List.IsChain loLE xs := pairwise_before_implies_chain_loLE xs hpw
        have h_chain_drop : List.IsChain loLE (xs.dropWhile p) := by
          have h_decomp := List.takeWhile_append_dropWhile (p := p) (l := xs)
          rw [← h_decomp] at h_chain
          exact List.IsChain.right_of_append h_chain
        rw [h_cons] at h_chain_drop
        simp only [List.mem_cons] at hnr
        rcases hnr with hnr_eq | hnr_tail
        · rw [hnr_eq]; exact h_first_ge
        · have h_nr_ge_first : first.val.lo ≤ nr.val.lo :=
            chain_head_le_all_tail first rest h_chain_drop nr hnr_tail
          exact le_trans h_first_ge h_nr_ge_first
    -- Apply the weak loop lemma - doesn't require Pairwise (initial :: after)
    exact ok_deleteExtraNRs_loop_weak start initial after h_initial_lo h_after_ge hpw_after

  -- Step 4: Prove cross product: all elements of before are ≺ all elements of result
  have hcross : ∀ x ∈ before, ∀ y ∈ (result.fst :: result.snd), NR.before x y := by
    intro x hx y hy
    unfold NR.before
    -- x ∈ before means x.lo < start (from span property)
    have hx_lo : x.val.lo < start := by
      -- before = xs.takeWhile p where p checks lo < start
      have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
      have : before = xs.takeWhile p := by
        have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
        simp [split, before] at this ⊢
        exact this.1
      rw [this] at hx
      have := List.mem_takeWhile_imp hx
      simp only [p, decide_eq_true_eq] at this
      exact this

    -- y ∈ (result.fst :: result.snd) means y.lo ≥ start (from loop preservation)
    have hy_lo : start ≤ y.val.lo := by
      -- Use deleteExtraNRs_loop_lo_ge to show result elements have lo ≥ start
      have h_initial_lo : initial.val.lo = start := by
        simp [initial, curr, inserted, mkNR]
      have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
        intro nr hnr
        -- after = xs.dropWhile p where p checks lo < start
        -- Elements in dropWhile don't satisfy p, so nr.lo ≥ start
        have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
        have : after = xs.dropWhile p := by
          have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
          simp [split, after] at this ⊢
          exact this.2
        rw [this] at hnr
        -- Elements in dropWhile either failed the predicate or come after one that did
        by_cases h_empty : xs.dropWhile p = []
        · rw [h_empty] at hnr
          cases hnr
        · -- dropWhile is non-empty, so first element doesn't satisfy p
          have ⟨first, rest, h_cons⟩ := List.exists_cons_of_ne_nil h_empty
          rw [h_cons] at hnr
          -- Use chain/pairwise to show all elements have lo ≥ start
          have h_first_ge : start ≤ first.val.lo := by
            have h_first_head : (xs.dropWhile p).head? = some first := by
              rw [h_cons]; rfl
            have := List.head?_dropWhile_not (p := p) (l := xs)
            rw [h_first_head] at this
            simp at this
            simp only [p, decide_eq_false_iff_not, not_lt] at this
            exact this
          -- From Pairwise xs and chain properties, all elements after first also have lo ≥ start
          -- For now, use that all elements maintain monotonicity
          have h_chain : List.IsChain loLE xs := pairwise_before_implies_chain_loLE xs hpw
          have h_chain_drop : List.IsChain loLE (xs.dropWhile p) := by
            have h_decomp := List.takeWhile_append_dropWhile (p := p) (l := xs)
            rw [← h_decomp] at h_chain
            exact List.IsChain.right_of_append h_chain
          rw [h_cons] at h_chain_drop
          simp only [List.mem_cons] at hnr
          rcases hnr with hnr_eq | hnr_tail
          · rw [hnr_eq]
            exact h_first_ge
          · have h_nr_ge_first : first.val.lo ≤ nr.val.lo :=
              chain_head_le_all_tail first rest h_chain_drop nr hnr_tail
            exact le_trans h_first_ge h_nr_ge_first
      have h_loop_props := deleteExtraNRs_loop_lo_ge start initial after h_initial_lo h_after_ge
      simp only [List.mem_cons] at hy
      rcases hy with hy_eq | hy_tail
      · rw [hy_eq, h_loop_props.1]
      · exact h_loop_props.2 y hy_tail

    -- Need: x.hi + 1 < y.lo
    -- Strategy: use the gap hypothesis to show all x ∈ before have x.hi + 1 < start,
    -- and all y in result have y.lo ≥ start (from deleteExtraNRs_loop_lo_ge)
    have hgap_before : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := hgap
    rcases hgap_before with hempty | ⟨hne, hlast_gap⟩
    · -- before is empty, so x ∈ before is vacuous
      rw [hempty] at hx
      cases hx
    · -- Nonempty before with gap: last(before).hi + 1 < start
      -- From the last-gap, push gap to all elements of before
      have hall_before : ∀ x ∈ before, x.val.hi + 1 < start :=
        all_before_strict_before_start before start hpw_before hne hlast_gap

      -- Get: x.hi + 1 < start
      have hx_lt : x.val.hi + 1 < start := hall_before x hx

      -- Get: start ≤ y.lo (all loop outputs have lo ≥ start)
      have hy_ge : start ≤ y.val.lo := by
        simp [result] at hy
        rcases hy with rfl | hy_tail
        · -- y = result.fst
          have h_initial_lo : initial.val.lo = start := by
            simp [initial, curr, inserted, mkNR]
          have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
            intro nr hnr
            have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
            have : after = xs.dropWhile p := by
              have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
              simp [split, after] at this ⊢
              exact this.2
            rw [this] at hnr
            by_cases h_empty : xs.dropWhile p = []
            · rw [h_empty] at hnr; cases hnr
            · have ⟨first, rest, h_cons⟩ := List.exists_cons_of_ne_nil h_empty
              rw [h_cons] at hnr
              have h_first_ge : start ≤ first.val.lo := by
                have h_first_head : (xs.dropWhile p).head? = some first := by rw [h_cons]; rfl
                have := List.head?_dropWhile_not (p := p) (l := xs)
                rw [h_first_head] at this
                simp at this
                simp only [p, decide_eq_false_iff_not, not_lt] at this
                exact this
              have h_chain : List.IsChain loLE xs := pairwise_before_implies_chain_loLE xs hpw
              have h_chain_drop : List.IsChain loLE (xs.dropWhile p) := by
                have h_decomp := List.takeWhile_append_dropWhile (p := p) (l := xs)
                rw [← h_decomp] at h_chain
                exact List.IsChain.right_of_append h_chain
              rw [h_cons] at h_chain_drop
              simp only [List.mem_cons] at hnr
              rcases hnr with rfl | hnr_tail
              · exact h_first_ge
              · have h_nr_ge_first : first.val.lo ≤ nr.val.lo :=
                  chain_head_le_all_tail first rest h_chain_drop nr hnr_tail
                exact le_trans h_first_ge h_nr_ge_first
          have h_loop_props := deleteExtraNRs_loop_lo_ge start initial after h_initial_lo h_after_ge
          rw [h_loop_props.1]
        · -- y ∈ result.snd
          have h_initial_lo : initial.val.lo = start := by
            simp [initial, curr, inserted, mkNR]
          have h_after_ge : ∀ nr ∈ after, start ≤ nr.val.lo := by
            intro nr hnr
            have h_split_eq := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
            have : after = xs.dropWhile p := by
              have : split = (xs.takeWhile p, xs.dropWhile p) := h_split_eq
              simp [split, after] at this ⊢
              exact this.2
            rw [this] at hnr
            by_cases h_empty : xs.dropWhile p = []
            · rw [h_empty] at hnr; cases hnr
            · have ⟨first, rest, h_cons⟩ := List.exists_cons_of_ne_nil h_empty
              rw [h_cons] at hnr
              have h_first_ge : start ≤ first.val.lo := by
                have h_first_head : (xs.dropWhile p).head? = some first := by rw [h_cons]; rfl
                have := List.head?_dropWhile_not (p := p) (l := xs)
                rw [h_first_head] at this
                simp at this
                simp only [p, decide_eq_false_iff_not, not_lt] at this
                exact this
              have h_chain : List.IsChain loLE xs := pairwise_before_implies_chain_loLE xs hpw
              have h_chain_drop : List.IsChain loLE (xs.dropWhile p) := by
                have h_decomp := List.takeWhile_append_dropWhile (p := p) (l := xs)
                rw [← h_decomp] at h_chain
                exact List.IsChain.right_of_append h_chain
              rw [h_cons] at h_chain_drop
              simp only [List.mem_cons] at hnr
              rcases hnr with rfl | hnr_tail
              · exact h_first_ge
              · have h_nr_ge_first : first.val.lo ≤ nr.val.lo :=
                  chain_head_le_all_tail first rest h_chain_drop nr hnr_tail
                exact le_trans h_first_ge h_nr_ge_first
          have h_loop_props := deleteExtraNRs_loop_lo_ge start initial after h_initial_lo h_after_ge
          exact h_loop_props.2 y hy_tail

      -- Conclude: x.hi + 1 < start ≤ y.lo, so x.hi + 1 < y.lo
      exact lt_of_lt_of_le hx_lt hy_ge  -- Step 5: Apply pairwise_append
  exact pairwise_append NR.before before (result.fst :: result.snd)
    hpw_before hpw_result hcross

/-- If the (≤ start) split is empty, then the (< start) split is also empty.
This is because `< start` is strictly stronger than `≤ start`. -/
private lemma span_le_empty_implies_lt_empty (xs : List NR) (start : Int)
    (h_le_empty : (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst = []) :
    (List.span (fun nr => decide (nr.val.lo < start)) xs).fst = [] := by
  -- Convert both spans to takeWhile
  have h_le_eq := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo ≤ start)) (l := xs)
  have h_lt_eq := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo < start)) (l := xs)

  have h_le_take : xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) = [] := by
    have : (List.span (fun nr => decide (nr.val.lo ≤ start)) xs).fst =
           xs.takeWhile (fun nr => decide (nr.val.lo ≤ start)) := by
      rw [h_le_eq]
    rw [h_le_empty] at this
    exact this.symm

  -- Show takeWhile (< start) is also empty
  have h_lt_take : xs.takeWhile (fun nr => decide (nr.val.lo < start)) = [] := by
    cases hxs : xs with
    | nil => simp [List.takeWhile]
    | cons hd tl =>
      -- If takeWhile (≤ start) is empty, then hd doesn't satisfy (≤ start)
      have h_hd_not_le : ¬(hd.val.lo ≤ start) := by
        rw [hxs] at h_le_take
        simp [List.takeWhile] at h_le_take
        by_contra h_le
        simp [h_le] at h_le_take
      -- Therefore hd doesn't satisfy (< start) either
      have h_hd_not_lt : ¬(hd.val.lo < start) := fun h => h_hd_not_le (le_of_lt h)
      -- So takeWhile (< start) stops immediately
      simp [List.takeWhile, h_hd_not_lt]

  -- Convert back to span
  have : (List.span (fun nr => decide (nr.val.lo < start)) xs).fst =
         xs.takeWhile (fun nr => decide (nr.val.lo < start)) := by
    rw [h_lt_eq]
  rw [this, h_lt_take]

-- Helper lemma: getLast? = some implies getLast returns the same value
theorem getLast?_eq_some_getLast {α : Type*} {xs : List α} {x : α} (h : xs.getLast? = some x) :
    ∃ hne : xs ≠ [], xs.getLast hne = x := by
  cases xs with
  | nil => simp at h
  | cons hd tl =>
    have hne : hd :: tl ≠ [] := List.cons_ne_nil hd tl
    use hne
    simp [List.getLast?] at h
    cases tl with
    | nil =>
      simp [List.getLast] at h ⊢
      exact h
    | cons hd2 tl2 =>
      simp [List.getLast] at h ⊢
      exact h

/-- Safe version of internalAdd2 that uses the gap hypothesis to construct
a provably-Pairwise result via fromNRs instead of fromNRsUnsafe. -/
def internalAdd2_safe (s : RangeSetBlaze) (r : IntRange)
    (hgap_lt :
      let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  if hempty : r.hi < r.lo then
    s
  else
    let hle : r.lo ≤ r.hi := not_lt.mp hempty
    let xs := s.ranges
    have hok : List.Pairwise NR.before
        (internalAdd2NRs xs r.lo r.hi hle) :=
      ok_internalAdd2NRs xs r.lo r.hi hle s.ok hgap_lt
    fromNRs (internalAdd2NRs xs r.lo r.hi hle) hok

/-- Wrapper for internalAdd2_safe that accepts a gap hypothesis with (≤ start) predicate
and converts it to the (< start) predicate needed by internalAdd2_safe. -/
def internalAdd2_safe_from_le (s : RangeSetBlaze) (r : IntRange)
    (hgap_le :
      let split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
      let before := split.fst
      before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo) :
    RangeSetBlaze :=
  -- Convert the (≤) gap to (<) gap
  have hgap_lt : let split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
                 let before := split.fst
                 before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < r.lo := by
    cases hgap_le with
    | inl h_empty =>
        -- The (≤ start) split is empty, so the (< start) split is also empty
        left
        exact span_le_empty_implies_lt_empty s.ranges r.lo h_empty
    | inr h =>
        -- Nonempty (≤) split with a gap at its last element
        obtain ⟨hne_le, h_gap⟩ := h
        let split_le := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
        let before_le := split_le.fst
        let split_lt := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
        let before_lt := split_lt.fst

        -- Key: x = last of (≤ split) has x.hi + 1 < r.lo, so x.lo < r.lo
        let x := before_le.getLast hne_le
        have hx_gap : x.val.hi + 1 < r.lo := h_gap
        have hx_prop : x.val.lo ≤ x.val.hi := x.property
        have hx_lt : x.val.lo < r.lo := calc x.val.lo
          _ ≤ x.val.hi := hx_prop
          _ < x.val.hi + 1 := by omega
          _ < r.lo := hx_gap

        -- The two splits are equal (both cut at the same point)
        have before_eq : before_lt = before_le := by
          unfold before_lt split_lt before_le split_le
          simp only [List.span_eq_takeWhile_dropWhile]
          -- Prove that takeWhile (< r.lo) consumes exactly the same prefix as takeWhile (≤ r.lo)
          -- Key: the last element x of before_le satisfies x.lo < r.lo (proven above)
          -- Strategy: show both takeWhile operations stop at the same place
          have key : ∀ nr ∈ s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)), nr.val.lo < r.lo := by
            intro nr hnr
            -- All elements in before_le satisfy nr.lo ≤ r.lo (by definition of takeWhile)
            have h_le : nr.val.lo ≤ r.lo := by
              have h_pred := mem_takeWhile_satisfies (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges nr hnr
              exact of_decide_eq_true h_pred
            -- If nr = x (the last element), we have nr.lo < r.lo by hx_lt
            by_cases h_eq : nr = x
            · rw [h_eq]; exact hx_lt
            · -- If nr ≠ x, then nr appears before x in the list
              -- Since s.ranges is Pairwise NR.before and x is the last in before_le,
              -- we have nr.hi < x.lo, so nr.lo ≤ nr.hi < x.lo < r.lo
              sorry
          sorry

        -- Provide the gap witness
        right
        have hne_lt : before_lt ≠ [] := by intro h; rw [before_eq] at h; exact hne_le h
        use hne_lt
        show (split_lt.fst.getLast hne_lt).val.hi + 1 < r.lo
        simp only [split_lt, before_lt, split_le, before_le, before_eq]
        exact h_gap
  internalAdd2_safe s r hgap_lt



def internalAddC (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  let start := r.lo
  let stop := r.hi
  if _hstop : stop < start then
    s
  else
    let xs := s.ranges
    let split := List.span (fun nr => decide (nr.val.lo <= start)) xs
    let before := split.fst
    let after := split.snd
    match h_last : List.getLast? before with
    | none =>
        -- before is empty, so pass the trivial gap
        have h_before_nil : before = [] := by
          cases hb : before with
          | nil => rfl
          | cons hd tl =>
            rw [hb] at h_last
            simp [List.getLast?] at h_last
        have hgap : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
          left
          exact h_before_nil
        internalAdd2_safe_from_le s r hgap
    | some prev =>
        if hgap : decide (prev.val.hi + 1 < start) then
          -- prev has a gap, pass it along
          have hgap_proof : before = [] ∨ ∃ hne : before ≠ [], (before.getLast hne).val.hi + 1 < start := by
            right
            have hne : before ≠ [] := by
              intro h_empty
              simp [h_empty] at h_last
            use hne
            have ⟨hne', heq⟩ := getLast?_eq_some_getLast h_last
            have : hne = hne' := proof_irrel hne hne'
            rw [this, heq]
            exact of_decide_eq_true hgap
          internalAdd2_safe_from_le s r hgap_proof
        else
          if h_lt : prev.val.hi < stop then
            have h_nonempty : prev.val.lo ≤ prev.val.hi := prev.property
            have h_le : prev.val.hi ≤ stop := le_of_lt h_lt
            have hle : prev.val.lo ≤ stop := le_trans h_nonempty h_le
            let extendedList :=
              List.dropLast before ++ (mkNR prev.val.lo stop hle :: after)
            let mergedSet := fromNRsUnsafe extendedList
            let target : IntRange := { lo := prev.val.lo, hi := stop }
            delete_extra mergedSet target
          else
            s

/-- Invariant preservation: `deleteExtraNRs` maintains `Pairwise NR.before`.The proof structure:
- Span xs into (before, after) at start
- If after is empty: result is xs, trivially Pairwise
- If after = curr :: tail:
  * Construct initial range from curr.lo to max curr.hi stop
  * Apply ok_deleteExtraNRs_loop to (initial, tail)
  * Combine: need Pairwise on (before ++ loop_result)
    - This requires showing that all elements of before are ≺ to loop_result.fst
    - Key: before all have lo < start, initial.lo = curr.lo ≥ start (from span property)
    - From Pairwise on original xs, last of before is ≺ curr
    - Need to show: last of before is ≺ initial (follows since initial extends curr)
-/

private lemma ok_deleteExtraNRs
    (xs : List NR) (start stop : Int)
    (_h : start ≤ stop)
    (hpw : List.Pairwise NR.before xs)
    (hstop : ∀ nr ∈ xs, nr.val.lo ≥ start → stop + 1 < nr.val.lo) :
    List.Pairwise NR.before (deleteExtraNRs xs start stop) := by
  unfold deleteExtraNRs
  simp only []
  split
  · rename_i h_nil
    -- rest = []
    exact hpw
  · rename_i curr tail h_cons
    -- rest = curr :: tail
    -- Get the split structure
    set split := List.span (fun nr => decide (nr.val.lo < start)) xs with hsplit
    set before := split.fst with hbefore
    set rest := split.snd with hrest

    -- Reconstruct xs from before ++ rest
    have h_xs_decomp : xs = before ++ rest := by
      have := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo < start)) (l := xs)
      calc xs
        _ = xs.takeWhile (fun nr => decide (nr.val.lo < start)) ++
            xs.dropWhile (fun nr => decide (nr.val.lo < start)) := by
          exact (List.takeWhile_append_dropWhile (p := fun nr => decide (nr.val.lo < start)) (l := xs)).symm
        _ = split.fst ++ split.snd := by simp [split]
        _ = before ++ rest := rfl

    -- Extract Pairwise on before and rest
    have hpw_before : List.Pairwise NR.before before := by
      rw [h_xs_decomp] at hpw
      exact pairwise_append_left NR.before before rest hpw

    have hpw_rest : List.Pairwise NR.before rest := by
      have h_eq : xs = before ++ rest := h_xs_decomp
      rw [h_eq] at hpw
      clear h_eq h_xs_decomp
      revert hpw
      induction before with
      | nil => intro hpw; exact hpw
      | cons x xs ih =>
          intro hpw
          cases hpw with
          | cons _ hrest => exact ih hrest

    -- rest = curr :: tail from h_cons
    have h_rest_eq : rest = curr :: tail := h_cons
    rw [h_rest_eq] at hpw_rest

    -- Construct initial and result
    set initialHi := max curr.val.hi stop with hinitialHi
    have hcurr : curr.val.lo ≤ curr.val.hi := curr.property
    have hmax : curr.val.hi ≤ initialHi := le_max_left _ _
    have hinit : curr.val.lo ≤ initialHi := le_trans hcurr hmax
    set initial := mkNR curr.val.lo initialHi hinit with hinitial
    set res := deleteExtraNRs_loop initial tail with hres

    -- Need to show: Pairwise (before ++ res.fst :: res.snd)
    -- Use pairwise_append helper
    apply pairwise_append NR.before
    · exact hpw_before
    · -- Pairwise on (res.fst :: res.snd)
      apply ok_deleteExtraNRs_loop curr.val.lo initial tail
      · simp [initial, mkNR]
      · -- ∀ nr ∈ tail, curr.lo ≤ nr.lo
        intro nr hmem
        -- From Pairwise (curr :: tail), we have curr ≺ nr
        cases hpw_rest with
        | cons h_curr_tail _ =>
            unfold NR.before at h_curr_tail
            have : curr.val.hi + 1 < nr.val.lo := h_curr_tail nr hmem
            have : curr.val.lo ≤ curr.val.hi := curr.property
            omega
      · -- Pairwise (initial :: tail)
        -- initial extends curr (same lo, larger hi), so initial ≺ z for all z that curr ≺ z
        cases hpw_rest with
        | cons h_curr_tail hpw_tail =>
            constructor
            · intro z hz
              unfold NR.before at *
              have h_curr_z : curr.val.hi + 1 < z.val.lo := h_curr_tail z hz
              have h_initial_lo : initial.val.lo = curr.val.lo := by simp [initial, mkNR]
              have h_initial_hi : initial.val.hi = max curr.val.hi stop := by
                simp [initial, mkNR, initialHi]
              rw [h_initial_hi]
              -- Need max curr.hi stop + 1 < z.lo
              -- We have curr.hi + 1 < z.lo
              by_cases hc : curr.val.hi ≤ stop
              · -- max = stop, need stop + 1 < z.lo
                have : max curr.val.hi stop = stop := max_eq_right hc
                rw [this]
                -- We need stop + 1 < z.lo
                -- From Pairwise curr :: tail, we know curr.hi + 1 < z.lo
                -- We have stop ≥ curr.hi
                -- So we need: stop < z.lo
                -- This is true because z.lo > curr.hi + 1 > curr.hi and we should have stop ≤ curr.hi typically
                -- But actually, this reveals that the lemma needs a precondition!
                -- The issue: when deleteExtraNRs is called, we need stop < (first element of rest).lo
                -- OR we need to accept that initial won't satisfy Pairwise and prove a different lemma

               -- Alternative approach: prove that if stop >= z.lo - 1, then the loop merges
                -- Actually, let's just constrain to the case where it's valid:
                -- We need z.lo ≥ start (from span) and we have h : start ≤ stop
                -- From curr ≺ z: curr.hi + 1 < z.lo, so z.lo ≥ curr.hi + 2
                -- If stop ≥ z.lo - 1, we'd need to merge, contradicting that z is separate
                -- So we must have stop < z.lo - 1, i.e., stop + 1 < z.lo
                -- But this requires stop ≤ curr.hi essentially for the list to make sense

                -- We need stop + 1 < z.lo
                -- z ∈ tail, and tail is part of rest = dropWhile (< start)
                -- So z.lo ≥ start (doesn't satisfy < start predicate)
                -- Apply hstop precondition: ∀ nr ∈ xs, nr.lo ≥ start → stop + 1 < nr.lo
                have hz_in_rest : z ∈ rest := by
                  rw [h_rest_eq]
                  simp [hz]
                have hz_in_xs : z ∈ xs := by
                  rw [h_xs_decomp]
                  simp [hz_in_rest]
                have hz_lo_ge : z.val.lo ≥ start := by
                  -- z ∈ tail, curr :: tail = rest = dropWhile (< start)
                  -- From Pairwise (curr :: tail) we have curr ≺ z, so z.lo > curr.hi ≥ curr.lo
                  -- And curr.lo ≥ start because curr is first element not dropped
                  have : curr.val.hi + 1 < z.val.lo := h_curr_tail z hz
                  have : curr.val.lo ≤ curr.val.hi := curr.property
                  -- Need to show curr.lo ≥ start
                  -- rest = dropWhile (< start), and curr is first element of rest
                  -- So curr doesn't satisfy (< start), meaning ¬(curr.lo < start), i.e., curr.lo ≥ start
                  have h_curr_ge : curr.val.lo ≥ start := by
                    -- rest = dropWhile (< start) and curr :: tail = rest
                    -- The first element of dropWhile result doesn't satisfy the predicate
                    have h_rest_drop : rest = xs.dropWhile (fun nr => decide (nr.val.lo < start)) := by
                      have h_span := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo < start)) (l := xs)
                      calc rest
                        _ = split.snd := rfl
                        _ = (List.span (fun nr => decide (nr.val.lo < start)) xs).snd := by rw [← hsplit]
                        _ = xs.dropWhile (fun nr => decide (nr.val.lo < start)) := congrArg Prod.snd h_span
                    have h_dropwhile_eq : xs.dropWhile (fun nr => decide (nr.val.lo < start)) = curr :: tail := by
                      rw [← h_rest_eq, h_rest_drop]
                    have h_not_sat := dropWhile_head_not_satisfies (fun nr => decide (nr.val.lo < start)) xs curr tail h_dropwhile_eq
                    simp at h_not_sat
                    omega
                  omega
                exact hstop z hz_in_xs hz_lo_ge
              · -- max = curr.hi, so we're done
                have : max curr.val.hi stop = curr.val.hi := max_eq_left (le_of_not_ge hc)
                rw [this]
                exact h_curr_z
            · exact hpw_tail
    · -- ∀ x ∈ before, ∀ y ∈ (res.fst :: res.snd), x ≺ y
      intro x hx y hy
      unfold NR.before
      -- Strategy: elements in before have lo < start (from span property)
      -- elements in result come from initial and tail, all have lo ≥ start
      -- From original Pairwise, if before is non-empty, last of before ≺ first of rest (curr)
      -- All elements of before ≺ curr (from Pairwise on xs)
      -- curr.lo = initial.lo and res comes from processing (initial, tail)
      -- So res.fst.lo ≥ initial.lo = curr.lo ≥ start
      -- And x.lo < start (from span), x.hi < start - 1 (or close)
      -- Actually, we need x.hi + 1 < y.lo

      -- First: show x.lo < start
      have hx_lo : x.val.lo < start := by
        -- x ∈ before, and before = takeWhile (λ nr, nr.lo < start) xs
        have h_span := List.span_eq_takeWhile_dropWhile
          (p := fun nr => decide (nr.val.lo < start)) (l := xs)
        have : before = xs.takeWhile (fun nr => decide (nr.val.lo < start)) := by
          calc before
            _ = split.fst := rfl
            _ = (List.span (fun nr => decide (nr.val.lo < start)) xs).fst := by rw [← hsplit]
            _ = xs.takeWhile (fun nr => decide (nr.val.lo < start)) := congrArg Prod.fst h_span
        rw [this] at hx
        have := mem_takeWhile_satisfies (fun nr => decide (nr.val.lo < start)) xs x hx
        simp at this
        exact this

      -- Second: show y.lo ≥ start
      -- y ∈ (res.fst :: res.snd), and res comes from loop on (initial, tail)
      -- Use helper: loop preserves that all elements have lo ≥ curr.lo
      have h_initial_lo : initial.val.lo = curr.val.lo := by simp [initial, mkNR]
      have h_tail_lo : ∀ nr ∈ tail, curr.val.lo ≤ nr.val.lo := by
        intro nr hmem
        cases hpw_rest with
        | cons h_curr_tail _ =>
            unfold NR.before at h_curr_tail
            have : curr.val.hi + 1 < nr.val.lo := h_curr_tail nr hmem
            have : curr.val.lo ≤ curr.val.hi := curr.property
            omega
      have h_loop_prop := deleteExtraNRs_loop_lo_ge curr.val.lo initial tail h_initial_lo h_tail_lo

      -- Now combine: x.hi + 1 < curr.lo ≤ y.lo
      -- From Pairwise on xs = before ++ rest, we get ∀ a ∈ before, ∀ b ∈ rest, a ≺ b
      have h_x_before_curr : x ≺ curr := by
        have : ∀ a ∈ before, ∀ b ∈ rest, a ≺ b := by
          rw [h_xs_decomp] at hpw
          exact pairwise_append_cross NR.before before rest hpw
        rw [h_rest_eq] at this
        exact this x hx curr (by simp)

      have h_curr_y : curr.val.lo ≤ y.val.lo := by
        cases hy with
        | head =>
            -- y = res.fst, and res.fst.lo = curr.lo, so curr.lo ≤ y.lo becomes res.fst.lo ≤ res.fst.lo
            rw [h_loop_prop.left]
        | tail _ hmem =>
            exact h_loop_prop.right y hmem

      calc x.val.hi + 1
        _ < curr.val.lo := by unfold NR.before at h_x_before_curr; exact h_x_before_curr
        _ ≤ y.val.lo := h_curr_y

private lemma deleteExtraNRs_sets_after_splice_of_chain
    (xs : List NR) (start stop : Int) (h : start ≤ stop)
    (hchain : List.IsChain loLE xs) :
    let split := List.span (fun nr => decide (nr.val.lo < start)) xs
    let before := split.fst
    let after := split.snd
    let inserted := mkNR start stop h
  listSet (deleteExtraNRs (before ++ inserted :: after) start stop) =
      listSet before ∪ inserted.val.toSet ∪ listSet after := by
  classical
  -- Bind names so their definitional equalities are available.
  set split := List.span (fun nr => decide (nr.val.lo < start)) xs with hsplit
  set before := split.fst with hbefore
  set after := split.snd with hafter
  set inserted := mkNR start stop h with hinserted
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)

  -- span facts on xs (use the symmetric orientation so congrArg doesn’t collapse)
  have h_span_symm :=
    (List.span_eq_takeWhile_dropWhile (p := p) (l := xs)).symm
  have h_take_split' :
      xs.takeWhile p = before :=
    (congrArg Prod.fst h_span_symm).trans hbefore.symm
  have h_drop_split' :
      xs.dropWhile p = after :=
    (congrArg Prod.snd h_span_symm).trans hafter.symm
  -- keep the original directions used later
  have h_take_split : before = xs.takeWhile p := h_take_split'.symm
  have h_drop_split : after = xs.dropWhile p := h_drop_split'.symm

  -- every elt of before satisfies p
  have h_take_all_aux :
      ∀ {ys : List NR} {nr : NR}, nr ∈ ys.takeWhile p → p nr = true := by
    intro ys; induction ys with
    | nil => intro nr hmem; cases hmem
    | cons x xs ih =>
        intro nr hmem
        cases hpx : p x with
        | false =>
          simp [List.takeWhile, hpx] at hmem
        | true  =>
          have := hmem
          simp [List.takeWhile, hpx] at this
          rcases this with hnr | hmem'
          · subst hnr; simp [hpx]
          · exact ih hmem'
  have h_before_all : ∀ nr ∈ before, p nr = true := by
    intro nr hmem
    -- rewrite membership: before = xs.takeWhile p
    have hmem_split : nr ∈ split.fst := by simpa [hbefore] using hmem
    have : nr ∈ xs.takeWhile p := by
      simpa [h_take_split, hsplit] using hmem_split
    exact h_take_all_aux this

  -- inserted.lo = start, so it breaks the predicate
  have h_inserted_false : p inserted = false := by
    simp [p, hinserted, mkNR]

  -- Span of the *spliced* list is exactly (before, inserted :: after)
  have h_span_splice :
      List.span p (before ++ inserted :: after)
        = (before, inserted :: after) := by
    have htake :
        (before ++ inserted :: after).takeWhile p = before :=
      takeWhile_append_of_all p before inserted after
        h_before_all h_inserted_false
    have hdrop :
        (before ++ inserted :: after).dropWhile p = inserted :: after :=
      dropWhile_append_of_all p before inserted after
        h_before_all h_inserted_false
    simp [List.span_eq_takeWhile_dropWhile, htake, hdrop]

  -- From the chain invariant on xs we get start ≤ lo for every elt of `after`
  have h_suffix :
      ∀ nr ∈ split.snd, start ≤ nr.val.lo := by
    simpa [hsplit] using span_suffix_all_ge_start_of_chain xs start hchain
  have h_ge_after_all : ∀ nr ∈ after, start ≤ nr.val.lo := by
    intro nr hmem
    have hmem_split : nr ∈ split.snd := by simpa [hafter] using hmem
    exact h_suffix nr hmem_split

  -- Unfold deleteExtraNRs and show it reduces to the cons case
  show listSet (deleteExtraNRs (before ++ inserted :: after) start stop) =
       listSet before ∪ inserted.val.toSet ∪ listSet after

  unfold deleteExtraNRs
  -- The span on (before ++ inserted :: after) with predicate p gives (before, inserted :: after)
  -- We need to convince Lean the match takes the cons branch
  have h_span_rw : List.span p (before ++ inserted :: after) = (before, inserted :: after) := h_span_splice

  -- Rewrite the span in the definition
  conv_lhs =>
    arg 1
    rw [h_span_rw]

  -- Now the match sees (inserted :: after) so it takes the cons branch
  simp only []

  -- Set up the initial value that appears in the cons branch
  set initialHi := max inserted.val.hi stop
  have h_inserted_le : inserted.val.lo ≤ inserted.val.hi := inserted.property
  have h_max_ge : inserted.val.hi ≤ initialHi := le_max_left _ _
  have h_initial_valid : inserted.val.lo ≤ initialHi := le_trans h_inserted_le h_max_ge
  set initial := mkNR inserted.val.lo initialHi h_initial_valid
  set res := deleteExtraNRs_loop initial after

  -- The result is: before ++ res.fst :: res.snd
  have h_result : listSet (before ++ res.fst :: res.snd) =
                  listSet before ∪ listSet (res.fst :: res.snd) := listSet_append _ _
  rw [h_result]

  -- Apply the loop lemma
  have h_initial_lo : initial.val.lo = start := by
    simp [initial, mkNR, inserted]
  have h_loop := deleteExtraNRs_loop_sets start after initial h_initial_lo h_ge_after_all
  rw [h_loop]

  -- Now we have: listSet before ∪ (initial.toSet ∪ listSet after)
  -- Need to show this equals: listSet before ∪ inserted.toSet ∪ listSet after
  -- Note: initial has lo = inserted.lo = start, hi = max inserted.hi stop = max stop stop = stop
  have h_initial_eq : initial.val.toSet = inserted.val.toSet := by
    have h_ins_hi : inserted.val.hi = stop := by simp [inserted, mkNR]
    have h_init_hi : initialHi = max stop stop := by simp [initialHi, h_ins_hi]
    have : initialHi = stop := by simp [h_init_hi]
    simp [initial, inserted, mkNR, IntRange.toSet, this]

  rw [h_initial_eq, Set.union_assoc]

-- Bridge lemma: listSet here is the same as listToSet in Basic.lean
private lemma listSet_eq_listToSet (rs : List NR) :
    listSet rs = rs.foldr (fun r acc => r.val.toSet ∪ acc) ∅ := rfl

lemma internalAdd2_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd2 s r).toSet = s.toSet ∪ r.toSet := by
  classical
  unfold internalAdd2
  by_cases hempty : r.hi < r.lo
  · -- Empty range case
    have hEmpty : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    simp [hempty, hEmpty]
  · -- Non-empty range case
    have hle : r.lo ≤ r.hi := not_lt.mp hempty
    simp only [hempty, dite_false]

    -- Use the chain invariant
    have hchain : List.Pairwise NR.before s.ranges := s.ok
    have hchain_loLE : List.IsChain loLE s.ranges := pairwise_before_implies_chain_loLE s.ranges hchain

    -- The result is fromNRsUnsafe (internalAdd2NRs s.ranges r.lo r.hi hle)
    -- internalAdd2NRs does span, then deleteExtraNRs on the spliced list
    unfold internalAdd2NRs

    -- Set up the split
    set split := List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges
    set before := split.fst
    set after := split.snd
    set inserted := mkNR r.lo r.hi hle

    -- Apply the splice lemma
    have h_splice := deleteExtraNRs_sets_after_splice_of_chain s.ranges r.lo r.hi hle hchain_loLE

    -- Convert fromNRsUnsafe result to listSet
    have h_result_toSet : (fromNRsUnsafe (deleteExtraNRs (before ++ inserted :: after) r.lo r.hi)).toSet =
                          listSet (deleteExtraNRs (before ++ inserted :: after) r.lo r.hi) := by
      unfold fromNRsUnsafe
      rw [RangeSetBlaze.toSet_eq_listToSet]
      rfl

    -- Now we have result.toSet = listSet (deleteExtraNRs ...) and h_splice says what that equals
    -- Goal after rewriting should be to show listSet before ∪ inserted.toSet ∪ listSet after = s.toSet ∪ r.toSet
    rw [h_result_toSet, h_splice]

    have h_inserted_eq : inserted.val.toSet = r.toSet := by
      simp [inserted, mkNR, IntRange.toSet]

    -- Decompose s.ranges via span
    have h_ranges_eq : s.ranges = before ++ after := by
      have h_span := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo < r.lo)) (l := s.ranges)
      have h_fst : before = (List.takeWhile (fun nr => decide (nr.val.lo < r.lo)) s.ranges) := by
        calc before
          _ = split.fst := rfl
          _ = (List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges).fst := rfl
          _ = (List.takeWhile (fun nr => decide (nr.val.lo < r.lo)) s.ranges) := congrArg Prod.fst h_span
      have h_snd : after = (List.dropWhile (fun nr => decide (nr.val.lo < r.lo)) s.ranges) := by
        calc after
          _ = split.snd := rfl
          _ = (List.span (fun nr => decide (nr.val.lo < r.lo)) s.ranges).snd := rfl
          _ = (List.dropWhile (fun nr => decide (nr.val.lo < r.lo)) s.ranges) := congrArg Prod.snd h_span
      rw [h_fst, h_snd]
      exact (List.takeWhile_append_dropWhile (p := fun nr => decide (nr.val.lo < r.lo)) (l := s.ranges)).symm

    -- The LHS still has span on (before ++ after), need to show it gives (before, after)
    have h_span_reconstruct : List.span (fun nr => decide (nr.val.lo < r.lo)) (before ++ after) = (before, after) := by
      -- before ++ after = s.ranges by h_ranges_eq, and span on s.ranges = (before, after) by definition
      rw [← h_ranges_eq]

    rw [h_inserted_eq, RangeSetBlaze.toSet_eq_listToSet, h_ranges_eq]
    simp only [h_span_reconstruct]
    -- listSet and listToSet from Basic are definitionally equal - both foldr with ∪
    -- listSet (before ++ after) = listSet before ∪ listSet after
    show listSet before ∪ r.toSet ∪ listSet after = listSet (before ++ after) ∪ r.toSet
    rw [listSet_append]
    ac_rfl/-– Spec for the “extend previous” branch of `internalAddC`.
Assumes: non-empty input `r`, we matched `some prev`, no gap (`¬ prev.hi + 1 < r.lo`),
and `prev.hi < r.hi` so we actually extend. -/
lemma internalAddC_extendPrev_toSet
    (s : RangeSetBlaze) (r : IntRange)
    (prev : NR)
    (h_nonempty : r.lo ≤ r.hi)
    (h_last :
      List.getLast?
        (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges)
      = some prev)
    (h_gap : ¬ prev.val.hi + 1 < r.lo)
    (h_extend : prev.val.hi < r.hi) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  -- The extend branch: replace prev with extended range from prev.lo to r.hi, then delete_extra
  unfold internalAddC

  -- Simplify the outer if
  have h_not_empty : ¬(r.hi < r.lo) := by
    intro h
    have := lt_of_le_of_lt h_nonempty h
    linarith
  simp only [h_not_empty]  -- Get the span result
  set split := List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges
  set before := split.fst
  set after := split.snd

  -- Match gives some prev
  have h_getLast : List.getLast? before = some prev := by
    calc List.getLast? before
      _ = List.getLast? split.fst := rfl
      _ = List.getLast? (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).fst := rfl
      _ = List.getLast? (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo))) := by
        congr 1
        exact congrArg Prod.fst (List.span_eq_takeWhile_dropWhile _ _)
      _ = some prev := h_last

  -- Gap check is false
  have h_gap_decide : decide (prev.val.hi + 1 < r.lo) = false := by
    simp [h_gap]

  -- Navigate through the match and ifs to reach the extend branch
  simp [List.span_eq_takeWhile_dropWhile]
  -- Split on the match
  split
  · -- Case: getLast? = none, but we know h_getLast says it's some prev
    rename_i h_none
    have h_eq : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges := by
      exact congrArg Prod.fst (List.span_eq_takeWhile_dropWhile _ _)
    have : List.getLast? (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges) = none := by
      rw [←h_eq]; exact h_none
    rw [h_last] at this
    simp at this
  · -- Case: getLast? = some prev'
    rename_i prev' h_some
    -- Show prev = prev'
    have : prev = prev' := by
      have h_eq : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                  List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges := by
        exact congrArg Prod.fst (List.span_eq_takeWhile_dropWhile _ _)
      have : some prev = some prev' := by
        calc some prev
          _ = List.getLast? (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges) := h_last.symm
          _ = List.getLast? (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 := by rw [h_eq]
          _ = some prev' := h_some
      injection this
    subst this
    -- Now handle the if statements
    simp [h_gap, h_extend]
    -- The proof for this case is complex and remains to be completed
    sorry

-- Main correctness theorem for internal AddC
theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  ·
    have hEmptySet : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    simp [internalAddC, hempty, hEmptySet, Set.union_comm]
  ·
    classical
    have hnonempty : r.lo ≤ r.hi := not_lt.mp hempty
    generalize hLast :
        List.getLast?
          (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges) =
        optPrev
    cases optPrev with
    | none =>
        have : internalAddC s r = internalAdd2 s r := by
          simp [internalAddC, hempty, List.span_eq_takeWhile_dropWhile]
          split
          · rfl
          · rename_i prev h_last
            exfalso
            have heq : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                       List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges := by
              rw [List.span_eq_takeWhile_dropWhile]
            have : (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).getLast? = some prev := by
              rw [←heq]; exact h_last
            rw [hLast] at this
            simp at this
        rw [this]
        exact internalAdd2_toSet s r
    | some prev =>
        by_cases hgap : prev.val.hi + 1 < r.lo
        ·
          have : internalAddC s r = internalAdd2 s r := by
            simp [internalAddC, hempty, List.span_eq_takeWhile_dropWhile]
            split
            · rename_i h_last
              exfalso
              have heq : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                         List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges := by
                rw [List.span_eq_takeWhile_dropWhile]
              have : (List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).getLast? = none := by
                rw [←heq]; exact h_last
              rw [hLast] at this
              simp at this
            · rename_i prev' h_last
              have heq : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).1 =
                         List.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges := by
                rw [List.span_eq_takeWhile_dropWhile]
              have : prev = prev' := by
                have : some prev = some prev' := by rw [←hLast, ←heq, h_last]
                injection this
              subst this
              simp [hgap]
              -- Show internalAdd2_safe_from_le = internalAdd2 in this case
              unfold internalAdd2_safe_from_le
              rfl
          rw [this]
          exact internalAdd2_toSet s r
        ·
          -- Remaining branch: no gap (¬hgap) between prev and r
          -- Need to case-split on whether prev.hi < r.hi
          by_cases h_extend : prev.val.hi < r.hi
          · -- prev extends into r: use the extend lemma
            exact internalAddC_extendPrev_toSet s r prev hnonempty hLast (by exact hgap) h_extend
          · -- r is covered by prev: internalAddC returns s unchanged
            -- Need to show s.toSet = s.toSet ∪ r.toSet
            -- When ¬hgap and ¬h_extend, internalAddC returns s
            have hbranch : internalAddC s r = s := by
              unfold internalAddC
              simp [hempty, List.span_eq_takeWhile_dropWhile]
              split
              · rename_i h_contra
                -- h_contra says the getLast? from the (now-simplified) span is none
                -- but hLast says takeWhile.getLast? is some prev
                -- After simp with span_eq_, span.1 became takeWhile, so they're the same
                simp [hLast] at h_contra
              · rename_i prev' h_match
                -- Similarly, h_match says (simplified span).getLast? = some prev'
                -- and hLast says takeWhile.getLast? = some prev
                have hprev_eq : prev = prev' := by
                  simp [hLast] at h_match
                  exact h_match
                subst hprev_eq
                simp [hgap, h_extend]
            rw [hbranch]

            -- Show that r.toSet ⊆ s.toSet
            have h_r_covered : r.toSet ⊆ s.toSet := by
              -- prev is in s.ranges (from getLast? of takeWhile)
              -- ¬hgap: prev.hi + 1 ≥ r.lo, so r.lo ≤ prev.hi + 1
              -- ¬h_extend: prev.hi ≥ r.hi
              -- hnonempty: r.lo ≤ r.hi

              -- First, establish the bounds: r.lo ≤ prev.hi and r.hi ≤ prev.hi
              have h_r_lo_le_prev_hi : r.lo ≤ prev.val.hi + 1 := not_lt.mp hgap
              have h_r_hi_le_prev_hi : r.hi ≤ prev.val.hi := not_lt.mp h_extend

              -- We also need: prev.lo ≤ r.lo
              -- This comes from the fact that prev is in the "before" part of the span
              -- where we span by (nr.lo ≤ r.lo), so prev.lo ≤ r.lo
              have h_prev_lo_le_r_lo : prev.val.lo ≤ r.lo := by
                -- prev came from getLast? of takeWhile (fun nr => decide (nr.lo ≤ r.lo))
                -- So prev must satisfy the predicate nr.lo ≤ r.lo
                let tw := s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo))
                have h_tw_nonempty : tw ≠ [] := by
                  intro h_empty
                  have : tw.getLast? = none := by simp [h_empty]
                  rw [this] at hLast
                  cases hLast
                have h_prev_mem : prev ∈ tw := by
                  have h_last : tw.getLast h_tw_nonempty = prev := by
                    have := List.getLast?_eq_getLast h_tw_nonempty
                    rw [this] at hLast
                    cases hLast
                    rfl
                  rw [← h_last]
                  exact List.getLast_mem h_tw_nonempty
                have h_pred := mem_takeWhile_satisfies (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges prev h_prev_mem
                exact of_decide_eq_true h_pred

              -- Now show r.toSet ⊆ prev.val.toSet
              have h_r_subset_prev : r.toSet ⊆ prev.val.toSet := by
                intro x hx
                simp [IntRange.toSet] at hx ⊢
                constructor
                · calc x
                    _ ≥ r.lo := hx.1
                    _ ≥ prev.val.lo := h_prev_lo_le_r_lo
                · calc x
                    _ ≤ r.hi := hx.2
                    _ ≤ prev.val.hi := h_r_hi_le_prev_hi

              -- And prev.val.toSet ⊆ s.toSet because prev ∈ s.ranges
              have h_prev_in_s : prev.val.toSet ⊆ s.toSet := by
                -- prev is in s.ranges (from takeWhile)
                let tw := s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo))
                have h_tw_nonempty : tw ≠ [] := by
                  intro h_empty
                  have : tw.getLast? = none := by simp [h_empty]
                  rw [this] at hLast
                  cases hLast
                have h_prev_mem_tw : prev ∈ tw := by
                  have h_last : tw.getLast h_tw_nonempty = prev := by
                    have := List.getLast?_eq_getLast h_tw_nonempty
                    rw [this] at hLast
                    cases hLast
                    rfl
                  rw [← h_last]
                  exact List.getLast_mem h_tw_nonempty
                have h_prev_mem_ranges : prev ∈ s.ranges := by
                  apply List.takeWhile_subset
                  exact h_prev_mem_tw
                have h_listSet := nr_mem_ranges_subset_listSet s.ranges prev h_prev_mem_ranges
                rw [RangeSetBlaze.toSet_eq_listToSet]
                convert h_listSet

              exact Set.Subset.trans h_r_subset_prev h_prev_in_s

            -- Therefore s.toSet ∪ r.toSet = s.toSet
            rw [Set.union_eq_self_of_subset_right h_r_covered]

open Classical
open IntRange

end RangeSetBlaze
