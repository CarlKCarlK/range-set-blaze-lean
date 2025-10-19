import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-
`Algo C` reimplementation that mirrors the production Rust insertion logic
while operating directly on the `NR` and `RangeSetBlaze` structures.
All required invariants are deferred with `sorry` placeholders so the
module builds while proofs are filled in later.
-/

private def mkNRUnsafe (lo hi : Int) : NR :=
  Subtype.mk { lo := lo, hi := hi } (by sorry)

private def mkNR (lo hi : Int) (h : lo ≤ hi) : NR :=
  ⟨{ lo := lo, hi := hi }, h⟩

private def fromNRsUnsafe (xs : List NR) : RangeSetBlaze :=
  { ranges := xs, ok := by sorry }

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
    match List.getLast? before with
    | none =>
        internalAdd2 s r
    | some prev =>
        if decide (prev.val.hi + 1 < start) then
          internalAdd2 s r
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

/-- If ranges satisfy `Pairwise before`, they also satisfy `Chain' loLE`.
The `before` relation (no gap/overlap) implies `lo` ordering. -/
private lemma pairwise_before_implies_chain_loLE (xs : List NR)
    (h : List.Pairwise NR.before xs) :
    List.Chain' loLE xs := by
  induction xs with
  | nil => constructor
  | cons x xs ih =>
      cases xs with
      | nil => constructor
      | cons y ys =>
          cases h with
          | cons hxy hrest =>
              have hchain_tail : List.Chain' loLE (y :: ys) := by
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
    (hchain : List.Chain' loLE (y :: ys)) :
    ∀ z ∈ ys, y.val.lo ≤ z.val.lo := by
  revert y
  induction ys with
  | nil =>
      intro y _ z hz
      cases hz
  | cons a ys ih =>
      intro y hchain z hz
      have h_y_le_a : y.val.lo ≤ a.val.lo := by
        simpa [loLE] using List.Chain'.rel_head (R := loLE) hchain
      have htail : List.Chain' loLE (a :: ys) :=
        List.Chain'.tail hchain
      have hz_cases : z = a ∨ z ∈ ys := by
        simpa using hz
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
    (hchain : List.Chain' loLE xs) :
    let p : NR → Bool := fun nr => decide (nr.val.lo < start)
    let split := List.span p xs
    ∀ nr ∈ split.snd, start ≤ nr.val.lo := by
  classical
  intro p split
  have h_span : split = (xs.takeWhile p, xs.dropWhile p) :=
    List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
  have h_take : split.fst = xs.takeWhile p := by
    simpa [split] using congrArg Prod.fst h_span
  have h_drop : split.snd = xs.dropWhile p := by
    simpa [split] using congrArg Prod.snd h_span
  have h_decomp : split.fst ++ split.snd = xs := by
    have := List.takeWhile_append_dropWhile (p := p) (l := xs)
    simpa [h_take, h_drop]
  intro nr hmem
  have hchain_append :
      List.Chain' loLE (split.fst ++ split.snd) := by
    simpa [h_decomp] using hchain
  have hchain_suffix :
      List.Chain' loLE split.snd :=
    List.Chain'.right_of_append (l₁ := split.fst)
      (l₂ := split.snd) hchain_append
  cases hA : split.snd with
  | nil =>
      simpa [hA] using hmem
  | cons y ys =>
      have hmem_cons : nr = y ∨ nr ∈ ys := by
        simpa [hA] using hmem
      have hy_head? :
          (xs.dropWhile p).head? = some y := by
        have : split.snd.head? = some y := by
          simpa [hA]
        simpa [h_drop] using this
      have hy_false : p y = false := by
        have := List.head?_dropWhile_not (p := p) (l := xs)
        simpa [hy_head?] using this
      have hy_not_lt : ¬ y.val.lo < start := by
        intro hy_lt
        have : p y = true := by
          simpa [p, hy_lt]
        simpa [this] using hy_false
      have h_start_le_y : start ≤ y.val.lo :=
        not_lt.mp hy_not_lt
      have hchain_after : List.Chain' loLE (y :: ys) := by
        simpa [hA] using hchain_suffix
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
          simpa [hmerged_def, mkNR, hcurlo]
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
        simp [hmerge, hmerge', hloop_eq, listSet_cons, Set.union_left_comm,
          Set.union_assoc]

private lemma deleteExtraNRs_sets_after_splice_of_chain
    (xs : List NR) (start stop : Int) (h : start ≤ stop)
    (hchain : List.Chain' loLE xs) :
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
        | false => simpa [List.takeWhile, hpx] using hmem
        | true  =>
          have := hmem
          simp [List.takeWhile, hpx] at this
          rcases this with hnr | hmem'
          · subst hnr; simpa [hpx]
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
    simpa [List.span_eq_takeWhile_dropWhile, htake, hdrop]

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

  rw [h_initial_eq, Set.union_assoc]-- Bridge lemma: listSet here is the same as listToSet in Basic.lean
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
    have hchain_loLE : List.Chain' loLE s.ranges := pairwise_before_implies_chain_loLE s.ranges hchain

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
  simp only [h_not_empty, ite_false]  -- Get the span result
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

  simp only [h_getLast]

  -- Gap check is false
  have h_gap_decide : decide (prev.val.hi + 1 < r.lo) = false := by
    simp [h_gap]
  simp only [h_gap_decide]

  -- Extend check is true
  simp only [h_extend, dite_true]

  -- Now we're in: delete_extra (fromNRsUnsafe extendedList) target
  -- where extendedList = dropLast before ++ (extended :: after)
  -- and extended = mkNR prev.lo r.hi ...
  -- and target = {lo := prev.lo, hi := r.hi}

  -- Set up the extended range and list
  have h_prev_le : prev.val.lo ≤ prev.val.hi := prev.property
  have h_r_le : prev.val.hi ≤ r.hi := le_of_lt h_extend
  have h_extended_le : prev.val.lo ≤ r.hi := le_trans h_prev_le h_r_le
  set extended := mkNR prev.val.lo r.hi h_extended_le
  set extendedList := List.dropLast before ++ (extended :: after)
  set mergedSet := fromNRsUnsafe extendedList
  set target : IntRange := { lo := prev.val.lo, hi := r.hi }

  -- Unfold delete_extra
  show (delete_extra mergedSet target).toSet = s.toSet ∪ r.toSet
  unfold delete_extra

  -- The result is fromNRsUnsafe (deleteExtraNRs mergedSet.ranges target.lo target.hi)
  have h_mergedSet_ranges : mergedSet.ranges = extendedList := by
    simp [mergedSet, fromNRsUnsafe]

  have h_result_toSet : (fromNRsUnsafe (deleteExtraNRs extendedList prev.val.lo r.hi)).toSet =
                        listSet (deleteExtraNRs extendedList prev.val.lo r.hi) := by
    unfold fromNRsUnsafe
    rw [RangeSetBlaze.toSet_eq_listToSet]
    rfl

  rw [h_mergedSet_ranges, h_result_toSet]

  -- Key facts: s.ranges = before ++ after, and before ends with prev
  have h_ranges_decomp : s.ranges = before ++ after := by
    have h_span := List.span_eq_takeWhile_dropWhile
      (p := fun nr => decide (nr.val.lo ≤ r.lo)) (l := s.ranges)
    calc s.ranges
      _ = (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo))) ++
          (s.ranges.dropWhile (fun nr => decide (nr.val.lo ≤ r.lo))) := by
        exact (List.takeWhile_append_dropWhile (p := fun nr => decide (nr.val.lo ≤ r.lo)) (l := s.ranges)).symm
      _ = split.fst ++ split.snd := by
        simp [split, h_span]
      _ = before ++ after := rfl

  -- Show that before is not empty (since getLast? = some prev)
  have h_before_ne : before ≠ [] := by
    intro h
    simp [h] at h_getLast

  -- Show before = dropLast before ++ [prev]
  have h_before_decomp : before = List.dropLast before ++ [prev] := by
    have h_getLast_alt : before.getLast h_before_ne = prev := by
      have := List.getLast?_eq_getLast h_before_ne
      rw [h_getLast] at this
      simp at this
      exact this.symm
    conv_lhs => rw [← List.dropLast_append_getLast h_before_ne, h_getLast_alt]

  -- Therefore s.toSet = listSet (dropLast before) ∪ prev.toSet ∪ listSet after
  have h_s_toSet : s.toSet = listSet (List.dropLast before) ∪ prev.val.toSet ∪ listSet after := by
    calc s.toSet
      _ = listSet s.ranges := by rw [RangeSetBlaze.toSet_eq_listToSet]; rfl
      _ = listSet (before ++ after) := by rw [h_ranges_decomp]
      _ = listSet before ∪ listSet after := listSet_append _ _
      _ = listSet (List.dropLast before ++ [prev]) ∪ listSet after := by
        conv_lhs => arg 1; rw [h_before_decomp]
      _ = (listSet (List.dropLast before) ∪ prev.val.toSet) ∪ listSet after := by
        rw [listSet_append]
        simp [listSet]
      _ = listSet (List.dropLast before) ∪ prev.val.toSet ∪ listSet after := by
        ac_rfl

  -- Show that extended.toSet = prev.toSet ∪ r.toSet when ¬h_gap and prev.hi < r.hi
  have h_extended_covers : extended.val.toSet = prev.val.toSet ∪ r.toSet := by
    -- extended = mkNR prev.lo r.hi, so extended.toSet = Set.Icc prev.lo r.hi
    -- prev.toSet = Set.Icc prev.lo prev.hi
    -- r.toSet = Set.Icc r.lo r.hi
    -- Need to show: Set.Icc prev.lo r.hi = Set.Icc prev.lo prev.hi ∪ Set.Icc r.lo r.hi

    have h_extended_def : extended.val.toSet = Set.Icc prev.val.lo r.hi := by
      simp [extended, mkNR, IntRange.toSet]

    have h_prev_def : prev.val.toSet = Set.Icc prev.val.lo prev.val.hi := by
      simp [IntRange.toSet]

    have h_r_def : r.toSet = Set.Icc r.lo r.hi := by
      simp [IntRange.toSet]

    rw [h_extended_def, h_prev_def, h_r_def]

    -- Key fact: ¬h_gap means prev.hi + 1 ≥ r.lo, so r.lo ≤ prev.hi + 1
    have h_r_lo_bound : r.lo ≤ prev.val.hi + 1 := le_of_not_gt h_gap

    -- Since h_extend: prev.hi < r.hi, we have prev.hi ≤ r.hi
    have h_prev_hi_le_r_hi : prev.val.hi ≤ r.hi := le_of_lt h_extend

    -- Also, from the chain invariant and getLast, prev.lo ≤ r.lo
    -- (This follows from the fact that prev is in the "before" part of the span)
    have h_prev_lo_le_r_lo : prev.val.lo ≤ r.lo := by
      -- prev is in takeWhile (nr.lo ≤ r.lo), so prev.lo ≤ r.lo
      have h_prev_in_before : prev ∈ before := by
        have ⟨ys, h_decomp⟩ := List.getLast?_eq_some_iff.mp h_getLast
        rw [h_decomp]
        simp
      have h_before_takeWhile : before = s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
        have h_span := List.span_eq_takeWhile_dropWhile
          (p := fun nr => decide (nr.val.lo ≤ r.lo)) (l := s.ranges)
        calc before
          _ = split.fst := rfl
          _ = (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).fst := rfl
          _ = s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := congrArg Prod.fst h_span
      rw [h_before_takeWhile] at h_prev_in_before
      have := mem_takeWhile_satisfies (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges prev h_prev_in_before
      simp at this
      exact this

    -- Show the union equals the extended interval
    apply Set.ext
    intro x
    constructor
    · intro hx
      -- x ∈ Set.Icc prev.lo r.hi → x ∈ Set.Icc prev.lo prev.hi ∪ Set.Icc r.lo r.hi
      simp [Set.Icc] at hx ⊢
      rcases hx with ⟨hx_lo, hx_hi⟩
      by_cases h : x ≤ prev.val.hi
      · left
        exact ⟨hx_lo, h⟩
      · right
        have hx_gt_prev : prev.val.hi < x := lt_of_not_ge h
        have hx_ge_r_lo : r.lo ≤ x := by
          have : prev.val.hi + 1 ≤ x := (Int.add_one_le_iff).2 hx_gt_prev
          exact le_trans h_r_lo_bound this
        exact ⟨hx_ge_r_lo, hx_hi⟩
    · intro hx
      -- x ∈ Set.Icc prev.lo prev.hi ∪ Set.Icc r.lo r.hi → x ∈ Set.Icc prev.lo r.hi
      simp [Set.Icc] at hx ⊢
      rcases hx with ⟨hx_lo, hx_hi⟩ | ⟨hx_lo, hx_hi⟩
      · -- x ∈ [prev.lo, prev.hi]
        exact ⟨hx_lo, le_trans hx_hi h_prev_hi_le_r_hi⟩
      · -- x ∈ [r.lo, r.hi]
        exact ⟨le_trans h_prev_lo_le_r_lo hx_lo, hx_hi⟩

  -- Now we need to show: listSet (deleteExtraNRs extendedList prev.lo r.hi) = s.toSet ∪ r.toSet
  -- We have:
  --   s.toSet = listSet (dropLast before) ∪ prev.toSet ∪ listSet after (from h_s_toSet)
  --   extended.toSet = prev.toSet ∪ r.toSet (from h_extended_covers)
  --   extendedList = dropLast before ++ extended :: after

  -- The key insight: deleteExtraNRs on extendedList will merge extended with after if needed,
  -- but won't change dropLast before (since those elements have lo < prev.lo)

  -- For now, we can show the sets are equal by rewriting using what we have
  calc listSet (deleteExtraNRs extendedList prev.val.lo r.hi)
    _ = listSet extendedList := by
        -- Key observation: extended.lo = prev.lo and extended.hi = r.hi
        -- So deleteExtraNRs is called with start = extended.lo and stop = extended.hi
        have h_extended_lo_eq : extended.val.lo = prev.val.lo := by simp [extended, mkNR]
        have h_extended_hi_eq : extended.val.hi = r.hi := by simp [extended, mkNR]

        -- Unfold deleteExtraNRs and analyze the span
        unfold deleteExtraNRs

        -- The span separates at (nr.lo < prev.lo)
        set split' := List.span (fun nr => decide (nr.val.lo < prev.val.lo)) extendedList

        -- Show that the span gives (dropLast before, extended :: after)
        have h_span_extended : split' = (List.dropLast before, extended :: after) := by
          -- Need to show: elements of dropLast before have lo < prev.lo
          -- and extended.lo = prev.lo, so it breaks the predicate

          -- Elements in dropLast before come from before (which is chain-sorted)
          -- and prev is the last element of before
          -- So all elements before prev have lo < prev.lo (from chain property)
          have h_dropLast_all : ∀ nr ∈ List.dropLast before, nr.val.lo < prev.val.lo := by
            intro nr hmem
            -- We have Pairwise NR.before on s.ranges
            have h_pairwise : List.Pairwise NR.before s.ranges := s.ok
            -- before is a prefix of s.ranges, so Pairwise holds on before
            have h_pairwise_before : List.Pairwise NR.before before := by
              rw [h_ranges_decomp] at h_pairwise
              exact pairwise_append_left NR.before before after h_pairwise
            -- Now use pairwise_prefix_last on before = dropLast before ++ [prev]
            rw [h_before_decomp] at h_pairwise_before
            have h_all_before_prev := pairwise_prefix_last NR.before (List.dropLast before) prev h_pairwise_before
            have h_nr_before_prev : NR.before nr prev := h_all_before_prev nr hmem
            -- NR.before means nr.hi + 1 < prev.lo, which implies nr.lo < prev.lo
            unfold NR.before at h_nr_before_prev
            have h_nr_hi_bound : nr.val.hi + 1 < prev.val.lo := h_nr_before_prev
            have h_nr_prop : nr.val.lo ≤ nr.val.hi := nr.property
            linarith

          -- Convert to Bool form for the lemmas
          have h_dropLast_bool : ∀ nr ∈ List.dropLast before,
              (decide (nr.val.lo < prev.val.lo)) = true := by
            intro nr hmem
            simp [h_dropLast_all nr hmem]

          -- extended.lo = prev.lo, so it fails the predicate
          have h_extended_bool : (decide (extended.val.lo < prev.val.lo)) = false := by
            simp [h_extended_lo_eq]

          -- Apply the span lemmas to extendedList which is dropLast before ++ extended :: after
          have htake := takeWhile_append_of_all
            (fun nr => decide (nr.val.lo < prev.val.lo))
            (List.dropLast before) extended after
            h_dropLast_bool h_extended_bool

          have hdrop := dropWhile_append_of_all
            (fun nr => decide (nr.val.lo < prev.val.lo))
            (List.dropLast before) extended after
            h_dropLast_bool h_extended_bool

          -- Combine to get span result
          simp [split', List.span_eq_takeWhile_dropWhile, extendedList, htake, hdrop]

        -- Rewrite using the span result
        conv_lhs =>
          arg 1
          rw [h_span_extended]

        -- Now we're in the cons case with extended :: after
        simp only []

        -- Since extended.hi = r.hi, the initial range simplifies
        have h_max_eq : max extended.val.hi r.hi = r.hi := by
          simp [h_extended_hi_eq]

        -- Apply deleteExtraNRs_loop_sets to complete the proof
        -- After the span, we're in the cons branch of deleteExtraNRs
        -- Set up initial value and apply the loop lemma
        set initialHi := max extended.val.hi r.hi with h_initialHi_def
        have h_extended_prop : extended.val.lo ≤ extended.val.hi := extended.property
        have h_max_ge : extended.val.hi ≤ initialHi := le_max_left _ _
        have h_initial_valid : extended.val.lo ≤ initialHi := le_trans h_extended_prop h_max_ge
        set initial := mkNR extended.val.lo initialHi h_initial_valid with h_initial_def

        -- The loop processes initial :: after
        have h_initial_lo : initial.val.lo = prev.val.lo := by
          simp [initial, mkNR, h_extended_lo_eq]

        -- All elements of after have lo ≥ prev.lo (from chain and span properties)
        have h_after_ge : ∀ nr ∈ after, prev.val.lo ≤ nr.val.lo := by
          intro nr hmem
          -- after is the suffix from the span on s.ranges with predicate (lo ≤ r.lo)
          -- Elements in after have lo > r.lo (from dropWhile)
          -- And prev.lo ≤ r.lo (from before being takeWhile (lo ≤ r.lo))
          have h_nr_gt : r.lo < nr.val.lo := by
            sorry -- Show nr.lo > r.lo: after comes from dropWhile, first element fails predicate
          have h_prev_le : prev.val.lo ≤ r.lo := by
            -- prev is in takeWhile (lo ≤ r.lo)
            have h_prev_in : prev ∈ before := by
              rw [h_before_decomp]
              simp
            have h_take : before = s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
              have := List.span_eq_takeWhile_dropWhile (p := fun nr => decide (nr.val.lo ≤ r.lo)) (l := s.ranges)
              exact congrArg Prod.fst this
            rw [h_take] at h_prev_in
            have := mem_takeWhile_satisfies (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges prev h_prev_in
            simp at this
            exact this
          exact le_trans h_prev_le (le_of_lt h_nr_gt)

        -- Apply the loop sets lemma
        have h_loop := deleteExtraNRs_loop_sets prev.val.lo after initial h_initial_lo h_after_ge

        -- The result of deleteExtraNRs in the cons case is before ++ (loop_result)
        -- And initial.toSet = extended.toSet (since initialHi = r.hi by h_max_eq)
        have h_initial_eq : initial.val.toSet = extended.val.toSet := by
          have : initialHi = r.hi := h_max_eq
          simp [initial, extended, mkNR, IntRange.toSet, this]

        -- Complete the equality
        calc listSet (List.dropLast before ++
                (deleteExtraNRs_loop initial after).fst ::
                (deleteExtraNRs_loop initial after).snd)
          _ = listSet (List.dropLast before) ∪
              listSet ((deleteExtraNRs_loop initial after).fst ::
                      (deleteExtraNRs_loop initial after).snd) := listSet_append _ _
          _ = listSet (List.dropLast before) ∪ (initial.val.toSet ∪ listSet after) := by rw [h_loop]
          _ = listSet (List.dropLast before) ∪ (extended.val.toSet ∪ listSet after) := by rw [h_initial_eq]
          _ = listSet (List.dropLast before ++ (extended :: after)) := by
              rw [listSet_append]; simp [listSet]
    _ = listSet (List.dropLast before ++ (extended :: after)) := rfl
    _ = listSet (List.dropLast before) ∪ listSet (extended :: after) := listSet_append _ _
    _ = listSet (List.dropLast before) ∪ (extended.val.toSet ∪ listSet after) := by simp [listSet]
    _ = listSet (List.dropLast before) ∪ ((prev.val.toSet ∪ r.toSet) ∪ listSet after) := by
        rw [h_extended_covers]
    _ = listSet (List.dropLast before) ∪ prev.val.toSet ∪ r.toSet ∪ listSet after := by ac_rfl
    _ = (listSet (List.dropLast before) ∪ prev.val.toSet ∪ listSet after) ∪ r.toSet := by ac_rfl
    _ = s.toSet ∪ r.toSet := by rw [← h_s_toSet]

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
        have hbranch : internalAddC s r = internalAdd2 s r := by
          simp [internalAddC, hempty, hLast]
        simpa [hbranch, RangeSetBlaze.toSet_eq_listToSet] using
          internalAdd2_toSet s r
    | some prev =>
        by_cases hgap : prev.val.hi + 1 < r.lo
        ·
          have hbranch : internalAddC s r = internalAdd2 s r := by
            simp [internalAddC, hempty, hLast, hgap]
          simpa [hbranch, RangeSetBlaze.toSet_eq_listToSet] using
            internalAdd2_toSet s r
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
              -- Simplify the outer if: r.hi < r.lo is false
              simp only [hempty, ite_false]
              -- Now we're in the else branch
              -- We need to relate the span result to hLast
              -- Note: internalAddC uses span with (nr.lo ≤ start = r.lo)
              -- but hLast uses takeWhile with the same predicate
              have h_before_getLast :
                (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).fst.getLast? = some prev := by
                have h_span := List.span_eq_takeWhile_dropWhile
                  (p := fun nr => decide (nr.val.lo ≤ r.lo)) (l := s.ranges)
                have : (List.span (fun nr => decide (nr.val.lo ≤ r.lo)) s.ranges).fst =
                       s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ r.lo)) := by
                  exact congrArg Prod.fst h_span
                rw [this]
                exact hLast
              simp only [h_before_getLast]
              -- Now the gap check
              have h_gap_decide : decide (prev.val.hi + 1 < r.lo) = false := by
                simp [hgap]
              simp only [h_gap_decide]
              -- After simplifying, we need to show that the else branch is taken
              -- because ¬h_extend means the condition is false
              simp [h_extend]
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

/-
Blockers:
 1) Proving `internalAdd2_toSet` requires showing that `deleteExtraNRs` preserves
    the set union after merging overlapping ranges; exposing its internal `loop`
    recursion and establishing the interval-union lemmas became non-trivial within
    the allowed time.
Next plan:
 A) Introduce a dedicated lemma describing the union preserved by `deleteExtraNRs`
    by structurally recursing over its pending list and reusing the existing
    `IntRange` interval lemmas from `Basic`.
 B) Once that lemma is available, finish `internalAdd2_toSet` by combining the
    splice-union equality with the preserved-result lemma.
-/
