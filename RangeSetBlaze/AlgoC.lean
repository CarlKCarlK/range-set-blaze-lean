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
      let rec loop (current : NR) (pending : List NR) :
          Prod NR (List NR) :=
        match pending with
        | [] => (current, [])
        | next :: pendingTail =>
            if decide (next.val.lo <= current.val.hi + 1) then
              let newLo := current.val.lo
              let newHi := max current.val.hi next.val.hi
              have hcurr' : current.val.lo ≤ current.val.hi := current.property
              have hmax' : current.val.hi ≤ newHi := le_max_left _ _
              have hmerged : newLo ≤ newHi := le_trans hcurr' hmax'
              let merged := mkNR newLo newHi hmerged
              loop merged pendingTail
            else
              (current, next :: pendingTail)
      let result := loop initial tail
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
      simp [ih, Set.union_left_comm, Set.union_assoc, Set.union_comm]

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
  have h_span := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
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

@[simp] private lemma deleteExtraNRs_loop_nil (current : NR) :
    deleteExtraNRs.loop current [] = (current, []) := by
  simp [deleteExtraNRs.loop]

/-- Splice lemma assuming the input list is chain-sorted by `lo`. -/
private lemma deleteExtraNRs_loop_sets
    (start : Int) :
    ∀ pending (current : NR),
      current.val.lo = start →
      (∀ nr ∈ pending, start ≤ nr.val.lo) →
      listSet
          ((deleteExtraNRs.loop current pending).fst ::
            (deleteExtraNRs.loop current pending).snd)
        =
          current.val.toSet ∪ listSet pending := by
  intro pending
  revert current
  induction pending with
  | nil =>
      intro current hcurlo hpend
      simp [deleteExtraNRs.loop, listSet_cons, listSet_nil, Set.union_comm]
  | cons next tail ih =>
      intro current hcurlo hpend
      dsimp [deleteExtraNRs.loop]
      cases hmerge_dec : decide (next.val.lo ≤ current.val.hi + 1) with
      | false =>
          have hmerge : ¬ next.val.lo ≤ current.val.hi + 1 :=
            of_decide_false hmerge_dec
          simp [hmerge_dec, hmerge, listSet_cons, Set.union_left_comm,
            Set.union_assoc]
      | true =>
          have hmerge : next.val.lo ≤ current.val.hi + 1 :=
            of_decide_true hmerge_dec
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
            ih tail merged hcurlo' hpend'
          have hmerged_toSet :
              merged.val.toSet = current.val.toSet ∪ next.val.toSet := by
            simpa [hmerged_def] using
              (merge_step_sets current next horder htouch).symm
          have hloop_simplified :
              listSet
                  ((deleteExtraNRs.loop current (next :: tail)).fst ::
                    (deleteExtraNRs.loop current (next :: tail)).snd)
                =
                  merged.val.toSet ∪ listSet tail := by
            simpa [hmerge_dec, hmerged_def] using hrec
          calc
            listSet
                ((deleteExtraNRs.loop current (next :: tail)).fst ::
                  (deleteExtraNRs.loop current (next :: tail)).snd)
                =
                  merged.val.toSet ∪ listSet tail := hloop_simplified
            _ = (current.val.toSet ∪ next.val.toSet) ∪ listSet tail := by
                  simp [hmerged_toSet]
            _ = current.val.toSet ∪ listSet (next :: tail) := by
                  simp [listSet_cons, Set.union_left_comm, Set.union_assoc,
                    Set.union_comm]

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
  -- Bind names so we can rewrite cleanly
  set split := List.span (fun nr => decide (nr.val.lo < start)) xs
  set before := split.fst
  set after := split.snd
  set inserted := mkNR start stop h
  let p : NR → Bool := fun nr => decide (nr.val.lo < start)

  -- span facts on xs
  have h_span := List.span_eq_takeWhile_dropWhile (p := p) (l := xs)
  have h_take_split : split.fst = xs.takeWhile p := by
    simpa [split] using congrArg Prod.fst h_span
  have h_drop_split : split.snd = xs.dropWhile p := by
    simpa [split] using congrArg Prod.snd h_span

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
    have hmem_split : nr ∈ split.fst := by simpa [before] using hmem
    have : nr ∈ xs.takeWhile p := by simpa [h_take_split] using hmem_split
    exact h_take_all_aux this

  -- inserted.lo = start, so it breaks the predicate
  have h_inserted_false : p inserted = false := by
    simp [p, inserted, mkNR]

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
    simpa [split] using span_suffix_all_ge_start_of_chain xs start hchain
  have h_ge_after_all : ∀ nr ∈ after, start ≤ nr.val.lo := by
    intro nr hmem
    have hmem_split : nr ∈ split.snd := by simpa [after] using hmem
    exact h_suffix nr hmem_split

  -- Unfold deleteExtraNRs on the spliced list and simplify the head step
  unfold deleteExtraNRs
  simp [split, before, after, h_span_splice]

  -- initial = inserted (since max stop stop = stop)
  have h_initial_eq :
      mkNR inserted.val.lo (max inserted.val.hi stop)
        (by
          have hc := inserted.property
          have := le_max_left inserted.val.hi stop
          exact le_trans hc this)
        = inserted := by
    apply Subtype.ext; simp [mkNR, inserted, max_self]

  -- Main loop lemma: revert `current` so the IH is polymorphic in it
  have loop_sets :
      ∀ pending (current : NR),
        current.val.lo = start →
        (∀ nr ∈ pending, start ≤ nr.val.lo) →
        listSet
          ((deleteExtraNRs.loop current pending).fst
            :: (deleteExtraNRs.loop current pending).snd)
          =
        current.val.toSet ∪ listSet pending := by
    intro pending
    revert current
    induction pending with
    | nil =>
        intro current hcurlo hpend
        simp [deleteExtraNRs.loop, listSet_cons, listSet_nil, Set.union_comm]
    | cons next tail ih =>
        intro current hcurlo hpend
        dsimp [deleteExtraNRs.loop]
        by_cases hmerge : next.val.lo ≤ current.val.hi + 1
        · -- merge branch
          -- order from start ≤ next.lo
          have horder : current.val.lo ≤ next.val.lo := by
            have : start ≤ next.val.lo := hpend next (by simp)
            simpa [hcurlo] using this
          -- ¬(hi+1 < next.lo) from ≤
          have htouch : ¬ (current.val.hi + 1 < next.val.lo) :=
            not_lt.mpr hmerge
          -- one-step set equality for the merge
          have hstep :
              current.val.toSet ∪ next.val.toSet =
                (mkNR current.val.lo (max current.val.hi next.val.hi)
                  (by
                    have hc : current.val.lo ≤ current.val.hi := current.property
                    exact le_trans hc (le_max_left _ _))).val.toSet := by
            simpa using merge_step_sets current next horder htouch
          -- merged current keeps low endpoint = start
          have hcurlo' :
              (mkNR current.val.lo (max current.val.hi next.val.hi)
                (by
                  have hc : current.val.lo ≤ current.val.hi := current.property
                  exact le_trans hc (le_max_left _ _))).val.lo = start := by
            simpa [mkNR, hcurlo]
          -- side-condition for the tail
          have hpend' : ∀ nr ∈ tail, start ≤ nr.val.lo := by
            intro nr hmem; exact hpend nr (by simp [hmem])
          -- apply IH to tail with merged current
          have hrec :=
            ih (mkNR current.val.lo (max current.val.hi next.val.hi)
                (by
                  have hc : current.val.lo ≤ current.val.hi := current.property
                  exact le_trans hc (le_max_left _ _)))
               hcurlo' hpend'
          simp [hmerge, hstep, hrec, listSet_cons, Set.union_left_comm, Set.union_assoc]
        · -- no-merge: loop returns (current, next :: tail)
          have hloop :
              deleteExtraNRs.loop current (next :: tail)
                = (current, next :: tail) := by
            simp [deleteExtraNRs.loop, hmerge]
          simp [hloop, listSet_cons, Set.union_left_comm, Set.union_assoc]

  -- Instatiate loop lemma at (inserted, after)
  have hloop_sets :
      listSet
        ((deleteExtraNRs.loop inserted after).fst
          :: (deleteExtraNRs.loop inserted after).snd)
        = inserted.val.toSet ∪ listSet after := by
    apply loop_sets after inserted
    · simp [inserted, mkNR]
    · exact h_ge_after_all

  -- Put `before ++ …` back and finish
  simp [split, before, after, h_initial_eq, hloop_sets,
        listSet_append, listSet_cons, Set.union_left_comm, Set.union_assoc]

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
private lemma deleteExtraNRs_sets_after_splice
    (xs : List NR) (start stop : Int) (h : start ≤ stop) :
    let split := List.span (fun nr => decide (nr.val.lo < start)) xs
    let before := split.fst
    let after := split.snd
    let inserted := mkNR start stop h
    listSet (deleteExtraNRs (before ++ inserted :: after) start stop) =
      listSet before ∪ inserted.val.toSet ∪ listSet after := by
  classical
  sorry

lemma internalAdd2_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd2 s r).toSet = s.toSet ∪ r.toSet := by
  classical
  unfold internalAdd2
  by_cases hempty : r.hi < r.lo
  ·
    have hEmpty : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    simp [hempty, hEmpty, Set.union_comm]
  ·
    have hle : r.lo ≤ r.hi := not_lt.mp hempty
    simp [hempty, hle, RangeSetBlaze.toSet_eq_listToSet,
      internalAdd2NRs]
    have :=
      deleteExtraNRs_sets_after_splice s.ranges r.lo r.hi hle
    -- TODO: finish rewriting the result of `deleteExtraNRs` into the desired union.
    sorry

/-– Spec for the “extend previous” branch of `internalAddC`.
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
  -- TODO(next increment): prove by unfolding the branch into
  -- `fromNRsUnsafe` + `delete_extra` and reusing union facts.
  sorry

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
          -- Remaining branch: no gap and we truly extend `prev`.
          have h_extend : prev.val.hi < r.hi := by
            -- placeholder derived from the branch guard of `internalAddC`
            sorry
          exact
            internalAddC_extendPrev_toSet s r prev
              hnonempty hLast (by exact hgap) h_extend

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


