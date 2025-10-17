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

theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hempty : r.hi < r.lo
  ·
    have hEmptySet : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hempty
    simp [internalAddC, hempty, hEmptySet, Set.union_comm]
  ·
    sorry

end RangeSetBlaze
