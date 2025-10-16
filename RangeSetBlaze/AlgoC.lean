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
      let initial := mkNRUnsafe curr.val.lo initialHi
      let rec loop (current : NR) (pending : List NR) :
          Prod NR (List NR) :=
        match pending with
        | [] => (current, [])
        | next :: pendingTail =>
            if decide (next.val.lo <= current.val.hi + 1) then
              let newLo := current.val.lo
              let newHi := max current.val.hi next.val.hi
              let merged := mkNRUnsafe newLo newHi
              loop merged pendingTail
            else
              (current, next :: pendingTail)
      let result := loop initial tail
      before ++ (result.fst :: result.snd)

private def internalAdd2NRs (xs : List NR) (start stop : Int) :
    List NR :=
  let split := List.span (fun nr => decide (nr.val.lo < start)) xs
  let before := split.fst
  let after := split.snd
  let inserted := mkNRUnsafe start stop
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
  fromNRsUnsafe (internalAdd2NRs s.ranges start stop)

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
        else if decide (prev.val.hi < stop) then
          let extendedList :=
            List.dropLast before ++ (mkNRUnsafe prev.val.lo stop :: after)
          let mergedSet := fromNRsUnsafe extendedList
          let target : IntRange := { lo := prev.val.lo, hi := stop }
          delete_extra mergedSet target
        else
          s

theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  sorry

end RangeSetBlaze
