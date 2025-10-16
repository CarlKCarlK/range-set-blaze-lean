import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange

/-!
Ports the production Rust algorithm into Lean using simple lists.
We keep the data manipulation faithful to the original logic but replace
all algebraic arguments with `sorry` placeholders so that the file builds today.
-/

private def toPairs (s : RangeSetBlaze) : List (Int × Int) :=
  s.ranges.map fun r => (r.val.lo, r.val.hi)

private def fromPairs (pairs : List (Int × Int)) : RangeSetBlaze :=
  { ranges :=
      pairs.map fun p =>
        let lo := p.1
        let hi := p.2
        let r : IntRange := { lo := lo, hi := hi }
        have : r.nonempty := by
          sorry
        ⟨r, this⟩
    ok := by
      sorry }

private def deleteExtraPairs (pairs : List (Int × Int)) (start stop : Int) :
    List (Int × Int) :=
  let split := List.span (fun p : Int × Int => p.1 < start) pairs
  let before := split.1
  let rest := split.2
  match rest with
  | [] => pairs
  | curr :: tail =>
      let currStart := curr.1
      -- Merge any following ranges whose start sits inside the grown interval.
      let rec loop (currentStop : Int) (pending : List (Int × Int)) :
          (Int × Int) × List (Int × Int) :=
        match pending with
        | [] => ((currStart, currentStop), [])
        | (nextStart, nextStop) :: pendingTail =>
            if nextStart ≤ currentStop + 1 then
              let extended := max currentStop nextStop
              loop extended pendingTail
            else
              ((currStart, currentStop), (nextStart, nextStop) :: pendingTail)
      let merged := loop stop tail
      before ++ merged.1 :: merged.2

private def internalAdd2Pairs (pairs : List (Int × Int)) (start stop : Int) :
    List (Int × Int) :=
  let split := List.span (fun p : Int × Int => p.1 < start) pairs
  let before := split.1
  let after := split.2
  deleteExtraPairs (before ++ (start, stop) :: after) start stop

def delete_extra (s : RangeSetBlaze) (internalRange : IntRange) :
    RangeSetBlaze :=
  let start := internalRange.lo
  let stop := internalRange.hi
  let pairs := toPairs s
  fromPairs (deleteExtraPairs pairs start stop)

def internalAdd2 (s : RangeSetBlaze) (internalRange : IntRange) :
    RangeSetBlaze :=
  let start := internalRange.lo
  let stop := internalRange.hi
  let pairs := toPairs s
  fromPairs (internalAdd2Pairs pairs start stop)

def internalAddC (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  let start := r.lo
  let stop := r.hi
  if stop < start then
    s
  else
    let pairs := toPairs s
    let split := List.span (fun p : Int × Int => p.1 ≤ start) pairs
    let before := split.1
    let after := split.2
    let lastOpt := List.getLast? before
    let prefixRanges := List.dropLast before
    match lastOpt with
    | none =>
        internalAdd2 s r
    | some prev =>
        let prevStart := prev.1
        let prevStop := prev.2
        if prevStop + 1 < start then
          internalAdd2 s r
        else if prevStop < stop then
          let extended := prefixRanges ++ (prevStart, stop) :: after
          let extendedSet := fromPairs extended
          delete_extra extendedSet { lo := prevStart, hi := stop }
        else
          s

theorem internalAddC_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddC s r).toSet = s.toSet ∪ r.toSet := by
  sorry

end RangeSetBlaze
