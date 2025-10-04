import RangeSetBlaze.Basic

open IntRange

-- Example 1: Create a couple of non-empty ranges and one empty range
def range1 : IntRange where
  lo := 1
  hi := 5

def range2 : IntRange where
  lo := 10
  hi := 15

def emptyRange : IntRange where  -- hi < lo, so this is empty
  lo := 10
  hi := 5

-- Proof that the empty range is indeed empty
example : emptyRange.toSet = ∅ := by
  apply IntRange.toSet_empty_of_hi_lt_lo
  decide

-- Example 2: A list of ranges that is sorted and disjoint
def goodRanges : List IntRange := [
  { lo := 1, hi := 3 },
  { lo := 5, hi := 7 },
  { lo := 10, hi := 12 }
]

-- Proof that range1 and range2 are disjoint
example : disjoint range1 range2 := by
  unfold disjoint range1 range2
  decide

-- Example showing that adjacent ranges are NOT disjoint
def adjacentRange1 : IntRange where
  lo := 1
  hi := 5

def adjacentRange2 : IntRange where
  lo := 6
  hi := 10  -- No gap, so not disjoint

-- Proof that adjacent ranges (touching) are not disjoint
example : ¬(disjoint adjacentRange1 adjacentRange2) := by
  unfold disjoint adjacentRange1 adjacentRange2
  decide

-- Example of overlapping ranges (also not disjoint)
def overlappingRange1 : IntRange where
  lo := 1
  hi := 8

def overlappingRange2 : IntRange where
  lo := 5
  hi := 12

example : ¬(disjoint overlappingRange1 overlappingRange2) := by
  unfold disjoint overlappingRange1 overlappingRange2
  decide

-- A list that is NOT sorted and disjoint (ranges overlap)
def badRanges : List IntRange := [
  { lo := 1, hi := 5 },
  { lo := 4, hi := 8 }
]  -- These overlap

def main : IO Unit := do
  IO.println "RangeSetBlaze - Lean 4 Port Examples"
  IO.println "====================================="
  IO.println ""
  IO.println s!"Non-empty range 1: {repr range1}"
  IO.println s!"Non-empty range 2: {repr range2}"
  IO.println s!"Empty range (hi < lo): {repr emptyRange}"
  IO.println ""
  IO.println s!"Range1 is empty: {range1.isEmpty}"
  IO.println s!"Range2 is empty: {range2.isEmpty}"
  IO.println s!"EmptyRange is empty: {emptyRange.isEmpty}"
  IO.println ""
  IO.println s!"Range1 disjoint from Range2: {decide (disjoint range1 range2)}"
  IO.println s!"Adjacent ranges are disjoint: {decide (disjoint adjacentRange1 adjacentRange2)}"
  IO.println s!"Overlapping ranges are disjoint: {decide (disjoint overlappingRange1 overlappingRange2)}"
  IO.println ""
  IO.println s!"Good ranges (sorted & disjoint): {repr goodRanges}"
  IO.println s!"All non-empty: {RangeSetBlaze.checkNonEmpty goodRanges}"
  IO.println s!"Sorted and disjoint: {RangeSetBlaze.checkSortedDisjoint goodRanges}"
  IO.println ""
  IO.println s!"Bad ranges (overlapping): {repr badRanges}"
  IO.println s!"All non-empty: {RangeSetBlaze.checkNonEmpty badRanges}"
  IO.println s!"Sorted and disjoint: {RangeSetBlaze.checkSortedDisjoint badRanges}"
  IO.println ""
  IO.println s!"Hello, {hello}!"
