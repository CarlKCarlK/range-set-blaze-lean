# RangeSetBlaze - Lean 4 Port

This is a Lean 4 port of the core data structures from the Rust RangeSetBlaze library.

## Core Components

### IntRange (`RangeSetBlaze/Basic.lean`)

An inclusive range of integers with fields `lo` and `hi`.

**Key Properties:**
- A range is empty when `hi < lo` (convention chosen for easier proofs)
- Provides a `toSet` function that views the range as a Set Int
- Includes a lemma proving that empty ranges produce empty sets

**Features:**
- `isEmpty`: Boolean check if range is empty
- `isNonEmpty`: Boolean check if range is non-empty
- `disjoint` (≺): Predicate checking if two ranges are strictly separated by at least one integer
- `toSet`: Converts range to a Set Int using mathlib's set operations

### RangeSetBlaze Structure

A type representing lists of non-empty ranges that are sorted and disjoint.

**Properties:**
- `sorted_disjoint`: Proof that all pairs of ranges are disjoint and ordered
- `non_empty`: Proof that all ranges are non-empty
- `toSet`: Converts the entire structure to a single Set Int (union of all ranges)

**Helper Functions:**
- `checkSortedDisjoint`: Runtime check if a list of ranges is sorted and disjoint
- `checkNonEmpty`: Runtime check if all ranges in a list are non-empty

## Examples (`Main.lean`)

The Main.lean file demonstrates:

1. **Creating ranges**: Both non-empty and empty ranges
2. **Proofs**: 
   - Empty ranges are indeed empty
   - Disjoint ranges satisfy the disjoint predicate
   - Adjacent and overlapping ranges are NOT disjoint
3. **Runtime examples**:
   - Lists of ranges that are properly sorted and disjoint
   - Lists that violate the constraints

## Design Decisions

1. **Empty range convention**: `hi < lo` makes proofs simpler
2. **Set representation**: Uses mathlib's Set operations for mathematical correctness
3. **Decidability**: The `disjoint` predicate is decidable, allowing runtime evaluation
4. **Structure invariants**: RangeSetBlaze maintains sorted/disjoint invariants via dependent types

## Building and Running

```powershell
# Build the project
lake build

# Run the executable
lake exe rangesetblaze
```

## Output Example

```
RangeSetBlaze - Lean 4 Port Examples
=====================================

Non-empty range 1: { lo := 1, hi := 5 }
Non-empty range 2: { lo := 10, hi := 15 }
Empty range (hi < lo): { lo := 10, hi := 5 }

Range1 is empty: false
Range2 is empty: false
EmptyRange is empty: true

Range1 disjoint from Range2: true
Adjacent ranges are disjoint: false
Overlapping ranges are disjoint: false

Good ranges (sorted & disjoint): [{ lo := 1, hi := 3 }, { lo := 5, hi := 7 }, { lo := 10, hi := 12 }]
All non-empty: true
Sorted and disjoint: true

Bad ranges (overlapping): [{ lo := 1, hi := 5 }, { lo := 4, hi := 8 }]
All non-empty: true
Sorted and disjoint: false

Hello, world!
```
