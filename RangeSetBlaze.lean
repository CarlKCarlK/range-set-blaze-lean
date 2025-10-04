-- This module serves as the root of the `RangeSetBlaze` library.
-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic

-- Export main types and definitions
export IntRange (toSet isEmpty disjoint isNonEmpty)
export RangeSetBlaze (toSet checkSortedDisjoint checkNonEmpty)
