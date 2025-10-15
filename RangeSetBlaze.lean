-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoB

-- Export main types and definitions
export IntRange (toSet empty nonempty)
export RangeSetBlaze (toSet internalAdd)
