-- Import modules here that should be built as part of the library.
import RangeSetBlaze.Basic
import RangeSetBlaze.AlgoB

namespace RangeSetBlaze

def internalAdd := internalAddB

@[simp] lemma internalAdd_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd s r).toSet = s.toSet ∪ r.toSet :=
  by simpa [internalAdd] using internalAddB_toSet s r

end RangeSetBlaze

-- Export main types and definitions
export IntRange (toSet empty nonempty)
export RangeSetBlaze (toSet internalAdd)
