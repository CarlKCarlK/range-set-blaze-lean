import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR
open Classical

/-- Strictly before the current range (with a gap). -/
def isBefore (curr : NR) (x : NR) : Prop :=
  x ≺ curr

/-- Strictly after the current range (with a gap). -/
def isAfter (curr : NR) (x : NR) : Prop :=
  curr ≺ x

/-- Touching or overlapping the current range. -/
def isTouch (curr : NR) (x : NR) : Prop :=
  ¬ x ≺ curr ∧ ¬ curr ≺ x

instance (curr : NR) : DecidablePred (isBefore curr) :=
  fun x => inferInstanceAs (Decidable (x ≺ curr))

instance (curr : NR) : DecidablePred (isAfter curr) :=
  fun x => inferInstanceAs (Decidable (curr ≺ x))

instance (curr : NR) : DecidablePred (isTouch curr) :=
  fun x => inferInstanceAs (Decidable (¬ x ≺ curr ∧ ¬ curr ≺ x))

structure SplitWitness (curr : NR) (xs : List NR) where
  before : List NR
  touching : List NR
  after : List NR
  order : xs = before ++ touching ++ after
  before_ok : ∀ {b}, b ∈ before → isBefore curr b
  touch_ok : ∀ {t}, t ∈ touching → isTouch curr t
  after_ok : ∀ {a}, a ∈ after → isAfter curr a

mutual
  def splitBefore (curr : NR) :
      (xs : List NR) → List.Pairwise (· ≺ ·) xs →
      SplitWitness curr xs
    | [], _ =>
        { before := []
          touching := []
          after := []
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by intro _ hb; cases hb
          after_ok := by intro _ hb; cases hb }
    | x :: xs, ok =>
        let head := List.pairwise_cons.1 ok
        let okTail := head.2
        match NR.Rel3.classify x curr with
        | NR.Rel3.left hx =>
            let tail := splitBefore curr xs okTail
            { before := x :: tail.before
              touching := tail.touching
              after := tail.after
              order := by
                have h := tail.order
                calc
                  x :: xs = x :: (tail.before ++ tail.touching ++ tail.after) := by
                    simpa [h]
                  _ = (x :: tail.before) ++ tail.touching ++ tail.after := by
                    simp [List.cons_append]
              before_ok := by
                intro b hb
                have hb' : b = x ∨ b ∈ tail.before := by
                  simpa using hb
                cases hb' with
                | inl hbEq =>
                    subst hbEq
                    exact hx
                | inr hbMem =>
                    exact tail.before_ok hbMem
              touch_ok := tail.touch_ok
              after_ok := tail.after_ok }
        | NR.Rel3.overlap hx₁ hx₂ =>
            splitTouching curr x ⟨hx₁, hx₂⟩ xs ok
        | NR.Rel3.right hx =>
            splitAfter curr x hx xs ok

  def splitTouching (curr : NR) (x : NR) (hx : isTouch curr x) :
      (xs : List NR) → List.Pairwise (· ≺ ·) (x :: xs) →
      SplitWitness curr (x :: xs)
    | [], _ =>
        { before := []
          touching := [x]
          after := []
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by
            intro t ht
            have ht' : t = x := by simpa using ht
            simpa [ht'] using hx
          after_ok := by intro _ hb; cases hb }
    | y :: ys, ok =>
        have hx_tail := (List.pairwise_cons.1 ok).1
        have okTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 ok).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.left hy =>
            have hFalse : False :=
              hx.1 (before_trans xBeforeY hy)
            False.elim hFalse
        | NR.Rel3.overlap hy₁ hy₂ =>
            let tail := splitTouching curr y ⟨hy₁, hy₂⟩ ys okTail
            { before := []
              touching := x :: tail.touching
              after := tail.after
              order := by
                have h :
                    y :: ys = tail.touching ++ tail.after := by
                  simpa [List.nil_append] using tail.order
                calc
                  x :: y :: ys = x :: (tail.touching ++ tail.after) := by
                    simpa [h]
                  _ = (x :: tail.touching) ++ tail.after := by
                    simp [List.cons_append]
              before_ok := by intro _ hb; cases hb
              touch_ok := by
                intro t ht
                have ht' : t = x ∨ t ∈ tail.touching := by
                  simpa using ht
                cases ht' with
                | inl htEq =>
                    subst htEq
                    simpa using hx
                | inr htMem =>
                    exact tail.touch_ok htMem
              after_ok := tail.after_ok }
        | NR.Rel3.right hy =>
            let tail := splitAfter curr y hy ys okTail
            { before := []
              touching := [x]
              after := tail.after
              order := by
                classical
                have hbefore : tail.before = [] := by
                  cases tail.before with
                  | nil => rfl
                  | cons b bs =>
                      have hbmem : b ∈ tail.before := by simp
                      have hb_before : isBefore curr b := tail.before_ok hbmem
                      have horder :
                          y :: ys = b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder).1
                      have hy_before : isBefore curr y := by
                        simpa [hy_eq] using hb_before
                      have hcy : curr ≺ y := hy
                      have hcc : curr ≺ curr := before_trans hcy hy_before
                      have hlt : curr.val.hi + 1 < curr.val.lo := hcc
                      have hle : curr.val.lo ≤ curr.val.hi := by
                        simpa [IntRange.nonempty] using curr.property
                      have : False := by
                        have hlt' : curr.val.hi + 1 < curr.val.hi :=
                          lt_of_lt_of_le hlt hle
                        have : curr.val.hi + 1 ≤ curr.val.hi := hlt'.le
                        linarith
                      exact this.elim
                have htouch : tail.touching = [] := by
                  cases tail.touching with
                  | nil => rfl
                  | cons t ts =>
                      have htmem : t ∈ tail.touching := by simp
                      have ht_touch : isTouch curr t := tail.touch_ok htmem
                      have horder :
                          y :: ys = tail.before ++ t :: ts ++ tail.after := by
                        simpa [List.cons_append, List.append_assoc] using tail.order
                      have horder' :
                          y :: ys = t :: (ts ++ tail.after) := by
                        simpa [hbefore, List.nil_append, List.cons_append,
                          List.append_assoc] using horder
                      have hy_eq : y = t := (List.cons.inj horder').1
                      have hy_touch : isTouch curr y := by
                        simpa [hy_eq] using ht_touch
                      have hcy : curr ≺ y := hy
                      have : False := hy_touch.2 hcy
                      exact this.elim
                have h : y :: ys = tail.after := by
                  have h := tail.order
                  simpa [hbefore, htouch, List.nil_append,
                    List.cons_append, List.append_assoc] using h
                simp [List.cons_append, h]
              before_ok := by intro _ hb; cases hb
              touch_ok := by
                intro t ht
                have ht' : t = x := by simpa using ht
                simpa [ht'] using hx
              after_ok := tail.after_ok }

  def splitAfter (curr : NR) (x : NR) (hx : isAfter curr x) :
      (xs : List NR) → List.Pairwise (· ≺ ·) (x :: xs) →
      SplitWitness curr (x :: xs)
    | [], _ =>
        { before := []
          touching := []
          after := [x]
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by intro _ hb; cases hb
          after_ok := by
            intro a ha
            have ha' : a = x := by simpa using ha
            simpa [ha'] using hx }
    | y :: ys, ok =>
        have hx_tail := (List.pairwise_cons.1 ok).1
        have okTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 ok).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.right hy =>
            let tail := splitAfter curr y hy ys okTail
            { before := []
              touching := []
              after := x :: tail.after
              order := by
                classical
                have hbefore : tail.before = [] := by
                  cases tail.before with
                  | nil => rfl
                  | cons b bs =>
                      have hbmem : b ∈ tail.before := by simp
                      have hb_before : isBefore curr b := tail.before_ok hbmem
                      have horder :
                          y :: ys = b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder).1
                      have hy_before : isBefore curr y := by
                        simpa [hy_eq] using hb_before
                      have hcy : curr ≺ y := hy
                      have hcc : curr ≺ curr := before_trans hcy hy_before
                      have hlt : curr.val.hi + 1 < curr.val.lo := hcc
                      have hle : curr.val.lo ≤ curr.val.hi := by
                        simpa [IntRange.nonempty] using curr.property
                      have : False := by
                        have hlt' : curr.val.hi + 1 < curr.val.hi :=
                          lt_of_lt_of_le hlt hle
                        have : curr.val.hi + 1 ≤ curr.val.hi := hlt'.le
                        linarith
                      exact this.elim
                have htouch : tail.touching = [] := by
                  cases tail.touching with
                  | nil => rfl
                  | cons t ts =>
                      have htmem : t ∈ tail.touching := by simp
                      have ht_touch : isTouch curr t := tail.touch_ok htmem
                      have horder :
                          y :: ys = tail.before ++ t :: ts ++ tail.after := by
                        simpa [List.cons_append, List.append_assoc] using tail.order
                      have horder' :
                          y :: ys = t :: (ts ++ tail.after) := by
                        simpa [hbefore, List.nil_append, List.cons_append,
                          List.append_assoc] using horder
                      have hy_eq : y = t := (List.cons.inj horder').1
                      have hy_touch : isTouch curr y := by
                        simpa [hy_eq] using ht_touch
                      have hcy : curr ≺ y := hy
                      have : False := hy_touch.2 hcy
                      exact this.elim
                have h : y :: ys = tail.after := by
                  have h := tail.order
                  simpa [hbefore, htouch, List.nil_append,
                    List.cons_append, List.append_assoc] using h
                simp [h, List.cons_append]
              before_ok := by intro _ hb; cases hb
              touch_ok := by intro _ hb; cases hb
              after_ok := by
                intro a ha
                have ha' : a = x ∨ a ∈ tail.after := by
                  simpa using ha
                cases ha' with
                | inl haEq =>
                    subst haEq
                    simpa using hx
                | inr haMem =>
                    exact tail.after_ok haMem }
        | NR.Rel3.left hy =>
            have hcy : curr ≺ y :=
              before_trans hx xBeforeY
            have h1 : curr.val.hi + 1 < y.val.lo := hcy
            have h2 : y.val.lo ≤ y.val.hi := by
              simpa [IntRange.nonempty] using y.property
            have h1' : curr.val.hi + 1 < y.val.hi :=
              lt_of_lt_of_le h1 h2
            have h3 : y.val.hi + 1 < curr.val.lo := hy
            have h2' : y.val.hi ≤ y.val.hi + 1 := by
              have : (0 : Int) ≤ 1 := by decide
              simpa using add_le_add_left this y.val.hi
            have h1'' : curr.val.hi + 1 < y.val.hi + 1 :=
              lt_of_lt_of_le h1' h2'
            have hlt : curr.val.hi + 1 < curr.val.lo :=
              lt_trans h1'' h3
            have hle : curr.val.lo ≤ curr.val.hi := by
              simpa [IntRange.nonempty] using curr.property
            have : False := by
              have hlt' : curr.val.hi + 1 < curr.val.hi :=
                lt_of_lt_of_le hlt hle
              have : curr.val.hi + 1 ≤ curr.val.hi := hlt'.le
              linarith
            this.elim
        | NR.Rel3.overlap _ hy₂ =>
            have hcy : curr ≺ y :=
              before_trans hx xBeforeY
            False.elim (hy₂ hcy)
end

/-- Once we are in the touching phase, the recursive tail cannot place any
element in the `before` block. -/
lemma splitTouching_tail_before_nil
    (curr y : NR) (hy : isTouch curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitTouching curr y hy ys ok).before = [] := by
  classical
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; simp [splitTouching]
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | left hz =>
          exact (hy.1 (before_trans hyz hz)).elim
      | overlap hz₁ hz₂ =>
          have ih' :
              (splitTouching curr z ⟨hz₁, hz₂⟩ zs okTail).before = [] :=
            ih _ ⟨hz₁, hz₂⟩ okTail
          simp [splitTouching, hyz, hcls, okTail, ih']
      | right hz =>
          simp [splitTouching, hyz, hcls, okTail, hz]
/-- Once we are in the after phase, the recursive tail cannot place any element
in the `touching` block. -/
lemma splitAfter_tail_touching_nil
    (curr y : NR) (hy : isAfter curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitAfter curr y hy ys ok).touching = [] := by
  classical
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; simp [splitAfter]
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | right hz =>
          have ih' :
              (splitAfter curr z hz zs okTail).touching = [] :=
            ih _ hz okTail
          simp [splitAfter, hcls, hyz, okTail, hz, ih']
      | left hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          have h1 : curr.val.hi + 1 < z.val.lo := hcy
          have h2 : z.val.lo ≤ z.val.hi := by
            simpa [IntRange.nonempty] using z.property
          have h1' : curr.val.hi + 1 < z.val.hi := lt_of_lt_of_le h1 h2
          have h3 : z.val.hi + 1 < curr.val.lo := hz
          have h2' : z.val.hi ≤ z.val.hi + 1 := by
            have : (0 : Int) ≤ 1 := by decide
            simpa using add_le_add_left this z.val.hi
          have h1'' : curr.val.hi + 1 < z.val.hi + 1 :=
            lt_of_lt_of_le h1' h2'
          have hlt : curr.val.hi + 1 < curr.val.lo := lt_trans h1'' h3
          exact (lt_irrefl _ hlt).elim
      | overlap hz₁ hz₂ =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (hz₂ hcy).elim

/-- Once we are in the after phase, the recursive tail cannot place any element
in the `before` block. -/
lemma splitAfter_tail_before_nil
    (curr y : NR) (hy : isAfter curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitAfter curr y hy ys ok).before = [] := by
  classical
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; simp [splitAfter]
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | right hz =>
          have ih' :
              (splitAfter curr z hz zs okTail).before = [] :=
            ih _ hz okTail
          simp [splitAfter, hcls, hyz, okTail, hz, ih']
      | left hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          have h1 : curr.val.hi + 1 < z.val.lo := hcy
          have h2 : z.val.lo ≤ z.val.hi := by
            simpa [IntRange.nonempty] using z.property
          have h1' : curr.val.hi + 1 < z.val.hi := lt_of_lt_of_le h1 h2
          have h3 : z.val.hi + 1 < curr.val.lo := hz
          have h2' : z.val.hi ≤ z.val.hi + 1 := by
            have : (0 : Int) ≤ 1 := by decide
            simpa using add_le_add_left this z.val.hi
          have h1'' : curr.val.hi + 1 < z.val.hi + 1 :=
            lt_of_lt_of_le h1' h2'
          have hlt : curr.val.hi + 1 < curr.val.lo := lt_trans h1'' h3
          have : False := (lt_irrefl _ hlt)
          exact this.elim
      | overlap hz₁ hz₂ =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (hz₂ hcy).elim

/-- Partition `xs` into the ranges before, touching, and after `curr`. -/
def splitRanges (curr : NR) (xs : List NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    SplitWitness curr xs :=
  splitBefore curr xs ok

/-- Fold `NR.glue` across a list, starting from `curr`. -/
def glueMany (curr : NR) (ts : List NR) : NR :=
  ts.foldl (fun acc t => NR.glue acc t) curr

/-- Set view of a list of ranges. -/
def listSet (rs : List NR) : Set Int :=
  rs.foldr (fun r acc => r.val.toSet ∪ acc) (∅ : Set Int)

@[simp] lemma listSet_nil : listSet ([] : List NR) = (∅ : Set Int) := rfl

@[simp] lemma listSet_cons (r : NR) (rs : List NR) :
    listSet (r :: rs) = r.val.toSet ∪ listSet rs := rfl

@[simp] lemma toSet_eq_listSet (s : RangeSetBlaze) :
    s.toSet = listSet s.ranges := rfl

lemma touch_after_glue_step
    (curr x y : NR)
    (hx : isTouch curr x)
    (hy : isTouch curr y) :
    isTouch (NR.glue curr x) y := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have : y.val.hi + 1 < curr.val.lo :=
      lt_of_lt_of_le h (min_le_left _ _)
    exact hy₁ this
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have hmax :
        curr.val.hi + 1 ≤ max curr.val.hi x.val.hi + 1 :=
      add_le_add_right (le_max_left _ _) _
    have : curr.val.hi + 1 < y.val.lo := lt_of_le_of_lt hmax h
    exact hy₂ this

lemma glueMany_sets_touching
    (curr : NR) (ts : List NR)
    (htouch : ∀ t ∈ ts, isTouch curr t) :
    (glueMany curr ts).val.toSet =
      curr.val.toSet ∪ listSet ts := by
  classical
  induction ts generalizing curr with
  | nil =>
      simp [glueMany, listSet_nil]
  | cons t ts ih =>
      have htouch_t : isTouch curr t := htouch _ (by simp)
      have htouch_tail : ∀ u ∈ ts, isTouch curr u := by
        intro u hu; exact htouch u (by simp [hu])
      have hglue :
          (NR.glue curr t).val.toSet =
            curr.val.toSet ∪ t.val.toSet :=
        NR.glue_sets curr t htouch_t.2 htouch_t.1
      have htouch_tail' :
          ∀ u ∈ ts, isTouch (NR.glue curr t) u := by
        intro u hu
        exact touch_after_glue_step curr t u htouch_t (htouch_tail u hu)
      have ih' := ih (NR.glue curr t) htouch_tail'
      simp [glueMany] at ih'
      calc
        (glueMany curr (t :: ts)).val.toSet
            = (glueMany (NR.glue curr t) ts).val.toSet := by
              simp [glueMany]
        _ = (NR.glue curr t).val.toSet ∪ listSet ts := ih'
        _ = (curr.val.toSet ∪ t.val.toSet) ∪ listSet ts := by
              simpa [hglue]
        _ = curr.val.toSet ∪ (t.val.toSet ∪ listSet ts) := by
              simp [Set.union_left_comm, Set.union_assoc, Set.union_comm]
        _ = curr.val.toSet ∪ listSet (t :: ts) := by
              simp [listSet_cons, Set.union_left_comm, Set.union_assoc]

lemma listSet_append (xs ys : List NR) :
    listSet (xs ++ ys) = listSet xs ∪ listSet ys := by
  induction xs with
  | nil =>
      simp [listSet_nil]
  | cons x xs ih =>
      simp [listSet_cons, List.cons_append, Set.union_left_comm,
        Set.union_assoc, ih]

/-- Rebuild the list by gluing the touching block. -/
def buildSplit (curr : NR) (before touching after : List NR) :
    List NR :=
  before ++ [glueMany curr touching] ++ after

lemma buildSplit_sets
    (curr : NR) {xs before touching after}
    (hx : xs = before ++ touching ++ after)
    (ht : ∀ t ∈ touching, isTouch curr t) :
    listSet (buildSplit curr before touching after) =
      curr.val.toSet ∪
        (listSet touching ∪ listSet before ∪ listSet after) := by
  classical
  subst hx
  simp [buildSplit, listSet_append, listSet_cons,
    glueMany_sets_touching curr touching ht, Set.union_left_comm,
    Set.union_assoc, Set.union_comm]

/-- Everything in `before` is before everything in `touching`. -/
lemma split_before_before_touch
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃b⦄, b ∈ w.before → ∀ ⦃t⦄, t ∈ w.touching → b ≺ t := by
  classical
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, cross_before⟩ :=
    List.pairwise_append.1 ok''
  intro b hb t ht
  have ht' : t ∈ w.touching ++ w.after := by
    simp [List.mem_append, ht]
  exact cross_before (a := b) (b := t) hb ht'

/-- Everything in `before` is before everything in `after`. -/
lemma split_before_before_after
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃b⦄, b ∈ w.before → ∀ ⦃a⦄, a ∈ w.after → b ≺ a := by
  classical
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, cross_before⟩ :=
    List.pairwise_append.1 ok''
  intro b hb a ha
  have ha' : a ∈ w.touching ++ w.after := by
    simp [List.mem_append, ha]
  exact cross_before (a := b) (b := a) hb ha'

/-- Everything in `touching` is before everything in `after`. -/
lemma split_touch_before_after
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃t⦄, t ∈ w.touching → ∀ ⦃a⦄, a ∈ w.after → t ≺ a := by
  classical
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, _⟩ :=
    List.pairwise_append.1 ok''
  obtain ⟨_, _, cross_touch⟩ :=
    List.pairwise_append.1 ok_tail
  intro t ht a ha
  exact cross_touch (a := t) (b := a) ht ha

/-- Legality for Algo B rebuild:
`before ++ [glueMany curr touching] ++ after` is pairwise `(· ≺ ·)`. -/
lemma buildSplit_pairwise
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs)
    (htouch : ∀ t ∈ w.touching, isTouch curr t) :
    List.Pairwise (· ≺ ·)
      (buildSplit curr w.before w.touching w.after) := by
  /- TODO:
    * From A, we have:
      - `b ∈ before` → `t ∈ touching` → `b ≺ t`
      - `b ∈ before` → `a ∈ after`    → `b ≺ a`
      - `t ∈ touching` → `a ∈ after`   → `t ≺ a`
    * Show `before ≺ glueMany curr touching`:
      fold over touching using `before_glue_of_before` from Basic.lean.
    * Show `glueMany curr touching ≺ after`:
      similar fold, or use `split_touch_before_after` plus `before_glue_of_before`.
    * Combine with pairwise of `before` and `after` (from `ok` via `w.order`).
  -/
  sorry

/-- New insertion algorithm reusing the existing `insert`. -/
def internalAddB (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  internalAddA s r

lemma internalAddB_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddB s r).toSet = s.toSet ∪ r.toSet := by
  classical
  simpa [internalAddB] using internalAddA_toSet s r

lemma internalAddB_agrees_with_split_sets
    (s : RangeSetBlaze) (r : IntRange) (hr : r.nonempty) :
    let curr : NR := ⟨r, hr⟩
    let w := splitRanges curr s.ranges s.ok
    listSet (buildSplit curr w.before w.touching w.after) =
      (internalAddB s r).toSet := by
  classical
  set curr : NR := ⟨r, hr⟩
  let w := splitRanges curr s.ranges s.ok
  have hsplit :
      listSet s.ranges =
        listSet w.before ∪ listSet w.touching ∪ listSet w.after := by
    simpa [w.order, listSet_append, Set.union_left_comm,
      Set.union_assoc, Set.union_comm]
  have hcurr : curr.val.toSet = r.toSet := rfl
  have hs : s.toSet = listSet s.ranges := toSet_eq_listSet s
  have hbuild :
      listSet (buildSplit curr w.before w.touching w.after) =
        curr.val.toSet ∪
          (listSet w.touching ∪ listSet w.before ∪ listSet w.after) :=
    buildSplit_sets (curr := curr) (xs := s.ranges)
      (before := w.before) (touching := w.touching) (after := w.after)
      w.order
      (by
        intro t ht
        exact w.touch_ok ht)
  calc
    listSet (buildSplit curr w.before w.touching w.after)
        = curr.val.toSet ∪
            (listSet w.touching ∪ listSet w.before ∪ listSet w.after) :=
            hbuild
    _ = listSet s.ranges ∪ r.toSet := by
        simp [hcurr, hsplit, Set.union_left_comm, Set.union_comm,
          Set.union_assoc]
    _ = s.toSet ∪ r.toSet := by
        rw [hs]
    _ = (internalAddB s r).toSet := by
        simpa using (internalAddB_toSet s r).symm

/-- Once we are in the touching phase, the recursive tail cannot place any
element in the `before` block. -/
end RangeSetBlaze
