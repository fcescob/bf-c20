import BoundarySearch

/-! Direct finite matching certificates.

Candidate: every admissible boundary state has either two or four
weighted perfect matchings whose spoke masks partition its vertices.
Certificate: explicit Boolean edge masks, checked at every vertex in
both orders. Kill condition: any failed state or mismatch between this
weighted incidence and the actual first-return expansion.

This interface avoids using the good-arc predicate in the final transfer.
The existing search remains an untrusted supplier of candidate masks.
-/

namespace C20.Boundary

def gapBit (flags i : Nat) : Bool :=
  if i % 2 == 0 then false else flags.testBit (i / 2)

def rowMatchingOK (order : List Nat) (flags mask edge : Nat) : Bool :=
  (List.range order.length).all fun i =>
    let prev := (i + order.length - 1) % order.length
    bit (selected mask (order.getD i 0)) +
      bit ((selected edge (order.getD prev 0)).xor (gapBit flags prev)) +
      bit (selected edge (order.getD i 0)) == 1

def RowMatching (order : List Nat) (flags mask edge : Nat) : Prop :=
  ∀ i, i < order.length →
    let prev := (i + order.length - 1) % order.length
    bit (selected mask (order.getD i 0)) +
      bit ((selected edge (order.getD prev 0)).xor (gapBit flags prev)) +
      bit (selected edge (order.getD i 0)) = 1

theorem rowMatchingOK_sound (order : List Nat) (flags mask edge : Nat)
    (h : rowMatchingOK order flags mask edge = true) : RowMatching order flags mask edge := by
  intro i hi
  have hrow := List.all_eq_true.mp h i (by simpa using hi)
  simpa using hrow

structure Pattern where
  mask : Nat
  outer : Nat
  inner : Nat
  deriving Repr, DecidableEq

def patternsOK (s : State) (patterns : List Pattern) : Bool :=
  (patterns.length == 2 || patterns.length == 4) &&
    patterns.all (fun p => rowMatchingOK (List.range s.k) s.cflags p.mask p.outer &&
      rowMatchingOK s.order s.dflags p.mask p.inner) &&
    (List.range s.k).all (fun v =>
      (patterns.filter (fun p => selected p.mask v)).length == 1)

def MatchingConclusion (s : State) : Prop :=
  ∃ patterns : List Pattern, (patterns.length = 2 ∨ patterns.length = 4) ∧
    (∀ p ∈ patterns, RowMatching (List.range s.k) s.cflags p.mask p.outer ∧
      RowMatching s.order s.dflags p.mask p.inner) ∧
    (∀ v, v < s.k → (patterns.filter (fun p => selected p.mask v)).length = 1)

theorem patternsOK_sound (s : State) (patterns : List Pattern)
    (h : patternsOK s patterns = true) : MatchingConclusion s := by
  simp only [patternsOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  refine ⟨patterns, h.1.1, ?_, ?_⟩
  · intro p hp
    have hs := h.1.2 p hp
    exact ⟨rowMatchingOK_sound _ _ _ _ hs.1, rowMatchingOK_sound _ _ _ _ hs.2⟩
  · intro v hv
    exact h.2 v (by simpa using hv)

/-- Candidate cycle edges from the next selected position. Correctness
is established only by rowMatchingOK, not by trusting this construction. -/
def edgesForMask (mask : Nat) (order : List Nat) (flags : Nat) : Nat := Id.run do
  let mut edges := 0
  for i in List.range order.length do
    let v := order.getD i 0
    if !selected mask v then
      match (List.range order.length).find? (fun j => selected mask (positionAt order i (j + 1))) with
      | none => pure ()
      | some j =>
        if !arcParity order.length flags i (j + 1) then
          edges := edges ||| (1 <<< v)
  return edges

def partitionPatterns (s : State) (masks : List Nat) : List Pattern :=
  masks.map fun mask => ⟨mask, edgesForMask mask (List.range s.k) s.cflags,
    edgesForMask mask s.order s.dflags⟩

/-- On a gap leaving an odd position, the edge colour complements the
spoke colour. Domino edges are unused by these two matchings. -/
def potentialEdges (order : List Nat) (mask : Nat) : Nat :=
  (List.range (order.length / 2)).foldl (fun bits j =>
    let v := order.getD (2 * j + 1) 0
    if !selected mask v then bits ||| (1 <<< v) else bits) 0

def potentialPatterns (s : State) (mask : Nat) : List Pattern :=
  let other := (2 ^ s.k - 1) ^^^ mask
  [⟨mask, potentialEdges (List.range s.k) mask, potentialEdges s.order mask⟩,
   ⟨other, potentialEdges (List.range s.k) other, potentialEdges s.order other⟩]

def checkMatchingState (s : State) (cg : List Nat) (dg : Nat) : Bool :=
  if patternsOK s (potentialPatterns s (potentialCandidate s)) then true
  else match partitionCandidate s.k cg dg with
    | none => false
    | some masks => patternsOK s (partitionPatterns s masks)

theorem checkMatchingState_sound (s : State) (cg : List Nat) (dg : Nat)
    (h : checkMatchingState s cg dg = true) : MatchingConclusion s := by
  unfold checkMatchingState at h
  split at h
  next hp => exact patternsOK_sound _ _ hp
  next hp =>
    split at h
    next he => contradiction
    next masks he => exact patternsOK_sound _ _ h

def checkMatchingOrder (k : Nat) (goods : Array (List Nat)) (tail : List Nat) : Bool :=
  let order := 0 :: tail
  let dgoods := permutedGoods k goods order
  (oddFlags k).all fun cf => (oddFlags k).all fun df =>
    checkMatchingState ⟨k, order, cf, df⟩ goods[cf]! dgoods[df]!

def allMatchingStates (k : Nat) : Bool :=
  let goods := ((List.range (2 ^ (k / 2))).map (localGood k)).toArray
  (permutations ((List.range (k - 1)).map (· + 1))).all (checkMatchingOrder k goods)

theorem allMatchingStates_sound (k : Nat) (tail : List Nat) (cf df : Nat)
    (hperm : tail.Perm ((List.range (k - 1)).map (· + 1)))
    (hc : cf ∈ oddFlags k) (hd : df ∈ oddFlags k)
    (h : allMatchingStates k = true) : MatchingConclusion ⟨k, 0 :: tail, cf, df⟩ := by
  have ht := all_permutations_sound _ _ h tail hperm
  simp only [checkMatchingOrder] at ht
  exact checkMatchingState_sound _ _ _ (List.all_eq_true.mp (List.all_eq_true.mp ht cf hc) df hd)

/-- Independent shards split the second vertex of the D order. The
enumerator and witness checker are unchanged; each permutation is still
covered exactly by its own head. No connectivity assumption is used. -/
def allMatchingStatesShard (k head : Nat) : Bool :=
  let goods := ((List.range (2 ^ (k / 2))).map (localGood k)).toArray
  (permutations ((List.range (k - 1)).map (· + 1))).all (fun tail =>
    if tail.headD 0 == head then checkMatchingOrder k goods tail else true)

theorem matchingShard_sound (k head : Nat) (tail : List Nat) (cf df : Nat)
    (hperm : tail.Perm ((List.range (k - 1)).map (· + 1)))
    (hc : cf ∈ oddFlags k) (hd : df ∈ oddFlags k) (hh : tail.headD 0 = head)
    (h : allMatchingStatesShard k head = true) : MatchingConclusion ⟨k, 0 :: tail, cf, df⟩ := by
  have ht := all_permutations_sound _ _ h tail hperm
  simp only [hh, beq_self_eq_true, ↓reduceIte, checkMatchingOrder] at ht
  exact checkMatchingState_sound _ _ _ (List.all_eq_true.mp (List.all_eq_true.mp ht cf hc) df hd)

theorem boundary_head_lt (k : Nat) (hk : 0 < k) (tail : List Nat)
    (hperm : tail.Perm ((List.range (k - 1)).map (· + 1))) : tail.headD 0 < k := by
  cases tail with
  | nil => exact hk
  | cons a rest =>
    have hm := hperm.mem_iff.mp (show a ∈ a :: rest from List.mem_cons_self)
    rcases List.mem_map.mp hm with ⟨i, hi, he⟩
    have hil : i < k - 1 := List.mem_range.mp hi
    simpa only [List.headD_cons] using (show a < k by omega)

end C20.Boundary

#print axioms C20.Boundary.allMatchingStates_sound
