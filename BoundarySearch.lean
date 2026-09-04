import C20Boundary

/-!+Pure candidate construction for the finite theorem. Every accepted
candidate is passed through `Boundary.verify`, whose soundness is proved.
Search heuristics do not enter the logical trust boundary.
-/

namespace C20.Boundary

def countBits (k mask : Nat) : Nat :=
  (List.range k).foldl (fun n i => n + bit (selected mask i)) 0

def oddFlags (k : Nat) : List Nat :=
  (List.range (2 ^ (k / 2))).filter fun w => countBits (k / 2) w % 2 == 1

def partners (order : List Nat) : Array Nat := Id.run do
  let mut result := Array.replicate order.length 0
  for j in [:order.length / 2] do
    let a := order.getD (2 * j) 0
    let b := order.getD (2 * j + 1) 0
    result := result.set! a b
    result := result.set! b a
  return result

def connectedDominoes (k : Nat) (order : List Nat) : Bool := Id.run do
  let p := partners order
  let mut seen := 1
  for _ in [:k] do
    for v in [:k] do
      if selected seen v then
        seen := seen ||| (1 <<< (v ^^^ 1)) ||| (1 <<< p[v]!)
  return seen == 2 ^ k - 1

def weightedPartners (order : List Nat) (flags : Nat) : Array (Nat × Bool) := Id.run do
  let mut result := Array.replicate order.length (0, false)
  for j in [:order.length / 2] do
    let a := order.getD (2 * j + 1) 0
    let b := order.getD ((2 * j + 2) % order.length) 0
    let w := flags.testBit j
    result := result.set! a (b, w)
    result := result.set! b (a, w)
  return result

def potentialCandidate (s : State) : Nat := Id.run do
  let c := weightedPartners (List.range s.k) s.cflags
  let d := weightedPartners s.order s.dflags
  let mut seen := 0
  let mut result := 0
  for start in [:s.k] do
    if !(selected seen start) then
      let mut v := start
      let mut side := false
      let mut value := false
      for step in [:s.k] do
        if step == 0 || v != start then
          seen := seen ||| (1 <<< v)
          if value then result := result ||| (1 <<< v)
          let edge := if side then d[v]! else c[v]!
          v := edge.1
          value := value.xor edge.2
          side := !side
  return result

/-- A fast candidate list; the final verification uses literal cyclic arcs. -/
def goodPrefix (k flags mask : Nat) : Bool := Id.run do
  let mut parity := false
  let mut first := false
  let mut last := false
  let mut haveFirst := false
  let mut valid := true
  for i in [:k] do
    if selected mask i then
      if haveFirst then
        if last == parity then valid := false
      else
        first := parity
        haveFirst := true
      last := parity
    parity := parity.xor (arcOdd flags i)
  return valid && haveFirst && first == last

def localGood (k flags : Nat) : List Nat :=
  (List.range (2 ^ k)).filter fun mask =>
    let size := countBits k mask
    size % 2 == 1 && size ≤ k - 3 && goodPrefix k flags mask

def permuteMask (order : List Nat) (mask : Nat) : Nat := Id.run do
  let mut result := 0
  for i in [:order.length] do
    if selected mask i then result := result ||| (1 <<< order.getD i 0)
  return result

def singles (k mask : Nat) : List Nat :=
  ((List.range k).filter (selected mask)).map (fun i => 1 <<< i)

def partitionCandidate (k : Nat) (cg : List Nat) (dg : Nat) : Option (List Nat) := Id.run do
  let full := 2 ^ k - 1
  if k == 4 then return some [1, 2, 4, 8]
  let common := cg.filter fun mask => selected dg mask
  if let some a := common.find? (fun mask => countBits k mask == k - 3) then
    return some (a :: singles k (full ^^^ a))
  if k == 6 then return none
  let triples := common.filter fun mask => countBits k mask == 3
  if k == 10 then
    for a in common do
      if countBits k a == 5 then
        for b in triples do
          if a &&& b == 0 then
            return some ([a, b] ++ singles k (full ^^^ (a ||| b)))
  for a in triples do
    for b in triples do
      if a < b && a &&& b == 0 then
        if k == 8 then
          return some ([a, b] ++ singles k (full ^^^ (a ||| b)))
        for c in triples do
          if b < c && (a ||| b) &&& c == 0 then
            return some [a, b, c, full ^^^ (a ||| b ||| c)]
  return none

def checkState (s : State) (cg : List Nat) (dg : Nat) : Bool :=
  if verify s (.potential (potentialCandidate s)) then true
  else match partitionCandidate s.k cg dg with
    | none => false
    | some parts => verify s (.partition parts)

theorem checkState_sound (s : State) (cg : List Nat) (dg : Nat)
    (h : checkState s cg dg = true) : Conclusion s := by
  unfold checkState at h
  split at h
  next hp => exact verify_sound s _ hp
  next hp =>
    split at h
    next he => contradiction
    next parts he => exact verify_sound s (.partition parts) h

def checkOrder (k : Nat) (goods : Array (List Nat)) (tail : List Nat) : Bool := Id.run do
  let order := 0 :: tail
  if !(connectedDominoes k order) then return true
  let flags := oddFlags k
  let mut dgoods := Array.replicate (2 ^ (k / 2)) 0
  for df in flags do
    let mut bits := 0
    for mask in goods[df]! do
      bits := bits ||| (1 <<< permuteMask order mask)
    dgoods := dgoods.set! df bits
  for cf in flags do
    for df in flags do
      if !(checkState ⟨k, order, cf, df⟩ goods[cf]! dgoods[df]!) then return false
  return true

/-- Every odd C flag is included: no rotational symmetry reduction. -/
def allBoundaryStates (k : Nat) : Bool := Id.run do
  let goods := ((List.range (2 ^ (k / 2))).map (localGood k)).toArray
  let tails := permutations ((List.range (k - 1)).map (· + 1))
  return tails.all (checkOrder k goods)

end C20.Boundary

#print axioms C20.Boundary.checkState_sound

def main (args : List String) : IO UInt32 := do
  let sizes := if args.isEmpty then [4, 6, 8] else args.filterMap String.toNat?
  for k in sizes do
    let start ← IO.monoMsNow
    let result := C20.Boundary.allBoundaryStates k
    let stop ← IO.monoMsNow
    IO.println s!"Lean boundary computation k={k} result={result} elapsed_ms={stop - start}"
    if !result then return 1
  return 0
