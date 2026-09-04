import C20Gaps

/-!+# Finite boundary witnesses and exhaustive-order coverage

The checker uses two direct witnesses: a binary potential on the weighted
complement graph, or four common-good classes. The binary potential is a
more explicit certificate of the original even-component alternative.

This module defines and proves the witness interface. The full finite
enumeration theorem and the graph-to-boundary reduction are still pending.
-/

namespace C20.Boundary

def permutationsFuel : Nat → List Nat → List (List Nat)
  | 0, xs => if xs.isEmpty then [[]] else []
  | n + 1, xs => xs.flatMap fun a =>
      (permutationsFuel n (xs.erase a)).map (a :: ·)

theorem permutationsFuel_complete (xs ys : List Nat) (h : ys.Perm xs) :
    ys ∈ permutationsFuel ys.length xs := by
  induction ys generalizing xs with
  | nil =>
    have hx : xs = [] := List.perm_nil.mp h.symm
    subst xs
    simp [permutationsFuel]
  | cons a ys ih =>
    have ht := List.cons_perm_iff_perm_erase.mp h
    simp only [List.length_cons, permutationsFuel, List.mem_flatMap, List.mem_map]
    exact ⟨a, ht.1, ys, ih _ ht.2, rfl⟩

def permutations (xs : List Nat) : List (List Nat) := permutationsFuel xs.length xs

theorem permutations_complete (xs ys : List Nat) (h : ys.Perm xs) :
    ys ∈ permutations xs := by
  unfold permutations
  rw [← h.length_eq]
  exact permutationsFuel_complete xs ys h

/-- Every permutation is covered, independently of the finite runtime.
This is the formal completeness gate for the eventual exhaustive check. -/
theorem all_permutations_sound (xs : List Nat) (p : List Nat → Bool)
    (h : (permutations xs).all p = true) :
    ∀ ys, ys.Perm xs → p ys = true := by
  intro ys hy
  exact List.all_eq_true.mp h ys (permutations_complete xs ys hy)

def selected (mask v : Nat) : Bool := mask.testBit v

/-- Edge-length parity of the arc leaving boundary index i. Domino arcs
have length one; the other arcs have length one plus the outside gap. -/
def arcOdd (flags i : Nat) : Bool :=
  if i % 2 == 0 then true else !(flags.testBit (i / 2))

def arcParity (k flags start length : Nat) : Bool :=
  (List.range length).foldl (fun p j => p.xor (arcOdd flags ((start + j) % k))) false

/-- The t-th following boundary position. -/
def positionAt (order : List Nat) (start t : Nat) : Nat :=
  order.getD ((start + t) % order.length) 0

/-- A selected start and a first later selected position, with no selected
boundary positions strictly between them. t=k includes singleton arcs. -/
def consecutive (mask : Nat) (order : List Nat) (start t : Nat) : Bool :=
  selected mask (positionAt order start 0) && selected mask (positionAt order start t) &&
    ((List.range (t - 1)).all fun j => !(selected mask (positionAt order start (j + 1))))

/-- Literal finite version of odd cyclic arcs; no prefix-field shortcut. -/
def good (mask : Nat) (order : List Nat) (flags : Nat) : Bool :=
  mask > 0 && mask < 2 ^ order.length &&
    (List.range order.length).all (fun start =>
      (List.range order.length).all (fun j =>
        !(consecutive mask order start (j + 1)) ||
          arcParity order.length flags start (j + 1)))

structure WeightedEdge where
  left : Nat
  right : Nat
  weight : Bool
  deriving Repr, DecidableEq

def gapEdges (order : List Nat) (flags : Nat) : List WeightedEdge :=
  (List.range (order.length / 2)).map fun j =>
    ⟨order.getD (2 * j + 1) 0,
      order.getD ((2 * j + 2) % order.length) 0,
      flags.testBit j⟩

def potentialOK (edges : List WeightedEdge) (potential : Nat) : Bool :=
  edges.all fun e =>
    (selected potential e.left).xor (selected potential e.right) == e.weight

theorem potentialOK_sound (edges : List WeightedEdge) (potential : Nat)
    (h : potentialOK edges potential = true) :
    ∀ e ∈ edges,
      (selected potential e.left).xor (selected potential e.right) = e.weight := by
  intro e he
  have ht := List.all_eq_true.mp h e he
  simpa using ht

structure State where
  k : Nat
  order : List Nat
  cflags : Nat
  dflags : Nat
  deriving Repr, DecidableEq

def edges (s : State) : List WeightedEdge :=
  gapEdges (List.range s.k) s.cflags ++ gapEdges s.order s.dflags

/-- Exact partition checks: four nonempty masks, each good in both orders,
and exactly one class at every boundary position. -/
def partitionOK (s : State) (parts : List Nat) : Bool :=
  parts.length == 4 &&
    parts.all (fun mask => good mask (List.range s.k) s.cflags && good mask s.order s.dflags) &&
    (List.range s.k).all (fun v =>
      (parts.filter (fun mask => selected mask v)).length == 1)

inductive Witness where
  | potential (bits : Nat)
  | partition (parts : List Nat)
  deriving Repr, DecidableEq

def verify (s : State) : Witness → Bool
  | .potential bits => potentialOK (edges s) bits
  | .partition parts => partitionOK s parts

/-- Exact logical conclusion certified by the finite verifier. -/
def Conclusion (s : State) : Prop :=
  (∃ bits, ∀ e ∈ edges s,
    (selected bits e.left).xor (selected bits e.right) = e.weight) ∨
  (∃ parts : List Nat, parts.length = 4 ∧
    (∀ mask ∈ parts, good mask (List.range s.k) s.cflags = true ∧
      good mask s.order s.dflags = true) ∧
    (∀ v, v < s.k → (parts.filter (fun mask => selected mask v)).length = 1))

theorem verify_sound (s : State) (w : Witness) (h : verify s w = true) :
    Conclusion s := by
  cases w with
  | potential bits =>
    exact Or.inl ⟨bits, potentialOK_sound (edges s) bits h⟩
  | partition parts =>
    change partitionOK s parts = true at h
    simp only [partitionOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    rcases h with ⟨⟨hlen, hgood⟩, hcover⟩
    refine Or.inr ⟨parts, hlen, ?_, ?_⟩
    · intro mask hm
      exact hgood mask hm
    · intro v hv
      exact hcover v (by simpa using hv)

end C20.Boundary

#print axioms C20.Boundary.all_permutations_sound
#print axioms C20.Boundary.verify_sound
