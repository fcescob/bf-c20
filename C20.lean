import Std

/-!+# The unbounded cover-lifting step in the C20 construction

This file proves the final, unbounded matching-cover implication. It does
not formalize the short-circuit reduction or the 9,474,568-case boundary
lemma. Those are supplied by PROOF.md and the C++ certificate checker.
There are no additional axioms, admitted proofs, or native_decide calls.

Vertices on the two cycles have a common type V, identified by the spoke
matching. An edge set is encoded by three Boolean indicator functions:
spokes and the outgoing edges of each of the two cycles. The three-term
incidence equations below mean exactly one selected edge at each vertex.
No finiteness bound on V or on the odd cycle length occurs in the lifting
theorem. A cycle-permutation graph instantiates this model by taking V to
be its spoke positions and taking next/prev from the two cyclic orders.
-/

namespace C20

def bit (b : Bool) : Nat := if b then 1 else 0

def walk {V : Type} (f : V → V) : Nat → V → V
  | 0, v => v
  | n + 1, v => f (walk f n v)

/-- Successor and predecessor on a cycle. Distinctness excludes loops. -/
structure Cycle (V : Type) where
  next : V → V
  prev : V → V
  prev_next : ∀ v, prev (next v) = v
  next_prev : ∀ v, next (prev v) = v
  next_ne : ∀ v, next v ≠ v

/-- Every orbit closes after one common odd number of steps. This is
weaker than being one odd cycle, so applies to an odd cycle of any size. -/
def OddCycle {V : Type} (c : Cycle V) : Prop :=
  ∃ r : Nat, ∀ v, walk c.next (2 * r + 1) v = v

/-- An edge set in the graph consisting of two cycles and their spokes. -/
structure EdgeSet (V : Type) where
  spoke : V → Bool
  outer : V → Bool
  inner : V → Bool

/-- The exact perfect-matching condition at both copies of every vertex. -/
def PerfectMatching {V : Type} (c d : Cycle V) (p : EdgeSet V) : Prop :=
  (∀ v, bit (p.spoke v) + bit (p.outer (c.prev v)) + bit (p.outer v) = 1) ∧
  (∀ v, bit (p.spoke v) + bit (p.inner (d.prev v)) + bit (p.inner v) = 1)

def spokes (V : Type) : EdgeSet V :=
  ⟨fun _ => true, fun _ => false, fun _ => false⟩

theorem spokes_perfect {V : Type} (c d : Cycle V) :
    PerfectMatching c d (spokes V) := by
  constructor <;> intro v <;> rfl

/-- On an odd closed orbit, adjacent multiplicities summing to four
force every multiplicity to be two. This is the unbounded parity step. -/
theorem odd_recurrence {V : Type} (f : V → V) (a : V → Nat)
    (r : Nat) (closed : ∀ v, walk f (2 * r + 1) v = v)
    (adjacent : ∀ v, a v + a (f v) = 4) : ∀ v, a v = 2 := by
  have two : ∀ v, a (f (f v)) = a v := by
    intro v
    have h₀ := adjacent v
    have h₁ := adjacent (f v)
    omega
  have even : ∀ n v, a (walk f (2 * n) v) = a v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      have e : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [e]
      simp only [walk]
      rw [two, ih]
  intro v
  have back := closed v
  have last := adjacent (walk f (2 * r) v)
  change a (walk f (2 * r) v) + a (walk f (2 * r + 1) v) = 4 at last
  rw [even r v, back] at last
  omega

/-- An explicit ordered five-tuple, avoiding external finite-sum libraries. -/
structure Five (α : Type) where
  p₀ : α
  p₁ : α
  p₂ : α
  p₃ : α
  p₄ : α

def total {α : Type} (p : Five α) (f : α → Nat) : Nat :=
  f p.p₀ + f p.p₁ + f p.p₂ + f p.p₃ + f p.p₄

def AllFive {α : Type} (p : Five α) (P : α → Prop) : Prop :=
  P p.p₀ ∧ P p.p₁ ∧ P p.p₂ ∧ P p.p₃ ∧ P p.p₄

/-- Five perfect matchings whose spokes partition V have cycle-edge
multiplicity two on both odd cycles, with no graph-order bound. -/
theorem five_multiplicity {V : Type} (c d : Cycle V)
    (hc : OddCycle c) (hd : OddCycle d) (p : Five (EdgeSet V))
    (hp : AllFive p (PerfectMatching c d))
    (hs : ∀ v, total p (fun q => bit (q.spoke v)) = 1) :
    (∀ v, total p (fun q => bit (q.outer v)) = 2) ∧
    (∀ v, total p (fun q => bit (q.inner v)) = 2) := by
  rcases hp with ⟨h₀, h₁, h₂, h₃, h₄⟩
  have outerAdj : ∀ v, total p (fun q => bit (q.outer v)) +
      total p (fun q => bit (q.outer (c.next v))) = 4 := by
    intro v
    have t₀ := h₀.1 (c.next v)
    have t₁ := h₁.1 (c.next v)
    have t₂ := h₂.1 (c.next v)
    have t₃ := h₃.1 (c.next v)
    have t₄ := h₄.1 (c.next v)
    have s := hs (c.next v)
    simp only [c.prev_next] at t₀ t₁ t₂ t₃ t₄
    simp only [total] at s ⊢
    omega
  have innerAdj : ∀ v, total p (fun q => bit (q.inner v)) +
      total p (fun q => bit (q.inner (d.next v))) = 4 := by
    intro v
    have t₀ := h₀.2 (d.next v)
    have t₁ := h₁.2 (d.next v)
    have t₂ := h₂.2 (d.next v)
    have t₃ := h₃.2 (d.next v)
    have t₄ := h₄.2 (d.next v)
    have s := hs (d.next v)
    simp only [d.prev_next] at t₀ t₁ t₂ t₃ t₄
    simp only [total] at s ⊢
    omega
  rcases hc with ⟨r, hr⟩
  rcases hd with ⟨s, ht⟩
  exact ⟨odd_recurrence c.next _ r hr outerAdj,
    odd_recurrence d.next _ s ht innerAdj⟩

/-- Six edge sets: one distinguished matching followed by five more. -/
structure Six (V : Type) where
  first : EdgeSet V
  rest : Five (EdgeSet V)

/-- A Berge–Fulkerson cover: six perfect matchings, every edge twice.
Repeated matchings are permitted and their multiplicities count. -/
def DoubleCover {V : Type} (c d : Cycle V) (s : Six V) : Prop :=
  PerfectMatching c d s.first ∧
  AllFive s.rest (PerfectMatching c d) ∧
  (∀ v, bit (s.first.spoke v) + total s.rest (fun p => bit (p.spoke v)) = 2) ∧
  (∀ v, bit (s.first.outer v) + total s.rest (fun p => bit (p.outer v)) = 2) ∧
  (∀ v, bit (s.first.inner v) + total s.rest (fun p => bit (p.inner v)) = 2)

/-- The main formal lifting theorem. Its hypotheses require the five
perfect matchings constructed from the common-good partition in PROOF.md.
It neither assumes nor derives the finite boundary lemma. -/
theorem five_matchings_cover {V : Type} (c d : Cycle V)
    (hc : OddCycle c) (hd : OddCycle d) (p : Five (EdgeSet V))
    (hp : AllFive p (PerfectMatching c d))
    (hs : ∀ v, total p (fun q => bit (q.spoke v)) = 1) :
    DoubleCover c d ⟨spokes V, p⟩ := by
  have h := five_multiplicity c d hc hd p hp hs
  refine ⟨spokes_perfect c d, hp, ?_, ?_, ?_⟩
  · intro v
    change 1 + total p (fun q => bit (q.spoke v)) = 2
    rw [hs]
  · intro v
    change 0 + total p (fun q => bit (q.outer v)) = 2
    simpa using h.1 v
  · intro v
    change 0 + total p (fun q => bit (q.inner v)) = 2
    simpa using h.2 v

/-- The other branch: doubling a three-colour perfect-matching partition. -/
theorem tait_double_cover {V : Type} (c d : Cycle V) (n a b : EdgeSet V)
    (hn : PerfectMatching c d n) (ha : PerfectMatching c d a)
    (hb : PerfectMatching c d b)
    (hs : ∀ v, bit (n.spoke v) + bit (a.spoke v) + bit (b.spoke v) = 1)
    (ho : ∀ v, bit (n.outer v) + bit (a.outer v) + bit (b.outer v) = 1)
    (hi : ∀ v, bit (n.inner v) + bit (a.inner v) + bit (b.inner v) = 1) :
    DoubleCover c d ⟨n, ⟨n, a, a, b, b⟩⟩ := by
  refine ⟨hn, ⟨hn, ha, ha, hb, hb⟩, ?_, ?_, ?_⟩
  · intro v; have h := hs v; simp only [total]; omega
  · intro v; have h := ho v; simp only [total]; omega
  · intro v; have h := hi v; simp only [total]; omega

/-! ## Constructing the perfect matchings from odd-gap data

For a selected spoke set S, distance v is the number of successor steps
from v to the next S-position, allowing zero at an S-position itself.
The three laws below express exactly the local facts used in constructing
the alternating matching on the paths between S-positions. In particular,
after a selected position the remaining distance is even, because the
whole gap has odd edge length. No distance bound is imposed.
-/

structure GapWitness {V : Type} (c : Cycle V) (selected : V → Bool) where
  distance : V → Nat
  zero_iff : ∀ v, distance v = 0 ↔ selected v = true
  step : ∀ v, selected v = false → distance v = distance (c.next v) + 1
  after_even : ∀ v, selected v = true → distance (c.next v) % 2 = 0

/-- Match along a gap starting at every positive even remaining distance. -/
def gapEdges {V : Type} {c : Cycle V} {s : V → Bool}
    (g : GapWitness c s) (v : V) : Bool :=
  decide (0 < g.distance v ∧ g.distance v % 2 = 0)

theorem gap_incidence {V : Type} {c : Cycle V} {s : V → Bool}
    (g : GapWitness c s) (v : V) :
    bit (s v) + bit (gapEdges g (c.prev v)) + bit (gapEdges g v) = 1 := by
  have z := g.zero_iff v
  have zp := g.zero_iff (c.prev v)
  have st := g.step (c.prev v)
  have ev := g.after_even (c.prev v)
  simp only [c.next_prev] at st ev
  cases hv : s v <;> cases hp : s (c.prev v) <;>
    simp only [hv, hp, Bool.false_eq_true, Bool.true_eq_false,
      iff_false, iff_true] at z zp st ev <;>
    simp only [bit, gapEdges, hv, Bool.false_eq_true, Bool.true_eq_true,
      decide_eq_true_eq] <;>
    (repeat' first | split | progress subst_vars) <;> omega

/-- One spoke class with odd-gap distance data on each of the two cycles. -/
structure GoodClass {V : Type} (c d : Cycle V) where
  selected : V → Bool
  outerGap : GapWitness c selected
  innerGap : GapWitness d selected

def classMatching {V : Type} {c d : Cycle V} (s : GoodClass c d) : EdgeSet V :=
  ⟨s.selected, gapEdges s.outerGap, gapEdges s.innerGap⟩

theorem class_matching_perfect {V : Type} {c d : Cycle V}
    (s : GoodClass c d) : PerfectMatching c d (classMatching s) := by
  exact ⟨gap_incidence s.outerGap, gap_incidence s.innerGap⟩

def classMatchings {V : Type} {c d : Cycle V} (s : Five (GoodClass c d)) :
    Five (EdgeSet V) :=
  ⟨classMatching s.p₀, classMatching s.p₁, classMatching s.p₂,
    classMatching s.p₃, classMatching s.p₄⟩

/-- Constructive lifting from five classes with odd-gap data on both
cycles. This includes construction and proof of all six perfect matchings. -/
theorem good_partition_cover {V : Type} (c d : Cycle V)
    (hc : OddCycle c) (hd : OddCycle d) (s : Five (GoodClass c d))
    (partition : ∀ v, total s (fun q => bit (q.selected v)) = 1) :
    DoubleCover c d ⟨spokes V, classMatchings s⟩ := by
  apply five_matchings_cover c d hc hd
  · exact ⟨class_matching_perfect s.p₀, class_matching_perfect s.p₁,
      class_matching_perfect s.p₂, class_matching_perfect s.p₃,
      class_matching_perfect s.p₄⟩
  · exact partition

end C20

#print axioms C20.odd_recurrence
#print axioms C20.five_matchings_cover
#print axioms C20.tait_double_cover
#print axioms C20.good_partition_cover
