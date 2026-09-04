import C20

/-!+# From common-good cyclic arcs to the six perfect matchings

This supplies the distance witnesses previously required by C20.lean.
`FirstHit f s v n` means that walking n edges from v first reaches s.
For a selected v, first reaching s from its successor after n further
edges makes an arc of length n+1. Thus the good-arc condition is n even.
No bound on arc lengths or graph order occurs here.

This is still not the C20 short-circuit theorem: the boundary reduction
and finite boundary lemma must supply the common-good partition.
-/

namespace C20

theorem walk_succ_start {V : Type} (f : V → V) (n : Nat) (v : V) :
    walk f (n + 1) v = walk f n (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [walk] at ih ⊢; rw [ih]

def FirstHit {V : Type} (f : V → V) (s : V → Bool) (v : V) (n : Nat) : Prop :=
  s (walk f n v) = true ∧ ∀ i, i < n → s (walk f i v) = false

theorem firstHit_zero {V : Type} (f : V → V) (s : V → Bool) (v : V)
    (h : s v = true) : FirstHit f s v 0 := by
  refine ⟨h, ?_⟩
  intro i hi
  omega

theorem firstHit_succ {V : Type} (f : V → V) (s : V → Bool) (v : V)
    (n : Nat) (hv : s v = false) (h : FirstHit f s (f v) n) :
    FirstHit f s v (n + 1) := by
  constructor
  · rw [walk_succ_start]
    exact h.1
  · intro i hi
    cases i with
    | zero => exact hv
    | succ i =>
      rw [walk_succ_start]
      exact h.2 i (by omega)

theorem firstHit_unique {V : Type} (f : V → V) (s : V → Bool) (v : V)
    (n m : Nat) (hn : FirstHit f s v n) (hm : FirstHit f s v m) : n = m := by
  have hnm : ¬ n < m := by
    intro h
    have bad := hm.2 n h
    rw [hn.1] at bad
    contradiction
  have hmn : ¬ m < n := by
    intro h
    have bad := hn.2 m h
    rw [hm.1] at bad
    contradiction
  omega

def firstHitWithin {V : Type} (f : V → V) (s : V → Bool) : Nat → V → Nat
  | 0, _ => 0
  | n + 1, v => if s v then 0 else firstHitWithin f s n (f v) + 1

theorem firstHitWithin_spec {V : Type} (f : V → V) (s : V → Bool)
    (n : Nat) (v : V) (h : s (walk f n v) = true) :
    FirstHit f s v (firstHitWithin f s n v) := by
  induction n generalizing v with
  | zero => exact firstHit_zero f s v h
  | succ n ih =>
    cases hv : s v with
    | false =>
      have h' : s (walk f n (f v)) = true := by
        rw [← walk_succ_start]
        exact h
      simp only [firstHitWithin, hv, Bool.false_eq_true, ↓reduceIte]
      exact firstHit_succ f s v _ hv (ih (f v) h')
    | true =>
      simp only [firstHitWithin, hv, ↓reduceIte]
      exact firstHit_zero f s v hv

/-- Every existing hit has a well-defined first hit. -/
theorem exists_firstHit {V : Type} (f : V → V) (s : V → Bool) (v : V)
    (h : ∃ n, s (walk f n v) = true) : ∃ n, FirstHit f s v n := by
  rcases h with ⟨n, hn⟩
  exact ⟨firstHitWithin f s n v, firstHitWithin_spec f s n v hn⟩

/-- The good-arc condition, including the whole-cycle arc of a singleton. -/
def OddArcs {V : Type} (c : Cycle V) (s : V → Bool) : Prop :=
  ∀ v, s v = true → ∀ n, FirstHit c.next s (c.next v) n → n % 2 = 0

noncomputable def gapOfOddArcs {V : Type} (c : Cycle V) (s : V → Bool)
    (hits : ∀ v, ∃ n, s (walk c.next n v) = true)
    (odd : OddArcs c s) : GapWitness c s := by
  classical
  let dist := fun v => Classical.choose (exists_firstHit c.next s v (hits v))
  have spec : ∀ v, FirstHit c.next s v (dist v) :=
    fun v => Classical.choose_spec (exists_firstHit c.next s v (hits v))
  refine ⟨dist, ?_, ?_, ?_⟩
  · intro v
    constructor
    · intro hz
      have h := (spec v).1
      rw [hz] at h
      exact h
    · intro hv
      exact firstHit_unique c.next s v (dist v) 0 (spec v)
        (firstHit_zero c.next s v hv)
  · intro v hv
    exact firstHit_unique c.next s v _ _ (spec v)
      (firstHit_succ c.next s v _ hv (spec (c.next v)))
  · intro v hv
    exact odd v hv _ (spec (c.next v))

/-- Any position is reachable from any other by going around the cycle. -/
def ConnectedCycle {V : Type} (c : Cycle V) : Prop :=
  ∀ v w, ∃ n, walk c.next n v = w

theorem hits_of_connected {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ w, s w = true) :
    ∀ v, ∃ n, s (walk c.next n v) = true := by
  intro v
  rcases nonempty with ⟨w, hw⟩
  rcases connected v w with ⟨n, hn⟩
  exact ⟨n, by rw [hn]; exact hw⟩

/-- A nonempty class whose successive selected positions have odd arcs
in each cyclic order. No distance functions are assumed as input. -/
structure CommonGood {V : Type} (c d : Cycle V) where
  selected : V → Bool
  nonempty : ∃ v, selected v = true
  outerOdd : OddArcs c selected
  innerOdd : OddArcs d selected

noncomputable def commonGoodClass {V : Type} (c d : Cycle V)
    (cc : ConnectedCycle c) (dc : ConnectedCycle d)
    (s : CommonGood c d) : GoodClass c d :=
  ⟨s.selected,
    gapOfOddArcs c s.selected (hits_of_connected c s.selected cc s.nonempty) s.outerOdd,
    gapOfOddArcs d s.selected (hits_of_connected d s.selected dc s.nonempty) s.innerOdd⟩

noncomputable def commonGoodClasses {V : Type} (c d : Cycle V)
    (cc : ConnectedCycle c) (dc : ConnectedCycle d)
    (s : Five (CommonGood c d)) : Five (GoodClass c d) :=
  ⟨commonGoodClass c d cc dc s.p₀, commonGoodClass c d cc dc s.p₁,
    commonGoodClass c d cc dc s.p₂, commonGoodClass c d cc dc s.p₃,
    commonGoodClass c d cc dc s.p₄⟩

/-- The complete common-good-partition lifting implication in the written
proof, with no preconstructed matchings or distance witnesses assumed. -/
theorem common_good_partition_cover {V : Type} (c d : Cycle V)
    (co : OddCycle c) (do_ : OddCycle d)
    (cc : ConnectedCycle c) (dc : ConnectedCycle d)
    (s : Five (CommonGood c d))
    (partition : ∀ v, total s (fun q => bit (q.selected v)) = 1) :
    DoubleCover c d ⟨spokes V, classMatchings (commonGoodClasses c d cc dc s)⟩ := by
  apply good_partition_cover c d co do_
  exact partition

end C20

#print axioms C20.gapOfOddArcs
#print axioms C20.common_good_partition_cover
