import C20Compression
import C20Domino

namespace C20

theorem cycle_isCycle {V : Type} (c : Cycle V) (connected : ConnectedCycle c)
    (root : V) : c.toPerm.IsCycle := by
  refine ⟨root, c.next_ne root, ?_⟩
  intro v _
  rcases connected root v with ⟨n, hn⟩
  exact ⟨(n : Int), by simpa only [zpow_natCast, toPerm_pow_apply] using hn⟩

theorem cycle_order {V : Type} [Fintype V] [DecidableEq V] (c : Cycle V)
    (connected : ConnectedCycle c) (root : V) : orderOf c.toPerm = Fintype.card V := by
  have hs : c.toPerm.support = Finset.univ := by
    ext v
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact c.next_ne v
  rw [(cycle_isCycle c connected root).orderOf, hs]
  simp

/-- Numbering a connected cycle in successor order, beginning at root. -/
noncomputable def cycleCoordinates {V : Type} [Fintype V] [DecidableEq V]
    (c : Cycle V) (connected : ConnectedCycle c) (root : V)
    (k : Nat) (card : Fintype.card V = k) : Fin k ≃ V := by
  classical
  have hc := cycle_isCycle c connected root
  have horder : orderOf c.toPerm = k := (cycle_order c connected root).trans card
  apply Equiv.ofBijective (fun i : Fin k => walk c.next i.val root)
  constructor
  · intro i j h
    have hp : c.toPerm ^ i.val = c.toPerm ^ j.val := hc.pow_eq_pow_iff.mpr
      ⟨root, c.next_ne root, by simpa only [toPerm_pow_apply] using h⟩
    have hi : i.val % orderOf c.toPerm = j.val % orderOf c.toPerm := pow_inj_mod.mp hp
    rw [horder, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hi
    exact Fin.ext hi
  · intro v
    rcases connected root v with ⟨n, hn⟩
    have hsame : c.toPerm.SameCycle root v :=
      ⟨(n : Int), by simpa only [zpow_natCast, toPerm_pow_apply] using hn⟩
    rcases hsame.exists_pow_eq' with ⟨i, hi, he⟩
    refine ⟨⟨i, by simpa only [horder] using hi⟩, ?_⟩
    simpa only [toPerm_pow_apply] using he

theorem cycleCoordinates_apply {V : Type} [Fintype V] [DecidableEq V]
    (c : Cycle V) (connected : ConnectedCycle c) (root : V)
    (k : Nat) (card : Fintype.card V = k) (i : Fin k) :
    cycleCoordinates c connected root k card i = walk c.next i.val root := rfl

theorem cycleCoordinates_next {V : Type} [Fintype V] [DecidableEq V]
    (c : Cycle V) (connected : ConnectedCycle c) (root : V)
    (k : Nat) (card : Fintype.card V = k) (i : Fin k) :
    cycleCoordinates c connected root k card (cyclicNext i) =
      c.next (cycleCoordinates c connected root k card i) := by
  have horder : orderOf c.toPerm = k := (cycle_order c connected root).trans card
  have h := congrArg (fun p : Equiv.Perm V => p root) (pow_mod_orderOf c.toPerm (i.val + 1))
  simpa only [cycleCoordinates_apply, cyclicNext, horder, toPerm_pow_apply, walk] using h

def kernelSelected {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) (v : Fin m) : Bool :=
  decide (v ∈ circuitKernel q)

noncomputable def kernelEquiv {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    Fin q.size ≃ {v // kernelSelected q v = true} := by
  apply Equiv.ofBijective (fun i => ⟨q.vertex i, by simp [kernelSelected, mem_circuitKernel]⟩)
  constructor
  · intro i j h
    exact q.injective i j (congrArg Subtype.val h)
  · intro v
    have hv : v.val ∈ circuitKernel q := by simpa [kernelSelected] using v.property
    rcases (mem_circuitKernel q v.val).mp hv with ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩

theorem kernelSelected_card {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    Fintype.card {v // kernelSelected q v = true} = q.size := by
  rw [← Fintype.card_congr (kernelEquiv q)]
  simp

theorem kernelSelected_nonempty {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    ∃ v, kernelSelected q v = true := by
  rcases circuitKernel_nonempty q with ⟨v, hv⟩
  exact ⟨v, by simp [kernelSelected, hv]⟩

instance kernelSelected_nontrivial {m : Nat} {c d : Cycle (Fin m)} (q : ShortCircuit c d) :
    Nontrivial {v // kernelSelected q v = true} := by
  have hq := q.min_two
  let i : Fin q.size := ⟨0, by omega⟩
  let j : Fin q.size := ⟨1, by omega⟩
  refine ⟨⟨kernelEquiv q i, kernelEquiv q j, ?_⟩⟩
  intro h
  have h' := congrArg Fin.val ((kernelEquiv q).injective h)
  change 0 = 1 at h'
  contradiction

theorem circuit_size_cases {V : Type} {c d : Cycle V} (q : ShortCircuit c d) :
    q.size ∈ [2, 4, 6, 8, 10] := by
  have h1 := q.min_two
  have h2 := q.even
  have h3 := q.length_le_twenty
  simp only [List.mem_cons, List.mem_singleton]
  omega

end C20

#print axioms C20.cycleCoordinates_next
#print axioms C20.kernelSelected_card
