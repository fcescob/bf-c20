import C20Statement
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!+# Finite-cycle facts used by the graph reduction

The cycle model in C20Statement is connected successor/predecessor
permutations on Fin m. Here it is connected to Mathlib's permutation
cycles, giving exact period m and a duplicate-free cyclic vertex list.
-/

namespace C20

def Cycle.toPerm {V : Type} (c : Cycle V) : Equiv.Perm V where
  toFun := c.next
  invFun := c.prev
  left_inv := c.prev_next
  right_inv := c.next_prev

theorem toPerm_pow_apply {V : Type} (c : Cycle V) (n : Nat) (v : V) :
    (c.toPerm ^ n) v = walk c.next n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    rfl

theorem toPerm_isCycle {m : Nat} (hm : 0 < m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) : c.toPerm.IsCycle := by
  let root : Fin m := ⟨0, hm⟩
  refine ⟨root, c.next_ne root, ?_⟩
  intro v _
  rcases connected root v with ⟨n, hn⟩
  refine ⟨(n : Int), ?_⟩
  simpa only [zpow_natCast, toPerm_pow_apply] using hn

theorem toPerm_support {m : Nat} (c : Cycle (Fin m)) :
    c.toPerm.support = Finset.univ := by
  ext v
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  exact c.next_ne v

theorem toPerm_order {m : Nat} (hm : 0 < m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) : orderOf c.toPerm = m := by
  rw [(toPerm_isCycle hm c connected).orderOf, toPerm_support]
  simp

theorem walk_full_cycle {m : Nat} (hm : 0 < m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) : ∀ v, walk c.next m v = v := by
  intro v
  have h := congrArg (fun p : Equiv.Perm (Fin m) => p v)
    (pow_orderOf_eq_one c.toPerm)
  simpa only [toPerm_order hm c connected, toPerm_pow_apply,
    Equiv.Perm.one_apply] using h

theorem oddCycle_of_odd_card {m : Nat} (hm : m % 2 = 1) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) : OddCycle c := by
  have hp : 0 < m := by omega
  have he : 2 * (m / 2) + 1 = m := by omega
  refine ⟨m / 2, ?_⟩
  rw [he]
  exact walk_full_cycle hp c connected

theorem walk_return_iff {m : Nat} (hm : 0 < m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) (v : Fin m) (n : Nat) :
    walk c.next n v = v ↔ m ∣ n := by
  rw [← toPerm_pow_apply c n v,
    ← (toPerm_isCycle hm c connected).pow_eq_one_iff' (c.next_ne v),
    ← orderOf_dvd_iff_pow_eq_one, toPerm_order hm c connected]

theorem cycle_neighbors_distinct {m : Nat} (hm : 3 ≤ m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) (v : Fin m) : c.next v ≠ c.prev v := by
  intro h
  have hw : walk c.next 2 v = v := by
    change c.next (c.next v) = v
    rw [h, c.next_prev]
  have hd := (walk_return_iff (by omega) c connected v 2).mp hw
  have hsmall : m ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

/-- Every vertex occurs exactly once in a cyclic list representing c. -/
theorem exists_cycle_list {m : Nat} (hm : 0 < m) (c : Cycle (Fin m))
    (connected : ConnectedCycle c) :
    ∃ order : List (Fin m), order.Nodup ∧ order.length = m ∧
      (∀ v, v ∈ order) ∧ order.formPerm = c.toPerm := by
  let root : Fin m := ⟨0, hm⟩
  have hc := toPerm_isCycle hm c connected
  have hr : c.toPerm root ≠ root := c.next_ne root
  have hcycle : c.toPerm.cycleOf root = c.toPerm := hc.cycleOf_eq hr
  refine ⟨c.toPerm.toList root, Equiv.Perm.nodup_toList _ _, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.length_toList, hcycle, toPerm_support]
    simp
  · intro v
    rw [Equiv.Perm.mem_toList_iff]
    constructor
    · rcases connected root v with ⟨n, hn⟩
      exact ⟨(n : Int), by simpa only [zpow_natCast, toPerm_pow_apply] using hn⟩
    · exact Equiv.Perm.mem_support.mpr (c.next_ne root)
  · rw [Equiv.Perm.formPerm_toList, hcycle]

end C20

#print axioms C20.walk_full_cycle
#print axioms C20.exists_cycle_list
