import C20Coordinates

namespace C20

structure KernelDomino {m : Nat} (c : Cycle (Fin m)) (s : Fin m → Bool) where
  mate : {v // s v = true} → {v // s v = true}
  involutive : Function.Involutive mate
  adjacent : ∀ v, Adjacent c v.val (mate v).val

def KernelDomino.out {m : Nat} {c : Cycle (Fin m)} {s : Fin m → Bool}
    (dom : KernelDomino c s) (v : {v // s v = true}) : Bool :=
  decide (c.next v.val = (dom.mate v).val)

theorem KernelDomino.mate_prev {m : Nat} {c : Cycle (Fin m)} {s : Fin m → Bool}
    (dom : KernelDomino c s) (v : {v // s v = true}) (hv : dom.out v = false) :
    (dom.mate v).val = c.prev v.val := by
  have hn : c.next v.val ≠ (dom.mate v).val := by simpa [KernelDomino.out] using hv
  rcases dom.adjacent v with h | h
  · exact False.elim (hn h)
  · simpa only [c.prev_next] using congrArg c.prev h

theorem KernelDomino.out_toggle {m : Nat} (hm : 3 ≤ m) {c : Cycle (Fin m)}
    {s : Fin m → Bool} (dom : KernelDomino c s)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    (v : {v // s v = true}) :
    dom.out (nextSelected c s connected nonempty v) = !(dom.out v) := by
  let w := nextSelected c s connected nonempty v
  cases hv : dom.out v with
  | true =>
    have hnext : c.next v.val = (dom.mate v).val := by simpa [KernelDomino.out] using hv
    have hw : w = dom.mate v := by
      change firstIndex c s connected nonempty (c.next v.val) = dom.mate v
      rw [hnext]
      exact firstIndex_selected c s connected nonempty (dom.mate v)
    have hn : c.next (dom.mate v).val ≠ v.val := by
      intro hn
      have hprev := congrArg c.prev hn
      simp only [c.prev_next] at hprev
      exact cycle_neighbors_distinct hm c connected v.val (hnext.trans hprev)
    change dom.out w = !true
    rw [hw]
    simp [KernelDomino.out, dom.involutive v, hn]
  | false =>
    change dom.out w = !false
    suffices hw : dom.out w ≠ false by cases he : dom.out w <;> simp_all
    intro hw
    have hprev := dom.mate_prev w hw
    let n := firstDistance c s connected nonempty (c.next v.val) + 1
    have hr := selected_return c s connected nonempty v
    have hp : 0 < n := hr.1
    have hend : walk c.next n v.val = w.val := hr.2.1
    have hpre : walk c.next (n - 1) v.val = c.prev w.val := by
      have he : n = (n - 1) + 1 := by omega
      rw [he, walk] at hend
      simpa only [c.prev_next] using congrArg c.prev hend
    have hn : n = 1 := by
      by_contra hn
      have hf := hr.2.2 (n - 1) (by omega) (by omega)
      rw [hpre, ← hprev, (dom.mate w).property] at hf
      contradiction
    have hvw : c.next v.val = w.val := by simpa only [hn, walk] using hend
    have hmv : dom.mate w = v := by
      apply Subtype.ext
      rw [hprev, ← hvw, c.prev_next]
    have hmw : dom.mate v = w := by
      have h := congrArg dom.mate hmv
      exact h.symm.trans (dom.involutive w)
    have ht : dom.out v = true := by simp [KernelDomino.out, hmw, hvw]
    rw [hv] at ht
    contradiction

noncomputable def circuitKernelDomino {m : Nat} {c d : Cycle (Fin m)}
    (q : ShortCircuit c d) (cycle : Cycle (Fin m)) (dom : Domino cycle q.vertex) :
    KernelDomino cycle (kernelSelected q) := by
  let e := kernelEquiv q
  refine ⟨fun v => e (dom.mate (e.symm v)), ?_, ?_⟩
  · intro v
    simp only [e.symm_apply_apply, dom.involutive (e.symm v), e.apply_symm_apply]
  · intro v
    have h := dom.adjacent (e.symm v)
    have he : ∀ i, (e i).val = q.vertex i := fun _ => rfl
    rw [← he (e.symm v), e.apply_symm_apply, ← he (dom.mate (e.symm v))] at h
    exact h

theorem alternating_walk {V : Type} (step : V → V) (colour : V → Bool)
    (toggle : ∀ v, colour (step v) = !(colour v)) (root : V) (hr : colour root = true) :
    ∀ n, colour (walk step n root) = decide (n % 2 = 0) := by
  intro n
  induction n with
  | zero => exact hr
  | succ n ih =>
    rw [walk, toggle, ih]
    cases h : decide (n % 2 = 0) <;> simp_all <;> omega

/-- In coordinates beginning at a forward domino, every even position
starts an actual domino edge. Its following gap is therefore empty. -/
theorem coordinate_even_gap {m : Nat} (hm : 3 ≤ m) {c : Cycle (Fin m)}
    {s : Fin m → Bool} (dom : KernelDomino c s) (cc : ConnectedCycle c)
    (nonempty : ∃ v, s v = true) [Nontrivial {v // s v = true}]
    (root : {v // s v = true}) (hr : dom.out root = true)
    (k : Nat) (card : Fintype.card {v // s v = true} = k) (i : Fin k)
    (hi : i.val % 2 = 0) :
    firstDistance c s cc nonempty
      (c.next (cycleCoordinates (compressedCycle c s cc nonempty)
        (compressedCycle_connected c s cc nonempty) root k card i).val) = 0 := by
  have hout := alternating_walk (nextSelected c s cc nonempty) dom.out
    (dom.out_toggle hm cc nonempty) root hr i.val
  have hc : dom.out (cycleCoordinates (compressedCycle c s cc nonempty)
      (compressedCycle_connected c s cc nonempty) root k card i) = true := by
    simpa only [cycleCoordinates_apply, hi, decide_true] using hout
  have he : c.next (cycleCoordinates (compressedCycle c s cc nonempty)
      (compressedCycle_connected c s cc nonempty) root k card i).val =
      (dom.mate (cycleCoordinates (compressedCycle c s cc nonempty)
        (compressedCycle_connected c s cc nonempty) root k card i)).val := by
    simpa only [KernelDomino.out, decide_eq_true_eq] using hc
  apply (firstDistance_zero_iff c s cc nonempty _).mpr
  rw [he]
  exact (dom.mate _).property

end C20

#print axioms C20.KernelDomino.out_toggle
#print axioms C20.coordinate_even_gap
