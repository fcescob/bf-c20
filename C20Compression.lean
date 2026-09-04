import C20Kernel
import C20Expansion

/-! First-return compression derived from a nonempty selected set. -/

namespace C20

theorem walk_add {V : Type} (f : V → V) (a b : Nat) (v : V) :
    walk f (a + b) v = walk f a (walk f b v) := by
  induction a with
  | zero => simp only [Nat.zero_add, walk]
  | succ a ih => simpa only [Nat.succ_add, walk] using congrArg f ih

theorem walk_injective {V : Type} (c : Cycle V) (n : Nat) :
    Function.Injective (walk c.next n) := by
  intro u v h
  apply (c.toPerm ^ n).injective
  simpa only [toPerm_pow_apply] using h

theorem firstHit_le {V : Type} {f : V → V} {s : V → Bool} {v : V} {n t : Nat}
    (hn : FirstHit f s v n) (ht : s (walk f t v) = true) : n ≤ t := by
  by_contra h
  have hf := hn.2 t (by omega)
  rw [ht] at hf
  contradiction

noncomputable def firstDistance {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V) : Nat :=
  Classical.choose (exists_firstHit c.next s v (hits_of_connected c s connected nonempty v))

theorem firstDistance_spec {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V) :
    FirstHit c.next s v (firstDistance c s connected nonempty v) :=
  Classical.choose_spec (exists_firstHit c.next s v (hits_of_connected c s connected nonempty v))

theorem firstDistance_zero_iff {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V) :
    firstDistance c s connected nonempty v = 0 ↔ s v = true := by
  constructor
  · intro h
    have hs := (firstDistance_spec c s connected nonempty v).1
    simpa only [h, walk] using hs
  · intro h
    exact firstHit_unique c.next s v _ 0 (firstDistance_spec c s connected nonempty v)
      (firstHit_zero c.next s v h)

theorem firstDistance_step {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V)
    (hv : s v = false) :
    firstDistance c s connected nonempty v =
      firstDistance c s connected nonempty (c.next v) + 1 :=
  firstHit_unique c.next s v _ _ (firstDistance_spec c s connected nonempty v)
    (firstHit_succ c.next s v _ hv (firstDistance_spec c s connected nonempty (c.next v)))

noncomputable def firstIndex {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V) : {w // s w = true} :=
  ⟨walk c.next (firstDistance c s connected nonempty v) v,
    (firstDistance_spec c s connected nonempty v).1⟩

theorem firstIndex_selected {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : {w // s w = true}) :
    firstIndex c s connected nonempty v = v := by
  apply Subtype.ext
  change walk c.next (firstDistance c s connected nonempty v) v = v
  rw [(firstDistance_zero_iff c s connected nonempty v).mpr v.property]
  rfl

theorem firstIndex_step {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) (v : V)
    (hv : s v = false) :
    firstIndex c s connected nonempty v = firstIndex c s connected nonempty (c.next v) := by
  apply Subtype.ext
  change walk c.next (firstDistance c s connected nonempty v) v = _
  rw [firstDistance_step c s connected nonempty v hv, walk_succ_start]
  rfl

noncomputable def nextSelected {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    (v : {w // s w = true}) : {w // s w = true} :=
  firstIndex c s connected nonempty (c.next v)

theorem selected_return {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    (v : {w // s w = true}) :
    let n := firstDistance c s connected nonempty (c.next v) + 1
    0 < n ∧ walk c.next n v = (nextSelected c s connected nonempty v).val ∧
      (∀ i, 0 < i → i < n → s (walk c.next i v) = false) := by
  dsimp only
  refine ⟨by omega, ?_, ?_⟩
  · rw [walk_succ_start]
    rfl
  · intro i hp hi
    have he : i = (i - 1) + 1 := by omega
    rw [he, walk_succ_start]
    exact (firstDistance_spec c s connected nonempty (c.next v)).2 _ (by omega)

/-- Deleting unselected vertices preserves injectivity of the successor. -/
theorem nextSelected_injective {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) :
    Function.Injective (nextSelected c s connected nonempty) := by
  have ordered : ∀ u v : {w // s w = true},
      firstDistance c s connected nonempty (c.next u) ≤
        firstDistance c s connected nonempty (c.next v) →
      nextSelected c s connected nonempty u = nextSelected c s connected nonempty v → u = v := by
    intro u v hle heq
    let nu := firstDistance c s connected nonempty (c.next u) + 1
    let nv := firstDistance c s connected nonempty (c.next v) + 1
    have hu := selected_return c s connected nonempty u
    have hv := selected_return c s connected nonempty v
    have hlen : nu + (nv - nu) = nv := by dsimp [nu, nv]; omega
    have hw : walk c.next nu u = walk c.next nu (walk c.next (nv - nu) v) := by
      rw [← walk_add, hlen]
      exact hu.2.1.trans ((congrArg Subtype.val heq).trans hv.2.1.symm)
    have hstart := walk_injective c nu hw
    by_cases hz : nv - nu = 0
    · apply Subtype.ext
      simpa only [hz, walk] using hstart
    · have hp : 0 < nv - nu := by omega
      have hs : nv - nu < nv := by
        have hpos : 0 < nu := hu.1
        omega
      have hfalse := hv.2.2 (nv - nu) hp hs
      rw [← hstart, u.property] at hfalse
      contradiction
  intro u v h
  by_cases hle : firstDistance c s connected nonempty (c.next u) ≤
      firstDistance c s connected nonempty (c.next v)
  · exact ordered u v hle h
  · exact (ordered v u (by omega) h.symm).symm

theorem nextSelected_connected {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true) :
    ∀ u v : {w // s w = true}, ∃ n, walk (nextSelected c s connected nonempty) n u = v := by
  let idx := firstIndex c s connected nonempty
  let step := nextSelected c s connected nonempty
  have lift : ∀ n u, ∃ t, walk step t (idx u) = idx (walk c.next n u) := by
    intro n
    induction n with
    | zero => intro u; exact ⟨0, rfl⟩
    | succ n ih =>
      intro u
      rcases ih u with ⟨t, ht⟩
      cases hs : s (walk c.next n u) with
      | false =>
        refine ⟨t, ?_⟩
        exact ht.trans (firstIndex_step c s connected nonempty _ hs)
      | true =>
        have hid : idx (walk c.next n u) = ⟨walk c.next n u, hs⟩ :=
          firstIndex_selected c s connected nonempty ⟨_, hs⟩
        refine ⟨t + 1, ?_⟩
        rw [walk, ht, hid]
        rfl
  intro u v
  rcases connected u v with ⟨n, hn⟩
  rcases lift n u.val with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simpa only [idx, hn, firstIndex_selected] using ht

noncomputable def compressedCycle {V : Type} [Finite V] (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    [Nontrivial {w // s w = true}] : Cycle {w // s w = true} := by
  classical
  let step := nextSelected c s connected nonempty
  let p := Equiv.ofBijective step
    ⟨nextSelected_injective c s connected nonempty,
      Finite.surjective_of_injective (nextSelected_injective c s connected nonempty)⟩
  refine ⟨step, p.symm, p.symm_apply_apply, p.apply_symm_apply, ?_⟩
  intro v hv
  rcases exists_ne v with ⟨w, hw⟩
  rcases nextSelected_connected c s connected nonempty v w with ⟨n, hn⟩
  have fixed : ∀ t, walk step t v = v := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [walk, ih]; exact hv
  exact hw (hn.symm.trans (fixed n))

theorem compressedCycle_connected {V : Type} [Finite V] (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    [Nontrivial {w // s w = true}] :
    ConnectedCycle (compressedCycle c s connected nonempty) :=
  nextSelected_connected c s connected nonempty

noncomputable def compressedGap {V : Type} (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    (v : {w // s w = true}) : Bool :=
  parityBit (firstDistance c s connected nonempty (c.next v))

/-- Every nontrivial selected set supplies the actual expansion interface.
No distances, boundary order, or gap parities are assumed as hypotheses. -/
noncomputable def compressionExpansion {V : Type} [Finite V] (c : Cycle V) (s : V → Bool)
    (connected : ConnectedCycle c) (nonempty : ∃ v, s v = true)
    [Nontrivial {w // s w = true}] :
    Expansion c (compressedCycle c s connected nonempty) (compressedGap c s connected nonempty) := by
  classical
  refine ⟨firstIndex c s connected nonempty, firstDistance c s connected nonempty, ?_, ?_, ?_⟩
  · intro v hv
    have hs : s v = false := by
      cases h : s v
      · rfl
      · exact False.elim (hv ((firstDistance_zero_iff c s connected nonempty v).mpr h))
    exact ⟨firstDistance_step c s connected nonempty v hs,
      firstIndex_step c s connected nonempty v hs⟩
  · intro v hv
    have hs := (firstDistance_zero_iff c s connected nonempty v).mp hv
    have hi := firstIndex_selected c s connected nonempty ⟨v, hs⟩
    change firstIndex c s connected nonempty (c.next v) =
      nextSelected c s connected nonempty (firstIndex c s connected nonempty v)
    rw [hi]
    rfl
  · intro v hv
    have hs := (firstDistance_zero_iff c s connected nonempty v).mp hv
    have hi := firstIndex_selected c s connected nonempty ⟨v, hs⟩
    rw [hi]
    rfl

end C20

#print axioms C20.nextSelected_injective
#print axioms C20.compressionExpansion
