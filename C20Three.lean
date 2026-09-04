import C20

namespace C20

theorem odd_recurrence_two {V : Type} (f : V → V) (a : V → Nat)
    (r : Nat) (closed : ∀ v, walk f (2 * r + 1) v = v)
    (adjacent : ∀ v, a v + a (f v) = 2) : ∀ v, a v = 1 := by
  have h := odd_recurrence f (fun v => 2 * a v) r closed (fun v => by
    have h := adjacent v
    change 2 * a v + 2 * a (f v) = 4
    omega)
  intro v
  have hv := h v
  change 2 * a v = 2 at hv
  omega

/-- On two odd cycles, three perfect matchings with partitioned spokes
already partition every edge; no complement-cycle argument is needed. -/
theorem three_spoke_partition_cover {V : Type} (c d : Cycle V)
    (hc : OddCycle c) (hd : OddCycle d) (n a b : EdgeSet V)
    (hn : PerfectMatching c d n) (ha : PerfectMatching c d a) (hb : PerfectMatching c d b)
    (hs : ∀ v, bit (n.spoke v) + bit (a.spoke v) + bit (b.spoke v) = 1) :
    DoubleCover c d ⟨n, ⟨n, a, a, b, b⟩⟩ := by
  apply tait_double_cover c d n a b hn ha hb hs
  · rcases hc with ⟨r, hr⟩
    apply odd_recurrence_two c.next _ r hr
    intro v
    have h1 := hn.1 (c.next v)
    have h2 := ha.1 (c.next v)
    have h3 := hb.1 (c.next v)
    have h4 := hs (c.next v)
    simp only [c.prev_next] at h1 h2 h3
    omega
  · rcases hd with ⟨r, hr⟩
    apply odd_recurrence_two d.next _ r hr
    intro v
    have h1 := hn.2 (d.next v)
    have h2 := ha.2 (d.next v)
    have h3 := hb.2 (d.next v)
    have h4 := hs (d.next v)
    simp only [d.prev_next] at h1 h2 h3
    omega

end C20

#print axioms C20.three_spoke_partition_cover
