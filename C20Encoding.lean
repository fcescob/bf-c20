import C20Normalize
import C20BoundaryMatching
import Mathlib.Data.List.FinRange

namespace C20

def encodeBits {n : Nat} (f : Fin n → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn f)).toNat

theorem encodeBits_lt {n : Nat} (f : Fin n → Bool) : encodeBits f < 2 ^ n := by
  have h := (BitVec.ofBoolListLE (List.ofFn f)).isLt
  simpa only [encodeBits, List.length_ofFn] using h

theorem getD_ofFn {n : Nat} {V : Type} (f : Fin n → V) (i : Fin n) (fallback : V) :
    (List.ofFn f).getD i.val fallback = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem encodeBits_testBit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (encodeBits f).testBit i.val = f i := by
  rw [encodeBits, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, getD_ofFn]

theorem cyclicPrev_val {k : Nat} (i : Fin k) :
    ((cyclicPerm k).symm i).val = (i.val + k - 1) % k := by
  let j := (cyclicPerm k).symm i
  have h : cyclicNext j = i := (cyclicPerm k).apply_symm_apply i
  have hv := congrArg Fin.val h
  rw [cyclicNext_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  change j.val = _
  split_ifs at hv with hjk
  · have he : i.val + k - 1 = k + j.val := by omega
    simp [he, Nat.add_mod, Nat.mod_eq_of_lt hj]
  · have he : i.val + k - 1 = j.val := by omega
    rw [he, Nat.mod_eq_of_lt hj]

def orderLabels {W : Type} {k : Nat} (coords : Fin k ≃ W) (labels : W ≃ Fin k) : List Nat :=
  List.ofFn (fun i => (labels (coords i)).val)

theorem ofFn_values_range (k : Nat) :
    List.ofFn (fun i : Fin k => i.val) = List.range k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem orderLabels_perm {W : Type} {k : Nat} (coords : Fin k ≃ W) (labels : W ≃ Fin k) :
    (orderLabels coords labels).Perm (List.range k) := by
  have h := Equiv.Perm.ofFn_comp_perm (coords.trans labels) (fun i : Fin k => i.val)
  simpa only [orderLabels, Function.comp_def, Equiv.trans_apply, ofFn_values_range] using h

/-- The literal finite row equation is exactly the abstract weighted
boundary incidence equation, under verified cyclic coordinates. -/
theorem rowMatching_transfer {W : Type} {k : Nat} (b : Cycle W) (gap : W → Bool)
    (coords : Fin k ≃ W) (labels : W ≃ Fin k)
    (next : ∀ i, coords (cyclicNext i) = b.next (coords i))
    (flags mask edges : Nat) (gaps : ∀ i, gap (coords i) = Boundary.gapBit flags i.val)
    (row : Boundary.RowMatching (orderLabels coords labels) flags mask edges) :
    ∀ w, bit (Boundary.selected mask (labels w).val) +
      bit (boundaryIncoming b gap (fun v => Boundary.selected edges (labels v).val) w) +
      bit (Boundary.selected edges (labels w).val) = 1 := by
  intro w
  let i := coords.symm w
  let j := (cyclicPerm k).symm i
  have hci : coords i = w := coords.apply_symm_apply w
  have hnj : cyclicNext j = i := (cyclicPerm k).apply_symm_apply i
  have hcj : coords j = b.prev w := by
    have h := next j
    rw [hnj, hci] at h
    have h' := congrArg b.prev h
    simpa only [b.prev_next] using h'.symm
  have hlen : (orderLabels coords labels).length = k := List.length_ofFn
  have hrow := row i.val (by rw [hlen]; exact i.isLt)
  dsimp only at hrow
  rw [hlen, ← cyclicPrev_val i] at hrow
  change bit (Boundary.selected mask ((List.ofFn (fun t => (labels (coords t)).val)).getD i.val 0)) +
    bit ((Boundary.selected edges ((List.ofFn (fun t => (labels (coords t)).val)).getD j.val 0)).xor
      (Boundary.gapBit flags j.val)) +
    bit (Boundary.selected edges ((List.ofFn (fun t => (labels (coords t)).val)).getD i.val 0)) = 1 at hrow
  rw [getD_ofFn, getD_ofFn, ← gaps j, hci, hcj] at hrow
  exact hrow

end C20

#print axioms C20.encodeBits_testBit
#print axioms C20.rowMatching_transfer
