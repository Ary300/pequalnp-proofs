import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

theorem mul_le_add_of_le_one {a b : ℕ} (h : a ≤ 1 ∨ b ≤ 1) : a * b ≤ a + b := by
  rcases h with h | h
  · interval_cases a <;> simp
  · interval_cases b <;> simp

theorem block_bound {N : ℕ} (inc : Fin N → Fin N → Prop)
    (huniq : ∀ p q : Fin N, p ≠ q → ∃! l : Fin N, inc p l ∧ inc q l)
    (A B : Finset (Fin N)) (hAB : ∀ p ∈ A, ∀ l ∈ B, inc p l) :
    A.card * B.card ≤ A.card + B.card := by
  apply mul_le_add_of_le_one
  by_contra hc
  push Not at hc
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc.1
  obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp hc.2
  obtain ⟨m, _, hm⟩ := huniq p q hpq
  have e1 := hm l ⟨hAB p hp l hl, hAB q hq l hl⟩
  have e2 := hm l' ⟨hAB p hp l' hl', hAB q hq l' hl'⟩
  exact hll (e1.trans e2.symm)

end PEqualNP.Outside.L_meta_3362

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m inc _ hk huniq A B hAB hcov
  let I : Finset (Fin N × Fin N) := Finset.univ.filter (fun pl => inc pl.1 pl.2)
  have hI : I.card = N * k := by
    have h1 : I.card = ∑ l : Fin N, (Finset.univ.filter (fun p => inc p l)).card := by
      simp only [I, Finset.card_filter]
      rw [Fintype.sum_prod_type_right]
    rw [h1]
    have h2 : ∀ l : Fin N, (Finset.univ.filter (fun p => inc p l)).card = k := by
      intro l
      rw [← hk l, Fintype.card_subtype]
    simp [h2]
  have hsub : I ⊆ (Finset.univ : Finset (Fin m)).biUnion (fun i => A i ×ˢ B i) := by
    intro pl hpl
    have hinc : inc pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    obtain ⟨i, hi1, hi2⟩ := hcov pl.1 pl.2 hinc
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨hi1, hi2⟩⟩
  calc N * k = I.card := hI.symm
    _ ≤ ((Finset.univ : Finset (Fin m)).biUnion (fun i => A i ×ˢ B i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin m, (A i ×ˢ B i).card := Finset.card_biUnion_le
    _ = ∑ i : Fin m, (A i).card * (B i).card := by simp [Finset.card_product]
    _ ≤ ∑ i : Fin m, ((A i).card + (B i).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact PEqualNP.Outside.L_meta_3362.block_bound inc huniq (A i) (B i) (hAB i)
