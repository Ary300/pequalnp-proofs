import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4671

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem fold_remap (f : ℕ → ℕ) : ∀ (gs : List Gate) (w1 w5 : List Bool),
    (∀ i, w1.length ≤ i → f i + w1.length = i + w5.length) →
    (∀ i, i < w1.length → f i < w5.length) →
    (∀ i, w1.getD i false = w5.getD (f i) false) →
    ∀ i, (gs.foldl step w1).getD i false = ((gs.map (rg f)).foldl step w5).getD (f i) false
  | [], w1, w5, _, _, hw => hw
  | g :: gs, w1, w5, hf, hlt, hw => by
    simp only [List.foldl_cons, List.map_cons]
    have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        (rg f g).op.eval ((rg f g).inputs.map fun i => w5.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact hw j
    apply fold_remap f gs
    · intro i hi
      simp [step] at hi ⊢
      have := hf i (by omega)
      omega
    · intro i hi
      simp [step] at hi ⊢
      rcases Nat.lt_or_eq_of_le hi with h | h
      · have := hlt i h
        omega
      · subst h
        have := hf _ le_rfl
        omega
    · intro i
      rcases lt_trichotomy i w1.length with h | h | h
      · have h5 := hlt i h
        simp only [step]
        rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h5]
        exact hw i
      · subst h
        have e := hf _ le_rfl
        have e' : f w1.length = w5.length := by omega
        rw [e']
        simp [step] at hv ⊢
        exact hv
      · have e := hf i h.le
        simp only [step]
        rw [List.getD_eq_default, List.getD_eq_default]
        · simp
          omega
        · simp
          omega

end PEqualNP.Outside.L_meta_4671

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro a b r C w hmono hout hw
  let f : ℕ → ℕ := fun i => if h : i < a then (r ⟨i, h⟩ : ℕ) else i - a + b
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_4671.rg f), f C.output⟩, f w, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hmono g0 hg0
    exact ⟨h1, by simpa [PEqualNP.Outside.L_meta_4671.rg] using h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_map]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hout
    simp only [f]
    split_ifs with h
    · have := (r ⟨C.output, h⟩).isLt
      omega
    · omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_map]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hw
    simp only [f]
    split_ifs with h
    · have := (r ⟨w, h⟩).isLt
      omega
    · omega
  · intro x
    have key := PEqualNP.Outside.L_meta_4671.fold_remap f C.gates (List.ofFn (x ∘ r)) (List.ofFn x)
      (by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        simp only [f, dif_neg (show ¬ i < a by omega)]
        omega)
      (by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        simp only [f, dif_pos hi]
        exact (r ⟨i, hi⟩).isLt)
      (by
        intro i
        by_cases hi : i < a
        · simp only [f, dif_pos hi]
          simp [List.getD_eq_getElem?_getD, hi]
        · simp only [f, dif_neg hi]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp)])
    constructor
    · show ((C.gates.map _).foldl PEqualNP.Outside.L_meta_4671.step (List.ofFn x)).getD (f C.output) false =
        (C.gates.foldl PEqualNP.Outside.L_meta_4671.step (List.ofFn (x ∘ r))).getD C.output false
      exact (key C.output).symm
    · show ((C.gates.map _).foldl PEqualNP.Outside.L_meta_4671.step (List.ofFn x)).getD (f w) false =
        (C.gates.foldl PEqualNP.Outside.L_meta_4671.step (List.ofFn (x ∘ r))).getD w false
      exact (key w).symm
