import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem fold_len : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length
  | [], w => by simp
  | g :: gs, w => by
    rw [List.foldl_cons, fold_len gs]
    simp [step]
    omega

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

theorem fold_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false
  | [], w, i, _ => by simp
  | g :: gs, w, i, h => by
    rw [List.foldl_cons, fold_pre gs (step w g) i (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ h]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

end PEqualNP.Outside.L_meta_2859

theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hmono hrb hm hp
  have hE : PEqualNP.CircuitMoves.eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map
          (PEqualNP.Outside.L_meta_2859.rg (PEqualNP.CircuitMoves.eraseRedirect n m p)),
        output := PEqualNP.CircuitMoves.eraseRedirect n m p C.output } := by
    rw [PEqualNP.CircuitMoves.eraseGate, if_pos hm]
    rfl
  rw [hE]
  have hlenD : (C.gates.take m ++ (C.gates.drop (m + 1)).map
      (PEqualNP.Outside.L_meta_2859.rg (PEqualNP.CircuitMoves.eraseRedirect n m p))).length + 1 =
      C.gates.length := by
    simp
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hmono g (List.mem_of_mem_take hg)
    · obtain ⟨h1, h2⟩ := hmono g0 (List.mem_of_mem_drop hg0)
      exact ⟨h1, by simpa [PEqualNP.Outside.L_meta_2859.rg] using h2⟩
  · intro j hj i hi
    simp only at hj
    rw [PEqualNP.Outside.L_meta_2859.gateAt_eq _ _ hj] at hi
    simp only at hi
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by simp; omega), List.getElem_take] at hi
      exact hrb j (by omega) i (by rw [PEqualNP.Outside.L_meta_2859.gateAt_eq C j (by omega)]; exact hi)
    · rw [List.getElem_append_right (by simp; omega)] at hi
      simp only [List.getElem_map, List.getElem_drop, PEqualNP.Outside.L_meta_2859.rg,
        List.mem_map, List.length_take] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hmin : min m C.gates.length = m := by omega
      simp only [hmin] at hi0
      have hidx : m + 1 + (j - m) < C.gates.length := by simp at hj; omega
      have := hrb (m + 1 + (j - m)) hidx i0
        (by rw [PEqualNP.Outside.L_meta_2859.gateAt_eq C _ hidx]; exact hi0)
      unfold PEqualNP.CircuitMoves.eraseRedirect
      split_ifs <;> omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · intro x hx
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
    have hz : (List.ofFn x).length = n := List.length_ofFn
    set P := (C.gates.take m).foldl PEqualNP.Outside.L_meta_2859.step (List.ofFn x) with hP
    have hPlen : P.length = n + m := by
      rw [hP, PEqualNP.Outside.L_meta_2859.fold_len, hz]
      simp
      omega
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm]
      simp
    have hC : C.wires (List.ofFn x) = (C.gates.drop (m + 1)).foldl PEqualNP.Outside.L_meta_2859.step
        (PEqualNP.Outside.L_meta_2859.step P C.gates[m]) := by
      show C.gates.foldl PEqualNP.Outside.L_meta_2859.step (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hD : PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map
            (PEqualNP.Outside.L_meta_2859.rg (PEqualNP.CircuitMoves.eraseRedirect n m p)),
          output := PEqualNP.CircuitMoves.eraseRedirect n m p C.output } (List.ofFn x) =
        ((C.gates.drop (m + 1)).map
          (PEqualNP.Outside.L_meta_2859.rg (PEqualNP.CircuitMoves.eraseRedirect n m p))).foldl
          PEqualNP.Outside.L_meta_2859.step P := by
      show List.foldl PEqualNP.Outside.L_meta_2859.step (List.ofFn x) _ = _
      rw [List.foldl_append]
    have hSlen : (PEqualNP.Outside.L_meta_2859.step P C.gates[m]).length = n + m + 1 := by
      simp [PEqualNP.Outside.L_meta_2859.step, hPlen]
    rw [hD, hC]
    symm
    apply PEqualNP.Outside.L_meta_2859.fold_remap
    · intro i hi
      rw [hSlen] at hi
      rw [hSlen, hPlen]
      unfold PEqualNP.CircuitMoves.eraseRedirect
      split_ifs <;> omega
    · intro i hi
      rw [hSlen] at hi
      rw [hPlen]
      unfold PEqualNP.CircuitMoves.eraseRedirect
      split_ifs <;> omega
    · intro i
      rcases lt_trichotomy i (n + m) with h | h | h
      · have hr : PEqualNP.CircuitMoves.eraseRedirect n m p i = i := by
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> omega
        rw [hr]
        simp only [PEqualNP.Outside.L_meta_2859.step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · have hr : PEqualNP.CircuitMoves.eraseRedirect n m p i = p := by
          unfold PEqualNP.CircuitMoves.eraseRedirect
          simp [h]
        rw [hr]
        rw [hC, PEqualNP.Outside.L_meta_2859.fold_pre _ _ _ (by omega),
          PEqualNP.Outside.L_meta_2859.fold_pre _ _ _ (by omega)] at hx
        rw [h, ← hx]
        simp only [PEqualNP.Outside.L_meta_2859.step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · have hr : PEqualNP.CircuitMoves.eraseRedirect n m p i = i - 1 := by
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> omega
        rw [hr, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
