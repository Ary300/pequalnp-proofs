import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3630

open PEqualNP.CircuitLowerBounds

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

theorem fold_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false
  | [], w, i, _ => by simp
  | g :: gs, w, i, h => by
    rw [List.foldl_cons, fold_pre gs (step w g) i (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ h]

theorem fold_remap (f : ℕ → ℕ) (d : ℕ) : ∀ (gs : List Gate) (w1 w5 : List Bool),
    w5.length = w1.length + d → (∀ i, w1.length ≤ i → f i = i + d) →
    (∀ i, i < w1.length → f i < w5.length) →
    (∀ i, w1.getD i false = w5.getD (f i) false) →
    ∀ i, (gs.foldl step w1).getD i false = ((gs.map (rg f)).foldl step w5).getD (f i) false
  | [], w1, w5, _, _, _, hw => hw
  | g :: gs, w1, w5, hlen, hf, hlt, hw => by
    simp only [List.foldl_cons, List.map_cons]
    have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        (rg f g).op.eval ((rg f g).inputs.map fun i => w5.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact hw j
    apply fold_remap f d gs
    · simp [step, hlen]
      omega
    · intro i hi
      apply hf
      simp [step] at hi
      omega
    · intro i hi
      simp [step] at hi ⊢
      rcases Nat.lt_or_eq_of_le hi with h | h
      · have := hlt i h
        omega
      · subst h
        rw [hf _ le_rfl]
        omega
    · intro i
      rcases lt_trichotomy i w1.length with h | h | h
      · have h5 := hlt i h
        simp only [step]
        rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h5]
        exact hw i
      · subst h
        rw [hf _ le_rfl, ← hlen]
        simp [step] at hv ⊢
        exact hv
      · have e := hf i h.le
        simp only [step]
        rw [List.getD_eq_default, List.getD_eq_default]
        · simp
          omega
        · simp
          omega

theorem wires_eq (D : Circuit) (z : List Bool) : D.wires z = D.gates.foldl step z := rfl

theorem getD_z (x6 : Fin 9 → Bool) (i : Fin 9) :
    (List.ofFn x6 ++ [false]).getD i false = x6 i := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp
  fin_cases i <;> rfl

theorem build (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (pre : List Gate)
    (hpre : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (p9 p10 : ℕ) (A B : (Fin 9 → Bool) → Bool) (hk : 1 ≤ pre.length)
    (h9 : p9 < 10 + pre.length) (h10 : p10 < 10 + pre.length)
    (hA : ∀ x6 : Fin 9 → Bool, (pre.foldl step (List.ofFn x6 ++ [false])).getD p9 false = A x6)
    (hB : ∀ x6 : Fin 9 → Bool, (pre.foldl step (List.ofFn x6 ++ [false])).getD p10 false = B x6) :
    ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = C.size + pre.length ∧
      ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false]) =
        C.eval (List.ofFn x6 ++ [A x6, B x6]) := by
  let f : ℕ → ℕ := fun i =>
    if i < 9 then i else if i = 9 then p9 else if i = 10 then p10 else i + (pre.length - 1)
  refine ⟨⟨pre ++ C.gates.map (rg f), f C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hpre g hg
    · obtain ⟨h1, h2⟩ := hC g0 hg0
      exact ⟨h1, by simpa [rg] using h2⟩
  · simp [Circuit.size]
    omega
  · intro x6
    rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
    simp only
    rw [List.foldl_append]
    symm
    have hL := fold_len pre (List.ofFn x6 ++ [false])
    simp only [List.length_append, List.length_ofFn, List.length_singleton] at hL
    apply fold_remap f (pre.length - 1)
    · rw [hL]
      simp
      omega
    · intro i hi
      simp at hi
      simp only [f]
      split_ifs <;> omega
    · intro i hi
      simp at hi
      rw [hL]
      simp only [f]
      split_ifs <;> omega
    · intro i
      by_cases h : i < 9
      · simp only [f, h, ↓reduceIte]
        rw [fold_pre _ _ _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_append _ _ _ _ (by simpa using h)]
      · by_cases e9 : i = 9
        · subst e9
          have hf9 : f 9 = p9 := by simp [f]
          rw [hf9, hA, List.getD_append_right _ _ _ _ (by simp)]
          simp
        · by_cases e10 : i = 10
          · subst e10
            have hf10 : f 10 = p10 := by simp [f]
            rw [hf10, hB, List.getD_append_right _ _ _ _ (by simp)]
            simp
          · simp only [f, h, e9, e10, ↓reduceIte]
            rw [List.getD_eq_default, List.getD_eq_default]
            · rw [hL]
              omega
            · simp
              omega

end PEqualNP.Outside.L_meta_3630

theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) := by
  intro x1 x2 hC hcard
  have hpre1 : ∀ g ∈ [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)],
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    simp at hg
    subst hg
    simp
  have hA1 : ∀ x6 : Fin 9 → Bool,
      ([(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)].foldl
        PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false])).getD 10 false =
        (x6 0 || x6 4) := by
    intro x6
    simp [PEqualNP.Outside.L_meta_3630.step, PEqualNP.CircuitLowerBounds.GateOp.eval]
  by_cases h1 : x2.card ≤ 1
  · rw [ite_eq_left_iff.mpr (fun h => absurd (Or.inl h1) h)]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h1'
    · obtain rfl := Finset.card_eq_zero.mp h0
      obtain ⟨x5, hF, hs, he⟩ := PEqualNP.Outside.L_meta_3630.build x1 hC _ hpre1 10 9
        (fun x6 => x6 0 || x6 4) (fun _ => false) (by simp) (by simp) (by simp) hA1
        (by intro x6; simp [PEqualNP.Outside.L_meta_3630.step])
      refine ⟨x5, hF, by simp at hs; omega, ?_⟩
      intro x6
      rw [he x6]
      simp
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1'
      obtain ⟨x5, hF, hs, he⟩ := PEqualNP.Outside.L_meta_3630.build x1 hC _ hpre1 10 (a : ℕ)
        (fun x6 => x6 0 || x6 4) (fun x6 => x6 a) (by simp) (by simp) (by simp; omega) hA1
        (by
          intro x6
          simp only [List.foldl_cons, List.foldl_nil, PEqualNP.Outside.L_meta_3630.step]
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          exact PEqualNP.Outside.L_meta_3630.getD_z x6 a)
      refine ⟨x5, hF, by simp at hs; omega, ?_⟩
      intro x6
      rw [he x6]
      simp
  · have h2 : x2.card = 2 := by omega
    obtain ⟨a, c, hac, rfl⟩ := Finset.card_eq_two.mp h2
    by_cases h04 : ({a, c} : Finset (Fin 9)) = {0, 4}
    · rw [ite_eq_left_iff.mpr (fun h => absurd (Or.inr h04) h), h04]
      obtain ⟨x5, hF, hs, he⟩ := PEqualNP.Outside.L_meta_3630.build x1 hC _ hpre1 10 10
        (fun x6 => x6 0 || x6 4) (fun x6 => x6 0 || x6 4) (by simp) (by simp) (by simp) hA1 hA1
      refine ⟨x5, hF, by simp at hs; omega, ?_⟩
      intro x6
      rw [he x6]
      congr 3
      cases h0 : x6 0 <;> cases h4 : x6 4 <;> simp [h0, h4]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h (by rw [h2]; simp [h04]))]
      let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩
      let g1 : PEqualNP.CircuitLowerBounds.Gate :=
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(a : ℕ), (c : ℕ)]⟩
      have hpre2 : ∀ g ∈ [g0, g1],
          g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
            PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
          g.inputs.length ≤ 2 := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp [g0, g1]
      have hA2 : ∀ x6 : Fin 9 → Bool,
          ([g0, g1].foldl PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false])).getD 10 false =
            (x6 0 || x6 4) := by
        intro x6
        rw [List.foldl_cons, PEqualNP.Outside.L_meta_3630.fold_pre _ _ _
          (by simp [PEqualNP.Outside.L_meta_3630.step])]
        exact hA1 x6
      have hB2 : ∀ x6 : Fin 9 → Bool,
          ([g0, g1].foldl PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false])).getD 11 false =
            (x6 a || x6 c) := by
        intro x6
        have hl : (PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false]) g0).length = 11 := by
          simp [PEqualNP.Outside.L_meta_3630.step]
        have hw : ∀ i : Fin 9,
            (PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false]) g0).getD i false = x6 i := by
          intro i
          simp only [PEqualNP.Outside.L_meta_3630.step]
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          exact PEqualNP.Outside.L_meta_3630.getD_z x6 i
        show (PEqualNP.Outside.L_meta_3630.step
          (PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false]) g0) g1).getD 11 false = _
        generalize PEqualNP.Outside.L_meta_3630.step (List.ofFn x6 ++ [false]) g0 = W at hl hw ⊢
        simp only [PEqualNP.Outside.L_meta_3630.step]
        rw [List.getD_append_right _ _ _ _ (by omega), hl]
        simp only [g1, List.map_cons, List.map_nil, hw]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      obtain ⟨x5, hF, hs, he⟩ := PEqualNP.Outside.L_meta_3630.build x1 hC _ hpre2 10 11
        (fun x6 => x6 0 || x6 4) (fun x6 => x6 a || x6 c) (by simp) (by simp) (by simp) hA2 hB2
      refine ⟨x5, hF, by simp at hs; omega, ?_⟩
      intro x6
      rw [he x6]
      congr 3
      cases ha : x6 a <;> cases hc : x6 c <;> simp [ha, hc]
