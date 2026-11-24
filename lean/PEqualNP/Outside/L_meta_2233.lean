import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def F (n : ℕ) (C : Circuit) (k : ℕ) : List (List ℕ) := (C.gates.take k).foldl (orStep n) []

theorem F_succ (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    F n C (k + 1) = orStep n (F n C k) C.gates[k] := by
  simp only [F]
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem F_len (n : ℕ) (C : Circuit) : ∀ k, k ≤ C.gates.length → (F n C k).length = k
  | 0, _ => by simp [F]
  | k + 1, hk => by
    rw [F_succ n C k (by omega)]
    simp [orStep, F_len n C k (by omega)]

theorem F_stable (n : ℕ) (C : Circuit) (k : ℕ) : ∀ d, k + d ≤ C.gates.length →
    ∀ j < k, (F n C (k + d)).getD j [] = (F n C k).getD j []
  | 0, _ => by simp
  | d + 1, hd => by
    intro j hj
    rw [show k + (d + 1) = (k + d) + 1 by omega, F_succ n C (k + d) (by omega), orStep,
      List.getD_append _ _ _ _ (by rw [F_len n C _ (by omega)]; omega)]
    exact F_stable n C k d (by omega) j hj

theorem orSets_eq (n : ℕ) (C : Circuit) : orSets n C = F n C C.gates.length := by
  simp [orSets, F]

theorem orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  rw [orSets_eq]
  exact F_len n C _ le_rfl

theorem stable_full (n : ℕ) (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) (j : ℕ) (hj : j < k) :
    (orSets n C).getD j [] = (F n C k).getD j [] := by
  rw [orSets_eq]
  have := F_stable n C k (C.gates.length - k) (by omega) j hj
  rw [show k + (C.gates.length - k) = C.gates.length by omega] at this
  exact this

theorem entry0 (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length) :
    (orSets n C).getD m [] = (orStep n (F n C m) C.gates[m]).getD m [] := by
  rw [stable_full n C (m + 1) (by omega) m (by omega), F_succ n C m hm]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem lt_of_mem (n : ℕ) (C : Circuit) {m g : ℕ} (h : g ∈ (orSets n C).getD m []) :
    m < C.gates.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [orSets_len]; omega)] at h
  simp at h

theorem self_mem (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length) :
    m ∈ (orSets n C).getD m [] := by
  rw [entry0 n C m hm]
  simp only [orStep]
  rw [List.getD_append_right _ _ _ _ (by rw [F_len n C m (by omega)]), F_len n C m (by omega)]
  simp

theorem inv (n : ℕ) (C : Circuit) {m g : ℕ} (h : g ∈ (orSets n C).getD m []) :
    g = m ∨ ((gateAt C m).op = GateOp.or ∧ ∃ w ∈ (gateAt C m).inputs, n ≤ w ∧ w < n + m ∧
      g ∈ (orSets n C).getD (w - n) []) := by
  have hm := lt_of_mem n C h
  rw [entry0 n C m hm] at h
  simp only [orStep] at h
  rw [List.getD_append_right _ _ _ _ (by rw [F_len n C m (by omega)]), F_len n C m (by omega)] at h
  simp only [Nat.sub_self, List.getD_cons_zero] at h
  rw [gateAt_eq C m hm]
  rcases List.mem_cons.mp h with e | h
  · exact Or.inl e
  · right
    split_ifs at h with hor
    · refine ⟨hor, ?_⟩
      obtain ⟨w, hw, hg⟩ := List.mem_flatMap.mp h
      rw [List.mem_filter] at hw
      simp only [decide_eq_true_eq] at hw
      refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
      rw [stable_full n C m (by omega) (w - n) (by omega)]
      exact hg
    · simp at h

theorem trans_mem (n : ℕ) (C : Circuit) {m w g : ℕ} (hm : m < C.gates.length)
    (hor : (gateAt C m).op = GateOp.or) (hw : w ∈ (gateAt C m).inputs) (h1 : n ≤ w)
    (h2 : w < n + m) (hg : g ∈ (orSets n C).getD (w - n) []) : g ∈ (orSets n C).getD m [] := by
  rw [gateAt_eq C m hm] at hor hw
  rw [entry0 n C m hm]
  simp only [orStep]
  rw [List.getD_append_right _ _ _ _ (by rw [F_len n C m (by omega)]), F_len n C m (by omega)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rw [if_pos hor]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨w, ?_, ?_⟩)
  · rw [List.mem_filter]
    exact ⟨hw, by simp [h1, h2]⟩
  · rw [← stable_full n C m (by omega) (w - n) (by omega)]
    exact hg

theorem desc (n : ℕ) (C : Circuit) (x : ℕ) : ∀ m, x ∈ (orSets n C).getD m [] → x ≠ m →
    ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ n + x ∈ (gateAt C k).inputs ∧
      k ∈ (orSets n C).getD m [] := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hx hne
    have hm := lt_of_mem n C hx
    rcases inv n C hx with e | ⟨hor, w, hw, h1, h2, h3⟩
    · exact absurd e hne
    · by_cases hxw : x = w - n
      · refine ⟨m, hm, hor, ?_, self_mem n C m hm⟩
        rw [show n + x = w by omega]
        exact hw
      · obtain ⟨k, hk, hkor, hkin, hkmem⟩ := ih (w - n) (by omega) h3 hxw
        exact ⟨k, hk, hkor, hkin, trans_mem n C hm hor hw h1 h2 hkmem⟩

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C Fs hC hF
  classical
  set D : Finset ℕ := (Finset.range C.gates.length).filter (fun i =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    PEqualNP.CleanedNonEdge.OrReaches n C C.output i) with hDdef
  have hD : Set.ncard {i : ℕ | i < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output i} = D.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [hDdef]
  rw [hD]
  by_cases hn : n ≤ C.output
  · set m := C.output - n with hmdef
    have hdisj : Disjoint Fs D := by
      rw [Finset.disjoint_left]
      intro x hx hxD
      have h1 := (hF x hx).2.1
      rw [hDdef, Finset.mem_filter] at hxD
      rw [h1] at hxD
      exact absurd hxD.2.1 (by intro h; cases h)
    have hex : ∀ x ∈ (Fs ∪ D).erase m, ∃ k ∈ D,
        n + x ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs := by
      intro x hx
      obtain ⟨hxm, hx⟩ := Finset.mem_erase.mp hx
      have hreach : PEqualNP.CleanedNonEdge.OrReaches n C C.output x := by
        rcases Finset.mem_union.mp hx with h | h
        · exact (hF x h).2.2
        · rw [hDdef, Finset.mem_filter] at h
          exact h.2.2
      obtain ⟨k, hk, hkor, hkin, hkmem⟩ :=
        PEqualNP.Outside.L_meta_2233.desc n C x m hreach.2 hxm
      refine ⟨k, ?_, hkin⟩
      rw [hDdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk, hkor, hn, hkmem⟩
    choose! φ hφD hφin using hex
    have hbound := Finset.card_le_mul_card_image_of_maps_to (f := φ) (s := (Fs ∪ D).erase m)
      (t := D) hφD 2 (by
        intro h hh
        have hhlen : h < C.gates.length := by
          rw [hDdef, Finset.mem_filter, Finset.mem_range] at hh
          exact hh.1
        have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs.length = 2 := by
          rw [PEqualNP.Outside.L_meta_2233.gateAt_eq C h hhlen]
          exact hC.2.2 _ (List.getElem_mem hhlen)
        calc (((Fs ∪ D).erase m).filter (fun x => φ x = h)).card
            ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs.toFinset.card := by
              apply Finset.card_le_card_of_injOn (fun x => n + x)
              · intro x hx
                rw [Finset.mem_coe, Finset.mem_filter] at hx
                rw [Finset.mem_coe, List.mem_toFinset]
                have := hφin x hx.1
                rw [hx.2] at this
                exact this
              · intro a _ b _ hab
                simp only at hab
                omega
          _ ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs.length := List.toFinset_card_le _
          _ = 2 := hlen2)
    have hcu : (Fs ∪ D).card = Fs.card + D.card := Finset.card_union_of_disjoint hdisj
    have herase : (Fs ∪ D).card ≤ ((Fs ∪ D).erase m).card + 1 := by
      have := Finset.pred_card_le_card_erase (s := Fs ∪ D) (a := m)
      omega
    omega
  · have hFe : Fs = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      exact hn (hF x hx).2.2.1
    rw [hFe]
    simp
