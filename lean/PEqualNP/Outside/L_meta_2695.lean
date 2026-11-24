import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
  PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

theorem wire_gate (C : Circuit) (z : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires z).getD (z.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map
        fun i => ((C.gates.take k).foldl step z).getD i false) ∧
    ∀ i < z.length + k, (C.wires z).getD i false = ((C.gates.take k).foldl step z).getD i false := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk]
    simp
  have hw : C.wires z =
      (C.gates.drop (k + 1)).foldl step (step ((C.gates.take k).foldl step z) C.gates[k]) := by
    show C.gates.foldl step z = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hPlen : ((C.gates.take k).foldl step z).length = z.length + k := by
    rw [fold_len]
    simp [List.length_take]
    omega
  constructor
  · rw [hw, fold_pre _ _ _ (by simp [step, hPlen])]
    simp only [step]
    rw [← hPlen]
    simp
  · intro i hi
    rw [hw, fold_pre _ _ _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ (by omega)]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def Inv (n : ℕ) (C : Circuit) (cs : List (List ℕ)) : Prop :=
  ∀ m < cs.length, ∀ g ∈ cs.getD m [], g = m ∨ ((gateAt C m).op = GateOp.or ∧
    ∃ w ∈ (gateAt C m).inputs, n ≤ w ∧ w < n + m ∧ g ∈ cs.getD (w - n) [])

theorem inv_take (n : ℕ) (C : Circuit) : ∀ k, k ≤ C.gates.length →
    ((C.gates.take k).foldl (orStep n) []).length = k ∧
      Inv n C ((C.gates.take k).foldl (orStep n) [])
  | 0, _ => by simp [Inv]
  | k + 1, hk => by
    obtain ⟨hl, hi⟩ := inv_take n C k (by omega)
    have hk' : k < C.gates.length := by omega
    have ht : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']
      simp
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cs := (C.gates.take k).foldl (orStep n) [] with hcs
    have hga : gateAt C k = C.gates[k] := gateAt_eq C k hk'
    refine ⟨by simp [orStep, hl], ?_⟩
    intro m hm g hg
    simp only [orStep, List.length_append, List.length_singleton] at hm
    rcases Nat.lt_or_ge m cs.length with h | h
    · rw [orStep, List.getD_append _ _ _ _ h] at hg
      rcases hi m h g hg with e | ⟨hor, w, hw, h1, h2, h3⟩
      · exact Or.inl e
      · refine Or.inr ⟨hor, w, hw, h1, h2, ?_⟩
        rw [orStep, List.getD_append _ _ _ _ (by omega)]
        exact h3
    · have hmk : m = cs.length := by omega
      subst hmk
      rw [orStep, List.getD_append_right _ _ _ _ le_rfl] at hg
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons] at hg
      rcases hg with e | hg
      · exact Or.inl e
      · rw [hl] at hg ⊢
        by_cases hor : C.gates[k].op = GateOp.or
        · rw [if_pos hor] at hg
          rw [List.mem_flatMap] at hg
          obtain ⟨w, hw, hgw⟩ := hg
          rw [List.mem_filter] at hw
          obtain ⟨hw1, hw2⟩ := hw
          simp only [decide_eq_true_eq] at hw2
          refine Or.inr ⟨by rw [hga]; exact hor, w, by rw [hga]; exact hw1, hw2.1, by omega, ?_⟩
          rw [orStep, List.getD_append _ _ _ _ (by omega)]
          exact hgw
        · rw [if_neg hor] at hg
          simp at hg

theorem orSets_eq (n : ℕ) (C : Circuit) :
    orSets n C = (C.gates.take C.gates.length).foldl (orStep n) [] := by
  simp [orSets]

theorem inv_full (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length ∧ Inv n C (orSets n C) := by
  rw [orSets_eq]
  exact inv_take n C _ le_rfl

theorem desc (n : ℕ) (C : Circuit) (j : ℕ) : ∀ m, j ∈ (orSets n C).getD m [] →
    j = m ∨ ∃ k, k < C.gates.length ∧ j < k ∧ (gateAt C k).op = GateOp.or ∧
      n + j ∈ (gateAt C k).inputs := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hj
    obtain ⟨hlen, hinv⟩ := inv_full n C
    have hm : m < (orSets n C).length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hj
      simp at hj
    rcases hinv m hm j hj with e | ⟨hor, w, hw, h1, h2, h3⟩
    · exact Or.inl e
    · right
      rcases ih (w - n) (by omega) h3 with e | hk
      · refine ⟨m, by omega, by omega, hor, ?_⟩
        have : n + j = w := by omega
        rw [this]
        exact hw
      · exact hk

theorem orIn_and (n : ℕ) (C : Circuit) (j : ℕ) (hand : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext i
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (h | ⟨k, hk, hr, hor, _⟩)
  · have := i.isLt
    omega
  · obtain ⟨_, hmem⟩ := hr
    obtain ⟨hlen, hinv⟩ := inv_full n C
    have hj : j < (orSets n C).length := by
      by_contra hc
      simp only [Nat.add_sub_cancel_left] at hmem
      rw [List.getD_eq_default _ _ (by omega)] at hmem
      simp at hmem
    simp only [Nat.add_sub_cancel_left] at hmem
    rcases hinv j hj k hmem with e | ⟨hor2, _⟩
    · subst e
      rw [hand] at hor
      cases hor
    · rw [hand] at hor2
      cases hor2

end PEqualNP.Outside.L_meta_2695

theorem PEqualNP.Outside.L_meta_2695 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x5 ∈ x4.gates, x5.inputs.length = (2 : ℕ)) → ∀ x6 ∈ PEqualNP.TopForm.tops x2 x4, ∀ (x8 : Fin (2 : ℕ)), ∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x6 x8) x9 → x6 ∈ PEqualNP.TopForm.centreless x2 x4 ∨ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).Nonempty := by
  intro n G _ C hfan a ha b j hj hreach
  simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hj
  obtain ⟨hjlen, hjand, -, x, hxj, hxF⟩ := hj
  obtain ⟨hn, hmem⟩ := hreach
  rcases PEqualNP.Outside.L_meta_2695.desc n C j _ hmem with e | ⟨k, hk, hjk, hor, hin⟩
  · left
    have hop : PEqualNP.TopForm.opnd C a b = n + j := by omega
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter]
    refine ⟨ha, ?_⟩
    have hs : PEqualNP.TopForm.side (n := n) C a b = ∅ := by
      simp only [PEqualNP.TopForm.side]
      rw [hop]
      exact PEqualNP.Outside.L_meta_2695.orIn_and n C j hjand
    fin_cases b
    · exact Or.inl hs
    · exact Or.inr hs
  · right
    refine ⟨k, ?_⟩
    rw [Finset.mem_sdiff]
    have hga := PEqualNP.Outside.L_meta_2695.gateAt_eq C k hk
    have hval : PEqualNP.EdgeOwnership.gateVal n C k x = true := by
      unfold PEqualNP.EdgeOwnership.gateVal
      have hz : (List.ofFn x).length = n := List.length_ofFn
      obtain ⟨h1, h2⟩ := PEqualNP.Outside.L_meta_2695.wire_gate C (List.ofFn x) k hk
      rw [hz] at h1 h2
      rw [h1]
      rw [hga] at hor hin
      rw [hor]
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map, id]
      refine ⟨_, ⟨n + j, hin, rfl⟩, ?_⟩
      rw [← h2 (n + j) (by omega)]
      exact hxj
    constructor
    · simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨hk, hor, ?_⟩
      intro hB
      have := hB x hval
      rw [hxF] at this
      simp at this
    · intro hl
      simp only [PEqualNP.TopForm.lam, Finset.mem_filter] at hl
      obtain ⟨_, h0, h1, _⟩ := hl
      have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length = 2 := by
        rw [hga]
        exact hfan _ (List.getElem_mem hk)
      obtain ⟨u0, u1, huv⟩ : ∃ u0 u1,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [u0, u1] := by
        rcases hh : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs with
          _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, t⟩⟩⟩ <;> simp [hh] at hlen2
        exact ⟨u0, u1, rfl⟩
      rw [huv] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      have e0 : PEqualNP.TopForm.opnd C k 0 = u0 := by simp [PEqualNP.TopForm.opnd, huv]
      have e1 : PEqualNP.TopForm.opnd C k 1 = u1 := by simp [PEqualNP.TopForm.opnd, huv]
      rcases hin with h | h
      · rw [e0, ← h, PEqualNP.Outside.L_meta_2695.orIn_and n C j hjand] at h0
        simp at h0
      · rw [e1, ← h, PEqualNP.Outside.L_meta_2695.orIn_and n C j hjand] at h1
        simp at h1
