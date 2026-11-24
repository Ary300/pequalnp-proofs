import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def Gen (L : List ℕ) (v : ℕ) : Prop :=
  ∃ a ∈ L, ∃ b ∈ L, v = a &&& b ∨ v = a ||| b

def Seq (base l : List ℕ) : Prop :=
  ∀ i : Fin l.length, Gen (base ++ List.take (↑i) l) (l.get i)

def D : List ℕ → List ℕ → Prop
  | _, [] => True
  | base, y :: ys => Gen base y ∧ D (base ++ [y]) ys

def keep : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | seen, y :: ys => if y ∈ seen then keep seen ys else y :: keep (seen ++ [y]) ys

theorem gen_mono {L L' : List ℕ} {v : ℕ} (h : Gen L v) (hs : ∀ z ∈ L, z ∈ L') : Gen L' v := by
  obtain ⟨a, ha, b, hb, hv⟩ := h
  exact ⟨a, hs a ha, b, hs b hb, hv⟩

theorem seq_cons (base : List ℕ) (y : ℕ) (ys : List ℕ) :
    Seq base (y :: ys) ↔ Gen base y ∧ Seq (base ++ [y]) ys := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h ⟨0, by simp⟩
      simpa using this
    · intro i
      have := h ⟨i.1 + 1, by simp⟩
      simpa [List.take_succ_cons, List.append_assoc] using this
  · rintro ⟨h0, h1⟩ i
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => simpa using h0
    | succ k =>
      have hk : k < ys.length := by simpa using hi
      have := h1 ⟨k, hk⟩
      simpa [List.take_succ_cons, List.append_assoc] using this

theorem seq_iff (l : List ℕ) : ∀ base : List ℕ, Seq base l ↔ D base l := by
  induction l with
  | nil => intro base; simp [Seq, D]
  | cons y ys ih =>
    intro base
    rw [seq_cons, ih]
    rfl

theorem d_mono : ∀ (l base base' : List ℕ), D base l → (∀ z ∈ base, z ∈ base') → D base' l := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons y ys ih =>
    intro base base' h hs
    refine ⟨gen_mono h.1 hs, ih _ _ h.2 ?_⟩
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ (hs z hz)
    · exact List.mem_append_right _ hz

theorem d_snoc : ∀ (s base : List ℕ) (v : ℕ), D base s → Gen (base ++ s) v → D base (s ++ [v]) := by
  intro s
  induction s with
  | nil => intro base v _ hv; exact ⟨by simpa using hv, trivial⟩
  | cons y ys ih =>
    intro base v h hv
    exact ⟨h.1, ih _ v h.2 (by simpa [List.append_assoc] using hv)⟩

theorem keep_length : ∀ (l seen : List ℕ), (keep seen l).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro _; simp [keep]
  | cons y ys ih =>
    intro seen
    unfold keep
    split
    · exact le_trans (ih seen) (Nat.le_succ _)
    · simpa using ih (seen ++ [y])

theorem keep_mem : ∀ (l seen : List ℕ) (z : ℕ), z ∈ keep seen l → z ∉ seen ∧ z ∈ l := by
  intro l
  induction l with
  | nil => intro _ z hz; simp [keep] at hz
  | cons y ys ih =>
    intro seen z hz
    unfold keep at hz
    split at hz
    · obtain ⟨h1, h2⟩ := ih seen z hz
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩
    · rename_i hy
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨hy, List.mem_cons_self⟩
      · obtain ⟨h1, h2⟩ := ih _ z hz
        exact ⟨fun h => h1 (List.mem_append_left _ h), List.mem_cons_of_mem _ h2⟩

theorem keep_nodup : ∀ (l seen : List ℕ), (keep seen l).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp [keep]
  | cons y ys ih =>
    intro seen
    unfold keep
    split
    · exact ih seen
    · refine List.nodup_cons.mpr ⟨?_, ih _⟩
      intro hy
      exact (keep_mem ys (seen ++ [y]) y hy).1 (List.mem_append_right _ (List.mem_singleton_self y))

theorem keep_cover : ∀ (l seen : List ℕ) (z : ℕ), z ∈ l → z ∈ seen ∨ z ∈ keep seen l := by
  intro l
  induction l with
  | nil => intro _ z hz; simp at hz
  | cons y ys ih =>
    intro seen z hz
    unfold keep
    split
    · rename_i hy
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl hy
      · exact ih seen z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr List.mem_cons_self
      · rcases ih (seen ++ [y]) z hz with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton.mp h]; exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem keep_d : ∀ (l base seen : List ℕ), D base l → (∀ z ∈ base, z ∈ seen) → D seen (keep seen l) := by
  intro l
  induction l with
  | nil => intro _ _ _ _; simp [keep, D]
  | cons y ys ih =>
    intro base seen h hs
    unfold keep
    split
    · rename_i hy
      refine ih (base ++ [y]) seen h.2 ?_
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hs z hz
      · rw [List.mem_singleton.mp hz]; exact hy
    · refine ⟨gen_mono h.1 hs, ih (base ++ [y]) (seen ++ [y]) h.2 ?_⟩
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ (hs z hz)
      · exact List.mem_append_right _ hz

theorem core (B : List ℕ) (a v : ℕ) (s : List ℕ) (hv : v ∉ B) (ha : Gen B a)
    (hs : Seq (a :: B) s) (hlast : Gen (a :: B ++ s) v) :
    ∃ t : List ℕ, t.length ≤ s.length + 2 ∧ t.Nodup ∧ (∀ y ∈ t, y ∉ B) ∧ v ∈ t ∧ Seq B t := by
  have hD : D B (a :: (s ++ [v])) := by
    refine ⟨by simpa using ha, ?_⟩
    have h1 : D (a :: B) s := (seq_iff s (a :: B)).mp hs
    have h2 : D (B ++ [a]) s := d_mono s (a :: B) (B ++ [a]) h1 (by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_append_right _ (List.mem_singleton_self z)
      · exact List.mem_append_left _ hz)
    refine d_snoc s (B ++ [a]) v h2 (gen_mono hlast ?_)
    intro z hz
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hz ⊢
    tauto
  refine ⟨keep B (a :: (s ++ [v])), ?_, keep_nodup _ _, ?_, ?_, ?_⟩
  · have := keep_length (a :: (s ++ [v])) B
    simp at this
    omega
  · intro y hy
    exact (keep_mem _ B y hy).1
  · rcases keep_cover (a :: (s ++ [v])) B v (by simp) with h | h
    · exact absurd h hv
    · exact h
  · exact (seq_iff _ B).mpr (keep_d _ B B hD (fun z hz => hz))

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 x3 x4 x5 x6 h5 h4 h6 hlast
  exact PEqualNP.Outside.L_meta_3328.core x3 x4 x5 x6 h5 h4 h6 hlast
