import HeppMartin.Cert
import HeppMartin.Conjectures

/-!
# From the Boolean checks to the hypotheses of the conjectures
-/

open Finset

namespace HM

theorem edgesValid_of (g : Gr) (h : wellFormed g = true) : EdgesValid g := by
  unfold wellFormed at h
  rw [Array.all_eq_true] at h
  intro i hi
  have := h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem phiOK_spec (g : Gr) (D : ℕ) (h : phiOK g D = true) {n : ℕ} (hn : n < 2 ^ g.ne) :
    (n = 0 ∨ n = 2 ^ g.ne - 1 → omegaFast g n = 0) ∧
      (n ≠ 0 → n ≠ 2 ^ g.ne - 1 → 1 ≤ omegaFast g n ∧ (D : ℤ) % omegaFast g n = 0) := by
  have := (allBelow_iff _ _).1 h n hn
  simp only at this
  by_cases h0 : n = 0 ∨ n = 2 ^ g.ne - 1
  · have hb : (n == 0 || n == 2 ^ g.ne - 1) = true := by
      rcases h0 with h0 | h0 <;> simp [h0]
    simp only [hb, ↓reduceIte] at this
    exact ⟨fun _ => by simpa using this, fun a b => absurd h0 (by tauto)⟩
  · have hb : ¬ (n == 0 || n == 2 ^ g.ne - 1) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq]; exact h0
    simp only [hb, ↓reduceIte, Bool.false_eq_true] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨fun h' => absurd h' h0, fun _ _ => this⟩

/-- The `omega` facts for every edge subset, from the two checks. -/
theorem phi4_and_divides (g : Gr) (D : ℕ) (hc : certAll g = true) (hp : phiOK g D = true) :
    (g.omega (range g.ne) = 0 ∧ ∀ S ⊆ range g.ne, S.Nonempty → S ≠ range g.ne → 0 < g.omega S) ∧
      OmegaDivides g D := by
  have hf := omegaFast_eq_of_certAll g hc
  have key : ∀ S ⊆ range g.ne, ∃ n < 2 ^ g.ne, bits n = S ∧ (n = 0 ↔ S = ∅) ∧
      (n = 2 ^ g.ne - 1 ↔ S = range g.ne) := by
    intro S hS
    refine ⟨∑ i ∈ S, 2 ^ i, bits_subset_iff.1 (by rw [bits_sum]; exact hS), bits_sum S, ?_, ?_⟩
    · constructor
      · intro h; rw [← bits_sum S, h, bits_zero]
      · rintro rfl; simp
    · constructor
      · intro h; rw [← bits_sum S, h, bits_full]
      · rintro rfl; rw [sum_range_two_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hn : 2 ^ g.ne - 1 < 2 ^ g.ne := Nat.sub_lt (by positivity) one_pos
    rw [← bits_full, ← hf _ hn]
    exact (phiOK_spec g D hp hn).1 (Or.inr rfl)
  · intro S hS hne hfull
    obtain ⟨n, hn, rfl, h0, h1⟩ := key S hS
    rw [← hf n hn]
    have := (phiOK_spec g D hp hn).2 (fun h => hne.ne_empty (h0.1 h)) (fun h => hfull (h1.1 h))
    omega
  · intro S hS
    obtain ⟨n, hn, rfl, -, -⟩ := key S hS
    rw [← hf n hn]
    by_cases h : n = 0 ∨ n = 2 ^ g.ne - 1
    · have := (phiOK_spec g D hp hn).1 h
      exact ⟨by omega, Or.inl this⟩
    · push Not at h
      obtain ⟨h1, h2⟩ := (phiOK_spec g D hp hn).2 h.1 h.2
      refine ⟨by omega, Or.inr ?_⟩
      have hd : omegaFast g n ∣ (D : ℤ) := Int.dvd_of_emod_eq_zero h2
      rw [← Int.toNat_of_nonneg (by omega : 0 ≤ omegaFast g n)] at hd
      exact Int.natCast_dvd_natCast.1 hd

theorem isPhi4_of (g : Gr) (D : ℕ) (hw : wellFormed g = true) (hd : maxDegLe g 4 = true)
    (hc : certAll g = true) (hp : phiOK g D = true) : IsPhi4 g := by
  refine ⟨edgesValid_of g hw, fun v hv => ?_, (phi4_and_divides g D hc hp).1⟩
  have := (allBelow_iff _ _).1 hd v hv
  simpa using this

/-! ## Cuts -/

theorem foldl_count {α : Type*} (p : α → Bool) (l : List α) : ∀ acc,
    l.foldl (fun c e => if p e then c + 1 else c) acc = acc + l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons, List.countP_cons]
    by_cases h : p a <;> simp [h, ih]; omega

theorem cutSize_eq (G : Gr) (Y : Finset ℕ) : cutSize G (∑ i ∈ Y, 2 ^ i) = cut G Y := by
  have h1 : ∀ x, (∑ i ∈ Y, 2 ^ i).testBit x = decide (x ∈ Y) := fun x => by
    have := @mem_bits (∑ i ∈ Y, 2 ^ i) x
    rw [bits_sum] at this
    by_cases hx : x ∈ Y <;> simp_all
  unfold cutSize cut
  rw [← Array.foldl_toList]
  simp only [h1]
  exact (foldl_count (fun e : ℕ × ℕ => decide (e.1 ∈ Y) != decide (e.2 ∈ Y)) _ 0).trans (zero_add _)

theorem two_le_of_not_acyclic {V : Type*} (H : SimpleGraph V) (s : Finset V) [DecidableEq V]
    (h : ¬ (H.induce (s : Set V)).IsAcyclic) : 2 ≤ s.card := by
  by_contra hlt
  apply h
  have hs : Subsingleton (s : Set V) := by
    have := Finset.card_le_one_iff_subsingleton_coe.1 (by omega : s.card ≤ 1)
    simpa using this
  intro v c hc
  cases c with
  | nil => exact SimpleGraph.Walk.not_isCycle_nil hc
  | cons ha _ => exact ha.ne (Subsingleton.elim _ _)

theorem completed_of (G : Gr) (hw : wellFormed G = true) (hp : noParallel G = true)
    (hr : regular G 4 = true) (hc : cutsOK G = true) : Completed G := by
  refine ⟨edgesValid_of G hw, hp, fun v hv => ?_, ?_⟩
  · have := (allBelow_iff _ _).1 hr v hv; simpa using this
  · intro X hX hXc
    have h1 := two_le_of_not_acyclic _ X hX
    have h2 := two_le_of_not_acyclic _ Xᶜ hXc
    rw [card_compl, Fintype.card_fin] at h2
    set Y := X.map Fin.valEmbedding
    have hY : Y ⊆ range G.nv := fun i hi => by
      obtain ⟨v, -, rfl⟩ := mem_map.1 hi; simp
    have hlt : ∑ i ∈ Y, 2 ^ i < 2 ^ G.nv := bits_subset_iff.1 (by rw [bits_sum]; exact hY)
    have hpc : popc (∑ i ∈ Y, 2 ^ i) G.nv = X.card := by
      rw [popc_eq_card hlt, bits_sum, card_map]
    have := (allBelow_iff _ _).1 hc _ hlt
    simp only [hpc] at this
    have hcond : (decide (2 ≤ X.card) && decide (X.card + 2 ≤ G.nv)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [hcond, ↓reduceIte] at this
    rw [← cutSize_eq]
    simpa using this

end HM
