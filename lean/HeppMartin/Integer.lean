import HeppMartin.Recursion

/-!
# Clearing denominators

If every `omega(T)` is `0` or divides `D`, then `gN g D S m = D^(m-1) · hq g S m` is a natural
number given by the same recursion with `1/omega` replaced by `D / omega`. It is at most
`(N·D)^(m-1)`.
-/

open Finset

namespace HM

variable (g : Gr) (D : ℕ)

noncomputable def gN (S : Finset ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | m + 2 => ∑ e ∈ range g.ne \ S, D / (g.omega (insert e S)).toNat * gN (insert e S) (m + 1)

/-- The divisibility hypothesis on the edge subsets of `g`. -/
def OmegaDivides : Prop :=
  ∀ T ⊆ range g.ne, 0 ≤ g.omega T ∧ (g.omega T = 0 ∨ (g.omega T).toNat ∣ D)

theorem hq_eq_gN (hD : 0 < D) (hω : OmegaDivides g D) (m : ℕ) :
    ∀ S ⊆ range g.ne, hq g S (m + 1) = (gN g D S (m + 1) : ℚ) / (D : ℚ) ^ m := by
  induction m with
  | zero => intro S _; simp [hq, gN]
  | succ m ih =>
    intro S hS
    rw [show hq g S (m + 1 + 1) = ∑ e ∈ range g.ne \ S,
        ((g.omega (insert e S) : ℚ))⁻¹ * hq g (insert e S) (m + 1) from rfl,
      show gN g D S (m + 1 + 1) = ∑ e ∈ range g.ne \ S,
        D / (g.omega (insert e S)).toNat * gN g D (insert e S) (m + 1) from rfl]
    push_cast
    rw [Finset.sum_div]
    refine sum_congr rfl fun e he => ?_
    have hT : insert e S ⊆ range g.ne := by
      rw [Finset.insert_subset_iff]; exact ⟨(Finset.mem_sdiff.1 he).1, hS⟩
    rw [ih _ hT]
    obtain ⟨h0, h1⟩ := hω _ hT
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    rcases h1 with h1 | h1
    · simp [h1]
    · have hpos : 0 < g.omega (insert e S) := lt_of_le_of_ne h0 (Ne.symm (by
        intro h; rw [h] at h1; simp at h1; omega))
      have hn : ((g.omega (insert e S)).toNat : ℚ) = (g.omega (insert e S) : ℚ) := by
        have := Int.toNat_of_nonneg h0
        exact_mod_cast this
      have hne : ((g.omega (insert e S)).toNat : ℚ) ≠ 0 := by
        rw [hn]; exact_mod_cast hpos.ne'
      rw [Nat.cast_div h1 hne, hn, pow_succ]
      field_simp

theorem gN_le (m : ℕ) : ∀ S, gN g D S (m + 1) ≤ (g.ne * D) ^ m := by
  induction m with
  | zero => intro S; simp [gN]
  | succ m ih =>
    intro S
    show ∑ e ∈ range g.ne \ S, D / (g.omega (insert e S)).toNat * gN g D (insert e S) (m + 1)
      ≤ (g.ne * D) ^ (m + 1)
    calc ∑ e ∈ range g.ne \ S, D / (g.omega (insert e S)).toNat * gN g D (insert e S) (m + 1)
        ≤ ∑ _e ∈ range g.ne \ S, D * (g.ne * D) ^ m :=
          sum_le_sum fun e _ => Nat.mul_le_mul (Nat.div_le_self _ _) (ih _)
      _ = (range g.ne \ S).card * (D * (g.ne * D) ^ m) := by rw [sum_const, smul_eq_mul]
      _ ≤ g.ne * (D * (g.ne * D) ^ m) := by
          apply Nat.mul_le_mul_right
          exact (card_le_card sdiff_subset).trans (by simp)
      _ = (g.ne * D) ^ (m + 1) := by ring

/-- The Hepp bound with denominators cleared. -/
theorem hepp_eq_gN (hN : 0 < g.ne) (hD : 0 < D) (hω : OmegaDivides g D) :
    hepp g = (gN g D ∅ g.ne : ℚ) / (D : ℚ) ^ (g.ne - 1) := by
  rw [hepp_eq_hq g hN]
  obtain ⟨m, hm⟩ : ∃ m, g.ne = m + 1 := ⟨g.ne - 1, by omega⟩
  have := hq_eq_gN g D hD hω m ∅ (empty_subset _)
  rw [hm]
  simpa using this

end HM
