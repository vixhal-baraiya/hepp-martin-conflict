import HeppMartin.Structure
import HeppMartin.Checks.CertA
import HeppMartin.Checks.CertB
import HeppMartin.Checks.Small
import HeppMartin.Checks.Hepp0
import HeppMartin.Checks.Hepp1
import HeppMartin.Checks.Hepp2
import HeppMartin.Checks.Hepp3
import HeppMartin.Checks.Hepp4
import HeppMartin.Checks.Hepp5
import HeppMartin.Checks.Hepp6
import HeppMartin.Checks.Hepp7
import HeppMartin.Checks.Hepp8
import HeppMartin.Checks.Hepp9
import HeppMartin.Checks.Hepp10

/-!
# Main theorem

`Ga` and `Gb` are completed primitive 13-loop φ⁴ graphs. Their decompletions at vertex 0 have
exactly equal Hepp bounds, while `M(Ga) = 71544 ≠ 71604 = M(Gb)`. Hence no period function
satisfies both Panzer's Conjecture 1.2 and Panzer–Yeats Conjecture 1.10.
-/

open Finset

namespace HM

theorem ga_phi4 : IsPhi4 (decomplete Ga 0) := by
  have h := dec_a; simp only [Bool.and_eq_true] at h
  exact isPhi4_of _ D h.1 h.2 cert_a phi_a

theorem gb_phi4 : IsPhi4 (decomplete Gb 0) := by
  have h := dec_b; simp only [Bool.and_eq_true] at h
  exact isPhi4_of _ D h.1 h.2 cert_b phi_b

theorem Ga_completed : Completed Ga := by
  have h := structure_a; simp only [Bool.and_eq_true] at h
  exact completed_of Ga h.1.1.1 h.1.1.2 h.1.2 h.2

theorem Gb_completed : Completed Gb := by
  have h := structure_b; simp only [Bool.and_eq_true] at h
  exact completed_of Gb h.1.1.1 h.1.1.2 h.1.2 h.2

theorem primes_split : primes = (List.range 11).flatMap chunk := by decide

theorem primes_coprime : primes.Pairwise Nat.Coprime := by decide

theorem primes_bound : (26 * D) ^ 25 < primes.prod := by decide

/-- The residues agree modulo every prime. -/
theorem residues_agree :
    ∀ p ∈ primes, gN (decomplete Ga 0) D ∅ 26 % p = gN (decomplete Gb 0) D ∅ 26 % p := by
  have ha := omegaFast_eq_of_certAll _ cert_a
  have hb := omegaFast_eq_of_certAll _ cert_b
  have hchunks : ∀ k < 11, ∀ p ∈ chunk k,
      gN (decomplete Ga 0) D ∅ 26 % p = gN (decomplete Gb 0) D ∅ 26 % p := by
    intro k hk
    have hk' : heppMods (decomplete Ga 0) D (chunk k) = heppMods (decomplete Gb 0) D (chunk k) := by
      interval_cases k
      exacts [hepp_chunk_0, hepp_chunk_1, hepp_chunk_2, hepp_chunk_3, hepp_chunk_4, hepp_chunk_5,
        hepp_chunk_6, hepp_chunk_7, hepp_chunk_8, hepp_chunk_9, hepp_chunk_10]
    rw [heppMods_eq _ D _ ha, heppMods_eq _ D _ hb, ne_a, ne_b] at hk'
    exact List.map_inj_left.1 hk'
  intro p hp
  rw [primes_split, List.mem_flatMap] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  exact hchunks k (List.mem_range.1 hk) p hpk

/-- **The Hepp bounds are exactly equal.** -/
theorem hepp_equal : hepp (decomplete Ga 0) = hepp (decomplete Gb 0) := by
  have hDa := (phi4_and_divides _ D cert_a phi_a).2
  have hDb := (phi4_and_divides _ D cert_b phi_b).2
  have hD : 0 < D := by decide
  have hmod : gN (decomplete Ga 0) D ∅ 26 ≡ gN (decomplete Gb 0) D ∅ 26 [MOD primes.prod] := by
    rw [Nat.modEq_list_prod_iff primes_coprime]
    intro i
    exact residues_agree _ (List.get_mem _ _)
  have hla := gN_le (decomplete Ga 0) D 25 ∅
  have hlb := gN_le (decomplete Gb 0) D 25 ∅
  rw [ne_a] at hla; rw [ne_b] at hlb
  have heq := hmod.eq_of_lt_of_lt (lt_of_le_of_lt hla primes_bound) (lt_of_le_of_lt hlb primes_bound)
  rw [hepp_eq_gN _ D (by rw [ne_a]; norm_num) hD hDa, hepp_eq_gN _ D (by rw [ne_b]; norm_num) hD hDb,
    ne_a, ne_b, heq]

theorem martin_ne : martin (multiply Ga 1) ≠ martin (multiply Gb 1) := by
  rw [martin_a, martin_b]
  decide

/-- **Main theorem.** No function `P` from graphs to real numbers satisfies both Panzer's
Conjecture 1.2 and Panzer–Yeats Conjecture 1.10. -/
theorem not_both (P : Gr → ℝ) : ¬ (HeppConj P ∧ MartinConj P) := by
  rintro ⟨hH, hM⟩
  have hP : P (decomplete Ga 0) = P (decomplete Gb 0) :=
    (hH _ _ ga_phi4 gb_phi4).2 hepp_equal
  have := (hM Ga Gb Ga_completed Gb_completed 0 (by decide) 0 (by decide)).1 hP 1 le_rfl
  exact martin_ne this

end HM
