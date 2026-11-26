import HeppMartin.Integer

/-!
# The table computed by `heppMods`

An edge subset `S ⊆ {0, …, N-1}` is stored at index `∑_{i ∈ S} 2^i`. `fill` computes the
entries from the top index down, each from entries at larger indices. We prove that, if the
`omega` table is correct, entry `0` of the filled table is `gN g D ∅ N mod p`.
-/

open Finset

namespace HM

/-- The edge set encoded by `n`. -/
def bits (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

theorem mem_bits {n e : ℕ} : e ∈ bits n ↔ n.testBit e = true := by
  simp [bits]

theorem bits_sum (s : Finset ℕ) : bits (∑ i ∈ s, 2 ^ i) = s := by
  simp [bits]

theorem sum_bits (n : ℕ) : ∑ i ∈ bits n, 2 ^ i = n := by
  simp [bits]

theorem bits_add {n e : ℕ} (h : n.testBit e = false) : bits (n + 2 ^ e) = insert e (bits n) := by
  have he : e ∉ bits n := by simp [mem_bits, h]
  have : n + 2 ^ e = ∑ i ∈ insert e (bits n), 2 ^ i := by
    rw [sum_insert he, sum_bits]; ring
  rw [this, bits_sum]

theorem sum_range_two_pow (N : ℕ) : ∑ i ∈ range N, 2 ^ i = 2 ^ N - 1 := by
  rw [Nat.geomSum_eq le_rfl]; simp

theorem bits_subset_iff {n N : ℕ} : bits n ⊆ range N ↔ n < 2 ^ N := by
  constructor
  · intro h
    have h1 : n ≤ 2 ^ N - 1 := by
      calc n = ∑ i ∈ bits n, 2 ^ i := (sum_bits n).symm
        _ ≤ ∑ i ∈ range N, 2 ^ i := sum_le_sum_of_subset h
        _ = 2 ^ N - 1 := sum_range_two_pow N
    have : 0 < 2 ^ N := by positivity
    omega
  · intro h i hi
    have h2 : 2 ^ i ≤ n := Nat.two_pow_le_of_mem_bitIndices (by simpa [bits] using hi)
    have : 2 ^ i < 2 ^ N := lt_of_le_of_lt h2 h
    simpa using (Nat.pow_lt_pow_iff_right (by norm_num)).1 this

theorem bits_zero : bits 0 = ∅ := by simp [bits]

theorem bits_full (N : ℕ) : bits (2 ^ N - 1) = range N := by
  rw [← sum_range_two_pow, bits_sum]

theorem popc_eq_card_filter (n : ℕ) : ∀ k, popc n k = ((range k).filter fun i => n.testBit i = true).card
  | 0 => rfl
  | k + 1 => by
    rw [popc, popc_eq_card_filter n k, range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · simp_all

theorem popc_eq_card {n N : ℕ} (h : n < 2 ^ N) : popc n N = (bits n).card := by
  rw [popc_eq_card_filter]
  congr 1
  ext i
  have := bits_subset_iff.2 h
  constructor
  · intro hi; exact mem_bits.2 (mem_filter.1 hi).2
  · intro hi; exact mem_filter.2 ⟨this hi, mem_bits.1 hi⟩

theorem dpSum_eq (D : ℕ) (om t : Array ℕ) (n : ℕ) : ∀ k acc,
    dpSum D om t n k acc =
      acc + ∑ e ∈ (range k).filter (fun e => n.testBit e = false), D / om[n + 2 ^ e]! * t[n + 2 ^ e]!
  | 0, acc => by simp [dpSum]
  | k + 1, acc => by
    rw [dpSum, dpSum_eq D om t n k, range_add_one, filter_insert]
    cases h : n.testBit k
    · simp only [Bool.false_eq_true, ite_false, ite_true]
      rw [sum_insert (by simp)]; ring
    · simp

section fill

variable (g : Gr) (D p : ℕ) (om : Array ℕ)

/-- The value the table should hold at index `n`. -/
noncomputable def val (n : ℕ) : ℕ := gN g D (bits n) (g.ne - (bits n).card) % p

/-- Entries at indices `≥ k` are correct. -/
def Inv (k : ℕ) (t : Array ℕ) : Prop :=
  t.size = 2 ^ g.ne ∧ ∀ n, k ≤ n → n < 2 ^ g.ne → t[n]! = val g D p n

variable {g D p om}

theorem stepv_eq (hom : ∀ n < 2 ^ g.ne, om[n]! = (g.omega (bits n)).toNat)
    {t : Array ℕ} {k : ℕ} (hk : k < 2 ^ g.ne) (hinv : Inv g D p (k + 1) t) :
    stepv g.ne D p om t k = val g D p k := by
  unfold stepv val
  rw [popc_eq_card hk]
  have hS := bits_subset_iff.2 hk
  have hc : (bits k).card ≤ g.ne := by simpa using card_le_card hS
  split_ifs with h
  · rcases (by omega : g.ne - (bits k).card = 0 ∨ g.ne - (bits k).card = 1) with h' | h' <;>
      simp [h', gN]
  · obtain ⟨m, hm⟩ : ∃ m, g.ne - (bits k).card = m + 2 := ⟨g.ne - (bits k).card - 2, by omega⟩
    rw [hm, dpSum_eq, zero_add]
    show _ = (∑ e ∈ range g.ne \ bits k,
      D / (g.omega (insert e (bits k))).toNat * gN g D (insert e (bits k)) (m + 1)) % p
    have hfilt : (range g.ne).filter (fun e => k.testBit e = false) = range g.ne \ bits k := by
      ext e; simp [mem_bits]
    rw [hfilt]
    conv_lhs => rw [sum_nat_mod]
    conv_rhs => rw [sum_nat_mod]
    refine congrArg (· % p) (sum_congr rfl fun e he => ?_)
    obtain ⟨heN, hek⟩ := mem_sdiff.1 he
    have hb : k.testBit e = false := by simpa [mem_bits] using hek
    have hadd := bits_add hb
    have hlt : k + 2 ^ e < 2 ^ g.ne := by
      rw [← bits_subset_iff, hadd, insert_subset_iff]; exact ⟨heN, hS⟩
    have hge : k + 1 ≤ k + 2 ^ e := by have := Nat.one_le_two_pow (n := e); omega
    rw [hinv.2 _ hge hlt, hom _ hlt, val, hadd, card_insert_of_notMem hek,
      show g.ne - ((bits k).card + 1) = m + 1 by omega, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem fill_inv (hom : ∀ n < 2 ^ g.ne, om[n]! = (g.omega (bits n)).toNat) :
    ∀ k (t : Array ℕ), k ≤ 2 ^ g.ne → Inv g D p k t → Inv g D p 0 (fill g.ne D p om k t)
  | 0, t, _, h => h
  | k + 1, t, hk, h => by
    rw [fill]
    apply fill_inv hom k _ (by omega)
    refine ⟨by simp [h.1], fun n hn hn2 => ?_⟩
    have hsz : n < t.size := by rw [h.1]; omega
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simpa using hsz),
        Array.getElem_setIfInBounds_self]
      exact stepv_eq hom (by omega) h
    · rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simpa using hsz),
        Array.getElem_setIfInBounds_ne hsz (by omega), ← getElem!_pos t n hsz]
      exact h.2 n hlt hn2

end fill

theorem omTab_get (g : Gr) {n : ℕ} (h : n < 2 ^ g.ne) : (omTab g)[n]! = (omegaFast g n).toNat := by
  unfold omTab
  rw [getElem!_pos _ _ (by simpa using h)]
  simp [Array.getElem_map, Array.getElem_range]

/-- If `omegaFast` computes `omega`, then `heppMods` computes `gN g D ∅ N` modulo each prime. -/
theorem heppMods_eq (g : Gr) (D : ℕ) (ps : List ℕ)
    (hfast : ∀ n < 2 ^ g.ne, omegaFast g n = g.omega (bits n)) :
    heppMods g D ps = ps.map fun p => gN g D ∅ g.ne % p := by
  unfold heppMods
  refine List.map_congr_left fun p _ => ?_
  have hom : ∀ n < 2 ^ g.ne, (omTab g)[n]! = (g.omega (bits n)).toNat := fun n h => by
    rw [omTab_get g h, hfast n h]
  have hinv := fill_inv (D := D) (p := p) hom (2 ^ g.ne) (Array.replicate (2 ^ g.ne) 0) le_rfl
    ⟨by simp, fun n h1 h2 => by omega⟩
  have := hinv.2 0 le_rfl (by positivity)
  rw [this, val, bits_zero, card_empty, Nat.sub_zero]

end HM
