import HeppMartin.Spec

/-!
# From the sum over orderings to a recursion over edge subsets

`hq g S m` sums, over all orderings of the `m` edges outside `S`, the product of `1/omega` of
`S` together with each proper initial segment. Splitting the orderings by their first edge gives
`hq g S (m+2) = ∑_{e ∉ S} omega(S ∪ {e})⁻¹ · hq g (S ∪ {e}) (m+1)`, and `hepp g = hq g ∅ N`.
-/

open Finset

namespace HM

variable (g : Gr)

/-- The subset recursion. The last argument is the number of edges outside `S`. -/
noncomputable def hq (S : Finset ℕ) : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | m + 2 => ∑ e ∈ range g.ne \ S, ((g.omega (insert e S) : ℚ))⁻¹ * hq (insert e S) (m + 1)

/-- Sum over all orderings `l` of the list `r` of the products of `1/omega(S ∪ initial segment)`. -/
noncomputable def ordSum (S : Finset ℕ) (r : List ℕ) : ℚ :=
  (r.permutations.map fun l =>
    ∏ k ∈ range (l.length - 1), ((g.omega (S ∪ (l.take (k + 1)).toFinset) : ℚ))⁻¹).sum

theorem sum_flatMap' {α β : Type*} [AddCommMonoid β] (r : List α) (F : α → List β) :
    (r.flatMap F).sum = (r.map fun e => (F e).sum).sum := by
  induction r with
  | nil => simp
  | cons a r ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Splitting the permutations of a duplicate-free nonempty list by their first entry. -/
theorem sum_permutations_cons {β : Type*} [AddCommMonoid β] (f : List ℕ → β) {r : List ℕ}
    (hr : r.Nodup) (hne : r ≠ []) :
    (r.permutations.map f).sum =
      (r.map fun e => ((r.erase e).permutations.map fun t => f (e :: t)).sum).sum := by
  have hperm : r.permutations.Perm (r.flatMap fun e => (r.erase e).permutations.map (e :: ·)) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_permutations _ hr)]
    · intro l
      simp only [List.mem_permutations, List.mem_flatMap, List.mem_map]
      constructor
      · intro hl
        cases l with
        | nil => exact absurd (List.Perm.nil_eq hl).symm hne
        | cons e t =>
          have he : e ∈ r := hl.subset (List.mem_cons_self ..)
          refine ⟨e, he, t, ?_, rfl⟩
          exact (hl.trans (List.perm_cons_erase he)).cons_inv
      · rintro ⟨e, he, t, ht, rfl⟩
        exact (ht.cons e).trans (List.perm_cons_erase he).symm
    · rw [List.nodup_flatMap]
      refine ⟨fun e _ => (List.nodup_permutations _ (hr.erase e)).map (fun _ _ h => by
        simpa using h), ?_⟩
      refine hr.imp fun {a b} hab => ?_
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro l ⟨t, -, rfl⟩ ⟨t', -, h⟩
      exact hab (List.cons.inj h).1.symm
  rw [(hperm.map f).sum_eq, List.map_flatMap, sum_flatMap']
  simp [Function.comp_def, List.map_map]

theorem ordSum_eq_hq (m : ℕ) :
    ∀ (S : Finset ℕ) (r : List ℕ), r.Nodup → r.length = m + 1 →
      (∀ x, x ∈ r ↔ x ∈ range g.ne \ S) → ordSum g S r = hq g S (m + 1) := by
  induction m with
  | zero =>
    intro S r _ hlen _
    match r, hlen with
    | [a], _ => simp [ordSum, hq, List.permutations]
  | succ m ih =>
    intro S r hr hlen hmem
    have hne : r ≠ [] := by rintro rfl; simp at hlen
    unfold ordSum
    rw [sum_permutations_cons _ hr hne]
    have step : ∀ e ∈ r,
        (((r.erase e).permutations.map fun t =>
          ∏ k ∈ range ((e :: t).length - 1),
            ((g.omega (S ∪ ((e :: t).take (k + 1)).toFinset) : ℚ))⁻¹).sum) =
        ((g.omega (insert e S) : ℚ))⁻¹ * hq g (insert e S) (m + 1) := by
      intro e he
      have hlen' : (r.erase e).length = m + 1 := by
        rw [List.length_erase_of_mem he]; omega
      rw [← ih (insert e S) (r.erase e) (hr.erase e) hlen' ?_]
      · unfold ordSum
        rw [← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
        have htl : t.length = m + 1 := by
          rw [(List.mem_permutations.1 ht).length_eq, hlen']
        simp only [List.length_cons, Nat.add_sub_cancel, htl]
        rw [prod_range_succ', mul_comm]
        congr 1
        · congr 3
          ext x; simp
        · refine prod_congr rfl fun k _ => ?_
          congr 3
          ext x; simp only [List.take_succ_cons, List.toFinset_cons, Finset.mem_union,
            Finset.mem_insert, List.mem_toFinset]; tauto
      · intro x
        rw [hr.mem_erase_iff, hmem]
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_range]
        constructor
        · rintro ⟨hxe, hx, hxS⟩; exact ⟨hx, by tauto⟩
        · rintro ⟨hx, hxe⟩; push Not at hxe; exact ⟨hxe.1, hx, hxe.2⟩
    rw [List.map_congr_left step]
    have htf : r.toFinset = range g.ne \ S := by ext x; simp [hmem x]
    rw [show hq g S (m + 1 + 1) = ∑ e ∈ range g.ne \ S,
        ((g.omega (insert e S) : ℚ))⁻¹ * hq g (insert e S) (m + 1) from rfl, ← htf,
      List.sum_toFinset _ hr]

/-- The Hepp bound satisfies the subset recursion. -/
theorem hepp_eq_hq (hN : 0 < g.ne) : hepp g = hq g ∅ g.ne := by
  obtain ⟨m, hm⟩ : ∃ m, g.ne = m + 1 := ⟨g.ne - 1, by omega⟩
  have := ordSum_eq_hq g m ∅ (List.range g.ne) (List.nodup_range) (by simp [hm])
    (fun x => by simp)
  rw [hm, ← this]
  unfold hepp ordSum
  rw [hm]
  refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
  simp only [heppTerm, Finset.empty_union]

end HM
