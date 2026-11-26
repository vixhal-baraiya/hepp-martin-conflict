import HeppMartin.Table

/-!
# Component certificates

For each edge subset, `certValid` checks a labelling of the vertices together with a search
tree: every edge joins equal labels, every label is a fixed point, and every other vertex has a
parent with the same label, adjacent to it, at smaller depth. Such a labelling has exactly one
fixed point per connected component, so `omegaFast` equals `Gr.omega`.
-/

open Finset

namespace HM

theorem allBelow_iff (f : ℕ → Bool) : ∀ n, allBelow f n = true ↔ ∀ i < n, f i = true
  | 0 => by simp [allBelow]
  | n + 1 => by
    unfold allBelow
    cases h : f n
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun H => absurd H (by simp), fun H => absurd (H n (by omega)) (by simp [h])⟩
    · simp only [ite_true, allBelow_iff f n]
      constructor
      · intro H i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact H i hi
        · exact h
      · intro H i hi; exact H i (by omega)

/-- A labelling with a search-tree certificate counts the connected components. -/
theorem card_connectedComponent_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (root par : V → V) (dep : V → ℕ)
    (h1 : ∀ x y, G.Adj x y → root x = root y) (h2 : ∀ v, root (root v) = root v)
    (h3 : ∀ v, root v ≠ v → G.Adj v (par v) ∧ root (par v) = root v ∧ dep (par v) < dep v) :
    Nat.card G.ConnectedComponent = (univ.filter fun v => root v = v).card := by
  have hreach : ∀ d, ∀ v, dep v = d → G.Reachable v (root v) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro v hd
      by_cases hv : root v = v
      · rw [hv]
      · obtain ⟨ha, hr, hdp⟩ := h3 v hv
        have := ih (dep (par v)) (hd ▸ hdp) (par v) rfl
        rw [hr] at this
        exact ha.reachable.trans this
  have hconst : ∀ x y (p : G.Walk x y), root x = root y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons ha _ ih => exact (h1 _ _ ha).trans ih
  let e : G.ConnectedComponent ≃ {v // root v = v} :=
    { toFun := fun c => c.lift (fun v => ⟨root v, h2 v⟩) (fun v w p _ => Subtype.ext (hconst v w p))
      invFun := fun r => G.connectedComponentMk r.1
      left_inv := fun c => by
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h v =>
          simp only [SimpleGraph.ConnectedComponent.lift_mk]
          exact SimpleGraph.ConnectedComponent.eq.2 (hreach _ v rfl).symm
      right_inv := fun r => Subtype.ext (by simp [r.2]) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem rootCount_eq (g : Gr) (L : ℕ) : ∀ k,
    rootCount g L k = ∑ v ∈ range k, if labGet L v = v then 1 else 0
  | 0 => rfl
  | k + 1 => by
    rw [rootCount, rootCount_eq g L k, sum_range_succ]
    simp [beq_iff_eq]

/-- `certValid` makes `omegaFast` equal to `omega` of the encoded edge set. -/
theorem omegaFast_eq (g : Gr) {n : ℕ} (hn : n < 2 ^ g.ne) (hc : certValid g n = true) :
    omegaFast g n = g.omega (bits n) := by
  unfold certValid at hc
  simp only [Bool.and_eq_true] at hc
  generalize bfsCert g n (labOf g n) = c at hc
  obtain ⟨par, dep, pe⟩ := c
  set L := labOf g n
  obtain ⟨hE, hT⟩ := hc
  unfold edgesRespect at hE
  unfold treeOK at hT
  rw [allBelow_iff] at hE hT
  -- facts about labels
  have hlab : ∀ v : Fin g.nv, labGet L v < g.nv := fun v => by
    have := hT v v.2; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.1
  have hfix : ∀ v : Fin g.nv, labGet L (labGet L v) = labGet L v := fun v => by
    have := hT v v.2; simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this.1.2
  let root : Fin g.nv → Fin g.nv := fun v => ⟨labGet L v, hlab v⟩
  let parF : Fin g.nv → Fin g.nv := fun v =>
    if h : par[v.val]! < g.nv then ⟨par[v.val]!, h⟩ else v
  have hcard := card_connectedComponent_eq (g.sub (bits n)) root parF (fun v => dep[v.val]!)
    ?h1 ?h2 ?h3
  case h1 =>
    intro x y hxy
    rw [Gr.sub, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨-, hr⟩ := hxy
    apply Fin.ext
    simp only [root]
    rcases hr with ⟨i, hi, hsz, he⟩ | ⟨i, hi, hsz, he⟩
    · have := hE i hsz
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
      rcases this with h | h
      · simp [mem_bits, h] at hi
      · rw [getElem!_pos g.edges i hsz, he] at h; exact h
    · have := hE i hsz
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
      rcases this with h | h
      · simp [mem_bits, h] at hi
      · rw [getElem!_pos g.edges i hsz, he] at h; exact h.symm
  case h2 => intro v; exact Fin.ext (hfix v)
  case h3 =>
    intro v hv
    have hv' : labGet L v ≠ v := fun h => hv (Fin.ext h)
    have := hT v v.2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨-, h | ⟨⟨⟨⟨⟨hp, hi⟩, hb⟩, hedge⟩, hl⟩, hd⟩⟩ := this
    · exact absurd h hv'
    have hpv : parF v = ⟨par[v.val]!, hp⟩ := by simp [parF, hp]
    refine ⟨?_, ?_, ?_⟩
    · rw [hpv, Gr.sub, SimpleGraph.fromRel_adj]
      refine ⟨fun h => ?_, ?_⟩
      · have : par[v.val]! = v.val := congrArg Fin.val h.symm
        rw [this] at hd; exact lt_irrefl _ hd
      · rw [getElem!_pos g.edges _ hi] at hedge
        rcases hedge with he | he
        · exact Or.inl ⟨_, mem_bits.2 hb, hi, he⟩
        · exact Or.inr ⟨_, mem_bits.2 hb, hi, he⟩
    · rw [hpv]; exact Fin.ext hl
    · simp only [hpv]; exact hd
  -- assemble
  have hroots : (univ.filter fun v : Fin g.nv => root v = v).card = rootCount g L g.nv := by
    rw [rootCount_eq, card_filter, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun v _ => ?_
    simp [root, Fin.ext_iff]
  have hle : rootCount g L g.nv ≤ g.nv := by
    rw [← hroots]; exact (card_filter_le _ _).trans (by simp)
  unfold omegaFast Gr.omega Gr.rank
  rw [hcard, hroots, popc_eq_card hn, Nat.cast_sub hle]

/-- All certificates valid: `omegaFast` computes `omega` on every edge subset. -/
theorem omegaFast_eq_of_certAll (g : Gr) (h : certAll g = true) :
    ∀ n < 2 ^ g.ne, omegaFast g n = g.omega (bits n) := fun n hn =>
  omegaFast_eq g hn ((allBelow_iff _ _).1 h n hn)

end HM
