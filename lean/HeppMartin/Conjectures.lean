import HeppMartin.Spec

/-!
# The two conjectures

The period `P` is an arbitrary real-valued function of graphs, so the final theorem holds for the
actual Feynman period and for any other function.

* **Panzer, Conjecture 1.2** (arXiv:1908.09820): two φ⁴ graphs have equal periods if and only if
  they have equal Hepp bounds. A φ⁴ graph is primitive and logarithmically divergent in four
  dimensions (`omega(E) = 0` and `omega(S) > 0` for every nonempty proper edge subset `S`) with
  all vertex degrees at most 4.
* **Panzer–Yeats, Conjecture 1.10** (arXiv:2304.05299): for cyclically 6-connected 4-regular
  graphs `G₁, G₂` and any vertices `v₁, v₂`, the periods of `G₁ - v₁` and `G₂ - v₂` are equal if and
  only if the Martin sequences agree: `M(G₁^[r]) = M(G₂^[r])` for all `r ≥ 1`.

`Completed` below asks for a simple graph; restricting the conjecture to fewer graphs only weakens
the hypothesis `MartinConj`, so the final theorem covers the conjecture as stated.
-/

open Finset

namespace HM

/-- Every edge joins two distinct vertices of the graph. -/
def EdgesValid (g : Gr) : Prop :=
  ∀ i (h : i < g.edges.size), g.edges[i].1 < g.nv ∧ g.edges[i].2 < g.nv ∧ g.edges[i].1 ≠ g.edges[i].2

/-- φ⁴ graphs in the sense of Panzer: primitive, logarithmically divergent, degrees at most 4. -/
def IsPhi4 (g : Gr) : Prop :=
  EdgesValid g ∧ (∀ v < g.nv, deg g v ≤ 4) ∧ g.omega (range g.ne) = 0 ∧
    ∀ S ⊆ range g.ne, S.Nonempty → S ≠ range g.ne → 0 < g.omega S

/-- The number of edges with exactly one end in the vertex set `X`. -/
def cut (G : Gr) (X : Finset ℕ) : ℕ :=
  G.edges.toList.countP fun e => decide (e.1 ∈ X) != decide (e.2 ∈ X)

/-- Cyclically 6-edge-connected: every edge cut separating two cycles has at least 6 edges. -/
def CyclicallySixConnected (G : Gr) : Prop :=
  ∀ X : Finset (Fin G.nv),
    ¬ ((G.sub (range G.ne)).induce (X : Set (Fin G.nv))).IsAcyclic →
    ¬ ((G.sub (range G.ne)).induce ((Xᶜ : Finset (Fin G.nv)) : Set (Fin G.nv))).IsAcyclic →
    6 ≤ cut G (X.map Fin.valEmbedding)

/-- Simple, 4-regular and cyclically 6-edge-connected. -/
def Completed (G : Gr) : Prop :=
  EdgesValid G ∧ noParallel G = true ∧ (∀ v < G.nv, deg G v = 4) ∧ CyclicallySixConnected G

/-- Panzer's Conjecture 1.2 for the period function `P`. -/
def HeppConj (P : Gr → ℝ) : Prop :=
  ∀ g₁ g₂ : Gr, IsPhi4 g₁ → IsPhi4 g₂ → (P g₁ = P g₂ ↔ hepp g₁ = hepp g₂)

/-- Panzer–Yeats Conjecture 1.10 for the period function `P`. `martin` is the vertex recursion of
their Definition 1.1, and `multiply G r = G^[r]`. -/
def MartinConj (P : Gr → ℝ) : Prop :=
  ∀ G₁ G₂ : Gr, Completed G₁ → Completed G₂ → ∀ v₁ < G₁.nv, ∀ v₂ < G₂.nv,
    (P (decomplete G₁ v₁) = P (decomplete G₂ v₂) ↔
      ∀ r ≥ 1, martin (multiply G₁ r) = martin (multiply G₂ r))

end HM
