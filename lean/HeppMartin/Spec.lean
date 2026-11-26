import Mathlib
import HeppCompute

/-!
# Definitions

* `Gr.sub g S`: the simple graph on the vertices `Fin g.nv` whose edges are the edges of `g`
  with index in `S`.
* `Gr.rank g S = nv - #components`, the rank of `S` in the graphic matroid.
* `Gr.omega g S = 2 rank(S) - |S|`, the superficial degree of convergence in `D = 4` dimensions.
* `hepp g`: the Hepp bound (Panzer, arXiv:1908.09820), the sum over all orderings
  `e₁, …, e_N` of the edges of `∏_{k=1}^{N-1} 1 / omega {e₁, …, e_k}`.
-/

open Finset

namespace HM

/-- The graph on all vertices of `g` with the edges whose index lies in `S`. -/
def Gr.sub (g : Gr) (S : Finset ℕ) : SimpleGraph (Fin g.nv) :=
  SimpleGraph.fromRel fun x y => ∃ i ∈ S, ∃ h : i < g.edges.size, g.edges[i] = (x.val, y.val)

/-- Rank of an edge set in the graphic matroid: number of vertices minus number of components. -/
noncomputable def Gr.rank (g : Gr) (S : Finset ℕ) : ℕ :=
  g.nv - Nat.card (g.sub S).ConnectedComponent

/-- `omega(S) = 2 rank(S) - |S|`. -/
noncomputable def Gr.omega (g : Gr) (S : Finset ℕ) : ℤ :=
  2 * (g.rank S : ℤ) - S.card

/-- The product of `1 / omega` over the proper nonempty initial segments of an ordering `l`. -/
noncomputable def heppTerm (g : Gr) (l : List ℕ) : ℚ :=
  ∏ k ∈ range (l.length - 1), ((g.omega (l.take (k + 1)).toFinset : ℚ))⁻¹

/-- The Hepp bound: the sum of `heppTerm` over all orderings of the edges `0, …, N-1`. -/
noncomputable def hepp (g : Gr) : ℚ :=
  ((List.range g.ne).permutations.map (heppTerm g)).sum

end HM
