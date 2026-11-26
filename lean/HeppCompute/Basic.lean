/-!
# Executable part

Everything in this file is ordinary executable Lean (no Mathlib), compiled to native code
(`precompileModules`). The kernel-checked files in `HeppMartin/` relate each function here to
its mathematical meaning; `native_decide` is used only to evaluate the Boolean checks below.

Graphs are given by a vertex count `nv` and an array of edges `(a, b)`; vertices are `0 … nv-1`.
A set of edges is encoded as a natural number `n`: edge `i` belongs to it iff bit `i` of `n` is set.
-/

namespace HM

structure Gr where
  nv : Nat
  edges : Array (Nat × Nat)

/-- Number of edges. -/
def Gr.ne (g : Gr) : Nat := g.edges.size

/-- `allBelow f n = true` iff `f i = true` for all `i < n`. Tail recursive, i.e. a loop. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => if f k then allBelow f k else false

/-- Number of `i < k` such that bit `i` of `n` is set. -/
def popc (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => popc n k + (if n.testBit k then 1 else 0)

/-! ## Connected components of an edge subset, with a certificate -/

/-- Vertex labels are packed four bits per vertex (graphs here have at most 16 vertices). -/
def labGet (L v : Nat) : Nat := (L >>> (4 * v)) % 16
def labSet (L v x : Nat) : Nat := L - (labGet L v <<< (4 * v)) + (x <<< (4 * v))
def labInit : Nat → Nat
  | 0 => 0
  | k + 1 => labInit k + (k <<< (4 * k))

/-- One pass of minimum-label propagation over the edges of subset `n`. -/
def sweep (g : Gr) (n : Nat) : Nat → Nat → Nat
  | 0, L => L
  | i + 1, L =>
    if n.testBit i then
      let e := g.edges[i]!
      let la := labGet L e.1
      let lb := labGet L e.2
      if la < lb then sweep g n i (labSet L e.2 la)
      else if lb < la then sweep g n i (labSet L e.1 lb)
      else sweep g n i L
    else sweep g n i L

def propagate (g : Gr) (n : Nat) : Nat → Nat → Nat
  | 0, L => L
  | f + 1, L => let L' := sweep g n g.ne L; if L' == L then L else propagate g n f L'

/-- Packed component labels of edge subset `n` (the least vertex of each component). -/
def labOf (g : Gr) (n : Nat) : Nat := propagate g n (g.nv + 1) (labInit g.nv)

/-- Number of vertices that are their own label. -/
def rootCount (g : Gr) (L : Nat) : Nat → Nat
  | 0 => 0
  | v + 1 => rootCount g L v + (if labGet L v == v then 1 else 0)

/-- `omega(S) = 2 rank(S) - |S|` with `rank = nv - #components`, from the labels. -/
def omegaFast (g : Gr) (n : Nat) : Int :=
  2 * ((g.nv : Int) - (rootCount g (labOf g n) g.nv : Nat)) - (popc n g.ne : Nat)

/-- Breadth-first search tree from the roots: parent, depth and parent edge of every vertex. -/
def bfsCert (g : Gr) (n L : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let V := g.nv
  let mut dep := Array.replicate V 1000
  let mut par := Array.replicate V 0
  let mut pe := Array.replicate V 0
  let mut queue : Array Nat := #[]
  for v in [0:V] do
    if labGet L v == v then
      dep := dep.set! v 0
      queue := queue.push v
  let mut qi := 0
  for _ in [0:V] do
    if qi < queue.size then
      let u := queue[qi]!
      qi := qi + 1
      for i in [0:g.ne] do
        if n.testBit i then
          let e := g.edges[i]!
          let w := if e.1 == u then e.2 else if e.2 == u then e.1 else V
          if w < V && dep[w]! == 1000 then
            dep := dep.set! w (dep[u]! + 1)
            par := par.set! w u
            pe := pe.set! w i
            queue := queue.push w
  return (par, dep, pe)

/-- Every edge of subset `n` joins two vertices with the same label. -/
def edgesRespect (g : Gr) (n L : Nat) : Bool :=
  allBelow (fun i => !n.testBit i || labGet L g.edges[i]!.1 == labGet L g.edges[i]!.2) g.ne

/-- Every label is a vertex that is its own label, and every other vertex has a parent with the
same label, joined to it by an edge of subset `n`, at smaller depth. -/
def treeOK (g : Gr) (n L : Nat) (par dep pe : Array Nat) : Bool :=
  allBelow (fun v =>
    labGet L v < g.nv && labGet L (labGet L v) == labGet L v &&
    (labGet L v == v ||
      (par[v]! < g.nv && pe[v]! < g.ne && n.testBit pe[v]! &&
        (g.edges[pe[v]!]! == (v, par[v]!) || g.edges[pe[v]!]! == (par[v]!, v)) &&
        labGet L par[v]! == labGet L v && decide (dep[par[v]!]! < dep[v]!)))) g.nv

def certValid (g : Gr) (n : Nat) : Bool :=
  let L := labOf g n
  let c := bfsCert g n L
  edgesRespect g n L && treeOK g n L c.1 c.2.1 c.2.2

/-- The component certificate is valid for every edge subset. -/
def certAll (g : Gr) : Bool := allBelow (certValid g) (2 ^ g.ne)

/-- The graph is primitive and logarithmically divergent, and every `omega` divides `D`:
`omega = 0` for the empty and the full set, `1 ≤ omega ∣ D` otherwise. -/
def phiOK (g : Gr) (D : Nat) : Bool :=
  allBelow (fun n =>
    let w := omegaFast g n
    if n == 0 || n == 2 ^ g.ne - 1 then w == 0 else decide (1 ≤ w) && (D : Int) % w == 0) (2 ^ g.ne)

/-- Edges are in range and are not self-loops. -/
def wellFormed (g : Gr) : Bool := g.edges.all fun e => e.1 < g.nv && e.2 < g.nv && e.1 != e.2

/-- Number of edge ends at vertex `v`. -/
def deg (g : Gr) (v : Nat) : Nat :=
  g.edges.foldl (fun c e => c + (if e.1 == v then 1 else 0) + (if e.2 == v then 1 else 0)) 0

def maxDegLe (g : Gr) (k : Nat) : Bool := allBelow (fun v => decide (deg g v ≤ k)) g.nv
def regular (g : Gr) (k : Nat) : Bool := allBelow (fun v => deg g v == k) g.nv

/-! ## Hepp bound modulo a prime -/

/-- Sum over edges `e < k` not in `n` of `(D / omega(n+e)) * t(n+e)`, added to `acc`. -/
def dpSum (D : Nat) (om t : Array Nat) (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | e + 1, acc =>
    dpSum D om t n e (if n.testBit e then acc else acc + D / om[n + 2 ^ e]! * t[n + 2 ^ e]!)

def stepv (N D p : Nat) (om t : Array Nat) (n : Nat) : Nat :=
  if N - popc n N ≤ 1 then 1 % p else dpSum D om t n N 0 % p

/-- Fills entries `k-1, k-2, …, 0` of `t`, each from entries with larger index. -/
def fill (N D p : Nat) (om : Array Nat) : Nat → Array Nat → Array Nat
  | 0, t => t
  | k + 1, t => fill N D p om k (t.set! k (stepv N D p om t k))

def omTab (g : Gr) : Array Nat := (Array.range (2 ^ g.ne)).map fun n => (omegaFast g n).toNat

/-- `D^(N-1) * H(g)` modulo each prime in `ps`. -/
def heppMods (g : Gr) (D : Nat) (ps : List Nat) : List Nat :=
  let om := omTab g
  ps.map fun p => (fill g.ne D p om (2 ^ g.ne) (Array.replicate (2 ^ g.ne) 0))[0]!

/-! ## Martin invariant (Panzer–Yeats, Definition 1.1) -/

/-- Neighbours of `v`, one entry per half-edge. -/
def halfEdges (es : List (Nat × Nat)) (v : Nat) : List Nat :=
  es.flatMap fun e => (if e.1 == v then [e.2] else []) ++ (if e.2 == v then [e.1] else [])

/-- All perfect matchings of a list of half-edges (positions are distinguished). -/
def matchings : List Nat → List (List (Nat × Nat))
  | [] => [[]]
  | a :: rest =>
    (List.finRange rest.length).flatMap fun (i : Fin rest.length) =>
      (matchings (rest.eraseIdx i.val)).map ((a, rest[i]) :: ·)
termination_by l => l.length
decreasing_by simp only [List.length_cons]; have := List.length_eraseIdx_le rest i.val; omega

/-- `M = 0` with a self-loop; `M = 1` with three vertices; otherwise eliminate the first vertex
of `order`, summing over all transitions (perfect matchings of its half-edges). -/
def martinAux : List Nat → List (Nat × Nat) → Nat
  | order, es =>
    if es.any (fun e => e.1 == e.2) then 0
    else match order with
      | [] => 1
      | v :: rest =>
        if rest.length ≤ 2 then 1
        else ((matchings (halfEdges es v)).map fun τ =>
          martinAux rest (es.filter (fun e => e.1 != v && e.2 != v) ++ τ)).sum

def martin (G : Gr) : Nat := martinAux (List.range G.nv) G.edges.toList

/-- `G^[r]`: every edge replaced by `r` parallel edges. -/
def multiply (G : Gr) (r : Nat) : Gr := ⟨G.nv, G.edges.flatMap fun e => Array.replicate r e⟩

/-! ## Completed graphs -/

/-- Delete vertex `v` and shift the larger labels down by one. -/
def decomplete (G : Gr) (v : Nat) : Gr :=
  ⟨G.nv - 1, (G.edges.filter fun e => e.1 != v && e.2 != v).map fun e =>
    (if e.1 > v then e.1 - 1 else e.1, if e.2 > v then e.2 - 1 else e.2)⟩

/-- Number of edges with exactly one end in the vertex set encoded by `X`. -/
def cutSize (G : Gr) (X : Nat) : Nat :=
  G.edges.foldl (fun c e => if X.testBit e.1 != X.testBit e.2 then c + 1 else c) 0

/-- Every vertex set with at least two vertices on each side has at least 6 edges across. -/
def cutsOK (G : Gr) : Bool :=
  allBelow (fun X => let k := popc X G.nv; if 2 ≤ k && k + 2 ≤ G.nv then decide (6 ≤ cutSize G X) else true)
    (2 ^ G.nv)

/-- No two edges join the same pair of vertices. -/
def noParallel (G : Gr) : Bool :=
  let es := G.edges.toList.map fun e => (min e.1 e.2, max e.1 e.2)
  es.Nodup

end HM
