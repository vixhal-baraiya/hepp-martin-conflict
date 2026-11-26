# Two "perfect invariant" conjectures for φ⁴ periods are incompatible

Two conjectures each claim that a single combinatorial invariant determines the period of a primitive φ⁴ graph.

- **Panzer, Conjecture 1.2** in *Hepp's bound for Feynman graphs and matroids*, [arXiv:1908.09820](https://arxiv.org/abs/1908.09820). Two φ⁴ graphs have equal periods if and only if they have equal Hepp bounds.
- **Panzer–Yeats, Conjecture 1.10** in *Feynman symmetries of the Martin and c₂ invariants of regular graphs*, [arXiv:2304.05299](https://arxiv.org/abs/2304.05299). For cyclically 6-connected 4-regular graphs $G_1, G_2$, the periods of $G_1\setminus v_1$ and $G_2\setminus v_2$ are equal if and only if the Martin sequences are equal, $M(G_1^{[r]}) = M(G_2^{[r]})$ for all $r\ge1$. Here $G^{[r]}$ replaces every edge by $r$ parallel edges, and $M$ is the Martin invariant.

## Result

**Theorem.** Each of the following pairs of completed primitive 13-loop φ⁴ graphs has exactly equal Hepp bounds and different Martin sequences. Graphs are given by their Nickel labels.

| Pair | Graph | Hepp bound | $M(G)$ | $M(G^{[2]})$ |
|---|---|---|---|---|
| 1 | `/bcde/2379/35a/56/67ae/9c/8b/8b/cd/be/cd///e//` | 2182616636.556… | 79588 | 348839598217834266624 |
|   | `/bcde/4567/56ae/79ae/56c/d/b/8b/9cd/be/cd/////` | equal | 79588 | 348843461127526416384 |
| 2 | `/bcde/2345/68a/45c/8c/7b/79b/de/de/abc/de/////` | 2595492870.040… | 73720 | 284715817343259770880 |
|   | `/bcde/3578/345a/45/6e/c/78d/9b/9b/ce/bcd///e//` | equal | 73720 | 284712506277809356800 |
| 3 | `/bcde/2469/89a/4578/57/6e/ab/ce/bd/cd/bc///e//` | 2694150096.292… | **71544** | 268222963836147204096 |
|   | `/bcde/489a/3567/578/569/e/ab/ce/bd/cd/bc///e//` | equal | **71604** | 268261011285444919296 |

**Corollary.** Panzer's Conjecture 1.2 and Panzer–Yeats Conjecture 1.10 cannot both be true.

The corollary follows from either pair. All six graphs are 4-regular and simple, and their only 4-edge cuts isolate a single vertex. Each is therefore cyclically 6-connected, and each decompletion is a primitive log-divergent φ⁴ graph. Both conjectures apply to every pair.
- Conjecture 1.2 says the two graphs of a pair have equal periods, because their Hepp bounds are equal.
- Conjecture 1.10 says they have different periods, because their Martin sequences differ.

The corollary is also proved in Lean, for pair 3 (see [Lean formalization](#lean-formalization)).

## Which conjecture fails

The periods of pair 3 were computed with Borinsky's tropical Monte Carlo integrator ([tropical-feynman-quadrature](https://github.com/michibo/tropical-feynman-quadrature)), using 7.5·10⁹ samples per graph:

| Graph | $M(G)$ | Period |
|---|---|---|
| `/bcde/2469/89a/4578/57/6e/ab/ce/bd/cd/bc///e//` | 71544 | 20703.18 ± 1.01 |
| `/bcde/489a/3567/578/569/e/ab/ce/bd/cd/bc///e//` | 71604 | 20703.00 ± 1.01 |

The difference is 0.18 ± 1.42, so the periods agree to about 7·10⁻⁵ of their size. This is numerical evidence that Conjecture 1.10 is the false one: two graphs with different Martin invariants appear to have the same period, as Conjecture 1.2 predicts. It is not a proof, since an exact evaluation of 13-loop periods is out of reach. Balduf's dataset gives 20696.3 ± 5.3 for the first graph, which is consistent.

## Method

**Hepp bound.** For the decompletion $G\setminus v$ with $N$ edges,

$$H = \sum_{\sigma}\ \prod_{k=1}^{N-1} \frac{1}{\omega(\{\sigma_1,\dots,\sigma_k\})},\qquad \omega(S) = 2\,\mathrm{rank}(S) - |S|,$$

where the sum runs over all orderings $\sigma$ of the edges (Panzer, Definition 2.4 with unit edge weights in four dimensions). The Hepp bound of a completed graph does not depend on $v$ (Panzer, Theorem 1.1).

[`src/hepp_check.c`](src/hepp_check.c) evaluates $H$ by a recursion over the $2^{26}$ edge subsets, modulo primes and in floating point. Equality is then proved by a Chinese remainder argument. Let $W=\max\omega$ (here $W = 13$) and $D=\mathrm{lcm}(1,\dots,W)$. Then $X = D^{N-1}H$ is a positive integer with $X\le N!\,D^{N-1} < 2^{550}$. If two Hepp bounds agree modulo primes whose product exceeds that bound, they are equal. The script uses the 24 largest primes below $2^{30}$, whose product exceeds $2^{719}$. The program also checks that every proper nonempty edge subset has $\omega > 0$ and that $\omega(E)=0$; this is exactly primitivity and log-divergence.

**Martin invariant.** Two unrelated computations:
1. [`src/martin_trees.py`](src/martin_trees.py) counts the partitions of $E(G\setminus v)$ into two spanning trees. This equals $M(G)$ for any vertex $v$ (Panzer–Yeats, Theorem 1.3). The count is done at all 15 vertices.
2. [`src/martin_recursion.py`](src/martin_recursion.py) evaluates the defining vertex recursion (Definition 1.1), both for $G$ and for the 8-regular graph $G^{[2]}$.

The two methods agree on $M(G)$. The values of $\ln M(G)$ and $\ln M(G^{[2]})$ also agree to ten decimals with those in Balduf's dataset, which were computed independently. In pairs 1 and 2 the values of $M(G^{[2]})$ differ by relative amounts of $1.1\cdot10^{-5}$ and $1.2\cdot10^{-5}$, far above the dataset's ten-decimal precision.

**Tests.** [`tests/selftest.py`](tests/selftest.py) checks every method on all 72 graphs of the dataset with 3 to 8 loops:
- the Hepp bound by definition (a sum over all orderings) against the rational subset recursion;
- the C code modulo primes against exact rational values, at several decompletion vertices;
- floating-point Hepp bounds and both Martin invariants against the dataset.

## Lean formalization

[`lean/`](lean) proves the corollary in Lean 4.36 with Mathlib (tag `v4.36.0`), using pair 3:

```lean
theorem HM.not_both (P : Gr → ℝ) : ¬ (HeppConj P ∧ MartinConj P)
```

`P` is an arbitrary real-valued function on graphs, so the theorem applies to the actual period. [`Conjectures.lean`](lean/HeppMartin/Conjectures.lean) states both conjectures. [`Spec.lean`](lean/HeppMartin/Spec.lean) defines the Hepp bound literally as Panzer's sum over all $N!$ edge orderings, with the rank taken from Mathlib's connected components.

**Kernel-checked proofs:**
- [`Recursion.lean`](lean/HeppMartin/Recursion.lean): the ordering sum equals a recursion over edge subsets.
- [`Integer.lean`](lean/HeppMartin/Integer.lean): denominators clear to an integer $X = D^{N-1}H$ with $X \le (N D)^{N-1}$.
- [`Table.lean`](lean/HeppMartin/Table.lean): the compiled table loop returns $X \bmod p$.
- [`Cert.lean`](lean/HeppMartin/Cert.lean): a labelling with a search-tree certificate counts Mathlib's connected components, so the fast $\omega$ equals the specification.
- [`Structure.lean`](lean/HeppMartin/Structure.lean): the Boolean checks imply the hypotheses of both conjectures, including cyclic 6-edge-connectivity.
- [`Main.lean`](lean/HeppMartin/Main.lean):
  - the Chinese remainder step, where coprimality of the 22 primes and the bound $(26D)^{25} < \prod p$ are decided by the kernel;
  - the final theorem.

**Checked with `native_decide`.** These are the finite computations too large for the kernel, in [`lean/HeppMartin/Checks`](lean/HeppMartin/Checks):
- the component certificates and $\omega$ values for all $2^{26}$ edge subsets of both decompletions;
- the two residue tables modulo 22 primes below $2^{30}$;
- the Martin values 71544 and 71604;
- the structural checks and the edge counts.

`native_decide` trusts Lean's compiler: in this Lean version each use adds an axiom stating that the compiled evaluation of its Boolean check returned `true`. So this is a Lean proof whose large finite computations are evaluated by compiled code, not a proof checked entirely by the kernel. [`results/lean_axioms.txt`](results/lean_axioms.txt), printed by [`Axioms.lean`](lean/HeppMartin/Axioms.lean), lists the axioms of the main theorem: `propext`, `Classical.choice`, `Quot.sound` and the 23 `native_decide` axioms of the checks above. The reductions (`hepp_eq_hq`, `heppMods_eq`, `omegaFast_eq_of_certAll`) use only the three standard axioms.

**Definitions you must trust:**
- `martin`, the vertex recursion of Panzer–Yeats Definition 1.1, which eliminates vertices in label order. The paper states that the result does not depend on the order; that statement is not formalized here.
- `decomplete`, `multiply`, `deg`, `noParallel` and `cut`, short executable functions.

**Not formalized:** the numerical periods.

```sh
cd lean
lake exe cache get            # prebuilt Mathlib
lake build                    # about 30 min with 15 cores and 24 GB of memory
```

## Verification

Requires Python 3.9+ and a C compiler; there are no other dependencies.

```sh
python3 tests/selftest.py     # about 15 s
python3 verify.py             # about 2.5 min on 8 cores; output in results/verify_output.txt
```

The period computation needs a checkout of tropical-feynman-quadrature (MIT license), Eigen and OpenMP. Copy [`periods/period.cpp`](periods/period.cpp) into the checkout, build it like the repository's examples, and run:

```sh
./period pair3_a_decompleted.txt 100000000 75 1301
./period pair3_b_decompleted.txt 100000000 75 1302
python3 periods/combine.py periods/pair3_a.log periods/pair3_b.log
```

The logs in [`periods/`](periods) are from these runs. Their `total` column comes from the library's running statistics, which overflow beyond $2^{32}$ samples, so it is ignored. The quoted values combine the 75 independent batch estimates. The batch scatter matches the batch error bars ($\chi^2/\mathrm{dof}$ = 0.79 and 1.04). Each run took about 70 minutes with 15 threads.

## Data

The graphs and the reference values come from P.-H. Balduf, *Feynman periods in φ⁴-theory*, Borealis, [doi:10.5683/SP3/NLEDGH](https://doi.org/10.5683/SP3/NLEDGH), licensed CC BY 4.0. [`data/graphs.json`](data/graphs.json) holds the six rows used, and [`data/small_graphs.json`](data/small_graphs.json) the rows for 3 to 8 loops. Both files keep the dataset's values unchanged.

## References

- E. Panzer, *Hepp's bound for Feynman graphs and matroids*, Ann. Inst. Henri Poincaré D 10 (2023) 31–119, [arXiv:1908.09820](https://arxiv.org/abs/1908.09820).
- E. Panzer, K. Yeats, *Feynman symmetries of the Martin and c₂ invariants of regular graphs*, [arXiv:2304.05299](https://arxiv.org/abs/2304.05299).
- P.-H. Balduf, *Statistics of Feynman amplitudes in φ⁴-theory*, JHEP 11 (2023) 160.
- P.-H. Balduf, K. Shaban, *Predicting Feynman periods in φ⁴-theory*, [arXiv:2403.16217](https://arxiv.org/abs/2403.16217).
- M. Borinsky, *Tropical Monte Carlo quadrature for Feynman integrals*, [arXiv:2008.12310](https://arxiv.org/abs/2008.12310).

## Author and license

Vishal Singh Baraiya. The code is released under the MIT License, and the text and data under CC BY 4.0. See [LICENSE](LICENSE).
