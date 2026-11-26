# Panzer's Hepp-bound conjecture contradicts the Martin and c₂ conjectures for φ⁴ periods

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24559411.svg)](https://doi.org/10.5281/zenodo.24559411)

Several conjectures claim that a combinatorial invariant determines, or is determined by, the period of a primitive φ⁴ graph.

- **Panzer, Conjecture 1.2** in *Hepp's bound for Feynman graphs and matroids*, [arXiv:1908.09820](https://arxiv.org/abs/1908.09820). Two φ⁴ graphs have equal periods if and only if they have equal Hepp bounds.
- **Panzer–Yeats, Conjecture 1.10** in *Feynman symmetries of the Martin and c₂ invariants of regular graphs*, [arXiv:2304.05299](https://arxiv.org/abs/2304.05299). For cyclically 6-connected 4-regular graphs $G_1, G_2$, the periods of $G_1\setminus v_1$ and $G_2\setminus v_2$ are equal if and only if the Martin sequences are equal, $M(G_1^{[r]}) = M(G_2^{[r]})$ for all $r\ge1$. Here $G^{[r]}$ replaces every edge by $r$ parallel edges, and $M$ is the Martin invariant.
- **Brown–Schnetz, Conjecture 5** in *A K3 in φ⁴*, Duke Math. J. 161 (2012), [arXiv:1006.4064](https://arxiv.org/abs/1006.4064). Graphs with equal periods have equal $c_2$ invariants.

## Result

**Theorem.** Each of the following pairs of completed primitive 13-loop φ⁴ graphs has exactly equal Hepp bounds and different Martin sequences. In pair 3 the $c_2$ invariants at $p = 3$ also differ. Graphs are given by their Nickel labels.

| Pair | Graph | Hepp bound | $M(G)$ | $M(G^{[2]})$ | $c_2^{(3)}$ |
|---|---|---|---|---|---|
| 1 | `/bcde/2379/35a/56/67ae/9c/8b/8b/cd/be/cd///e//` | 2182616636.556… | 79588 | 348839598217834266624 | 0 |
|   | `/bcde/4567/56ae/79ae/56c/d/b/8b/9cd/be/cd/////` | equal | 79588 | 348843461127526416384 | 0 |
| 2 | `/bcde/2345/68a/45c/8c/7b/79b/de/de/abc/de/////` | 2595492870.040… | 73720 | 284715817343259770880 | 2 |
|   | `/bcde/3578/345a/45/6e/c/78d/9b/9b/ce/bcd///e//` | equal | 73720 | 284712506277809356800 | 2 |
| 3 | `/bcde/2469/89a/4578/57/6e/ab/ce/bd/cd/bc///e//` | 2694150096.292… | **71544** | 268222963836147204096 | **1** |
|   | `/bcde/489a/3567/578/569/e/ab/ce/bd/cd/bc///e//` | equal | **71604** | 268261011285444919296 | **0** |

$c_2^{(p)}$ is the $c_2$ invariant of $G\setminus v$ at the prime $p$. It follows from the Martin sequence by Panzer–Yeats Theorem 1.8: $c_2^{(p)}(G\setminus v) \equiv M(G^{[p-1]})/(3p) \bmod p$. At $p = 2$ all six graphs have $c_2^{(2)} = 0$.

**Corollary.**
1. Panzer's Conjecture 1.2 and Panzer–Yeats Conjecture 1.10 cannot both be true (any of the three pairs).
2. Panzer's Conjecture 1.2 and Brown–Schnetz Conjecture 5 cannot both be true (pair 3).

All six graphs are 4-regular and simple, and their only 4-edge cuts isolate a single vertex. Each is therefore cyclically 6-connected, and each decompletion is a primitive log-divergent φ⁴ graph, so all three conjectures apply.
- Conjecture 1.2 says the two graphs of a pair have equal periods, because their Hepp bounds are equal.
- Conjecture 1.10 says they have different periods, because their Martin sequences differ.
- Conjecture 5 says the graphs of pair 3 have different periods, because their $c_2$ invariants differ.

Part 1 is also proved in Lean, for pair 3 (see [Lean formalization](#lean-formalization)). Part 2 uses Panzer–Yeats Theorem 1.8, which is not formalized here.

## Which conjecture fails

The periods of pair 3 were computed with Borinsky's tropical Monte Carlo integrator ([tropical-feynman-quadrature](https://github.com/michibo/tropical-feynman-quadrature)), using 7.5·10⁹ samples per graph:

| Graph | $M(G)$ | $c_2^{(3)}$ | Period |
|---|---|---|---|
| `/bcde/2469/89a/4578/57/6e/ab/ce/bd/cd/bc///e//` | 71544 | 1 | 20703.18 ± 1.01 |
| `/bcde/489a/3567/578/569/e/ab/ce/bd/cd/bc///e//` | 71604 | 0 | 20703.00 ± 1.01 |

The difference is 0.18 ± 1.42, so the periods agree to about 7·10⁻⁵ of their size. Balduf's dataset gives 20696.3 ± 5.3 for the first graph, which is consistent. The numerics do not decide the question:
- Equal periods would refute both the Martin conjecture and the Brown–Schnetz $c_2$ conjecture.
- Periods that differ by less than the error bar would refute only Panzer's Hepp conjecture.

Graphs with equal Hepp bounds are expected to have very close periods in any case, because the Hepp bound tracks the period closely (Panzer, Section 5). Panzer also notes that his conjecture requires graphs with equal Hepp bounds to have equal $c_2$ invariants. Pair 3 is a pair where this fails, which points to Conjecture 1.2 as the false one. Settling the question needs either the exact periods or a far more precise computation than the one here.

## Method

**Hepp bound.** For the decompletion $G\setminus v$ with $N$ edges,

$$H = \sum_{\sigma}\ \prod_{k=1}^{N-1} \frac{1}{\omega(\{\sigma_1,\dots,\sigma_k\})},\qquad \omega(S) = 2\,\mathrm{rank}(S) - |S|,$$

where the sum runs over all orderings $\sigma$ of the edges (Panzer, Definition 2.4 with unit edge weights in four dimensions). The Hepp bound of a completed graph does not depend on $v$ (Panzer, Theorem 1.1).

[`src/hepp_check.c`](src/hepp_check.c) evaluates $H$ by a recursion over the $2^{26}$ edge subsets, modulo primes and in floating point. Equality is then proved by a Chinese remainder argument. Let $W=\max\omega$ (here $W = 13$) and $D=\mathrm{lcm}(1,\dots,W)$. Then $X = D^{N-1}H$ is a positive integer with $X\le N!\,D^{N-1} < 2^{550}$. If two Hepp bounds agree modulo primes whose product exceeds that bound, they are equal. The script uses the 24 largest primes below $2^{30}$, whose product exceeds $2^{719}$. The program also checks that every proper nonempty edge subset has $\omega > 0$ and that $\omega(E)=0$; this is exactly primitivity and log-divergence.

**$c_2$ invariant.** [`src/c2.py`](src/c2.py) applies Panzer–Yeats Theorem 1.8 to the exact values of $M(G)$ and $M(G^{[2]})$, giving $c_2$ at $p = 2$ and $p = 3$. The self-test checks it on the zigzag graphs, whose $c_2$ is $-1$ at every prime.

**Martin invariant.** Two unrelated computations:
1. [`src/martin_trees.py`](src/martin_trees.py) counts the partitions of $E(G\setminus v)$ into two spanning trees. This equals $M(G)$ for any vertex $v$ (Panzer–Yeats, Theorem 1.3). The count is done at all 15 vertices.
2. [`src/martin_recursion.py`](src/martin_recursion.py) evaluates the defining vertex recursion (Definition 1.1), both for $G$ and for the 8-regular graph $G^{[2]}$.

The two methods agree on $M(G)$. The values of $\ln M(G)$ and $\ln M(G^{[2]})$ also agree to ten decimals with those in Balduf's dataset, which were computed independently. In pairs 1 and 2 the values of $M(G^{[2]})$ differ by relative amounts of $1.1\cdot10^{-5}$ and $1.2\cdot10^{-5}$, far above the dataset's ten-decimal precision.

**Tests.** [`tests/selftest.py`](tests/selftest.py) checks every method on all 72 graphs of the dataset with 3 to 8 loops:
- the Hepp bound by definition (a sum over all orderings) against the rational subset recursion;
- the C code modulo primes against exact rational values, at several decompletion vertices;
- floating-point Hepp bounds and both Martin invariants against the dataset;
- the $c_2$ formula on the zigzag graphs.

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
- F. Brown, O. Schnetz, *A K3 in φ⁴*, Duke Math. J. 161 (2012) 1817–1862, [arXiv:1006.4064](https://arxiv.org/abs/1006.4064).
- P.-H. Balduf, *Statistics of Feynman amplitudes in φ⁴-theory*, JHEP 11 (2023) 160.
- P.-H. Balduf, K. Shaban, *Predicting Feynman periods in φ⁴-theory*, [arXiv:2403.16217](https://arxiv.org/abs/2403.16217).
- M. Borinsky, *Tropical Monte Carlo quadrature for Feynman integrals*, [arXiv:2008.12310](https://arxiv.org/abs/2008.12310).

## Citation

The code, data and Lean proof are archived on Zenodo: [doi:10.5281/zenodo.24559411](https://doi.org/10.5281/zenodo.24559411) (all versions). Version 1.1 ([doi:10.5281/zenodo.24560046](https://doi.org/10.5281/zenodo.24560046)) adds the $c_2$ invariants and corrects the assessment of which conjecture fails; version 1.0 is [doi:10.5281/zenodo.24559412](https://doi.org/10.5281/zenodo.24559412). GitHub's "Cite this repository" button uses [CITATION.cff](CITATION.cff).

## Author and license

Vishal Singh Baraiya. The code is released under the MIT License, and the text and data under CC BY 4.0. See [LICENSE](LICENSE).
