# Erdős similarity for distance sets

[![Lean build](https://github.com/haraldschilly/math-distance-set-similarity/actions/workflows/lean.yml/badge.svg)](https://github.com/haraldschilly/math-distance-set-similarity/actions/workflows/lean.yml)

Lean 4 formalization and paper for

> **Erdős similarity for distance sets: finite patterns, a pinned obstruction, and an open window**
> Harald Schilly, 2026. [PDF](paper/distance-set-similarity-schilly-2026.pdf)
>
> **New to the topic?** Read the [plain-language explanation](EXPLAINER.md).

For a compact `E ⊂ ℝ^d` let `Δ(E) = {|x − y| : x, y ∈ E}`. The question studied here:

> **Question.** If `dim_H E > d/2`, must `Δ(E)` contain an affine copy `x + s·{2⁻ⁿ : n ≥ 1}` of the
> dyadic sequence?

It combines two results from the [OpenAI math release](https://github.com/openai/math):
the **Falconer distance theorem** (family 073) and the **dyadic case of the Erdős similarity
conjecture** (family 084).

| Result | Content | Lean |
|---|---|---|
| Theorem A | `dim_H E > d/2` ⇒ `Δ(E)` contains `x + sF` for every finite `F`, for a positive-measure set of `x` at every small scale `s` (both signs) | `finite_pattern_distSet` |
| Proposition 3.4 | Positive measure at every scale (which `Δ(E)` has) does not by itself force a dyadic copy | `exists_dyadicFree_pos_every_scale` |
| Theorem B | A compact `K ⊂ ℝ^d` with `0 ∈ K` and volume ≥ (1−η)^d·vol(B) whose distance set from the origin avoids every affine copy of the dyadic sequence, while `Δ(K)` contains one and, for d ≥ 2, every other `Δ_p(K)` contains an interval. Theorem 4.6 does the same for any ratio `q` | `pinned_dyadic_obstruction`, `pinned_geometric_obstruction` |
| Proposition C | A counterexample to the question has `Δ(E)` of positive measure with empty interior. With Mattila–Sjölin, the question is open only for `d/2 < dim_H E ≤ (d+1)/2`; a counterexample would be the first known set of dimension > d/2 whose distance set has empty interior | `counterexample_properties`, `window_of_mattilaSjolin` |

**Every lemma, proposition and theorem in the paper has a Lean proof** (table in the paper, Section 7, and in
[EXPLAINER.md](EXPLAINER.md#86-where-each-paper-statement-lives)). `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound` for all of them. CI enforces this on every push: the build
fails on any warning (including `sorry`), and `verify/check_axioms.py` fails on any other axiom.

## Trust base: please read

External results enter only as **explicit hypotheses** (`DistanceSimilarity/Statements.lean`),
never as axioms:

| Hypothesis | Source | Lean proof? | Used in |
|---|---|---|---|
| `FalconerStatement` | OpenAI, family 073 | **yes**, by OpenAI; re-checked here (`verify/`) | Thm A, Lemma 3.3, Prop 3.2, Prop C(iii) |
| `DyadicAvoidanceStatement` | OpenAI, family 084 | **yes**, by OpenAI; re-checked here (`verify/`) | Thm B, Prop 3.4 |
| `GeometricAvoidanceStatement q` | OpenAI preprint (Oct 5, 2026) | no (q = 1/2 is the dyadic case) | only Thm 4.6 for q ≠ 1/2 |
| `MattilaSjolinStatement` | Mattila–Sjölin 1999, peer-reviewed | **yes**, in [math-mattila-sjolin](https://github.com/haraldschilly/math-mattila-sjolin); re-checked here (`verify/`) | only Remark 5.1 |

The OpenAI inputs come from an AI-generated, **unrefereed** collection, whose README says "some of
the unformalized results could have issues". The first two inputs are among the formalized ones;
the third is not. The first two statements are copied verbatim from OpenAI's formal
statement files. `MattilaSjolinStatement` is proved, with exactly this statement, in the separate
repository [math-mattila-sjolin](https://github.com/haraldschilly/math-mattila-sjolin) (commit
`435cd62`, also written with Claude), which reuses some of OpenAI's Lean files. `verify/` rebuilds
OpenAI's Lean proofs (2459 files at commit `adc7f12`, Mathlib only) and the Mattila–Sjölin proof,
checks with the kernel that they prove *exactly* these statements, and derives unconditional
versions (`verify/Verify/Unconditional.lean`). The whole environment was also replayed with
`leanchecker --fresh`. Only `GeometricAvoidanceStatement q` for q ≠ 1/2 has no Lean proof.

## Build

Toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b` (the same pins as `openai/math/lean`).

```sh
lake exe cache get          # Mathlib build cache (~8 GB)
lake build                  # the conditional library, about a minute
lake env lean verify/Axioms.lean
```

## Re-checking the proofs of the inputs (optional, heavy)

```sh
git clone https://github.com/openai/math ../openai-math        # then check out commit adc7f12
git clone https://github.com/haraldschilly/math-mattila-sjolin ../math-mattila-sjolin  # commit 435cd62
python3 verify/fetch_oai.py ../openai-math ../math-mattila-sjolin   # copies 2459 OAI + 17 MS files
lake build Verify       # builds the proofs (~1–2 h on 6 cores, ~10 GB RAM), prints axioms
lake env leanchecker --fresh Verify.Unconditional   # replay the whole environment (~20 min, ~9 GB)
```

Lake builds in parallel on all cores. On a machine with little RAM, limit the build, e.g.
`systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0 -p AllowedCPUs=0-5 lake build Verify`.

## Paper

`paper/distance-set-similarity-schilly-2026.tex`; `paper/make-arxiv.sh` builds the PDF and an
arXiv upload bundle with the `.bbl` included.

## Citation

```bibtex
@misc{Schilly2026DistanceSimilarity,
  author       = {Schilly, Harald},
  title        = {Erd\H{o}s similarity for distance sets: finite patterns, a pinned obstruction, and an open window},
  year         = {2026},
  howpublished = {\url{https://github.com/haraldschilly/math-distance-set-similarity}}
}
```

## Use of AI

The results build on AI-generated mathematics (OpenAI). This repository and the paper were
prepared with substantial assistance from Claude (Anthropic). See the paper's acknowledgments.

## License

Apache-2.0. Files copied into `verify/oai-src/` by the fetch script are © OpenAI, Apache-2.0,
and are not part of this repository.
