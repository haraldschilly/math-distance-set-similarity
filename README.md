# Erdős similarity for distance sets

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
| Theorem B | A compact `K ⊂ ℝ^d` with volume ≥ (1−η)^d·vol(B) whose distance set from the origin avoids every affine copy of the dyadic sequence, while `Δ(K)` and every other `Δ_p(K)` (d ≥ 2) contain one. Theorem 4.6 does the same for any ratio `q` | `pinned_dyadic_obstruction`, `pinned_geometric_obstruction` |
| Proposition C | A counterexample to the question has `Δ(E)` of positive measure with empty interior. With Mattila–Sjölin, the question is open only for `d/2 < dim_H E ≤ (d+1)/2` | `counterexample_properties`, `window_of_mattilaSjolin` |

**Every numbered statement in the paper has a Lean proof** (table in the paper, Section 7, and in
[EXPLAINER.md](EXPLAINER.md#76-where-each-paper-statement-lives)). `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound` for all of them (`lake env lean verify/Axioms.lean`).

## Trust base: please read

External results enter only as **explicit hypotheses** (`DistanceSimilarity/Statements.lean`),
never as axioms:

| Hypothesis | Source | Lean proof? | Used in |
|---|---|---|---|
| `FalconerStatement` | OpenAI, family 073 | **yes**, by OpenAI; re-checked here (`verify/`) | Thm A, Lemma 3.3, Prop 3.2, Prop C(iii) |
| `DyadicAvoidanceStatement` | OpenAI, family 084 | **yes**, by OpenAI; re-checked here (`verify/`) | Thm B |
| `GeometricAvoidanceStatement q` | OpenAI preprint (Oct 5, 2026) | no (q = 1/2 is the dyadic case) | only Thm 4.6 for q ≠ 1/2 |
| `MattilaSjolinStatement` | Mattila–Sjölin 1999, peer-reviewed | no (not in Mathlib or OpenAI's library) | only Remark 5.1 |

The OpenAI inputs come from an AI-generated, **unrefereed** collection, whose README says some
results "could have issues". The first two statements are copied verbatim from OpenAI's formal
statement files. `verify/` rebuilds OpenAI's Lean proofs (2459 files at commit `adc7f12`, Mathlib
only), checks with the kernel that they prove *exactly* these statements, and derives unconditional
versions (`verify/Verify/Unconditional.lean`). The whole environment was also replayed with
`leanchecker --fresh`.

## Build

Toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b` (the same pins as `openai/math/lean`).

```sh
lake exe cache get          # Mathlib build cache (~8 GB)
lake build                  # the conditional library, about a minute
lake env lean verify/Axioms.lean
```

## Re-checking OpenAI's proofs of the inputs (optional, heavy)

```sh
git clone https://github.com/openai/math ../openai-math        # then check out commit adc7f12
python3 verify/fetch_oai.py ../openai-math                       # copies the 2459 needed files
lake build Verify       # builds the OAI proofs (~1–2 h on 6 cores, ~10 GB RAM), prints axioms
lake env leanchecker Verify.Unconditional   # replay the whole environment in the kernel
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
