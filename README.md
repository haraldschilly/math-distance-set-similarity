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
| Theorem A | `dim_H E > d/2` ⇒ `Δ(E)` contains `x + sF` for every finite `F`, for a positive-measure set of `x` at every small scale `s` (both signs) | `finite_pattern_distSet`, `exists_finite_pattern_distSet` |
| Theorem B | There is a compact `K ⊂ ℝ^d` with volume ≥ (1−η)^d·vol(B) (so `dim_H K = d`) whose distance set from the origin avoids every affine copy of the dyadic sequence, while `Δ(K)` and every other pinned distance set `Δ_p(K)` (d ≥ 2) contain one | `pinned_dyadic_obstruction` |
| Proposition C | Above the Mattila–Sjölin threshold `(d+1)/2` the answer is yes, so the question is open only for `d/2 < dim_H E ≤ (d+1)/2` | paper only |

## Status of the inputs: please read

The two inputs come from an AI-generated, **unrefereed** manuscript collection. Its README says
some results "could have issues". In this repository:

1. **Main library (`DistanceSimilarity/`)**: the inputs are **explicit hypotheses**
   (`FalconerStatement`, `DyadicAvoidanceStatement` in `Statements.lean`), with Lean types copied
   verbatim from OpenAI's formal statements. Theorems A and B are proved from them. `#print axioms`
   shows only `propext`, `Classical.choice`, `Quot.sound`.
2. **Verification (`verify/`)**: copies OpenAI's Lean proofs of the two inputs (2459 files at
   commit `adc7f12`, depending only on Mathlib), builds them with the same toolchain, and checks with
   the Lean kernel that they prove *exactly* our hypotheses. Unconditional versions of A and B
   are then derived.

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
