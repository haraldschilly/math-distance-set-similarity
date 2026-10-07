# What is this about? A plain-language explanation

This page explains the paper without assuming a mathematics background. The precise
statements are in the [paper](paper/distance-set-similarity-schilly-2026.pdf).

## 1. Distance sets

Take any collection of points in the plane, or in 3D space, or in higher dimensions. Measure the
distance between every pair of points and write down all the numbers you get. That list of
numbers is the **distance set** of the collection.

- Three corners of an equilateral triangle with side 1 have distance set {0, 1}.
- A full disk of radius 1 has distance set [0, 2]: every length from 0 to 2 occurs.

The interesting cases lie in between. These are **fractals**, dust-like sets that are thinner than a
solid region but much richer than finitely many points. Their size is measured by a
**fractal dimension**: a line has dimension 1, a filled square 2, and a fractal can have
dimension 1.37.

## 2. Falconer's question (1985)

How big must a set be before its distance set is "substantial", meaning its distances
cover a positive total length of the number line rather than a negligible dust of numbers?

Falconer conjectured that, in d-dimensional space, **dimension more than d/2** is enough. In the
plane that means dimension above 1. This was a famous open problem for 40 years. In 2026
OpenAI published a proof in all dimensions (input 1 of our paper).

## 3. Erdős' question (1974)

Take an infinite pattern of numbers, for example

    1/2, 1/4, 1/8, 1/16, ...

Now take any "fat" set of numbers, meaning one with positive total length, like an interval with
lots of tiny holes punched in it. Must the fat set contain a **shrunken and shifted copy** of the
pattern, that is, numbers x + s/2, x + s/4, x + s/8, ... for some starting point x and scale s?

- For **finite** patterns the answer is yes: every fat set contains small copies of every finite
  pattern (Steinhaus, 1920).
- Erdős conjectured that for **infinite** patterns the answer is always no. For 1/2, 1/4, 1/8, ...
  this was a well-known open case for decades. In 2026 OpenAI published a construction of a fat set
  that avoids every copy of it (input 2 of our paper).

## 4. Our question: combining the two

Falconer's theorem says distance sets of big sets are fat. Erdős-type results say fat isn't
enough to guarantee an infinite pattern. But distance sets are special fat sets. They have
structure at every scale: zooming into a small piece of the set gives its own distances. So:

> **If a set has dimension more than d/2, must its distance set contain a copy of
> 1/2, 1/4, 1/8, ...?**

As far as we could find, nobody had asked this before.

## 5. What we prove

**Theorem A: finite patterns, yes.** Every finite pattern appears in the distance set, at every
small scale and with lots of room to move it around. This follows from Falconer's theorem plus
the classical Steinhaus argument.

**Theorem B: an "onion" counterexample, from one point of view.** Take the bad fat set A from Erdős'
side (numbers between 0 and 1). Build a ball made of thin spherical shells around the center, one
shell of radius r for every number r in A. Like an onion, but with the layers chosen by A.

```
        .-~~~-.
     .'  .-~-.  '.        shells at radii r in A
    /  .' .-. '.  \       (A = the bad set that avoids
   |  |  ( o )  |  |       every copy of 1/2, 1/4, 1/8, ...)
    \  '. '-' .'  /
     '.  '-~-'  .'        o = the center
        '-~~~-'
```

- Distances measured **from the center** are exactly the radii, the numbers in A. So they contain
  no copy of the pattern.
- This onion fills almost the whole ball, so by any measure it is as big as possible.
- Yet distances measured **from any other point**, or between all pairs of points, contain whole
  intervals and so contain the pattern. The obstruction exists only at the single center point.

**Proposition C: where the real question lives.** If the dimension is more than (d+1)/2, the
distance set is known to contain a whole interval (Mattila–Sjölin, 1999), so it contains the
pattern. The question is therefore **open only for dimensions between d/2 and (d+1)/2**.

It sits next to a known open problem: in that range, must the distance set contain a whole
interval? If yes, our question is answered yes too. A counterexample to our question would instead
give the first known sets of dimension above d/2 whose distance set is fat but contains no interval;
the only known examples of that kind have dimension at most d/2.

**Proposition 3.4: fat at every scale is not enough.** Falconer's theorem shows more than fatness:
the distance set is fat in every interval [0, r]. That alone does not force the pattern. Shrunken
copies of the bad set A, placed at scales 1, 1/8, 1/64, ..., give a set that is fat at every scale
and still avoids every copy of 1/2, 1/4, 1/8, ...

**One bad center is the most one can expect.** For a set of positive volume in dimension ≥ 2, a
classical theorem about averages over spheres (Stein, Bourgain) shows that almost every point sees
all small distances. So the "onion" center of Theorem B is necessarily exceptional. This remark is
not formalized.

## 6. What is new here, and what isn't

**The core is the question, not the theorems.** The main contribution is the question itself:
can distance sets, which have extra structure, escape the dyadic obstruction? The second is
pinning down where the answer is unknown. As far as we could find, nobody had asked this before.
It only became a sensible question in 2026: Falconer's theorem makes these distance sets fat, and
the dyadic result shows that fat alone is not enough.

**The theorems are short.** Each result is a short argument on top of the deep inputs. Theorem A
is Falconer's theorem plus a classical argument from 1920. Proposition 3.4 places shrunken copies
of the bad set A at different scales. Proposition C combines known facts.

**The onion is a standard trick.** Building a set out of spheres whose radii come from a chosen set
A is the obvious way to control the distances from one point. Specialists would not see it as new.
What is new is feeding in OpenAI's bad set A, which was not possible before their result. Its main
property is almost automatic: the distances from the center are exactly the radii. Its real
message is the contrast. The center is bad, every other point sees whole intervals, and in any set
of positive volume almost every point does (Remark 4.7). So the question has to be about distances
between many points, not from a single one. Note also that Theorem B uses only the dyadic result;
Falconer's theorem enters in Theorem A and Proposition C.

**We are not hunting for a counterexample.** The paper proves neither answer. The onion is a
counterexample only to the one-point version of the question. Its full distance set contains a
whole interval, and therefore the pattern. In fact no set of positive volume can be a
counterexample. A real counterexample would have to be thin, with dimension between d/2 and
(d+1)/2, and its distance set would have to be fat but contain no interval. No set like that is
known. Some experts believe that dimension above d/2 always forces an interval; if they are right,
the answer is "yes". So if anything, the expected answer is "yes".

**Is the open range within reach?** Probably not with current tools.
- A "yes" needs more than fatness, even fatness at every scale (Proposition 3.4). The only known
  way to get more is a whole interval. That threshold has not moved below (d+1)/2 since 1999, as
  far as we found, even while the threshold for fatness came down to d/2. OpenAI's Falconer proof
  gives fatness and, as stated, nothing stronger.
- A "no" needs a set of dimension above d/2 whose distances are all under control. The known
  constructions of that kind (Falconer's examples) stop at dimension d/2. Above d/2 the distance
  set is automatically fat, so a counterexample would need a new kind of construction: one whose
  distance set is fat and still avoids the pattern.
- Smaller steps look more realistic: special families of sets (products, self-similar or random
  sets), the "all pins" version in Section 6 of the paper, and other infinite patterns.

## 7. What "formalized in Lean" means

[Lean](https://lean-lang.org) is a programming language in which mathematical proofs can be
written so that a computer checks every single logical step. If Lean accepts a proof, it contains
no gaps, provided the statement was written down correctly.

- Our Lean files prove every lemma, proposition and theorem of the paper. Results that need the
  two OpenAI theorems take them as **explicitly stated hypotheses**. In other words: "if Falconer's theorem
  and the dyadic Erdős result hold, then A and B hold". Lean checks this implication.
- OpenAI also published Lean proofs of the two inputs. We downloaded the relevant ~2,500 files,
  compiled them on a laptop, and had Lean confirm that they prove *exactly* the statements we
  assume. Combined, Theorems A and B are then checked from the ground up.
- The classical Mattila–Sjölin theorem of 1999 (used only in the remark that pins down the open
  window) has a Lean proof too, in a separate project
  ([math-mattila-sjolin](https://github.com/haraldschilly/math-mattila-sjolin)), and Lean confirms
  that it proves exactly the statement we assume.
- Only one input has no Lean proof: OpenAI's claim for ratios other than 1/2. It is used in one
  place, clearly marked (the "general ratio" version of Theorem B).
- Remark 4.7 (one bad center at most) and parts of the open questions cite harmonic-analysis
  results that are not formalized. Nothing else depends on them.

## 8. A short primer: how to read the Lean statements

You don't need to read proofs to check what was proved. You only need to read the **statements**
and the **definitions** they use. Lean checks the rest.

### 8.1 The shape of a theorem

Every Lean theorem looks like this:

```lean
theorem name (hypothesis₁ : ...) (hypothesis₂ : ...) : conclusion := by
  proof ...
```

Read it as: *"Theorem `name`: if hypothesis₁ and hypothesis₂ hold, then the conclusion holds."*
Everything after `:= by` is the proof. Lean checks it, and you can skip it. Arguments in curly braces
`{d : ℕ}` are things Lean infers on its own ("for any d"). Arguments in round brackets are inputs you
must supply, such as a set or a proof of a hypothesis.

### 8.2 Symbols

| Lean | Meaning |
|---|---|
| `∀ x, ...` / `∃ x, ...` | for all x / there exists x |
| `∧`, `¬`, `→` | and, not, implies |
| `ℕ`, `ℝ` | natural numbers, real numbers |
| `EuclideanSpace ℝ (Fin d)` | ordinary d-dimensional space ℝ^d |
| `Set X` | a subset of X |
| `IsCompact E` | E is compact (closed and bounded) |
| `volume E` | Lebesgue measure: length, area or volume of E |
| `dimH E` | Hausdorff (fractal) dimension of E |
| `dist x y` | Euclidean distance between x and y |
| `closedBall 0 1`, `ball 0 1` | unit ball, closed or open |
| `Icc a b` | the closed interval [a, b] |
| `ℝ≥0∞`, `ENNReal.ofReal` | numbers in [0, ∞]; measures can be infinite, so Lean compares them there |
| `∀ᶠ s in 𝓝 0, P s` | "P(s) holds for every s close enough to 0" |

### 8.3 The definitions everything rests on

These four definitions (in `DistanceSimilarity/Statements.lean`) are where the formal and informal
mathematics meet, so they are worth reading carefully:

```lean
def distSet (E : Set X) : Set ℝ :=
  {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}
```
The distance set Δ(E): all numbers r that are the distance between two points of E.

```lean
def pinnedDistSet (p : X) (E : Set X) : Set ℝ :=
  {r : ℝ | ∃ y ∈ E, dist p y = r}
```
The pinned distance set Δ_p(E): all distances from the fixed point p to points of E.

```lean
def ContainsDyadicCopy (P : Set ℝ) : Prop :=
  ∃ x s : ℝ, s ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → x + s * dyadicPoint n ∈ P
```
"P contains a shifted and scaled copy of 1/2, 1/4, 1/8, …": there are a start x and a nonzero
scale s such that x + s·2⁻ⁿ lies in P for every n ≥ 1. (`dyadicPoint n` is defined as 2⁻ⁿ.)

```lean
def FalconerStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E →
      0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}
```
Falconer's theorem: in every dimension d ≥ 2, every compact E with dimension > d/2 has a distance
set of positive length. This text is **copied character for character** from OpenAI's file
`lean/ComparatorChallenges/FalconerAllDimensions.lean`. The same holds for
`DyadicAvoidanceStatement` and `DyadicAvoidance.lean`.

### 8.4 Reading Theorem A

```lean
theorem finite_pattern_distSet (hFal : FalconerStatement) {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ distSet E}
```

Line by line:
- `(hFal : FalconerStatement)`: assuming Falconer's theorem,
- `{d : ℕ} (hd : 2 ≤ d)`: for any dimension d ≥ 2,
- `{E : ...} (hE : IsCompact E) (hdim : d/2 < dimH E)`: and any compact set E in ℝ^d of
  dimension greater than d/2,
- `(F : Finset ℝ)`: and any finite set of numbers F,
- conclusion: for every scale s close enough to 0, the set of starting points x such that
  x + s·a is a distance of E for every a in F has positive length.

That is exactly Theorem A of the paper.

### 8.5 Reading Theorem B

```lean
theorem pinned_dyadic_obstruction (hDy : DyadicAvoidanceStatement) {d : ℕ} (hd : 1 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → (∃ a b : ℝ, a < b ∧ Icc a b ⊆ pinnedDistSet p K) ∧
        ContainsDyadicCopy (pinnedDistSet p K))
```

"Assuming the dyadic Erdős result, for every dimension d ≥ 1 and every η between 0 and 1, there
is a set K such that:"
1. `IsCompact K ∧ K ⊆ closedBall 0 1 ∧ 0 ∈ K`: K is compact, inside the unit ball, and contains
   the center;
2. `(1 - η)^d · volume(ball) ≤ volume K`: K fills at least a fraction (1−η)^d of the ball;
3. `0 < volume K ∧ dimH K = d`: K has positive volume and full dimension;
4. `¬ ContainsDyadicCopy (pinnedDistSet 0 K)`: the distances **from the center** contain no
   copy of 1/2, 1/4, 1/8, … (the "onion" property);
5. `ContainsDyadicCopy (distSet K)`: but **all** distances together do contain one;
6. `2 ≤ d → ∀ p, p ≠ 0 → ...`: and in dimension ≥ 2, the distances from **any other point** p
   contain a whole interval `[a, b]` with `a < b`, and therefore a copy too.

### 8.6 Where each paper statement lives

| Paper | Lean name (namespace `DistanceSimilarity`) | File |
|---|---|---|
| Theorems 2.1, 2.2 (the inputs, proved by OpenAI) | `falconer_holds`, `dyadicAvoidance_holds` | `verify/Verify/` |
| Theorem 2.4 (Mattila–Sjölin, proved in math-mattila-sjolin) | `mattilaSjolin_holds` | `verify/Verify/` |
| Lemma 3.1, Theorem A, Proposition 3.2 | `eventually_volume_pattern_pos`, `finite_pattern_distSet`, `exists_finite_pattern_distSet`, `volume_pattern_pairs_pos` | `FinitePatterns.lean` |
| Lemma 3.3 (distances at every scale) | `volume_distSet_inter_Icc_pos` | `FinitePatterns.lean` |
| Proposition 3.4 (fat at every scale is not enough) | `exists_dyadicFree_pos_every_scale` | `Scales.lean` |
| Lemmas 4.1–4.5 | `not_containsGeomCopy_insert_zero`, `volume_norm_preimage_ge`, `dimH_eq_of_volume_pos`, `exists_Ico_subset_distSet`, `Icc_subset_pinnedDistSet` | `Patterns.lean`, `RadialVolume.lean`, `PinnedObstruction.lean` |
| Theorem B / Theorem 4.6 (any ratio q) | `pinned_dyadic_obstruction` / `pinned_geometric_obstruction` | `PinnedObstruction.lean` |
| Proposition C | `distSet_containsAffineCopy_of_interior`, `distSet_containsAffineCopy_of_volume_pos`, `counterexample_properties` | `Window.lean` |
| Remark 5.1 (Mattila–Sjölin window) | `window_of_mattilaSjolin` (unconditional version in `verify/`) | `Window.lean` |
| Lemma 6.1 (spheres) | `not_containsGeomCopy_pinnedDistSet_iff` | `Window.lean` |

### 8.7 How do we know nothing is hidden?

- **No unfinished proofs.** Lean has an escape hatch, `sorry`, that skips a proof. The build
  reports every use of it, and the axiom check below would show it as `sorryAx`. Our files contain
  none.
- **No extra assumptions.** `#print axioms` lists everything a theorem ultimately relies on. For
  every result here it prints only `propext`, `Classical.choice` and `Quot.sound`, the three
  standard axioms of ordinary mathematics in Lean. Run `lake env lean verify/Axioms.lean` to see
  it yourself.
- **The OpenAI inputs really are proved.** `verify/Verify/Falconer.lean` contains
  ```lean
  theorem falconer_holds : FalconerStatement := OAI.Falconer.falconer_distance_conjecture
  ```
  Lean accepts this line only if OpenAI's theorem has *exactly* the type `FalconerStatement`. The
  same holds for the dyadic input and for the Mattila–Sjölin theorem
  (`verify/Verify/MattilaSjolin.lean`). `verify/Verify/Unconditional.lean` then restates
  Theorems A and B (and Propositions 3.2, 3.4, C(iii), Lemma 3.3 and Remark 5.1) without
  hypotheses.
- **Independent replay.** Lean's `leanchecker --fresh` re-checks the entire chain from scratch in
  the kernel (Mathlib, OpenAI's files, the Mattila–Sjölin proof and ours).
- **What remains for a human:** check that the definitions in 8.3 and the statements in 8.4–8.5
  say what the paper says. That is the reason this primer exists.

## 9. Caveats

- The two inputs were produced by an AI model at OpenAI and have **not yet been reviewed** by
  human experts. Lean proofs are strong evidence, but a proof only shows the statement *as written
  in Lean*. Experts should still compare the Lean statement with the intended mathematics.
- This paper and its Lean code were written with substantial help from Claude (Anthropic). Harald
  Schilly is responsible for the content.
- The new results are modest: short arguments on top of deep inputs. Section 6 says what is new
  and what is not.
