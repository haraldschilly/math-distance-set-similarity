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
pattern. The question is therefore **open only for dimensions between d/2 and (d+1)/2**. A
counterexample in that range would also give distance sets that are fat but contain no interval.
We could not find in the literature whether such sets exist in that range.

## 6. What "formalized in Lean" means

[Lean](https://lean-lang.org) is a programming language in which mathematical proofs can be
written so that a computer checks every single logical step. If Lean accepts a proof, it contains
no gaps, provided the statement was written down correctly.

- Our Lean files prove Theorems A and B completely, **assuming** the two OpenAI results as
  explicitly stated hypotheses. In other words: "if Falconer's theorem and the dyadic Erdős result
  hold, then A and B hold". Lean checks this implication.
- OpenAI also published Lean proofs of the two inputs. We downloaded the relevant ~2,500 files,
  compiled them on a laptop, and had Lean confirm that they prove *exactly* the statements we
  assume. Combined, Theorems A and B are then checked from the ground up.

## 7. Caveats

- The two inputs were produced by an AI model at OpenAI and have **not yet been reviewed** by
  human experts. Lean proofs are strong evidence, but a proof only shows the statement *as written
  in Lean*. Experts should still compare the Lean statement with the intended mathematics.
- This paper and its Lean code were written with substantial help from Claude (Anthropic). Harald
  Schilly is responsible for the content.
- The new results are modest: short arguments on top of deep inputs. The main contribution is the
  question, the contrast between the center and every other point, and identifying exactly where
  the problem is open.
