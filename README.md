Verified computation of the Mandelbrot Böttcher series
======================================================

[![build](https://github.com/girving/bottcher/actions/workflows/lean.yml/badge.svg)](https://github.com/girving/bottcher/actions/workflows/lean.yml)

Verified computation of the [Böttcher series](https://en.wikipedia.org/wiki/B%C3%B6ttcher%27s_equation) of the Mandelbrot set: the power series around infinity of the analytic homeomorphism from the complement of the closed unit disk to the complement of the Mandelbrot set. This repo builds on top of three other Lean repositories:

1. [ray](https://github.com/girving/ray): Definitions and basic results about complex dynamics, including Böttcher coordinates and the connectivity of the Mandelbrot set.
2. [interval](https://github.com/girving/interval): Conservative interval arithmetic using software floating point.
3. [series](https://github.com/girving/series): Conservative power series arithmetic.

All of which of course build on top of the wonderful [mathlib](https://github.com/leanprover-community/mathlib4) base!

## Building

1. Install [`elan`](https://github.com/leanprover/elan) (`brew install elan-init` on Mac)
2. `lake build`
