# Complete Characterization of Neusis Constructibility: A Lean 4 Proof Settling a 400-Year-Old Problem Since Viète (1593)

A complete, axiom-clean Lean 4 formalization resolving the **Neusis Constructibility Problem** for planar constructions using a compass, straightedge, and strictly point-verging unit-mark neusis (twice-notched straightedge with mark distance `1`), starting from `(0, 0)` and `(1, 0)`.

In *Supplementum geometriae* (1593), François Viète adopted the neusis as a geometric postulate and showed that it solves all cubic and quartic problems. After Gauss (1801) and Wantzel (1837) characterized compass-and-straightedge constructibility, the analogous question for compass and marked ruler remained open: Baragar (2002) established the degree-`≤ 6` tower necessity bound (ruling out the regular 23-gon), and Benjamin and Snyder (2014) constructed the regular 11-gon, leaving the complete field characterization, general quintics, and regular polygons such as the 25-, 31-, 41-, 61-, 101-, and 125-gons open. This repository formally proves that Baragar's degree-`≤ 6` condition is both necessary and sufficient.

## Main Theorems

All three main results are proved without `sorry` or custom axioms in [`NeusisLean/MainTheorems.lean`](NeusisLean/MainTheorems.lean):

1. **Complete Field Characterization**
   - `Neusis.neusisReal_iff_inDeg6Tower`: A real number `x : ℝ` is neusis-constructible if and only if it lies in a real tower of field extensions `ℚ = K₀ ≤ K₁ ≤ … ≤ Kᵣ ⊆ ℝ` with `[K_{i+1} : K_i] ≤ 6` at every step.
   - `Neusis.neusisComplex_iff`: A complex number `z : ℂ` is neusis-constructible if and only if both `z.re` and `z.im` lie in real degree-`≤ 6` towers over `ℚ`.

2. **Regular $n$-gon Characterization**
   - `Neusis.regularPolygonConstructible_iff`: For every `n ≥ 3`, the regular `n`-gon is neusis-constructible if and only if every prime divisor of Euler's totient `φ(n)` is at most `5` (equivalently, `φ(n) = 2^a 3^b 5^c`). In particular, all previously open cases (`n = 25, 31, 41, 61, 101, 125, …`) are constructible.

3. **Universal Solvability of General Quintics and Sextics**
   - `Neusis.neusisReal_of_real_sextic`: Every real root of every nonzero polynomial of degree `≤ 6` over `NeusisSubfield` is neusis-constructible.
   - `Neusis.neusisComplex_of_real_quintic`: Every complex root of every nonzero polynomial of degree `≤ 5` over `NeusisSubfield` is neusis-constructible.

## Module Structure

| File | Lines | Contents |
|---|---:|---|
| [`NeusisLean/Defs.lean`](NeusisLean/Defs.lean) | 120 | Geometric definitions of points, lines, circles, point-verging unit-mark `NeusisSolutions`, `NeusisPoint`, `NeusisReal`, `NeusisComplex`, `InDeg6Tower`, and `RegularPolygonConstructible`. |
| [`NeusisLean/BasicField.lean`](NeusisLean/BasicField.lean) | 289 | Compass-and-straightedge field operations (`NeusisSubfield : Subfield ℝ`), closure under square roots of nonnegative reals, and real quadratics. |
| [`NeusisLean/BaragarNecessity.lean`](NeusisLean/BaragarNecessity.lean) | 1,141 | Formalization of Baragar's necessity theorem (2002): every neusis-constructible point has coordinates in a real degree-`≤ 6` tower over `ℚ`. |
| [`NeusisLean/CubicQuartic.lean`](NeusisLean/CubicQuartic.lean) | 801 | Scaling to arbitrary constructible mark lengths (`neusis_scaled`), angle trisection, real cube roots, and all real roots of real cubics and quartics. |
| [`NeusisLean/CircleCircleNeusis.lean`](NeusisLean/CircleCircleNeusis.lean) | 591 | Exact right-isosceles circle–circle neusis solving `z^6 + A₄ z^4 + A₂ z^2 + A₁ z + A₀ = 0` on the explicit open region `CircleCircleValid`, plus angle quintisection and the regular 25-gon. |
| [`NeusisLean/QuinticSextic.lean`](NeusisLean/QuinticSextic.lean) | 2,105 | Openness of `CircleCircleValid`, three rational witnesses covering all real-root signatures of degrees 5 and 6, Lagrange interpolation + rational approximation + cubic `S₃ = 0` reduction, proving `neusisReal_of_poly_le6`. |
| [`NeusisLean/MainTheorems.lean`](NeusisLean/MainTheorems.lean) | 1,192 | The three main theorems (`neusisReal_iff_inDeg6Tower`, `neusisComplex_iff`, `regularPolygonConstructible_iff`, `neusisReal_of_real_sextic`, `neusisComplex_of_real_quintic`). |
| [`NeusisLean.lean`](NeusisLean.lean) | 7 | Root library module importing all submodules. |

## Building and Verifying

Requires Lean `v4.36.0` (specified in [`lean-toolchain`](lean-toolchain)) and Mathlib `v4.36.0` (pinned in [`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json)):

```bash
lake exe cache get
lake build
```
