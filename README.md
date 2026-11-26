# Complete Characterization of Neusis Constructibility: A Lean 4 Proof Formalizing a 400-Year-Old Problem Since Viète (1593)

[![Lean 4 CI](https://github.com/adrianvalentim/neusis-constructibility-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/adrianvalentim/neusis-constructibility-lean/actions/workflows/lean_action_ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A complete, axiom-clean Lean 4 formalization resolving the **Neusis Constructibility Problem** for planar constructions using a compass, straightedge, and strictly point-verging unit-mark neusis (a twice-notched straightedge with mark distance `1`), starting from `(0, 0)` and `(1, 0)`.

In *Supplementum geometriae* (1593), François Viète adopted the neusis as an explicit geometric postulate and proved that it solves all cubic and quartic problems. After Gauss (1801) and Wantzel (1837) characterized compass-and-straightedge constructibility, the analogous characterization for compass and marked ruler remained open for centuries: Arthur Baragar (2002) proved the degree-`≤ 6` tower necessity bound (excluding the regular 23-gon), and Elliot Benjamin and Chip Snyder (2014) constructed the regular 11-gon, leaving the full field characterization, general quintics, and regular polygons such as the 25-, 31-, 41-, 61-, 101-, and 125-gons open. This repository formally proves in Lean 4 that Baragar's degree-`≤ 6` tower condition is both necessary and sufficient.

## Main Theorems

All main results are proved in [`NeusisLean/MainTheorems.lean`](NeusisLean/MainTheorems.lean) with zero `sorry`s and only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **Complete Field Characterization**
   - `Neusis.neusisReal_iff_inDeg6Tower`: A real number `x : ℝ` is neusis-constructible if and only if it lies in a real tower of field extensions `ℚ = K₀ ≤ K₁ ≤ … ≤ Kᵣ ⊆ ℝ` with `[K_{i+1} : K_i] ≤ 6` at every step.
   - `Neusis.neusisComplex_iff`: A complex number `z : ℂ` is neusis-constructible if and only if both `z.re` and `z.im` lie in real degree-`≤ 6` towers over `ℚ`.

2. **Regular $n$-gon Characterization**
   - `Neusis.regularPolygonConstructible_iff`: For every `n ≥ 3`, the regular `n`-gon is neusis-constructible if and only if every prime divisor of Euler's totient `φ(n)` is at most `5` (equivalently, `φ(n) = 2^a 3^b 5^c`). In particular, the regular 25-, 31-, 41-, 61-, 101-, and 125-gons are all neusis-constructible.

3. **Universal Solvability of General Quintics and Sextics**
   - `Neusis.neusisReal_of_real_sextic`: Every real root of every nonzero polynomial of degree `≤ 6` over `NeusisSubfield` is neusis-constructible.
   - `Neusis.neusisComplex_of_real_quintic`: Every complex root of every nonzero polynomial of degree `≤ 5` over `NeusisSubfield` is neusis-constructible.

## Auditing the Definitions and Axioms

When reviewing a formal proof, the two things to check are the **formal definitions** and the **axiom footprint**:

- **Geometric model ([`NeusisLean/Defs.lean`](NeusisLean/Defs.lean), 120 lines):**
  - Base points: `(0, 0)` and `(1, 0)` in `ℝ × ℝ`.
  - Allowed operations (`NeusisPoint`): line–line, line–circle, and circle–circle intersections (with standard non-degeneracy: non-parallel lines, distinct centers), plus **point-verging unit-mark neusis** (`neusis_left`, `neusis_right`): given a constructed pole `P` and two constructed curves `γ₁, γ₂` (each a line or a circle), any `(X, Y)` with `X ∈ γ₁`, `Y ∈ γ₂`, `P, X, Y` collinear, and `distSq X Y = 1`, provided the solution set `NeusisSolutions P γ₁ γ₂` is **finite** (intrinsically excluding degenerate overlapping curves or concentric unit-gap circles).
  - Target notions: `NeusisReal x := NeusisPoint (x, 0)`, `NeusisComplex z := NeusisPoint (z.re, z.im)`, and `RegularPolygonConstructible n := NeusisComplex (Complex.exp (2 * Real.pi * Complex.I / n))`.
- **Axiom check:** Run the command below after building to confirm zero `sorry`s, zero custom axioms, and no `native_decide` / `Lean.trustCompiler`:

```bash
lake env lean --stdin <<'EOF'
import NeusisLean.MainTheorems
#print axioms Neusis.neusisReal_iff_inDeg6Tower
#print axioms Neusis.neusisComplex_iff
#print axioms Neusis.regularPolygonConstructible_iff
#print axioms Neusis.neusisReal_of_real_sextic
#print axioms Neusis.neusisComplex_of_real_quintic
EOF
```

Expected output:

```text
'Neusis.neusisReal_iff_inDeg6Tower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neusis.neusisComplex_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neusis.regularPolygonConstructible_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neusis.neusisReal_of_real_sextic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neusis.neusisComplex_of_real_quintic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof Overview

1. **Necessity (Baragar 2002):** Every compass, straightedge, and non-degenerate point-verging neusis step over a subfield `K ⊆ ℝ` produces coordinates satisfying nonzero polynomials of degree at most `6` over `K` ([`BaragarNecessity.lean`](NeusisLean/BaragarNecessity.lean)).
2. **Low-degree closure:** Compass and straightedge give a subfield closed under real square roots ([`BasicField.lean`](NeusisLean/BasicField.lean)); scaling to arbitrary constructible mark lengths, angle trisection, and real cube roots close `NeusisSubfield` under all real roots of real cubics and quartics ([`CubicQuartic.lean`](NeusisLean/CubicQuartic.lean)).
3. **Right-isosceles circle–circle neusis:** A pole at `(0, 0)` with two circles centered at `(-1/2, 1/2)` and `(1/2, 1/2)` solves `z^6 + A₄ z^4 + A₂ z^2 + A₁ z + A₀ = 0` on an explicit open region `CircleCircleValid ⊆ ℝ⁴` controlled by the scale cubic `5 t^3 + 3 A₄ t^2 + A₂ t - A₀ = 0`, immediately yielding one-neusis angle quintisection and the regular 25-gon ([`CircleCircleNeusis.lean`](NeusisLean/CircleCircleNeusis.lean)).
4. **Universal degree-5 and degree-6 sufficiency:** `CircleCircleValid` is proved open around any simple witness; three exact rational witnesses (`Q₅`, `Q₃`, `Q₁`) cover all six real-root signatures of degrees 5 and 6; conjugation-invariant Lagrange interpolation, rational approximation, and a real cubic reduction `S₃ = 0` transport any irreducible degree-5 or degree-6 real polynomial over `NeusisSubfield` into `CircleCircleValid` ([`QuinticSextic.lean`](NeusisLean/QuinticSextic.lean)), completing all three main theorems via Galois descent for cyclotomic fields ([`MainTheorems.lean`](NeusisLean/MainTheorems.lean)).

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

## References & Prior Work

- F. Viète, *Supplementum geometriae* (1593).
- A. Baragar, "Constructions using a compass and twice-notched straightedge", *Amer. Math. Monthly* **109** (2002), no. 2, 151–164, [doi:10.1080/00029890.2002.11919848](https://doi.org/10.1080/00029890.2002.11919848).
- E. Benjamin and C. Snyder, "On the construction of the regular hendecagon by marked ruler and compass", *Math. Proc. Cambridge Philos. Soc.* **156** (2014), no. 3, 409–424, [doi:10.1017/S0305004113000753](https://doi.org/10.1017/S0305004113000753).
- J. Shipman, "General quintics and sextics with marked ruler and compass", Pith preprint `2026.000007` (24 October 2026), [doi:10.67347/pith.preprint.2026.000007](https://doi.org/10.67347/pith.preprint.2026.000007) (unrefereed informal preprint, no formal proof).

**Provenance & AI assistance:** This formalization was created with the help of **Gemini 4 Neon (high) on Antigravity**. Shipman's October 2026 unrefereed preprint proposed resolving Conway's conjecture and the general quintic/sextic problem via local-to-global openness on circle–circle neusis sextics, rational Tschirnhaus transport, and a point-verging scale cubic. During development of this Lean 4 formalization, two high-level web-search summaries referencing that strategy and the "scale cubic" clue were seen (Shipman's manuscript itself was never downloaded or read). All explicit geometric parameterizations, algebraic identities, rational witnesses, transport proofs, Baragar's necessity proof, and all 6,246 lines of Lean 4 code in this repository were derived and machine-verified independently from scratch.

## License

Released under the [Apache License 2.0](LICENSE).
