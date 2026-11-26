# Neusis constructibility proof audit

Reviewed on 26 November 2026. The source under review is commit `7a4c618ded9df3d6ee558004b356f791fbca2b91`. All source references below refer to that proof. The review branch adds verification material.

## Mathematical verdict

The field and polygon theorems address the modern problem of constructibility by compass, straightedge, and a ruler with two fixed marks one unit apart that must pass through a constructed pole. Both marks may lie on constructed circles. The substantive advance over the known necessary condition is the converse. **Every real number in a finite tower of real extensions of degree at most six per step is reachable by these geometric operations.** In particular, this answers the general field problem posed by Snyder for this instrument. [Snyder’s statement and rules, slides 3–4](https://www.maine-quebec.mat.ulaval.ca/14/Construction_Q_M_slides.pdf#page=3) · [Baragar, 2002](https://doi.org/10.1080/00029890.2002.11919848)

| Question | What the source proves | Where to inspect it |
|---|---|---|
| Which real and complex numbers? | A real number belongs to the geometric field exactly when it lies in such a tower over the rationals. For a complex point the criterion applies to both coordinates. Two witnessing towers can be combined. | [Field equivalences](NeusisLean/MainTheorems.lean#L63), [combining towers](NeusisLean/BaragarNecessity.lean#L21) |
| Which polygons? | For each integer $n\ge3$, the regular $n$-gon is constructible exactly when all prime factors of Euler’s totient $\varphi(n)$ are 2, 3 or 5. The formal target is the point $e^{2\pi i/n}$. Its powers give every vertex by field arithmetic. | [Polygon definition](NeusisLean/Defs.lean#L115), [polygon equivalence](NeusisLean/MainTheorems.lean#L1184) |
| Which polynomial roots? | For a nonzero polynomial over the field of constructible **real** coefficients, every real root through degree six and every complex root through degree five is constructible. Repeated roots and reducible inputs are included. | [Real-root theorem](NeusisLean/MainTheorems.lean#L78), [complex-root theorem](NeusisLean/MainTheorems.lean#L275) |
| Can every quintic be solved in one ruler placement? | The public theorems establish a finite construction for each root. They impose no bound of one placement and give no uniform construction algorithm or move count. The proof uses preparatory constructions, including real cubics. The direct 25-gon argument is a separate special case. | [Geometric induction](NeusisLean/Defs.lean#L59), [cubic parameter](NeusisLean/QuinticSextic.lean#L1922), [25-gon](NeusisLean/CircleCircleNeusis.lean#L517) |

The coefficient restriction matters if the problem is phrased with arbitrary real numbers supplied as additional starting data. The public declarations fix the starting field over the rationals. A theorem parameterized by an arbitrary input field or a single uniform recipe would require a separate statement.

### Does Lean model the instrument faithfully?

The only starting points are $(0,0)$ and $(1,0)$. Each line and circle uses two already constructed defining points. Ordinary intersections have the expected nondegeneracy conditions. A marked-ruler move requires incidence of the two marks, collinearity with the pole, and squared distance exactly one. It must exhibit a solution and prove that the whole set of admissible placements is finite. Either mark of any such placement is permitted. This makes the usual finite-choice convention explicit. For example, concentric circles of radii one and two with the pole at their common center would otherwise let the user choose any angle. Rescaling to another positive constructible mark length is proved by similarity. [Definitions](NeusisLean/Defs.lean#L28) · [Rescaling](NeusisLean/CubicQuartic.lean#L69) · [Benjamin and Snyder’s distinction between full and restricted verging, §2](https://doi.org/10.1216/RMJ-2016-46-3-749)

The field of constructible reals has the geometric predicate as its carrier. Closure under the field operations is proved. The tower starts at the smallest subfield of the reals and adjoins a root of a **nonzero** polynomial of bounded degree at each step. The smallest subfield is the rationals. The minimal polynomial divides any annihilating polynomial, and conversely each finite real field extension is separable and has a primitive element. These facts identify the inductive definition with the ordinary field-degree formulation. [Geometric field](NeusisLean/BasicField.lean#L226) · [Tower definition](NeusisLean/Defs.lean#L100) · [Primitive element theorem in the pinned mathlib](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/FieldTheory/PrimitiveElement.lean#L208)

### Where the converse comes from

1. For two circles in a specified configuration, the proof works backwards from a real root of a reduced sextic to a legal placement. It proves positivity of both radii, proves finiteness, treats the exceptional signed distances separately and recovers the root from the coordinates of the marks. This establishes geometric realizability for an open neighborhood of each simple witness used later. [Circle construction and recovery](NeusisLean/CircleCircleNeusis.lean#L190) · [Neighborhood theorem](NeusisLean/QuinticSextic.lean#L299)
2. Three rational sample quintics have five, three and one real root. Multiplication by $X$ yields sextics with six, four and two real roots. These exhaust the possible signatures of separable quintics and sextics having a real root. I independently checked all six real-root counts and the absence of repeated roots by exact polynomial arithmetic. In order of decreasing real-root count, the derivatives of the scale cubic at the three chosen parameters are $-13/72,-1/5,1/9$, all nonzero. [Exact samples](NeusisLean/QuinticSextic.lean#L370) · [Coverage by signature](NeusisLean/QuinticSextic.lean#L958)
3. For an irreducible input with a chosen real root, interpolation matches its conjugate roots to a sample of the same signature. Approximation chooses **rational polynomial coefficients** in an open neighborhood. An exact root of a nonzero polynomial of degree at most three then enforces the third-power-sum equation. Centering enforces the first-power-sum equation. The resulting coefficients and the correcting parameter are proved constructible. The approximation selects the data for an exact construction. [Interpolation](NeusisLean/QuinticSextic.lean#L1027) · [Rational perturbation](NeusisLean/QuinticSextic.lean#L1575) · [Coefficient descent](NeusisLean/QuinticSextic.lean#L1878)
4. If the input root is $a$, the two circles construct $Q(a)$ for a polynomial $Q$ of degree strictly below the input degree. The construction separates two conjugate images, so $Q(X)-Q(a)$ is a **nonzero** polynomial of lower degree over the geometric field vanishing at $a$. This contradicts irreducibility. Factoring reducible inputs finishes the proof, and induction up a tower gives sufficiency. For polygons, the proof uses the abelian cyclotomic Galois group and descends through real fixed fields with prime-degree steps. [Irreducibility contradiction](NeusisLean/QuinticSextic.lean#L2024) · [Tower induction](NeusisLean/MainTheorems.lean#L35) · [Polygon sufficiency](NeusisLean/MainTheorems.lean#L987)

## Verification record

I built the original GitHub sources in a fresh checkout on arm64 macOS. Lean was 4.36.0, release commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Mathlib was `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. I compared the checked-out Git revision of every one of the nine dependencies with the manifest. Lake obtained mathlib’s dependency cache, then compiled each of the seven NeusisLean modules and the root module from source. It exited successfully and reported 18,266 build jobs including dependencies.

Lean reported exactly `propext`, `Classical.choice`, and `Quot.sound` on each of ten declarations, including all five advertised theorems, the central polynomial theorem, the geometric two-circle solver and the independent 25-gon proof. A separate implementation of the Lean type checker, **Nanoda 0.4.17**, read the export of those declarations and their transitive dependencies. Its configuration rejects any unlisted axiom, including `sorryAx` and `Lean.trustCompiler`. Its final result was `Checked 62126 declarations with no errors`. The SHA-256 digest of the 652,279,164-byte export in this run was `269e99f80aaccd28e2b4b411cef9f29f3b2eee33bc0ea3539ce55e76b3164d39`. The inputs and verification procedure below allow the check to be repeated without distributing that file. [Checker configuration](audit/nanoda.json)

The original build emitted a module-system migration warning, deprecation and simplifier warnings in `QuinticSextic.lean`, and a `ring_nf` suggestion at line 309 of `CircleCircleNeusis.lean`. The affected declaration passed independent type checking. The concrete audit file also checks the six positive polygon cases from the README, the negative 23-gon case, the fifth root of 2, and an arbitrary complex root of the real polynomial $X^5-X-1$. [Reproducible theorem checks](audit/Check.lean)

Run from the review branch with the pinned toolchain. Only NeusisLean sources in the audited commit are used as proof input to the independent checker.

```bash
set -o pipefail
lake exe cache get
lake build
lake env lean audit/Check.lean
sed -n 's/^#print axioms //p' audit/Check.lean |
  xargs lake env leanexport NeusisLean.MainTheorems -- |
  lake env nanoda_bin audit/nanoda.json
```

## A concrete test from the literature

Benjamin and Snyder ended their 2016 paper by asking whether the real fifth root of 2 can be constructed. The accompanying Lean check specializes the general theorem to the actual positive real $2^{1/5}$. I also obtained a direct reduction using only the earlier two-circle theorem. It bypasses the interpolation and irreducibility arguments entirely. [2016 paper](https://doi.org/10.1216/RMJ-2016-46-3-749) · [Lean check](audit/Check.lean) · [Two-circle theorem](NeusisLean/CircleCircleNeusis.lean#L190)

Write $x=\sqrt[5]{2}$ and $y=-x+x^2+x^3-x^4$. Exact elimination gives

$$
g(y)=y^5-20y^3+110y+6=0,\qquad
x=\frac{3y^4+79y^3-137y^2-911y+880}{809}.
$$

The sextic $y g(y)$ has coefficients $(A_4,A_2,A_1,A_0)=(-20,110,6,0)$ in the repository’s normal form. For the scale parameter choose $t=6-\sqrt{14}$, which lies between two and three and satisfies $5t^2-60t+110=0$. The expression $M=110-40t+3t^2=44-4t$ exceeds 32. Thus $4M^2-36/t>0$, $W=\sqrt{2M+\sqrt{4M^2-36/t}}>8$, and $U=W+20-t>0$. Both circle radii are positive because $20-t>6/(\sqrt t\,W)$. These are the inequalities in `CircleCircleValid`. All the auxiliary data in this example use only field operations and square roots. A Sturm count gives exactly one real root of $g$, lying between $-1$ and $0$. Choose it from the finite two-circle placements and apply the displayed rational polynomial to recover $x$. [Parameter inequalities](NeusisLean/CircleCircleNeusis.lean#L32)

For an actual unit-mark layout, put $h=\sqrt{t/U}$, $S=W/U$ and $D=6/(U\sqrt t\,W)$. Use the origin as pole. Place the first and second circle centers at $(-1,1)/(4h)$ and $(1,1)/(4h)$, respectively. Their radii are $\sqrt{(1-S-D)/2}/(2h)$ and $\sqrt{(1-S+D)/2}/(2h)$. For marks $X$ and $Y$ on the first and second circles, the unit-scale readout is $y=\sqrt t\,(\|Y\|^2-\|X\|^2)$. Use a placement with negative readout. The geometric identity and Sturm count above ensure it gives the desired root. [Original placement and readout](NeusisLean/CircleCircleNeusis.lean#L357)

The following exact SymPy calculation reproduces the elimination, inverse, and root count.

```python
from sympy import Poly, oo, rem, resultant, symbols

x, y = symbols("x y")
q = -x + x**2 + x**3 - x**4
g = y**5 - 20*y**3 + 110*y + 6
r = (3*y**4 + 79*y**3 - 137*y**2 - 911*y + 880) / 809
assert resultant(x**5 - 2, y - q, x) == g
assert rem(r.subs(y, q) - x, x**5 - 2, x) == 0
assert Poly(g, y).count_roots(-oo, oo) == Poly(g, y).count_roots(-1, 0) == 1
```

## History and priority

Viète’s *Supplementum geometriae* appeared in 1593. His postulate and constructions document the sixteenth-century setting, including trisection and the heptagon. I found no evidence that he posed today’s field or polygon classification in that form. The modern general question is explicitly documented by Snyder, alongside a distinct restricted problem that excludes circle–circle verging. Benjamin and Snyder proved the 11-gon result in 2014 using the restricted moves. [Viète’s postulate in the collected works, p. 240](https://www.e-rara.ch/download/pdf/2759790.pdf) · [Hartshorne’s reading of Viète](https://math.berkeley.edu/~robin/Viete/construction.html) · [Snyder’s slides](https://www.maine-quebec.mat.ulaval.ca/14/Construction_Q_M_slides.pdf) · [2014 paper](https://doi.org/10.1017/S0305004113000753)

On 20 September 2026, a public post reproduced a message attributed to Joe Shipman announcing a general-quintic construction. The account mentions a Tschirnhaus transformation and a “double neusis.” The post predates this repository commit. I could verify the public repost, but could not retrieve the underlying FOM message or a detailed manuscript establishing which geometric moves it permits. The announcement makes no explicit general real-sextic or full field-classification claim. Its possible overlap is material to quintic and polygon priority. The correctness review therefore gives no priority determination. [Dated public repost](https://news.ycombinator.com/item?id=49774271) · [FOM moderator’s archive information](https://mathweb.ucsd.edu/~sbuss/FOM/)
