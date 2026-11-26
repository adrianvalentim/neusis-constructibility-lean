import NeusisLean.CubicQuartic

/-!
# Right-Isosceles Circle-Circle Neusis Construction

We formalize our exact point-verging circle-circle neusis construction for real roots of
sextics of the form
  `z^6 + A₄ z^4 + A₂ z^2 + A₁ z + A₀ = 0`
whose parameters `(A₄, A₂, A₁, A₀)` lie in the explicit open validity region `CircleCircleValid`.

Configuration (with mark length `2 h > 0`, reduced to unit mark by `neusis_scaled`):
- Pole `P = (0, 0)`.
- Circle 1: center `C₁ = (-1/2, 1/2)`, squared radius `r₁² = (1 - S - D)/2 > 0`.
- Circle 2: center `C₂ = (1/2, 1/2)`, squared radius `r₂² = (1 - S + D)/2 > 0`.

Crucially, **every** real root `z` of the sextic produces genuine real circles and real
incidence points `(X, Y)` (no extraneous real roots!), and `z` is recovered explicitly via
  `z = L * ((Y.1^2 + Y.2^2) - (X.1^2 + X.2^2)) / (4 * h)`.

As an immediate explicit corollary, we prove **angle quintisection** (`z^5 - 5 z^3 + 5 z = c`
for all `|c| < 2`) using only square roots and **one** circle-circle neusis, and deduce the
neusis-constructibility of the regular 25-gon.
-/

namespace Neusis

open Polynomial

/-- The explicit open parameter region where our right-isosceles circle-circle neusis
produces two genuine real circles (`r₁² > 0`, `r₂² > 0`) and real scaling (`U > 0`, `t_s > 0`)
solving `z^6 + A₄ z^4 + A₂ z^2 + A₁ z + A₀ = 0`. -/
def CircleCircleValid (A₄ A₂ A₁ A₀ : ℝ) : Prop :=
  ∃ t_s : ℝ,
    0 < t_s ∧
    5 * t_s ^ 3 + 3 * A₄ * t_s ^ 2 + A₂ * t_s - A₀ = 0 ∧
    A₄ + t_s < 0 ∧
    0 < 4 * (A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2) ^ 2 - A₁ ^ 2 / t_s ∧
    0 < 2 * (A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2) +
        Real.sqrt (4 * (A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2) ^ 2 - A₁ ^ 2 / t_s) ∧
    let W := Real.sqrt (2 * (A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2) +
        Real.sqrt (4 * (A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2) ^ 2 - A₁ ^ 2 / t_s))
    let U := W - A₄ - t_s
    0 < U ∧
    let S := W / U
    let D := A₁ / (U * Real.sqrt t_s * W)
    0 < (1 - S - D) / 2 ∧
    0 < (1 - S + D) / 2

/-- Helper: a monic degree-6 real polynomial has finitely many real roots. -/
private lemma poly6_monic_zero_set_finite (c₅ c₄ c₃ c₂ c₁ c₀ : ℝ) :
    { z : ℝ | z ^ 6 + c₅ * z ^ 5 + c₄ * z ^ 4 + c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ = 0 }.Finite := by
  let p : Polynomial ℝ :=
    Polynomial.X ^ 6 + C c₅ * Polynomial.X ^ 5 + C c₄ * Polynomial.X ^ 4 +
    C c₃ * Polynomial.X ^ 3 + C c₂ * Polynomial.X ^ 2 + C c₁ * Polynomial.X + C c₀
  have hp : p ≠ 0 := by
    intro h0
    have h6 := congrArg (fun q => q.coeff 6) h0
    simp [p] at h6
  have hsub : { z : ℝ | z ^ 6 + c₅ * z ^ 5 + c₄ * z ^ 4 + c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ = 0 } ⊆
      (p.roots.toFinset : Set ℝ) := by
    intro z hz
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    simpa [p] using hz
  exact (p.roots.toFinset.finite_toSet).subset hsub

/-- Helper: intersection of a circle with center `(a, b) ≠ (0, 0)` and the circle `x^2 + y^2 = R2`
is finite (in fact has at most 2 points). -/
private lemma circle_origin_inter_finite (a b r2 R2 : ℝ) (ha : a ≠ 0) :
    { q : Point | (q.1 - a) ^ 2 + (q.2 - b) ^ 2 = r2 ∧ q.1 ^ 2 + q.2 ^ 2 = R2 }.Finite := by
  let rhs : ℝ := R2 + a ^ 2 + b ^ 2 - r2
  let m : ℝ := -b / a
  let k : ℝ := rhs / (2 * a)
  let S_y : Set ℝ := { y : ℝ | (1 + m ^ 2) * y ^ 2 + (2 * m * k) * y + (k ^ 2 - R2) = 0 }
  have hS_fin : S_y.Finite := quad_zero_set_finite (1 + m ^ 2) (2 * m * k) (k ^ 2 - R2)
    (Or.inl (by positivity))
  refine (hS_fin.image (fun y => (m * y + k, y))).subset ?_
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  have hlin : 2 * a * x + 2 * b * y = rhs := by dsimp [rhs]; linarith
  have hx : x = m * y + k := by dsimp [m, k]; field_simp [ha]; linarith
  refine ⟨y, ?_, Prod.ext hx.symm rfl⟩
  dsimp [S_y]
  rw [hx] at h2
  linarith

/-- Finiteness of solutions to our right-isosceles circle-circle neusis. -/
private lemma circleCircle_solutions_finite {h S D r₁ r₂ : ℝ}
    (hh : 0 < h) (hr₁ : r₁ ^ 2 = (1 - S - D) / 2) (hr₂ : r₂ ^ 2 = (1 - S + D) / 2)
    (hne₁ : ((-1 / 2 : ℝ), (1 / 2 : ℝ)) ≠ (-1 / 2 + r₁, 1 / 2))
    (hne₂ : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ≠ (1 / 2 + r₂, 1 / 2)) :
    (NeusisSolutionsScaled (2 * h) (0, 0)
      (Curve.circle (-1 / 2, 1 / 2) (-1 / 2 + r₁, 1 / 2) hne₁)
      (Curve.circle (1 / 2, 1 / 2) (1 / 2 + r₂, 1 / 2) hne₂)).Finite := by
  let C₁ := Curve.circle (-1 / 2, 1 / 2) (-1 / 2 + r₁, 1 / 2) hne₁
  let C₂ := Curve.circle (1 / 2, 1 / 2) (1 / 2 + r₂, 1 / 2) hne₂
  let d₁ : ℝ := (S + D) / 2
  let d₂ : ℝ := (S - D) / 2
  have hC₁_eq : ∀ q : Point, OnCurve C₁ q ↔ q.1 ^ 2 + q.2 ^ 2 + q.1 - q.2 + d₁ = 0 := by
    intro q; unfold OnCurve distSq; dsimp [C₁, d₁]; constructor <;> intro H <;> linarith
  have hC₂_eq : ∀ q : Point, OnCurve C₂ q ↔ q.1 ^ 2 + q.2 ^ 2 - q.1 - q.2 + d₂ = 0 := by
    intro q; unfold OnCurve distSq; dsimp [C₂, d₂]; constructor <;> intro H <;> linarith
  let F_X0 : Set (Point × Point) :=
    (fun Y => (((0 : ℝ), (0 : ℝ)), Y)) ''
      { q : Point | (q.1 - 1 / 2) ^ 2 + (q.2 - 1 / 2) ^ 2 = r₂ ^ 2 ∧ q.1 ^ 2 + q.2 ^ 2 = (2 * h) ^ 2 }
  let F_Y0 : Set (Point × Point) :=
    (fun X => (X, ((0 : ℝ), (0 : ℝ)))) ''
      { q : Point | (q.1 - (-1 / 2)) ^ 2 + (q.2 - 1 / 2) ^ 2 = r₁ ^ 2 ∧ q.1 ^ 2 + q.2 ^ 2 = (2 * h) ^ 2 }
  let S_z : Set ℝ := { z : ℝ |
    z ^ 6 + 0 * z ^ 5 + (S - h ^ 2 - 1) * z ^ 4 + 0 * z ^ 3 +
    ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4) * z ^ 2 +
    (D * S * h) * z +
    (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4) = 0 }
  let ptOfZ : ℝ → Point × Point := fun z =>
    let ρ₁ := z - h
    let ρ₂ := z + h
    let c := ((ρ₂ ^ 2 + d₂) / ρ₂ - (ρ₁ ^ 2 + d₁) / ρ₁) / 2
    let s := ((ρ₂ ^ 2 + d₂) / ρ₂ + (ρ₁ ^ 2 + d₁) / ρ₁) / 2
    ((ρ₁ * c, ρ₁ * s), (ρ₂ * c, ρ₂ * s))
  let F_main : Set (Point × Point) := ptOfZ '' S_z
  have hFX0_fin : F_X0.Finite :=
    (circle_origin_inter_finite (1 / 2) (1 / 2) (r₂ ^ 2) ((2 * h) ^ 2) (by norm_num)).image _
  have hFY0_fin : F_Y0.Finite :=
    (circle_origin_inter_finite (-1 / 2) (1 / 2) (r₁ ^ 2) ((2 * h) ^ 2) (by norm_num)).image _
  have hFm_fin : F_main.Finite := (poly6_monic_zero_set_finite _ _ _ _ _ _).image _
  refine ((hFX0_fin.union hFY0_fin).union hFm_fin).subset ?_
  rintro ⟨X, Y⟩ ⟨hX, hY, hcol, hdist⟩
  by_cases hX0 : X = (0, 0)
  · left; left
    refine ⟨Y, ⟨?_, ?_⟩, Prod.ext hX0.symm rfl⟩
    · unfold OnCurve distSq at hY; dsimp [C₂] at hY; linarith
    · rw [hX0] at hdist; unfold distSq at hdist; dsimp at hdist; linarith
  by_cases hY0 : Y = (0, 0)
  · left; right
    refine ⟨X, ⟨?_, ?_⟩, Prod.ext rfl hY0.symm⟩
    · unfold OnCurve distSq at hX; dsimp [C₁] at hX; linarith
    · rw [hY0] at hdist; unfold distSq at hdist; dsimp at hdist; linarith
  right
  have h2h : 2 * h ≠ 0 := by linarith
  let c : ℝ := (Y.1 - X.1) / (2 * h)
  let s : ℝ := (Y.2 - X.2) / (2 * h)
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    unfold distSq at hdist; dsimp [c, s]; field_simp [h2h]; linarith
  have hcol_u : X.1 * s = X.2 * c := by
    unfold Collinear3 at hcol; dsimp [c, s]; field_simp [h2h]; linarith
  let ρ₁ : ℝ := X.1 * c + X.2 * s
  let ρ₂ : ℝ := ρ₁ + 2 * h
  have hX1 : X.1 = ρ₁ * c := by dsimp [ρ₁]; linear_combination -X.1 * hcs + s * hcol_u
  have hX2 : X.2 = ρ₁ * s := by dsimp [ρ₁]; linear_combination -X.2 * hcs - c * hcol_u
  have hY1 : Y.1 = ρ₂ * c := by
    dsimp [ρ₂]; rw [add_mul, ← hX1]; dsimp [c]; field_simp [h2h]; ring
  have hY2 : Y.2 = ρ₂ * s := by
    dsimp [ρ₂]; rw [add_mul, ← hX2]; dsimp [s]; field_simp [h2h]; ring
  have hρ₁0 : ρ₁ ≠ 0 := by
    intro h0; apply hX0
    exact Prod.ext (by rw [hX1, h0]; ring) (by rw [hX2, h0]; ring)
  have hρ₂0 : ρ₂ ≠ 0 := by
    intro h0; apply hY0
    exact Prod.ext (by rw [hY1, h0]; ring) (by rw [hY2, h0]; ring)
  have heq1 : ρ₁ * (s - c) = ρ₁ ^ 2 + d₁ := by
    have h1 := (hC₁_eq X).mp hX
    rw [hX1, hX2] at h1
    linear_combination -h1 + ρ₁ ^ 2 * hcs
  have heq2 : ρ₂ * (c + s) = ρ₂ ^ 2 + d₂ := by
    have h2 := (hC₂_eq Y).mp hY
    rw [hY1, hY2] at h2
    linear_combination -h2 + ρ₂ ^ 2 * hcs
  have hsc1 : s - c = (ρ₁ ^ 2 + d₁) / ρ₁ := by field_simp [hρ₁0]; linarith
  have hsc2 : c + s = (ρ₂ ^ 2 + d₂) / ρ₂ := by field_simp [hρ₂0]; linarith
  have hc_eq : c = ((ρ₂ ^ 2 + d₂) / ρ₂ - (ρ₁ ^ 2 + d₁) / ρ₁) / 2 := by linarith
  have hs_eq : s = ((ρ₂ ^ 2 + d₂) / ρ₂ + (ρ₁ ^ 2 + d₁) / ρ₁) / 2 := by linarith
  let z : ℝ := ρ₁ + h
  have hz1 : ρ₁ = z - h := by dsimp [z]; ring
  have hz2 : ρ₂ = z + h := by dsimp [z, ρ₂]; ring
  refine ⟨z, ?_, ?_⟩
  · dsimp [S_z]
    have hcs_alg : 2 * (c ^ 2 + s ^ 2) = ((ρ₂ ^ 2 + d₂) / ρ₂) ^ 2 + ((ρ₁ ^ 2 + d₁) / ρ₁) ^ 2 := by
      rw [← hsc1, ← hsc2]; ring
    rw [hcs] at hcs_alg
    have hclr : ρ₁ ^ 2 * (ρ₂ ^ 2 + d₂) ^ 2 + ρ₂ ^ 2 * (ρ₁ ^ 2 + d₁) ^ 2 - 2 * ρ₁ ^ 2 * ρ₂ ^ 2 = 0 := by
      field_simp [hρ₁0, hρ₂0] at hcs_alg; linarith
    rw [hz1, hz2] at hclr
    dsimp [d₁, d₂] at hclr
    linear_combination (1 / 2 : ℝ) * hclr
  · dsimp [ptOfZ]
    rw [← hz1, ← hz2, ← hc_eq, ← hs_eq]
    exact Prod.ext (Prod.ext hX1.symm hX2.symm) (Prod.ext hY1.symm hY2.symm)

/-- **Right-Isosceles Circle-Circle Neusis Theorem**:
If `(A₄, A₂, A₁, A₀) ∈ NeusisSubfield⁴` satisfies `CircleCircleValid A₄ A₂ A₁ A₀`,
then **every** real root `z` of `z^6 + A₄ z^4 + A₂ z^2 + A₁ z + A₀ = 0` lies in `NeusisSubfield`. -/
theorem neusisReal_of_circleCircleValid {A₄ A₂ A₁ A₀ z : ℝ}
    (hA₄ : NeusisReal A₄) (hA₂ : NeusisReal A₂) (hA₁ : NeusisReal A₁) (hA₀ : NeusisReal A₀)
    (hvalid : CircleCircleValid A₄ A₂ A₁ A₀)
    (hroot : z ^ 6 + A₄ * z ^ 4 + A₂ * z ^ 2 + A₁ * z + A₀ = 0) :
    NeusisReal z := by
  rcases hvalid with ⟨t_s, hts_pos, hts_cub, hA4ts_neg, hdisc_pos, hWsq_pos, hU_pos, hr1_pos, hr2_pos⟩
  have hts_ne : t_s ≠ 0 := ne_of_gt hts_pos
  have h2m : NeusisReal (2 : ℝ) := by exact_mod_cast subfield_natCast_mem NeusisSubfield 2
  have h3m : NeusisReal (3 : ℝ) := by exact_mod_cast subfield_natCast_mem NeusisSubfield 3
  have h4m : NeusisReal (4 : ℝ) := by exact_mod_cast subfield_natCast_mem NeusisSubfield 4
  have h5m : NeusisReal (5 : ℝ) := by exact_mod_cast subfield_natCast_mem NeusisSubfield 5
  have hts_mem : NeusisReal t_s := by
    apply neusisReal_of_cubic h5m (NeusisSubfield.mul_mem h3m hA₄) hA₂ (neusisReal_neg hA₀)
      (by norm_num)
    linarith
  let M : ℝ := A₂ + 2 * A₄ * t_s + 3 * t_s ^ 2
  have hM_mem : NeusisReal M :=
    NeusisSubfield.add_mem
      (NeusisSubfield.add_mem hA₂
        (NeusisSubfield.mul_mem (NeusisSubfield.mul_mem h2m hA₄) hts_mem))
      (NeusisSubfield.mul_mem h3m (NeusisSubfield.pow_mem hts_mem 2))
  let disc : ℝ := 4 * M ^ 2 - A₁ ^ 2 / t_s
  have hdisc_mem : NeusisReal disc :=
    NeusisSubfield.sub_mem
      (NeusisSubfield.mul_mem h4m (NeusisSubfield.pow_mem hM_mem 2))
      (NeusisSubfield.div_mem (NeusisSubfield.pow_mem hA₁ 2) hts_mem)
  let sdisc : ℝ := Real.sqrt disc
  have hsdisc_sq : sdisc ^ 2 = disc := Real.sq_sqrt (le_of_lt hdisc_pos)
  have hsdisc_mem : NeusisReal sdisc := neusisReal_sqrt hdisc_mem (le_of_lt hdisc_pos)
  let Wsq : ℝ := 2 * M + sdisc
  have hWsq_mem : NeusisReal Wsq :=
    NeusisSubfield.add_mem (NeusisSubfield.mul_mem h2m hM_mem) hsdisc_mem
  let W : ℝ := Real.sqrt Wsq
  have hW_pos : 0 < W := Real.sqrt_pos.mpr hWsq_pos
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hW_sq : W ^ 2 = Wsq := Real.sq_sqrt (le_of_lt hWsq_pos)
  have hW_mem : NeusisReal W := neusisReal_sqrt hWsq_mem (le_of_lt hWsq_pos)
  have hW_biq : W ^ 4 - 4 * M * W ^ 2 + A₁ ^ 2 / t_s = 0 := by
    have h1 : (W ^ 2 - 2 * M) ^ 2 = disc := by
      rw [hW_sq]; dsimp [Wsq]; linarith [hsdisc_sq]
    dsimp [disc] at h1; linarith
  let U : ℝ := W - A₄ - t_s
  have hU_ne : U ≠ 0 := ne_of_gt hU_pos
  have hU_mem : NeusisReal U := NeusisSubfield.sub_mem (NeusisSubfield.sub_mem hW_mem hA₄) hts_mem
  let L : ℝ := Real.sqrt U
  have hL_pos : 0 < L := Real.sqrt_pos.mpr hU_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hL_sq : L ^ 2 = U := Real.sq_sqrt (le_of_lt hU_pos)
  have hL_mem : NeusisReal L := neusisReal_sqrt hU_mem (le_of_lt hU_pos)
  let st : ℝ := Real.sqrt t_s
  have hst_pos : 0 < st := Real.sqrt_pos.mpr hts_pos
  have hst_ne : st ≠ 0 := ne_of_gt hst_pos
  have hst_sq : st ^ 2 = t_s := Real.sq_sqrt (le_of_lt hts_pos)
  have hst_mem : NeusisReal st := neusisReal_sqrt hts_mem (le_of_lt hts_pos)
  let h : ℝ := st / L
  have hh_pos : 0 < h := div_pos hst_pos hL_pos
  have hh_ne : h ≠ 0 := ne_of_gt hh_pos
  have hh_sq : h ^ 2 = t_s / U := by dsimp [h]; rw [div_pow, hst_sq, hL_sq]
  have hh_mem : NeusisReal h := NeusisSubfield.div_mem hst_mem hL_mem
  let S : ℝ := W / U
  let D : ℝ := A₁ / (U * st * W)
  have hS_mem : NeusisReal S := NeusisSubfield.div_mem hW_mem hU_mem
  have hD_mem : NeusisReal D :=
    NeusisSubfield.div_mem hA₁ (NeusisSubfield.mul_mem (NeusisSubfield.mul_mem hU_mem hst_mem) hW_mem)
  let r₁sq : ℝ := (1 - S - D) / 2
  let r₂sq : ℝ := (1 - S + D) / 2
  let r₁ : ℝ := Real.sqrt r₁sq
  let r₂ : ℝ := Real.sqrt r₂sq
  have hr₁_pos : 0 < r₁ := Real.sqrt_pos.mpr hr1_pos
  have hr₂_pos : 0 < r₂ := Real.sqrt_pos.mpr hr2_pos
  have hr₁_sq : r₁ ^ 2 = (1 - S - D) / 2 := Real.sq_sqrt (le_of_lt hr1_pos)
  have hr₂_sq : r₂ ^ 2 = (1 - S + D) / 2 := Real.sq_sqrt (le_of_lt hr2_pos)
  have hr₁_mem : NeusisReal r₁ := neusisReal_sqrt
    (NeusisSubfield.div_mem (NeusisSubfield.sub_mem (NeusisSubfield.sub_mem NeusisSubfield.one_mem hS_mem) hD_mem)
      h2m) (le_of_lt hr1_pos)
  have hr₂_mem : NeusisReal r₂ := neusisReal_sqrt
    (NeusisSubfield.div_mem (NeusisSubfield.add_mem (NeusisSubfield.sub_mem NeusisSubfield.one_mem hS_mem) hD_mem)
      h2m) (le_of_lt hr2_pos)
  let z_cc : ℝ := z / L
  have hz_eq : z = L * z_cc := by dsimp [z_cc]; field_simp [hL_ne]
  by_cases hz_p : z_cc = h
  · have : z = st := by rw [hz_eq, hz_p]; dsimp [h]; field_simp [hL_ne]
    rwa [this]
  by_cases hz_m : z_cc = -h
  · have : z = -st := by rw [hz_eq, hz_m]; dsimp [h]; field_simp [hL_ne]
    rw [this]; exact neusisReal_neg hst_mem
  let ρ₁ : ℝ := z_cc - h
  let ρ₂ : ℝ := z_cc + h
  have hρ₁0 : ρ₁ ≠ 0 := sub_ne_zero.mpr hz_p
  have hρ₂0 : ρ₂ ≠ 0 := fun h0 => hz_m (by linarith)
  let d₁ : ℝ := (S + D) / 2
  let d₂ : ℝ := (S - D) / 2
  let c : ℝ := ((ρ₂ ^ 2 + d₂) / ρ₂ - (ρ₁ ^ 2 + d₁) / ρ₁) / 2
  let s : ℝ := ((ρ₂ ^ 2 + d₂) / ρ₂ + (ρ₁ ^ 2 + d₁) / ρ₁) / 2
  have hW2 : W ^ 2 + A₁ ^ 2 / (t_s * W ^ 2) = 4 * M := by
    have hW2_ne : W ^ 2 ≠ 0 := pow_ne_zero 2 hW_ne
    field_simp [hts_ne, hW2_ne] at hW_biq ⊢
    linarith
  have hD2 : U ^ 2 * D ^ 2 = A₁ ^ 2 / (t_s * W ^ 2) := by
    dsimp [D]; field_simp [hU_ne, hst_ne, hW_ne]; rw [hst_sq]
  have hS2 : U ^ 2 * S ^ 2 = W ^ 2 := by dsimp [S]; field_simp [hU_ne]
  have hSh2 : U ^ 2 * (S * h ^ 2) = W * t_s := by dsimp [S]; rw [hh_sq]; field_simp [hU_ne]
  have hh4 : U ^ 2 * h ^ 4 = t_s ^ 2 := by
    rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, hh_sq]; field_simp [hU_ne]
  have hh2 : U ^ 2 * h ^ 2 = U * t_s := by rw [hh_sq]; field_simp [hU_ne]
  have hcoeff4 : U * (S - h ^ 2 - 1) = A₄ := by
    dsimp [S]; rw [hh_sq]; field_simp [hU_ne]; dsimp [U]; ring
  have hcoeff2 : U ^ 2 * ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4) = A₂ := by
    calc U ^ 2 * ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4)
        = (U ^ 2 * D ^ 2 + U ^ 2 * S ^ 2 - 8 * (U ^ 2 * (S * h ^ 2)) - 4 * (U ^ 2 * h ^ 4) +
            8 * (U ^ 2 * h ^ 2)) / 4 := by ring
      _ = (A₁ ^ 2 / (t_s * W ^ 2) + W ^ 2 - 8 * (W * t_s) - 4 * t_s ^ 2 + 8 * (U * t_s)) / 4 := by
          rw [hD2, hS2, hSh2, hh4, hh2]
      _ = (4 * M - 8 * (W * t_s) - 4 * t_s ^ 2 + 8 * (U * t_s)) / 4 := by linarith [hW2]
      _ = A₂ := by dsimp [M, U]; ring
  have hcoeff1 : L ^ 5 * (D * S * h) = A₁ := by
    have hL4 : L ^ 4 = U ^ 2 := by rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, hL_sq]
    dsimp [D, S, h]
    have hprod : L ^ 5 * (A₁ / (U * st * W) * (W / U) * (st / L)) =
        (L ^ 4 / U ^ 2) * A₁ * (W / W) * (st / st) * (L / L) := by ring
    rw [hprod, hL4, div_self (pow_ne_zero 2 hU_ne), div_self hW_ne, div_self hst_ne, div_self hL_ne]
    ring
  have hcoeff0 : U ^ 3 * (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4) = A₀ := by
    have hUh2 : U * h ^ 2 = t_s := by rw [hh_sq]; field_simp [hU_ne]
    calc U ^ 3 * (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4)
        = (U * h ^ 2) * (U ^ 2 * D ^ 2 + U ^ 2 * S ^ 2 + 4 * (U ^ 2 * (S * h ^ 2)) +
            4 * (U ^ 2 * h ^ 4) - 4 * (U ^ 2 * h ^ 2)) / 4 := by ring
      _ = t_s * (A₁ ^ 2 / (t_s * W ^ 2) + W ^ 2 + 4 * (W * t_s) + 4 * t_s ^ 2 - 4 * (U * t_s)) / 4 := by
          rw [hUh2, hD2, hS2, hSh2, hh4, hh2]
      _ = t_s * (4 * M + 4 * (W * t_s) + 4 * t_s ^ 2 - 4 * (U * t_s)) / 4 := by
          have : A₁ ^ 2 / (t_s * W ^ 2) + W ^ 2 = 4 * M := by linarith [hW2]
          rw [this]
      _ = 5 * t_s ^ 3 + 3 * A₄ * t_s ^ 2 + A₂ * t_s := by dsimp [M, U]; ring
      _ = A₀ := by linarith [hts_cub]
  have hz_cc_sextic : z_cc ^ 6 + (S - h ^ 2 - 1) * z_cc ^ 4 +
      ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4) * z_cc ^ 2 +
      (D * S * h) * z_cc +
      (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4) = 0 := by
    have hL6_ne : L ^ 6 ≠ 0 := pow_ne_zero 6 hL_ne
    apply mul_left_cancel₀ hL6_ne
    rw [mul_zero]
    have hL2 : L ^ 2 = U := hL_sq
    have hL4 : L ^ 4 = U ^ 2 := by rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, hL_sq]
    have hL6 : L ^ 6 = U ^ 3 := by rw [show L ^ 6 = (L ^ 2) ^ 3 by ring, hL_sq]
    calc L ^ 6 * (z_cc ^ 6 + (S - h ^ 2 - 1) * z_cc ^ 4 +
            ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4) * z_cc ^ 2 +
            (D * S * h) * z_cc +
            (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4))
        = (L * z_cc) ^ 6 + (L ^ 2 * (S - h ^ 2 - 1)) * (L * z_cc) ^ 4 +
            (L ^ 4 * ((D ^ 2 + S ^ 2 - 8 * S * h ^ 2 - 4 * h ^ 4 + 8 * h ^ 2) / 4)) * (L * z_cc) ^ 2 +
            (L ^ 5 * (D * S * h)) * (L * z_cc) +
            L ^ 6 * (h ^ 2 * (D ^ 2 + S ^ 2 + 4 * S * h ^ 2 + 4 * h ^ 4 - 4 * h ^ 2) / 4) := by ring
      _ = z ^ 6 + A₄ * z ^ 4 + A₂ * z ^ 2 + A₁ * z + A₀ := by
          rw [← hz_eq, hL2, hL4, hL6, hcoeff4, hcoeff2, hcoeff1, hcoeff0]
      _ = 0 := hroot
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have hclr : ρ₁ ^ 2 * (ρ₂ ^ 2 + d₂) ^ 2 + ρ₂ ^ 2 * (ρ₁ ^ 2 + d₁) ^ 2 - 2 * ρ₁ ^ 2 * ρ₂ ^ 2 = 0 := by
      dsimp [ρ₁, ρ₂, d₁, d₂]
      linear_combination 2 * hz_cc_sextic
    dsimp [c, s]
    field_simp [hρ₁0, hρ₂0]
    linear_combination 2 * hclr
  have hne₁ : ((-1 / 2 : ℝ), (1 / 2 : ℝ)) ≠ (-1 / 2 + r₁, 1 / 2) := by
    intro heq; have h1 : (-1 / 2 : ℝ) = -1 / 2 + r₁ := congrArg Prod.fst heq; linarith
  have hne₂ : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ≠ (1 / 2 + r₂, 1 / 2) := by
    intro heq; have h1 : (1 / 2 : ℝ) = 1 / 2 + r₂ := congrArg Prod.fst heq; linarith
  let C₁ := Curve.circle (-1 / 2, 1 / 2) (-1 / 2 + r₁, 1 / 2) hne₁
  let C₂ := Curve.circle (1 / 2, 1 / 2) (1 / 2 + r₂, 1 / 2) hne₂
  let X : Point := (ρ₁ * c, ρ₁ * s)
  let Y : Point := (ρ₂ * c, ρ₂ * s)
  have hsol : (X, Y) ∈ NeusisSolutionsScaled (2 * h) (0, 0) C₁ C₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold OnCurve distSq; dsimp [C₁, X]
      have hsc1 : ρ₁ * (s - c) = ρ₁ ^ 2 + d₁ := by dsimp [c, s]; field_simp [hρ₁0]; ring
      dsimp [d₁] at hsc1
      linear_combination ρ₁ ^ 2 * hcs - hsc1 - hr₁_sq
    · unfold OnCurve distSq; dsimp [C₂, Y]
      have hsc2 : ρ₂ * (c + s) = ρ₂ ^ 2 + d₂ := by dsimp [c, s]; field_simp [hρ₂0]; ring
      dsimp [d₂] at hsc2
      linear_combination ρ₂ ^ 2 * hcs - hsc2 - hr₂_sq
    · unfold Collinear3; dsimp [X, Y]; ring
    · unfold distSq; dsimp [X, Y, ρ₁, ρ₂]
      linear_combination (2 * h) ^ 2 * hcs
  have hfin := circleCircle_solutions_finite hh_pos hr₁_sq hr₂_sq hne₁ hne₂
  have hhalf : NeusisReal (1 / 2 : ℝ) := by simpa using neusisReal_ratCast (1 / 2)
  have hmhalf : NeusisReal (-1 / 2 : ℝ) := by simpa using neusisReal_ratCast (-1 / 2)
  have hXY := neusis_scaled (γ₁ := C₁) (γ₂ := C₂)
    (NeusisSubfield.mul_mem h2m hh_mem)
    (by linarith)
    NeusisPoint.base0
    (neusisPoint_mk hmhalf hhalf)
    (neusisPoint_mk (neusisReal_add hmhalf hr₁_mem) hhalf)
    (neusisPoint_mk hhalf hhalf)
    (neusisPoint_mk (neusisReal_add hhalf hr₂_mem) hhalf)
    hfin hsol
  have hX1_mem : NeusisReal X.1 := neusisReal_fst hXY.1
  have hX2_mem : NeusisReal X.2 := neusisReal_snd hXY.1
  have hY1_mem : NeusisReal Y.1 := neusisReal_fst hXY.2
  have hY2_mem : NeusisReal Y.2 := neusisReal_snd hXY.2
  have hz_rec : z = L * ((Y.1 ^ 2 + Y.2 ^ 2) - (X.1 ^ 2 + X.2 ^ 2)) / (4 * h) := by
    have hXnorm : X.1 ^ 2 + X.2 ^ 2 = ρ₁ ^ 2 := by dsimp [X]; linear_combination ρ₁ ^ 2 * hcs
    have hYnorm : Y.1 ^ 2 + Y.2 ^ 2 = ρ₂ ^ 2 := by dsimp [Y]; linear_combination ρ₂ ^ 2 * hcs
    rw [hXnorm, hYnorm]
    dsimp [ρ₁, ρ₂]
    rw [hz_eq]
    field_simp [hh_ne]; ring
  rw [hz_rec]
  exact NeusisSubfield.div_mem
    (NeusisSubfield.mul_mem hL_mem
      (NeusisSubfield.sub_mem
        (NeusisSubfield.add_mem (NeusisSubfield.pow_mem hY1_mem 2) (NeusisSubfield.pow_mem hY2_mem 2))
        (NeusisSubfield.add_mem (NeusisSubfield.pow_mem hX1_mem 2) (NeusisSubfield.pow_mem hX2_mem 2))))
    (NeusisSubfield.mul_mem h4m hh_mem)

/-- **Angle Quintisection via Compass, Straightedge, and ONE Circle-Circle Neusis**:
For any `c ∈ NeusisSubfield` with `|c| < 2`, every real root `z` of
`z^5 - 5 z^3 + 5 z - c = 0` lies in `NeusisSubfield`. -/
theorem neusisReal_angle_quintisection {c z : ℝ} (hc : NeusisReal c) (hc2 : |c| < 2)
    (hroot : z ^ 5 - 5 * z ^ 3 + 5 * z - c = 0) : NeusisReal z := by
  have hc_sq : c ^ 2 < 4 := by
    have h1 : |c| ^ 2 < 2 ^ 2 := sq_lt_sq' (by linarith [abs_nonneg c]) hc2
    rw [sq_abs] at h1; linarith
  let s5 : ℝ := Real.sqrt 5
  have hs5_sq : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5_gt2 : 2 < s5 := by
    have : (2 : ℝ) ^ 2 < s5 ^ 2 := by rw [hs5_sq]; norm_num
    nlinarith [Real.sqrt_nonneg 5]
  have hs5_lt3 : s5 < 3 := by
    have : s5 ^ 2 < (3 : ℝ) ^ 2 := by rw [hs5_sq]; norm_num
    nlinarith [Real.sqrt_nonneg 5]
  let t_s : ℝ := (3 - s5) / 2
  have hts_pos : 0 < t_s := by dsimp [t_s]; linarith
  have hts_cub : 5 * t_s ^ 3 + 3 * (-5) * t_s ^ 2 + 5 * t_s - 0 = 0 := by
    dsimp [t_s]; linear_combination (5 / 8 : ℝ) * (3 - s5) * hs5_sq
  have hA4ts : (-5 : ℝ) + t_s < 0 := by dsimp [t_s]; linarith
  let M : ℝ := 5 + 2 * (-5) * t_s + 3 * t_s ^ 2
  have hM_eq : M = (1 + s5) / 2 := by
    dsimp [M, t_s]; linear_combination (3 / 4 : ℝ) * hs5_sq
  have hM_pos : 0 < M := by rw [hM_eq]; linarith
  have hM2_ts : M ^ 2 * t_s = 1 := by
    rw [hM_eq]; dsimp [t_s]; linear_combination (1 / 8 : ℝ) * (1 - s5) * hs5_sq
  have hinv_ts : 1 / t_s = M ^ 2 := by field_simp [ne_of_gt hts_pos]; linarith
  have hdisc_eq : 4 * M ^ 2 - (-c) ^ 2 / t_s = M ^ 2 * (4 - c ^ 2) := by
    have : (-c) ^ 2 / t_s = c ^ 2 * (1 / t_s) := by ring
    rw [this, hinv_ts]; ring
  have hdisc_pos : 0 < 4 * M ^ 2 - (-c) ^ 2 / t_s := by rw [hdisc_eq]; positivity
  have hWsq_pos : 0 < 2 * M + Real.sqrt (4 * M ^ 2 - (-c) ^ 2 / t_s) := by
    linarith [Real.sqrt_pos.mpr hdisc_pos]
  let W := Real.sqrt (2 * M + Real.sqrt (4 * M ^ 2 - (-c) ^ 2 / t_s))
  have hW_pos : 0 < W := Real.sqrt_pos.mpr hWsq_pos
  have hW_sq : W ^ 2 = 2 * M + Real.sqrt (4 * M ^ 2 - (-c) ^ 2 / t_s) :=
    Real.sq_sqrt (le_of_lt hWsq_pos)
  have hW_gt : 2 * M < W ^ 2 := by rw [hW_sq]; linarith [Real.sqrt_pos.mpr hdisc_pos]
  let U := W - (-5) - t_s
  have hU_eq : U = W + (5 - t_s) := by dsimp [U]; ring
  have hU_pos : 0 < U := by rw [hU_eq]; linarith
  let S := W / U
  let D := (-c) / (U * Real.sqrt t_s * W)
  have h1S : 1 - S = (5 - t_s) / U := by
    dsimp [S]; field_simp [ne_of_gt hU_pos]; linarith [hU_eq]
  have hD_lt : |D| < 1 - S := by
    rw [h1S]; dsimp [D]
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hU_pos,
      abs_of_pos (Real.sqrt_pos.mpr hts_pos), abs_of_pos hW_pos]
    have hden_pos : 0 < U * Real.sqrt t_s * W := by positivity
    rw [div_lt_div_iff₀ hden_pos hU_pos]
    have htM : t_s * M = (s5 - 1) / 2 := by
      rw [hM_eq]; dsimp [t_s]; linear_combination -(1 / 4 : ℝ) * hs5_sq
    have h5t : 4 < 5 - t_s := by dsimp [t_s]; linarith
    have h2tM : 1 < 2 * (t_s * M) := by rw [htM]; linarith
    have hsq_rhs : (4 : ℝ) < (5 - t_s) ^ 2 * (t_s * W ^ 2) := by
      have h1 : (16 : ℝ) < (5 - t_s) ^ 2 := by nlinarith
      have h2 : (16 : ℝ) * 1 < (5 - t_s) ^ 2 * (2 * (t_s * M)) :=
        mul_lt_mul'' h1 h2tM (by norm_num) (by norm_num)
      have h3 : (5 - t_s) ^ 2 * (2 * (t_s * M)) < (5 - t_s) ^ 2 * (t_s * W ^ 2) := by
        have hpos : 0 < (5 - t_s) ^ 2 * t_s := by positivity
        calc (5 - t_s) ^ 2 * (2 * (t_s * M))
            = (5 - t_s) ^ 2 * t_s * (2 * M) := by ring
          _ < (5 - t_s) ^ 2 * t_s * W ^ 2 := mul_lt_mul_of_pos_left hW_gt hpos
          _ = (5 - t_s) ^ 2 * (t_s * W ^ 2) := by ring
      linarith
    have hsq : |c| ^ 2 < ((5 - t_s) * Real.sqrt t_s * W) ^ 2 := by
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hts_pos)]
      calc c ^ 2 < 4 := hc_sq
        _ < (5 - t_s) ^ 2 * (t_s * W ^ 2) := hsq_rhs
        _ = (5 - t_s) ^ 2 * t_s * W ^ 2 := by ring
    have hstep : |c| < (5 - t_s) * Real.sqrt t_s * W := by
      have hnn : 0 ≤ (5 - t_s) * Real.sqrt t_s * W := by positivity
      by_contra hle
      push Not at hle
      have hsq_le : ((5 - t_s) * Real.sqrt t_s * W) ^ 2 ≤ |c| ^ 2 := by
        rw [sq, sq]; exact mul_self_le_mul_self hnn hle
      linarith
    calc |c| * U < (5 - t_s) * Real.sqrt t_s * W * U := mul_lt_mul_of_pos_right hstep hU_pos
      _ = (5 - t_s) * (U * Real.sqrt t_s * W) := by ring
  have hr1_pos : 0 < (1 - S - D) / 2 := by linarith [le_abs_self D]
  have hr2_pos : 0 < (1 - S + D) / 2 := by linarith [neg_le_abs D]
  have hvalid : CircleCircleValid (-5) 5 (-c) 0 :=
    ⟨t_s, hts_pos, hts_cub, hA4ts, hdisc_pos, hWsq_pos, hU_pos, hr1_pos, hr2_pos⟩
  have hsextic : z ^ 6 + (-5) * z ^ 4 + 5 * z ^ 2 + (-c) * z + 0 = 0 := by
    linear_combination z * hroot
  exact neusisReal_of_circleCircleValid
    (neusisReal_neg (by exact_mod_cast subfield_natCast_mem NeusisSubfield 5))
    (by exact_mod_cast subfield_natCast_mem NeusisSubfield 5)
    (neusisReal_neg hc)
    neusisReal_zero
    hvalid hsextic

/-- Chebyshev identity `2 cos(5 θ) = (2 cos θ)^5 - 5 (2 cos θ)^3 + 5 (2 cos θ)`. -/
private lemma two_cos_five_mul (θ : ℝ) :
    (2 * Real.cos θ) ^ 5 - 5 * (2 * Real.cos θ) ^ 3 + 5 * (2 * Real.cos θ) = 2 * Real.cos (5 * θ) := by
  have hsc : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have h3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
    rw [show 3 * θ = 2 * θ + θ by ring, Real.cos_add, h2, hs2]
    linear_combination -2 * Real.cos θ * hsc
  have hs3 : Real.sin (3 * θ) = (4 * Real.cos θ ^ 2 - 1) * Real.sin θ := by
    rw [show 3 * θ = 2 * θ + θ by ring, Real.sin_add, h2, hs2]; ring
  have h5 : Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
    rw [show 5 * θ = 3 * θ + 2 * θ by ring, Real.cos_add, h3, h2, hs3, hs2]
    linear_combination -(8 * Real.cos θ ^ 3 - 2 * Real.cos θ) * hsc
  rw [h5]; ring

/-- **Regular 25-gon Corollary**: The regular 25-gon is neusis-constructible (directly via
our single circle-circle neusis angle quintisection of `2π/5`). -/
theorem regularPolygonConstructible_25 : RegularPolygonConstructible 25 := by
  unfold RegularPolygonConstructible NeusisComplex
  rw [neusisPoint_iff]
  let θ : ℝ := 2 * Real.pi / 25
  have hexp : Complex.exp (2 * Real.pi * Complex.I / (25 : ℕ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    have : (2 * Real.pi * Complex.I / (25 : ℕ) : ℂ) = (θ : ℂ) * Complex.I := by
      dsimp [θ]; push_cast; ring
    rw [this, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hexp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  let z : ℝ := 2 * Real.cos θ
  let c : ℝ := 2 * Real.cos (5 * θ)
  have h5θ : 5 * θ = 2 * Real.pi / 5 := by dsimp [θ]; ring
  -- Show c = 2 cos(2π/5) satisfies c^2 + c - 1 = 0, hence c ∈ NeusisSubfield!
  have hc_lt2 : |c| < 2 := by
    have hpos : 0 < 2 * Real.pi / 5 := by positivity
    have hlt : 2 * Real.pi / 5 < Real.pi := by linarith [Real.pi_pos]
    have hcos_lt1 : Real.cos (2 * Real.pi / 5) < 1 := by
      have hle := Real.cos_le_one (2 * Real.pi / 5)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have hsin0 : Real.sin (2 * Real.pi / 5) = 0 := by
          have := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
          nlinarith [sq_nonneg (Real.sin (2 * Real.pi / 5))]
        have hsin_pos : 0 < Real.sin (2 * Real.pi / 5) := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        linarith
    have hcos_gt : -1 < Real.cos (2 * Real.pi / 5) := by
      have hge := Real.neg_one_le_cos (2 * Real.pi / 5)
      rcases lt_or_eq_of_le hge with h | h
      · exact h
      · exfalso
        have hsin0 : Real.sin (2 * Real.pi / 5) = 0 := by
          have := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
          nlinarith [sq_nonneg (Real.sin (2 * Real.pi / 5))]
        have hsin_pos : 0 < Real.sin (2 * Real.pi / 5) := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        linarith
    dsimp [c]; rw [h5θ, abs_lt]; constructor <;> linarith
  have hc_quad : c ^ 2 + c - 1 = 0 := by
    have h5c := two_cos_five_mul (5 * θ)
    have h2pi : 5 * (5 * θ) = 2 * Real.pi := by dsimp [θ]; ring
    rw [h2pi, Real.cos_two_pi] at h5c
    have hfac : (c - 2) * (c ^ 2 + c - 1) ^ 2 = 0 := by
      dsimp [c]; linear_combination h5c
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exfalso; have := (abs_lt.mp hc_lt2).2; linarith
    · exact sq_eq_zero_iff.mp h2
  have hc_mem : NeusisReal c :=
    neusisReal_of_quadratic neusisReal_one neusisReal_one (neusisReal_neg neusisReal_one)
      one_ne_zero (by linarith)
  have hcheb : z ^ 5 - 5 * z ^ 3 + 5 * z - c = 0 := by
    dsimp [z, c]; linear_combination two_cos_five_mul θ
  have hz_mem : NeusisReal z := neusisReal_angle_quintisection hc_mem hc_lt2 hcheb
  have hcos_mem : NeusisReal (Real.cos θ) := by
    have : Real.cos θ = z / 2 := by dsimp [z]; ring
    rw [this]; exact NeusisSubfield.div_mem hz_mem (subfield_natCast_mem NeusisSubfield 2)
  have hsin_nonneg : 0 ≤ Real.sin θ := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · dsimp [θ]; positivity
    · dsimp [θ]; linarith [Real.pi_pos]
  have hsin_eq : Real.sin θ = Real.sqrt (1 - Real.cos θ ^ 2) := by
    have hsc := Real.sin_sq_add_cos_sq θ
    have : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
    rw [← this, Real.sqrt_sq hsin_nonneg]
  have hsin_mem : NeusisReal (Real.sin θ) := by
    rw [hsin_eq]
    exact neusisReal_sqrt
      (NeusisSubfield.sub_mem NeusisSubfield.one_mem (NeusisSubfield.pow_mem hcos_mem 2))
      (by have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_nonneg (Real.sin θ)])
  exact ⟨hcos_mem, hsin_mem⟩

end Neusis
