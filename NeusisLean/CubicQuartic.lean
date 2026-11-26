import NeusisLean.BaragarNecessity

/-!
# Scaling, Angle Trisection, Cube Roots, and Real Cubics & Quartics via Neusis

We prove that `NeusisSubfield` is closed under:
1. Neusis constructions with any constructible mark length `s > 0` (`neusis_scaled`).
2. Angle trisection (`4 u^3 - 3 u = c` for `|c| ≤ 1`) via Archimedes's unit-mark line-circle neusis.
3. Real cube roots (`u^3 = a` for all `a : ℝ`) via a single unit-mark circle-line neusis.
4. All real roots of all real cubic and quartic polynomials over `NeusisSubfield`.
-/

namespace Neusis

open Polynomial

/-- Helper: rational numbers lie in `NeusisSubfield`. -/
lemma neusisReal_ratCast (q : ℚ) : NeusisReal (q : ℝ) := by
  have : (q : ℝ) ∈ NeusisSubfield := by
    rw [Rat.cast_def]
    refine NeusisSubfield.div_mem ?_ (subfield_natCast_mem NeusisSubfield q.den)
    cases q.num with
    | ofNat n => simp
    | negSucc n =>
      push_cast
      exact NeusisSubfield.neg_mem (NeusisSubfield.add_mem (subfield_natCast_mem NeusisSubfield n)
        NeusisSubfield.one_mem)
  exact this

/-- Scale a point by `c`. -/
def scalePt (c : ℝ) (p : Point) : Point := (c * p.1, c * p.2)

/-- Scale a curve by nonzero `c`. -/
def scaleCurve (c : ℝ) (hc : c ≠ 0) : Curve → Curve
  | Curve.line A B h => Curve.line (scalePt c A) (scalePt c B) (by
      intro heq; apply h
      have h1 : c * A.1 = c * B.1 := congrArg Prod.fst heq
      have h2 : c * A.2 = c * B.2 := congrArg Prod.snd heq
      exact Prod.ext (mul_left_cancel₀ hc h1) (mul_left_cancel₀ hc h2))
  | Curve.circle C Q h => Curve.circle (scalePt c C) (scalePt c Q) (by
      intro heq; apply h
      have h1 : c * C.1 = c * Q.1 := congrArg Prod.fst heq
      have h2 : c * C.2 = c * Q.2 := congrArg Prod.snd heq
      exact Prod.ext (mul_left_cancel₀ hc h1) (mul_left_cancel₀ hc h2))

lemma onCurve_scale {c : ℝ} (hc : c ≠ 0) (γ : Curve) (X : Point) :
    OnCurve (scaleCurve c hc γ) (scalePt c X) ↔ OnCurve γ X := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  cases γ with
  | line A B _ =>
    unfold OnCurve scaleCurve scalePt Collinear3
    dsimp only
    constructor <;> intro h
    · apply mul_left_cancel₀ hc2; linear_combination h
    · linear_combination c ^ 2 * h
  | circle C Q _ =>
    unfold OnCurve scaleCurve scalePt distSq
    dsimp only
    constructor <;> intro h
    · apply mul_left_cancel₀ hc2; linear_combination h
    · linear_combination c ^ 2 * h

/-- Scaled neusis solutions with mark length `s > 0`. -/
def NeusisSolutionsScaled (s : ℝ) (P : Point) (γ₁ γ₂ : Curve) : Set (Point × Point) :=
  { xy | OnCurve γ₁ xy.1 ∧ OnCurve γ₂ xy.2 ∧ Collinear3 P xy.1 xy.2 ∧ distSq xy.1 xy.2 = s ^ 2 }

/-- A neusis construction with any constructible mark length `s > 0` produces constructible points
(by scaling the plane by `s⁻¹`, applying unit-mark neusis, and scaling back by `s`). -/
lemma neusis_scaled {s : ℝ} (hs : NeusisReal s) (hspos : 0 < s)
    {P X Y : Point} {γ₁ γ₂ : Curve}
    (hP : NeusisPoint P)
    (hγ₁₁ : NeusisPoint γ₁.pt1) (hγ₁₂ : NeusisPoint γ₁.pt2)
    (hγ₂₁ : NeusisPoint γ₂.pt1) (hγ₂₂ : NeusisPoint γ₂.pt2)
    (hfin : (NeusisSolutionsScaled s P γ₁ γ₂).Finite)
    (hsol : (X, Y) ∈ NeusisSolutionsScaled s P γ₁ γ₂) :
    NeusisPoint X ∧ NeusisPoint Y := by
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hinv0 : s⁻¹ ≠ 0 := inv_ne_zero hs0
  have hinv : NeusisReal s⁻¹ := neusisReal_inv hs
  have hscale_pt : ∀ {q : Point}, NeusisPoint q → NeusisPoint (scalePt s⁻¹ q) := by
    intro q hq
    rw [neusisPoint_iff] at hq ⊢
    exact ⟨neusisReal_mul hinv hq.1, neusisReal_mul hinv hq.2⟩
  have hpt1_sc : ∀ (γ : Curve), (scaleCurve s⁻¹ hinv0 γ).pt1 = scalePt s⁻¹ γ.pt1 := by
    intro γ; cases γ <;> rfl
  have hpt2_sc : ∀ (γ : Curve), (scaleCurve s⁻¹ hinv0 γ).pt2 = scalePt s⁻¹ γ.pt2 := by
    intro γ; cases γ <;> rfl
  have hfin' : (NeusisSolutions (scalePt s⁻¹ P) (scaleCurve s⁻¹ hinv0 γ₁)
      (scaleCurve s⁻¹ hinv0 γ₂)).Finite := by
    let f : Point × Point → Point × Point := fun xy => (scalePt s xy.1, scalePt s xy.2)
    have hinj : Function.Injective f := by
      intro a b h
      have h1 : s * a.1.1 = s * b.1.1 := congrArg (fun p => p.1.1) h
      have h2 : s * a.1.2 = s * b.1.2 := congrArg (fun p => p.1.2) h
      have h3 : s * a.2.1 = s * b.2.1 := congrArg (fun p => p.2.1) h
      have h4 : s * a.2.2 = s * b.2.2 := congrArg (fun p => p.2.2) h
      exact Prod.ext (Prod.ext (mul_left_cancel₀ hs0 h1) (mul_left_cancel₀ hs0 h2))
        (Prod.ext (mul_left_cancel₀ hs0 h3) (mul_left_cancel₀ hs0 h4))
    refine Set.Finite.of_finite_image ?_ (hinj.injOn)
    refine hfin.subset ?_
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy, hcol, hdist⟩, rfl⟩
    have hx' : scalePt s⁻¹ (scalePt s x) = x := by
      unfold scalePt; ext <;> simp [hs0]
    have hy' : scalePt s⁻¹ (scalePt s y) = y := by
      unfold scalePt; ext <;> simp [hs0]
    refine ⟨(onCurve_scale hinv0 γ₁ _).mp (by rwa [hx']),
            (onCurve_scale hinv0 γ₂ _).mp (by rwa [hy']), ?_, ?_⟩
    · unfold Collinear3 at hcol ⊢; dsimp only [f, scalePt] at hcol ⊢
      have := congrArg (fun z => s ^ 2 * z) hcol
      field_simp [hs0] at this; linarith
    · unfold distSq at hdist ⊢; dsimp only [f, scalePt] at hdist ⊢
      linear_combination s ^ 2 * hdist
  have hsol' : (scalePt s⁻¹ X, scalePt s⁻¹ Y) ∈
      NeusisSolutions (scalePt s⁻¹ P) (scaleCurve s⁻¹ hinv0 γ₁) (scaleCurve s⁻¹ hinv0 γ₂) := by
    rcases hsol with ⟨hx, hy, hcol, hdist⟩
    refine ⟨(onCurve_scale hinv0 γ₁ X).mpr hx, (onCurve_scale hinv0 γ₂ Y).mpr hy, ?_, ?_⟩
    · unfold Collinear3 at hcol ⊢; dsimp only [scalePt] at hcol ⊢
      linear_combination (s⁻¹) ^ 2 * hcol
    · unfold distSq at hdist ⊢; dsimp only [scalePt] at hdist ⊢
      have hsq : s⁻¹ ^ 2 * s ^ 2 = 1 := by field_simp [hs0]
      linear_combination (s⁻¹) ^ 2 * hdist + hsq
  have hX' : NeusisPoint (scalePt s⁻¹ X) :=
    NeusisPoint.neusis_left (hscale_pt hP)
      (by rw [hpt1_sc]; exact hscale_pt hγ₁₁) (by rw [hpt2_sc]; exact hscale_pt hγ₁₂)
      (by rw [hpt1_sc]; exact hscale_pt hγ₂₁) (by rw [hpt2_sc]; exact hscale_pt hγ₂₂)
      hfin' hsol'
  have hY' : NeusisPoint (scalePt s⁻¹ Y) :=
    NeusisPoint.neusis_right (hscale_pt hP)
      (by rw [hpt1_sc]; exact hscale_pt hγ₁₁) (by rw [hpt2_sc]; exact hscale_pt hγ₁₂)
      (by rw [hpt1_sc]; exact hscale_pt hγ₂₁) (by rw [hpt2_sc]; exact hscale_pt hγ₂₂)
      hfin' hsol'
  rw [neusisPoint_iff] at hX' hY'
  constructor
  · rw [neusisPoint_iff]
    refine ⟨?_, ?_⟩
    · have : X.1 = s * (scalePt s⁻¹ X).1 := by unfold scalePt; field_simp [hs0]
      rw [this]; exact neusisReal_mul hs hX'.1
    · have : X.2 = s * (scalePt s⁻¹ X).2 := by unfold scalePt; field_simp [hs0]
      rw [this]; exact neusisReal_mul hs hX'.2
  · rw [neusisPoint_iff]
    refine ⟨?_, ?_⟩
    · have : Y.1 = s * (scalePt s⁻¹ Y).1 := by unfold scalePt; field_simp [hs0]
      rw [this]; exact neusisReal_mul hs hY'.1
    · have : Y.2 = s * (scalePt s⁻¹ Y).2 := by unfold scalePt; field_simp [hs0]
      rw [this]; exact neusisReal_mul hs hY'.2

/-- Helper: a polynomial `f : ℝ → ℝ` with a nonzero leading coefficient of degree `4`
has finitely many real roots. -/
private lemma poly4_zero_set_finite (a₄ a₃ a₂ a₁ a₀ : ℝ) (ha₄ : a₄ ≠ 0) :
    { t : ℝ | a₄ * t ^ 4 + a₃ * t ^ 3 + a₂ * t ^ 2 + a₁ * t + a₀ = 0 }.Finite := by
  let p : Polynomial ℝ :=
    C a₄ * Polynomial.X ^ 4 + C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2 +
    C a₁ * Polynomial.X + C a₀
  have hp : p ≠ 0 := by
    intro h0
    have h4 := congrArg (fun q => q.coeff 4) h0
    simp [p] at h4
    exact ha₄ h4
  have hsub : { t : ℝ | a₄ * t ^ 4 + a₃ * t ^ 3 + a₂ * t ^ 2 + a₁ * t + a₀ = 0 } ⊆
      (p.roots.toFinset : Set ℝ) := by
    intro t ht
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    simpa [p] using ht
  exact (p.roots.toFinset.finite_toSet).subset hsub

/-- **Archimedes's Angle Trisection via Unit-Mark Line-Circle Neusis**:
If `c ∈ NeusisSubfield`, `|c| ≤ 1`, and `4 u^3 - 3 u = c`, then `u ∈ NeusisSubfield`. -/
lemma neusisReal_angle_trisection {c u : ℝ} (hc : NeusisReal c) (hcle : |c| ≤ 1)
    (hu : 4 * u ^ 3 - 3 * u = c) : NeusisReal u := by
  have hc2 : c ^ 2 ≤ 1 := by
    have := sq_abs c
    nlinarith [abs_nonneg c]
  by_cases hc1 : c = 1
  · have hfac : (u - 1) * (2 * u + 1) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have : u = 1 := by linarith
      rw [this]; exact neusisReal_one
    · have h2' : 2 * u + 1 = 0 := sq_eq_zero_iff.mp h2
      have : u = ((-1 / 2 : ℚ) : ℝ) := by push_cast; linarith
      rw [this]; exact neusisReal_ratCast _
  by_cases hcm1 : c = -1
  · have hfac : (u + 1) * (2 * u - 1) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have : u = -1 := by linarith
      rw [this]; exact neusisReal_neg neusisReal_one
    · have h2' : 2 * u - 1 = 0 := sq_eq_zero_iff.mp h2
      have : u = ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith
      rw [this]; exact neusisReal_ratCast _
  have hc2_lt : c ^ 2 < 1 := by
    rcases lt_or_eq_of_le hc2 with h | h
    · exact h
    · exfalso
      have : (c - 1) * (c + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h2
      · exact hc1 (by linarith)
      · exact hcm1 (by linarith)
  have hu2_le : u ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have habs : 1 < |u| := by
      have : 1 ^ 2 < |u| ^ 2 := by rw [sq_abs]; linarith
      nlinarith [abs_nonneg u]
    rcases le_or_gt 0 u with hu0 | hu0
    · have hu1 : 1 < u := by rwa [abs_of_nonneg hu0] at habs
      have : 1 < 4 * u ^ 3 - 3 * u := by nlinarith
      linarith [le_abs_self c]
    · have hum1 : u < -1 := by
        rw [abs_of_neg hu0] at habs; linarith
      have : 4 * u ^ 3 - 3 * u < -1 := by nlinarith
      linarith [neg_le_abs c]
  let s₀ : ℝ := Real.sqrt (1 - c ^ 2)
  have hs₀_pos : 0 < s₀ := Real.sqrt_pos.mpr (by linarith)
  have hs₀_sq : s₀ ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
  have hs₀_mem : NeusisReal s₀ :=
    neusisReal_sqrt (NeusisSubfield.sub_mem NeusisSubfield.one_mem (NeusisSubfield.pow_mem hc 2))
      (by linarith)
  let v₀ : ℝ := Real.sqrt (1 - u ^ 2)
  have hv₀_sq : v₀ ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
  have hs₀_v : s₀ ^ 2 = (v₀ * (4 * u ^ 2 - 1)) ^ 2 := by
    have : 1 - c ^ 2 = (1 - u ^ 2) * (4 * u ^ 2 - 1) ^ 2 := by
      rw [← hu]; ring
    nlinarith [hs₀_sq, hv₀_sq, this]
  obtain ⟨v, hv_sq, hs₀_eq⟩ : ∃ v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ s₀ = v * (4 * u ^ 2 - 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs₀_v with h | h
    · exact ⟨v₀, by linarith, h⟩
    · exact ⟨-v₀, by linarith, by linarith⟩
  let P : Point := (c, s₀)
  let L : Curve := Curve.line (0, 0) (1, 0) (by norm_num)
  let C : Curve := Curve.circle (0, 0) (1, 0) (by norm_num)
  let X : Point := (-2 * u, 0)
  let Y : Point := (-u, v)
  have hsol : (X, Y) ∈ NeusisSolutions P L C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold OnCurve Collinear3; dsimp [L, X]; ring
    · unfold OnCurve distSq; dsimp [C, Y]; linarith
    · unfold Collinear3; dsimp [P, X, Y]
      rw [hs₀_eq, ← hu]; ring
    · unfold distSq; dsimp [X, Y]; linarith
  have hfin : (NeusisSolutions P L C).Finite := by
    -- Split into x = 0 and x ≠ 0; for each X = (x, 0), x lies in a finite set and Y has ≤ 2 choices!
    let S_nz : Set ℝ := { x : ℝ |
      (-1 : ℝ) * x ^ 4 + (2 * c) * x ^ 3 + (3 : ℝ) * x ^ 2 + (-8 * c) * x + (4 * c ^ 2) = 0 }
    -- Map (X', Y') ↦ (X'.1, Y'.1, Y'.2) with finite projection on X'.1 and finite fibers!
    have hmem : ∀ xy ∈ NeusisSolutions P L C,
        xy.1.2 = 0 ∧
        (xy.1.1 = 0 ∧ xy.2.1 ^ 2 + xy.2.2 ^ 2 = 1 ∧ c * xy.2.2 = s₀ * xy.2.1 ∨
         xy.1.1 ∈ S_nz ∧ xy.2.1 = xy.1.1 / 2 ∧ xy.2.2 ^ 2 = 1 - (xy.1.1 / 2) ^ 2) := by
      rintro ⟨⟨x, x₂⟩, ⟨y₁, y₂⟩⟩ ⟨hL, hC, hcol, hdist⟩
      have hx2 : x₂ = 0 := by unfold OnCurve Collinear3 at hL; dsimp [L] at hL; linarith
      subst hx2
      have hcirc : y₁ ^ 2 + y₂ ^ 2 = 1 := by unfold OnCurve distSq at hC; dsimp [C] at hC; linarith
      have hd : (x - y₁) ^ 2 + y₂ ^ 2 = 1 := by unfold distSq at hdist; dsimp at hdist; linarith
      have hx_y : x * (x - 2 * y₁) = 0 := by linarith
      refine ⟨rfl, ?_⟩
      rcases mul_eq_zero.mp hx_y with hx0 | hxy
      · left
        refine ⟨hx0, hcirc, ?_⟩
        unfold Collinear3 at hcol; dsimp [P] at hcol; subst hx0; linarith
      · right
        have hy1 : y₁ = x / 2 := by linarith
        have hy2_sq : y₂ ^ 2 = 1 - (x / 2) ^ 2 := by rw [← hy1]; linarith
        have hcol' : (x - c) * y₂ = s₀ * (x / 2) := by
          unfold Collinear3 at hcol; dsimp [P] at hcol; rw [hy1] at hcol; linarith
        have hsq_eq : (x - c) ^ 2 * (1 - (x / 2) ^ 2) = (1 - c ^ 2) * (x / 2) ^ 2 := by
          have := congrArg (fun z => z ^ 2) hcol'
          rw [mul_pow, mul_pow, hy2_sq, hs₀_sq] at this
          exact this
        refine ⟨?_, hy1, hy2_sq⟩
        dsimp [S_nz]
        linear_combination 4 * hsq_eq
    -- Finite union of the x=0 fiber (≤ 2 points) and the x ∈ S_nz set (≤ 2 points per x)
    let F0 : Set (Point × Point) := { xy | xy.1 = (0, 0) ∧ xy.2.1 ^ 2 + xy.2.2 ^ 2 = 1 ∧ c * xy.2.2 = s₀ * xy.2.1 }
    let F1 : Set (Point × Point) :=
      ⋃ x ∈ S_nz, { ((x, 0), (x / 2, Real.sqrt (1 - (x / 2) ^ 2))),
                    ((x, 0), (x / 2, -Real.sqrt (1 - (x / 2) ^ 2))) }
    have hF0_fin : F0.Finite := by
      -- Since c^2 + s₀^2 = 1, y₂ = ±s₀ and y₁ = ±c (at most 2 points!)
      have hsub : F0 ⊆ { ((0, 0), (c, s₀)), ((0, 0), (-c, -s₀)) } := by
        rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ⟨hx, hcirc, hlin⟩
        have hx1 : x₁ = 0 := congrArg Prod.fst hx
        have hx2 : x₂ = 0 := congrArg Prod.snd hx
        have hy2_sq : y₂ ^ 2 = s₀ ^ 2 := by
          linear_combination s₀ ^ 2 * hcirc + (c * y₂ + s₀ * y₁) * hlin - y₂ ^ 2 * hs₀_sq
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2_sq with hy2 | hy2
        · have hy1 : y₁ = c := by
            have : s₀ * y₁ = s₀ * c := by rw [← hlin, hy2]; ring
            exact mul_left_cancel₀ (ne_of_gt hs₀_pos) this
          simp [hx1, hx2, hy1, hy2]
        · have hy1 : y₁ = -c := by
            have : s₀ * y₁ = s₀ * (-c) := by rw [← hlin, hy2]; ring
            exact mul_left_cancel₀ (ne_of_gt hs₀_pos) this
          simp [hx1, hx2, hy1, hy2]
      exact (Set.toFinite _).subset hsub
    have hF1_fin : F1.Finite :=
      (poly4_zero_set_finite _ _ _ _ _ (by norm_num)).biUnion fun _ _ => Set.toFinite _
    refine (hF0_fin.union hF1_fin).subset ?_
    intro xy hxy
    rcases hmem xy hxy with ⟨hx2, h0 | h1⟩
    · left
      exact ⟨Prod.ext h0.1 hx2, h0.2.1, h0.2.2⟩
    · right
      rcases h1 with ⟨hxS, hy1, hy2_sq⟩
      have hnn : 0 ≤ 1 - (xy.1.1 / 2) ^ 2 := by rw [← hy2_sq]; exact sq_nonneg _
      have hsq : xy.2.2 ^ 2 = (Real.sqrt (1 - (xy.1.1 / 2) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt hnn, hy2_sq]
      refine Set.mem_biUnion hxS ?_
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
      · left; exact Prod.ext (Prod.ext rfl hx2) (Prod.ext hy1 hpos)
      · right; exact Prod.ext (Prod.ext rfl hx2) (Prod.ext hy1 hneg)
  have hX : NeusisPoint X :=
    NeusisPoint.neusis_left (γ₁ := L) (γ₂ := C) (neusisPoint_mk hc hs₀_mem)
      NeusisPoint.base0 NeusisPoint.base1 NeusisPoint.base0 NeusisPoint.base1 hfin hsol
  have hX1 : NeusisReal (-2 * u) := neusisReal_fst hX
  have hu_eq : u = (-2 * u) / (-2) := by ring
  rw [hu_eq]
  exact NeusisSubfield.div_mem hX1 (NeusisSubfield.neg_mem (subfield_natCast_mem NeusisSubfield 2))

/-- Unit-mark circle-line neusis for real cube roots `u^3 = a` when `a > 1`. -/
private lemma neusisReal_cbrt_gt_one {a u : ℝ} (ha : NeusisReal a) (ha1 : 1 < a)
    (hu : u ^ 3 = a) : NeusisReal u := by
  have ha1_pos : 0 < a - 1 := by linarith
  have hr2_pos : 0 < 3 / (a - 1) := div_pos (by norm_num) ha1_pos
  let r : ℝ := Real.sqrt (3 / (a - 1))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hr2_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_sq : r ^ 2 = 3 / (a - 1) := Real.sq_sqrt (le_of_lt hr2_pos)
  have hr_mem : NeusisReal r :=
    neusisReal_sqrt (NeusisSubfield.div_mem (subfield_natCast_mem NeusisSubfield 3)
      (NeusisSubfield.sub_mem ha NeusisSubfield.one_mem)) (le_of_lt hr2_pos)
  have hra : r ^ 2 * a = r ^ 2 + 3 := by
    rw [hr_sq]; field_simp [ne_of_gt ha1_pos]; ring
  let p : ℝ := -3 * r / 2
  let q : ℝ := (1 - 3 * r ^ 2) / 4
  let h : ℝ := (3 * r ^ 2 + 3) / 4
  let d : ℝ := h - q
  have hd_eq : d = (3 * r ^ 2 + 1) / 2 := by dsimp [d, h, q]; ring
  have hd_pos : 0 < d := by rw [hd_eq]; positivity
  have hp_mem : NeusisReal p :=
    NeusisSubfield.div_mem (NeusisSubfield.mul_mem
      (NeusisSubfield.neg_mem (subfield_natCast_mem NeusisSubfield 3)) hr_mem)
      (subfield_natCast_mem NeusisSubfield 2)
  have hq_mem : NeusisReal q :=
    NeusisSubfield.div_mem (NeusisSubfield.sub_mem NeusisSubfield.one_mem
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 3) (NeusisSubfield.pow_mem hr_mem 2)))
      (subfield_natCast_mem NeusisSubfield 4)
  have hh_mem : NeusisReal h :=
    NeusisSubfield.div_mem (NeusisSubfield.add_mem
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 3) (NeusisSubfield.pow_mem hr_mem 2))
      (subfield_natCast_mem NeusisSubfield 3))
      (subfield_natCast_mem NeusisSubfield 4)
  let P : Point := (p, q)
  have hP_ne0 : ((0 : ℝ), (0 : ℝ)) ≠ P := by
    intro heq
    have h1 : (0 : ℝ) = p := congrArg Prod.fst heq
    dsimp [p] at h1; linarith
  let L : Curve := Curve.line (0, h) (1, h) (by norm_num)
  let C : Curve := Curve.circle (0, 0) P hP_ne0
  let t : ℝ := r * (u + 2)
  have htd_pos : 0 < t ^ 2 + d ^ 2 := by positivity
  let lam : ℝ := -2 * (p * t + q * d) / (t ^ 2 + d ^ 2)
  let X : Point := (p + t, h)
  let Y : Point := (p + lam * t, q + lam * d)
  have hsol : (X, Y) ∈ NeusisSolutions P L C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold OnCurve Collinear3; dsimp [L, X]; ring
    · unfold OnCurve distSq; dsimp [C, P, Y, lam]
      field_simp [ne_of_gt htd_pos]; ring
    · unfold Collinear3; dsimp [P, X, Y, d]; ring
    · unfold distSq; dsimp [X, Y, lam]
      have hnum : (t ^ 2 + 2 * p * t + d ^ 2 + 2 * q * d) ^ 2 - (t ^ 2 + d ^ 2) = 0 := by
        dsimp [t, p, q, d, h]
        linear_combination r ^ 2 * (u + 2) * (r ^ 2 * hu + hra)
      field_simp [ne_of_gt htd_pos]
      dsimp [d] at hnum ⊢
      linear_combination (t ^ 2 + (h - q) ^ 2) * hnum
  have hfin : (NeusisSolutions P L C).Finite := by
    let S_t : Set ℝ := { τ : ℝ | 1 * τ ^ 2 + 0 * τ + (d ^ 2 - 1) = 0 } ∪
      { τ : ℝ | (-1 : ℝ) * τ ^ 4 + (6 * r) * τ ^ 3 + (-12 * r ^ 2) * τ ^ 2 +
        (9 * r ^ 3 + 3 * r) * τ + 0 = 0 }
    have hS_fin : S_t.Finite :=
      (quad_zero_set_finite 1 0 (d ^ 2 - 1) (Or.inl one_ne_zero)).union
        (poly4_zero_set_finite (-1) (6 * r) (-12 * r ^ 2) (9 * r ^ 3 + 3 * r) 0 (by norm_num))
    let F : Set (Point × Point) :=
      ⋃ τ ∈ S_t, { ((p + τ, h), P),
                   ((p + τ, h), (p + (-2 * (p * τ + q * d) / (τ ^ 2 + d ^ 2)) * τ,
                                 q + (-2 * (p * τ + q * d) / (τ ^ 2 + d ^ 2)) * d)) }
    have hF_fin : F.Finite := hS_fin.biUnion fun _ _ => Set.toFinite _
    refine hF_fin.subset ?_
    rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ⟨hL, hC, hcol, hdist⟩
    have hx2 : x₂ = h := by unfold OnCurve Collinear3 at hL; dsimp [L] at hL; linarith
    subst hx2
    let τ : ℝ := x₁ - p
    have hx1 : x₁ = p + τ := by dsimp [τ]; ring
    have hτd_pos : 0 < τ ^ 2 + d ^ 2 := by positivity
    by_cases hYP : (y₁, y₂) = P
    · have hτ_mem : τ ∈ S_t := by
        left
        have hy1 : y₁ = p := congrArg Prod.fst hYP
        have hy2 : y₂ = q := congrArg Prod.snd hYP
        unfold distSq at hdist; dsimp at hdist
        rw [hx1, hy1, hy2] at hdist
        dsimp [d]; linarith
      refine Set.mem_biUnion hτ_mem ?_
      left; exact Prod.ext (Prod.ext hx1 rfl) hYP
    · -- Y ≠ P, so Y = P + μ*(τ, d) with μ = -2*(p*τ + q*d)/(τ^2 + d^2)
      let μ : ℝ := (y₂ - q) / d
      have hy2_eq : y₂ = q + μ * d := by dsimp [μ]; field_simp [ne_of_gt hd_pos]; ring
      have hy1_eq : y₁ = p + μ * τ := by
        unfold Collinear3 at hcol; dsimp [P] at hcol
        have hcol' : τ * (y₂ - q) = d * (y₁ - p) := by dsimp [τ, d]; linarith
        rw [hy2_eq] at hcol'
        have : d * (y₁ - p - μ * τ) = 0 := by linarith
        rcases mul_eq_zero.mp this with hd0 | h0
        · exact absurd hd0 (ne_of_gt hd_pos)
        · linarith
      have hμ0 : μ ≠ 0 := by
        intro h0; apply hYP
        exact Prod.ext (by rw [hy1_eq, h0]; ring) (by rw [hy2_eq, h0]; ring)
      have hcirc : μ * (μ * (τ ^ 2 + d ^ 2) + 2 * (p * τ + q * d)) = 0 := by
        unfold OnCurve distSq at hC; dsimp [C, P] at hC
        rw [hy1_eq, hy2_eq] at hC; linarith
      have hμ_val : μ = -2 * (p * τ + q * d) / (τ ^ 2 + d ^ 2) := by
        rcases mul_eq_zero.mp hcirc with h0 | hlin
        · exact absurd h0 hμ0
        · field_simp [ne_of_gt hτd_pos]; linarith
      have hdist_eq : (τ ^ 2 + 2 * p * τ + d ^ 2 + 2 * q * d) ^ 2 = τ ^ 2 + d ^ 2 := by
        unfold distSq at hdist; dsimp at hdist
        rw [hx1, hy1_eq, hy2_eq, hμ_val] at hdist
        have hd_sub : h - (q + -2 * (p * τ + q * d) / (τ ^ 2 + d ^ 2) * d) =
            (1 - (-2 * (p * τ + q * d) / (τ ^ 2 + d ^ 2))) * d := by dsimp [d]; ring
        rw [hd_sub] at hdist
        field_simp [ne_of_gt hτd_pos] at hdist
        apply mul_right_cancel₀ (ne_of_gt hτd_pos)
        linear_combination hdist
      have hτ_mem : τ ∈ S_t := by
        right
        dsimp [p, q, d, h] at hdist_eq
        change (-1 : ℝ) * τ ^ 4 + 6 * r * τ ^ 3 + -12 * r ^ 2 * τ ^ 2 + (9 * r ^ 3 + 3 * r) * τ + 0 = 0
        linear_combination -hdist_eq
      refine Set.mem_biUnion hτ_mem ?_
      right
      exact Prod.ext (Prod.ext hx1 rfl) (Prod.ext (by rw [hy1_eq, hμ_val]) (by rw [hy2_eq, hμ_val]))
  have hX : NeusisPoint X :=
    NeusisPoint.neusis_left (γ₁ := L) (γ₂ := C) (neusisPoint_mk hp_mem hq_mem)
      (neusisPoint_mk neusisReal_zero hh_mem) (neusisPoint_mk neusisReal_one hh_mem)
      NeusisPoint.base0 (neusisPoint_mk hp_mem hq_mem) hfin hsol
  have hX1 : NeusisReal (p + t) := neusisReal_fst hX
  have hu_eq : u = ((p + t) - p) / r - 2 := by dsimp [t]; field_simp [hr_ne]; ring
  rw [hu_eq]
  exact NeusisSubfield.sub_mem
    (NeusisSubfield.div_mem (NeusisSubfield.sub_mem hX1 hp_mem) hr_mem)
    (subfield_natCast_mem NeusisSubfield 2)

/-- `NeusisSubfield` is closed under arbitrary real cube roots: if `u^3 = a` and `a ∈ NeusisSubfield`,
then `u ∈ NeusisSubfield`. -/
lemma neusisReal_cbrt {a u : ℝ} (ha : NeusisReal a) (hu : u ^ 3 = a) : NeusisReal u := by
  rcases lt_trichotomy a 0 with hneg | rfl | hpos
  · have hpos' : 0 < -a := by linarith
    have hk_mem : NeusisReal (2 + (-a)⁻¹) :=
      NeusisSubfield.add_mem (subfield_natCast_mem NeusisSubfield 2)
        (neusisReal_inv (neusisReal_neg ha))
    have hk_pos : 0 < 2 + (-a)⁻¹ := by positivity
    let a' : ℝ := (-a) * (2 + (-a)⁻¹) ^ 3
    have ha'_mem : NeusisReal a' :=
      NeusisSubfield.mul_mem (neusisReal_neg ha) (NeusisSubfield.pow_mem hk_mem 3)
    have ha'_gt1 : 1 < a' := by
      dsimp [a']
      have h1 : (-a) * (-a)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos')
      have : (-a) * (2 + (-a)⁻¹) ^ 3 = 8 * (-a) + 12 + 6 * (-a)⁻¹ + (-a)⁻¹ ^ 2 := by
        calc (-a) * (2 + (-a)⁻¹) ^ 3
            = 8 * (-a) + 12 * ((-a) * (-a)⁻¹) + 6 * ((-a) * (-a)⁻¹) * (-a)⁻¹ +
              ((-a) * (-a)⁻¹) * (-a)⁻¹ ^ 2 := by ring
          _ = 8 * (-a) + 12 + 6 * (-a)⁻¹ + (-a)⁻¹ ^ 2 := by rw [h1]; ring
      rw [this]
      have hpos2 : 0 < 8 * (-a) + 6 * (-a)⁻¹ + (-a)⁻¹ ^ 2 := by positivity
      linarith
    have hprod : (-u * (2 + (-a)⁻¹)) ^ 3 = a' := by dsimp [a']; linear_combination -(2 + (-a)⁻¹) ^ 3 * hu
    have hprod_mem := neusisReal_cbrt_gt_one ha'_mem ha'_gt1 hprod
    have hu_eq : u = -((-u * (2 + (-a)⁻¹)) / (2 + (-a)⁻¹)) := by
      rw [mul_div_cancel_right₀ (-u) (ne_of_gt hk_pos), neg_neg]
    rw [hu_eq]
    exact neusisReal_neg (NeusisSubfield.div_mem hprod_mem hk_mem)
  · have : u = 0 := by
      rcases eq_or_ne u 0 with rfl | hne
      · rfl
      · exfalso; exact pow_ne_zero 3 hne hu
    rw [this]; exact neusisReal_zero
  · have hk_mem : NeusisReal (2 + a⁻¹) :=
      NeusisSubfield.add_mem (subfield_natCast_mem NeusisSubfield 2) (neusisReal_inv ha)
    have hk_pos : 0 < 2 + a⁻¹ := by positivity
    let a' : ℝ := a * (2 + a⁻¹) ^ 3
    have ha'_mem : NeusisReal a' := NeusisSubfield.mul_mem ha (NeusisSubfield.pow_mem hk_mem 3)
    have ha'_gt1 : 1 < a' := by
      dsimp [a']
      have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      have : a * (2 + a⁻¹) ^ 3 = 8 * a + 12 + 6 * a⁻¹ + a⁻¹ ^ 2 := by
        calc a * (2 + a⁻¹) ^ 3
            = 8 * a + 12 * (a * a⁻¹) + 6 * (a * a⁻¹) * a⁻¹ + (a * a⁻¹) * a⁻¹ ^ 2 := by ring
          _ = 8 * a + 12 + 6 * a⁻¹ + a⁻¹ ^ 2 := by rw [h1]; ring
      rw [this]
      have hpos2 : 0 < 8 * a + 6 * a⁻¹ + a⁻¹ ^ 2 := by positivity
      linarith
    have hprod : (u * (2 + a⁻¹)) ^ 3 = a' := by dsimp [a']; linear_combination (2 + a⁻¹) ^ 3 * hu
    have hprod_mem := neusisReal_cbrt_gt_one ha'_mem ha'_gt1 hprod
    have hu_eq : u = (u * (2 + a⁻¹)) / (2 + a⁻¹) := by field_simp [ne_of_gt hk_pos]
    rw [hu_eq]
    exact NeusisSubfield.div_mem hprod_mem hk_mem

/-- Existence of a real cube root for any real number `a`. -/
private lemma exists_real_cbrt (a : ℝ) : ∃ u : ℝ, u ^ 3 = a := by
  rcases le_or_gt 0 a with h | h
  · refine ⟨a ^ ((1 : ℝ) / 3), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul h]
    norm_num
  · refine ⟨-((-a) ^ ((1 : ℝ) / 3)), ?_⟩
    have hnn : 0 ≤ -a := by linarith
    have h3 : ((-a) ^ ((1 : ℝ) / 3)) ^ 3 = -a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
    linear_combination -h3

/-- Injectivity of `x ↦ x ^ 3` on `ℝ`. -/
private lemma pow_three_injective {x y : ℝ} (h : x ^ 3 = y ^ 3) : x = y := by
  have hfac : (x - y) * ((x + y / 2) ^ 2 + 3 * y ^ 2 / 4) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · have hy0 : y = 0 := by nlinarith [sq_nonneg (x + y / 2), sq_nonneg y]
    nlinarith [sq_nonneg (x + y / 2), hy0]

/-- Every real root of a depressed cubic `y^3 + p y + q = 0` over `NeusisSubfield` lies in `NeusisSubfield`. -/
private lemma neusisReal_of_depressed_cubic {p q y : ℝ}
    (hp : NeusisReal p) (hq : NeusisReal q) (hroot : y ^ 3 + p * y + q = 0) :
    NeusisReal y := by
  by_cases hp0 : p = 0
  · subst hp0
    exact neusisReal_cbrt (neusisReal_neg hq) (by linarith)
  let Δ : ℝ := (q / 2) ^ 2 + (p / 3) ^ 3
  have hΔ_mem : NeusisReal Δ :=
    NeusisSubfield.add_mem
      (NeusisSubfield.pow_mem (NeusisSubfield.div_mem hq (subfield_natCast_mem NeusisSubfield 2)) 2)
      (NeusisSubfield.pow_mem (NeusisSubfield.div_mem hp (subfield_natCast_mem NeusisSubfield 3)) 3)
  rcases le_or_gt 0 Δ with hΔ | hΔ
  · -- Cardano case (Δ ≥ 0): construct one real root y₀ = u + v, then factor to quadratic!
    let s : ℝ := Real.sqrt Δ
    have hs_mem : NeusisReal s := neusisReal_sqrt hΔ_mem hΔ
    have hs_sq : s ^ 2 = Δ := Real.sq_sqrt hΔ
    rcases exists_real_cbrt (-q / 2 + s) with ⟨u, hu⟩
    rcases exists_real_cbrt (-q / 2 - s) with ⟨v, hv⟩
    have hu_mem : NeusisReal u := neusisReal_cbrt
      (NeusisSubfield.add_mem (NeusisSubfield.div_mem (neusisReal_neg hq)
        (subfield_natCast_mem NeusisSubfield 2)) hs_mem) hu
    have hv_mem : NeusisReal v := neusisReal_cbrt
      (NeusisSubfield.sub_mem (NeusisSubfield.div_mem (neusisReal_neg hq)
        (subfield_natCast_mem NeusisSubfield 2)) hs_mem) hv
    have huv3 : (u * v) ^ 3 = (-p / 3) ^ 3 := by
      have : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by ring
      rw [this, hu, hv]
      dsimp [Δ] at hs_sq
      linear_combination -hs_sq
    have huv : u * v = -p / 3 := pow_three_injective huv3
    let y₀ : ℝ := u + v
    have hy₀_mem : NeusisReal y₀ := neusisReal_add hu_mem hv_mem
    have hy₀_root : y₀ ^ 3 + p * y₀ + q = 0 := by
      dsimp [y₀]
      linear_combination hu + hv + 3 * (u + v) * huv
    have hfac : (y - y₀) * (y ^ 2 + y₀ * y + (y₀ ^ 2 + p)) = 0 := by
      linear_combination hroot - hy₀_root
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have : y = y₀ := by linarith
      rwa [this]
    · exact neusisReal_of_quadratic neusisReal_one hy₀_mem
        (NeusisSubfield.add_mem (NeusisSubfield.pow_mem hy₀_mem 2) hp) one_ne_zero (by linarith)
  · -- Casus irreducibilis (Δ < 0): p < 0, reduce to Archimedes angle trisection!
    have hp_neg : p < 0 := by
      by_contra h
      push Not at h
      have : 0 ≤ Δ := by dsimp [Δ]; positivity
      linarith
    have hm_pos : 0 < -p / 3 := by linarith
    let k : ℝ := 2 * Real.sqrt (-p / 3)
    have hk_pos : 0 < k := mul_pos two_pos (Real.sqrt_pos.mpr hm_pos)
    have hk_ne : k ≠ 0 := ne_of_gt hk_pos
    have hk_sq : k ^ 2 = 4 * (-p / 3) := by
      dsimp [k]; rw [mul_pow, Real.sq_sqrt (le_of_lt hm_pos)]; ring
    have hk_mem : NeusisReal k :=
      NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2)
        (neusisReal_sqrt (NeusisSubfield.div_mem (neusisReal_neg hp)
          (subfield_natCast_mem NeusisSubfield 3)) (le_of_lt hm_pos))
    let c₀ : ℝ := -4 * q / k ^ 3
    have hc₀_mem : NeusisReal c₀ :=
      NeusisSubfield.div_mem (NeusisSubfield.mul_mem
        (NeusisSubfield.neg_mem (subfield_natCast_mem NeusisSubfield 4)) hq)
        (NeusisSubfield.pow_mem hk_mem 3)
    have hc₀_sq : c₀ ^ 2 < 1 := by
      dsimp [c₀]
      have hk6 : (k ^ 3) ^ 2 = 64 * (-p / 3) ^ 3 := by
        calc (k ^ 3) ^ 2 = (k ^ 2) ^ 3 := by ring
          _ = (4 * (-p / 3)) ^ 3 := by rw [hk_sq]
          _ = 64 * (-p / 3) ^ 3 := by ring
      have hk6_pos : 0 < (k ^ 3) ^ 2 := by positivity
      rw [div_pow, div_lt_one hk6_pos, hk6]
      dsimp [Δ] at hΔ
      linarith
    have hc₀_le : |c₀| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (c₀ + 1), sq_nonneg (c₀ - 1)]
    let u : ℝ := y / k
    have hu_eq : 4 * u ^ 3 - 3 * u = c₀ := by
      dsimp [u, c₀]
      have hk3_ne : k ^ 3 ≠ 0 := pow_ne_zero 3 hk_ne
      field_simp [hk_ne]
      linear_combination 4 * hroot - 3 * y * hk_sq
    have hu_mem : NeusisReal u := neusisReal_angle_trisection hc₀_mem hc₀_le hu_eq
    have hy_eq : y = k * u := by dsimp [u]; field_simp [hk_ne]
    rw [hy_eq]
    exact neusisReal_mul hk_mem hu_mem

/-- Every real root of a general cubic `a r^3 + b r^2 + c r + d = 0` (`a ≠ 0`)
over `NeusisSubfield` lies in `NeusisSubfield`. -/
lemma neusisReal_of_cubic {a b c d r : ℝ}
    (ha : NeusisReal a) (hb : NeusisReal b) (hc : NeusisReal c) (hd : NeusisReal d)
    (ha0 : a ≠ 0) (hroot : a * r ^ 3 + b * r ^ 2 + c * r + d = 0) :
    NeusisReal r := by
  let s : ℝ := b / (3 * a)
  have hs_mem : NeusisReal s :=
    NeusisSubfield.div_mem hb (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 3) ha)
  let y : ℝ := r + s
  let p : ℝ := c / a - 3 * s ^ 2
  let q : ℝ := d / a - c * s / a + 2 * s ^ 3
  have hp_mem : NeusisReal p :=
    NeusisSubfield.sub_mem (NeusisSubfield.div_mem hc ha)
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 3) (NeusisSubfield.pow_mem hs_mem 2))
  have hq_mem : NeusisReal q :=
    NeusisSubfield.add_mem
      (NeusisSubfield.sub_mem (NeusisSubfield.div_mem hd ha)
        (NeusisSubfield.div_mem (NeusisSubfield.mul_mem hc hs_mem) ha))
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) (NeusisSubfield.pow_mem hs_mem 3))
  have hy_root : y ^ 3 + p * y + q = 0 := by
    dsimp [y, p, q, s]
    field_simp [ha0]
    linear_combination 27 * a ^ 2 * hroot
  have hy_mem : NeusisReal y := neusisReal_of_depressed_cubic hp_mem hq_mem hy_root
  have hr_eq : r = y - s := by dsimp [y]; ring
  rw [hr_eq]
  exact NeusisSubfield.sub_mem hy_mem hs_mem

/-- Every real root of a depressed quartic `y^4 + p y^2 + q y + s = 0` over `NeusisSubfield`
lies in `NeusisSubfield` (by Ferrari's resolvent cubic). -/
private lemma neusisReal_of_depressed_quartic {p q s y : ℝ}
    (hp : NeusisReal p) (hq : NeusisReal q) (hs : NeusisReal s)
    (hroot : y ^ 4 + p * y ^ 2 + q * y + s = 0) :
    NeusisReal y := by
  by_cases hq0 : q = 0
  · subst hq0
    have hy2_mem : NeusisReal (y ^ 2) :=
      neusisReal_of_quadratic neusisReal_one hp hs one_ne_zero (by linear_combination hroot)
    exact neusisReal_of_quadratic neusisReal_one neusisReal_zero (neusisReal_neg hy2_mem)
      one_ne_zero (by ring)
  -- Ferrari resolvent cubic: f(t) = 8*t^3 + 8*p*t^2 + (2*p^2 - 8*s)*t - q^2 = 0
  let f : ℝ → ℝ := fun t => 8 * t ^ 3 + 8 * p * t ^ 2 + (2 * p ^ 2 - 8 * s) * t - q ^ 2
  have hf_cont : Continuous f := by fun_prop
  have hf0 : f 0 < 0 := by dsimp [f]; nlinarith [sq_pos_of_ne_zero hq0]
  -- Pick R > 0 large enough so f(R) > 0
  let R : ℝ := 1 + |p| + |2 * p ^ 2 - 8 * s| + q ^ 2
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have hfR : 0 < f R := by
    dsimp [f]
    have h1 : -|p| ≤ p := neg_abs_le p
    have h2 : -|2 * p ^ 2 - 8 * s| ≤ 2 * p ^ 2 - 8 * s := neg_abs_le _
    have hR1 : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg p, abs_nonneg (2 * p ^ 2 - 8 * s), sq_nonneg q]
    have hRp : |p| ≤ R - 1 := by dsimp [R]; linarith [abs_nonneg (2 * p ^ 2 - 8 * s), sq_nonneg q]
    have hR2 : |2 * p ^ 2 - 8 * s| ≤ R - 1 := by dsimp [R]; linarith [abs_nonneg p, sq_nonneg q]
    have hRq : q ^ 2 ≤ R - 1 := by dsimp [R]; linarith [abs_nonneg p, abs_nonneg (2 * p ^ 2 - 8 * s)]
    have hR2_le : R ≤ R ^ 2 := by nlinarith
    nlinarith [sq_nonneg R]
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f 0) (f R) := ⟨le_of_lt hf0, le_of_lt hfR⟩
  rcases intermediate_value_Icc (le_of_lt hR_pos) hf_cont.continuousOn hzero_mem with ⟨t, htI, hft⟩
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le htI.1 with h | rfl
    · exact h
    · exfalso; linarith
  have ht_mem : NeusisReal t := by
    apply neusisReal_of_cubic
      (show NeusisReal (8 : ℝ) by exact_mod_cast subfield_natCast_mem NeusisSubfield 8)
      (NeusisSubfield.mul_mem (show NeusisReal (8 : ℝ) by exact_mod_cast subfield_natCast_mem NeusisSubfield 8) hp)
      (NeusisSubfield.sub_mem
        (NeusisSubfield.mul_mem (show NeusisReal (2 : ℝ) by exact_mod_cast subfield_natCast_mem NeusisSubfield 2)
          (NeusisSubfield.pow_mem hp 2))
        (NeusisSubfield.mul_mem (show NeusisReal (8 : ℝ) by exact_mod_cast subfield_natCast_mem NeusisSubfield 8) hs))
      (neusisReal_neg (NeusisSubfield.pow_mem hq 2))
      (by norm_num)
    dsimp [f] at hft; linarith
  let m : ℝ := Real.sqrt (2 * t)
  have hm_pos : 0 < m := Real.sqrt_pos.mpr (by linarith)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hm_sq : m ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  have hm_mem : NeusisReal m :=
    neusisReal_sqrt (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) ht_mem) (by linarith)
  have hfac : (y ^ 2 + m * y + (p / 2 + t - q / (2 * m))) *
      (y ^ 2 - m * y + (p / 2 + t + q / (2 * m))) = 0 := by
    have hft' : 8 * t ^ 3 + 8 * p * t ^ 2 + (2 * p ^ 2 - 8 * s) * t - q ^ 2 = 0 := hft
    have h2 : (y ^ 2 + p / 2 + t) ^ 2 - (m * y - q / (2 * m)) ^ 2 = 0 := by
      field_simp [hm_ne]
      have hm4 : m ^ 4 = 4 * t ^ 2 := by rw [show m ^ 4 = (m ^ 2) ^ 2 by ring, hm_sq]; ring
      linear_combination 8 * t * hroot + hft' +
        (4 * y ^ 4 + 4 * p * y ^ 2 + 4 * q * y + 8 * t * y ^ 2 + p ^ 2 + 4 * p * t + 4 * t ^ 2) * hm_sq -
        4 * y ^ 2 * hm4
    linear_combination h2
  have hc1_mem : NeusisReal (p / 2 + t - q / (2 * m)) :=
    NeusisSubfield.sub_mem
      (NeusisSubfield.add_mem (NeusisSubfield.div_mem hp (subfield_natCast_mem NeusisSubfield 2)) ht_mem)
      (NeusisSubfield.div_mem hq (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) hm_mem))
  have hc2_mem : NeusisReal (p / 2 + t + q / (2 * m)) :=
    NeusisSubfield.add_mem
      (NeusisSubfield.add_mem (NeusisSubfield.div_mem hp (subfield_natCast_mem NeusisSubfield 2)) ht_mem)
      (NeusisSubfield.div_mem hq (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) hm_mem))
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact neusisReal_of_quadratic neusisReal_one hm_mem hc1_mem one_ne_zero (by linarith)
  · exact neusisReal_of_quadratic neusisReal_one (neusisReal_neg hm_mem) hc2_mem one_ne_zero (by linarith)

/-- Every real root of a general quartic `a r^4 + b r^3 + c r^2 + d r + e = 0` (`a ≠ 0`)
over `NeusisSubfield` lies in `NeusisSubfield`. -/
lemma neusisReal_of_quartic {a b c d e r : ℝ}
    (ha : NeusisReal a) (hb : NeusisReal b) (hc : NeusisReal c)
    (hd : NeusisReal d) (he : NeusisReal e)
    (ha0 : a ≠ 0) (hroot : a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0) :
    NeusisReal r := by
  let u : ℝ := b / (4 * a)
  have hu_mem : NeusisReal u :=
    NeusisSubfield.div_mem hb (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 4) ha)
  let y : ℝ := r + u
  let p : ℝ := c / a - 6 * u ^ 2
  let q : ℝ := d / a - 2 * c * u / a + 8 * u ^ 3
  let s : ℝ := e / a - d * u / a + c * u ^ 2 / a - 3 * u ^ 4
  have hp_mem : NeusisReal p :=
    NeusisSubfield.sub_mem (NeusisSubfield.div_mem hc ha)
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 6) (NeusisSubfield.pow_mem hu_mem 2))
  have hq_mem : NeusisReal q :=
    NeusisSubfield.add_mem
      (NeusisSubfield.sub_mem (NeusisSubfield.div_mem hd ha)
        (NeusisSubfield.div_mem (NeusisSubfield.mul_mem
          (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) hc) hu_mem) ha))
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 8) (NeusisSubfield.pow_mem hu_mem 3))
  have hs_mem : NeusisReal s :=
    NeusisSubfield.sub_mem
      (NeusisSubfield.add_mem
        (NeusisSubfield.sub_mem (NeusisSubfield.div_mem he ha)
          (NeusisSubfield.div_mem (NeusisSubfield.mul_mem hd hu_mem) ha))
        (NeusisSubfield.div_mem (NeusisSubfield.mul_mem hc (NeusisSubfield.pow_mem hu_mem 2)) ha))
      (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 3) (NeusisSubfield.pow_mem hu_mem 4))
  have hy_root : y ^ 4 + p * y ^ 2 + q * y + s = 0 := by
    dsimp [y, p, q, s, u]
    field_simp [ha0]
    linear_combination 256 * a ^ 3 * hroot
  have hy_mem : NeusisReal y := neusisReal_of_depressed_quartic hp_mem hq_mem hs_mem hy_root
  have hr_eq : r = y - u := by dsimp [y]; ring
  rw [hr_eq]
  exact NeusisSubfield.sub_mem hy_mem hu_mem

/-- Every real root of a nonzero polynomial of degree `≤ 4` over `NeusisSubfield`
lies in `NeusisSubfield`. -/
theorem neusisReal_of_poly_le4 (P : Polynomial NeusisSubfield) (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 4) {r : ℝ} (hroot : Polynomial.aeval r P = 0) :
    NeusisReal r := by
  have heval : (P.coeff 4 : ℝ) * r ^ 4 + (P.coeff 3 : ℝ) * r ^ 3 + (P.coeff 2 : ℝ) * r ^ 2 +
      (P.coeff 1 : ℝ) * r + (P.coeff 0 : ℝ) = 0 := by
    have hsum := Polynomial.aeval_eq_sum_range' (x := r) (p := P) (n := 5) (by omega)
    rw [hroot] at hsum
    have hcoe : ∀ x : NeusisSubfield, algebraMap (↥NeusisSubfield) ℝ x = (x : ℝ) := fun _ => rfl
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Algebra.smul_def, hcoe] at hsum
    linarith
  have hlc : (P.coeff P.natDegree : ℝ) ≠ 0 := by
    intro h0
    have : P.leadingCoeff = 0 := Subtype.ext h0
    exact hP (Polynomial.leadingCoeff_eq_zero.mp this)
  have hgt : ∀ k, P.natDegree < k → (P.coeff k : ℝ) = 0 := by
    intro k hk; simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  have hdeg_cases : P.natDegree = 0 ∨ P.natDegree = 1 ∨ P.natDegree = 2 ∨
      P.natDegree = 3 ∨ P.natDegree = 4 := by omega
  rcases hdeg_cases with h0 | h1 | h2 | h3 | h4
  · exfalso
    rw [h0] at hlc
    rw [hgt 4 (by omega), hgt 3 (by omega), hgt 2 (by omega), hgt 1 (by omega)] at heval
    apply hlc; linarith
  · rw [h1] at hlc
    rw [hgt 4 (by omega), hgt 3 (by omega), hgt 2 (by omega)] at heval
    have hr : r = -(P.coeff 0 : ℝ) / (P.coeff 1 : ℝ) := by field_simp [hlc]; linarith
    rw [hr]
    exact NeusisSubfield.div_mem (neusisReal_neg (P.coeff 0).2) (P.coeff 1).2
  · rw [h2] at hlc
    rw [hgt 4 (by omega), hgt 3 (by omega)] at heval
    exact neusisReal_of_quadratic (P.coeff 2).2 (P.coeff 1).2 (P.coeff 0).2 hlc (by linarith)
  · rw [h3] at hlc
    rw [hgt 4 (by omega)] at heval
    exact neusisReal_of_cubic (P.coeff 3).2 (P.coeff 2).2 (P.coeff 1).2 (P.coeff 0).2 hlc
      (by linarith)
  · rw [h4] at hlc
    exact neusisReal_of_quartic (P.coeff 4).2 (P.coeff 3).2 (P.coeff 2).2 (P.coeff 1).2
      (P.coeff 0).2 hlc heval

end Neusis
