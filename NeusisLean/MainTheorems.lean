import NeusisLean.BaragarNecessity
import NeusisLean.QuinticSextic

/-!
# Main Theorems: Complete Characterization of Neusis Constructibility

This file proves the three main theorems resolving the neusis constructibility problem
for compass, straightedge, and strictly point-verging unit-mark neusis:

1. **Main Theorem 1 (Field Characterization):**
   - `neusisReal_iff_inDeg6Tower`: A real number `x` is neusis-constructible if and only if
     it lies in a real tower of field extensions `ℚ = K₀ ≤ K₁ ≤ ... ≤ Kᵣ ⊆ ℝ` with
     `[K_{i+1} : K_i] ≤ 6` at every step.
   - `neusisComplex_iff`: A complex number `z` is neusis-constructible if and only if both
     `z.re` and `z.im` lie in real degree-≤6 towers over `ℚ`.

2. **Main Theorem 2 (Regular `n`-gons):**
   - `regularPolygonConstructible_iff`: For `n ≥ 3`, the regular `n`-gon is
     neusis-constructible if and only if every prime divisor of `φ(n)` is at most `5`
     (equivalently, `φ(n) = 2^a 3^b 5^c`).

3. **Main Theorem 3 (General Quintics and Sextics):**
   - `neusisReal_of_real_sextic`: Every real root of every nonzero polynomial of degree `≤ 6`
     over `NeusisSubfield` is neusis-constructible.
   - `neusisComplex_of_real_quintic`: Every complex root of every nonzero polynomial of
     degree `≤ 5` over `NeusisSubfield` is neusis-constructible.
-/

namespace Neusis

open Polynomial

/-! ### Main Theorem 1: Field Characterization -/

/-- Every subfield of `ℝ` reachable by a real degree-≤6 tower over `ℚ` is contained in
`NeusisSubfield`. -/
theorem inDeg6Tower_le_neusisSubfield {K : Subfield ℝ} (hK : InDeg6Tower K) :
    K ≤ NeusisSubfield := by
  induction hK with
  | base => exact bot_le
  | @adjoin K α _ p hp hdeg hroot ih =>
    rw [Subfield.closure_le]
    intro x hx
    rcases hx with hxK | hxα
    · exact ih hxK
    · rw [Set.mem_singleton_iff] at hxα
      subst hxα
      let ι : K →+* NeusisSubfield := Subfield.inclusion ih
      have hι_inj : Function.Injective ι := fun a b hab =>
        Subtype.ext (congrArg (Subtype.val : NeusisSubfield → ℝ) hab)
      let p' : Polynomial NeusisSubfield := p.map ι
      have hp' : p' ≠ 0 := by
        intro h0
        exact hp (Polynomial.map_injective ι hι_inj (by simpa [p'] using h0))
      have hdeg' : p'.natDegree ≤ 6 := Polynomial.natDegree_map_le.trans hdeg
      have hroot' : Polynomial.aeval x p' = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap NeusisSubfield ℝ).comp ι = algebraMap K ℝ := rfl
        rw [hcomp]
        exact hroot
      exact neusisReal_of_poly_le6 p' hp' hdeg' hroot'

/-- **Main Theorem 1 (Real Field Characterization)**:
A real number `x` is neusis-constructible (by compass, straightedge, and point-verging
unit-mark neusis) if and only if it lies in a real degree-≤6 tower over `ℚ`. -/
theorem neusisReal_iff_inDeg6Tower (x : ℝ) : NeusisReal x ↔ RealInDeg6Tower x :=
  ⟨neusisReal_inDeg6Tower, fun ⟨_, hK, hx⟩ => inDeg6Tower_le_neusisSubfield hK hx⟩

/-- **Main Theorem 1 (Complex Plane Characterization)**:
A complex number `z` is neusis-constructible if and only if both `z.re` and `z.im` lie
in real degree-≤6 towers over `ℚ`. -/
theorem neusisComplex_iff (z : ℂ) :
    NeusisComplex z ↔ RealInDeg6Tower z.re ∧ RealInDeg6Tower z.im := by
  rw [NeusisComplex, neusisPoint_iff, neusisReal_iff_inDeg6Tower, neusisReal_iff_inDeg6Tower]

/-! ### Main Theorem 3: General Real Sextics and Complex Roots of Real Quintics -/

/-- **Main Theorem 3a (Real Roots of General Sextics)**:
Every real root of every nonzero polynomial of degree `≤ 6` over `NeusisSubfield` is
neusis-constructible. -/
theorem neusisReal_of_real_sextic (P : Polynomial NeusisSubfield) (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 6) {α : ℝ} (hroot : Polynomial.aeval α P = 0) :
    NeusisReal α :=
  neusisReal_of_poly_le6 P hP hdeg hroot

private lemma neusisComplex_iff_re_im (z : ℂ) :
    NeusisComplex z ↔ NeusisReal z.re ∧ NeusisReal z.im :=
  neusisPoint_iff

private lemma neusisComplex_ofReal {x : ℝ} (hx : NeusisReal x) : NeusisComplex (x : ℂ) := by
  rw [neusisComplex_iff_re_im]; exact ⟨hx, NeusisSubfield.zero_mem⟩

private lemma neusisComplex_neg {z : ℂ} (hz : NeusisComplex z) : NeusisComplex (-z) := by
  rw [neusisComplex_iff_re_im] at hz ⊢
  exact ⟨NeusisSubfield.neg_mem hz.1, NeusisSubfield.neg_mem hz.2⟩

private lemma neusisComplex_add {z w : ℂ} (hz : NeusisComplex z) (hw : NeusisComplex w) :
    NeusisComplex (z + w) := by
  rw [neusisComplex_iff_re_im] at hz hw ⊢
  exact ⟨NeusisSubfield.add_mem hz.1 hw.1, NeusisSubfield.add_mem hz.2 hw.2⟩

private lemma neusisComplex_sub {z w : ℂ} (hz : NeusisComplex z) (hw : NeusisComplex w) :
    NeusisComplex (z - w) := by
  rw [sub_eq_add_neg]; exact neusisComplex_add hz (neusisComplex_neg hw)

private lemma neusisComplex_mul {z w : ℂ} (hz : NeusisComplex z) (hw : NeusisComplex w) :
    NeusisComplex (z * w) := by
  rw [neusisComplex_iff_re_im] at hz hw ⊢
  rw [Complex.mul_re, Complex.mul_im]
  exact ⟨NeusisSubfield.sub_mem (NeusisSubfield.mul_mem hz.1 hw.1) (NeusisSubfield.mul_mem hz.2 hw.2),
         NeusisSubfield.add_mem (NeusisSubfield.mul_mem hz.1 hw.2) (NeusisSubfield.mul_mem hz.2 hw.1)⟩

private lemma neusisComplex_inv {z : ℂ} (hz : NeusisComplex z) : NeusisComplex z⁻¹ := by
  rw [neusisComplex_iff_re_im] at hz ⊢
  have hnorm : NeusisReal (z.re ^ 2 + z.im ^ 2) :=
    NeusisSubfield.add_mem (NeusisSubfield.pow_mem hz.1 2) (NeusisSubfield.pow_mem hz.2 2)
  have hnorm_eq : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply, sq]
  refine ⟨?_, ?_⟩
  · rw [Complex.inv_re, hnorm_eq]; exact NeusisSubfield.div_mem hz.1 hnorm
  · rw [Complex.inv_im, hnorm_eq]; exact NeusisSubfield.div_mem (NeusisSubfield.neg_mem hz.2) hnorm

private lemma neusisComplex_div {z w : ℂ} (hz : NeusisComplex z) (hw : NeusisComplex w) :
    NeusisComplex (z / w) := by
  rw [div_eq_mul_inv]; exact neusisComplex_mul hz (neusisComplex_inv hw)

private lemma neusisComplex_sqrt {z : ℂ} (hz : NeusisComplex z) :
    ∃ w : ℂ, w ^ 2 = z ∧ NeusisComplex w := by
  rw [neusisComplex_iff_re_im] at hz
  set a : ℝ := z.re
  set b : ℝ := z.im
  set r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hr_mem : NeusisReal r :=
    neusisReal_sqrt (NeusisSubfield.add_mem (NeusisSubfield.pow_mem hz.1 2) (NeusisSubfield.pow_mem hz.2 2))
      (by positivity)
  have h2_mem : NeusisReal 2 := subfield_natCast_mem NeusisSubfield 2
  have hra_nonneg : 0 ≤ (r + a) / 2 := by
    have : a ^ 2 ≤ r ^ 2 := by nlinarith
    have : -r ≤ a := by nlinarith
    linarith
  have hrma_nonneg : 0 ≤ (r - a) / 2 := by
    have : a ^ 2 ≤ r ^ 2 := by nlinarith
    have : a ≤ r := by nlinarith
    linarith
  set u : ℝ := Real.sqrt ((r + a) / 2)
  set v : ℝ := Real.sqrt ((r - a) / 2)
  have hu_mem : NeusisReal u :=
    neusisReal_sqrt (NeusisSubfield.div_mem (NeusisSubfield.add_mem hr_mem hz.1) h2_mem) hra_nonneg
  have hv_mem : NeusisReal v :=
    neusisReal_sqrt (NeusisSubfield.div_mem (NeusisSubfield.sub_mem hr_mem hz.1) h2_mem) hrma_nonneg
  have hu_sq : u ^ 2 = (r + a) / 2 := Real.sq_sqrt hra_nonneg
  have hv_sq : v ^ 2 = (r - a) / 2 := Real.sq_sqrt hrma_nonneg
  have huv_nonneg : 0 ≤ 2 * u * v := by positivity
  have huv_sq : (2 * u * v) ^ 2 = b ^ 2 := by
    have h1 : (2 * u * v) ^ 2 = 4 * u ^ 2 * v ^ 2 := by ring
    rw [h1, hu_sq, hv_sq]; linarith
  by_cases hb : 0 ≤ b
  · refine ⟨⟨u, v⟩, ?_, ?_⟩
    · apply Complex.ext
      · simp only [sq, Complex.mul_re]
        rw [← sq, ← sq, hu_sq, hv_sq]; ring
      · simp only [sq, Complex.mul_im]
        have : 2 * u * v = b := by nlinarith
        linarith
    · rw [neusisComplex_iff_re_im]; exact ⟨hu_mem, hv_mem⟩
  · push Not at hb
    refine ⟨⟨u, -v⟩, ?_, ?_⟩
    · apply Complex.ext
      · simp only [sq, Complex.mul_re]
        have : u * u - -v * -v = u ^ 2 - v ^ 2 := by ring
        rw [this, hu_sq, hv_sq]; ring
      · simp only [sq, Complex.mul_im]
        have : 2 * u * v = -b := by nlinarith
        linarith
    · rw [neusisComplex_iff_re_im]; exact ⟨hu_mem, NeusisSubfield.neg_mem hv_mem⟩

private lemma neusisComplex_of_complex_quadratic {a b c z : ℂ}
    (ha : NeusisComplex a) (hb : NeusisComplex b) (hc : NeusisComplex c)
    (ha0 : a ≠ 0) (hroot : a * z ^ 2 + b * z + c = 0) :
    NeusisComplex z := by
  have h2C : NeusisComplex 2 := neusisComplex_ofReal (subfield_natCast_mem NeusisSubfield 2)
  have h4C : NeusisComplex 4 := neusisComplex_ofReal (subfield_natCast_mem NeusisSubfield 4)
  set Δ : ℂ := b ^ 2 - 4 * a * c
  have hb2 : NeusisComplex (b ^ 2) := by rw [sq]; exact neusisComplex_mul hb hb
  have hΔ : NeusisComplex Δ :=
    neusisComplex_sub hb2 (neusisComplex_mul (neusisComplex_mul h4C ha) hc)
  rcases neusisComplex_sqrt hΔ with ⟨w, hw_sq, hwC⟩
  have hfac : (2 * a * z + b - w) * (2 * a * z + b + w) = 0 := by
    linear_combination 4 * a * hroot - hw_sq
  have h2a0 : (2 : ℂ) * a ≠ 0 := mul_ne_zero two_ne_zero ha0
  rcases mul_eq_zero.mp hfac with h1 | h2
  · have hz : z = (-b + w) / (2 * a) := by
      field_simp [h2a0]; linear_combination h1
    rw [hz]
    exact neusisComplex_div (neusisComplex_add (neusisComplex_neg hb) hwC) (neusisComplex_mul h2C ha)
  · have hz : z = (-b - w) / (2 * a) := by
      field_simp [h2a0]; linear_combination h2
    rw [hz]
    exact neusisComplex_div (neusisComplex_sub (neusisComplex_neg hb) hwC) (neusisComplex_mul h2C ha)

/-- Every real polynomial of odd degree has a real root. -/
private lemma exists_real_root_of_odd_degree (P : Polynomial ℝ) (hodd : Odd P.natDegree) :
    ∃ r : ℝ, P.eval r = 0 := by
  have hP : P ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hodd; exact Nat.not_odd_zero hodd
  set d := P.natDegree
  have hd_pos : 0 < d := by rcases hodd with ⟨k, hk⟩; omega
  set Q : Polynomial ℝ := Polynomial.C P.leadingCoeff⁻¹ * P
  have hlead_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hQ_mon : Q.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlead_ne]
  have hQ_deg : Q.natDegree = d := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlead_ne)]
  set M : ℝ := 1 + ∑ i ∈ Finset.range d, |Q.coeff i|
  have hM_ge1 : 1 ≤ M := by
    have : (0 : ℝ) ≤ ∑ i ∈ Finset.range d, |Q.coeff i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hM_pos : 0 < M := by linarith
  have hbound : ∀ x : ℝ, |x| = M →
      |∑ i ∈ Finset.range d, Q.coeff i * x ^ i| < M ^ d := by
    intro x hx
    have hle1 : |∑ i ∈ Finset.range d, Q.coeff i * x ^ i| ≤
        ∑ i ∈ Finset.range d, |Q.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
    have hle2 : ∑ i ∈ Finset.range d, |Q.coeff i * x ^ i| ≤
        ∑ i ∈ Finset.range d, |Q.coeff i| * M ^ (d - 1) := by
      apply Finset.sum_le_sum; intro i hi
      rw [Finset.mem_range] at hi
      rw [abs_mul, abs_pow, hx]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hM_ge1 (by omega)) (abs_nonneg _)
    have hsum_eq : ∑ i ∈ Finset.range d, |Q.coeff i| * M ^ (d - 1) =
        (M - 1) * M ^ (d - 1) := by
      rw [← Finset.sum_mul]; dsimp [M]; ring
    have hlt : (M - 1) * M ^ (d - 1) < M ^ d := by
      have hMd : M ^ d = M * M ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ, mul_comm]
      have hpow_pos : 0 < M ^ (d - 1) := pow_pos hM_pos _
      rw [hMd]; nlinarith
    linarith
  have hQ_eval : ∀ x : ℝ, Q.eval x = x ^ d + ∑ i ∈ Finset.range d, Q.coeff i * x ^ i := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (show Q.natDegree < d + 1 by omega),
      Finset.sum_range_succ]
    have hcd : Q.coeff d = 1 := by rw [← hQ_deg]; exact hQ_mon.leadingCoeff
    rw [hcd, one_mul, add_comm]
  have hpos : 0 < Q.eval M := by
    rw [hQ_eval]
    have := (abs_lt.mp (hbound M (abs_of_pos hM_pos))).1
    linarith
  have hneg : Q.eval (-M) < 0 := by
    rw [hQ_eval, hodd.neg_pow]
    have := (abs_lt.mp (hbound (-M) (by rw [abs_neg, abs_of_pos hM_pos]))).2
    linarith
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc (show -M ≤ M by linarith)
    Q.continuous.continuousOn ⟨le_of_lt hneg, le_of_lt hpos⟩
  refine ⟨r, ?_⟩
  simp only [Q, Polynomial.eval_mul, Polynomial.eval_C] at hr
  exact (mul_eq_zero.mp hr).resolve_left (inv_ne_zero hlead_ne)

private lemma isRoot_of_aeval_zero {P : Polynomial NeusisSubfield} {r : ℝ}
    (hr_mem : NeusisReal r) (hr_aeval : Polynomial.aeval r P = 0) :
    P.IsRoot ⟨r, hr_mem⟩ := by
  let rK : NeusisSubfield := ⟨r, hr_mem⟩
  have h1 : ((P.eval rK : NeusisSubfield) : ℝ) = Polynomial.aeval r P := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    push_cast
    rfl
  apply Subtype.ext
  change ((P.eval rK : NeusisSubfield) : ℝ) = 0
  rw [h1, hr_aeval]

/-- **Main Theorem 3b (Complex Roots of General Real Quintics)**:
Every complex root of every nonzero polynomial of degree `≤ 5` over `NeusisSubfield` is
neusis-constructible. -/
theorem neusisComplex_of_real_quintic (P : Polynomial NeusisSubfield) (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 5) {z : ℂ} (hroot : Polynomial.aeval z P = 0) :
    NeusisComplex z := by
  generalize hn : P.natDegree = n
  induction n using Nat.strongRecOn generalizing P with
  | ind n ih =>
    subst hn
    by_cases him : z.im = 0
    · have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
      have hrootR : Polynomial.aeval z.re P = 0 := by
        have hcomp : (algebraMap ℝ ℂ).comp (algebraMap NeusisSubfield ℝ) =
            algebraMap NeusisSubfield ℂ := rfl
        have hC : ((Polynomial.aeval z.re P : ℝ) : ℂ) = 0 := by
          change (algebraMap ℝ ℂ) (Polynomial.aeval z.re P) = 0
          rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp]
          change Polynomial.aeval (z.re : ℂ) P = 0
          rwa [← hz_eq]
        exact_mod_cast hC
      rw [hz_eq]
      exact neusisComplex_ofReal (neusisReal_of_poly_le6 P hP (by omega) hrootR)
    · have hcoeffC : ∀ k : ℕ, NeusisComplex ((P.coeff k : NeusisSubfield) : ℂ) := fun k =>
        neusisComplex_ofReal (P.coeff k).2
      have hlead_ne : ((P.leadingCoeff : NeusisSubfield) : ℂ) ≠ 0 := by
        intro h0
        apply Polynomial.leadingCoeff_ne_zero.mpr hP
        apply Subtype.ext
        exact_mod_cast h0
      have hP_eval : Polynomial.aeval z P =
          ∑ k ∈ Finset.range (P.natDegree + 1), ((P.coeff k : NeusisSubfield) : ℂ) * z ^ k := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
        rfl
      interval_cases hd : P.natDegree
      · exfalso
        rw [hP_eval] at hroot
        simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at hroot
        have : P.leadingCoeff = P.coeff 0 := by rw [Polynomial.leadingCoeff, hd]
        exact hlead_ne (by rw [this]; exact hroot)
      · rw [hP_eval, Finset.sum_range_succ, Finset.sum_range_one] at hroot
        simp only [pow_zero, mul_one, pow_one] at hroot
        have hc1_ne : ((P.coeff 1 : NeusisSubfield) : ℂ) ≠ 0 := by
          rwa [Polynomial.leadingCoeff, hd] at hlead_ne
        have hz : z = -((P.coeff 0 : NeusisSubfield) : ℂ) / ((P.coeff 1 : NeusisSubfield) : ℂ) := by
          field_simp [hc1_ne]; linear_combination hroot
        rw [hz]
        exact neusisComplex_div (neusisComplex_neg (hcoeffC 0)) (hcoeffC 1)
      · rw [hP_eval, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hroot
        simp only [pow_zero, mul_one, pow_one] at hroot
        have hc2_ne : ((P.coeff 2 : NeusisSubfield) : ℂ) ≠ 0 := by
          rwa [Polynomial.leadingCoeff, hd] at hlead_ne
        exact neusisComplex_of_complex_quadratic (hcoeffC 2) (hcoeffC 1) (hcoeffC 0) hc2_ne
          (by linear_combination hroot)
      · -- Degree 3: factor out a real root
        let Pℝ : Polynomial ℝ := P.map (algebraMap NeusisSubfield ℝ)
        have hPℝ_deg : Pℝ.natDegree = 3 := by
          rw [Polynomial.natDegree_map_eq_of_injective (algebraMap NeusisSubfield ℝ).injective, hd]
        obtain ⟨r, hr⟩ := exists_real_root_of_odd_degree Pℝ (by rw [hPℝ_deg]; exact ⟨1, rfl⟩)
        have hr_aeval : Polynomial.aeval r P = 0 := by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hr
        have hr_mem : NeusisReal r := neusisReal_of_poly_le6 P hP (by omega) hr_aeval
        let rK : NeusisSubfield := ⟨r, hr_mem⟩
        rcases Polynomial.dvd_iff_isRoot.mpr (isRoot_of_aeval_zero hr_mem hr_aeval) with ⟨Q, hPQ⟩
        have hQ_ne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hPQ; exact hP hPQ
        have hQ_deg : Q.natDegree = 2 := by
          have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero rK) hQ_ne
          rw [← hPQ, hd, Polynomial.natDegree_X_sub_C] at this; omega
        have hz_ne_r : z - (r : ℂ) ≠ 0 := by
          intro h0
          have := congrArg Complex.im h0
          simp at this
          exact him this
        have hQ_root : Polynomial.aeval z Q = 0 := by
          have h1 := congrArg (Polynomial.aeval z) hPQ
          rw [hroot, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h1
          exact (mul_eq_zero.mp h1.symm).resolve_left hz_ne_r
        exact ih 2 (by omega) Q hQ_ne (by omega) hQ_root hQ_deg
      · -- Degree 4: Ferrari's resolvent cubic over NeusisSubfield
        set c4 := P.coeff 4
        have hc4_ne : c4 ≠ 0 := by
          have := Polynomial.leadingCoeff_ne_zero.mpr hP
          rwa [Polynomial.leadingCoeff, hd] at this
        let d3 : NeusisSubfield := P.coeff 3 / c4
        let d2 : NeusisSubfield := P.coeff 2 / c4
        let d1 : NeusisSubfield := P.coeff 1 / c4
        let d0 : NeusisSubfield := P.coeff 0 / c4
        have hmon_root : z ^ 4 + ((d3 : ℝ) : ℂ) * z ^ 3 + ((d2 : ℝ) : ℂ) * z ^ 2 +
            ((d1 : ℝ) : ℂ) * z + ((d0 : ℝ) : ℂ) = 0 := by
          rw [hP_eval, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, Finset.sum_range_one] at hroot
          simp only [pow_zero, mul_one, pow_one] at hroot
          have hc4C : ((c4 : ℝ) : ℂ) ≠ 0 := by
            intro h0; exact hc4_ne (Subtype.ext (by exact_mod_cast h0))
          have hd3 : ((d3 : ℝ) : ℂ) = ((P.coeff 3 : ℝ) : ℂ) / ((c4 : ℝ) : ℂ) := by
            dsimp [d3]; push_cast; rfl
          have hd2 : ((d2 : ℝ) : ℂ) = ((P.coeff 2 : ℝ) : ℂ) / ((c4 : ℝ) : ℂ) := by
            dsimp [d2]; push_cast; rfl
          have hd1 : ((d1 : ℝ) : ℂ) = ((P.coeff 1 : ℝ) : ℂ) / ((c4 : ℝ) : ℂ) := by
            dsimp [d1]; push_cast; rfl
          have hd0 : ((d0 : ℝ) : ℂ) = ((P.coeff 0 : ℝ) : ℂ) / ((c4 : ℝ) : ℂ) := by
            dsimp [d0]; push_cast; rfl
          rw [hd3, hd2, hd1, hd0]
          field_simp [hc4C]
          linear_combination hroot
        let pK : NeusisSubfield := d2 - 3 * d3 ^ 2 / 8
        let qK : NeusisSubfield := d1 - d2 * d3 / 2 + d3 ^ 3 / 8
        let rK : NeusisSubfield := d0 - d1 * d3 / 4 + d2 * d3 ^ 2 / 16 - 3 * d3 ^ 4 / 256
        let w : ℂ := z + ((d3 : ℝ) : ℂ) / 4
        have hw_dep : w ^ 4 + ((pK : ℝ) : ℂ) * w ^ 2 + ((qK : ℝ) : ℂ) * w + ((rK : ℝ) : ℂ) = 0 := by
          have h2K : (((2 : NeusisSubfield) : ℝ) : ℂ) = 2 := rfl
          have h3K : (((3 : NeusisSubfield) : ℝ) : ℂ) = 3 := rfl
          have h4K : (((4 : NeusisSubfield) : ℝ) : ℂ) = 4 := rfl
          have h8K : (((8 : NeusisSubfield) : ℝ) : ℂ) = 8 := rfl
          have h16K : (((16 : NeusisSubfield) : ℝ) : ℂ) = 16 := rfl
          have h256K : (((256 : NeusisSubfield) : ℝ) : ℂ) = 256 := rfl
          have hpC : ((pK : ℝ) : ℂ) = ((d2 : ℝ) : ℂ) - 3 * ((d3 : ℝ) : ℂ) ^ 2 / 8 := by
            dsimp [pK]; push_cast; rw [h3K, h8K]
          have hqC : ((qK : ℝ) : ℂ) = ((d1 : ℝ) : ℂ) - ((d2 : ℝ) : ℂ) * ((d3 : ℝ) : ℂ) / 2 +
              ((d3 : ℝ) : ℂ) ^ 3 / 8 := by
            dsimp [qK]; push_cast; rw [h2K, h8K]
          have hrC : ((rK : ℝ) : ℂ) = ((d0 : ℝ) : ℂ) - ((d1 : ℝ) : ℂ) * ((d3 : ℝ) : ℂ) / 4 +
              ((d2 : ℝ) : ℂ) * ((d3 : ℝ) : ℂ) ^ 2 / 16 - 3 * ((d3 : ℝ) : ℂ) ^ 4 / 256 := by
            dsimp [rK]; push_cast; rw [h3K, h4K, h16K, h256K]
          rw [hpC, hqC, hrC]; dsimp [w]
          linear_combination hmon_root
        have hw_mem : NeusisComplex w := by
          by_cases hq0 : qK = 0
          · have hqC0 : ((qK : ℝ) : ℂ) = 0 := by rw [hq0]; simp
            rw [hqC0, zero_mul, add_zero] at hw_dep
            have hw2_mem : NeusisComplex (w ^ 2) :=
              neusisComplex_of_complex_quadratic
                (neusisComplex_ofReal NeusisSubfield.one_mem)
                (neusisComplex_ofReal pK.2)
                (neusisComplex_ofReal rK.2)
                (by norm_num) (by push_cast; linear_combination hw_dep)
            rcases neusisComplex_sqrt hw2_mem with ⟨u, hu_sq, huC⟩
            have hfac : (w - u) * (w + u) = 0 := by linear_combination -hu_sq
            rcases mul_eq_zero.mp hfac with h1 | h2
            · rwa [show w = u by linear_combination h1]
            · rw [show w = -u by linear_combination h2]; exact neusisComplex_neg huC
          · set pR : ℝ := (pK : ℝ)
            set qR : ℝ := (qK : ℝ)
            set rR : ℝ := (rK : ℝ)
            have hqR_ne : qR ≠ 0 := fun h0 => hq0 (Subtype.ext h0)
            have hqR_sq_pos : 0 < qR ^ 2 := sq_pos_of_ne_zero hqR_ne
            let R : Polynomial NeusisSubfield :=
              C 8 * Polynomial.X ^ 3 + C (8 * pK) * Polynomial.X ^ 2 +
              C (2 * pK ^ 2 - 8 * rK) * Polynomial.X - C (qK ^ 2)
            let fR : ℝ → ℝ := fun t => 8 * t ^ 3 + 8 * pR * t ^ 2 + (2 * pR ^ 2 - 8 * rR) * t - qR ^ 2
            have hfR_cont : Continuous fR := by dsimp [fR]; fun_prop
            have hfR_0 : fR 0 < 0 := by dsimp [fR]; linarith
            set M : ℝ := 1 + |pR| + |2 * pR ^ 2 - 8 * rR| + qR ^ 2
            have hM_ge1 : 1 ≤ M := by
              have : 0 ≤ |pR| + |2 * pR ^ 2 - 8 * rR| + qR ^ 2 := by positivity
              linarith
            have hfR_M : 0 < fR M := by
              dsimp [fR]
              have h1 : -|pR| ≤ pR := neg_abs_le pR
              have h2 : -|2 * pR ^ 2 - 8 * rR| ≤ 2 * pR ^ 2 - 8 * rR := neg_abs_le _
              have hM_sq : M ≤ M ^ 2 := by nlinarith
              have h8M3 : 8 * M ^ 3 ≥ 8 * (1 + |pR|) * M ^ 2 := by
                have : 1 + |pR| ≤ M := by
                  have : 0 ≤ |2 * pR ^ 2 - 8 * rR| + qR ^ 2 := by positivity
                  linarith
                nlinarith
              have h8M2 : 8 * M ^ 2 ≥ 8 * M * (|2 * pR ^ 2 - 8 * rR| + qR ^ 2) := by
                have : |2 * pR ^ 2 - 8 * rR| + qR ^ 2 ≤ M := by
                  have : 0 ≤ 1 + |pR| := by positivity
                  linarith
                nlinarith
              nlinarith [abs_nonneg pR, abs_nonneg (2 * pR ^ 2 - 8 * rR)]
            obtain ⟨t, htI, ht_root⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ M by linarith)
              hfR_cont.continuousOn ⟨le_of_lt hfR_0, le_of_lt hfR_M⟩
            have ht_pos : 0 < t := by
              rcases lt_or_eq_of_le htI.1 with hlt | rfl
              · exact hlt
              · linarith
            have hR_eval : ∀ x : ℝ, Polynomial.aeval x R = fR x := by
              intro x; dsimp [R, fR, pR, qR, rR]
              simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
              change 8 * x ^ 3 + 8 * (pK : ℝ) * x ^ 2 + (2 * (pK : ℝ) ^ 2 - 8 * (rK : ℝ)) * x - (qK : ℝ) ^ 2 = _
              rfl
            have hR_ne : R ≠ 0 := by
              intro h0; have := hR_eval 0; rw [h0, map_zero] at this; linarith
            have hR_deg : R.natDegree ≤ 6 := by
              have h3 : (C (8 : NeusisSubfield) * Polynomial.X ^ 3).natDegree ≤ 3 :=
                natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow, zero_add, le_refl])
              have h2 : (C (8 * pK) * Polynomial.X ^ 2).natDegree ≤ 2 :=
                natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow, zero_add, le_refl])
              have h1 : (C (2 * pK ^ 2 - 8 * rK) * Polynomial.X).natDegree ≤ 1 :=
                natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl])
              have h32 : (C (8 : NeusisSubfield) * Polynomial.X ^ 3 + C (8 * pK) * Polynomial.X ^ 2).natDegree ≤ 3 :=
                (natDegree_add_le _ _).trans (max_le h3 (by omega))
              have h321 : (C (8 : NeusisSubfield) * Polynomial.X ^ 3 + C (8 * pK) * Polynomial.X ^ 2 +
                  C (2 * pK ^ 2 - 8 * rK) * Polynomial.X).natDegree ≤ 3 :=
                (natDegree_add_le _ _).trans (max_le h32 (by omega))
              have hsub : R.natDegree ≤ 3 :=
                (natDegree_sub_le _ _).trans (max_le h321 (by simp only [natDegree_C, Nat.zero_le]))
              omega
            have ht_mem : NeusisReal t :=
              neusisReal_of_poly_le6 R hR_ne hR_deg (by rw [hR_eval]; exact ht_root)
            set m : ℝ := Real.sqrt (2 * t)
            have hm_pos : 0 < m := Real.sqrt_pos.mpr (by linarith)
            have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm_pos
            have hm_sq : m ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
            have hm_mem : NeusisReal m :=
              neusisReal_sqrt (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) ht_mem)
                (by linarith)
            have hfac : (w ^ 2 + (m : ℂ) * w + ((pR / 2 + t - qR / (2 * m) : ℝ) : ℂ)) *
                (w ^ 2 - (m : ℂ) * w + ((pR / 2 + t + qR / (2 * m) : ℝ) : ℂ)) = 0 := by
              have hmsqC : (m : ℂ) ^ 2 = 2 * (t : ℂ) := by exact_mod_cast hm_sq
              have hcubC : 8 * (t : ℂ) ^ 3 + 8 * (pR : ℂ) * (t : ℂ) ^ 2 +
                  (2 * (pR : ℂ) ^ 2 - 8 * (rR : ℂ)) * (t : ℂ) - (qR : ℂ) ^ 2 = 0 := by
                exact_mod_cast ht_root
              push_cast
              have h2m_ne : (2 : ℂ) * (m : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hm_ne
              have h4m2_ne : (4 : ℂ) * (m : ℂ) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hm_ne)
              apply mul_left_cancel₀ h4m2_ne
              rw [mul_zero]
              have h1 : (4 : ℂ) * (m : ℂ) ^ 2 *
                  ((w ^ 2 + (m : ℂ) * w + ((pR : ℂ) / 2 + (t : ℂ) - (qR : ℂ) / (2 * (m : ℂ)))) *
                  (w ^ 2 - (m : ℂ) * w + ((pR : ℂ) / 2 + (t : ℂ) + (qR : ℂ) / (2 * (m : ℂ))))) =
                  4 * (m : ℂ) ^ 2 * (w ^ 4 + (pR : ℂ) * w ^ 2 + (qR : ℂ) * w + (rR : ℂ)) +
                  4 * (m : ℂ) ^ 2 * (2 * (t : ℂ) - (m : ℂ) ^ 2) * w ^ 2 +
                  ((m : ℂ) ^ 2 * ((pR : ℂ) + 2 * (t : ℂ)) ^ 2 - 4 * (m : ℂ) ^ 2 * (rR : ℂ) - (qR : ℂ) ^ 2) := by
                field_simp [hm_ne, h2m_ne]; ring
              rw [h1]
              have hdep' : w ^ 4 + (pR : ℂ) * w ^ 2 + (qR : ℂ) * w + (rR : ℂ) = 0 := hw_dep
              rw [hdep', hmsqC]
              linear_combination hcubC
            have h2m : NeusisReal (2 * m) :=
              NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) hm_mem
            have hp2t : NeusisReal (pR / 2 + t) :=
              NeusisSubfield.add_mem
                (NeusisSubfield.div_mem pK.2 (subfield_natCast_mem NeusisSubfield 2)) ht_mem
            have hq2m : NeusisReal (qR / (2 * m)) := NeusisSubfield.div_mem qK.2 h2m
            rcases mul_eq_zero.mp hfac with h1 | h2
            · exact neusisComplex_of_complex_quadratic
                (neusisComplex_ofReal NeusisSubfield.one_mem)
                (neusisComplex_ofReal hm_mem)
                (neusisComplex_ofReal (NeusisSubfield.sub_mem hp2t hq2m))
                (by norm_num) (by rw [Complex.ofReal_one]; linear_combination h1)
            · exact neusisComplex_of_complex_quadratic
                (neusisComplex_ofReal NeusisSubfield.one_mem)
                (neusisComplex_neg (neusisComplex_ofReal hm_mem))
                (neusisComplex_ofReal (NeusisSubfield.add_mem hp2t hq2m))
                (by norm_num) (by rw [Complex.ofReal_one]; linear_combination h2)
        have hz_eq : z = w - ((d3 : ℝ) : ℂ) / 4 := by dsimp [w]; ring
        rw [hz_eq]
        exact neusisComplex_sub hw_mem
          (neusisComplex_div (neusisComplex_ofReal d3.2)
            (neusisComplex_ofReal (subfield_natCast_mem NeusisSubfield 4)))
      · -- Degree 5: factor out a real root, reducing to degree 4
        let Pℝ : Polynomial ℝ := P.map (algebraMap NeusisSubfield ℝ)
        have hPℝ_deg : Pℝ.natDegree = 5 := by
          rw [Polynomial.natDegree_map_eq_of_injective (algebraMap NeusisSubfield ℝ).injective, hd]
        obtain ⟨r, hr⟩ := exists_real_root_of_odd_degree Pℝ (by rw [hPℝ_deg]; exact ⟨2, rfl⟩)
        have hr_aeval : Polynomial.aeval r P = 0 := by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hr
        have hr_mem : NeusisReal r := neusisReal_of_poly_le6 P hP (by omega) hr_aeval
        let rK : NeusisSubfield := ⟨r, hr_mem⟩
        rcases Polynomial.dvd_iff_isRoot.mpr (isRoot_of_aeval_zero hr_mem hr_aeval) with ⟨Q, hPQ⟩
        have hQ_ne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hPQ; exact hP hPQ
        have hQ_deg : Q.natDegree = 4 := by
          have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero rK) hQ_ne
          rw [← hPQ, hd, Polynomial.natDegree_X_sub_C] at this; omega
        have hz_ne_r : z - (r : ℂ) ≠ 0 := by
          intro h0
          have := congrArg Complex.im h0
          simp at this
          exact him this
        have hQ_root : Polynomial.aeval z Q = 0 := by
          have h1 := congrArg (Polynomial.aeval z) hPQ
          rw [hroot, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h1
          exact (mul_eq_zero.mp h1.symm).resolve_left hz_ne_r
        exact ih 4 (by omega) Q hQ_ne (by omega) hQ_root hQ_deg

/-! ### Main Theorem 2: Regular `n`-gon Characterization -/

private lemma subfield_ratCast_mem (K : Subfield ℝ) (q : ℚ) : (q : ℝ) ∈ K := by
  rw [Rat.cast_def]
  exact K.div_mem (K.intCast_mem q.num) (subfield_natCast_mem K q.den)

/-- Promote any `Subfield ℝ` to an `IntermediateField ℚ ℝ` with the exact same carrier. -/
private noncomputable def subfieldToIF (K : Subfield ℝ) : IntermediateField ℚ ℝ :=
  K.toIntermediateField fun q => subfield_ratCast_mem K q

/-- Any real degree-≤6 tower `K` over `ℚ` is finite-dimensional over `ℚ`, and every prime
divisor of `[K : ℚ]` is at most `5`. -/
private lemma inDeg6Tower_finrank_prime_le5 {K : Subfield ℝ} (hK : InDeg6Tower K) :
    FiniteDimensional ℚ (subfieldToIF K) ∧
      ∀ p : ℕ, p.Prime → p ∣ Module.finrank ℚ (subfieldToIF K) → p ≤ 5 := by
  induction hK with
  | base =>
    have hbot : subfieldToIF (⊥ : Subfield ℝ) = (⊥ : IntermediateField ℚ ℝ) := by
      ext x
      constructor
      · intro hx
        have hle : (⊥ : Subfield ℝ) ≤ (⊥ : IntermediateField ℚ ℝ).toSubfield := bot_le
        exact hle hx
      · intro hx
        rw [IntermediateField.mem_bot] at hx
        rcases hx with ⟨q, rfl⟩
        exact subfield_ratCast_mem (⊥ : Subfield ℝ) q
    rw [hbot]
    refine ⟨inferInstance, fun p hp hdvd => ?_⟩
    rw [IntermediateField.finrank_bot] at hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hp.ne_one
  | @adjoin K α _ p hp hdeg hroot ih =>
    rcases ih with ⟨hfinK, hprimeK⟩
    let K' : Subfield ℝ := Subfield.closure ((K : Set ℝ) ∪ {α})
    let E : IntermediateField K ℝ := IntermediateField.adjoin K ({α} : Set ℝ)
    have hcarrier : ∀ x : ℝ, x ∈ K' ↔ x ∈ E := by
      intro x
      constructor
      · intro hx
        have hle : K' ≤ E.toSubfield := by
          rw [Subfield.closure_le]
          intro y hy
          rcases hy with hyK | hyα
          · exact E.algebraMap_mem ⟨y, hyK⟩
          · rw [Set.mem_singleton_iff] at hyα; subst hyα
            exact IntermediateField.subset_adjoin K {y} (Set.mem_singleton y)
        exact hle hx
      · intro hx
        let K'_IF : IntermediateField K ℝ :=
          K'.toIntermediateField fun y => Subfield.subset_closure (Or.inl y.2)
        have hle : E ≤ K'_IF := IntermediateField.adjoin_le_iff.mpr (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy; subst hy
          exact Subfield.subset_closure (Or.inr (Set.mem_singleton y)))
        exact hle hx
    have hα_int : IsIntegral K α := by
      refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, ?_, ?_⟩
      · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)]
      · rw [Polynomial.eval₂_mul, show Polynomial.eval₂ (algebraMap K ℝ) α p = 0 from hroot, zero_mul]
    let e_KE : (subfieldToIF K') ≃ₗ[ℚ] E :=
      { toFun := fun x => ⟨x.1, (hcarrier x.1).mp x.2⟩
        invFun := fun x => ⟨x.1, (hcarrier x.1).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hfin_E_K : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hα_int
    have hfin_K_Q : FiniteDimensional ℚ K := hfinK
    have hfin_E_Q : FiniteDimensional ℚ E := Module.Finite.trans K E
    have hfin_K'_Q : FiniteDimensional ℚ (subfieldToIF K') := Module.Finite.equiv e_KE.symm
    have hfr_E_K : Module.finrank K E ≤ 6 := by
      rw [IntermediateField.adjoin.finrank hα_int]
      exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K α hroot) hp).trans hdeg
    have hfr_eq : Module.finrank ℚ (subfieldToIF K') =
        Module.finrank ℚ K * Module.finrank K E := by
      rw [e_KE.finrank_eq]
      exact (Module.finrank_mul_finrank ℚ K E).symm
    refine ⟨hfin_K'_Q, fun q hq hdvd => ?_⟩
    rw [hfr_eq] at hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact hprimeK q hq h1
    · have hpos : 0 < Module.finrank K E := Module.finrank_pos
      have hle6 : q ≤ 6 := (Nat.le_of_dvd hpos h2).trans hfr_E_K
      have hne6 : q ≠ 6 := by intro h; rw [h] at hq; norm_num at hq
      omega

/-- Every `n`-th primitive root of unity `ζ = exp(2πi/n)` has minimal polynomial
`cyclotomic n ℚ` over `ℚ`. -/
private lemma minpoly_exp_two_pi_I_div (n : ℕ) (hn : 0 < n) :
    minpoly ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) = Polynomial.cyclotomic n ℚ := by
  have hprim := Complex.isPrimitiveRoot_exp n (Nat.pos_iff_ne_zero.mp hn)
  have hroot : Polynomial.aeval (Complex.exp (2 * Real.pi * Complex.I / n))
      (Polynomial.cyclotomic n ℚ) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hprim.isRoot_cyclotomic hn
  exact (minpoly.eq_of_irreducible_of_monic
    (Polynomial.cyclotomic.irreducible_rat hn) hroot
    (Polynomial.cyclotomic.monic n ℚ)).symm

private lemma regularPolygon_necessity {n : ℕ} (hn : 3 ≤ n)
    (hreg : RegularPolygonConstructible n) :
    ∀ p : ℕ, p.Prime → p ∣ n.totient → p ≤ 5 := by
  have hn_pos : 0 < n := by omega
  have hn_ne : n ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn_ne
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := minpoly_exp_two_pi_I_div n hn_pos
  have hζ_int : IsIntegral ℚ ζ := by
    refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic.monic n ℚ, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hprim.isRoot_cyclotomic hn_pos
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have hL_fin : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hζ_int
  have hL_fr : Module.finrank ℚ L = n.totient := by
    rw [IntermediateField.adjoin.finrank hζ_int, hmin, Polynomial.natDegree_cyclotomic]
  rw [RegularPolygonConstructible, neusisComplex_iff] at hreg
  rcases hreg.1 with ⟨K₁, hK₁, hre⟩
  rcases hreg.2 with ⟨K₂, hK₂, him⟩
  let K : Subfield ℝ := K₁ ⊔ K₂
  have hK : InDeg6Tower K := inDeg6Tower_sup hK₁ hK₂
  have hle1 : K₁ ≤ K := le_sup_left
  have hle2 : K₂ ≤ K := le_sup_right
  rcases inDeg6Tower_finrank_prime_le5 hK with ⟨hfinK, hprimeK⟩
  let K_C : IntermediateField ℚ ℂ :=
    (subfieldToIF K).map (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have hK_C_eq : Module.finrank ℚ K_C = Module.finrank ℚ (subfieldToIF K) := by
    let e : (subfieldToIF K) ≃ₐ[ℚ] K_C :=
      IntermediateField.equivMap (subfieldToIF K) (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    exact e.toLinearEquiv.finrank_eq.symm
  have hfin_KC : FiniteDimensional ℚ K_C := by
    let e : (subfieldToIF K) ≃ₐ[ℚ] K_C :=
      IntermediateField.equivMap (subfieldToIF K) (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    exact Module.Finite.equiv e.toLinearEquiv
  let M : IntermediateField K_C ℂ := IntermediateField.adjoin K_C ({Complex.I} : Set ℂ)
  have hI_int : IsIntegral K_C Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C 1 (by norm_num), ?_⟩
    simp [Complex.I_sq]
  have hfin_M_KC : FiniteDimensional K_C M := IntermediateField.adjoin.finiteDimensional hI_int
  have hfin_M_Q : FiniteDimensional ℚ M := Module.Finite.trans K_C M
  have hfr_M_KC : Module.finrank K_C M ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hI_int]
    have hrootI : Polynomial.aeval Complex.I (Polynomial.X ^ 2 + 1 : Polynomial K_C) = 0 := by
      simp [Complex.I_sq]
    have hneI : (Polynomial.X ^ 2 + 1 : Polynomial K_C) ≠ 0 :=
      (Polynomial.monic_X_pow_add_C (1 : K_C) (by norm_num)).ne_zero
    have hdegI : (Polynomial.X ^ 2 + 1 : Polynomial K_C).natDegree ≤ 2 :=
      (Polynomial.natDegree_add_le _ _).trans (by simp)
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K_C Complex.I hrootI) hneI).trans hdegI
  let M_Q : IntermediateField ℚ ℂ := M.restrictScalars ℚ
  have hζ_mem_M : ζ ∈ M_Q := by
    have hre_KC : (ζ.re : ℂ) ∈ K_C := ⟨ζ.re, hle1 hre, rfl⟩
    have him_KC : (ζ.im : ℂ) ∈ K_C := ⟨ζ.im, hle2 him, rfl⟩
    have hre_M : (ζ.re : ℂ) ∈ M := M.algebraMap_mem ⟨(ζ.re : ℂ), hre_KC⟩
    have him_M : (ζ.im : ℂ) ∈ M := M.algebraMap_mem ⟨(ζ.im : ℂ), him_KC⟩
    have hI_M : Complex.I ∈ M := IntermediateField.subset_adjoin K_C {Complex.I} (Set.mem_singleton _)
    have hsum : (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I = ζ := Complex.re_add_im ζ
    rw [← hsum]
    exact M.add_mem hre_M (M.mul_mem him_M hI_M)
  have hL_le_M : L ≤ M_Q :=
    IntermediateField.adjoin_le_iff.mpr (by
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hζ_mem_M)
  let M_over_L : IntermediateField L ℂ := IntermediateField.extendScalars hL_le_M
  let e_ML : M_over_L ≃ₗ[ℚ] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfin_ML_Q : FiniteDimensional ℚ M_over_L := Module.Finite.equiv e_ML.symm
  have hfin_ML_L : FiniteDimensional L M_over_L := Module.Finite.of_restrictScalars_finite ℚ L M_over_L
  have hdvd_tot : n.totient ∣ Module.finrank ℚ M := by
    rw [← hL_fr, ← e_ML.finrank_eq]
    exact ⟨Module.finrank L M_over_L, (Module.finrank_mul_finrank ℚ L M_over_L).symm⟩
  have hfr_M_Q : Module.finrank ℚ M = Module.finrank ℚ K_C * Module.finrank K_C M :=
    (Module.finrank_mul_finrank ℚ K_C M).symm
  intro p hp hdvd
  have hdvd2 : p ∣ Module.finrank ℚ K_C * Module.finrank K_C M := by
    rw [← hfr_M_Q]; exact hdvd.trans hdvd_tot
  rcases hp.dvd_mul.mp hdvd2 with h1 | h2
  · rw [hK_C_eq] at h1; exact hprimeK p hp h1
  · have hpos : 0 < Module.finrank K_C M := Module.finrank_pos
    have hle2 : p ≤ 2 := (Nat.le_of_dvd hpos h2).trans hfr_M_KC
    omega

/-- Helper to avoid nested `IntermediateField` typeclass search in `Module.finrank_mul_finrank`. -/
private lemma intermediateField_tower_finrank (K L : Type*) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) :
    Module.finrank K E * Module.finrank E L = Module.finrank K L :=
  Module.finrank_mul_finrank K E L

/-- Helper to avoid nested `IntermediateField` typeclass search in `minpoly.natDegree_le`. -/
private lemma field_minpoly_natDegree_le (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (x : E) :
    (minpoly K x).natDegree ≤ Module.finrank K E :=
  minpoly.natDegree_le x

/-- One step of Galois descent: if `H ≤ H'` are subgroups of `Gal(L/ℚ)` with `Nat.card H' = p * Nat.card H`
and `p ≤ 6`, and every element of `fixedField H'` is real and lies in `NeusisSubfield`,
then every real element of `fixedField H` lies in `NeusisSubfield`. -/
private lemma galois_descent_step {L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L]
    {H H' : Subgroup (L ≃ₐ[ℚ] L)} (hH_le : H ≤ H') {p : ℕ} (hp_le6 : p ≤ 6)
    (hcard_rel : Nat.card H' = p * Nat.card H)
    (hF'_im : ∀ y ∈ IntermediateField.fixedField H', (y.1 : ℂ).im = 0)
    (hF'_mem : ∀ y ∈ IntermediateField.fixedField H', NeusisReal (y.1 : ℂ).re)
    {x : L} (hx : x ∈ IntermediateField.fixedField H) (hx_im : (x.1 : ℂ).im = 0) :
    NeusisReal (x.1 : ℂ).re := by
  let F' : IntermediateField ℚ L := IntermediateField.fixedField H'
  let F : IntermediateField ℚ L := IntermediateField.fixedField H
  have hF'_le_F : F' ≤ F := fun y hy g => hy ⟨g.1, hH_le g.2⟩
  let F_ext : IntermediateField F' L := IntermediateField.extendScalars hF'_le_F
  have hfin_F'_L : FiniteDimensional F' L := Module.Finite.of_restrictScalars_finite ℚ F' L
  have hfin_F_L : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  have hfin_Fext_L : FiniteDimensional F_ext L := Module.Finite.of_restrictScalars_finite F' F_ext L
  have hfin_F'_Fext : FiniteDimensional F' F_ext :=
    Submodule.finiteDimensional_of_le (le_top : F_ext.toSubalgebra.toSubmodule ≤ ⊤)
  let e_ring : F_ext ≃+* F :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have : RingHomInvPair e_ring.toRingHom e_ring.symm.toRingHom :=
    ⟨RingHom.ext e_ring.left_inv, RingHom.ext e_ring.right_inv⟩
  have : RingHomInvPair e_ring.symm.toRingHom e_ring.toRingHom :=
    ⟨RingHom.ext e_ring.right_inv, RingHom.ext e_ring.left_inv⟩
  let e_L : L ≃ₛₗ[e_ring.toRingHom] L :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfr_Fext_L : Module.finrank F_ext L = Module.finrank F L := e_L.finrank_eq
  have hfr_F_L : Module.finrank F L = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  have hfr_F'_L : Module.finrank F' L = Nat.card H' :=
    IntermediateField.finrank_fixedField_eq_card H'
  have hfr_FF' : Module.finrank F' F_ext = p := by
    have hmul : Module.finrank F' F_ext * Module.finrank F_ext L = Module.finrank F' L :=
      intermediateField_tower_finrank F' L F_ext
    rw [hfr_Fext_L, hfr_F_L, hfr_F'_L, hcard_rel] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  let xF : F_ext := ⟨x, hx⟩
  have hxF_int : IsIntegral F' xF := Algebra.IsIntegral.isIntegral xF
  let P : Polynomial F' := minpoly F' xF
  have hP_ne : P ≠ 0 := minpoly.ne_zero hxF_int
  have hP_deg : P.natDegree ≤ 6 := by
    have := field_minpoly_natDegree_le F' F_ext xF
    rw [hfr_FF'] at this
    exact this.trans hp_le6
  have hF'_eq_re : ∀ y : F', (y.1.1 : ℂ) = ((y.1.1 : ℂ).re : ℂ) := fun y =>
    Complex.ext rfl (by simp [hF'_im y.1 y.2])
  let φ : F' →+* NeusisSubfield :=
    { toFun := fun y => ⟨(y.1.1 : ℂ).re, hF'_mem y.1 y.2⟩
      map_one' := Subtype.ext (by change (1 : ℂ).re = 1; simp)
      map_mul' := fun a b => Subtype.ext (by
        change (a.1.1 * b.1.1 : ℂ).re = (a.1.1 : ℂ).re * (b.1.1 : ℂ).re
        rw [Complex.mul_re, hF'_im a.1 a.2, hF'_im b.1 b.2]; ring)
      map_zero' := Subtype.ext (by change (0 : ℂ).re = 0; simp)
      map_add' := fun a b => Subtype.ext (by
        change (a.1.1 + b.1.1 : ℂ).re = (a.1.1 : ℂ).re + (b.1.1 : ℂ).re
        exact Complex.add_re _ _) }
  let P_N : Polynomial NeusisSubfield := P.map φ
  have hP_N_ne : P_N ≠ 0 := by
    intro h0
    exact hP_ne (Polynomial.map_injective φ φ.injective (by simpa [P_N] using h0))
  have hP_N_deg : P_N.natDegree ≤ 6 := Polynomial.natDegree_map_le.trans hP_deg
  have hP_N_root : Polynomial.aeval (x.1 : ℂ).re P_N = 0 := by
    have hC_root : ((Polynomial.aeval (x.1 : ℂ).re P_N : ℝ) : ℂ) = 0 := by
      change (algebraMap ℝ ℂ) (Polynomial.aeval (x.1 : ℂ).re P_N) = 0
      have hcomp1 : (algebraMap ℝ ℂ).comp (algebraMap NeusisSubfield ℝ) =
          algebraMap NeusisSubfield ℂ := rfl
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp1]
      dsimp [P_N]
      rw [Polynomial.eval₂_map]
      let ιFL : F_ext →+* ℂ := (algebraMap L ℂ).comp (algebraMap F_ext L)
      have hcomp2 : (algebraMap NeusisSubfield ℂ).comp φ = ιFL.comp (algebraMap F' F_ext) := by
        ext y
        change (((y.1.1 : ℂ).re : ℂ)) = y.1.1
        exact (hF'_eq_re y).symm
      rw [hcomp2]
      have hx_re : ((x.1 : ℂ).re : ℂ) = ιFL xF := by
        change ((x.1 : ℂ).re : ℂ) = x.1
        apply Complex.ext
        · exact Complex.ofReal_re _
        · rw [Complex.ofReal_im, hx_im]
      rw [hx_re, ← Polynomial.hom_eval₂]
      have hmin0 : Polynomial.eval₂ (algebraMap F' F_ext) xF P = 0 := minpoly.aeval F' xF
      rw [hmin0, map_zero]
    exact_mod_cast hC_root
  exact neusisReal_of_poly_le6 P_N hP_N_ne hP_N_deg hP_N_root

private lemma exp_two_pi_I_div_parts {n : ℕ} :
    let ζ := Complex.exp (2 * Real.pi * Complex.I / n)
    starRingEnd ℂ ζ = ζ⁻¹ ∧
    ((Real.cos (2 * Real.pi / n) : ℝ) : ℂ) = (ζ + ζ⁻¹) / 2 ∧
    ζ.re = Real.cos (2 * Real.pi / n) ∧
    ζ.im = Real.sin (2 * Real.pi / n) := by
  intro ζ
  have h1 : ζ = ((Real.cos (2 * Real.pi / n) : ℝ) : ℂ) +
      ((Real.sin (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I := by
    dsimp [ζ]
    rw [show (2 * ↑Real.pi * Complex.I / ↑n : ℂ) = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := by
    dsimp [ζ]
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  have h2 : ζ⁻¹ = ((Real.cos (2 * Real.pi / n) : ℝ) : ℂ) -
      ((Real.sin (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I := by
    rw [← hconj, h1, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  refine ⟨hconj, by rw [h2, h1]; ring, ?_, ?_⟩
  · rw [h1]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]; ring
  · rw [h1]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.I_im]; ring

private lemma regularPolygon_of_neusisReal_cos {n : ℕ} (hn : 3 ≤ n)
    (hcos : NeusisReal (Real.cos (2 * Real.pi / n))) :
    RegularPolygonConstructible n := by
  rcases exp_two_pi_I_div_parts (n := n) with ⟨_, _, hre_eq, him_eq⟩
  have hsin_nonneg : 0 ≤ Real.sin (2 * Real.pi / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpi : 0 < Real.pi := Real.pi_pos
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
      nlinarith
  have hsin_eq : Real.sin (2 * Real.pi / n) = Real.sqrt (1 - Real.cos (2 * Real.pi / n) ^ 2) := by
    have hsq : Real.sin (2 * Real.pi / n) ^ 2 = 1 - Real.cos (2 * Real.pi / n) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (2 * Real.pi / n)]
    rw [← hsq, Real.sqrt_sq hsin_nonneg]
  have hsin_real : NeusisReal (Real.sin (2 * Real.pi / n)) := by
    rw [hsin_eq]
    exact neusisReal_sqrt
      (NeusisSubfield.sub_mem NeusisSubfield.one_mem (NeusisSubfield.pow_mem hcos 2))
      (by nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi / n)])
  rw [RegularPolygonConstructible, neusisComplex_iff_re_im]
  exact ⟨hre_eq ▸ hcos, him_eq ▸ hsin_real⟩

/-- The cyclotomic subfield `ℚ(exp(2πi/n)) ⊆ ℂ` is finite Galois over `ℚ`, of degree `φ(n)`,
generated as a `ℚ`-algebra by `ζ = exp(2πi/n)`. -/
private lemma cyclotomic_field_isGalois {n : ℕ} (hn : 3 ≤ n) :
    let ζ := Complex.exp (2 * Real.pi * Complex.I / n)
    let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
    FiniteDimensional ℚ L ∧
    Module.finrank ℚ L = n.totient ∧
    IsGalois ℚ L ∧
    ∀ hζL : ζ ∈ L, Algebra.adjoin ℚ ({(⟨ζ, hζL⟩ : L)} : Set L) = ⊤ := by
  intro ζ L
  have hn_pos : 0 < n := by omega
  have hn_ne : n ≠ 0 := by omega
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn_ne
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := minpoly_exp_two_pi_I_div n hn_pos
  have hζ_int : IsIntegral ℚ ζ := by
    refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic.monic n ℚ, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hprim.isRoot_cyclotomic hn_pos
  have hL_fin : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hζ_int
  have hL_fr : Module.finrank ℚ L = n.totient := by
    rw [IntermediateField.adjoin.finrank hζ_int, hmin, Polynomial.natDegree_cyclotomic]
  have hζL : ζ ∈ L := IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)
  let ζL : L := ⟨ζ, hζL⟩
  have hζL_prim : IsPrimitiveRoot ζL n := by
    have hinj : Function.Injective (algebraMap L ℂ) := Subtype.val_injective
    exact (IsPrimitiveRoot.map_iff_of_injective hinj).mp hprim
  have htop_ζ : Algebra.adjoin ℚ ({ζL} : Set L) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hmem_adjoin : x.1 ∈ Algebra.adjoin ℚ ({ζ} : Set ℂ) := by
      have hsub := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ_int.isAlgebraic
      have hx' : x.1 ∈ (IntermediateField.adjoin ℚ ({ζ} : Set ℂ)).toSubalgebra := x.2
      rwa [hsub] at hx'
    have hmap_eq : (Algebra.adjoin ℚ ({ζL} : Set L)).map (IsScalarTower.toAlgHom ℚ L ℂ) =
        Algebra.adjoin ℚ ({ζ} : Set ℂ) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
    rw [← hmap_eq] at hmem_adjoin
    rcases hmem_adjoin with ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hPL_eq : (Polynomial.X ^ n - 1 : Polynomial ℚ).map (algebraMap ℚ L) =
      Polynomial.X ^ n - 1 := by simp
  have hPL_ne : (Polynomial.X ^ n - 1 : Polynomial L) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C (1 : L) hn_ne).ne_zero
  have hPL_deg : (Polynomial.X ^ n - 1 : Polynomial L).natDegree = n := by
    rw [← (Polynomial.C_1 : Polynomial.C (1 : L) = 1)]
    exact Polynomial.natDegree_X_pow_sub_C (1 : L)
  have hsplit : Polynomial.IsSplittingField ℚ L (Polynomial.X ^ n - 1) := by
    refine ⟨?_, ?_⟩
    · rw [hPL_eq, Polynomial.splits_iff_card_roots]
      let S : Finset L := (Finset.range n).image (fun k => ζL ^ k)
      have hS_card : S.card = n := by
        rw [Finset.card_image_of_injOn hζL_prim.injOn_pow, Finset.card_range]
      have hS_sub : S.val ⊆ (Polynomial.X ^ n - 1 : Polynomial L).roots := by
        intro u hu
        have hu' : u ∈ S := hu
        rcases Finset.mem_image.mp hu' with ⟨k, _, rfl⟩
        rw [Polynomial.mem_roots hPL_ne]
        simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one]
        rw [← pow_mul, mul_comm, pow_mul, hζL_prim.pow_eq_one, one_pow, sub_self]
      have hS_le : S.val ≤ (Polynomial.X ^ n - 1 : Polynomial L).roots :=
        (Multiset.le_iff_subset S.nodup).mpr hS_sub
      have hge : n ≤ (Polynomial.X ^ n - 1 : Polynomial L).roots.card :=
        calc n = S.card := hS_card.symm
          _ ≤ (Polynomial.X ^ n - 1 : Polynomial L).roots.card := Multiset.card_le_card hS_le
      have hle : (Polynomial.X ^ n - 1 : Polynomial L).roots.card ≤ n :=
        calc (Polynomial.X ^ n - 1 : Polynomial L).roots.card
            ≤ (Polynomial.X ^ n - 1 : Polynomial L).natDegree := Polynomial.card_roots' _
          _ = n := hPL_deg
      rw [hPL_deg]; omega
    · apply eq_top_iff.mpr
      have hPQ_ne : (Polynomial.X ^ n - 1 : Polynomial ℚ) ≠ 0 :=
        (Polynomial.monic_X_pow_sub_C (1 : ℚ) hn_ne).ne_zero
      have hζ_root : ζL ∈ (Polynomial.X ^ n - 1 : Polynomial ℚ).rootSet L := by
        rw [Polynomial.mem_rootSet_of_ne hPQ_ne]
        simp [hζL_prim.pow_eq_one]
      have hsub : ({ζL} : Set L) ⊆ (Polynomial.X ^ n - 1 : Polynomial ℚ).rootSet L := by
        intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hζ_root
      rw [← htop_ζ]
      exact Algebra.adjoin_mono hsub
  have hsep : (Polynomial.X ^ n - 1 : Polynomial ℚ).Separable := by
    have h1 : (Polynomial.X ^ n - Polynomial.C (1 : ℚ)).Separable :=
      Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn_ne) one_ne_zero
    simpa using h1
  exact ⟨hL_fin, hL_fr, IsGalois.of_separable_splitting_field hsep, fun _ => htop_ζ⟩

private lemma regularPolygon_sufficiency {n : ℕ} (hn : 3 ≤ n)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n.totient → p ≤ 5) :
    RegularPolygonConstructible n := by
  have hn_pos : 0 < n := by omega
  have hn_ne : n ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  rcases exp_two_pi_I_div_parts (n := n) with ⟨hconj_ζ, hcos_eq, _, _⟩
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  rcases cyclotomic_field_isGalois hn with ⟨hL_fin, hL_fr, hL_gal, htop_fn⟩
  have hζL : ζ ∈ L := IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)
  let ζL : L := ⟨ζ, hζL⟩
  have htop_ζ : Algebra.adjoin ℚ ({ζL} : Set L) = ⊤ := htop_fn hζL
  have hζL_prim : IsPrimitiveRoot ζL n := by
    have hinj : Function.Injective (algebraMap L ℂ) := Subtype.val_injective
    exact (IsPrimitiveRoot.map_iff_of_injective hinj).mp (Complex.isPrimitiveRoot_exp n hn_ne)
  -- 2. Galois group `G = Gal(L/ℚ)` is finite abelian of order `φ(n)`
  let G := L ≃ₐ[ℚ] L
  have : Finite G := inferInstance
  let _ : Fintype G := Fintype.ofFinite G
  have hG_card : Nat.card G = n.totient := by
    rw [IsGalois.card_aut_eq_finrank ℚ L, hL_fr]
  have hG_pow : ∀ σ : G, ∃ k : ℕ, σ ζL = ζL ^ k := by
    intro σ
    have hpow : (σ ζL) ^ n = 1 := by
      rw [← map_pow, hζL_prim.pow_eq_one, map_one]
    have : NeZero n := ⟨hn_ne⟩
    rcases hζL_prim.eq_pow_of_pow_eq_one hpow with ⟨k, _, hk⟩
    exact ⟨k, hk.symm⟩
  have hG_ext : ∀ σ τ : G, σ ζL = τ ζL → σ = τ := by
    intro σ τ heq
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin ℚ ({ζL} : Set L) := by rw [htop_ζ]; trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact heq
    · intro r; simp
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro a b _ _ ha hb; simp [ha, hb]
  have hG_comm : ∀ σ τ : G, σ * τ = τ * σ := by
    intro σ τ
    apply hG_ext
    rcases hG_pow σ with ⟨a, ha⟩
    rcases hG_pow τ with ⟨b, hb⟩
    change σ (τ ζL) = τ (σ ζL)
    rw [hb, map_pow, ha, ← pow_mul, mul_comm, pow_mul, ← hb, ← map_pow, ← ha]
  have hNormal_all : ∀ H : Subgroup G, H.Normal := fun H =>
    ⟨fun h hh g => by
      have h1 : g * h * g⁻¹ = h := by rw [hG_comm g h, mul_assoc, mul_inv_cancel, mul_one]
      rwa [h1]⟩
  -- 3. Complex conjugation restricts to `conjAut : G`
  have hconj_mem : ∀ x ∈ L, starRingEnd ℂ x ∈ L := by
    intro x hx
    let S_conj : Subfield ℂ :=
      { carrier := { z : ℂ | starRingEnd ℂ z ∈ L }
        mul_mem' := fun ha hb => by show starRingEnd ℂ (_ * _) ∈ L; rw [map_mul]; exact L.mul_mem ha hb
        one_mem' := by show starRingEnd ℂ 1 ∈ L; rw [map_one]; exact L.one_mem
        add_mem' := fun ha hb => by show starRingEnd ℂ (_ + _) ∈ L; rw [map_add]; exact L.add_mem ha hb
        zero_mem' := by show starRingEnd ℂ 0 ∈ L; rw [map_zero]; exact L.zero_mem
        neg_mem' := fun ha => by show starRingEnd ℂ (-_) ∈ L; rw [map_neg]; exact L.neg_mem ha
        inv_mem' := fun a ha => by show starRingEnd ℂ (a⁻¹) ∈ L; rw [map_inv₀]; exact L.inv_mem ha }
    let L_conj : IntermediateField ℚ ℂ :=
      S_conj.toIntermediateField fun q => by
        show starRingEnd ℂ (algebraMap ℚ ℂ q) ∈ L
        have hq : starRingEnd ℂ (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q := by
          change starRingEnd ℂ ((q : ℝ) : ℂ) = ((q : ℝ) : ℂ)
          exact Complex.conj_ofReal _
        rw [hq]; exact L.algebraMap_mem q
    have hle : L ≤ L_conj := IntermediateField.adjoin_le_iff.mpr (by
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
      show starRingEnd ℂ ζ ∈ L
      rw [hconj_ζ]; exact L.inv_mem hζL)
    exact hle hx
  let conjAut : G :=
    { toFun := fun x => ⟨starRingEnd ℂ x.1, hconj_mem x.1 x.2⟩
      invFun := fun x => ⟨starRingEnd ℂ x.1, hconj_mem x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by
        change starRingEnd ℂ ((q : ℝ) : ℂ) = ((q : ℝ) : ℂ)
        exact Complex.conj_ofReal _) }
  let H₀ : Subgroup G := Subgroup.zpowers conjAut
  have hfixed_real : ∀ (H : Subgroup G), H₀ ≤ H →
      ∀ x ∈ IntermediateField.fixedField H, (x.1 : ℂ).im = 0 := by
    intro H hH x hx
    have hconj_in : conjAut ∈ H := hH (Subgroup.mem_zpowers conjAut)
    have hfix : conjAut x = x := hx ⟨conjAut, hconj_in⟩
    have hstar : starRingEnd ℂ x.1 = x.1 := congrArg Subtype.val hfix
    exact Complex.conj_eq_iff_im.mp hstar
  -- 4. Strong induction on `H.index` for all subgroups `H ≥ H₀`
  have hdescent : ∀ k : ℕ, ∀ H : Subgroup G, H₀ ≤ H → H.index = k →
      ∀ x ∈ IntermediateField.fixedField H, NeusisReal (x.1 : ℂ).re := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro H hH hidx x hx
      have hidx_pos : 0 < H.index := by
        have hmul := Subgroup.card_mul_index H
        have hposG : 0 < Nat.card G := by rw [hG_card]; exact Nat.totient_pos.mpr hn_pos
        rcases Nat.eq_zero_or_pos H.index with h0 | hpos
        · rw [h0, mul_zero] at hmul; omega
        · exact hpos
      by_cases h1 : k = 1
      · subst h1
        have htop : H = ⊤ := Subgroup.index_eq_one.mp hidx
        have hbot_fix : (⊥ : IntermediateField ℚ L).fixingSubgroup = ⊤ := by
          ext g
          simp only [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_top, iff_true]
          intro y hy
          rw [IntermediateField.mem_bot] at hy
          rcases hy with ⟨q, rfl⟩
          exact g.commutes q
        have hfix_bot : IntermediateField.fixedField H = ⊥ := by
          rw [htop, ← hbot_fix, IsGalois.fixedField_fixingSubgroup]
        rw [hfix_bot, IntermediateField.mem_bot] at hx
        rcases hx with ⟨q, hqx⟩
        have hre : (x.1 : ℂ).re = (q : ℝ) := by
          rw [← hqx]
          change ((q : ℝ) : ℂ).re = (q : ℝ)
          exact Complex.ofReal_re _
        rw [hre]; exact neusisReal_ratCast q
      · have hk_gt1 : 1 < H.index := by omega
        have hidx_dvd : H.index ∣ n.totient := by
          rw [← hG_card]
          exact ⟨Nat.card H, (Subgroup.card_mul_index H).symm.trans (mul_comm _ _)⟩
        set p : ℕ := H.index.minFac
        have hp_prime : p.Prime := Nat.minFac_prime (by omega)
        have hp_dvd_idx : p ∣ H.index := Nat.minFac_dvd H.index
        have hp_le5 : p ≤ 5 := hsmooth p hp_prime (hp_dvd_idx.trans hidx_dvd)
        have : H.Normal := hNormal_all H
        let Q := G ⧸ H
        let _ : Fintype Q := Fintype.ofFinite Q
        have hQ_card : Fintype.card Q = H.index := by
          rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
        have : Fact p.Prime := ⟨hp_prime⟩
        obtain ⟨q, hq_ord⟩ := exists_prime_orderOf_dvd_card p (by rwa [hQ_card])
        let H' : Subgroup G := Subgroup.comap (QuotientGroup.mk' H) (Subgroup.zpowers q)
        have hH_le_H' : H ≤ H' := by
          intro g hg
          change QuotientGroup.mk' H g ∈ Subgroup.zpowers q
          have : QuotientGroup.mk' H g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
          rw [this]; exact Subgroup.one_mem _
        have hH'_idx_eq : H'.index = (Subgroup.zpowers q).index :=
          Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective H)
        have hp_mul_idx : p * H'.index = H.index := by
          rw [hH'_idx_eq, ← hq_ord, ← Nat.card_zpowers, Subgroup.card_mul_index,
            ← Subgroup.index_eq_card]
        have hH'_idx_pos : 0 < H'.index := by
          rcases Nat.eq_zero_or_pos H'.index with h0 | hpos
          · rw [h0, mul_zero] at hp_mul_idx; omega
          · exact hpos
        have hH'_idx_lt : H'.index < k := by
          have hp_ge2 : 2 ≤ p := hp_prime.two_le
          nlinarith
        have hIH : ∀ y ∈ IntermediateField.fixedField H', NeusisReal (y.1 : ℂ).re :=
          ih H'.index hH'_idx_lt H' (hH.trans hH_le_H') rfl
        have hcard_rel : Nat.card H' = p * Nat.card H := by
          have h3 : Nat.card H' * H'.index = (p * Nat.card H) * H'.index := by
            calc Nat.card H' * H'.index = Nat.card G := Subgroup.card_mul_index H'
              _ = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
              _ = Nat.card H * (p * H'.index) := by rw [hp_mul_idx]
              _ = (p * Nat.card H) * H'.index := by ring
          exact Nat.eq_of_mul_eq_mul_right hH'_idx_pos h3
        exact galois_descent_step hH_le_H' (by omega) hcard_rel
          (hfixed_real H' (hH.trans hH_le_H')) hIH hx (hfixed_real H hH x hx)
  -- 5. Apply descent to `x = (ζ + ζ⁻¹) / 2 = cos(2π/n) ∈ fixedField H₀`
  have hcos_mem_L : ((Real.cos (2 * Real.pi / n) : ℝ) : ℂ) ∈ L := by
    rw [hcos_eq]
    exact L.div_mem (L.add_mem hζL (L.inv_mem hζL)) (L.algebraMap_mem 2)
  let x_cos : L := ⟨((Real.cos (2 * Real.pi / n) : ℝ) : ℂ), hcos_mem_L⟩
  have hx_cos_fix : x_cos ∈ IntermediateField.fixedField H₀ := by
    rintro ⟨g, hg⟩
    rcases Subgroup.mem_zpowers_iff.mp hg with ⟨m, rfl⟩
    change (conjAut ^ m) x_cos = x_cos
    clear hg
    have hconj_fix : conjAut x_cos = x_cos := Subtype.ext (Complex.conj_ofReal _)
    induction m using Int.induction_on with
    | zero => rw [zpow_zero]; rfl
    | succ k ih =>
      rw [zpow_add, zpow_one]
      change (conjAut ^ (k : ℤ)) (conjAut x_cos) = x_cos
      rw [hconj_fix, ih]
    | pred k ih =>
      rw [zpow_sub, zpow_one]
      have hinv : conjAut⁻¹ x_cos = x_cos := by
        apply conjAut.injective
        change (conjAut * conjAut⁻¹) x_cos = conjAut x_cos
        rw [mul_inv_cancel, hconj_fix]; rfl
      change (conjAut ^ (-(k : ℤ))) (conjAut⁻¹ x_cos) = x_cos
      rw [hinv, ih]
  have hcos_real : NeusisReal (Real.cos (2 * Real.pi / n)) := by
    have h := hdescent H₀.index H₀ le_rfl rfl x_cos hx_cos_fix
    have hre : (x_cos.1 : ℂ).re = Real.cos (2 * Real.pi / n) := Complex.ofReal_re _
    rwa [hre] at h
  exact regularPolygon_of_neusisReal_cos hn hcos_real

/-- **Main Theorem 2 (Regular `n`-gon Characterization)**:
For `n ≥ 3`, the regular `n`-gon is neusis-constructible (using compass, straightedge,
and strictly point-verging unit-mark neusis) if and only if every prime factor of `φ(n)`
is at most `5` (equivalently `φ(n) = 2^a 3^b 5^c`). -/
theorem regularPolygonConstructible_iff {n : ℕ} (hn : 3 ≤ n) :
    RegularPolygonConstructible n ↔ ∀ p : ℕ, p.Prime → p ∣ n.totient → p ≤ 5 :=
  ⟨regularPolygon_necessity hn, regularPolygon_sufficiency hn⟩

end Neusis
