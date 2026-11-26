import NeusisLean.CircleCircleNeusis

/-!
# Universal Solution of General Real Quintics and Sextics via Point-Verging Neusis

We prove that **every** real root of **every** nonzero polynomial of degree `≤ 6` over
`NeusisSubfield` lies in `NeusisSubfield` (`neusisReal_of_poly_le6`).

## Proof Architecture
1. **Openness of `CircleCircleValid`** (`circleCircleValid_eventually_of_witness`):
   At any witness `(A₄*, A₂*, A₁*, A₀*, t_s*)` where `t_s*` is a simple root of the scale cubic
   `5 t^3 + 3 A₄ t^2 + A₂ t - A₀ = 0` and all strict inequalities hold, `CircleCircleValid` holds
   on an open `δ`-ball around `(A₄*, A₂*, A₁*, A₀*)` in `ℝ⁴`.
2. **Three Exact Rational Witnesses** (`Q₅`, `Q₃`, `Q₁`):
   Covering all 6 real-root signatures of degrees 5 and 6 (`(5,0), (3,1), (1,2)` via `Q₅, Q₃, Q₁`,
   and `(6,0), (4,1), (2,2)` via `X * Q₅, X * Q₃, X * Q₁`), each verified by pure rational
   arithmetic (`norm_num`) + IVT + Rolle's theorem.
3. **Lagrange Interpolation + Rational Line + Cubic `S₃ = 0`**:
   Given any monic irreducible real polynomial `f ∈ NeusisSubfield[X]` of degree `d ∈ {5, 6}`
   with a real root `α`, we match its real/complex root signature `(r₁, r₂)` to the corresponding
   witness, lift the witness and a transverse tangent direction via conjugation-invariant Lagrange
   interpolation, approximate by rational polynomials, solve a real cubic `S₃ = 0` over
   `NeusisSubfield`, apply `neusisReal_of_circleCircleValid`, and derive a contradiction to
   irreducibility of `f`.
-/

namespace Neusis

open Polynomial

/-- Helper: continuity of a finite sum of continuous functions. -/
private lemma continuous_finset_sum_aux {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y]
    (s : Finset ι) (f : ι → X → Y) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ### Part 1: Openness of `CircleCircleValid` around a simple witness -/

/-- A witness `(A₄, A₂, A₁, A₀, t_s)` for `CircleCircleValid` where `t_s` is a simple root of
the scale cubic `5 t^3 + 3 A₄ t^2 + A₂ t - A₀ = 0`. -/
def CircleCircleWitness (A₄ A₂ A₁ A₀ t_s : ℝ) : Prop :=
  0 < t_s ∧
  5 * t_s ^ 3 + 3 * A₄ * t_s ^ 2 + A₂ * t_s - A₀ = 0 ∧
  15 * t_s ^ 2 + 6 * A₄ * t_s + A₂ ≠ 0 ∧
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

/-- Part 1a: The 7 strict inequalities in `CircleCircleValid` are open in `(A₄, A₂, A₁, t)`. -/
private lemma circleCircle_ineqs_open {A₄s A₂s A₁s ts : ℝ}
    (hts_pos : 0 < ts) (hA4ts : A₄s + ts < 0)
    (hdisc : 0 < 4 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) ^ 2 - A₁s ^ 2 / ts)
    (hWsq : 0 < 2 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) +
        Real.sqrt (4 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) ^ 2 - A₁s ^ 2 / ts))
    (hU : 0 < Real.sqrt (2 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) +
        Real.sqrt (4 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) ^ 2 - A₁s ^ 2 / ts)) - A₄s - ts)
    (hr1 : let W := Real.sqrt (2 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) +
              Real.sqrt (4 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) ^ 2 - A₁s ^ 2 / ts))
           let U := W - A₄s - ts
           0 < (1 - W / U - A₁s / (U * Real.sqrt ts * W)) / 2)
    (hr2 : let W := Real.sqrt (2 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) +
              Real.sqrt (4 * (A₂s + 2 * A₄s * ts + 3 * ts ^ 2) ^ 2 - A₁s ^ 2 / ts))
           let U := W - A₄s - ts
           0 < (1 - W / U + A₁s / (U * Real.sqrt ts * W)) / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ A₄ A₂ A₁ t : ℝ,
      |A₄ - A₄s| < η → |A₂ - A₂s| < η → |A₁ - A₁s| < η → |t - ts| < η →
      0 < t ∧ A₄ + t < 0 ∧
      0 < 4 * (A₂ + 2 * A₄ * t + 3 * t ^ 2) ^ 2 - A₁ ^ 2 / t ∧
      0 < 2 * (A₂ + 2 * A₄ * t + 3 * t ^ 2) +
          Real.sqrt (4 * (A₂ + 2 * A₄ * t + 3 * t ^ 2) ^ 2 - A₁ ^ 2 / t) ∧
      let W := Real.sqrt (2 * (A₂ + 2 * A₄ * t + 3 * t ^ 2) +
          Real.sqrt (4 * (A₂ + 2 * A₄ * t + 3 * t ^ 2) ^ 2 - A₁ ^ 2 / t))
      let U := W - A₄ - t
      0 < U ∧
      0 < (1 - W / U - A₁ / (U * Real.sqrt t * W)) / 2 ∧
      0 < (1 - W / U + A₁ / (U * Real.sqrt t * W)) / 2 := by
  let p0 : (ℝ × ℝ) × (ℝ × ℝ) := ((A₄s, A₂s), (A₁s, ts))
  let c4 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => p.1.1
  let c2 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => p.1.2
  let c1 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => p.2.1
  let ct : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => p.2.2
  have hc4 : ContinuousAt c4 p0 := continuousAt_fst.comp continuousAt_fst
  have hc2 : ContinuousAt c2 p0 := continuousAt_snd.comp continuousAt_fst
  have hc1 : ContinuousAt c1 p0 := continuousAt_fst.comp continuousAt_snd
  have hct : ContinuousAt ct p0 := continuousAt_snd.comp continuousAt_snd
  let fM := fun p => c2 p + 2 * c4 p * ct p + 3 * ct p ^ 2
  let fdisc := fun p => 4 * fM p ^ 2 - c1 p ^ 2 / ct p
  let fWsq := fun p => 2 * fM p + Real.sqrt (fdisc p)
  let fW := fun p => Real.sqrt (fWsq p)
  let fU := fun p => fW p - c4 p - ct p
  let fS := fun p => fW p / fU p
  let fD := fun p => c1 p / (fU p * Real.sqrt (ct p) * fW p)
  have hcM : ContinuousAt fM p0 :=
    (hc2.add ((continuousAt_const.mul hc4).mul hct)).add (continuousAt_const.mul (hct.pow 2))
  have hcdisc : ContinuousAt fdisc p0 :=
    (continuousAt_const.mul (hcM.pow 2)).sub ((hc1.pow 2).div hct (ne_of_gt hts_pos))
  have hcWsq : ContinuousAt fWsq p0 :=
    (continuousAt_const.mul hcM).add (Real.continuous_sqrt.continuousAt.comp hcdisc)
  have hcW : ContinuousAt fW p0 := Real.continuous_sqrt.continuousAt.comp hcWsq
  have hcU : ContinuousAt fU p0 := (hcW.sub hc4).sub hct
  have hcS : ContinuousAt fS p0 := hcW.div hcU (ne_of_gt hU)
  have hden0 : fU p0 * Real.sqrt (ct p0) * fW p0 ≠ 0 := by
    have hW0 : 0 < fW p0 := Real.sqrt_pos.mpr hWsq
    have hst0 : 0 < Real.sqrt ts := Real.sqrt_pos.mpr hts_pos
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hU) (ne_of_gt hst0)) (ne_of_gt hW0)
  have hcD : ContinuousAt fD p0 :=
    hc1.div ((hcU.mul (Real.continuous_sqrt.continuousAt.comp hct)).mul hcW) hden0
  have hcr1 : ContinuousAt (fun p => (1 - fS p - fD p) / 2) p0 :=
    ((continuousAt_const.sub hcS).sub hcD).div_const 2
  have hcr2 : ContinuousAt (fun p => (1 - fS p + fD p) / 2) p0 :=
    ((continuousAt_const.sub hcS).add hcD).div_const 2
  have hev : ∀ᶠ p in nhds p0,
      0 < ct p ∧ c4 p + ct p < 0 ∧ 0 < fdisc p ∧ 0 < fWsq p ∧ 0 < fU p ∧
      0 < (1 - fS p - fD p) / 2 ∧ 0 < (1 - fS p + fD p) / 2 := by
    refine (hct.eventually (Ioi_mem_nhds hts_pos)).and ?_
    refine ((hc4.add hct).eventually (Iio_mem_nhds hA4ts)).and ?_
    refine (hcdisc.eventually (Ioi_mem_nhds hdisc)).and ?_
    refine (hcWsq.eventually (Ioi_mem_nhds hWsq)).and ?_
    refine (hcU.eventually (Ioi_mem_nhds hU)).and ?_
    exact (hcr1.eventually (Ioi_mem_nhds hr1)).and (hcr2.eventually (Ioi_mem_nhds hr2))
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨η, hη_pos, hη⟩
  refine ⟨η, hη_pos, ?_⟩
  intro A₄ A₂ A₁ t h4 h2 h1 ht
  have hdist : dist ((A₄, A₂), (A₁, t)) p0 < η := by
    simp only [p0, Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨⟨h4, h2⟩, ⟨h1, ht⟩⟩
  exact hη hdist

/-- Part 1b: A simple real root `ts` of `5 t^3 + 3 A₄ t^2 + A₂ t - A₀ = 0` persists inside
`(ts - η, ts + η)` for all `(A₄, A₂, A₀)` in an open `δ₂`-cube. -/
private lemma scale_cubic_persist {A₄s A₂s A₀s ts η : ℝ}
    (hη_pos : 0 < η)
    (hcub : 5 * ts ^ 3 + 3 * A₄s * ts ^ 2 + A₂s * ts - A₀s = 0)
    (hderiv : 15 * ts ^ 2 + 6 * A₄s * ts + A₂s ≠ 0) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ A₄ A₂ A₀ : ℝ,
      |A₄ - A₄s| < δ₂ → |A₂ - A₂s| < δ₂ → |A₀ - A₀s| < δ₂ →
      ∃ t : ℝ, |t - ts| < η ∧ 5 * t ^ 3 + 3 * A₄ * t ^ 2 + A₂ * t - A₀ = 0 := by
  let g : ℝ → ℝ → ℝ → ℝ → ℝ := fun A₄ A₂ A₀ t => 5 * t ^ 3 + 3 * A₄ * t ^ 2 + A₂ * t - A₀
  obtain ⟨D₀, hD₀_def⟩ : ∃ D₀ : ℝ, D₀ = 15 * ts ^ 2 + 6 * A₄s * ts + A₂s := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀_def⟩ : ∃ B₀ : ℝ, B₀ = 15 * ts + 3 * A₄s := ⟨_, rfl⟩
  have hD₀_ne : D₀ ≠ 0 := by rwa [hD₀_def]
  have hD₀_pos : 0 < |D₀| := abs_pos.mpr hD₀_ne
  obtain ⟨ρ, hρ_pos, hρ_lt_η, hρ_le1, hρ_div⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < η ∧ ρ ≤ 1 ∧ ρ ≤ |D₀| / (2 * (|B₀| + 6)) := by
    refine ⟨min (η / 2) (min 1 (|D₀| / (2 * (|B₀| + 6)))), ?_, ?_, ?_, ?_⟩
    · positivity
    · have : min (η / 2) (min 1 (|D₀| / (2 * (|B₀| + 6)))) ≤ η / 2 := min_le_left _ _; linarith
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hρ_small : |B₀ * ρ + 5 * ρ ^ 2| < |D₀| ∧ |-B₀ * ρ + 5 * ρ ^ 2| < |D₀| := by
    have hbound : |B₀| * ρ + 5 * ρ ^ 2 ≤ (|B₀| + 5) * ρ := by nlinarith [abs_nonneg B₀]
    have hden_pos : 0 < 2 * (|B₀| + 6) := by positivity
    have hlt : (|B₀| + 5) * ρ < |D₀| := by
      have h1 : (|B₀| + 6) * ρ ≤ |D₀| / 2 := by
        have := (le_div_iff₀ hden_pos).mp hρ_div; linarith
      nlinarith [abs_nonneg B₀]
    have h5p : (0 : ℝ) < 5 * ρ ^ 2 := by positivity
    constructor
    · calc |B₀ * ρ + 5 * ρ ^ 2| ≤ |B₀ * ρ| + |5 * ρ ^ 2| := abs_add_le _ _
        _ = |B₀| * ρ + 5 * ρ ^ 2 := by rw [abs_mul, abs_of_pos hρ_pos, abs_of_pos h5p]
        _ < |D₀| := lt_of_le_of_lt hbound hlt
    · calc |-B₀ * ρ + 5 * ρ ^ 2| ≤ |-B₀ * ρ| + |5 * ρ ^ 2| := abs_add_le _ _
        _ = |B₀| * ρ + 5 * ρ ^ 2 := by
            rw [show -B₀ * ρ = -(B₀ * ρ) by ring, abs_neg, abs_mul, abs_of_pos hρ_pos, abs_of_pos h5p]
        _ < |D₀| := lt_of_le_of_lt hbound hlt
  have hg_plus : g A₄s A₂s A₀s (ts + ρ) = ρ * (D₀ + B₀ * ρ + 5 * ρ ^ 2) := by
    dsimp only [g]; rw [hD₀_def, hB₀_def]; linear_combination hcub
  have hg_minus : g A₄s A₂s A₀s (ts - ρ) = -ρ * (D₀ - B₀ * ρ + 5 * ρ ^ 2) := by
    dsimp only [g]; rw [hD₀_def, hB₀_def]; linear_combination hcub
  have hprod_neg : g A₄s A₂s A₀s (ts - ρ) * g A₄s A₂s A₀s (ts + ρ) < 0 := by
    rw [hg_minus, hg_plus]
    have hsq_pos : 0 < ρ * ρ := mul_pos hρ_pos hρ_pos
    rcases lt_or_gt_of_ne hD₀_ne with hDneg | hDpos
    · have habs : |D₀| = -D₀ := abs_of_neg hDneg
      have h1 : D₀ + B₀ * ρ + 5 * ρ ^ 2 < 0 := by
        have := (abs_lt.mp hρ_small.1).2; rw [habs] at this; linarith
      have h2 : D₀ - B₀ * ρ + 5 * ρ ^ 2 < 0 := by
        have := (abs_lt.mp hρ_small.2).2; rw [habs] at this; linarith
      have hpos1 : 0 < (-(D₀ + B₀ * ρ + 5 * ρ ^ 2)) * (-(D₀ - B₀ * ρ + 5 * ρ ^ 2)) :=
        mul_pos (by linarith) (by linarith)
      have hprod_pos : 0 < (ρ * ρ) * ((-(D₀ + B₀ * ρ + 5 * ρ ^ 2)) * (-(D₀ - B₀ * ρ + 5 * ρ ^ 2))) :=
        mul_pos hsq_pos hpos1
      have hident : -ρ * (D₀ - B₀ * ρ + 5 * ρ ^ 2) * (ρ * (D₀ + B₀ * ρ + 5 * ρ ^ 2)) =
          -((ρ * ρ) * ((-(D₀ + B₀ * ρ + 5 * ρ ^ 2)) * (-(D₀ - B₀ * ρ + 5 * ρ ^ 2)))) := by ring
      rw [hident]; linarith
    · have habs : |D₀| = D₀ := abs_of_pos hDpos
      have h1 : 0 < D₀ + B₀ * ρ + 5 * ρ ^ 2 := by
        have := (abs_lt.mp hρ_small.1).1; rw [habs] at this; linarith
      have h2 : 0 < D₀ - B₀ * ρ + 5 * ρ ^ 2 := by
        have := (abs_lt.mp hρ_small.2).1; rw [habs] at this; linarith
      have hpos1 : 0 < (D₀ + B₀ * ρ + 5 * ρ ^ 2) * (D₀ - B₀ * ρ + 5 * ρ ^ 2) := mul_pos h1 h2
      have hprod_pos : 0 < (ρ * ρ) * ((D₀ + B₀ * ρ + 5 * ρ ^ 2) * (D₀ - B₀ * ρ + 5 * ρ ^ 2)) :=
        mul_pos hsq_pos hpos1
      have hident : -ρ * (D₀ - B₀ * ρ + 5 * ρ ^ 2) * (ρ * (D₀ + B₀ * ρ + 5 * ρ ^ 2)) =
          -((ρ * ρ) * ((D₀ + B₀ * ρ + 5 * ρ ^ 2) * (D₀ - B₀ * ρ + 5 * ρ ^ 2))) := by ring
      rw [hident]; linarith
  have hgl_ne : g A₄s A₂s A₀s (ts - ρ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hprod_neg; linarith
  have hgr_ne : g A₄s A₂s A₀s (ts + ρ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hprod_neg; linarith
  obtain ⟨M, hM_pos, hMl, hMr⟩ :
      ∃ M : ℝ, 0 < M ∧
        3 * (ts - ρ) ^ 2 + |ts - ρ| + 1 ≤ M ∧
        3 * (ts + ρ) ^ 2 + |ts + ρ| + 1 ≤ M := by
    refine ⟨max (3 * (ts - ρ) ^ 2 + |ts - ρ| + 1) (3 * (ts + ρ) ^ 2 + |ts + ρ| + 1), ?_,
      le_max_left _ _, le_max_right _ _⟩
    have : (0 : ℝ) < 3 * (ts - ρ) ^ 2 + |ts - ρ| + 1 := by positivity
    exact lt_of_lt_of_le this (le_max_left _ _)
  obtain ⟨δ₂, hδ₂_pos, hδ₂_l, hδ₂_r⟩ :
      ∃ δ₂ : ℝ, 0 < δ₂ ∧
        M * δ₂ < |g A₄s A₂s A₀s (ts - ρ)| ∧
        M * δ₂ < |g A₄s A₂s A₀s (ts + ρ)| := by
    have hl_pos : 0 < |g A₄s A₂s A₀s (ts - ρ)| := abs_pos.mpr hgl_ne
    have hr_pos : 0 < |g A₄s A₂s A₀s (ts + ρ)| := abs_pos.mpr hgr_ne
    refine ⟨min (|g A₄s A₂s A₀s (ts - ρ)| / (2 * M)) (|g A₄s A₂s A₀s (ts + ρ)| / (2 * M)),
      by positivity, ?_, ?_⟩
    · have h1 : min (|g A₄s A₂s A₀s (ts - ρ)| / (2 * M)) (|g A₄s A₂s A₀s (ts + ρ)| / (2 * M)) ≤
          |g A₄s A₂s A₀s (ts - ρ)| / (2 * M) := min_le_left _ _
      have h2 := (le_div_iff₀ (show (0 : ℝ) < 2 * M by positivity)).mp h1
      linarith
    · have h1 : min (|g A₄s A₂s A₀s (ts - ρ)| / (2 * M)) (|g A₄s A₂s A₀s (ts + ρ)| / (2 * M)) ≤
          |g A₄s A₂s A₀s (ts + ρ)| / (2 * M) := min_le_right _ _
      have h2 := (le_div_iff₀ (show (0 : ℝ) < 2 * M by positivity)).mp h1
      linarith
  refine ⟨δ₂, hδ₂_pos, ?_⟩
  intro A₄ A₂ A₀ h4 h2 h0
  have hdiff : ∀ t : ℝ, 3 * t ^ 2 + |t| + 1 ≤ M →
      |g A₄ A₂ A₀ t - g A₄s A₂s A₀s t| < M * δ₂ := by
    intro t htM
    have heq : g A₄ A₂ A₀ t - g A₄s A₂s A₀s t =
        (3 * t ^ 2) * (A₄ - A₄s) + t * (A₂ - A₂s) + (-(A₀ - A₀s)) := by dsimp only [g]; ring
    rw [heq]
    have h1 : |(3 * t ^ 2) * (A₄ - A₄s)| ≤ (3 * t ^ 2) * δ₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * t ^ 2)]
      exact mul_le_mul_of_nonneg_left (le_of_lt h4) (by positivity)
    have h2' : |t * (A₂ - A₂s)| ≤ |t| * δ₂ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (le_of_lt h2) (abs_nonneg t)
    have h3 : |-(A₀ - A₀s)| < 1 * δ₂ := by rw [abs_neg, one_mul]; exact h0
    have hsum : |(3 * t ^ 2) * (A₄ - A₄s) + t * (A₂ - A₂s) + -(A₀ - A₀s)| ≤
        |(3 * t ^ 2) * (A₄ - A₄s)| + |t * (A₂ - A₂s)| + |-(A₀ - A₀s)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hMle : (3 * t ^ 2 + |t| + 1) * δ₂ ≤ M * δ₂ :=
      mul_le_mul_of_nonneg_right htM (le_of_lt hδ₂_pos)
    linarith
  have hdl : |g A₄ A₂ A₀ (ts - ρ) - g A₄s A₂s A₀s (ts - ρ)| < |g A₄s A₂s A₀s (ts - ρ)| :=
    lt_trans (hdiff (ts - ρ) hMl) hδ₂_l
  have hdr : |g A₄ A₂ A₀ (ts + ρ) - g A₄s A₂s A₀s (ts + ρ)| < |g A₄s A₂s A₀s (ts + ρ)| :=
    lt_trans (hdiff (ts + ρ) hMr) hδ₂_r
  have hg_cont : Continuous (g A₄ A₂ A₀) :=
    (((continuous_const.mul (continuous_pow 3)).add
      (continuous_const.mul (continuous_pow 2))).add
      (continuous_const.mul continuous_id)).sub continuous_const
  obtain ⟨t, htI, hgt⟩ : ∃ t ∈ Set.Icc (ts - ρ) (ts + ρ), g A₄ A₂ A₀ t = 0 := by
    rcases lt_or_gt_of_ne hgl_ne with hgl_neg | hgl_pos
    · have hgr_pos : 0 < g A₄s A₂s A₀s (ts + ρ) := by
        by_contra hle; push Not at hle
        have : 0 ≤ g A₄s A₂s A₀s (ts - ρ) * g A₄s A₂s A₀s (ts + ρ) :=
          mul_nonneg_of_nonpos_of_nonpos (le_of_lt hgl_neg) hle
        linarith
      have hl_neg : g A₄ A₂ A₀ (ts - ρ) < 0 := by
        rw [abs_of_neg hgl_neg] at hdl; linarith [(abs_lt.mp hdl).2]
      have hr_pos : 0 < g A₄ A₂ A₀ (ts + ρ) := by
        rw [abs_of_pos hgr_pos] at hdr; linarith [(abs_lt.mp hdr).1]
      exact intermediate_value_Icc (by linarith) hg_cont.continuousOn ⟨le_of_lt hl_neg, le_of_lt hr_pos⟩
    · have hgr_neg : g A₄s A₂s A₀s (ts + ρ) < 0 := by
        by_contra hge; push Not at hge
        have : 0 ≤ g A₄s A₂s A₀s (ts - ρ) * g A₄s A₂s A₀s (ts + ρ) :=
          mul_nonneg (le_of_lt hgl_pos) hge
        linarith
      have hl_pos : 0 < g A₄ A₂ A₀ (ts - ρ) := by
        rw [abs_of_pos hgl_pos] at hdl; linarith [(abs_lt.mp hdl).1]
      have hr_neg : g A₄ A₂ A₀ (ts + ρ) < 0 := by
        rw [abs_of_neg hgr_neg] at hdr; linarith [(abs_lt.mp hdr).2]
      exact intermediate_value_Icc' (by linarith) hg_cont.continuousOn ⟨le_of_lt hr_neg, le_of_lt hl_pos⟩
  exact ⟨t, abs_lt.mpr ⟨by linarith [htI.1], by linarith [htI.2]⟩, hgt⟩

/-- **Openness Lemma**: If `(A₄*, A₂*, A₁*, A₀*, t_s*)` satisfies `CircleCircleWitness`,
then `CircleCircleValid` holds on an open `δ`-cube around `(A₄*, A₂*, A₁*, A₀*)`. -/
lemma circleCircleValid_eventually_of_witness {A₄s A₂s A₁s A₀s ts : ℝ}
    (hw : CircleCircleWitness A₄s A₂s A₁s A₀s ts) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A₄ A₂ A₁ A₀ : ℝ,
      |A₄ - A₄s| < δ → |A₂ - A₂s| < δ → |A₁ - A₁s| < δ → |A₀ - A₀s| < δ →
      CircleCircleValid A₄ A₂ A₁ A₀ := by
  rcases hw with ⟨hts_pos, hcub, hderiv, hA4ts, hdisc, hWsq, hU, hr1, hr2⟩
  rcases circleCircle_ineqs_open hts_pos hA4ts hdisc hWsq hU hr1 hr2 with ⟨η, hη_pos, hη⟩
  rcases scale_cubic_persist hη_pos hcub hderiv with ⟨δ₂, hδ₂_pos, hδ₂⟩
  refine ⟨min η δ₂, lt_min hη_pos hδ₂_pos, ?_⟩
  intro A₄ A₂ A₁ A₀ h4 h2 h1 h0
  rcases hδ₂ A₄ A₂ A₀ (lt_of_lt_of_le h4 (min_le_right _ _))
      (lt_of_lt_of_le h2 (min_le_right _ _)) (lt_of_lt_of_le h0 (min_le_right _ _)) with ⟨t, ht, hgt⟩
  rcases hη A₄ A₂ A₁ t (lt_of_lt_of_le h4 (min_le_left _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _)) (lt_of_lt_of_le h1 (min_le_left _ _)) ht with
    ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7⟩
  exact ⟨t, ht1, hgt, ht2, ht3, ht4, ht5, ht6, ht7⟩

/-! ### Part 2: Three Exact Rational Witnesses for All 6 Signatures -/

private lemma circleCircleWitness_of_rat {A₂ A₁ t_s : ℝ}
    (hts_pos : 0 < t_s) (hts_lt1 : t_s < 1)
    (hquad : 5 * t_s ^ 2 - 3 * t_s + A₂ = 0)
    (hderiv : 15 * t_s ^ 2 - 6 * t_s + A₂ ≠ 0)
    (hM_pos : 0 < A₂ - 2 * t_s + 3 * t_s ^ 2)
    (hdisc : A₁ ^ 2 < 4 * (A₂ - 2 * t_s + 3 * t_s ^ 2) ^ 2 * t_s)
    (hR_margin : A₁ ^ 2 < (1 - t_s) ^ 2 * t_s * (2 * (A₂ - 2 * t_s + 3 * t_s ^ 2))) :
    CircleCircleWitness (-1) A₂ A₁ 0 t_s := by
  let M := A₂ + 2 * (-1) * t_s + 3 * t_s ^ 2
  have hM_eq : M = A₂ - 2 * t_s + 3 * t_s ^ 2 := by dsimp [M]; ring
  have hdisc_p : 0 < 4 * M ^ 2 - A₁ ^ 2 / t_s := by
    rw [sub_pos, div_lt_iff₀ hts_pos]; linarith [hM_eq ▸ hdisc]
  have hWsq_p : 0 < 2 * M + Real.sqrt (4 * M ^ 2 - A₁ ^ 2 / t_s) := by
    linarith [Real.sqrt_pos.mpr hdisc_p, hM_eq ▸ hM_pos]
  let W := Real.sqrt (2 * M + Real.sqrt (4 * M ^ 2 - A₁ ^ 2 / t_s))
  have hW_p : 0 < W := Real.sqrt_pos.mpr hWsq_p
  have hW_sq : W ^ 2 = 2 * M + Real.sqrt (4 * M ^ 2 - A₁ ^ 2 / t_s) :=
    Real.sq_sqrt (le_of_lt hWsq_p)
  have hW_gt : 2 * M < W ^ 2 := by linarith [Real.sqrt_pos.mpr hdisc_p]
  let U := W - (-1) - t_s
  have hU_eq : U = W + (1 - t_s) := by dsimp [U]; ring
  have hU_p : 0 < U := by rw [hU_eq]; linarith
  let S := W / U
  let D := A₁ / (U * Real.sqrt t_s * W)
  have h1S : 1 - S = (1 - t_s) / U := by dsimp [S]; field_simp [ne_of_gt hU_p]; linarith [hU_eq]
  have hD_lt : |D| < 1 - S := by
    rw [h1S]; dsimp [D]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hU_p, abs_of_pos (Real.sqrt_pos.mpr hts_pos),
      abs_of_pos hW_p]
    have hden_p : 0 < U * Real.sqrt t_s * W := by positivity
    rw [div_lt_div_iff₀ hden_p hU_p]
    have hsq : |A₁| ^ 2 < ((1 - t_s) * Real.sqrt t_s * W) ^ 2 := by
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hts_pos)]
      have hpos_fac : 0 < (1 - t_s) ^ 2 * t_s :=
        mul_pos (sq_pos_of_pos (by linarith)) hts_pos
      have h1 : (1 - t_s) ^ 2 * t_s * (2 * M) < (1 - t_s) ^ 2 * t_s * W ^ 2 :=
        mul_lt_mul_of_pos_left hW_gt hpos_fac
      linarith [hM_eq ▸ hR_margin]
    have hstep : |A₁| < (1 - t_s) * Real.sqrt t_s * W := by
      have hnn : 0 ≤ (1 - t_s) * Real.sqrt t_s * W := by positivity
      by_contra hle; push Not at hle
      have : ((1 - t_s) * Real.sqrt t_s * W) ^ 2 ≤ |A₁| ^ 2 := by
        rw [sq, sq]; exact mul_self_le_mul_self hnn hle
      linarith
    calc |A₁| * U < (1 - t_s) * Real.sqrt t_s * W * U := mul_lt_mul_of_pos_right hstep hU_p
      _ = (1 - t_s) * (U * Real.sqrt t_s * W) := by ring
  have hr1 : 0 < (1 - S - D) / 2 := by linarith [le_abs_self D]
  have hr2 : 0 < (1 - S + D) / 2 := by linarith [neg_le_abs D]
  refine ⟨hts_pos, ?_, ?_, by linarith, hdisc_p, hWsq_p, hU_p, hr1, hr2⟩
  · linear_combination t_s * hquad
  · convert hderiv using 1; ring

private lemma witness5_cc : CircleCircleWitness (-1) (31 / 144) (1 / 64) 0 (1 / 12) :=
  circleCircleWitness_of_rat (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma witness3_cc : CircleCircleWitness (-1) (1 / 4) (1 / 32) 0 (1 / 10) :=
  circleCircleWitness_of_rat (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma witness1_cc : CircleCircleWitness (-1) (4 / 9) (1 / 20) 0 (1 / 3) :=
  circleCircleWitness_of_rat (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Witness quintic polynomial `X^5 - X^3 + C A₂ * X + C A₁` over `ℝ`. -/
noncomputable def witnessQuintic (A₂ A₁ : ℝ) : Polynomial ℝ :=
  Polynomial.X ^ 5 - Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁

private lemma witnessQuintic_tail_deg (A₂ A₁ : ℝ) :
    (-Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁ : Polynomial ℝ).natDegree < 5 := by
  have h3 : (-Polynomial.X ^ 3 : Polynomial ℝ).natDegree ≤ 3 := by simp
  have h1 : (C A₂ * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := (natDegree_mul_le).trans (by simp)
  have h31 : (-Polynomial.X ^ 3 + C A₂ * Polynomial.X : Polynomial ℝ).natDegree ≤ 3 :=
    (natDegree_add_le _ _).trans (max_le h3 (by omega))
  have h310 : (-Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁ : Polynomial ℝ).natDegree ≤ 3 :=
    (natDegree_add_le _ _).trans (max_le h31 (by simp))
  omega

private lemma witnessQuintic_monic (A₂ A₁ : ℝ) : (witnessQuintic A₂ A₁).Monic := by
  unfold witnessQuintic
  have heq : Polynomial.X ^ 5 - Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁ =
      Polynomial.X ^ 5 + (-Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁) := by ring
  rw [heq]
  apply (monic_X_pow 5).add_of_left
  apply Polynomial.degree_lt_degree
  rw [natDegree_X_pow]
  exact witnessQuintic_tail_deg A₂ A₁

private lemma witnessQuintic_natDegree (A₂ A₁ : ℝ) : (witnessQuintic A₂ A₁).natDegree = 5 := by
  unfold witnessQuintic
  have heq : Polynomial.X ^ 5 - Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁ =
      Polynomial.X ^ 5 + (-Polynomial.X ^ 3 + C A₂ * Polynomial.X + C A₁) := by ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; exact witnessQuintic_tail_deg A₂ A₁),
    natDegree_X_pow]

/-- Any nonzero polynomial `P : Polynomial ℂ` whose roots never also annihilate `derivative P`
has `P.roots.Nodup`. -/
private lemma nodup_roots_of_deriv_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0)
    (h : ∀ ζ : ℂ, P.eval ζ = 0 → (Polynomial.derivative P).eval ζ ≠ 0) :
    P.roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro ζ
  by_contra hgt
  have h2 : 2 ≤ P.roots.count ζ := by omega
  rw [Polynomial.count_roots] at h2
  have hdvd : (Polynomial.X - C ζ) ^ 2 ∣ P := (Polynomial.le_rootMultiplicity_iff hP).mp h2
  rcases hdvd with ⟨Q, hQ⟩
  have hP0 : P.eval ζ = 0 := by rw [hQ]; simp
  have hd0 : (Polynomial.derivative P).eval ζ = 0 := by
    rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_pow]; simp
  exact h ζ hP0 hd0

/-- Separability over `ℂ` for all 3 witness quintics via the exact rational square discriminant
of their biquadratic derivative `5 z^4 - 3 z^2 + A₂`. -/
private lemma witnessQuintic_nodup_roots {A₂ A₁ δ : ℝ}
    (hδ : 9 - 20 * A₂ = δ ^ 2)
    (h1 : ((3 + δ) / 10) * (-2 * ((3 + δ) / 10) + 4 * A₂) ^ 2 ≠ 25 * A₁ ^ 2)
    (h2 : ((3 - δ) / 10) * (-2 * ((3 - δ) / 10) + 4 * A₂) ^ 2 ≠ 25 * A₁ ^ 2) :
    ((witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)).roots.Nodup := by
  let P : Polynomial ℂ := (witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)
  have hP_monic : P.Monic := (witnessQuintic_monic A₂ A₁).map _
  apply nodup_roots_of_deriv_ne_zero hP_monic.ne_zero
  intro ζ hζ hdζ
  have hPeq : P = Polynomial.X ^ 5 - Polynomial.X ^ 3 + C (A₂ : ℂ) * Polynomial.X + C (A₁ : ℂ) := by
    simp [P, witnessQuintic]
  have hev : ζ ^ 5 - ζ ^ 3 + (A₂ : ℂ) * ζ + (A₁ : ℂ) = 0 := by
    rw [hPeq] at hζ; simpa using hζ
  have hdev : 5 * ζ ^ 4 - 3 * ζ ^ 2 + (A₂ : ℂ) = 0 := by
    rw [hPeq] at hdζ
    simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_pow,
      Polynomial.derivative_X, Polynomial.derivative_mul, Polynomial.derivative_C,
      mul_one, zero_mul, zero_add, add_zero, Nat.cast_ofNat] at hdζ
    simpa using hdζ
  have hquad : (10 * ζ ^ 2 - 3) ^ 2 = (δ : ℂ) ^ 2 := by
    have hδC : (9 : ℂ) - 20 * (A₂ : ℂ) = (δ : ℂ) ^ 2 := by exact_mod_cast hδ
    linear_combination 20 * hdev + hδC
  have hlin : ζ * (-2 * ζ ^ 2 + 4 * (A₂ : ℂ)) + 5 * (A₁ : ℂ) = 0 := by
    linear_combination 5 * hev - ζ * hdev
  have hsq : ζ ^ 2 * (-2 * ζ ^ 2 + 4 * (A₂ : ℂ)) ^ 2 = 25 * (A₁ : ℂ) ^ 2 := by
    have : (ζ * (-2 * ζ ^ 2 + 4 * (A₂ : ℂ))) ^ 2 = (-5 * (A₁ : ℂ)) ^ 2 := by
      congr 1; linear_combination hlin
    linear_combination this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hquad with hpos | hneg
  · have hz2 : ζ ^ 2 = (((3 + δ) / 10 : ℝ) : ℂ) := by
      push_cast; linear_combination (1 / 10 : ℂ) * hpos
    rw [hz2] at hsq
    have hreal : ((3 + δ) / 10) * (-2 * ((3 + δ) / 10) + 4 * A₂) ^ 2 = 25 * A₁ ^ 2 := by
      exact_mod_cast hsq
    exact h1 hreal
  · have hz2 : ζ ^ 2 = (((3 - δ) / 10 : ℝ) : ℂ) := by
      push_cast; linear_combination (1 / 10 : ℂ) * hneg
    rw [hz2] at hsq
    have hreal : ((3 - δ) / 10) * (-2 * ((3 - δ) / 10) + 4 * A₂) ^ 2 = 25 * A₁ ^ 2 := by
      exact_mod_cast hsq
    exact h2 hreal

private lemma witness5_nodup :
    ((witnessQuintic (31 / 144) (1 / 64)).map (algebraMap ℝ ℂ)).roots.Nodup :=
  witnessQuintic_nodup_roots (δ := 13 / 6) (by norm_num) (by norm_num) (by norm_num)

private lemma witness3_nodup :
    ((witnessQuintic (1 / 4) (1 / 32)).map (algebraMap ℝ ℂ)).roots.Nodup :=
  witnessQuintic_nodup_roots (δ := 2) (by norm_num) (by norm_num) (by norm_num)

private lemma witness1_nodup :
    ((witnessQuintic (4 / 9) (1 / 20)).map (algebraMap ℝ ℂ)).roots.Nodup :=
  witnessQuintic_nodup_roots (δ := 1 / 3) (by norm_num) (by norm_num) (by norm_num)

/-! ### Part 3: Canonical Root Tuples and Real Root Signature Counting -/

/-- Canonical conjugation involution on `Fin d` fixing the first `r₁` indices and swapping
`(r₁ + 2*k, r₁ + 2*k + 1)` for `k < r₂`, where `r₁ + 2 * r₂ = d`. -/
def canonInv (d r₁ r₂ : ℕ) (hsum : r₁ + 2 * r₂ = d) : Equiv.Perm (Fin d) where
  toFun i :=
    if h : i.1 < r₁ then i
    else if h2 : (i.1 - r₁) % 2 = 0 then ⟨i.1 + 1, by omega⟩
    else ⟨i.1 - 1, by omega⟩
  invFun i :=
    if h : i.1 < r₁ then i
    else if h2 : (i.1 - r₁) % 2 = 0 then ⟨i.1 + 1, by omega⟩
    else ⟨i.1 - 1, by omega⟩
  left_inv i := by
    ext
    by_cases h : i.1 < r₁
    · simp [h]
    · by_cases h2 : (i.1 - r₁) % 2 = 0
      · have hne : ¬ (i.1 + 1 < r₁) := by omega
        have hodd : ¬ ((i.1 + 1 - r₁) % 2 = 0) := by omega
        simp [h, h2, hne, hodd]
      · have hne : ¬ (i.1 - 1 < r₁) := by omega
        have heven : (i.1 - 1 - r₁) % 2 = 0 := by omega
        simp [h, h2, hne, heven]; omega
  right_inv i := by
    ext
    by_cases h : i.1 < r₁
    · simp [h]
    · by_cases h2 : (i.1 - r₁) % 2 = 0
      · have hne : ¬ (i.1 + 1 < r₁) := by omega
        have hodd : ¬ ((i.1 + 1 - r₁) % 2 = 0) := by omega
        simp [h, h2, hne, hodd]
      · have hne : ¬ (i.1 - 1 < r₁) := by omega
        have heven : (i.1 - 1 - r₁) % 2 = 0 := by omega
        simp [h, h2, hne, heven]; omega

lemma canonInv_invol (d r₁ r₂ : ℕ) (hsum : r₁ + 2 * r₂ = d) (i : Fin d) :
    canonInv d r₁ r₂ hsum (canonInv d r₁ r₂ hsum i) = i :=
  (canonInv d r₁ r₂ hsum).left_inv i

private lemma canonInv_congr {d r₁ r₁' r₂ r₂' : ℕ} (h1 : r₁ = r₁') (h2 : r₂ = r₂')
    (hsum : r₁ + 2 * r₂ = d) (hsum' : r₁' + 2 * r₂' = d) (i : Fin d) :
    canonInv d r₁ r₂ hsum i = canonInv d r₁' r₂' hsum' i := by
  subst h1 h2; rfl

private lemma eval_map_conj (P : Polynomial ℝ) (z : ℂ) :
    (P.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((P.map (algebraMap ℝ ℂ)).eval z) := by
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ := by
    ext r; simp
  rw [Polynomial.eval_map, Polynomial.eval_map]
  have h := (Polynomial.hom_eval₂ P (algebraMap ℝ ℂ) (starRingEnd ℂ) z).symm
  rw [hcomp] at h
  exact h

private lemma extract_root_tuple {P : Polynomial ℝ} {d : ℕ}
    (hmon : P.Monic) (hdeg : P.natDegree = d)
    (hnodup : (P.map (algebraMap ℝ ℂ)).roots.Nodup) :
    let S := (P.map (algebraMap ℝ ℂ)).roots.toFinset
    let r₁ := (S.filter (fun z : ℂ => z.im = 0)).card
    let r₂ := (S.filter (fun z : ℂ => 0 < z.im)).card
    ∃ hsum : r₁ + 2 * r₂ = d,
    ∃ roots : Fin d → ℂ,
      Function.Injective roots ∧
      (∀ i : Fin d, starRingEnd ℂ (roots i) = roots (canonInv d r₁ r₂ hsum i)) ∧
      (∀ i : Fin d, i.1 < r₁ → (roots i).im = 0) ∧
      (∀ z : ℂ, z ∈ S ↔ ∃ i : Fin d, roots i = z) ∧
      P.map (algebraMap ℝ ℂ) = ∏ i : Fin d, (Polynomial.X - C (roots i)) := by
  intro S r₁ r₂
  let Pℂ := P.map (algebraMap ℝ ℂ)
  have hPℂ_monic : Pℂ.Monic := hmon.map _
  have hPℂ_deg : Pℂ.natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective, hdeg]
  have hcard_roots : Pℂ.roots.card = d := by
    have hsp : Pℂ.Splits := IsAlgClosed.splits Pℂ
    rw [← hPℂ_deg, ← Polynomial.Splits.natDegree_eq_card_roots hsp]
  have hS_card : S.card = d := by
    dsimp [S]; rw [Multiset.toFinset_card_of_nodup hnodup, hcard_roots]
  have hPℂ_prod : Pℂ = ∏ z ∈ S, (Polynomial.X - C z) := by
    have h1 := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPℂ_monic
      (by rw [hcard_roots, hPℂ_deg])
    rw [← h1]
    change (Pℂ.roots.map fun a => Polynomial.X - C a).prod = ∏ z ∈ Pℂ.roots.toFinset, (Polynomial.X - C z)
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
  have hS_star : ∀ z, z ∈ S → starRingEnd ℂ z ∈ S := by
    intro z hz
    dsimp [S] at hz ⊢
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPℂ_monic.ne_zero, Polynomial.IsRoot] at hz ⊢
    rw [eval_map_conj, hz, map_zero]
  let S_real := S.filter (fun z : ℂ => z.im = 0)
  let S_pos := S.filter (fun z : ℂ => 0 < z.im)
  let S_neg := S.filter (fun z : ℂ => z.im < 0)
  have hS_neg_eq : S_neg = S_pos.image (starRingEnd ℂ) := by
    ext z
    simp only [S_neg, S_pos, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hzS, hzim⟩
      refine ⟨starRingEnd ℂ z, ⟨hS_star z hzS, ?_⟩, Complex.conj_conj z⟩
      simp [hzim]
    · rintro ⟨w, ⟨hwS, hwim⟩, rfl⟩
      refine ⟨hS_star w hwS, ?_⟩
      simp [hwim]
  have hneg_card : S_neg.card = r₂ := by
    rw [hS_neg_eq, Finset.card_image_of_injective _ (starRingEnd ℂ).injective]
  have hdisj1 : Disjoint S_real S_pos := by
    rw [Finset.disjoint_left]; intro z h1 h2
    simp only [S_real, S_pos, Finset.mem_filter] at h1 h2; linarith
  have hdisj2 : Disjoint (S_real ∪ S_pos) S_neg := by
    rw [Finset.disjoint_left]; intro z h1 h2
    simp only [S_real, S_pos, S_neg, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> linarith
  have hunion : S_real ∪ S_pos ∪ S_neg = S := by
    ext z
    simp only [S_real, S_pos, S_neg, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hz
      rcases lt_trichotomy z.im 0 with h | h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl (Or.inl ⟨hz, h⟩)
      · exact Or.inl (Or.inr ⟨hz, h⟩)
  have hsum : r₁ + 2 * r₂ = d := by
    have hc : S.card = S_real.card + S_pos.card + S_neg.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
    have h1 : S_real.card = r₁ := rfl
    have h2 : S_pos.card = r₂ := rfl
    omega
  let e₁ : Fin r₁ ≃ S_real := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])).symm
  let e₂ : Fin r₂ ≃ S_pos := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])).symm
  let roots : Fin d → ℂ := fun i =>
    if h : i.1 < r₁ then (e₁ ⟨i.1, h⟩).1
    else if h2 : (i.1 - r₁) % 2 = 0 then (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).1
    else starRingEnd ℂ (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).1
  have hroots_im_real : ∀ i : Fin d, i.1 < r₁ → (roots i).im = 0 := by
    intro i hi; dsimp [roots]; simp only [hi, ↓reduceDIte]
    exact (Finset.mem_filter.mp (e₁ ⟨i.1, hi⟩).2).2
  have hroots_mem : ∀ i : Fin d, roots i ∈ S := by
    intro i; dsimp [roots]
    split_ifs with h h2
    · exact (Finset.mem_filter.mp (e₁ _).2).1
    · exact (Finset.mem_filter.mp (e₂ _).2).1
    · exact hS_star _ (Finset.mem_filter.mp (e₂ _).2).1
  have hinj : Function.Injective roots := by
    intro i j heq
    by_cases hi : i.1 < r₁ <;> by_cases hj : j.1 < r₁
    · dsimp [roots] at heq; simp only [hi, hj, ↓reduceDIte] at heq
      have h1 := e₁.injective (Subtype.ext heq)
      exact Fin.ext (congrArg (fun x : Fin r₁ => x.1) h1)
    · exfalso
      have him : (roots i).im = 0 := hroots_im_real i hi
      rw [heq] at him; dsimp [roots] at him; simp only [hj, ↓reduceDIte] at him
      split_ifs at him with h2
      · have := (Finset.mem_filter.mp (e₂ ⟨(j.1 - r₁) / 2, by omega⟩).2).2; linarith
      · have := (Finset.mem_filter.mp (e₂ ⟨(j.1 - r₁) / 2, by omega⟩).2).2; simp at him; linarith
    · exfalso
      have him : (roots j).im = 0 := hroots_im_real j hj
      rw [← heq] at him; dsimp [roots] at him; simp only [hi, ↓reduceDIte] at him
      split_ifs at him with h2
      · have := (Finset.mem_filter.mp (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).2).2; linarith
      · have := (Finset.mem_filter.mp (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).2).2; simp at him; linarith
    · dsimp [roots] at heq; simp only [hi, hj, ↓reduceDIte] at heq
      split_ifs at heq with h2i h2j h2j
      · have h1 := e₂.injective (Subtype.ext heq)
        have hv : (i.1 - r₁) / 2 = (j.1 - r₁) / 2 := congrArg (fun x : Fin r₂ => x.1) h1
        exact Fin.ext (by omega)
      · exfalso
        have hpos := (Finset.mem_filter.mp (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).2).2
        have hpos2 := (Finset.mem_filter.mp (e₂ ⟨(j.1 - r₁) / 2, by omega⟩).2).2
        have him := congrArg Complex.im heq; simp at him; linarith
      · exfalso
        have hpos := (Finset.mem_filter.mp (e₂ ⟨(i.1 - r₁) / 2, by omega⟩).2).2
        have hpos2 := (Finset.mem_filter.mp (e₂ ⟨(j.1 - r₁) / 2, by omega⟩).2).2
        have him := congrArg Complex.im heq; simp at him; linarith
      · have h1 := e₂.injective (Subtype.ext ((starRingEnd ℂ).injective heq))
        have hv : (i.1 - r₁) / 2 = (j.1 - r₁) / 2 := congrArg (fun x : Fin r₂ => x.1) h1
        exact Fin.ext (by omega)
  have hstar_eq : ∀ i : Fin d, starRingEnd ℂ (roots i) = roots (canonInv d r₁ r₂ hsum i) := by
    intro i
    dsimp [canonInv, roots]
    by_cases hi : i.1 < r₁
    · simp only [hi, ↓reduceDIte]
      have him := (Finset.mem_filter.mp (e₁ ⟨i.1, hi⟩).2).2
      exact Complex.conj_eq_iff_im.mpr him
    · by_cases h2 : (i.1 - r₁) % 2 = 0
      · have hne : ¬ (i.1 + 1 < r₁) := by omega
        have hodd : ¬ ((i.1 + 1 - r₁) % 2 = 0) := by omega
        have hdiv : (i.1 + 1 - r₁) / 2 = (i.1 - r₁) / 2 := by omega
        simp only [hi, h2, hne, hodd, ↓reduceDIte, hdiv]
      · have hne : ¬ (i.1 - 1 < r₁) := by omega
        have heven : (i.1 - 1 - r₁) % 2 = 0 := by omega
        have hdiv : (i.1 - 1 - r₁) / 2 = (i.1 - r₁) / 2 := by omega
        simp only [hi, h2, hne, heven, ↓reduceDIte, hdiv, Complex.conj_conj]
  have hsurj : ∀ z : ℂ, z ∈ S ↔ ∃ i : Fin d, roots i = z := by
    intro z
    constructor
    · intro hz
      have hcard_img : (Finset.univ.image roots).card = S.card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_fin, hS_card]
      have hsub : Finset.univ.image roots ⊆ S := by
        intro w hw; rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩; exact hroots_mem i
      have heqS : Finset.univ.image roots = S := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_img.symm)
      rw [← heqS] at hz
      rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact hroots_mem i
  have hprod : Pℂ = ∏ i : Fin d, (Polynomial.X - C (roots i)) := by
    have hcard_img : (Finset.univ.image roots).card = S.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin, hS_card]
    have hsub : Finset.univ.image roots ⊆ S := by
      intro w hw; rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩; exact hroots_mem i
    have heqS : Finset.univ.image roots = S := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_img.symm)
    rw [hPℂ_prod, ← heqS, Finset.prod_image (fun a _ b _ h => hinj h)]
  exact ⟨hsum, roots, hinj, hstar_eq, hroots_im_real, hsurj, hprod⟩

private lemma real_root_iff_mem_filter {P : Polynomial ℝ} (hmon : P.Monic) (x : ℝ) :
    P.eval x = 0 ↔ (x : ℂ) ∈ ((P.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im = 0)) := by
  have hne : P.map (algebraMap ℝ ℂ) ≠ 0 := (hmon.map _).ne_zero
  simp only [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
    Complex.ofReal_im, and_true]
  rw [Polynomial.eval_map]
  have hev : Polynomial.eval₂ (algebraMap ℝ ℂ) (x : ℂ) P = ((P.eval x : ℝ) : ℂ) := by
    simpa using (Polynomial.hom_eval₂ P (RingHom.id ℝ) (algebraMap ℝ ℂ) x).symm
  rw [hev, Complex.ofReal_eq_zero]

private lemma witness5_real_count :
    (((witnessQuintic (31 / 144) (1 / 64)).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = 5 := by
  let P := witnessQuintic (31 / 144) (1 / 64)
  let f : ℝ → ℝ := fun x => P.eval x
  have hf_eq : ∀ x, f x = x ^ 5 - x ^ 3 + (31 / 144 : ℝ) * x + 1 / 64 := by
    intro x; simp [f, P, witnessQuintic]
  have hf_cont : Continuous f := by
    have : f = fun x => x ^ 5 - x ^ 3 + (31 / 144 : ℝ) * x + 1 / 64 := funext hf_eq
    rw [this]; fun_prop
  have get_root_up : ∀ a b : ℝ, a < b → f a < 0 → 0 < f b → ∃ x ∈ Set.Ioo a b, f x = 0 := by
    intro a b hab ha hb
    rcases intermediate_value_Icc (le_of_lt hab) hf_cont.continuousOn ⟨le_of_lt ha, le_of_lt hb⟩ with ⟨x, hxI, hfx⟩
    refine ⟨x, ⟨lt_of_le_of_ne hxI.1 (fun h => by linarith [h ▸ hfx]),
                lt_of_le_of_ne hxI.2 (fun h => by linarith [h ▸ hfx])⟩, hfx⟩
  have get_root_dn : ∀ a b : ℝ, a < b → 0 < f a → f b < 0 → ∃ x ∈ Set.Ioo a b, f x = 0 := by
    intro a b hab ha hb
    rcases intermediate_value_Icc' (le_of_lt hab) hf_cont.continuousOn ⟨le_of_lt hb, le_of_lt ha⟩ with ⟨x, hxI, hfx⟩
    refine ⟨x, ⟨lt_of_le_of_ne hxI.1 (fun h => by linarith [h ▸ hfx]),
                lt_of_le_of_ne hxI.2 (fun h => by linarith [h ▸ hfx])⟩, hfx⟩
  rcases get_root_up (-1) (-7 / 10) (by norm_num) (by rw [hf_eq]; norm_num) (by rw [hf_eq]; norm_num) with ⟨x₁, hx₁I, hx₁⟩
  rcases get_root_dn (-7 / 10) (-1 / 4) (by norm_num) (by rw [hf_eq]; norm_num) (by rw [hf_eq]; norm_num) with ⟨x₂, hx₂I, hx₂⟩
  rcases get_root_up (-1 / 4) 0 (by norm_num) (by rw [hf_eq]; norm_num) (by rw [hf_eq]; norm_num) with ⟨x₃, hx₃I, hx₃⟩
  rcases get_root_dn 0 (7 / 10) (by norm_num) (by rw [hf_eq]; norm_num) (by rw [hf_eq]; norm_num) with ⟨x₄, hx₄I, hx₄⟩
  rcases get_root_up (7 / 10) 1 (by norm_num) (by rw [hf_eq]; norm_num) (by rw [hf_eq]; norm_num) with ⟨x₅, hx₅I, hx₅⟩
  let S_r := (P.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im = 0)
  have hsub : ({(x₁ : ℂ), (x₂ : ℂ), (x₃ : ℂ), (x₄ : ℂ), (x₅ : ℂ)} : Finset ℂ) ⊆ S_r := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₁).mp hx₁
    · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₂).mp hx₂
    · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₃).mp hx₃
    · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₄).mp hx₄
    · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₅).mp hx₅
  have h5_le : 5 ≤ S_r.card := by
    have hcard5 : ({(x₁ : ℂ), (x₂ : ℂ), (x₃ : ℂ), (x₄ : ℂ), (x₅ : ℂ)} : Finset ℂ).card = 5 := by
      have h12 : x₁ < x₂ := lt_trans hx₁I.2 hx₂I.1
      have h23 : x₂ < x₃ := lt_trans hx₂I.2 hx₃I.1
      have h34 : x₃ < x₄ := lt_trans hx₃I.2 hx₄I.1
      have h45 : x₄ < x₅ := lt_trans hx₄I.2 hx₅I.1
      have hne : ∀ a b : ℝ, a < b → (a : ℂ) ≠ (b : ℂ) := fun a b h hab => ne_of_lt h (Complex.ofReal_injective hab)
      simp [hne x₁ x₂ h12, hne x₁ x₃ (lt_trans h12 h23), hne x₁ x₄ (lt_trans (lt_trans h12 h23) h34),
            hne x₁ x₅ (lt_trans (lt_trans (lt_trans h12 h23) h34) h45),
            hne x₂ x₃ h23, hne x₂ x₄ (lt_trans h23 h34), hne x₂ x₅ (lt_trans (lt_trans h23 h34) h45),
            hne x₃ x₄ h34, hne x₃ x₅ (lt_trans h34 h45), hne x₄ x₅ h45]
    rw [← hcard5]; exact Finset.card_le_card hsub
  have hle5 : S_r.card ≤ 5 := by
    calc S_r.card ≤ (P.map (algebraMap ℝ ℂ)).roots.toFinset.card := Finset.card_filter_le _ _
      _ = (P.map (algebraMap ℝ ℂ)).roots.card := Multiset.toFinset_card_of_nodup witness5_nodup
      _ ≤ (P.map (algebraMap ℝ ℂ)).natDegree := Polynomial.card_roots' _
      _ = 5 := by rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective, witnessQuintic_natDegree]
  change S_r.card = 5; omega

private lemma witness3_real_count :
    (((witnessQuintic (1 / 4) (1 / 32)).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = 3 := by
  let P := witnessQuintic (1 / 4) (1 / 32)
  let f : ℝ → ℝ := fun x => x ^ 5 - x ^ 3 + (1 / 4 : ℝ) * x + 1 / 32
  have hf_eq : ∀ x, P.eval x = f x := fun x => by simp [f, P, witnessQuintic]
  have hf_cont : Continuous f := by dsimp [f]; fun_prop
  have get_root_up : ∀ a b : ℝ, a < b → f a < 0 → 0 < f b → ∃ x ∈ Set.Ioo a b, f x = 0 := by
    intro a b hab ha hb
    rcases intermediate_value_Icc (le_of_lt hab) hf_cont.continuousOn ⟨le_of_lt ha, le_of_lt hb⟩ with ⟨x, hxI, hfx⟩
    refine ⟨x, ⟨lt_of_le_of_ne hxI.1 (fun h => by linarith [h ▸ hfx]),
                lt_of_le_of_ne hxI.2 (fun h => by linarith [h ▸ hfx])⟩, hfx⟩
  have get_root_dn : ∀ a b : ℝ, a < b → 0 < f a → f b < 0 → ∃ x ∈ Set.Ioo a b, f x = 0 := by
    intro a b hab ha hb
    rcases intermediate_value_Icc' (le_of_lt hab) hf_cont.continuousOn ⟨le_of_lt hb, le_of_lt ha⟩ with ⟨x, hxI, hfx⟩
    refine ⟨x, ⟨lt_of_le_of_ne hxI.1 (fun h => by linarith [h ▸ hfx]),
                lt_of_le_of_ne hxI.2 (fun h => by linarith [h ▸ hfx])⟩, hfx⟩
  rcases get_root_up (-1) (-7 / 10) (by norm_num) (by dsimp [f]; norm_num) (by dsimp [f]; norm_num) with ⟨x₁, hx₁I, hx₁⟩
  rcases get_root_dn (-7 / 10) (-1 / 3) (by norm_num) (by dsimp [f]; norm_num) (by dsimp [f]; norm_num) with ⟨x₂, hx₂I, hx₂⟩
  rcases get_root_up (-1 / 3) 0 (by norm_num) (by dsimp [f]; norm_num) (by dsimp [f]; norm_num) with ⟨x₃, hx₃I, hx₃⟩
  let S_r := (P.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im = 0)
  have h3_le : 3 ≤ S_r.card := by
    have hsub : ({(x₁ : ℂ), (x₂ : ℂ), (x₃ : ℂ)} : Finset ℂ) ⊆ S_r := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₁).mp (by rw [hf_eq]; exact hx₁)
      · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₂).mp (by rw [hf_eq]; exact hx₂)
      · exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₃).mp (by rw [hf_eq]; exact hx₃)
    have h12 : x₁ < x₂ := lt_trans hx₁I.2 hx₂I.1
    have h23 : x₂ < x₃ := lt_trans hx₂I.2 hx₃I.1
    have hne : ∀ a b : ℝ, a < b → (a : ℂ) ≠ (b : ℂ) := fun a b h hab => ne_of_lt h (Complex.ofReal_injective hab)
    have hcard3 : ({(x₁ : ℂ), (x₂ : ℂ), (x₃ : ℂ)} : Finset ℂ).card = 3 := by
      simp [hne x₁ x₂ h12, hne x₁ x₃ (lt_trans h12 h23), hne x₂ x₃ h23]
    rw [← hcard3]; exact Finset.card_le_card hsub
  have hle3 : S_r.card ≤ 3 := by
    by_contra hgt
    have h4 : 4 ≤ S_r.card := by omega
    let R_set : Finset ℝ := S_r.image Complex.re
    have hR_card : R_set.card = S_r.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have haim := (Finset.mem_filter.mp ha).2
      have hbim := (Finset.mem_filter.mp hb).2
      exact Complex.ext hab (by rw [haim, hbim])
    have hR_root : ∀ x ∈ R_set, f x = 0 ∧ x < 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      have hzim := (Finset.mem_filter.mp hz).2
      have hz_eq : (z.re : ℂ) = z := Complex.ext rfl (by simp [hzim])
      have hfx : f z.re = 0 := by
        rw [← hf_eq]; exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) z.re).mpr (by rwa [hz_eq])
      refine ⟨hfx, ?_⟩
      by_contra hnn; push Not at hnn
      have hpos : 0 < f z.re := by
        have : f z.re = z.re * (z.re ^ 2 - 1 / 2) ^ 2 + 1 / 32 := by dsimp [f]; ring
        rw [this]; nlinarith [sq_nonneg (z.re ^ 2 - 1 / 2)]
      linarith
    let emb := R_set.orderEmbOfFin rfl
    have h01 : emb ⟨0, by omega⟩ < emb ⟨1, by omega⟩ := emb.strictMono (Fin.mk_lt_mk.mpr (by omega))
    have h12 : emb ⟨1, by omega⟩ < emb ⟨2, by omega⟩ := emb.strictMono (Fin.mk_lt_mk.mpr (by omega))
    have h23 : emb ⟨2, by omega⟩ < emb ⟨3, by omega⟩ := emb.strictMono (Fin.mk_lt_mk.mpr (by omega))
    have hf_deriv : ∀ x : ℝ, HasDerivAt f (5 * x ^ 4 - 3 * x ^ 2 + 1 / 4) x := by
      intro x
      have h5 : HasDerivAt (fun t : ℝ => t ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
      have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
      have h1 : HasDerivAt (fun t : ℝ => (1 / 4 : ℝ) * t) (1 / 4) x := by
        simpa using (hasDerivAt_id x).const_mul (1 / 4 : ℝ)
      have hc : HasDerivAt (fun _ : ℝ => (1 / 32 : ℝ)) 0 x := hasDerivAt_const x (1 / 32)
      convert ((h5.sub h3).add h1).add hc using 1; ring
    have rolle : ∀ a b : ℝ, a < b → f a = 0 → f b = 0 →
        ∃ c ∈ Set.Ioo a b, 5 * c ^ 4 - 3 * c ^ 2 + 1 / 4 = 0 := by
      intro a b hab ha hb
      rcases exists_deriv_eq_zero hab hf_cont.continuousOn (by rw [ha, hb]) with ⟨c, hcI, hdc⟩
      refine ⟨c, hcI, ?_⟩
      rw [(hf_deriv c).deriv] at hdc; exact hdc
    rcases rolle _ _ h01 (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1
        (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1 with ⟨c₁, hc₁I, hc₁⟩
    rcases rolle _ _ h12 (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1
        (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1 with ⟨c₂, hc₂I, hc₂⟩
    rcases rolle _ _ h23 (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1
        (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).1 with ⟨c₃, hc₃I, hc₃⟩
    have hc₃_neg : c₃ < 0 := lt_trans hc₃I.2 (hR_root _ (Finset.orderEmbOfFin_mem R_set rfl _)).2
    have hc₂_lt : c₂ < c₃ := lt_trans hc₂I.2 hc₃I.1
    have hc₁_lt : c₁ < c₂ := lt_trans hc₁I.2 hc₂I.1
    have hroot_class : ∀ c : ℝ, c < 0 → 5 * c ^ 4 - 3 * c ^ 2 + 1 / 4 = 0 →
        c = -Real.sqrt (1 / 2) ∨ c = -Real.sqrt (1 / 10) := by
      intro c hc_neg hc_eq
      have hfac : (c ^ 2 - 1 / 2) * (c ^ 2 - 1 / 10) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with hA | hB
      · left
        have hsq : c ^ 2 = (Real.sqrt (1 / 2)) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hm
        · exfalso; linarith [Real.sqrt_nonneg (1 / 2 : ℝ)]
        · exact hm
      · right
        have hsq : c ^ 2 = (Real.sqrt (1 / 10)) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hm
        · exfalso; linarith [Real.sqrt_nonneg (1 / 10 : ℝ)]
        · exact hm
    rcases hroot_class c₁ (lt_trans (lt_trans hc₁_lt hc₂_lt) hc₃_neg) hc₁ with h1 | h1 <;>
    rcases hroot_class c₂ (lt_trans hc₂_lt hc₃_neg) hc₂ with h2 | h2 <;>
    rcases hroot_class c₃ hc₃_neg hc₃ with h3 | h3 <;> linarith
  change S_r.card = 3; omega

private lemma witness1_real_count :
    (((witnessQuintic (4 / 9) (1 / 20)).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = 1 := by
  let P := witnessQuintic (4 / 9) (1 / 20)
  let f : ℝ → ℝ := fun x => x ^ 5 - x ^ 3 + (4 / 9 : ℝ) * x + 1 / 20
  have hf_eq : ∀ x, P.eval x = f x := fun x => by simp [f, P, witnessQuintic]
  have hf_cont : Continuous f := by dsimp [f]; fun_prop
  have hmem0 : (0 : ℝ) ∈ Set.Icc (f (-3 / 10)) (f 0) := ⟨by dsimp [f]; norm_num, by dsimp [f]; norm_num⟩
  rcases intermediate_value_Icc (show (-3 / 10 : ℝ) ≤ 0 by norm_num) hf_cont.continuousOn hmem0 with ⟨x₀, _, hx₀⟩
  let S_r := (P.map (algebraMap ℝ ℂ)).roots.toFinset.filter (fun z : ℂ => z.im = 0)
  have hx₀_mem : (x₀ : ℂ) ∈ S_r :=
    (real_root_iff_mem_filter (witnessQuintic_monic _ _) x₀).mp (by rw [hf_eq]; exact hx₀)
  have huniq : ∀ z ∈ S_r, z = (x₀ : ℂ) := by
    intro z hz
    have hzim := (Finset.mem_filter.mp hz).2
    have hz_eq : (z.re : ℂ) = z := Complex.ext rfl (by simp [hzim])
    have hfx : f z.re = 0 := by
      rw [← hf_eq]; exact (real_root_iff_mem_filter (witnessQuintic_monic _ _) z.re).mpr (by rwa [hz_eq])
    have hin_I : ∀ x : ℝ, f x = 0 → -3 / 10 < x ∧ x < 0 := by
      intro x hfx'
      have hform : f x = x * ((x ^ 2 - 1 / 2) ^ 2 + 7 / 36) + 1 / 20 := by dsimp [f]; ring
      constructor
      · by_contra hle; push Not at hle
        have hpos : (7 / 36 : ℝ) ≤ (x ^ 2 - 1 / 2) ^ 2 + 7 / 36 := by nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
        have : x * ((x ^ 2 - 1 / 2) ^ 2 + 7 / 36) ≤ (-3 / 10) * (7 / 36) := by nlinarith
        linarith
      · by_contra hge; push Not at hge
        have : 0 ≤ x * ((x ^ 2 - 1 / 2) ^ 2 + 7 / 36) := by nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
        linarith
    have hderiv : ∀ x : ℝ, HasDerivAt f (5 * x ^ 4 - 3 * x ^ 2 + 4 / 9) x := by
      intro x
      have h5 : HasDerivAt (fun t : ℝ => t ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
      have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
      have h1 : HasDerivAt (fun t : ℝ => (4 / 9 : ℝ) * t) (4 / 9) x := by
        simpa using (hasDerivAt_id x).const_mul (4 / 9 : ℝ)
      have hc : HasDerivAt (fun _ : ℝ => (1 / 20 : ℝ)) 0 x := hasDerivAt_const x (1 / 20)
      convert ((h5.sub h3).add h1).add hc using 1; ring
    have heq_re : z.re = x₀ := by
      by_contra hne
      have hI1 := hin_I z.re hfx
      have hI2 := hin_I x₀ hx₀
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rcases exists_deriv_eq_zero hlt hf_cont.continuousOn (by rw [hfx, hx₀]) with ⟨c, hcI, hdc⟩
        rw [(hderiv c).deriv] at hdc
        have hc2 : c ^ 2 ≤ 9 / 100 := by nlinarith [hcI.1, hcI.2, hI1.1, hI2.2]
        nlinarith [sq_nonneg (c ^ 2)]
      · rcases exists_deriv_eq_zero hgt hf_cont.continuousOn (by rw [hx₀, hfx]) with ⟨c, hcI, hdc⟩
        rw [(hderiv c).deriv] at hdc
        have hc2 : c ^ 2 ≤ 9 / 100 := by nlinarith [hcI.1, hcI.2, hI2.1, hI1.2]
        nlinarith [sq_nonneg (c ^ 2)]
    rw [← hz_eq, heq_re]
  have hS_eq : S_r = {(x₀ : ℂ)} := by
    ext z; simp only [Finset.mem_singleton]
    exact ⟨huniq z, fun h => h ▸ hx₀_mem⟩
  change S_r.card = 1
  rw [hS_eq, Finset.card_singleton]

private lemma deg6_witness_from_deg5 {A₂ A₁ : ℝ} (hA₁ : A₁ ≠ 0)
    (hnodup : ((witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)).roots.Nodup)
    {k : ℕ} (hk : (((witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = k) :
    (Polynomial.X * witnessQuintic A₂ A₁).Monic ∧
    (Polynomial.X * witnessQuintic A₂ A₁).natDegree = 6 ∧
    ((Polynomial.X * witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)).roots.Nodup ∧
    (((Polynomial.X * witnessQuintic A₂ A₁).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = k + 1 := by
  let Q := witnessQuintic A₂ A₁
  have hQmon := witnessQuintic_monic A₂ A₁
  have hQdeg := witnessQuintic_natDegree A₂ A₁
  have hmon6 : (Polynomial.X * Q).Monic := (Polynomial.monic_X).mul hQmon
  have hdeg6 : (Polynomial.X * Q).natDegree = 6 := by
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hQmon.ne_zero, Polynomial.natDegree_X, hQdeg]
  have hmap6 : (Polynomial.X * Q).map (algebraMap ℝ ℂ) = Polynomial.X * Q.map (algebraMap ℝ ℂ) := by
    simp
  have hroots6 : ((Polynomial.X * Q).map (algebraMap ℝ ℂ)).roots =
      0 ::ₘ (Q.map (algebraMap ℝ ℂ)).roots := by
    rw [hmap6, Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero (hQmon.map _).ne_zero),
      Polynomial.roots_X, Multiset.singleton_add]
  have h0_not_mem : (0 : ℂ) ∉ (Q.map (algebraMap ℝ ℂ)).roots := by
    rw [Polynomial.mem_roots (hQmon.map _).ne_zero, Polynomial.IsRoot]
    simp [Q, witnessQuintic, hA₁]
  have hnodup6 : ((Polynomial.X * Q).map (algebraMap ℝ ℂ)).roots.Nodup := by
    rw [hroots6, Multiset.nodup_cons]; exact ⟨h0_not_mem, hnodup⟩
  have hcard6 : (((Polynomial.X * Q).map (algebraMap ℝ ℂ)).roots.toFinset.filter
      (fun z : ℂ => z.im = 0)).card = k + 1 := by
    rw [hroots6, Multiset.toFinset_cons, Finset.filter_insert, if_pos Complex.zero_im,
      Finset.card_insert_of_notMem]
    · rw [hk]
    · intro hm; exact h0_not_mem (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hm).1)
  exact ⟨hmon6, hdeg6, hnodup6, hcard6⟩

private lemma exists_matching_witness {d r₁ r₂ : ℕ} (hd : d = 5 ∨ d = 6) (hr₁ : 1 ≤ r₁)
    (hsum : r₁ + 2 * r₂ = d) :
    ∃ (A₂s A₁s ts : ℝ) (zs : Fin d → ℂ),
      CircleCircleWitness (-1) A₂s A₁s 0 ts ∧
      Function.Injective zs ∧
      (∀ i : Fin d, starRingEnd ℂ (zs i) = zs (canonInv d r₁ r₂ hsum i)) ∧
      (if d = 5 then
        ∏ i : Fin d, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 5 - Polynomial.X ^ 3 + C (A₂s : ℂ) * Polynomial.X + C (A₁s : ℂ)
       else
        ∏ i : Fin d, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 6 - Polynomial.X ^ 4 + C (A₂s : ℂ) * Polynomial.X ^ 2 +
          C (A₁s : ℂ) * Polynomial.X) := by
  rcases hd with rfl | rfl
  · have hcases : (r₁ = 5 ∧ r₂ = 0) ∨ (r₁ = 3 ∧ r₂ = 1) ∨ (r₁ = 1 ∧ r₂ = 2) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases extract_root_tuple (witnessQuintic_monic (31 / 144) (1 / 64))
          (witnessQuintic_natDegree _ _) witness5_nodup with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      have hr1' := witness5_real_count
      refine ⟨31 / 144, 1 / 64, 1 / 12, zs, witness5_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [↓reduceIte]; rw [← hprod]; simp [witnessQuintic]
    · rcases extract_root_tuple (witnessQuintic_monic (1 / 4) (1 / 32))
          (witnessQuintic_natDegree _ _) witness3_nodup with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      have hr1' := witness3_real_count
      refine ⟨1 / 4, 1 / 32, 1 / 10, zs, witness3_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [↓reduceIte]; rw [← hprod]; simp [witnessQuintic]
    · rcases extract_root_tuple (witnessQuintic_monic (4 / 9) (1 / 20))
          (witnessQuintic_natDegree _ _) witness1_nodup with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      have hr1' := witness1_real_count
      refine ⟨4 / 9, 1 / 20, 1 / 3, zs, witness1_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [↓reduceIte]; rw [← hprod]; simp [witnessQuintic]
  · have hcases : (r₁ = 6 ∧ r₂ = 0) ∨ (r₁ = 4 ∧ r₂ = 1) ∨ (r₁ = 2 ∧ r₂ = 2) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases deg6_witness_from_deg5 (by norm_num) witness5_nodup witness5_real_count with
        ⟨hmon6, hdeg6, hnod6, hr1'⟩
      rcases extract_root_tuple hmon6 hdeg6 hnod6 with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      refine ⟨31 / 144, 1 / 64, 1 / 12, zs, witness5_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [show ¬(6 = 5) by decide, ↓reduceIte]; rw [← hprod]; simp [witnessQuintic]; ring
    · rcases deg6_witness_from_deg5 (by norm_num) witness3_nodup witness3_real_count with
        ⟨hmon6, hdeg6, hnod6, hr1'⟩
      rcases extract_root_tuple hmon6 hdeg6 hnod6 with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      refine ⟨1 / 4, 1 / 32, 1 / 10, zs, witness3_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [show ¬(6 = 5) by decide, ↓reduceIte]; rw [← hprod]; simp [witnessQuintic]; ring
    · rcases deg6_witness_from_deg5 (by norm_num) witness1_nodup witness1_real_count with
        ⟨hmon6, hdeg6, hnod6, hr1'⟩
      rcases extract_root_tuple hmon6 hdeg6 hnod6 with ⟨hsum', zs, hinj, hstar, _, _, hprod⟩
      refine ⟨4 / 9, 1 / 20, 1 / 3, zs, witness1_cc, hinj, ?_, ?_⟩
      · intro i; rw [hstar i]; congr 1; exact canonInv_congr hr1' (by omega) hsum' hsum i
      · simp only [show ¬(6 = 5) by decide, ↓reduceIte]; rw [← hprod]; simp [witnessQuintic]; ring

/-! ### Part 4: Real Lagrange Interpolation and Newton Power Sums -/

private lemma natDegree_sum_lt {R ι : Type*} [Semiring R] {s : Finset ι} {f : ι → Polynomial R}
    {d : ℕ} (hd : 0 < d) (h : ∀ i ∈ s, (f i).natDegree < d) :
    (∑ i ∈ s, f i).natDegree < d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hd]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (natDegree_add_le _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
              (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma exists_real_lagrange {d : ℕ} (hd : 0 < d) {α z : Fin d → ℂ} {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ i, σ (σ i) = i)
    (hinj : Function.Injective α)
    (hα : ∀ i, starRingEnd ℂ (α i) = α (σ i))
    (hz : ∀ i, starRingEnd ℂ (z i) = z (σ i)) :
    ∃ c : Fin d → ℝ, ∀ i : Fin d, ∑ k : Fin d, (c k : ℂ) * (α i) ^ k.1 = z i := by
  let L : Fin d → Polynomial ℂ := fun i =>
    ∏ j ∈ Finset.univ.erase i, C ((α i - α j)⁻¹) * (Polynomial.X - C (α j))
  let P : Polynomial ℂ := ∑ i : Fin d, C (z i) * L i
  have hL_eval : ∀ i k : Fin d, (L i).eval (α k) = if k = i then 1 else 0 := by
    intro i k; dsimp [L]; rw [Polynomial.eval_prod]
    by_cases hki : k = i
    · subst hki; rw [if_pos rfl]
      apply Finset.prod_eq_one; intro j hj
      have hij : α k - α j ≠ 0 := sub_ne_zero.mpr (fun heq => (Finset.ne_of_mem_erase hj).symm (hinj heq))
      simp [hij]
    · rw [if_neg hki]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩); simp
  have hP_eval : ∀ k : Fin d, P.eval (α k) = z k := by
    intro k; dsimp [P]
    rw [show (∑ i : Fin d, C (z i) * L i).eval (α k) = ∑ i : Fin d, (C (z i) * L i).eval (α k) from
      map_sum (Polynomial.evalRingHom (α k)) _ _]
    simp [hL_eval]
  have hL_deg : ∀ i : Fin d, (L i).natDegree < d := by
    intro i; dsimp [L]
    have h1 := Polynomial.natDegree_prod_le (Finset.univ.erase i)
      (fun j => C ((α i - α j)⁻¹) * (Polynomial.X - C (α j)))
    have h2 : ∀ j ∈ Finset.univ.erase i, (C ((α i - α j)⁻¹) * (Polynomial.X - C (α j))).natDegree ≤ 1 := by
      intro j _
      have hx : (Polynomial.X - C (α j)).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
      exact (natDegree_mul_le).trans (by simp [hx])
    have h3 := h1.trans (Finset.sum_le_sum h2)
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_fin] at h3
    omega
  have hP_deg : P.natDegree < d :=
    natDegree_sum_lt hd fun i _ => (natDegree_mul_le).trans_lt (by simp [hL_deg i])
  let Q : Polynomial ℂ := P.map (starRingEnd ℂ)
  have hQ_deg : Q.natDegree < d := by
    dsimp [Q]; rw [Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective]; exact hP_deg
  have hQ_eval : ∀ k : Fin d, Q.eval (α k) = z k := by
    intro k; dsimp [Q]
    have h1 : α k = starRingEnd ℂ (α (σ k)) := by rw [hα, hσ]
    rw [h1, Polynomial.eval_map]
    have hhom : Polynomial.eval₂ (starRingEnd ℂ) (starRingEnd ℂ (α (σ k))) P =
        starRingEnd ℂ (P.eval (α (σ k))) := by
      simpa using (Polynomial.hom_eval₂ P (RingHom.id ℂ) (starRingEnd ℂ) (α (σ k))).symm
    rw [hhom, hP_eval, hz, hσ]
  have hPQ : P = Q := by
    by_contra hne
    have hsub_ne : P - Q ≠ 0 := sub_ne_zero.mpr hne
    have hsub_deg : (P - Q).natDegree < d :=
      (natDegree_sub_le P Q).trans_lt (max_lt hP_deg hQ_deg)
    have hsub_roots : Finset.univ.image α ⊆ (P - Q).roots.toFinset := by
      intro w hw; rcases Finset.mem_image.mp hw with ⟨k, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub_ne, Polynomial.IsRoot, Polynomial.eval_sub,
        hP_eval, hQ_eval, sub_self]
    have hcard : d ≤ (P - Q).natDegree := by
      calc d = (Finset.univ.image α).card := by rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
        _ ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hsub_roots
        _ ≤ (P - Q).roots.card := Multiset.toFinset_card_le _
        _ ≤ (P - Q).natDegree := Polynomial.card_roots' _
    omega
  refine ⟨fun k => (P.coeff k.1).re, ?_⟩
  intro i
  rw [← hP_eval i, Polynomial.eval_eq_sum_range' hP_deg,
    Fin.sum_univ_eq_sum_range (fun k => ((P.coeff k).re : ℂ) * (α i) ^ k) d]
  apply Finset.sum_congr rfl
  intro k _
  have hreal : starRingEnd ℂ (P.coeff k) = P.coeff k := by
    have := congrArg (fun R => R.coeff k) hPQ.symm
    simpa [Q] using this
  have hcoe : ((P.coeff k).re : ℂ) = P.coeff k :=
    Complex.ext rfl (by simp [Complex.conj_eq_iff_im.mp hreal])
  rw [hcoe]

/-- Explicit power sum `∑ i, (y i)^m`. -/
def powSum {d : ℕ} (y : Fin d → ℂ) (m : ℕ) : ℂ := ∑ i : Fin d, (y i) ^ m

noncomputable def coeffA4 {d : ℕ} (y : Fin d → ℂ) : ℂ := -powSum y 2 / 2
noncomputable def coeffA2 {d : ℕ} (y : Fin d → ℂ) : ℂ := (powSum y 2 ^ 2 - 2 * powSum y 4) / 8
noncomputable def coeffA1 {d : ℕ} (y : Fin d → ℂ) : ℂ := -powSum y 5 / 5
noncomputable def coeffA0 {d : ℕ} (y : Fin d → ℂ) : ℂ :=
  if d = 5 then 0
  else -(coeffA2 y * powSum y 2 + coeffA4 y * powSum y 4 + powSum y 6) / 6

private lemma newton_deg5_zero13 (y : Fin 5 → ℂ) (hp1 : powSum y 1 = 0) (hp3 : powSum y 3 = 0) :
    ∏ i : Fin 5, (Polynomial.X - C (y i)) =
      Polynomial.X ^ 5 + C (coeffA4 y) * Polynomial.X ^ 3 + C (coeffA2 y) * Polynomial.X +
      C (coeffA1 y) := by
  let y0 := y 0; let y1 := y 1; let y2 := y 2; let y3 := y 3; let y4 := y 4
  have hp1' : y0 + y1 + y2 + y3 + y4 = 0 := by
    simpa [powSum, Fin.sum_univ_five, y0, y1, y2, y3, y4] using hp1
  have hp3' : y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 = 0 := by
    simpa [powSum, Fin.sum_univ_five, y0, y1, y2, y3, y4] using hp3
  have hprod : ∏ i : Fin 5, (Polynomial.X - C (y i)) =
      (Polynomial.X - C y0) * (Polynomial.X - C y1) * (Polynomial.X - C y2) *
      (Polynomial.X - C y3) * (Polynomial.X - C y4) := by
    simp [Fin.prod_univ_five, y0, y1, y2, y3, y4]
  rw [hprod]
  let p2 := y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2
  let p4 := y0 ^ 4 + y1 ^ 4 + y2 ^ 4 + y3 ^ 4 + y4 ^ 4
  let p5 := y0 ^ 5 + y1 ^ 5 + y2 ^ 5 + y3 ^ 5 + y4 ^ 5
  let e1 := y0 + y1 + y2 + y3 + y4
  let e2 := y0*y1 + y0*y2 + y0*y3 + y0*y4 + y1*y2 + y1*y3 + y1*y4 + y2*y3 + y2*y4 + y3*y4
  let e3 := y0*y1*y2 + y0*y1*y3 + y0*y1*y4 + y0*y2*y3 + y0*y2*y4 + y0*y3*y4 +
            y1*y2*y3 + y1*y2*y4 + y1*y3*y4 + y2*y3*y4
  let e4 := y0*y1*y2*y3 + y0*y1*y2*y4 + y0*y1*y3*y4 + y0*y2*y3*y4 + y1*y2*y3*y4
  let e5 := y0*y1*y2*y3*y4
  have hexp : (Polynomial.X - C y0) * (Polynomial.X - C y1) * (Polynomial.X - C y2) *
      (Polynomial.X - C y3) * (Polynomial.X - C y4) =
      Polynomial.X ^ 5 - C e1 * Polynomial.X ^ 4 + C e2 * Polynomial.X ^ 3 -
      C e3 * Polynomial.X ^ 2 + C e4 * Polynomial.X + C (-e5) := by
    simp only [e1, e2, e3, e4, e5, map_add, map_mul, map_neg]; ring
  have hn2 : 2 * e2 - e1 ^ 2 + p2 = 0 := by dsimp [e1, e2, p2]; ring
  have hn3 : 3 * e3 - e2 * e1 + e1 * p2 - (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3) = 0 := by
    dsimp [e1, e2, e3, p2]; ring
  have hn4 : 4 * e4 - e3 * e1 + e2 * p2 - e1 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3) + p4 = 0 := by
    dsimp [e1, e2, e3, e4, p2, p4]; ring
  have hn5 : 5 * e5 - e4 * e1 + e3 * p2 - e2 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3) +
      e1 * p4 - p5 = 0 := by
    dsimp [e1, e2, e3, e4, e5, p2, p4, p5]; ring
  have he1 : e1 = 0 := hp1'
  rw [he1] at hn2 hn3 hn4 hn5
  rw [hp3'] at hn3 hn4 hn5
  have he2 : e2 = -p2 / 2 := by linear_combination (1 / 2 : ℂ) * hn2
  have he3 : e3 = 0 := by linear_combination (1 / 3 : ℂ) * hn3
  rw [he2, he3] at hn4 hn5
  have he4 : e4 = (p2 ^ 2 - 2 * p4) / 8 := by linear_combination (1 / 4 : ℂ) * hn4
  have he5 : -e5 = -p5 / 5 := by linear_combination -(1 / 5 : ℂ) * hn5
  have hp2_eq : powSum y 2 = p2 := by simp [powSum, Fin.sum_univ_five, p2, y0, y1, y2, y3, y4]
  have hp4_eq : powSum y 4 = p4 := by simp [powSum, Fin.sum_univ_five, p4, y0, y1, y2, y3, y4]
  have hp5_eq : powSum y 5 = p5 := by simp [powSum, Fin.sum_univ_five, p5, y0, y1, y2, y3, y4]
  have hA4 : coeffA4 y = e2 := by rw [coeffA4, hp2_eq, he2]
  have hA2 : coeffA2 y = e4 := by rw [coeffA2, hp2_eq, hp4_eq, he4]
  have hA1 : coeffA1 y = -e5 := by rw [coeffA1, hp5_eq, he5]
  rw [hexp, he1, he3, ← hA4, ← hA2, ← hA1]; simp

private lemma newton_deg6_zero13 (y : Fin 6 → ℂ) (hp1 : powSum y 1 = 0) (hp3 : powSum y 3 = 0) :
    ∏ i : Fin 6, (Polynomial.X - C (y i)) =
      Polynomial.X ^ 6 + C (coeffA4 y) * Polynomial.X ^ 4 + C (coeffA2 y) * Polynomial.X ^ 2 +
      C (coeffA1 y) * Polynomial.X + C (coeffA0 y) := by
  let y0 := y 0; let y1 := y 1; let y2 := y 2; let y3 := y 3; let y4 := y 4; let y5 := y 5
  have hp1' : y0 + y1 + y2 + y3 + y4 + y5 = 0 := by
    simpa [powSum, Fin.sum_univ_six, y0, y1, y2, y3, y4, y5] using hp1
  have hp3' : y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3 = 0 := by
    simpa [powSum, Fin.sum_univ_six, y0, y1, y2, y3, y4, y5] using hp3
  have hprod : ∏ i : Fin 6, (Polynomial.X - C (y i)) =
      (Polynomial.X - C y0) * (Polynomial.X - C y1) * (Polynomial.X - C y2) *
      (Polynomial.X - C y3) * (Polynomial.X - C y4) * (Polynomial.X - C y5) := by
    simp [Fin.prod_univ_six, y0, y1, y2, y3, y4, y5]
  rw [hprod]
  let p2 := y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 + y5 ^ 2
  let p4 := y0 ^ 4 + y1 ^ 4 + y2 ^ 4 + y3 ^ 4 + y4 ^ 4 + y5 ^ 4
  let p5 := y0 ^ 5 + y1 ^ 5 + y2 ^ 5 + y3 ^ 5 + y4 ^ 5 + y5 ^ 5
  let p6 := y0 ^ 6 + y1 ^ 6 + y2 ^ 6 + y3 ^ 6 + y4 ^ 6 + y5 ^ 6
  let e1 := y0 + y1 + y2 + y3 + y4 + y5
  let e2 := y0*y1 + y0*y2 + y0*y3 + y0*y4 + y0*y5 + y1*y2 + y1*y3 + y1*y4 + y1*y5 +
            y2*y3 + y2*y4 + y2*y5 + y3*y4 + y3*y5 + y4*y5
  let e3 := y0*y1*y2 + y0*y1*y3 + y0*y1*y4 + y0*y1*y5 + y0*y2*y3 + y0*y2*y4 + y0*y2*y5 +
            y0*y3*y4 + y0*y3*y5 + y0*y4*y5 + y1*y2*y3 + y1*y2*y4 + y1*y2*y5 + y1*y3*y4 +
            y1*y3*y5 + y1*y4*y5 + y2*y3*y4 + y2*y3*y5 + y2*y4*y5 + y3*y4*y5
  let e4 := y0*y1*y2*y3 + y0*y1*y2*y4 + y0*y1*y2*y5 + y0*y1*y3*y4 + y0*y1*y3*y5 +
            y0*y1*y4*y5 + y0*y2*y3*y4 + y0*y2*y3*y5 + y0*y2*y4*y5 + y0*y3*y4*y5 +
            y1*y2*y3*y4 + y1*y2*y3*y5 + y1*y2*y4*y5 + y1*y3*y4*y5 + y2*y3*y4*y5
  let e5 := y0*y1*y2*y3*y4 + y0*y1*y2*y3*y5 + y0*y1*y2*y4*y5 + y0*y1*y3*y4*y5 +
            y0*y2*y3*y4*y5 + y1*y2*y3*y4*y5
  let e6 := y0*y1*y2*y3*y4*y5
  have hexp : (Polynomial.X - C y0) * (Polynomial.X - C y1) * (Polynomial.X - C y2) *
      (Polynomial.X - C y3) * (Polynomial.X - C y4) * (Polynomial.X - C y5) =
      Polynomial.X ^ 6 - C e1 * Polynomial.X ^ 5 + C e2 * Polynomial.X ^ 4 -
      C e3 * Polynomial.X ^ 3 + C e4 * Polynomial.X ^ 2 + C (-e5) * Polynomial.X + C e6 := by
    simp only [e1, e2, e3, e4, e5, e6, map_add, map_mul, map_neg]; ring
  have hn2 : 2 * e2 - e1 ^ 2 + p2 = 0 := by dsimp [e1, e2, p2]; ring
  have hn3 : 3 * e3 - e2 * e1 + e1 * p2 - (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3) = 0 := by
    dsimp [e1, e2, e3, p2]; ring
  have hn4 : 4 * e4 - e3 * e1 + e2 * p2 - e1 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3) + p4 = 0 := by
    dsimp [e1, e2, e3, e4, p2, p4]; ring
  have hn5 : 5 * e5 - e4 * e1 + e3 * p2 - e2 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3) +
      e1 * p4 - p5 = 0 := by
    dsimp [e1, e2, e3, e4, e5, p2, p4, p5]; ring
  have hn6 : 6 * e6 - e5 * e1 + e4 * p2 - e3 * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3) +
      e2 * p4 - e1 * p5 + p6 = 0 := by
    dsimp [e1, e2, e3, e4, e5, e6, p2, p4, p5, p6]; ring
  have he1 : e1 = 0 := hp1'
  rw [he1] at hn2 hn3 hn4 hn5 hn6
  rw [hp3'] at hn3 hn4 hn5 hn6
  have he2 : e2 = -p2 / 2 := by linear_combination (1 / 2 : ℂ) * hn2
  have he3 : e3 = 0 := by linear_combination (1 / 3 : ℂ) * hn3
  rw [he2, he3] at hn4 hn5
  have he4 : e4 = (p2 ^ 2 - 2 * p4) / 8 := by linear_combination (1 / 4 : ℂ) * hn4
  have he5 : -e5 = -p5 / 5 := by linear_combination -(1 / 5 : ℂ) * hn5
  have he6 : e6 = -(e4 * p2 + e2 * p4 + p6) / 6 := by
    rw [he3] at hn6; linear_combination (1 / 6 : ℂ) * hn6
  have hp2_eq : powSum y 2 = p2 := by simp [powSum, Fin.sum_univ_six, p2, y0, y1, y2, y3, y4, y5]
  have hp4_eq : powSum y 4 = p4 := by simp [powSum, Fin.sum_univ_six, p4, y0, y1, y2, y3, y4, y5]
  have hp5_eq : powSum y 5 = p5 := by simp [powSum, Fin.sum_univ_six, p5, y0, y1, y2, y3, y4, y5]
  have hp6_eq : powSum y 6 = p6 := by simp [powSum, Fin.sum_univ_six, p6, y0, y1, y2, y3, y4, y5]
  have hA4 : coeffA4 y = e2 := by rw [coeffA4, hp2_eq, he2]
  have hA2 : coeffA2 y = e4 := by rw [coeffA2, hp2_eq, hp4_eq, he4]
  have hA1 : coeffA1 y = -e5 := by rw [coeffA1, hp5_eq, he5]
  have hA0 : coeffA0 y = e6 := by
    rw [coeffA0, if_neg (by decide), hA2, hA4, hp2_eq, hp4_eq, hp6_eq, he6]
  rw [hexp, he1, he3, ← hA4, ← hA2, ← hA1, ← hA0]; simp

private lemma coeff_poly5 (e1 e2 e3 e4 e5 : ℂ) :
    let P : Polynomial ℂ := Polynomial.X ^ 5 - C e1 * Polynomial.X ^ 4 + C e2 * Polynomial.X ^ 3 -
      C e3 * Polynomial.X ^ 2 + C e4 * Polynomial.X - C e5
    P.coeff 4 = -e1 ∧ P.coeff 3 = e2 ∧ P.coeff 2 = -e3 ∧ P.coeff 1 = e4 ∧ P.coeff 0 = -e5 := by
  intro P; dsimp [P]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private lemma coeff_poly6 (e1 e2 e3 e4 e5 e6 : ℂ) :
    let P : Polynomial ℂ := Polynomial.X ^ 6 - C e1 * Polynomial.X ^ 5 + C e2 * Polynomial.X ^ 4 -
      C e3 * Polynomial.X ^ 3 + C e4 * Polynomial.X ^ 2 - C e5 * Polynomial.X + C e6
    P.coeff 5 = -e1 ∧ P.coeff 4 = e2 ∧ P.coeff 3 = -e3 ∧ P.coeff 2 = e4 ∧ P.coeff 1 = -e5 ∧ P.coeff 0 = e6 := by
  intro P; dsimp [P]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private lemma power_sum_mem_of_monic {d : ℕ} (hd : d = 5 ∨ d = 6)
    (f : Polynomial NeusisSubfield) (hmon : f.Monic) (hdeg : f.natDegree = d)
    (α : Fin d → ℂ)
    (hprod : f.map (algebraMap NeusisSubfield ℂ) = ∏ i : Fin d, (Polynomial.X - C (α i))) :
    ∀ m : ℕ, ∃ s : NeusisSubfield, (s : ℂ) = powSum α m := by
  have hcoeff : ∀ k : ℕ, ((f.coeff k : NeusisSubfield) : ℂ) =
      (f.map (algebraMap NeusisSubfield ℂ)).coeff k := by
    intro k; simp [Polynomial.coeff_map]; rfl
  have hbase : ∀ m : ℕ, m < d → ∃ s : NeusisSubfield, (s : ℂ) = powSum α m := by
    rcases hd with rfl | rfl
    · let y0 := α 0; let y1 := α 1; let y2 := α 2; let y3 := α 3; let y4 := α 4
      let e1 := y0 + y1 + y2 + y3 + y4
      let e2 := y0*y1 + y0*y2 + y0*y3 + y0*y4 + y1*y2 + y1*y3 + y1*y4 + y2*y3 + y2*y4 + y3*y4
      let e3 := y0*y1*y2 + y0*y1*y3 + y0*y1*y4 + y0*y2*y3 + y0*y2*y4 + y0*y3*y4 +
                y1*y2*y3 + y1*y2*y4 + y1*y3*y4 + y2*y3*y4
      let e4 := y0*y1*y2*y3 + y0*y1*y2*y4 + y0*y1*y3*y4 + y0*y2*y3*y4 + y1*y2*y3*y4
      let e5 := y0*y1*y2*y3*y4
      have hexp : f.map (algebraMap NeusisSubfield ℂ) =
          Polynomial.X ^ 5 - C e1 * Polynomial.X ^ 4 + C e2 * Polynomial.X ^ 3 -
          C e3 * Polynomial.X ^ 2 + C e4 * Polynomial.X - C e5 := by
        rw [hprod]
        simp only [Fin.prod_univ_five, e1, e2, e3, e4, e5, y0, y1, y2, y3, y4, map_add, map_mul]; ring
      have hc := coeff_poly5 e1 e2 e3 e4 e5
      rw [← hexp] at hc
      have he1 : ((f.coeff 4 : NeusisSubfield) : ℂ) = -e1 := by rw [hcoeff 4]; exact hc.1
      have he2 : ((f.coeff 3 : NeusisSubfield) : ℂ) = e2 := by rw [hcoeff 3]; exact hc.2.1
      have he3 : ((f.coeff 2 : NeusisSubfield) : ℂ) = -e3 := by rw [hcoeff 2]; exact hc.2.2.1
      have he4 : ((f.coeff 1 : NeusisSubfield) : ℂ) = e4 := by rw [hcoeff 1]; exact hc.2.2.2.1
      have h2K : (((2 : NeusisSubfield) : ℝ) : ℂ) = 2 := rfl
      have h3K : (((3 : NeusisSubfield) : ℝ) : ℂ) = 3 := rfl
      have h4K : (((4 : NeusisSubfield) : ℝ) : ℂ) = 4 := rfl
      have h5K : (((5 : NeusisSubfield) : ℝ) : ℂ) = 5 := rfl
      intro m hm
      interval_cases m
      · exact ⟨5, by rw [h5K]; simp [powSum]⟩
      · refine ⟨-f.coeff 4, ?_⟩
        push_cast; rw [he1]; simp only [powSum, Fin.sum_univ_five, e1, y0, y1, y2, y3, y4]; ring
      · refine ⟨(-f.coeff 4) ^ 2 - 2 * f.coeff 3, ?_⟩
        push_cast; rw [he1, he2, h2K]; simp only [powSum, Fin.sum_univ_five]; dsimp only [e1, e2, y0, y1, y2, y3, y4]; ring
      · refine ⟨(-f.coeff 4) ^ 3 - 3 * (-f.coeff 4) * f.coeff 3 + 3 * (-f.coeff 2), ?_⟩
        push_cast; rw [he1, he2, he3, h3K]; simp only [powSum, Fin.sum_univ_five]; dsimp only [e1, e2, e3, y0, y1, y2, y3, y4]; ring
      · refine ⟨(-f.coeff 4) ^ 4 - 4 * (-f.coeff 4) ^ 2 * f.coeff 3 + 2 * f.coeff 3 ^ 2 +
            4 * (-f.coeff 4) * (-f.coeff 2) - 4 * f.coeff 1, ?_⟩
        push_cast; rw [he1, he2, he3, he4, h2K, h4K]
        simp only [powSum, Fin.sum_univ_five]; dsimp only [e1, e2, e3, e4, y0, y1, y2, y3, y4]; ring
    · let y0 := α 0; let y1 := α 1; let y2 := α 2; let y3 := α 3; let y4 := α 4; let y5 := α 5
      let e1 := y0 + y1 + y2 + y3 + y4 + y5
      let e2 := y0*y1 + y0*y2 + y0*y3 + y0*y4 + y0*y5 + y1*y2 + y1*y3 + y1*y4 + y1*y5 +
                y2*y3 + y2*y4 + y2*y5 + y3*y4 + y3*y5 + y4*y5
      let e3 := y0*y1*y2 + y0*y1*y3 + y0*y1*y4 + y0*y1*y5 + y0*y2*y3 + y0*y2*y4 + y0*y2*y5 +
                y0*y3*y4 + y0*y3*y5 + y0*y4*y5 + y1*y2*y3 + y1*y2*y4 + y1*y2*y5 + y1*y3*y4 +
                y1*y3*y5 + y1*y4*y5 + y2*y3*y4 + y2*y3*y5 + y2*y4*y5 + y3*y4*y5
      let e4 := y0*y1*y2*y3 + y0*y1*y2*y4 + y0*y1*y2*y5 + y0*y1*y3*y4 + y0*y1*y3*y5 +
                y0*y1*y4*y5 + y0*y2*y3*y4 + y0*y2*y3*y5 + y0*y2*y4*y5 + y0*y3*y4*y5 +
                y1*y2*y3*y4 + y1*y2*y3*y5 + y1*y2*y4*y5 + y1*y3*y4*y5 + y2*y3*y4*y5
      let e5 := y0*y1*y2*y3*y4 + y0*y1*y2*y3*y5 + y0*y1*y2*y4*y5 + y0*y1*y3*y4*y5 +
                y0*y2*y3*y4*y5 + y1*y2*y3*y4*y5
      let e6 := y0*y1*y2*y3*y4*y5
      have hexp : f.map (algebraMap NeusisSubfield ℂ) =
          Polynomial.X ^ 6 - C e1 * Polynomial.X ^ 5 + C e2 * Polynomial.X ^ 4 -
          C e3 * Polynomial.X ^ 3 + C e4 * Polynomial.X ^ 2 - C e5 * Polynomial.X + C e6 := by
        rw [hprod]
        simp only [Fin.prod_univ_six, e1, e2, e3, e4, e5, e6, y0, y1, y2, y3, y4, y5, map_add, map_mul]; ring
      have hc := coeff_poly6 e1 e2 e3 e4 e5 e6
      rw [← hexp] at hc
      have he1 : ((f.coeff 5 : NeusisSubfield) : ℂ) = -e1 := by rw [hcoeff 5]; exact hc.1
      have he2 : ((f.coeff 4 : NeusisSubfield) : ℂ) = e2 := by rw [hcoeff 4]; exact hc.2.1
      have he3 : ((f.coeff 3 : NeusisSubfield) : ℂ) = -e3 := by rw [hcoeff 3]; exact hc.2.2.1
      have he4 : ((f.coeff 2 : NeusisSubfield) : ℂ) = e4 := by rw [hcoeff 2]; exact hc.2.2.2.1
      have he5 : ((f.coeff 1 : NeusisSubfield) : ℂ) = -e5 := by rw [hcoeff 1]; exact hc.2.2.2.2.1
      have h2K : (((2 : NeusisSubfield) : ℝ) : ℂ) = 2 := rfl
      have h3K : (((3 : NeusisSubfield) : ℝ) : ℂ) = 3 := rfl
      have h4K : (((4 : NeusisSubfield) : ℝ) : ℂ) = 4 := rfl
      have h5K : (((5 : NeusisSubfield) : ℝ) : ℂ) = 5 := rfl
      have h6K : (((6 : NeusisSubfield) : ℝ) : ℂ) = 6 := rfl
      intro m hm
      interval_cases m
      · exact ⟨6, by rw [h6K]; simp [powSum]⟩
      · refine ⟨-f.coeff 5, ?_⟩
        push_cast; rw [he1]; simp only [powSum, Fin.sum_univ_six, e1, y0, y1, y2, y3, y4, y5]; ring
      · refine ⟨(-f.coeff 5) ^ 2 - 2 * f.coeff 4, ?_⟩
        push_cast; rw [he1, he2, h2K]; simp only [powSum, Fin.sum_univ_six]; dsimp only [e1, e2, y0, y1, y2, y3, y4, y5]; ring
      · refine ⟨(-f.coeff 5) ^ 3 - 3 * (-f.coeff 5) * f.coeff 4 + 3 * (-f.coeff 3), ?_⟩
        push_cast; rw [he1, he2, he3, h3K]; simp only [powSum, Fin.sum_univ_six]; dsimp only [e1, e2, e3, y0, y1, y2, y3, y4, y5]; ring
      · refine ⟨(-f.coeff 5) ^ 4 - 4 * (-f.coeff 5) ^ 2 * f.coeff 4 + 2 * f.coeff 4 ^ 2 +
            4 * (-f.coeff 5) * (-f.coeff 3) - 4 * f.coeff 2, ?_⟩
        push_cast; rw [he1, he2, he3, he4, h2K, h4K]
        simp only [powSum, Fin.sum_univ_six]; dsimp only [e1, e2, e3, e4, y0, y1, y2, y3, y4, y5]; ring
      · refine ⟨(-f.coeff 5) ^ 5 - 5 * (-f.coeff 5) ^ 3 * f.coeff 4 + 5 * (-f.coeff 5) * f.coeff 4 ^ 2 +
            5 * (-f.coeff 5) ^ 2 * (-f.coeff 3) - 5 * f.coeff 4 * (-f.coeff 3) -
            5 * (-f.coeff 5) * f.coeff 2 + 5 * (-f.coeff 1), ?_⟩
        push_cast; rw [he1, he2, he3, he4, he5, h5K]
        simp only [powSum, Fin.sum_univ_six]; dsimp only [e1, e2, e3, e4, e5, y0, y1, y2, y3, y4, y5]; ring
  have hroot : ∀ i : Fin d, (α i) ^ d = -∑ j ∈ Finset.range d, ((f.coeff j : NeusisSubfield) : ℂ) * (α i) ^ j := by
    intro i
    have hev0 : (f.map (algebraMap NeusisSubfield ℂ)).eval (α i) = 0 := by
      rw [hprod, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hdeg_map : (f.map (algebraMap NeusisSubfield ℂ)).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective (algebraMap NeusisSubfield ℂ).injective, hdeg]
    rw [Polynomial.eval_eq_sum_range' (show (f.map (algebraMap NeusisSubfield ℂ)).natDegree < d + 1 by omega),
      Finset.sum_range_succ] at hev0
    have hlead : (f.map (algebraMap NeusisSubfield ℂ)).coeff d = 1 := by
      rw [← hdeg_map]; exact (hmon.map _).leadingCoeff
    rw [hlead, one_mul] at hev0
    have hsum_eq : ∑ j ∈ Finset.range d, (f.map (algebraMap NeusisSubfield ℂ)).coeff j * (α i) ^ j =
        ∑ j ∈ Finset.range d, ((f.coeff j : NeusisSubfield) : ℂ) * (α i) ^ j :=
      Finset.sum_congr rfl fun j _ => by rw [hcoeff j]
    rw [hsum_eq] at hev0
    linear_combination hev0
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m < d
    · exact hbase m hm
    · have hge : d ≤ m := by omega
      have hlt : ∀ j ∈ Finset.range d, m - d + j < m := by
        intro j hj; rw [Finset.mem_range] at hj; omega
      choose s hs using fun j (hj : j ∈ Finset.range d) => ih (m - d + j) (hlt j hj)
      refine ⟨-∑ j ∈ Finset.range d, f.coeff j * (if hj : j ∈ Finset.range d then s j hj else 0), ?_⟩
      push_cast
      have h1 : ∀ j ∈ Finset.range d,
          ((f.coeff j : NeusisSubfield) : ℂ) * ((if hj : j ∈ Finset.range d then s j hj else 0 : NeusisSubfield) : ℂ) =
          ((f.coeff j : NeusisSubfield) : ℂ) * powSum α (m - d + j) := by
        intro j hj; rw [dif_pos hj, hs j hj]
      rw [Finset.sum_congr rfl h1]
      dsimp [powSum]
      calc -(∑ j ∈ Finset.range d, ((f.coeff j : NeusisSubfield) : ℂ) * ∑ i : Fin d, (α i) ^ (m - d + j))
          = -(∑ i : Fin d, ∑ j ∈ Finset.range d, ((f.coeff j : NeusisSubfield) : ℂ) * (α i) ^ (m - d + j)) := by
            congr 1; simp_rw [Finset.mul_sum]; exact Finset.sum_comm
        _ = ∑ i : Fin d, (α i) ^ (m - d) * (-∑ j ∈ Finset.range d, ((f.coeff j : NeusisSubfield) : ℂ) * (α i) ^ j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl; intro i _
            rw [mul_neg, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl; intro j _
            rw [pow_add]; ring
        _ = ∑ i : Fin d, (α i) ^ m := by
            apply Finset.sum_congr rfl; intro i _
            rw [← hroot i, ← pow_add, Nat.sub_add_cancel hge]

private lemma eval_sum_mem_of_powSum_mem {d : ℕ} {α : Fin d → ℂ}
    (hpow : ∀ m : ℕ, ∃ s : NeusisSubfield, (s : ℂ) = powSum α m)
    (P : Polynomial NeusisSubfield) :
    ∃ s : NeusisSubfield, (s : ℂ) = ∑ i : Fin d, (P.map (algebraMap NeusisSubfield ℂ)).eval (α i) := by
  choose p hp using hpow
  refine ⟨∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * p k, ?_⟩
  push_cast
  have h1 : ∑ k ∈ Finset.range (P.natDegree + 1), ((P.coeff k : NeusisSubfield) : ℂ) * ((p k : NeusisSubfield) : ℂ) =
      ∑ k ∈ Finset.range (P.natDegree + 1), ((P.coeff k : NeusisSubfield) : ℂ) * ∑ i : Fin d, (α i) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [hp k]; rfl
  rw [h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hdeg_le : (P.map (algebraMap NeusisSubfield ℂ)).natDegree < P.natDegree + 1 :=
    Nat.lt_succ_of_le Polynomial.natDegree_map_le
  rw [Polynomial.eval_eq_sum_range' hdeg_le]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_map]; rfl

/-! ### Part 5: Witness Coefficients, Tangent Vector, Rational Approximation, and Contradiction -/

private lemma witness_root_coeffs {d : ℕ} (hd : d = 5 ∨ d = 6) {A₂s A₁s : ℝ} {zs : Fin d → ℂ}
    (hzs_prod : if d = 5 then
        ∏ i : Fin d, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 5 - Polynomial.X ^ 3 + C (A₂s : ℂ) * Polynomial.X + C (A₁s : ℂ)
       else
        ∏ i : Fin d, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 6 - Polynomial.X ^ 4 + C (A₂s : ℂ) * Polynomial.X ^ 2 +
          C (A₁s : ℂ) * Polynomial.X) :
    powSum zs 1 = 0 ∧ powSum zs 3 = 0 ∧
    coeffA4 zs = (-1 : ℂ) ∧ coeffA2 zs = (A₂s : ℂ) ∧ coeffA1 zs = (A₁s : ℂ) ∧ coeffA0 zs = 0 := by
  rcases hd with rfl | rfl
  · simp only [↓reduceIte] at hzs_prod
    let z0 := zs 0; let z1 := zs 1; let z2 := zs 2; let z3 := zs 3; let z4 := zs 4
    let e1 := z0 + z1 + z2 + z3 + z4
    let e2 := z0*z1 + z0*z2 + z0*z3 + z0*z4 + z1*z2 + z1*z3 + z1*z4 + z2*z3 + z2*z4 + z3*z4
    let e3 := z0*z1*z2 + z0*z1*z3 + z0*z1*z4 + z0*z2*z3 + z0*z2*z4 + z0*z3*z4 +
              z1*z2*z3 + z1*z2*z4 + z1*z3*z4 + z2*z3*z4
    let e4 := z0*z1*z2*z3 + z0*z1*z2*z4 + z0*z1*z3*z4 + z0*z2*z3*z4 + z1*z2*z3*z4
    let e5 := z0*z1*z2*z3*z4
    have hexp : Polynomial.X ^ 5 - C e1 * Polynomial.X ^ 4 + C e2 * Polynomial.X ^ 3 -
        C e3 * Polynomial.X ^ 2 + C e4 * Polynomial.X - C e5 =
        Polynomial.X ^ 5 - C (0 : ℂ) * Polynomial.X ^ 4 + C (-1 : ℂ) * Polynomial.X ^ 3 -
        C (0 : ℂ) * Polynomial.X ^ 2 + C (A₂s : ℂ) * Polynomial.X - C (-(A₁s : ℂ)) := by
      have hL : ∏ i : Fin 5, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 5 - C e1 * Polynomial.X ^ 4 + C e2 * Polynomial.X ^ 3 -
          C e3 * Polynomial.X ^ 2 + C e4 * Polynomial.X - C e5 := by
        simp only [Fin.prod_univ_five, e1, e2, e3, e4, e5, z0, z1, z2, z3, z4, map_add, map_mul]; ring
      rw [← hL, hzs_prod]; simp; ring
    have hcL := coeff_poly5 e1 e2 e3 e4 e5
    have hcR := coeff_poly5 0 (-1) 0 (A₂s : ℂ) (-(A₁s : ℂ))
    rw [hexp] at hcL
    have he1 : e1 = 0 := by linear_combination -(hcL.1.symm.trans hcR.1)
    have he3 : e3 = 0 := by linear_combination -(hcL.2.2.1.symm.trans hcR.2.2.1)
    have hp1 : powSum zs 1 = 0 := by simpa [powSum, Fin.sum_univ_five, e1, z0, z1, z2, z3, z4] using he1
    have hp3 : powSum zs 3 = 0 := by
      simp only [powSum, Fin.sum_univ_five]
      change z0 ^ 3 + z1 ^ 3 + z2 ^ 3 + z3 ^ 3 + z4 ^ 3 = 0
      have hn3 : z0 ^ 3 + z1 ^ 3 + z2 ^ 3 + z3 ^ 3 + z4 ^ 3 - e1 ^ 3 + 3 * e1 * e2 - 3 * e3 = 0 := by
        dsimp [e1, e2, e3]; ring
      linear_combination hn3 + (e1 ^ 2 - 3 * e2) * he1 + 3 * he3
    have hpol := newton_deg5_zero13 zs hp1 hp3
    rw [hzs_prod] at hpol
    have hpol' : Polynomial.X ^ 5 - C (0 : ℂ) * Polynomial.X ^ 4 + C (coeffA4 zs) * Polynomial.X ^ 3 -
        C (0 : ℂ) * Polynomial.X ^ 2 + C (coeffA2 zs) * Polynomial.X - C (-coeffA1 zs) =
        Polynomial.X ^ 5 - C (0 : ℂ) * Polynomial.X ^ 4 + C (-1 : ℂ) * Polynomial.X ^ 3 -
        C (0 : ℂ) * Polynomial.X ^ 2 + C (A₂s : ℂ) * Polynomial.X - C (-(A₁s : ℂ)) := by
      simp only [map_zero, map_one, zero_mul, sub_zero, map_neg, sub_neg_eq_add, neg_mul, one_mul]
      rw [← hpol]; ring
    have hc1 := coeff_poly5 0 (coeffA4 zs) 0 (coeffA2 zs) (-coeffA1 zs)
    rw [hpol'] at hc1
    have hA1 : coeffA1 zs = (A₁s : ℂ) := by
      have h := hc1.2.2.2.2.symm.trans hcR.2.2.2.2
      simpa using h
    exact ⟨hp1, hp3, hc1.2.1.symm.trans hcR.2.1, hc1.2.2.2.1.symm.trans hcR.2.2.2.1, hA1, by simp [coeffA0]⟩
  · simp only [show ¬(6 = 5) by decide, ↓reduceIte] at hzs_prod
    let z0 := zs 0; let z1 := zs 1; let z2 := zs 2; let z3 := zs 3; let z4 := zs 4; let z5 := zs 5
    let e1 := z0 + z1 + z2 + z3 + z4 + z5
    let e2 := z0*z1 + z0*z2 + z0*z3 + z0*z4 + z0*z5 + z1*z2 + z1*z3 + z1*z4 + z1*z5 +
              z2*z3 + z2*z4 + z2*z5 + z3*z4 + z3*z5 + z4*z5
    let e3 := z0*z1*z2 + z0*z1*z3 + z0*z1*z4 + z0*z1*z5 + z0*z2*z3 + z0*z2*z4 + z0*z2*z5 +
              z0*z3*z4 + z0*z3*z5 + z0*z4*z5 + z1*z2*z3 + z1*z2*z4 + z1*z2*z5 + z1*z3*z4 +
              z1*z3*z5 + z1*z4*z5 + z2*z3*z4 + z2*z3*z5 + z2*z4*z5 + z3*z4*z5
    let e4 := z0*z1*z2*z3 + z0*z1*z2*z4 + z0*z1*z2*z5 + z0*z1*z3*z4 + z0*z1*z3*z5 +
              z0*z1*z4*z5 + z0*z2*z3*z4 + z0*z2*z3*z5 + z0*z2*z4*z5 + z0*z3*z4*z5 +
              z1*z2*z3*z4 + z1*z2*z3*z5 + z1*z2*z4*z5 + z1*z3*z4*z5 + z2*z3*z4*z5
    let e5 := z0*z1*z2*z3*z4 + z0*z1*z2*z3*z5 + z0*z1*z2*z4*z5 + z0*z1*z3*z4*z5 +
              z0*z2*z3*z4*z5 + z1*z2*z3*z4*z5
    let e6 := z0*z1*z2*z3*z4*z5
    have hexp : Polynomial.X ^ 6 - C e1 * Polynomial.X ^ 5 + C e2 * Polynomial.X ^ 4 -
        C e3 * Polynomial.X ^ 3 + C e4 * Polynomial.X ^ 2 - C e5 * Polynomial.X + C e6 =
        Polynomial.X ^ 6 - C (0 : ℂ) * Polynomial.X ^ 5 + C (-1 : ℂ) * Polynomial.X ^ 4 -
        C (0 : ℂ) * Polynomial.X ^ 3 + C (A₂s : ℂ) * Polynomial.X ^ 2 - C (-(A₁s : ℂ)) * Polynomial.X + C 0 := by
      have hL : ∏ i : Fin 6, (Polynomial.X - C (zs i)) =
          Polynomial.X ^ 6 - C e1 * Polynomial.X ^ 5 + C e2 * Polynomial.X ^ 4 -
          C e3 * Polynomial.X ^ 3 + C e4 * Polynomial.X ^ 2 - C e5 * Polynomial.X + C e6 := by
        simp only [Fin.prod_univ_six, e1, e2, e3, e4, e5, e6, z0, z1, z2, z3, z4, z5, map_add, map_mul]; ring
      rw [← hL, hzs_prod]; simp; ring
    have hcL := coeff_poly6 e1 e2 e3 e4 e5 e6
    have hcR := coeff_poly6 0 (-1) 0 (A₂s : ℂ) (-(A₁s : ℂ)) 0
    rw [hexp] at hcL
    have he1 : e1 = 0 := by linear_combination -(hcL.1.symm.trans hcR.1)
    have he3 : e3 = 0 := by linear_combination -(hcL.2.2.1.symm.trans hcR.2.2.1)
    have hp1 : powSum zs 1 = 0 := by simpa [powSum, Fin.sum_univ_six, e1, z0, z1, z2, z3, z4, z5] using he1
    have hp3 : powSum zs 3 = 0 := by
      simp only [powSum, Fin.sum_univ_six]
      change z0 ^ 3 + z1 ^ 3 + z2 ^ 3 + z3 ^ 3 + z4 ^ 3 + z5 ^ 3 = 0
      have hn3 : z0 ^ 3 + z1 ^ 3 + z2 ^ 3 + z3 ^ 3 + z4 ^ 3 + z5 ^ 3 - e1 ^ 3 + 3 * e1 * e2 - 3 * e3 = 0 := by
        dsimp [e1, e2, e3]; ring
      linear_combination hn3 + (e1 ^ 2 - 3 * e2) * he1 + 3 * he3
    have hpol := newton_deg6_zero13 zs hp1 hp3
    rw [hzs_prod] at hpol
    have hpol' : Polynomial.X ^ 6 - C (0 : ℂ) * Polynomial.X ^ 5 + C (coeffA4 zs) * Polynomial.X ^ 4 -
        C (0 : ℂ) * Polynomial.X ^ 3 + C (coeffA2 zs) * Polynomial.X ^ 2 - C (-coeffA1 zs) * Polynomial.X + C (coeffA0 zs) =
        Polynomial.X ^ 6 - C (0 : ℂ) * Polynomial.X ^ 5 + C (-1 : ℂ) * Polynomial.X ^ 4 -
        C (0 : ℂ) * Polynomial.X ^ 3 + C (A₂s : ℂ) * Polynomial.X ^ 2 - C (-(A₁s : ℂ)) * Polynomial.X + C 0 := by
      simp only [map_zero, map_one, zero_mul, sub_zero, add_zero, map_neg, neg_mul, sub_neg_eq_add, one_mul]
      rw [← hpol]; ring
    have hc1 := coeff_poly6 0 (coeffA4 zs) 0 (coeffA2 zs) (-coeffA1 zs) (coeffA0 zs)
    rw [hpol'] at hc1
    have hA1 : coeffA1 zs = (A₁s : ℂ) := by
      have h := hc1.2.2.2.2.1.symm.trans hcR.2.2.2.2.1
      simpa using h
    exact ⟨hp1, hp3, hc1.2.1.symm.trans hcR.2.1, hc1.2.2.2.1.symm.trans hcR.2.2.2.1, hA1,
           hc1.2.2.2.2.2.symm.trans hcR.2.2.2.2.2⟩

private lemma exists_tangent_vector {d : ℕ} (hd : 3 ≤ d) {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ i, σ (σ i) = i) {zs : Fin d → ℂ}
    (hzs_inj : Function.Injective zs) (hzs_star : ∀ i, starRingEnd ℂ (zs i) = zs (σ i)) :
    ∃ vs : Fin d → ℂ,
      (∀ i, starRingEnd ℂ (vs i) = vs (σ i)) ∧
      ∑ i : Fin d, vs i = 0 ∧
      0 < (∑ i : Fin d, (zs i) ^ 2 * vs i).re := by
  let μ : ℂ := (1 / (d : ℂ)) * ∑ i : Fin d, (zs i) ^ 2
  have hμ_star : starRingEnd ℂ μ = μ := by
    dsimp [μ]
    rw [map_mul, map_div₀, map_one, map_natCast, map_sum]
    congr 1; rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl; intro i _; rw [map_pow, hzs_star, hσ]
  let vs : Fin d → ℂ := fun i => starRingEnd ℂ ((zs i) ^ 2 - μ)
  have hvs_star : ∀ i : Fin d, starRingEnd ℂ (vs i) = vs (σ i) := by
    intro i; dsimp [vs]
    rw [Complex.conj_conj, map_sub, map_pow, ← hzs_star i, Complex.conj_conj, hμ_star]
  have hvs_sum : ∑ i : Fin d, vs i = 0 := by
    dsimp [vs]
    rw [← map_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have : ∑ i : Fin d, (zs i) ^ 2 - (d : ℂ) * μ = 0 := by dsimp [μ]; field_simp [hd_ne]; ring
    rw [this, map_zero]
  have hB_pos : 0 < (∑ i : Fin d, (zs i) ^ 2 * vs i).re := by
    have heq : ∑ i : Fin d, (zs i) ^ 2 * vs i =
        ∑ i : Fin d, ((zs i) ^ 2 - μ) * starRingEnd ℂ ((zs i) ^ 2 - μ) := by
      have h1 : ∑ i : Fin d, μ * vs i = 0 := by rw [← Finset.mul_sum, hvs_sum, mul_zero]
      have h2 : ∑ i : Fin d, (zs i) ^ 2 * vs i - ∑ i : Fin d, μ * vs i =
          ∑ i : Fin d, ((zs i) ^ 2 - μ) * vs i := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h1, sub_zero] at h2; exact h2
    rw [heq, Complex.re_sum]
    have hterm_eq : ∀ i : Fin d, (((zs i) ^ 2 - μ) * starRingEnd ℂ ((zs i) ^ 2 - μ)).re =
        Complex.normSq ((zs i) ^ 2 - μ) := fun i => by rw [Complex.mul_conj, Complex.ofReal_re]
    simp_rw [hterm_eq]
    obtain ⟨j, hj⟩ : ∃ j : Fin d, (zs j) ^ 2 ≠ μ := by
      by_contra hall; push Not at hall
      have h0 := hall ⟨0, by omega⟩
      have h1 := hall ⟨1, by omega⟩
      have h2 := hall ⟨2, by omega⟩
      have h01 : zs ⟨0, by omega⟩ = -zs ⟨1, by omega⟩ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h0.trans h1.symm) with h | h
        · exfalso; have := congrArg Fin.val (hzs_inj h); dsimp at this; omega
        · exact h
      have h02 : zs ⟨0, by omega⟩ = -zs ⟨2, by omega⟩ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h0.trans h2.symm) with h | h
        · exfalso; have := congrArg Fin.val (hzs_inj h); dsimp at this; omega
        · exact h
      have h12 : zs ⟨1, by omega⟩ = zs ⟨2, by omega⟩ := by linear_combination h01 - h02
      have := congrArg Fin.val (hzs_inj h12); dsimp at this; omega
    apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    exact ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr (sub_ne_zero.mpr hj)⟩
  exact ⟨vs, hvs_star, hvs_sum, hB_pos⟩

/-- Part 5a: Rational line approximation + IVT root `s₀` near `0` keeping `(y i)` in the valid
open ball around `zs` with `S₃(y) = 0`. -/
private lemma exists_rational_line_solution {d : ℕ} (hd_pos : 0 < d)
    {σ : Equiv.Perm (Fin d)} (hσ : ∀ i, σ (σ i) = i)
    {roots zs vs : Fin d → ℂ} {i₀ i₁ : Fin d} {A₂s A₁s δ : ℝ}
    (hδ_pos : 0 < δ)
    (hinj : Function.Injective roots) (hstar : ∀ i, starRingEnd ℂ (roots i) = roots (σ i))
    (hzs_inj : Function.Injective zs) (hzs_star : ∀ i, starRingEnd ℂ (zs i) = zs (σ i))
    (hvs_star : ∀ i, starRingEnd ℂ (vs i) = vs (σ i))
    (hi₁_ne : i₁ ≠ i₀)
    (hzs_p1 : powSum zs 1 = 0) (hzs_p3 : powSum zs 3 = 0)
    (hzs_A4 : coeffA4 zs = (-1 : ℂ)) (hzs_A2 : coeffA2 zs = (A₂s : ℂ))
    (hzs_A1 : coeffA1 zs = (A₁s : ℂ)) (hzs_A0 : coeffA0 zs = 0)
    (hvs_sum : ∑ i : Fin d, vs i = 0)
    (hB_pos : 0 < (∑ i : Fin d, (zs i) ^ 2 * vs i).re) :
    let rawEval : (Fin d → ℝ) → Fin d → ℂ := fun c i => ∑ k : Fin d, (c k : ℂ) * (roots i) ^ k.1
    let Y : (Fin d → ℝ) → Fin d → ℂ := fun c i =>
      rawEval c i - (1 / (d : ℂ)) * ∑ j : Fin d, rawEval c j
    ∃ (c0 w0 : Fin d → ℚ) (ε s₀ : ℝ),
      0 < ε ∧
      0 < (powSum (fun i => Y (fun k => (c0 k : ℝ)) i + (ε : ℂ) * Y (fun k => (w0 k : ℝ)) i) 3).re ∧
      let y : Fin d → ℂ := fun i => Y (fun k => (c0 k : ℝ)) i + (s₀ : ℂ) * Y (fun k => (w0 k : ℝ)) i
      powSum y 1 = 0 ∧
      powSum y 3 = 0 ∧
      |(coeffA4 y).re - (-1)| < δ ∧ |(coeffA2 y).re - A₂s| < δ ∧
      |(coeffA1 y).re - A₁s| < δ ∧ |(coeffA0 y).re - 0| < δ ∧
      y i₀ ≠ y i₁ := by
  intro rawEval Y
  rcases exists_real_lagrange hd_pos hσ hinj hstar hzs_star with ⟨cs, hcs⟩
  rcases exists_real_lagrange hd_pos hσ hinj hstar hvs_star with ⟨ws, hws⟩
  have hY_cs : Y cs = zs := by
    funext i; dsimp [Y, rawEval]
    have hsum0 : ∑ j : Fin d, ∑ k : Fin d, (cs k : ℂ) * (roots j) ^ k.1 = 0 := by
      simp_rw [hcs]; simpa [powSum] using hzs_p1
    rw [hcs i, hsum0, mul_zero, sub_zero]
  have hY_ws : Y ws = vs := by
    funext i; dsimp [Y, rawEval]
    have hsum0 : ∑ j : Fin d, ∑ k : Fin d, (ws k : ℂ) * (roots j) ^ k.1 = 0 := by
      simp_rw [hws]; exact hvs_sum
    rw [hws i, hsum0, mul_zero, sub_zero]
  have hY_sum0 : ∀ c : Fin d → ℝ, powSum (Y c) 1 = 0 := by
    intro c; have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp [powSum, Y]
    simp only [pow_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp [hd_ne]; ring
  have hY_star : ∀ (c : Fin d → ℝ) (i : Fin d), starRingEnd ℂ (Y c i) = Y c (σ i) := by
    intro c i
    have hraw_star : ∀ j, starRingEnd ℂ (rawEval c j) = rawEval c (σ j) := by
      intro j; dsimp [rawEval]; rw [map_sum]
      apply Finset.sum_congr rfl; intro k _; rw [map_mul, map_pow, Complex.conj_ofReal, hstar j]
    have hsum_star : starRingEnd ℂ (∑ j : Fin d, rawEval c j) = ∑ j : Fin d, rawEval c j := by
      rw [map_sum, ← Equiv.sum_comp σ]; apply Finset.sum_congr rfl; intro j _; rw [hraw_star, hσ]
    dsimp [Y]; rw [map_sub, hraw_star, map_mul, map_div₀, map_one, map_natCast, hsum_star]
  have hpow_cont : ∀ m : ℕ, Continuous (fun y : Fin d → ℂ => powSum y m) := fun m =>
    continuous_finset_sum_aux Finset.univ (fun i (y : Fin d → ℂ) => (y i) ^ m)
      fun i _ => (continuous_apply i).pow m
  have hA4_cont : Continuous (fun y : Fin d → ℂ => (coeffA4 y).re) :=
    Complex.continuous_re.comp (((hpow_cont 2).neg).div_const 2)
  have hA2_cont : Continuous (fun y : Fin d → ℂ => (coeffA2 y).re) :=
    Complex.continuous_re.comp ((((hpow_cont 2).pow 2).sub (continuous_const.mul (hpow_cont 4))).div_const 8)
  have hA1_cont : Continuous (fun y : Fin d → ℂ => (coeffA1 y).re) :=
    Complex.continuous_re.comp (((hpow_cont 5).neg).div_const 5)
  have hA0_cont : Continuous (fun y : Fin d → ℂ => (coeffA0 y).re) := by
    dsimp [coeffA0]; split_ifs
    · exact continuous_const
    · have hA2c : Continuous (fun y : Fin d → ℂ => coeffA2 y) :=
        (((hpow_cont 2).pow 2).sub (continuous_const.mul (hpow_cont 4))).div_const 8
      have hA4c : Continuous (fun y : Fin d → ℂ => coeffA4 y) := ((hpow_cont 2).neg).div_const 2
      exact Complex.continuous_re.comp
        ((((hA2c.mul (hpow_cont 2)).add (hA4c.mul (hpow_cont 4))).add (hpow_cont 6)).neg.div_const 6)
  have hsep_cont : Continuous (fun y : Fin d → ℂ => dist (y i₀) (y i₁)) :=
    (continuous_apply i₀).dist (continuous_apply i₁)
  have hsep_pos : 0 < dist (zs i₀) (zs i₁) := dist_pos.mpr (fun h => hi₁_ne (hzs_inj h).symm)
  have hev_y : ∀ᶠ y in nhds zs,
      |(coeffA4 y).re - (-1)| < δ ∧ |(coeffA2 y).re - A₂s| < δ ∧
      |(coeffA1 y).re - A₁s| < δ ∧ |(coeffA0 y).re - 0| < δ ∧
      0 < dist (y i₀) (y i₁) := by
    have h4 : |(coeffA4 zs).re - (-1)| < δ := by rw [hzs_A4]; simp [hδ_pos]
    have h2 : |(coeffA2 zs).re - A₂s| < δ := by rw [hzs_A2]; simp [hδ_pos]
    have h1 : |(coeffA1 zs).re - A₁s| < δ := by rw [hzs_A1]; simp [hδ_pos]
    have h0 : |(coeffA0 zs).re - 0| < δ := by rw [hzs_A0]; simp [hδ_pos]
    refine (((hA4_cont.sub continuous_const).abs.continuousAt).eventually (Iio_mem_nhds h4)).and ?_
    refine (((hA2_cont.sub continuous_const).abs.continuousAt).eventually (Iio_mem_nhds h2)).and ?_
    refine (((hA1_cont.sub continuous_const).abs.continuousAt).eventually (Iio_mem_nhds h1)).and ?_
    exact (((hA0_cont.sub continuous_const).abs.continuousAt).eventually (Iio_mem_nhds h0)).and
      (hsep_cont.continuousAt.eventually (Ioi_mem_nhds hsep_pos))
  rw [Metric.eventually_nhds_iff] at hev_y
  rcases hev_y with ⟨ρ₀, hρ₀_pos, hρ₀⟩
  let S₃ : (Fin d → ℂ) → ℝ := fun y => (powSum y 3).re
  let B : ℝ := (∑ i : Fin d, (zs i) ^ 2 * vs i).re
  let C₃ : ℝ := (∑ i : Fin d, zs i * (vs i) ^ 2).re
  let D₃ : ℝ := (∑ i : Fin d, (vs i) ^ 3).re
  have hS₃_expand : ∀ s : ℝ, S₃ (fun i => zs i + (s : ℂ) * vs i) =
      s * (3 * B + 3 * C₃ * s + D₃ * s ^ 2) := by
    intro s; dsimp [S₃, powSum, B, C₃, D₃]
    have hsum_exp : ∑ i : Fin d, (zs i + (s : ℂ) * vs i) ^ 3 =
        powSum zs 3 + 3 * (s : ℂ) * ∑ i : Fin d, (zs i) ^ 2 * vs i +
        3 * (s : ℂ) ^ 2 * ∑ i : Fin d, zs i * (vs i) ^ 2 +
        (s : ℂ) ^ 3 * ∑ i : Fin d, (vs i) ^ 3 := by
      dsimp [powSum]; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum_exp, hzs_p3, zero_add]
    have hsq1 : ((s : ℂ) ^ 2).re = s ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hsq2 : ((s : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
    have hcu1 : ((s : ℂ) ^ 3).re = s ^ 3 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hcu2 : ((s : ℂ) ^ 3).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, add_zero, Complex.re_ofNat, Complex.im_ofNat, zero_mul, hsq1, hsq2, hcu1, hcu2]
    ring
  let M_vs : ℝ := ‖vs‖ + 1
  have hM_vs_pos : 0 < M_vs := by dsimp [M_vs]; positivity
  let ε : ℝ := min 1 (min (ρ₀ / (3 * M_vs)) (B / (3 * |C₃| + |D₃| + 1)))
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hε_le1 : ε ≤ 1 := min_le_left _ _
  have hε_vs : ε * ‖vs‖ < ρ₀ / 3 := by
    have h1 : ε ≤ ρ₀ / (3 * M_vs) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : ε * M_vs ≤ ρ₀ / 3 := by
      have := (le_div_iff₀ (show (0 : ℝ) < 3 * M_vs by positivity)).mp h1; linarith
    have hlt : ‖vs‖ < M_vs := by dsimp [M_vs]; linarith
    nlinarith [norm_nonneg vs]
  have hε_S3 : S₃ (fun i => zs i + ((-ε : ℝ) : ℂ) * vs i) < 0 ∧
      0 < S₃ (fun i => zs i + ((ε : ℝ) : ℂ) * vs i) := by
    have h1 : ε ≤ B / (3 * |C₃| + |D₃| + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have hden_pos : 0 < 3 * |C₃| + |D₃| + 1 := by positivity
    have h2 : (3 * |C₃| + |D₃| + 1) * ε ≤ B := by
      have := (le_div_iff₀ hden_pos).mp h1; linarith
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have hbd : |3 * C₃ * ε + D₃ * ε ^ 2| < 3 * B := by
      calc |3 * C₃ * ε + D₃ * ε ^ 2| ≤ |3 * C₃ * ε| + |D₃ * ε ^ 2| := abs_add_le _ _
        _ = 3 * |C₃| * ε + |D₃| * ε ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hε_pos,
                abs_mul, abs_of_pos (sq_pos_of_pos hε_pos)]
        _ ≤ (3 * |C₃| + |D₃|) * ε := by nlinarith [abs_nonneg D₃]
        _ < (3 * |C₃| + |D₃| + 1) * ε := by nlinarith
        _ ≤ B := h2
        _ < 3 * B := by linarith [hB_pos]
    have hbd_neg : |3 * C₃ * (-ε) + D₃ * (-ε) ^ 2| < 3 * B := by
      calc |3 * C₃ * (-ε) + D₃ * (-ε) ^ 2| ≤ |3 * C₃ * (-ε)| + |D₃ * (-ε) ^ 2| := abs_add_le _ _
        _ = 3 * |C₃| * ε + |D₃| * ε ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_neg, abs_of_pos hε_pos,
                abs_mul, neg_sq, abs_of_pos (sq_pos_of_pos hε_pos)]
        _ ≤ (3 * |C₃| + |D₃|) * ε := by nlinarith [abs_nonneg D₃]
        _ < (3 * |C₃| + |D₃| + 1) * ε := by nlinarith
        _ ≤ B := h2
        _ < 3 * B := by linarith [hB_pos]
    constructor
    · rw [hS₃_expand (-ε)]
      have hpos : 0 < 3 * B + 3 * C₃ * (-ε) + D₃ * (-ε) ^ 2 := by
        have := (abs_lt.mp hbd_neg).1; linarith
      nlinarith
    · rw [hS₃_expand ε]
      have hpos : 0 < 3 * B + 3 * C₃ * ε + D₃ * ε ^ 2 := by
        have := (abs_lt.mp hbd).1; linarith
      nlinarith
  have hraw_cont : ∀ i : Fin d, Continuous (fun c : Fin d → ℝ => rawEval c i) := fun i =>
    continuous_finset_sum_aux Finset.univ (fun k (c : Fin d → ℝ) => (c k : ℂ) * (roots i) ^ k.1)
      fun k _ => (Complex.continuous_ofReal.comp (continuous_apply k)).mul continuous_const
  have hY_cont : Continuous Y := continuous_pi fun i =>
    (hraw_cont i).sub (continuous_const.mul (continuous_finset_sum_aux Finset.univ
      (fun j c => rawEval c j) fun j _ => hraw_cont j))
  have hS₃_cont : Continuous S₃ := Complex.continuous_re.comp (hpow_cont 3)
  let F_neg_fn : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun cw =>
    S₃ (fun i => Y cw.1 i + ((-ε : ℝ) : ℂ) * Y cw.2 i)
  let F_pos_fn : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun cw =>
    S₃ (fun i => Y cw.1 i + ((ε : ℝ) : ℂ) * Y cw.2 i)
  have hFn_cont : Continuous F_neg_fn :=
    hS₃_cont.comp (continuous_pi fun i =>
      ((continuous_apply i).comp (hY_cont.comp continuous_fst)).add
        (continuous_const.mul ((continuous_apply i).comp (hY_cont.comp continuous_snd))))
  have hFp_cont : Continuous F_pos_fn :=
    hS₃_cont.comp (continuous_pi fun i =>
      ((continuous_apply i).comp (hY_cont.comp continuous_fst)).add
        (continuous_const.mul ((continuous_apply i).comp (hY_cont.comp continuous_snd))))
  have hev_cw : ∀ᶠ cw : (Fin d → ℝ) × (Fin d → ℝ) in nhds (cs, ws),
      dist (Y cw.1) zs < ρ₀ / 3 ∧ dist (Y cw.2) vs < ρ₀ / (3 * ε) ∧
      F_neg_fn cw < 0 ∧ 0 < F_pos_fn cw := by
    have h1 : ContinuousAt (fun cw : (Fin d → ℝ) × (Fin d → ℝ) => dist (Y cw.1) zs) (cs, ws) :=
      (hY_cont.comp continuous_fst).continuousAt.dist continuousAt_const
    have h2 : ContinuousAt (fun cw : (Fin d → ℝ) × (Fin d → ℝ) => dist (Y cw.2) vs) (cs, ws) :=
      (hY_cont.comp continuous_snd).continuousAt.dist continuousAt_const
    refine (h1.eventually (Iio_mem_nhds (by dsimp only; rw [hY_cs, dist_self]; positivity))).and ?_
    refine (h2.eventually (Iio_mem_nhds (by dsimp only; rw [hY_ws, dist_self]; positivity))).and ?_
    refine (hFn_cont.continuousAt.eventually (Iio_mem_nhds (by
      dsimp [F_neg_fn]; rw [hY_cs, hY_ws]; exact hε_S3.1))).and ?_
    exact hFp_cont.continuousAt.eventually (Ioi_mem_nhds (by
      dsimp [F_pos_fn]; rw [hY_cs, hY_ws]; exact hε_S3.2))
  rw [Metric.eventually_nhds_iff] at hev_cw
  rcases hev_cw with ⟨η_cw, hη_cw_pos, hη_cw⟩
  have pick_rat : ∀ x : ℝ, ∃ q : ℚ, |((q : ℝ)) - x| < η_cw := by
    intro x
    rcases exists_rat_btwn (show x - η_cw < x + η_cw by linarith) with ⟨q, h1, h2⟩
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose c0 hc0 using fun k : Fin d => pick_rat (cs k)
  choose w0 hw0 using fun k : Fin d => pick_rat (ws k)
  let c0ℝ : Fin d → ℝ := fun k => (c0 k : ℝ)
  let w0ℝ : Fin d → ℝ := fun k => (w0 k : ℝ)
  have hdist_cw : dist (c0ℝ, w0ℝ) (cs, ws) < η_cw := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor <;> rw [dist_pi_lt_iff hη_cw_pos] <;> intro k
    · simpa [Real.dist_eq, c0ℝ] using hc0 k
    · simpa [Real.dist_eq, w0ℝ] using hw0 k
  rcases hη_cw hdist_cw with ⟨hYc_dist, hYw_dist, hF_neg, hF_pos⟩
  let h_cub : ℝ → ℝ := fun s => S₃ (fun i => Y c0ℝ i + (s : ℂ) * Y w0ℝ i)
  have hh_cont : Continuous h_cub :=
    hS₃_cont.comp (continuous_pi fun i =>
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  rcases intermediate_value_Icc (show -ε ≤ ε by linarith) hh_cont.continuousOn
      ⟨le_of_lt hF_neg, le_of_lt hF_pos⟩ with ⟨s₀, hs₀I, hs₀_zero⟩
  let y : Fin d → ℂ := fun i => Y c0ℝ i + (s₀ : ℂ) * Y w0ℝ i
  have hy_star : ∀ i : Fin d, starRingEnd ℂ (y i) = y (σ i) := by
    intro i; dsimp [y]; rw [map_add, map_mul, hY_star c0ℝ i, hY_star w0ℝ i, Complex.conj_ofReal]
  have hy_p1 : powSum y 1 = 0 := by
    dsimp [powSum, y]
    simp only [pow_one, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := hY_sum0 c0ℝ; have h2 := hY_sum0 w0ℝ
    simp only [powSum, pow_one] at h1 h2; rw [h1, h2, mul_zero, add_zero]
  have hy_p3 : powSum y 3 = 0 := by
    have him : (powSum y 3).im = 0 := by
      have hst : starRingEnd ℂ (powSum y 3) = powSum y 3 := by
        dsimp [powSum]; rw [map_sum, ← Equiv.sum_comp σ]
        apply Finset.sum_congr rfl; intro i _; rw [map_pow, hy_star, hσ]
      exact Complex.conj_eq_iff_im.mp hst
    exact Complex.ext (by simpa [h_cub, S₃, y] using hs₀_zero) him
  have hy_dist : dist y zs < ρ₀ := by
    rw [dist_pi_lt_iff hρ₀_pos]
    intro i
    have h1 : dist (Y c0ℝ i) (zs i) < ρ₀ / 3 :=
      lt_of_le_of_lt (dist_le_pi_dist (Y c0ℝ) zs i) hYc_dist
    have h2 : dist (Y w0ℝ i) (vs i) < ρ₀ / (3 * ε) :=
      lt_of_le_of_lt (dist_le_pi_dist (Y w0ℝ) vs i) hYw_dist
    have hs₀_abs : |s₀| ≤ ε := abs_le.mpr ⟨hs₀I.1, hs₀I.2⟩
    have h3 : ‖(s₀ : ℂ) * (Y w0ℝ i - vs i)‖ < ρ₀ / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← dist_eq_norm]
      have hlt : |s₀| * dist (Y w0ℝ i) (vs i) ≤ ε * dist (Y w0ℝ i) (vs i) :=
        mul_le_mul_of_nonneg_right hs₀_abs dist_nonneg
      have hlt2 : ε * dist (Y w0ℝ i) (vs i) < ρ₀ / 3 := by
        calc ε * dist (Y w0ℝ i) (vs i) < ε * (ρ₀ / (3 * ε)) := mul_lt_mul_of_pos_left h2 hε_pos
          _ = ρ₀ / 3 := by field_simp [ne_of_gt hε_pos]
      linarith
    have h4 : ‖(s₀ : ℂ) * vs i‖ < ρ₀ / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hvi : ‖vs i‖ ≤ ‖vs‖ := norm_le_pi_norm vs i
      have : |s₀| * ‖vs i‖ ≤ ε * ‖vs‖ := mul_le_mul hs₀_abs hvi (norm_nonneg _) (le_of_lt hε_pos)
      linarith
    have hsplit : y i - zs i = (Y c0ℝ i - zs i) + (s₀ : ℂ) * (Y w0ℝ i - vs i) + (s₀ : ℂ) * vs i := by
      dsimp [y]; ring
    rw [dist_eq_norm, hsplit]
    calc ‖(Y c0ℝ i - zs i) + (s₀ : ℂ) * (Y w0ℝ i - vs i) + (s₀ : ℂ) * vs i‖
        ≤ ‖(Y c0ℝ i - zs i) + (s₀ : ℂ) * (Y w0ℝ i - vs i)‖ + ‖(s₀ : ℂ) * vs i‖ := norm_add_le _ _
      _ ≤ ‖Y c0ℝ i - zs i‖ + ‖(s₀ : ℂ) * (Y w0ℝ i - vs i)‖ + ‖(s₀ : ℂ) * vs i‖ := by
          linarith [norm_add_le (Y c0ℝ i - zs i) ((s₀ : ℂ) * (Y w0ℝ i - vs i))]
      _ = dist (Y c0ℝ i) (zs i) + ‖(s₀ : ℂ) * (Y w0ℝ i - vs i)‖ + ‖(s₀ : ℂ) * vs i‖ := by
          rw [dist_eq_norm]
      _ < ρ₀ / 3 + ρ₀ / 3 + ρ₀ / 3 := by linarith
      _ = ρ₀ := by ring
  rcases hρ₀ hy_dist with ⟨hA4_ball, hA2_ball, hA1_ball, hA0_ball, hy_sep⟩
  exact ⟨c0, w0, ε, s₀, hε_pos, hF_pos, hy_p1, hy_p3, hA4_ball, hA2_ball, hA1_ball, hA0_ball,
         dist_pos.mp hy_sep⟩

/-- Main Theorem for degrees 5 and 6: No monic irreducible polynomial of degree `5` or `6` over
`NeusisSubfield` can have a real root! -/
private theorem not_irreducible_deg5_or_6_with_real_root {d : ℕ} (hd : d = 5 ∨ d = 6)
    (f : Polynomial NeusisSubfield) (hmon : f.Monic) (hdeg : f.natDegree = d)
    (hirr : Irreducible f) {α : ℝ} (hα : Polynomial.aeval α f = 0) : False := by
  have hd_pos : 0 < d := by omega
  let fℝ : Polynomial ℝ := f.map (algebraMap NeusisSubfield ℝ)
  have hfℝ_mon : fℝ.Monic := hmon.map _
  have hfℝ_deg : fℝ.natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap NeusisSubfield ℝ).injective, hdeg]
  have hfℂ_eq : fℝ.map (algebraMap ℝ ℂ) = f.map (algebraMap NeusisSubfield ℂ) := by
    rw [Polynomial.map_map]; congr 1
  have hnodup : (fℝ.map (algebraMap ℝ ℂ)).roots.Nodup := by
    rw [hfℂ_eq]; exact Polynomial.nodup_roots hirr.separable.map
  rcases extract_root_tuple hfℝ_mon hfℝ_deg hnodup with ⟨hsum, roots, hinj, hstar, _, hsurj, hprod⟩
  let S := (fℝ.map (algebraMap ℝ ℂ)).roots.toFinset
  let r₁ := (S.filter (fun z : ℂ => z.im = 0)).card
  let r₂ := (S.filter (fun z : ℂ => 0 < z.im)).card
  have hα_eval : fℝ.eval α = 0 := by
    rw [Polynomial.eval_map]; simpa [Polynomial.aeval_def] using hα
  have hα_mem_S : (α : ℂ) ∈ S :=
    (Finset.mem_filter.mp ((real_root_iff_mem_filter hfℝ_mon α).mp hα_eval)).1
  have hr₁_pos : 1 ≤ r₁ :=
    Finset.one_le_card.mpr ⟨(α : ℂ), (real_root_iff_mem_filter hfℝ_mon α).mp hα_eval⟩
  rcases (hsurj (α : ℂ)).mp hα_mem_S with ⟨i₀, hi₀⟩
  obtain ⟨i₁, hi₁_ne⟩ : ∃ i₁ : Fin d, i₁ ≠ i₀ := by
    by_cases h0 : i₀ = ⟨0, hd_pos⟩
    · exact ⟨⟨1, by omega⟩, fun h => by rw [h0] at h; have := congrArg Fin.val h; dsimp at this; omega⟩
    · exact ⟨⟨0, hd_pos⟩, Ne.symm h0⟩
  rcases exists_matching_witness hd hr₁_pos hsum with ⟨A₂s, A₁s, ts, zs, hwit, hzs_inj, hzs_star, hzs_prod⟩
  rcases circleCircleValid_eventually_of_witness hwit with ⟨δ, hδ_pos, hδ_valid⟩
  rcases witness_root_coeffs hd hzs_prod with ⟨hzs_p1, hzs_p3, hzs_A4, hzs_A2, hzs_A1, hzs_A0⟩
  rcases exists_tangent_vector (by omega) (canonInv_invol d r₁ r₂ hsum) hzs_inj hzs_star with
    ⟨vs, hvs_star, hvs_sum, hB_pos⟩
  rcases exists_rational_line_solution hd_pos (canonInv_invol d r₁ r₂ hsum) hδ_pos
      hinj hstar hzs_inj hzs_star hvs_star hi₁_ne
      hzs_p1 hzs_p3 hzs_A4 hzs_A2 hzs_A1 hzs_A0 hvs_sum hB_pos with
    ⟨c0, w0, ε, s₀, hε_pos, hF_pos, hy_p1, hy_p3, hA4_ball, hA2_ball, hA1_ball, hA0_ball, hy_sep⟩
  let rawEval : (Fin d → ℝ) → Fin d → ℂ := fun c i => ∑ k : Fin d, (c k : ℂ) * (roots i) ^ k.1
  let Y : (Fin d → ℝ) → Fin d → ℂ := fun c i =>
    rawEval c i - (1 / (d : ℂ)) * ∑ j : Fin d, rawEval c j
  let c0ℝ : Fin d → ℝ := fun k => (c0 k : ℝ)
  let w0ℝ : Fin d → ℝ := fun k => (w0 k : ℝ)
  let y : Fin d → ℂ := fun i => Y c0ℝ i + (s₀ : ℂ) * Y w0ℝ i
  have hvalid : CircleCircleValid (coeffA4 y).re (coeffA2 y).re (coeffA1 y).re (coeffA0 y).re :=
    hδ_valid _ _ _ _ hA4_ball hA2_ball hA1_ball hA0_ball
  -- Build Qc, Qw ∈ NeusisSubfield[X] and show s₀ ∈ NeusisSubfield
  have hpow_mem := power_sum_mem_of_monic hd f hmon hdeg roots (by rwa [← hfℂ_eq])
  have build_centered_poly : ∀ (q : Fin d → ℚ),
      ∃ Q : Polynomial NeusisSubfield, Q.natDegree < d ∧
        ∀ i : Fin d, (Q.map (algebraMap NeusisSubfield ℂ)).eval (roots i) = Y (fun k => (q k : ℝ)) i := by
    intro q
    let qK : Fin d → NeusisSubfield := fun k => ⟨(q k : ℝ), neusisReal_ratCast (q k)⟩
    let P_raw : Polynomial NeusisSubfield := ∑ k : Fin d, C (qK k) * Polynomial.X ^ k.1
    have hP_eval : ∀ i : Fin d, (P_raw.map (algebraMap NeusisSubfield ℂ)).eval (roots i) =
        rawEval (fun k => (q k : ℝ)) i := by
      intro i; dsimp [P_raw, rawEval]
      rw [Polynomial.map_sum]
      change (Polynomial.evalRingHom (roots i)) (∑ k : Fin d, _) = _
      rw [map_sum (Polynomial.evalRingHom (roots i))]
      apply Finset.sum_congr rfl; intro k _
      change Polynomial.eval (roots i) (Polynomial.map (algebraMap NeusisSubfield ℂ) (C (qK k) * Polynomial.X ^ k.1)) = _
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rfl
    rcases eval_sum_mem_of_powSum_mem hpow_mem P_raw with ⟨tr, htr⟩
    let dK : NeusisSubfield := ⟨(d : ℝ), subfield_natCast_mem NeusisSubfield d⟩
    let Q : Polynomial NeusisSubfield := P_raw - C (tr / dK)
    have hP_deg : P_raw.natDegree < d :=
      natDegree_sum_lt hd_pos fun k _ => (natDegree_mul_le).trans_lt (by simp [k.2])
    have hQ_deg : Q.natDegree < d :=
      (natDegree_sub_le _ _).trans_lt (max_lt hP_deg (by simp [hd_pos]))
    refine ⟨Q, hQ_deg, ?_⟩
    intro i; dsimp [Q, Y]
    rw [Polynomial.map_sub, Polynomial.eval_sub, hP_eval, Polynomial.map_C, Polynomial.eval_C]
    have htr_eq : ((tr / dK : NeusisSubfield) : ℂ) = (1 / (d : ℂ)) * ∑ j : Fin d, rawEval (fun k => (q k : ℝ)) j := by
      have hdiv : ((tr / dK : NeusisSubfield) : ℂ) = (tr : ℂ) / (d : ℂ) := by
        change (((tr : ℝ) / (d : ℝ) : ℝ) : ℂ) = (tr : ℂ) / (d : ℂ)
        push_cast; rfl
      rw [hdiv, htr]; simp_rw [hP_eval]; ring
    change rawEval (fun k => (q k : ℝ)) i - ((tr / dK : NeusisSubfield) : ℂ) = _
    rw [htr_eq]
  rcases build_centered_poly c0 with ⟨Qc, hQc_deg, hQc_eval⟩
  rcases build_centered_poly w0 with ⟨Qw, hQw_deg, hQw_eval⟩
  rcases eval_sum_mem_of_powSum_mem hpow_mem (Qw ^ 3) with ⟨a₃, ha₃⟩
  rcases eval_sum_mem_of_powSum_mem hpow_mem (3 * Qc * Qw ^ 2) with ⟨a₂, ha₂⟩
  rcases eval_sum_mem_of_powSum_mem hpow_mem (3 * Qc ^ 2 * Qw) with ⟨a₁, ha₁⟩
  rcases eval_sum_mem_of_powSum_mem hpow_mem (Qc ^ 3) with ⟨a₀, ha₀⟩
  let H_poly : Polynomial NeusisSubfield :=
    C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2 + C a₁ * Polynomial.X + C a₀
  have hH_eval : ∀ s : ℝ, Polynomial.aeval s H_poly =
      (powSum (fun i => Y c0ℝ i + (s : ℂ) * Y w0ℝ i) 3).re := by
    intro s
    have hsumC : ((Polynomial.aeval s H_poly : ℝ) : ℂ) =
        ∑ i : Fin d, (Y c0ℝ i + (s : ℂ) * Y w0ℝ i) ^ 3 := by
      have h1 : Polynomial.aeval s H_poly = (a₃ : ℝ) * s ^ 3 + (a₂ : ℝ) * s ^ 2 + (a₁ : ℝ) * s + (a₀ : ℝ) := by
        simp [H_poly]; rfl
      rw [h1]; push_cast
      rw [ha₃, ha₂, ha₁, ha₀]
      simp only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_ofNat,
        Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_ofNat,
        hQc_eval, hQw_eval, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; dsimp [c0ℝ, w0ℝ]; ring
    have hre := congrArg Complex.re hsumC
    simpa [powSum] using hre
  have hH_ne : H_poly ≠ 0 := by
    intro h0; have := hH_eval ε; rw [h0, map_zero] at this; linarith
  have hH_deg : H_poly.natDegree ≤ 4 := by
    have h3 : (C a₃ * Polynomial.X ^ 3).natDegree ≤ 3 := (natDegree_mul_le).trans (by simp)
    have h2 : (C a₂ * Polynomial.X ^ 2).natDegree ≤ 2 := (natDegree_mul_le).trans (by simp)
    have h1 : (C a₁ * Polynomial.X).natDegree ≤ 1 := (natDegree_mul_le).trans (by simp)
    have h32 : (C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2).natDegree ≤ 3 :=
      (natDegree_add_le _ _).trans (max_le h3 (by omega))
    have h321 : (C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2 + C a₁ * Polynomial.X).natDegree ≤ 3 :=
      (natDegree_add_le _ _).trans (max_le h32 (by omega))
    have h3210 : H_poly.natDegree ≤ 3 := (natDegree_add_le _ _).trans (max_le h321 (by simp))
    omega
  have hs₀_mem : NeusisReal s₀ :=
    neusisReal_of_poly_le4 H_poly hH_ne hH_deg (by rw [hH_eval, show (fun i => Y c0ℝ i + (s₀ : ℂ) * Y w0ℝ i) = y from rfl, hy_p3]; simp)
  -- Form Q = Qc + C s₀ * Qw ∈ NeusisSubfield[X]
  let Q : Polynomial NeusisSubfield := Qc + C ⟨s₀, hs₀_mem⟩ * Qw
  have hQ_deg : Q.natDegree < d := by
    refine (natDegree_add_le _ _).trans_lt (max_lt hQc_deg ?_)
    exact (natDegree_mul_le).trans_lt (by simp [hQw_deg])
  have hQ_eval : ∀ i : Fin d, (Q.map (algebraMap NeusisSubfield ℂ)).eval (roots i) = y i := by
    intro i; dsimp [Q, y]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hQc_eval, hQw_eval]; rfl
  have hQpow_mem : ∀ m : ℕ, ∃ s : NeusisSubfield, (s : ℂ) = powSum y m := by
    intro m
    rcases eval_sum_mem_of_powSum_mem hpow_mem (Q ^ m) with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [hs]; dsimp [powSum]
    apply Finset.sum_congr rfl; intro i _
    rw [Polynomial.map_pow, Polynomial.eval_pow, hQ_eval]
  rcases hQpow_mem 2 with ⟨p2K, hp2K⟩
  rcases hQpow_mem 4 with ⟨p4K, hp4K⟩
  rcases hQpow_mem 5 with ⟨p5K, hp5K⟩
  rcases hQpow_mem 6 with ⟨p6K, hp6K⟩
  have hA4_eq : (((-p2K / 2 : NeusisSubfield) : ℝ) : ℂ) = coeffA4 y := by
    dsimp [coeffA4]; rw [← hp2K]; push_cast; rfl
  have hA2_eq : ((((p2K ^ 2 - 2 * p4K) / 8 : NeusisSubfield) : ℝ) : ℂ) = coeffA2 y := by
    dsimp [coeffA2]; rw [← hp2K, ← hp4K]; push_cast; rfl
  have hA1_eq : (((-p5K / 5 : NeusisSubfield) : ℝ) : ℂ) = coeffA1 y := by
    dsimp [coeffA1]; rw [← hp5K]; push_cast; rfl
  have hA0_mem : ∃ a0K : NeusisSubfield, ((a0K : ℝ) : ℂ) = coeffA0 y := by
    by_cases h5 : d = 5
    · exact ⟨0, by simp [coeffA0, h5]⟩
    · refine ⟨-(((p2K ^ 2 - 2 * p4K) / 8) * p2K + (-p2K / 2) * p4K + p6K) / 6, ?_⟩
      have h2K : (((2 : NeusisSubfield) : ℝ) : ℂ) = 2 := rfl
      have h6K : (((6 : NeusisSubfield) : ℝ) : ℂ) = 6 := rfl
      have h8K : (((8 : NeusisSubfield) : ℝ) : ℂ) = 8 := rfl
      dsimp [coeffA0]; rw [ite_eq_right_iff.mpr (fun h => absurd h h5), ← hA2_eq, ← hA4_eq, ← hp2K, ← hp4K, ← hp6K]
      push_cast; rw [h2K, h6K, h8K]
  rcases hA0_mem with ⟨a0K, hA0_eq⟩
  have hA4_re : (coeffA4 y).re = ((-p2K / 2 : NeusisSubfield) : ℝ) := by rw [← hA4_eq, Complex.ofReal_re]
  have hA2_re : (coeffA2 y).re = (((p2K ^ 2 - 2 * p4K) / 8 : NeusisSubfield) : ℝ) := by rw [← hA2_eq, Complex.ofReal_re]
  have hA1_re : (coeffA1 y).re = ((-p5K / 5 : NeusisSubfield) : ℝ) := by rw [← hA1_eq, Complex.ofReal_re]
  have hA0_re : (coeffA0 y).re = (a0K : ℝ) := by rw [← hA0_eq, Complex.ofReal_re]
  let y₀ : ℝ := Polynomial.aeval α Q
  have hy₀_eq : (y₀ : ℂ) = y i₀ := by
    rw [← hQ_eval i₀, hi₀]
    dsimp [y₀]
    rw [Polynomial.eval_map, Polynomial.aeval_def]
    have hcomp : (algebraMap ℝ ℂ).comp (algebraMap NeusisSubfield ℝ) = algebraMap NeusisSubfield ℂ := rfl
    rw [← hcomp]
    exact Polynomial.hom_eval₂ Q (algebraMap NeusisSubfield ℝ) (algebraMap ℝ ℂ) α
  have hy₀_sextic : y₀ ^ 6 + (coeffA4 y).re * y₀ ^ 4 + (coeffA2 y).re * y₀ ^ 2 +
      (coeffA1 y).re * y₀ + (coeffA0 y).re = 0 := by
    have hprod_y : (∏ i : Fin d, (Polynomial.X - C (y i))).eval (y i₀) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp)
    have hsext_C : (y i₀) ^ 6 + coeffA4 y * (y i₀) ^ 4 + coeffA2 y * (y i₀) ^ 2 +
        coeffA1 y * (y i₀) + coeffA0 y = 0 := by
      rcases hd with rfl | rfl
      · rw [newton_deg5_zero13 y hy_p1 hy_p3] at hprod_y
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at hprod_y
        simp only [coeffA0, ↓reduceIte]
        linear_combination y i₀ * hprod_y
      · rw [newton_deg6_zero13 y hy_p1 hy_p3] at hprod_y
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at hprod_y
        exact hprod_y
    rw [← hy₀_eq, ← hA4_eq, ← hA2_eq, ← hA1_eq, ← hA0_eq] at hsext_C
    rw [hA4_re, hA2_re, hA1_re, hA0_re]
    exact_mod_cast hsext_C
  have hy₀_mem : NeusisReal y₀ :=
    neusisReal_of_circleCircleValid
      (by rw [hA4_re]; exact (-p2K / 2 : NeusisSubfield).2)
      (by rw [hA2_re]; exact (((p2K ^ 2 - 2 * p4K) / 8 : NeusisSubfield)).2)
      (by rw [hA1_re]; exact (-p5K / 5 : NeusisSubfield).2)
      (by rw [hA0_re]; exact a0K.2)
      hvalid hy₀_sextic
  let R : Polynomial NeusisSubfield := Q - C ⟨y₀, hy₀_mem⟩
  have hR_deg : R.natDegree < f.natDegree := by
    rw [hdeg]; exact (natDegree_sub_le _ _).trans_lt (max_lt hQ_deg (by simp [hd_pos]))
  have hR_root : Polynomial.aeval α R = 0 := by
    dsimp [R, y₀]; simp only [map_sub, Polynomial.aeval_C]
    exact sub_self _
  have hR_ne : R ≠ 0 := by
    intro h0
    have hev1 : (R.map (algebraMap NeusisSubfield ℂ)).eval (roots i₁) = 0 := by
      rw [h0, Polynomial.map_zero, Polynomial.eval_zero]
    dsimp [R] at hev1
    rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_C, hQ_eval] at hev1
    have hyeq : y i₁ = y i₀ := by
      have hcast : (algebraMap NeusisSubfield ℂ) ⟨y₀, hy₀_mem⟩ = (y₀ : ℂ) := rfl
      rw [hcast] at hev1
      rw [← hy₀_eq]; linear_combination hev1
    exact hy_sep hyeq.symm
  have hnot_dvd : ¬ (f ∣ R) := fun hdvd => by
    have := Polynomial.natDegree_le_of_dvd hdvd hR_ne; omega
  rcases hirr.coprime_iff_not_dvd.mpr hnot_dvd with ⟨u, v, huv⟩
  have heval1 := congrArg (Polynomial.aeval α) huv
  simp only [map_add, map_mul, map_one, hα, hR_root, mul_zero, add_zero] at heval1
  exact zero_ne_one heval1

/-- **Universal Degree-≤6 Solvability Theorem**:
Every real root of every nonzero polynomial of degree `≤ 6` over `NeusisSubfield`
lies in `NeusisSubfield`. -/
theorem neusisReal_of_poly_le6 (P : Polynomial NeusisSubfield) (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 6) {α : ℝ} (hroot : Polynomial.aeval α P = 0) :
    NeusisReal α := by
  generalize hn : P.natDegree = n
  induction n using Nat.strongRecOn generalizing P with
  | ind n ih =>
    subst hn
    by_cases hle4 : P.natDegree ≤ 4
    · exact neusisReal_of_poly_le4 P hP hle4 hroot
    have hd56 : P.natDegree = 5 ∨ P.natDegree = 6 := by omega
    by_cases hirr : Irreducible P
    · let lc : NeusisSubfield := P.leadingCoeff
      have hlc : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
      let f : Polynomial NeusisSubfield := C lc⁻¹ * P
      have hf_mon : f.Monic := by
        dsimp [f, lc]
        rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ hlc]
      have hf_deg : f.natDegree = P.natDegree := by
        dsimp [f]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc)]
      have hf_irr : Irreducible f := by
        have hu : IsUnit (C lc⁻¹ : Polynomial NeusisSubfield) :=
          Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc))
        exact (associated_unit_mul_left P _ hu).symm.irreducible hirr
      have hf_root : Polynomial.aeval α f = 0 := by dsimp [f]; simp [hroot]
      exact False.elim (not_irreducible_deg5_or_6_with_real_root (by rwa [hf_deg]) f hf_mon rfl hf_irr hf_root)
    · have hnot_unit : ¬ IsUnit P := fun hu => by
        have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
      rw [irreducible_iff] at hirr
      push Not at hirr
      rcases hirr hnot_unit with ⟨A, B, hAB, hAu, hBu⟩
      have hA0 : A ≠ 0 := fun h => hP (by rw [hAB, h, zero_mul])
      have hB0 : B ≠ 0 := fun h => hP (by rw [hAB, h, mul_zero])
      have hA_pos : 1 ≤ A.natDegree := by
        by_contra h0; push Not at h0
        have hdeg0 : A.natDegree = 0 := by omega
        have hAeq : A = C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        have hc0 : A.coeff 0 ≠ 0 := fun h => hA0 (by rw [hAeq, h, map_zero])
        exact hAu (by rw [hAeq]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
      have hB_pos : 1 ≤ B.natDegree := by
        by_contra h0; push Not at h0
        have hdeg0 : B.natDegree = 0 := by omega
        have hBeq : B = C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        have hc0 : B.coeff 0 ≠ 0 := fun h => hB0 (by rw [hBeq, h, map_zero])
        exact hBu (by rw [hBeq]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
      have hdeg_sum : P.natDegree = A.natDegree + B.natDegree := by
        rw [hAB, Polynomial.natDegree_mul hA0 hB0]
      have hrootAB : Polynomial.aeval α A * Polynomial.aeval α B = 0 := by
        rw [← map_mul, ← hAB]; exact hroot
      rcases mul_eq_zero.mp hrootAB with hAroot | hBroot
      · exact ih A.natDegree (by omega) A hA0 (by omega) hAroot rfl
      · exact ih B.natDegree (by omega) B hB0 (by omega) hBroot rfl

end Neusis
