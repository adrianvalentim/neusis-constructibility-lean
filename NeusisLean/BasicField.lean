import NeusisLean.Defs

/-!
# Basic Compass-and-Straightedge Field Operations

We prove that:
1. A point `(x, y)` is neusis-constructible iff both `x` and `y` are neusis-constructible reals.
2. `NeusisReal` forms a `Subfield ℝ` (`NeusisSubfield`), closed under square roots of nonnegative reals.
3. Consequently, every quadratic equation over `NeusisSubfield` has its real roots in `NeusisSubfield`.
-/

namespace Neusis

lemma subfield_natCast_mem (K : Subfield ℝ) (n : ℕ) : (n : ℝ) ∈ K := by
  induction n with
  | zero => simp [K.zero_mem]
  | succ k ih =>
    push_cast
    exact K.add_mem ih K.one_mem

lemma distSq_symm (p q : Point) : distSq p q = distSq q p := by
  unfold distSq; ring

lemma neusisPoint_neg1_0 : NeusisPoint (-1, 0) := by
  apply NeusisPoint.inter_lc NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
    NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
  · unfold Collinear3; ring
  · unfold distSq; ring

lemma neusisPoint_0_sqrt3 : NeusisPoint (0, Real.sqrt 3) := by
  apply NeusisPoint.inter_cc neusisPoint_neg1_0 NeusisPoint.base1 (by norm_num)
    NeusisPoint.base1 neusisPoint_neg1_0 (by norm_num) (by norm_num)
  · unfold distSq; simp; ring
  · unfold distSq; simp; ring

lemma neusisPoint_0_neg_sqrt3 : NeusisPoint (0, -Real.sqrt 3) := by
  apply NeusisPoint.inter_cc neusisPoint_neg1_0 NeusisPoint.base1 (by norm_num)
    NeusisPoint.base1 neusisPoint_neg1_0 (by norm_num) (by norm_num)
  · unfold distSq; simp; ring
  · unfold distSq; simp; ring

lemma neusisPoint_0_1 : NeusisPoint (0, 1) := by
  have hne : ((0 : ℝ), Real.sqrt 3) ≠ ((0 : ℝ), -Real.sqrt 3) := by
    intro h
    have h2 : Real.sqrt 3 = -Real.sqrt 3 := congrArg Prod.snd h
    have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  apply NeusisPoint.inter_lc neusisPoint_0_sqrt3 neusisPoint_0_neg_sqrt3 hne
    NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
  · unfold Collinear3; ring
  · unfold distSq; ring

lemma neusisPoint_neg_y {x y : ℝ} (hp : NeusisPoint (x, y)) : NeusisPoint (x, -y) := by
  by_cases hy : y = 0
  · subst hy; simpa using hp
  · have hne0 : ((0 : ℝ), (0 : ℝ)) ≠ (x, y) := by
      intro h; exact hy (congrArg Prod.snd h).symm
    have hne1 : ((1 : ℝ), (0 : ℝ)) ≠ (x, y) := by
      intro h; exact hy (congrArg Prod.snd h).symm
    apply NeusisPoint.inter_cc NeusisPoint.base0 hp hne0 NeusisPoint.base1 hp hne1 (by norm_num)
    · unfold distSq; ring
    · unfold distSq; ring

lemma neusisPoint_neg_x {x y : ℝ} (hp : NeusisPoint (x, y)) : NeusisPoint (-x, y) := by
  by_cases hx : x = 0
  · subst hx; simpa using hp
  · have hne0 : ((0 : ℝ), (0 : ℝ)) ≠ (x, y) := by
      intro h; exact hx (congrArg Prod.fst h).symm
    have hne1 : ((0 : ℝ), (1 : ℝ)) ≠ (x, y) := by
      intro h; exact hx (congrArg Prod.fst h).symm
    apply NeusisPoint.inter_cc NeusisPoint.base0 hp hne0 neusisPoint_0_1 hp hne1 (by norm_num)
    · unfold distSq; ring
    · unfold distSq; ring

lemma neusisReal_fst {p : Point} (hp : NeusisPoint p) : NeusisReal p.1 := by
  rcases p with ⟨x, y⟩
  by_cases hy : y = 0
  · subst hy; exact hp
  · have hne : (x, y) ≠ (x, -y) := by
      intro h; have h2 : y = -y := congrArg Prod.snd h; exact hy (by linarith)
    have hnonpar : (x - x) * ((0 : ℝ) - 0) ≠ (-y - y) * (1 - 0) := by
      intro h; exact hy (by linarith)
    exact NeusisPoint.inter_ll hp (neusisPoint_neg_y hp) hne
      NeusisPoint.base0 NeusisPoint.base1 (by norm_num) hnonpar
      (by unfold Collinear3; ring) (by unfold Collinear3; ring)

lemma neusisPoint_0_y_of_pt {p : Point} (hp : NeusisPoint p) : NeusisPoint (0, p.2) := by
  rcases p with ⟨x, y⟩
  by_cases hx : x = 0
  · subst hx; exact hp
  · have hne : (x, y) ≠ (-x, y) := by
      intro h; have h2 : x = -x := congrArg Prod.fst h; exact hx (by linarith)
    have hnonpar : (-x - x) * ((1 : ℝ) - 0) ≠ (y - y) * (0 - 0) := by
      intro h; exact hx (by linarith)
    exact NeusisPoint.inter_ll hp (neusisPoint_neg_x hp) hne
      NeusisPoint.base0 neusisPoint_0_1 (by norm_num) hnonpar
      (by unfold Collinear3; ring) (by unfold Collinear3; ring)

lemma neusisPoint_0_of_real {y : ℝ} (hy : NeusisReal y) : NeusisPoint (0, y) := by
  by_cases h0 : y = 0
  · subst h0; exact NeusisPoint.base0
  · have hne : ((0 : ℝ), (0 : ℝ)) ≠ (y, 0) := by
      intro h; exact h0 (congrArg Prod.fst h).symm
    exact NeusisPoint.inter_lc NeusisPoint.base0 neusisPoint_0_1 (by norm_num)
      NeusisPoint.base0 hy hne
      (by unfold Collinear3; ring) (by unfold distSq; ring)

lemma neusisReal_of_0_y {y : ℝ} (hy : NeusisPoint (0, y)) : NeusisReal y := by
  by_cases h0 : y = 0
  · subst h0; exact NeusisPoint.base0
  · have hne : ((0 : ℝ), (0 : ℝ)) ≠ (0, y) := by
      intro h; exact h0 (congrArg Prod.snd h).symm
    exact NeusisPoint.inter_lc NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
      NeusisPoint.base0 hy hne
      (by unfold Collinear3; ring) (by unfold distSq; ring)

lemma neusisReal_snd {p : Point} (hp : NeusisPoint p) : NeusisReal p.2 :=
  neusisReal_of_0_y (neusisPoint_0_y_of_pt hp)

lemma neusisPoint_double_x {x : ℝ} (hx : NeusisReal x) : NeusisReal (2 * x) := by
  by_cases h0 : x = 0
  · subst h0; rw [mul_zero]; exact NeusisPoint.base0
  · have hne : (x, (0 : ℝ)) ≠ ((0 : ℝ), (0 : ℝ)) := by
      intro h; exact h0 (congrArg Prod.fst h)
    exact NeusisPoint.inter_lc NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
      hx NeusisPoint.base0 hne
      (by unfold Collinear3; ring) (by unfold distSq; ring)

lemma neusisPoint_double_y {y : ℝ} (hy : NeusisPoint (0, y)) : NeusisPoint (0, 2 * y) := by
  by_cases h0 : y = 0
  · subst h0; rw [mul_zero]; exact NeusisPoint.base0
  · have hne : ((0 : ℝ), y) ≠ ((0 : ℝ), (0 : ℝ)) := by
      intro h; exact h0 (congrArg Prod.snd h)
    exact NeusisPoint.inter_lc NeusisPoint.base0 neusisPoint_0_1 (by norm_num)
      hy NeusisPoint.base0 hne
      (by unfold Collinear3; ring) (by unfold distSq; ring)

lemma neusisPoint_mk {x y : ℝ} (hx : NeusisReal x) (hy : NeusisReal y) : NeusisPoint (x, y) := by
  by_cases hx0 : x = 0
  · subst hx0; exact neusisPoint_0_of_real hy
  by_cases hy0 : y = 0
  · subst hy0; exact hx
  -- Construct two points on the vertical line X = x: (x, ± √3 * x)
  have h2x : NeusisReal (2 * x) := neusisPoint_double_x hx
  have hne02x : ((0 : ℝ), (0 : ℝ)) ≠ (2 * x, (0 : ℝ)) := by
    intro h; have h2 : (0 : ℝ) = 2 * x := congrArg Prod.fst h; exact hx0 (by linarith)
  have hvx1 : NeusisPoint (x, Real.sqrt 3 * x) := by
    apply NeusisPoint.inter_cc NeusisPoint.base0 h2x hne02x h2x NeusisPoint.base0 hne02x.symm hne02x
    · unfold distSq; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · unfold distSq; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hvx2 : NeusisPoint (x, -(Real.sqrt 3 * x)) := neusisPoint_neg_y hvx1
  -- Construct two points on the horizontal line Y = y: (± √3 * y, y)
  have h0y : NeusisPoint (0, y) := neusisPoint_0_of_real hy
  have h02y : NeusisPoint (0, 2 * y) := neusisPoint_double_y h0y
  have hne02y : ((0 : ℝ), (0 : ℝ)) ≠ ((0 : ℝ), 2 * y) := by
    intro h; have h2 : (0 : ℝ) = 2 * y := congrArg Prod.snd h; exact hy0 (by linarith)
  have hhy1 : NeusisPoint (Real.sqrt 3 * y, y) := by
    apply NeusisPoint.inter_cc NeusisPoint.base0 h02y hne02y h02y NeusisPoint.base0 hne02y.symm hne02y
    · unfold distSq; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · unfold distSq; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hhy2 : NeusisPoint (-(Real.sqrt 3 * y), y) := neusisPoint_neg_x hhy1
  have hsq3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnev : (x, Real.sqrt 3 * x) ≠ (x, -(Real.sqrt 3 * x)) := by
    intro h; have h2 : Real.sqrt 3 * x = -(Real.sqrt 3 * x) := congrArg Prod.snd h
    exact (mul_ne_zero hsq3 hx0) (by linarith)
  have hneh : (Real.sqrt 3 * y, y) ≠ (-(Real.sqrt 3 * y), y) := by
    intro h; have h2 : Real.sqrt 3 * y = -(Real.sqrt 3 * y) := congrArg Prod.fst h
    exact (mul_ne_zero hsq3 hy0) (by linarith)
  have hnonpar : (x - x) * (y - y) ≠ (-(Real.sqrt 3 * x) - Real.sqrt 3 * x) * (-(Real.sqrt 3 * y) - Real.sqrt 3 * y) := by
    simp
    constructor
    · intro h; exact mul_ne_zero hsq3 hx0 (by linarith)
    · intro h; exact mul_ne_zero hsq3 hy0 (by linarith)
  exact NeusisPoint.inter_ll hvx1 hvx2 hnev hhy1 hhy2 hneh hnonpar
    (by unfold Collinear3; ring) (by unfold Collinear3; ring)

theorem neusisPoint_iff {p : Point} : NeusisPoint p ↔ NeusisReal p.1 ∧ NeusisReal p.2 :=
  ⟨fun h => ⟨neusisReal_fst h, neusisReal_snd h⟩, fun ⟨h1, h2⟩ => neusisPoint_mk h1 h2⟩

lemma neusisReal_zero : NeusisReal 0 := NeusisPoint.base0
lemma neusisReal_one : NeusisReal 1 := NeusisPoint.base1

lemma neusisReal_neg {x : ℝ} (hx : NeusisReal x) : NeusisReal (-x) :=
  neusisPoint_neg_x hx

lemma neusisReal_add {x y : ℝ} (hx : NeusisReal x) (hy : NeusisReal y) : NeusisReal (x + y) := by
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx
  · have hxy : NeusisPoint (x, y) := neusisPoint_mk hx hy
    have hne : (x, (0 : ℝ)) ≠ (x, y) := by
      intro h; exact hy0 (congrArg Prod.snd h).symm
    exact NeusisPoint.inter_lc NeusisPoint.base0 NeusisPoint.base1 (by norm_num)
      hx hxy hne
      (by unfold Collinear3; ring) (by unfold distSq; ring)

lemma neusisReal_mul {x y : ℝ} (hx : NeusisReal x) (hy : NeusisReal y) : NeusisReal (x * y) := by
  by_cases hy0 : y = 0
  · subst hy0; simpa using neusisReal_zero
  · have h1y : NeusisPoint (1, y) := neusisPoint_mk neusisReal_one hy
    have hx1 : NeusisPoint (x, 1) := neusisPoint_mk hx neusisReal_one
    have hne1 : ((0 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), y) := by
      intro h; have h2 : (0 : ℝ) = 1 := congrArg Prod.fst h; norm_num at h2
    have hne2 : (x, (0 : ℝ)) ≠ (x, (1 : ℝ)) := by
      intro h; have h2 : (0 : ℝ) = 1 := congrArg Prod.snd h; norm_num at h2
    have hnonpar : ((1 : ℝ) - 0) * ((1 : ℝ) - 0) ≠ (y - 0) * (x - x) := by norm_num
    have hpt : NeusisPoint (x, x * y) :=
      NeusisPoint.inter_ll NeusisPoint.base0 h1y hne1 hx hx1 hne2 hnonpar
        (by unfold Collinear3; ring) (by unfold Collinear3; ring)
    exact neusisReal_snd hpt

lemma neusisReal_inv {x : ℝ} (hx : NeusisReal x) : NeusisReal x⁻¹ := by
  by_cases hx0 : x = 0
  · subst hx0; simpa using neusisReal_zero
  · have hx1 : NeusisPoint (x, 1) := neusisPoint_mk hx neusisReal_one
    have h11 : NeusisPoint (1, 1) := neusisPoint_mk neusisReal_one neusisReal_one
    have hne1 : ((0 : ℝ), (0 : ℝ)) ≠ (x, (1 : ℝ)) := by
      intro h; have h2 : (0 : ℝ) = 1 := congrArg Prod.snd h; norm_num at h2
    have hne2 : ((1 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), (1 : ℝ)) := by norm_num
    have hnonpar : (x - 0) * ((1 : ℝ) - 0) ≠ ((1 : ℝ) - 0) * ((1 : ℝ) - 1) := by
      simpa using hx0
    have hpt : NeusisPoint (1, x⁻¹) :=
      NeusisPoint.inter_ll NeusisPoint.base0 hx1 hne1 NeusisPoint.base1 h11 hne2 hnonpar
        (by unfold Collinear3; field_simp [hx0]; ring) (by unfold Collinear3; ring)
    exact neusisReal_snd hpt

/-- The subfield of `ℝ` consisting of neusis-constructible real numbers. -/
def NeusisSubfield : Subfield ℝ where
  carrier := { x | NeusisReal x }
  zero_mem' := neusisReal_zero
  one_mem' := neusisReal_one
  add_mem' := fun hx hy => neusisReal_add hx hy
  neg_mem' := fun hx => neusisReal_neg hx
  mul_mem' := fun hx hy => neusisReal_mul hx hy
  inv_mem' := fun _ hx => neusisReal_inv hx

lemma mem_neusisSubfield {x : ℝ} : x ∈ NeusisSubfield ↔ NeusisReal x := Iff.rfl

/-- `NeusisReal` is closed under square roots of nonnegative real numbers. -/
lemma neusisReal_sqrt {x : ℝ} (hx : NeusisReal x) (hpos : 0 ≤ x) : NeusisReal (Real.sqrt x) := by
  by_cases h0 : x = 0
  · subst h0; simpa using neusisReal_zero
  have hxpos : 0 < x := lt_of_le_of_ne hpos (Ne.symm h0)
  have hmid : NeusisReal ((x - 1) / 2) := by
    have : ((x - 1) / 2) ∈ NeusisSubfield := by
      apply NeusisSubfield.div_mem
      · exact NeusisSubfield.sub_mem hx NeusisSubfield.one_mem
      · exact subfield_natCast_mem NeusisSubfield 2
    exact this
  have hne : (((x - 1) / 2 : ℝ), (0 : ℝ)) ≠ ((-1 : ℝ), (0 : ℝ)) := by
    intro h; have h1 : (x - 1) / 2 = -1 := congrArg Prod.fst h; linarith
  have hpt : NeusisPoint (0, Real.sqrt x) := by
    apply NeusisPoint.inter_lc NeusisPoint.base0 neusisPoint_0_1 (by norm_num)
      hmid neusisPoint_neg1_0 hne
    · unfold Collinear3; ring
    · unfold distSq; simp; nlinarith [Real.sq_sqrt hpos]
  exact neusisReal_of_0_y hpt

/-- Every real root of a quadratic polynomial over `NeusisSubfield` lies in `NeusisSubfield`. -/
lemma neusisReal_of_quadratic {a b c r : ℝ}
    (ha : NeusisReal a) (hb : NeusisReal b) (hc : NeusisReal c)
    (ha0 : a ≠ 0) (hroot : a * r ^ 2 + b * r + c = 0) :
    NeusisReal r := by
  have hsq_id : (2 * a * r + b) ^ 2 = b ^ 2 - 4 * a * c := by
    linear_combination 4 * a * hroot
  have hdisc_nonneg : 0 ≤ b ^ 2 - 4 * a * c := by
    rw [← hsq_id]; exact sq_nonneg _
  have hdisc_mem : NeusisReal (b ^ 2 - 4 * a * c) := by
    have : b ^ 2 - 4 * a * c ∈ NeusisSubfield := by
      refine NeusisSubfield.sub_mem (NeusisSubfield.pow_mem hb 2) ?_
      exact NeusisSubfield.mul_mem
        (NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 4) ha) hc
    exact this
  have hsq : (2 * a * r + b) ^ 2 = (Real.sqrt (b ^ 2 - 4 * a * c)) ^ 2 := by
    rw [Real.sq_sqrt hdisc_nonneg, hsq_id]
  have hpm := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hsqrt : NeusisReal (Real.sqrt (b ^ 2 - 4 * a * c)) := neusisReal_sqrt hdisc_mem hdisc_nonneg
  have h2a : (2 * a) ∈ NeusisSubfield :=
    NeusisSubfield.mul_mem (subfield_natCast_mem NeusisSubfield 2) ha
  rcases hpm with h1 | h2
  · have hr : r = (Real.sqrt (b ^ 2 - 4 * a * c) - b) / (2 * a) := by
      field_simp [ha0]; linarith
    rw [hr]
    exact NeusisSubfield.div_mem (NeusisSubfield.sub_mem hsqrt hb) h2a
  · have hr : r = (-Real.sqrt (b ^ 2 - 4 * a * c) - b) / (2 * a) := by
      field_simp [ha0]; linarith
    rw [hr]
    exact NeusisSubfield.div_mem (NeusisSubfield.sub_mem (NeusisSubfield.neg_mem hsqrt) hb) h2a

end Neusis
