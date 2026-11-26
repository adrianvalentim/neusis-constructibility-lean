import NeusisLean.BasicField

/-!
# Baragar's Necessity Theorem (2002)

We prove that every point `(x, y)` constructible with compass, straightedge, and point-verging
neusis lies in a real subfield `K ⊆ ℝ` reachable from `ℚ` by a finite tower of extensions of
degree at most `6` (`InDeg6Tower K`).
-/

namespace Neusis

open Polynomial

/-- Membership of a curve's defining points in a subfield `K ⊆ ℝ`. -/
def CurveIn (K : Subfield ℝ) : Curve → Prop
  | Curve.line A B _ => A.1 ∈ K ∧ A.2 ∈ K ∧ B.1 ∈ K ∧ B.2 ∈ K
  | Curve.circle C Q _ => C.1 ∈ K ∧ C.2 ∈ K ∧ Q.1 ∈ K ∧ Q.2 ∈ K

/-- Joining two subfields in `InDeg6Tower` remains in `InDeg6Tower`. -/
lemma inDeg6Tower_sup {K₁ K₂ : Subfield ℝ} (h₁ : InDeg6Tower K₁) (h₂ : InDeg6Tower K₂) :
    InDeg6Tower (K₁ ⊔ K₂) := by
  induction h₂ with
  | base =>
    simpa [sup_bot_eq] using h₁
  | @adjoin K α hK p hp hdeg hroot ih =>
    have hsup : K₁ ⊔ Subfield.closure ((K : Set ℝ) ∪ {α}) =
        Subfield.closure (((K₁ ⊔ K : Subfield ℝ) : Set ℝ) ∪ {α}) := by
      have mL : K₁ ≤ K₁ ⊔ K := le_sup_left
      have mR : K ≤ K₁ ⊔ K := le_sup_right
      apply le_antisymm
      · refine sup_le ?_ ?_
        · intro x hx
          exact Subfield.subset_closure (Or.inl (mL hx))
        · rw [Subfield.closure_le]
          rintro x (hx | rfl)
          · exact Subfield.subset_closure (Or.inl (mR hx))
          · exact Subfield.subset_closure (Or.inr rfl)
      · rw [Subfield.closure_le]
        have hK_le : K ≤ Subfield.closure ((K : Set ℝ) ∪ {α}) := by
          intro y hy; exact Subfield.subset_closure (Or.inl hy)
        have mSup : K₁ ⊔ K ≤ K₁ ⊔ Subfield.closure ((K : Set ℝ) ∪ {α}) :=
          sup_le_sup_left hK_le K₁
        have mCl : Subfield.closure ((K : Set ℝ) ∪ {α}) ≤ K₁ ⊔ Subfield.closure ((K : Set ℝ) ∪ {α}) :=
          le_sup_right
        rintro x (hx | rfl)
        · exact mSup hx
        · exact mCl (Subfield.subset_closure (Or.inr rfl))
    rw [hsup]
    let ι : K →+* (K₁ ⊔ K : Subfield ℝ) := Subfield.inclusion le_sup_right
    have hι : Function.Injective ι :=
      fun _ _ h => Subtype.ext (congrArg (Subtype.val : ↥(K₁ ⊔ K) → ℝ) h)
    refine InDeg6Tower.adjoin ih (p.map ι) ?_ ?_ ?_
    · intro h0
      exact hp (Polynomial.map_injective ι hι (by simpa using h0))
    · rw [Polynomial.natDegree_map_eq_of_injective hι]
      exact hdeg
    · have hcomp : (algebraMap (↥(K₁ ⊔ K)) ℝ).comp ι = algebraMap (↥K) ℝ := rfl
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      simpa [Polynomial.aeval_def] using hroot

/-- Adjoining a real root of a nonzero polynomial of degree `≤ 6` over `K` gives `InDeg6Tower`. -/
lemma inDeg6Tower_adjoin_poly {K : Subfield ℝ} (hK : InDeg6Tower K) {α : ℝ}
    (p : Polynomial K) (hp : p ≠ 0) (hdeg : p.natDegree ≤ 6) (hroot : Polynomial.aeval α p = 0) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧ α ∈ K' := by
  refine ⟨Subfield.closure ((K : Set ℝ) ∪ {α}), InDeg6Tower.adjoin hK p hp hdeg hroot, ?_, ?_⟩
  · intro x hx; exact Subfield.subset_closure (Or.inl hx)
  · exact Subfield.subset_closure (Or.inr rfl)

/-- Helper: `algebraMap K ℝ ⟨x, hx⟩ = x`. -/
@[simp] lemma subfield_algebraMap_coe {K : Subfield ℝ} (x : ℝ) (hx : x ∈ K) :
    algebraMap (↥K) ℝ ⟨x, hx⟩ = x := rfl

/-- Helper: degree bound for quadratic polynomial over a field `K`. -/
lemma natDegree_quad_le {K : Type*} [Field K] (a b c : K) :
    (C a * Polynomial.X ^ 2 + C b * Polynomial.X + C c).natDegree ≤ 2 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans (by simp))
    ((natDegree_mul_le).trans (by simp)))

/-- Helper: degree bound for the Baragar sextic `q₁^2 * (X^2+1) - C k * q₁ * q₂ * q₃ + C d * q₂^2 * (X^2+1)`. -/
lemma natDegree_baragar_sextic_le {K : Type*} [Field K]
    (q₁ q₂ q₃ : Polynomial K) (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hq₃ : q₃.natDegree ≤ 2)
    (k d : K) :
    (q₁ ^ 2 * (Polynomial.X ^ 2 + 1) - C k * q₁ * q₂ * q₃ +
      C d * q₂ ^ 2 * (Polynomial.X ^ 2 + 1)).natDegree ≤ 6 := by
  have hX2 : (Polynomial.X ^ 2 + (1 : Polynomial K)).natDegree ≤ 2 :=
    (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have ht1 : (q₁ ^ 2 * (Polynomial.X ^ 2 + 1)).natDegree ≤ 6 := by
    have h1 : (q₁ ^ 2).natDegree ≤ 4 := (natDegree_pow_le).trans (by omega)
    exact (natDegree_mul_le).trans (by omega)
  have ht2 : (C k * q₁ * q₂ * q₃).natDegree ≤ 6 := by
    have h1 : (C k * q₁).natDegree ≤ 2 := (natDegree_mul_le).trans (by simp; omega)
    have h2 : (C k * q₁ * q₂).natDegree ≤ 4 := (natDegree_mul_le).trans (by omega)
    exact (natDegree_mul_le).trans (by omega)
  have ht3 : (C d * q₂ ^ 2 * (Polynomial.X ^ 2 + 1)).natDegree ≤ 6 := by
    have h2 : (q₂ ^ 2).natDegree ≤ 4 := (natDegree_pow_le).trans (by omega)
    have h1 : (C d * q₂ ^ 2).natDegree ≤ 4 := (natDegree_mul_le).trans (by simp; omega)
    exact (natDegree_mul_le).trans (by omega)
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ht1 ht2)) ht3)

/-- Adjoining a real root of a nontrivial quadratic `a * x^2 + b * x + c = 0` over `K`. -/
lemma inDeg6Tower_of_quad {K : Subfield ℝ} (hK : InDeg6Tower K) {a b c α : ℝ}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (hne : a ≠ 0 ∨ b ≠ 0)
    (hroot : a * α ^ 2 + b * α + c = 0) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧ α ∈ K' := by
  let p : Polynomial K :=
    C ⟨a, ha⟩ * Polynomial.X ^ 2 + C ⟨b, hb⟩ * Polynomial.X + C ⟨c, hc⟩
  have hp_ne : p ≠ 0 := by
    intro h0
    rcases hne with ha0 | hb0
    · have h2 := congrArg (fun q => q.coeff 2) h0
      simp [p] at h2
      exact ha0 (congrArg Subtype.val h2)
    · have h1 := congrArg (fun q => q.coeff 1) h0
      simp [p] at h1
      exact hb0 (congrArg Subtype.val h1)
  have hdeg : p.natDegree ≤ 6 := (natDegree_quad_le _ _ _).trans (by omega)
  have hr : Polynomial.aeval α p = 0 := by
    simp [p, hroot]
  exact inDeg6Tower_adjoin_poly hK p hp_ne hdeg hr

/-- Every polynomial of degree `≤ 4` with coefficients in `K` evaluating to `0` at `α`
and nonzero at some `t₀ : ℝ` allows adjoining `α` to `K` in `InDeg6Tower`. -/
lemma inDeg6Tower_of_poly4 {K : Subfield ℝ} (hK : InDeg6Tower K) {α : ℝ}
    (c₀ c₁ c₂ c₃ c₄ : ℝ)
    (h₀ : c₀ ∈ K) (h₁ : c₁ ∈ K) (h₂ : c₂ ∈ K) (h₃ : c₃ ∈ K) (h₄ : c₄ ∈ K)
    (hnontriv : ∃ t₀ : ℝ, c₄ * t₀ ^ 4 + c₃ * t₀ ^ 3 + c₂ * t₀ ^ 2 + c₁ * t₀ + c₀ ≠ 0)
    (hroot : c₄ * α ^ 4 + c₃ * α ^ 3 + c₂ * α ^ 2 + c₁ * α + c₀ = 0) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧ α ∈ K' := by
  let a₄ : K := ⟨c₄, h₄⟩
  let a₃ : K := ⟨c₃, h₃⟩
  let a₂ : K := ⟨c₂, h₂⟩
  let a₁ : K := ⟨c₁, h₁⟩
  let a₀ : K := ⟨c₀, h₀⟩
  let p : Polynomial K :=
    C a₄ * Polynomial.X ^ 4 + C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2 +
    C a₁ * Polynomial.X + C a₀
  have heval : ∀ t : ℝ, Polynomial.aeval t p =
      c₄ * t ^ 4 + c₃ * t ^ 3 + c₂ * t ^ 2 + c₁ * t + c₀ := by
    intro t; simp [p, a₄, a₃, a₂, a₁, a₀]
  have hp_ne : p ≠ 0 := by
    intro h0
    rcases hnontriv with ⟨t₀, ht₀⟩
    have := heval t₀
    rw [h0, map_zero] at this
    exact ht₀ this.symm
  have hdeg : p.natDegree ≤ 6 := by
    have h4 : (C a₄ * Polynomial.X ^ 4).natDegree ≤ 4 := (natDegree_mul_le).trans (by simp)
    have h3 : (C a₃ * Polynomial.X ^ 3).natDegree ≤ 3 := (natDegree_mul_le).trans (by simp)
    have h2 : (C a₂ * Polynomial.X ^ 2).natDegree ≤ 2 := (natDegree_mul_le).trans (by simp)
    have h1 : (C a₁ * Polynomial.X).natDegree ≤ 1 := (natDegree_mul_le).trans (by simp)
    have h43 : (C a₄ * Polynomial.X ^ 4 + C a₃ * Polynomial.X ^ 3).natDegree ≤ 4 :=
      (natDegree_add_le _ _).trans (max_le h4 (by omega))
    have h432 : (C a₄ * Polynomial.X ^ 4 + C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2).natDegree ≤ 4 :=
      (natDegree_add_le _ _).trans (max_le h43 (by omega))
    have h4321 : (C a₄ * Polynomial.X ^ 4 + C a₃ * Polynomial.X ^ 3 + C a₂ * Polynomial.X ^ 2 +
        C a₁ * Polynomial.X).natDegree ≤ 4 :=
      (natDegree_add_le _ _).trans (max_le h432 (by omega))
    have h43210 : p.natDegree ≤ 4 :=
      (natDegree_add_le _ _).trans (max_le h4321 (by simp))
    omega
  exact inDeg6Tower_adjoin_poly hK p hp_ne hdeg (by rw [heval]; exact hroot)

/-- Line-circle intersection lies in a degree-≤2 extension of `K`. -/
lemma inter_lc_inDeg6Tower {K : Subfield ℝ} (hK : InDeg6Tower K)
    {A B C Q X : Point}
    (hA : A.1 ∈ K ∧ A.2 ∈ K) (hB : B.1 ∈ K ∧ B.2 ∈ K) (hne : A ≠ B)
    (hC : C.1 ∈ K ∧ C.2 ∈ K) (hQ : Q.1 ∈ K ∧ Q.2 ∈ K)
    (h₁ : Collinear3 A B X) (h₂ : distSq C X = distSq C Q) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧ X.1 ∈ K' ∧ X.2 ∈ K' := by
  have hdxdy : B.1 - A.1 ≠ 0 ∨ B.2 - A.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    exact Prod.ext (by linarith) (by linarith)
  have hr2 : distSq C Q ∈ K := by
    unfold distSq
    exact K.add_mem (K.pow_mem (K.sub_mem hC.1 hQ.1) 2) (K.pow_mem (K.sub_mem hC.2 hQ.2) 2)
  rcases hdxdy with hdx | hdy
  · let m : ℝ := (B.2 - A.2) / (B.1 - A.1)
    let b₀ : ℝ := A.2 - m * A.1
    have hmK : m ∈ K := K.div_mem (K.sub_mem hB.2 hA.2) (K.sub_mem hB.1 hA.1)
    have hbK : b₀ ∈ K := K.sub_mem hA.2 (K.mul_mem hmK hA.1)
    have hX2 : X.2 = m * X.1 + b₀ := by
      unfold Collinear3 at h₁
      dsimp [m, b₀]
      field_simp [hdx]
      linarith
    have hquad : (1 + m ^ 2) * X.1 ^ 2 + (2 * (m * (b₀ - C.2) - C.1)) * X.1 +
        (C.1 ^ 2 + (b₀ - C.2) ^ 2 - distSq C Q) = 0 := by
      unfold distSq at h₂ ⊢
      rw [hX2] at h₂
      linarith
    have haK : 1 + m ^ 2 ∈ K := K.add_mem K.one_mem (K.pow_mem hmK 2)
    have hlinK : 2 * (m * (b₀ - C.2) - C.1) ∈ K :=
      K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem (K.mul_mem hmK (K.sub_mem hbK hC.2)) hC.1)
    have hcK : C.1 ^ 2 + (b₀ - C.2) ^ 2 - distSq C Q ∈ K :=
      K.sub_mem (K.add_mem (K.pow_mem hC.1 2) (K.pow_mem (K.sub_mem hbK hC.2) 2)) hr2
    have ha0 : 1 + m ^ 2 ≠ 0 := by positivity
    rcases inDeg6Tower_of_quad hK haK hlinK hcK (Or.inl ha0) hquad with ⟨K', hK', hle, hX1⟩
    refine ⟨K', hK', hle, hX1, ?_⟩
    rw [hX2]
    exact K'.add_mem (K'.mul_mem (hle hmK) hX1) (hle hbK)
  · let m : ℝ := (B.1 - A.1) / (B.2 - A.2)
    let b₀ : ℝ := A.1 - m * A.2
    have hmK : m ∈ K := K.div_mem (K.sub_mem hB.1 hA.1) (K.sub_mem hB.2 hA.2)
    have hbK : b₀ ∈ K := K.sub_mem hA.1 (K.mul_mem hmK hA.2)
    have hX1 : X.1 = m * X.2 + b₀ := by
      unfold Collinear3 at h₁
      dsimp [m, b₀]
      field_simp [hdy]
      linarith
    have hquad : (1 + m ^ 2) * X.2 ^ 2 + (2 * (m * (b₀ - C.1) - C.2)) * X.2 +
        (C.2 ^ 2 + (b₀ - C.1) ^ 2 - distSq C Q) = 0 := by
      unfold distSq at h₂ ⊢
      rw [hX1] at h₂
      linarith
    have haK : 1 + m ^ 2 ∈ K := K.add_mem K.one_mem (K.pow_mem hmK 2)
    have hlinK : 2 * (m * (b₀ - C.1) - C.2) ∈ K :=
      K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem (K.mul_mem hmK (K.sub_mem hbK hC.1)) hC.2)
    have hcK : C.2 ^ 2 + (b₀ - C.1) ^ 2 - distSq C Q ∈ K :=
      K.sub_mem (K.add_mem (K.pow_mem hC.2 2) (K.pow_mem (K.sub_mem hbK hC.1) 2)) hr2
    have ha0 : 1 + m ^ 2 ≠ 0 := by positivity
    rcases inDeg6Tower_of_quad hK haK hlinK hcK (Or.inl ha0) hquad with ⟨K', hK', hle, hX2⟩
    refine ⟨K', hK', hle, ?_, hX2⟩
    rw [hX1]
    exact K'.add_mem (K'.mul_mem (hle hmK) hX2) (hle hbK)

/-- Circle-circle intersection with distinct centers lies in a degree-≤2 extension of `K`. -/
lemma inter_cc_inDeg6Tower {K : Subfield ℝ} (hK : InDeg6Tower K)
    {C₁ Q₁ C₂ Q₂ X : Point}
    (hC₁ : C₁.1 ∈ K ∧ C₁.2 ∈ K) (hQ₁ : Q₁.1 ∈ K ∧ Q₁.2 ∈ K)
    (hC₂ : C₂.1 ∈ K ∧ C₂.2 ∈ K) (hQ₂ : Q₂.1 ∈ K ∧ Q₂.2 ∈ K)
    (hdiff : C₁ ≠ C₂)
    (h₁ : distSq C₁ X = distSq C₁ Q₁) (h₂ : distSq C₂ X = distSq C₂ Q₂) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧ X.1 ∈ K' ∧ X.2 ∈ K' := by
  have hrad : 2 * (C₂.1 - C₁.1) * X.1 + 2 * (C₂.2 - C₁.2) * X.2 =
      (C₂.1 ^ 2 + C₂.2 ^ 2 - distSq C₂ Q₂) - (C₁.1 ^ 2 + C₁.2 ^ 2 - distSq C₁ Q₁) := by
    unfold distSq at h₁ h₂ ⊢; linarith
  have hne : C₂.1 - C₁.1 ≠ 0 ∨ C₂.2 - C₁.2 ≠ 0 := by
    by_contra h; push Not at h; apply hdiff; exact Prod.ext (by linarith) (by linarith)
  have hr1 : distSq C₁ Q₁ ∈ K := by
    unfold distSq
    exact K.add_mem (K.pow_mem (K.sub_mem hC₁.1 hQ₁.1) 2) (K.pow_mem (K.sub_mem hC₁.2 hQ₁.2) 2)
  have hr2 : distSq C₂ Q₂ ∈ K := by
    unfold distSq
    exact K.add_mem (K.pow_mem (K.sub_mem hC₂.1 hQ₂.1) 2) (K.pow_mem (K.sub_mem hC₂.2 hQ₂.2) 2)
  let rhs : ℝ := (C₂.1 ^ 2 + C₂.2 ^ 2 - distSq C₂ Q₂) - (C₁.1 ^ 2 + C₁.2 ^ 2 - distSq C₁ Q₁)
  have hrhsK : rhs ∈ K := K.sub_mem
    (K.sub_mem (K.add_mem (K.pow_mem hC₂.1 2) (K.pow_mem hC₂.2 2)) hr2)
    (K.sub_mem (K.add_mem (K.pow_mem hC₁.1 2) (K.pow_mem hC₁.2 2)) hr1)
  rcases hne with hdx | hdy
  · let m : ℝ := -(C₂.2 - C₁.2) / (C₂.1 - C₁.1)
    let b₀ : ℝ := rhs / (2 * (C₂.1 - C₁.1))
    have hmK : m ∈ K := K.div_mem (K.neg_mem (K.sub_mem hC₂.2 hC₁.2)) (K.sub_mem hC₂.1 hC₁.1)
    have hbK : b₀ ∈ K := K.div_mem hrhsK (K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem hC₂.1 hC₁.1))
    have hX1 : X.1 = m * X.2 + b₀ := by
      dsimp [m, b₀, rhs] at *; field_simp [hdx]; linarith
    have hquad : (1 + m ^ 2) * X.2 ^ 2 + (2 * (m * (b₀ - C₁.1) - C₁.2)) * X.2 +
        (C₁.2 ^ 2 + (b₀ - C₁.1) ^ 2 - distSq C₁ Q₁) = 0 := by
      unfold distSq at h₁ ⊢; rw [hX1] at h₁; linarith
    have haK : 1 + m ^ 2 ∈ K := K.add_mem K.one_mem (K.pow_mem hmK 2)
    have hlinK : 2 * (m * (b₀ - C₁.1) - C₁.2) ∈ K :=
      K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem (K.mul_mem hmK (K.sub_mem hbK hC₁.1)) hC₁.2)
    have hcK : C₁.2 ^ 2 + (b₀ - C₁.1) ^ 2 - distSq C₁ Q₁ ∈ K :=
      K.sub_mem (K.add_mem (K.pow_mem hC₁.2 2) (K.pow_mem (K.sub_mem hbK hC₁.1) 2)) hr1
    rcases inDeg6Tower_of_quad hK haK hlinK hcK (Or.inl (by positivity)) hquad with ⟨K', hK', hle, hX2⟩
    exact ⟨K', hK', hle, by rw [hX1]; exact K'.add_mem (K'.mul_mem (hle hmK) hX2) (hle hbK), hX2⟩
  · let m : ℝ := -(C₂.1 - C₁.1) / (C₂.2 - C₁.2)
    let b₀ : ℝ := rhs / (2 * (C₂.2 - C₁.2))
    have hmK : m ∈ K := K.div_mem (K.neg_mem (K.sub_mem hC₂.1 hC₁.1)) (K.sub_mem hC₂.2 hC₁.2)
    have hbK : b₀ ∈ K := K.div_mem hrhsK (K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem hC₂.2 hC₁.2))
    have hX2 : X.2 = m * X.1 + b₀ := by
      dsimp [m, b₀, rhs] at *; field_simp [hdy]; linarith
    have hquad : (1 + m ^ 2) * X.1 ^ 2 + (2 * (m * (b₀ - C₁.2) - C₁.1)) * X.1 +
        (C₁.1 ^ 2 + (b₀ - C₁.2) ^ 2 - distSq C₁ Q₁) = 0 := by
      unfold distSq at h₁ ⊢; rw [hX2] at h₁; linarith
    have haK : 1 + m ^ 2 ∈ K := K.add_mem K.one_mem (K.pow_mem hmK 2)
    have hlinK : 2 * (m * (b₀ - C₁.2) - C₁.1) ∈ K :=
      K.mul_mem (subfield_natCast_mem K 2) (K.sub_mem (K.mul_mem hmK (K.sub_mem hbK hC₁.2)) hC₁.1)
    have hcK : C₁.1 ^ 2 + (b₀ - C₁.2) ^ 2 - distSq C₁ Q₁ ∈ K :=
      K.sub_mem (K.add_mem (K.pow_mem hC₁.1 2) (K.pow_mem (K.sub_mem hbK hC₁.2) 2)) hr1
    rcases inDeg6Tower_of_quad hK haK hlinK hcK (Or.inl (by positivity)) hquad with ⟨K', hK', hle, hX1⟩
    exact ⟨K', hK', hle, hX1, by rw [hX2]; exact K'.add_mem (K'.mul_mem (hle hmK) hX1) (hle hbK)⟩

/-- If every `t` with `D(t) ≠ 0` and `f(t) = 0` produces a distinct element of a finite set `S`,
then `f` must be nonzero at some `t₀`. -/
lemma exists_ne_zero_of_finite_solutions {S : Set (Point × Point)} (hfin : S.Finite)
    (D f : ℝ → ℝ)
    (hD_finite : { t : ℝ | D t = 0 }.Finite)
    (hmap : ∀ t : ℝ, D t ≠ 0 → f t = 0 →
      ∃ xy ∈ S, (xy.2.1 - xy.1.1) = (1 - t ^ 2) / (1 + t ^ 2) ∧
                (xy.2.2 - xy.1.2) = (2 * t) / (1 + t ^ 2)) :
    ∃ t₀ : ℝ, f t₀ ≠ 0 := by
  by_contra h
  push Not at h
  have hinf : ({ t : ℝ | D t ≠ 0 }).Infinite := by
    intro hfin_nz
    have heq : (Set.univ : Set ℝ) = { t : ℝ | D t = 0 } ∪ { t : ℝ | D t ≠ 0 } := by
      ext t; simp [em]
    exact Set.infinite_univ (by rw [heq]; exact hD_finite.union hfin_nz)
  have hex : ∀ t : { t : ℝ // D t ≠ 0 }, ∃ xy ∈ S,
      (xy.2.1 - xy.1.1) = (1 - t.1 ^ 2) / (1 + t.1 ^ 2) ∧
      (xy.2.2 - xy.1.2) = (2 * t.1) / (1 + t.1 ^ 2) :=
    fun t => hmap t.1 t.2 (h t.1)
  choose g hgS hgu1 hgu2 using hex
  let g' : { t : ℝ // D t ≠ 0 } → S := fun t => ⟨g t, hgS t⟩
  have hinj : Function.Injective g' := by
    intro t₁ t₂ heq'
    have heq : g t₁ = g t₂ := congrArg Subtype.val heq'
    have hu1 : (1 - t₁.1 ^ 2) / (1 + t₁.1 ^ 2) = (1 - t₂.1 ^ 2) / (1 + t₂.1 ^ 2) := by
      rw [← hgu1 t₁, ← hgu1 t₂, heq]
    have hu2 : (2 * t₁.1) / (1 + t₁.1 ^ 2) = (2 * t₂.1) / (1 + t₂.1 ^ 2) := by
      rw [← hgu2 t₁, ← hgu2 t₂, heq]
    have hpos1 : (0 : ℝ) < 1 + t₁.1 ^ 2 := by positivity
    have hpos2 : (0 : ℝ) < 1 + t₂.1 ^ 2 := by positivity
    have h1 : (1 - t₁.1 ^ 2) * (1 + t₂.1 ^ 2) = (1 - t₂.1 ^ 2) * (1 + t₁.1 ^ 2) := by
      rwa [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos2)] at hu1
    have h2 : (2 * t₁.1) * (1 + t₂.1 ^ 2) = (2 * t₂.1) * (1 + t₁.1 ^ 2) := by
      rwa [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos2)] at hu2
    have hsq : t₁.1 ^ 2 = t₂.1 ^ 2 := by linarith
    have hdiff : (t₁.1 - t₂.1) * (1 + t₁.1 ^ 2) = 0 := by
      linear_combination (1 / 2 : ℝ) * h2 + t₁.1 * hsq
    apply Subtype.ext
    rcases mul_eq_zero.mp hdiff with hsub | h0
    · linarith
    · linarith
  have : Finite S := hfin.to_subtype
  exact hinf (Set.finite_coe_iff.mp (Finite.of_injective g' hinj))

/-- A nonzero quadratic `a * t^2 + b * t + c` has finitely many real roots. -/
lemma quad_zero_set_finite (a b c : ℝ) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    { t : ℝ | a * t ^ 2 + b * t + c = 0 }.Finite := by
  let p : Polynomial ℝ := C a * Polynomial.X ^ 2 + C b * Polynomial.X + C c
  have hp : p ≠ 0 := by
    intro h0
    rcases hne with ha | hb | hc
    · have := congrArg (fun q => q.coeff 2) h0; simp [p] at this; exact ha this
    · have := congrArg (fun q => q.coeff 1) h0; simp [p] at this; exact hb this
    · have := congrArg (fun q => q.coeff 0) h0; simp [p] at this; exact hc this
  have hsub : { t : ℝ | a * t ^ 2 + b * t + c = 0 } ⊆ (p.roots.toFinset : Set ℝ) := by
    intro t ht
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    simpa [p] using ht
  exact (p.roots.toFinset.finite_toSet).subset hsub

/-- Once direction `(u₁, u₂)` lies in `K₁` (with `u₁^2 + u₂^2 = 1`), the radial coordinate `ρ`
(and hence `X`, `Y`) lies in a degree-≤2 extension of `K₁`. -/
private lemma neusis_origin_from_dir {K K₁ : Subfield ℝ} (hK₁ : InDeg6Tower K₁) (hle₁ : K ≤ K₁)
    {P₁ P₂ : Point} {γ₁ γ₂ : Curve}
    (hγ₁ : CurveIn K γ₁) (hγ₂ : CurveIn K γ₂)
    (hfin : (NeusisSolutions (0, 0) γ₁ γ₂).Finite)
    (hXγ₁ : OnCurve γ₁ P₁) (hYγ₂ : OnCurve γ₂ P₂)
    {u₁ u₂ ρ : ℝ}
    (hu_norm : u₁ ^ 2 + u₂ ^ 2 = 1)
    (hX1 : P₁.1 = ρ * u₁) (hX2 : P₁.2 = ρ * u₂)
    (hY1 : P₂.1 = (ρ + 1) * u₁) (hY2 : P₂.2 = (ρ + 1) * u₂)
    (hu1K : u₁ ∈ K₁) (hu2K : u₂ ∈ K₁) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧
      P₁.1 ∈ K' ∧ P₁.2 ∈ K' ∧ P₂.1 ∈ K' ∧ P₂.2 ∈ K' := by
  have finish : ∀ (K' : Subfield ℝ), InDeg6Tower K' → K₁ ≤ K' → ρ ∈ K' →
      ∃ K'' : Subfield ℝ, InDeg6Tower K'' ∧ K ≤ K'' ∧
        P₁.1 ∈ K'' ∧ P₁.2 ∈ K'' ∧ P₂.1 ∈ K'' ∧ P₂.2 ∈ K'' := by
    intro K' hK' hle' hρK
    refine ⟨K', hK', hle₁.trans hle', ?_, ?_, ?_, ?_⟩
    · rw [hX1]; exact K'.mul_mem hρK (hle' hu1K)
    · rw [hX2]; exact K'.mul_mem hρK (hle' hu2K)
    · rw [hY1]; exact K'.mul_mem (K'.add_mem hρK K'.one_mem) (hle' hu1K)
    · rw [hY2]; exact K'.mul_mem (K'.add_mem hρK K'.one_mem) (hle' hu2K)
  have hnot_all : ¬ (∀ r : ℝ, OnCurve γ₁ (r * u₁, r * u₂) ∧ OnCurve γ₂ ((r + 1) * u₁, (r + 1) * u₂)) := by
    intro hall
    let f : ℝ → NeusisSolutions (0, 0) γ₁ γ₂ := fun r =>
      ⟨((r * u₁, r * u₂), ((r + 1) * u₁, (r + 1) * u₂)),
        ⟨(hall r).1, (hall r).2, by unfold Collinear3; ring,
         by unfold distSq; dsimp only; linear_combination hu_norm⟩⟩
    have hinj : Function.Injective f := by
      intro r₁ r₂ heq
      have h1 : r₁ * u₁ = r₂ * u₁ := congrArg (fun p => p.1.1.1) heq
      have h2 : r₁ * u₂ = r₂ * u₂ := congrArg (fun p => p.1.1.2) heq
      linear_combination u₁ * h1 + u₂ * h2 - (r₁ - r₂) * hu_norm
    have : Finite (NeusisSolutions (0, 0) γ₁ γ₂) := hfin.to_subtype
    have hfinR : Finite ℝ := Finite.of_injective f hinj
    exact Set.infinite_univ (@Set.finite_univ ℝ hfinR)
  have curve_eq : ∀ (γ : Curve), CurveIn K γ →
      ∃ (a b c : ℝ), a ∈ K₁ ∧ b ∈ K₁ ∧ c ∈ K₁ ∧
        ∀ r : ℝ, OnCurve γ (r * u₁, r * u₂) ↔ a * r ^ 2 + b * r + c = 0 := by
    intro γ hγ
    cases γ with
    | line A B hne =>
      rcases hγ with ⟨hA1, hA2, hB1, hB2⟩
      refine ⟨0, (B.1 - A.1) * u₂ - (B.2 - A.2) * u₁,
        -(B.1 - A.1) * A.2 + (B.2 - A.2) * A.1, K₁.zero_mem, ?_, ?_, ?_⟩
      · exact K₁.sub_mem (K₁.mul_mem (K₁.sub_mem (hle₁ hB1) (hle₁ hA1)) hu2K)
          (K₁.mul_mem (K₁.sub_mem (hle₁ hB2) (hle₁ hA2)) hu1K)
      · exact K₁.add_mem (K₁.mul_mem (K₁.neg_mem (K₁.sub_mem (hle₁ hB1) (hle₁ hA1))) (hle₁ hA2))
          (K₁.mul_mem (K₁.sub_mem (hle₁ hB2) (hle₁ hA2)) (hle₁ hA1))
      · intro r; unfold OnCurve Collinear3; constructor <;> intro h <;> linarith
    | circle C Q hne =>
      rcases hγ with ⟨hC1, hC2, hQ1, hQ2⟩
      have hdK : C.1 ^ 2 + C.2 ^ 2 - distSq C Q ∈ K₁ := by
        unfold distSq
        exact K₁.sub_mem (K₁.add_mem (K₁.pow_mem (hle₁ hC1) 2) (K₁.pow_mem (hle₁ hC2) 2))
          (K₁.add_mem (K₁.pow_mem (K₁.sub_mem (hle₁ hC1) (hle₁ hQ1)) 2)
            (K₁.pow_mem (K₁.sub_mem (hle₁ hC2) (hle₁ hQ2)) 2))
      refine ⟨1, -2 * (C.1 * u₁ + C.2 * u₂), C.1 ^ 2 + C.2 ^ 2 - distSq C Q, K₁.one_mem, ?_, hdK, ?_⟩
      · exact K₁.mul_mem (K₁.neg_mem (subfield_natCast_mem K₁ 2))
          (K₁.add_mem (K₁.mul_mem (hle₁ hC1) hu1K) (K₁.mul_mem (hle₁ hC2) hu2K))
      · intro r
        unfold OnCurve distSq
        constructor <;> intro h
        · linear_combination h - r ^ 2 * hu_norm
        · linear_combination h + r ^ 2 * hu_norm
  rcases curve_eq γ₁ hγ₁ with ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hiff₁⟩
  rcases curve_eq γ₂ hγ₂ with ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hiff₂⟩
  have hXeq : P₁ = (ρ * u₁, ρ * u₂) := Prod.ext hX1 hX2
  have hYeq : P₂ = ((ρ + 1) * u₁, (ρ + 1) * u₂) := Prod.ext hY1 hY2
  have hr₁ : a₁ * ρ ^ 2 + b₁ * ρ + c₁ = 0 := (hiff₁ ρ).mp (by rwa [← hXeq])
  have hr₂ : a₂ * (ρ + 1) ^ 2 + b₂ * (ρ + 1) + c₂ = 0 := (hiff₂ (ρ + 1)).mp (by rwa [← hYeq])
  by_cases h1 : a₁ ≠ 0 ∨ b₁ ≠ 0
  · rcases inDeg6Tower_of_quad hK₁ ha₁ hb₁ hc₁ h1 hr₁ with ⟨K', hK', hle', hρK⟩
    exact finish K' hK' hle' hρK
  · push Not at h1
    have hc1_0 : c₁ = 0 := by nlinarith [h1.1, h1.2, hr₁]
    by_cases h2 : a₂ ≠ 0 ∨ b₂ ≠ 0
    · have hr₂' : a₂ * ρ ^ 2 + (2 * a₂ + b₂) * ρ + (a₂ + b₂ + c₂) = 0 := by linarith
      have h2' : a₂ ≠ 0 ∨ 2 * a₂ + b₂ ≠ 0 := by
        rcases h2 with ha2 | hb2
        · exact Or.inl ha2
        · by_cases ha2 : a₂ = 0
          · exact Or.inr (fun h => hb2 (by linarith))
          · exact Or.inl ha2
      rcases inDeg6Tower_of_quad hK₁ ha₂
          (K₁.add_mem (K₁.mul_mem (subfield_natCast_mem K₁ 2) ha₂) hb₂)
          (K₁.add_mem (K₁.add_mem ha₂ hb₂) hc₂) h2' hr₂' with ⟨K', hK', hle', hρK⟩
      exact finish K' hK' hle' hρK
    · push Not at h2
      have hc2_0 : c₂ = 0 := by nlinarith [h2.1, h2.2, hr₂]
      exfalso; apply hnot_all; intro r
      rw [hiff₁ r, hiff₂ (r + 1)]
      exact ⟨by simp [h1.1, h1.2, hc1_0], by simp [h2.1, h2.2, hc2_0]⟩

/-- Case 1 (Line-Line) of Baragar's necessity theorem: `t` lies in a degree-≤4 extension of `K`. -/
private lemma neusis_origin_ll_t {K : Subfield ℝ} (hK : InDeg6Tower K)
    {A₁ B₁ A₂ B₂ P₁ P₂ : Point} {hne₁ : A₁ ≠ B₁} {hne₂ : A₂ ≠ B₂}
    (hγ₁ : CurveIn K (Curve.line A₁ B₁ hne₁)) (hγ₂ : CurveIn K (Curve.line A₂ B₂ hne₂))
    (hfin : (NeusisSolutions (0, 0) (Curve.line A₁ B₁ hne₁) (Curve.line A₂ B₂ hne₂)).Finite)
    (hXγ₁ : OnCurve (Curve.line A₁ B₁ hne₁) P₁) (hYγ₂ : OnCurve (Curve.line A₂ B₂ hne₂) P₂)
    {t ρ : ℝ}
    (hX1 : P₁.1 = ρ * ((1 - t ^ 2) / (1 + t ^ 2))) (hX2 : P₁.2 = ρ * (2 * t / (1 + t ^ 2)))
    (hY1 : P₂.1 = (ρ + 1) * ((1 - t ^ 2) / (1 + t ^ 2))) (hY2 : P₂.2 = (ρ + 1) * (2 * t / (1 + t ^ 2))) :
    ∃ K₁ : Subfield ℝ, InDeg6Tower K₁ ∧ K ≤ K₁ ∧ t ∈ K₁ := by
  have ht_den : 1 + t ^ 2 ≠ 0 := by positivity
  rcases hγ₁ with ⟨hA1x, hA1y, hB1x, hB1y⟩
  let a₁ : ℝ := B₁.2 - A₁.2
  let b₁ : ℝ := -(B₁.1 - A₁.1)
  let c₁ : ℝ := a₁ * A₁.1 + b₁ * A₁.2
  have ha₁K : a₁ ∈ K := K.sub_mem hB1y hA1y
  have hb₁K : b₁ ∈ K := K.neg_mem (K.sub_mem hB1x hA1x)
  have hc₁K : c₁ ∈ K := K.add_mem (K.mul_mem ha₁K hA1x) (K.mul_mem hb₁K hA1y)
  have hab₁ : a₁ ≠ 0 ∨ b₁ ≠ 0 := by
    by_contra h; push Not at h; apply hne₁
    exact Prod.ext (by dsimp [b₁] at h; linarith) (by dsimp [a₁] at h; linarith)
  have hL₁_iff : ∀ p : Point, OnCurve (Curve.line A₁ B₁ hne₁) p ↔ a₁ * p.1 + b₁ * p.2 = c₁ := by
    intro p; unfold OnCurve Collinear3; dsimp [a₁, b₁, c₁]; constructor <;> intro h <;> linarith
  let L₁ : ℝ → ℝ := fun τ => (-a₁) * τ ^ 2 + (2 * b₁) * τ + a₁
  have hL₁_nz : (-a₁) ≠ 0 ∨ (2 * b₁) ≠ 0 ∨ a₁ ≠ 0 := by
    rcases hab₁ with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr (Or.inl (mul_ne_zero two_ne_zero h))
  have hL₁_t : ρ * L₁ t = c₁ * (1 + t ^ 2) := by
    have h1 := (hL₁_iff P₁).mp hXγ₁
    rw [hX1, hX2] at h1
    dsimp [L₁]; field_simp [ht_den] at h1; linarith
  by_cases hL1_0 : L₁ t = 0
  · have hne2 : (-a₁) ≠ 0 ∨ (2 * b₁) ≠ 0 := by
      rcases hab₁ with h | h
      · exact Or.inl (neg_ne_zero.mpr h)
      · exact Or.inr (mul_ne_zero two_ne_zero h)
    exact inDeg6Tower_of_quad hK (K.neg_mem ha₁K) (K.mul_mem (subfield_natCast_mem K 2) hb₁K) ha₁K
        hne2 hL1_0
  · rcases hγ₂ with ⟨hA2x, hA2y, hB2x, hB2y⟩
    let a₂ : ℝ := B₂.2 - A₂.2
    let b₂ : ℝ := -(B₂.1 - A₂.1)
    let c₂ : ℝ := a₂ * A₂.1 + b₂ * A₂.2
    have ha₂K : a₂ ∈ K := K.sub_mem hB2y hA2y
    have hb₂K : b₂ ∈ K := K.neg_mem (K.sub_mem hB2x hA2x)
    have hc₂K : c₂ ∈ K := K.add_mem (K.mul_mem ha₂K hA2x) (K.mul_mem hb₂K hA2y)
    have hL₂_iff : ∀ p : Point, OnCurve (Curve.line A₂ B₂ hne₂) p ↔ a₂ * p.1 + b₂ * p.2 = c₂ := by
      intro p; unfold OnCurve Collinear3; dsimp [a₂, b₂, c₂]; constructor <;> intro h <;> linarith
    let L₂ : ℝ → ℝ := fun τ => (-a₂) * τ ^ 2 + (2 * b₂) * τ + a₂
    let f : ℝ → ℝ := fun τ => (c₁ * (1 + τ ^ 2) + L₁ τ) * L₂ τ - c₂ * (1 + τ ^ 2) * L₁ τ
    have hft : f t = 0 := by
      have h2 := (hL₂_iff P₂).mp hYγ₂
      rw [hY1, hY2] at h2
      field_simp [ht_den] at h2
      have hL2_t : (ρ + 1) * L₂ t = c₂ * (1 + t ^ 2) := by dsimp [L₂]; linarith
      dsimp [f]; linear_combination -L₂ t * hL₁_t + L₁ t * hL2_t
    have hfnz : ∃ t₀ : ℝ, f t₀ ≠ 0 := by
      apply exists_ne_zero_of_finite_solutions hfin L₁ f (quad_zero_set_finite _ _ _ hL₁_nz)
      intro τ hD hfz
      let r : ℝ := c₁ * (1 + τ ^ 2) / L₁ τ
      let v₁ : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)
      let v₂ : ℝ := (2 * τ) / (1 + τ ^ 2)
      have hq : 1 + τ ^ 2 ≠ 0 := by positivity
      have hv : v₁ ^ 2 + v₂ ^ 2 = 1 := by dsimp [v₁, v₂]; field_simp [hq]; ring
      refine ⟨((r * v₁, r * v₂), ((r + 1) * v₁, (r + 1) * v₂)), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hL₁_iff]; dsimp only [r, v₁, v₂]; field_simp [hq, hD]; dsimp only [L₁]; ring
      · rw [hL₂_iff]; dsimp only [r, v₁, v₂]; field_simp [hq, hD]
        dsimp only [f] at hfz; dsimp only [L₁, L₂] at hfz ⊢; linear_combination hfz
      · unfold Collinear3; ring
      · unfold distSq; dsimp only; linear_combination hv
      · ring
      · ring
    let k₄ := (c₁ - a₁) * (-a₂) - c₂ * (-a₁)
    let k₃ := (c₁ - a₁) * (2 * b₂) + (2 * b₁) * (-a₂) - c₂ * (2 * b₁)
    let k₂ := (c₁ - a₁) * a₂ + (2 * b₁) * (2 * b₂) + (c₁ + a₁) * (-a₂) - c₂ * (a₁ - a₁)
    let k₁ := (2 * b₁) * a₂ + (c₁ + a₁) * (2 * b₂) - c₂ * (2 * b₁)
    let k₀ := (c₁ + a₁) * a₂ - c₂ * a₁
    have hf_eq : ∀ τ : ℝ, f τ = k₄ * τ ^ 4 + k₃ * τ ^ 3 + k₂ * τ ^ 2 + k₁ * τ + k₀ := by
      intro τ; dsimp [f, L₁, L₂, k₄, k₃, k₂, k₁, k₀]; ring
    have hk₄K : k₄ ∈ K :=
      K.sub_mem (K.mul_mem (K.sub_mem hc₁K ha₁K) (K.neg_mem ha₂K)) (K.mul_mem hc₂K (K.neg_mem ha₁K))
    have hk₃K : k₃ ∈ K :=
      K.sub_mem (K.add_mem (K.mul_mem (K.sub_mem hc₁K ha₁K) (K.mul_mem (subfield_natCast_mem K 2) hb₂K))
        (K.mul_mem (K.mul_mem (subfield_natCast_mem K 2) hb₁K) (K.neg_mem ha₂K)))
        (K.mul_mem hc₂K (K.mul_mem (subfield_natCast_mem K 2) hb₁K))
    have hk₂K : k₂ ∈ K :=
      K.sub_mem (K.add_mem (K.add_mem (K.mul_mem (K.sub_mem hc₁K ha₁K) ha₂K)
        (K.mul_mem (K.mul_mem (subfield_natCast_mem K 2) hb₁K) (K.mul_mem (subfield_natCast_mem K 2) hb₂K)))
        (K.mul_mem (K.add_mem hc₁K ha₁K) (K.neg_mem ha₂K)))
        (K.mul_mem hc₂K (K.sub_mem ha₁K ha₁K))
    have hk₁K : k₁ ∈ K :=
      K.sub_mem (K.add_mem (K.mul_mem (K.mul_mem (subfield_natCast_mem K 2) hb₁K) ha₂K)
        (K.mul_mem (K.add_mem hc₁K ha₁K) (K.mul_mem (subfield_natCast_mem K 2) hb₂K)))
        (K.mul_mem hc₂K (K.mul_mem (subfield_natCast_mem K 2) hb₁K))
    have hk₀K : k₀ ∈ K :=
      K.sub_mem (K.mul_mem (K.add_mem hc₁K ha₁K) ha₂K) (K.mul_mem hc₂K ha₁K)
    exact inDeg6Tower_of_poly4 hK k₀ k₁ k₂ k₃ k₄ hk₀K hk₁K hk₂K hk₃K hk₄K
        (by rcases hfnz with ⟨t₀, ht₀⟩; exact ⟨t₀, by rwa [← hf_eq t₀]⟩)
        (by rw [← hf_eq t]; exact hft)

/-- Case 2 (Line-Circle) of Baragar's necessity theorem: `t` lies in a degree-≤6 extension of `K`. -/
private lemma neusis_origin_lc_t {K : Subfield ℝ} (hK : InDeg6Tower K)
    {A₁ B₁ C₂ Q₂ P₁ P₂ : Point} {hne₁ : A₁ ≠ B₁} {hne₂ : C₂ ≠ Q₂}
    (hγ₁ : CurveIn K (Curve.line A₁ B₁ hne₁)) (hγ₂ : CurveIn K (Curve.circle C₂ Q₂ hne₂))
    (hfin : (NeusisSolutions (0, 0) (Curve.line A₁ B₁ hne₁) (Curve.circle C₂ Q₂ hne₂)).Finite)
    (hXγ₁ : OnCurve (Curve.line A₁ B₁ hne₁) P₁) (hYγ₂ : OnCurve (Curve.circle C₂ Q₂ hne₂) P₂)
    {t ρ : ℝ}
    (hX1 : P₁.1 = ρ * ((1 - t ^ 2) / (1 + t ^ 2))) (hX2 : P₁.2 = ρ * (2 * t / (1 + t ^ 2)))
    (hY1 : P₂.1 = (ρ + 1) * ((1 - t ^ 2) / (1 + t ^ 2))) (hY2 : P₂.2 = (ρ + 1) * (2 * t / (1 + t ^ 2))) :
    ∃ K₁ : Subfield ℝ, InDeg6Tower K₁ ∧ K ≤ K₁ ∧ t ∈ K₁ := by
  have ht_den : 1 + t ^ 2 ≠ 0 := by positivity
  rcases hγ₁ with ⟨hA1x, hA1y, hB1x, hB1y⟩
  let a₁ : ℝ := B₁.2 - A₁.2
  let b₁ : ℝ := -(B₁.1 - A₁.1)
  let c₁ : ℝ := a₁ * A₁.1 + b₁ * A₁.2
  have ha₁K : a₁ ∈ K := K.sub_mem hB1y hA1y
  have hb₁K : b₁ ∈ K := K.neg_mem (K.sub_mem hB1x hA1x)
  have hc₁K : c₁ ∈ K := K.add_mem (K.mul_mem ha₁K hA1x) (K.mul_mem hb₁K hA1y)
  have hab₁ : a₁ ≠ 0 ∨ b₁ ≠ 0 := by
    by_contra h; push Not at h; apply hne₁
    exact Prod.ext (by dsimp [b₁] at h; linarith) (by dsimp [a₁] at h; linarith)
  have hL₁_iff : ∀ p : Point, OnCurve (Curve.line A₁ B₁ hne₁) p ↔ a₁ * p.1 + b₁ * p.2 = c₁ := by
    intro p; unfold OnCurve Collinear3; dsimp [a₁, b₁, c₁]; constructor <;> intro h <;> linarith
  let L₁ : ℝ → ℝ := fun τ => (-a₁) * τ ^ 2 + (2 * b₁) * τ + a₁
  have hL₁_nz : (-a₁) ≠ 0 ∨ (2 * b₁) ≠ 0 ∨ a₁ ≠ 0 := by
    rcases hab₁ with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr (Or.inl (mul_ne_zero two_ne_zero h))
  have hL₁_t : ρ * L₁ t = c₁ * (1 + t ^ 2) := by
    have h1 := (hL₁_iff P₁).mp hXγ₁
    rw [hX1, hX2] at h1
    dsimp [L₁]; field_simp [ht_den] at h1; linarith
  by_cases hL1_0 : L₁ t = 0
  · have hne2 : (-a₁) ≠ 0 ∨ (2 * b₁) ≠ 0 := by
      rcases hab₁ with h | h
      · exact Or.inl (neg_ne_zero.mpr h)
      · exact Or.inr (mul_ne_zero two_ne_zero h)
    exact inDeg6Tower_of_quad hK (K.neg_mem ha₁K) (K.mul_mem (subfield_natCast_mem K 2) hb₁K) ha₁K
        hne2 hL1_0
  · rcases hγ₂ with ⟨hC2x, hC2y, hQ2x, hQ2y⟩
    let a₂ := C₂.1; let b₂ := C₂.2
    let d₂ := C₂.1 ^ 2 + C₂.2 ^ 2 - distSq C₂ Q₂
    have ha₂K : a₂ ∈ K := hC2x; have hb₂K : b₂ ∈ K := hC2y
    have hd₂K : d₂ ∈ K := by
      dsimp [d₂]; unfold distSq
      exact K.sub_mem (K.add_mem (K.pow_mem hC2x 2) (K.pow_mem hC2y 2))
        (K.add_mem (K.pow_mem (K.sub_mem hC2x hQ2x) 2) (K.pow_mem (K.sub_mem hC2y hQ2y) 2))
    have hC₂_iff : ∀ p : Point, OnCurve (Curve.circle C₂ Q₂ hne₂) p ↔
        p.1 ^ 2 + p.2 ^ 2 - 2 * a₂ * p.1 - 2 * b₂ * p.2 + d₂ = 0 := by
      intro p; unfold OnCurve; dsimp only [a₂, b₂, d₂]; unfold distSq; constructor <;> intro h <;> linarith
    let NL : ℝ → ℝ := fun τ => c₁ * (1 + τ ^ 2) + L₁ τ
    let f : ℝ → ℝ := fun τ =>
      NL τ ^ 2 * (1 + τ ^ 2) - 2 * NL τ * L₁ τ * (a₂ * (1 - τ ^ 2) + 2 * b₂ * τ) +
      d₂ * L₁ τ ^ 2 * (1 + τ ^ 2)
    have hft : f t = 0 := by
      have h2 := (hC₂_iff P₂).mp hYγ₂
      rw [hY1, hY2] at h2
      have hρ_eq : ρ + 1 = NL t / L₁ t := by dsimp [NL]; field_simp [hL1_0]; linarith
      have hu : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
        field_simp [ht_den]; ring
      have h2'' : (ρ + 1) ^ 2 - 2 * (ρ + 1) * (a₂ * ((1 - t ^ 2) / (1 + t ^ 2)) +
          b₂ * (2 * t / (1 + t ^ 2))) + d₂ = 0 := by
        linear_combination h2 - (ρ + 1) ^ 2 * hu
      have h2' : (ρ + 1) ^ 2 * (1 + t ^ 2) - 2 * (ρ + 1) * (a₂ * (1 - t ^ 2) + 2 * b₂ * t) +
          d₂ * (1 + t ^ 2) = 0 := by
        field_simp [ht_den] at h2''; linarith
      rw [hρ_eq] at h2'; field_simp [hL1_0] at h2'; dsimp [f]; linarith
    have hfnz : ∃ t₀ : ℝ, f t₀ ≠ 0 := by
      apply exists_ne_zero_of_finite_solutions hfin L₁ f (quad_zero_set_finite _ _ _ hL₁_nz)
      intro τ hD hfz
      let r : ℝ := c₁ * (1 + τ ^ 2) / L₁ τ
      let v₁ : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)
      let v₂ : ℝ := (2 * τ) / (1 + τ ^ 2)
      have hq : 1 + τ ^ 2 ≠ 0 := by positivity
      have hv : v₁ ^ 2 + v₂ ^ 2 = 1 := by dsimp [v₁, v₂]; field_simp [hq]; ring
      refine ⟨((r * v₁, r * v₂), ((r + 1) * v₁, (r + 1) * v₂)), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hL₁_iff]; dsimp only [r, v₁, v₂]; field_simp [hq, hD]; dsimp only [L₁]; ring
      · rw [hC₂_iff]
        have h1 : r + 1 = NL τ / L₁ τ := by dsimp only [r, NL]; field_simp [hD]
        have hsq : ((r + 1) * v₁) ^ 2 + ((r + 1) * v₂) ^ 2 = (r + 1) ^ 2 := by
          linear_combination (r + 1) ^ 2 * hv
        rw [hsq, h1]; dsimp only [v₁, v₂]; field_simp [hq, hD]
        dsimp only [f] at hfz; linear_combination hfz
      · unfold Collinear3; ring
      · unfold distSq; dsimp only; linear_combination hv
      · ring
      · ring
    let q₁ : Polynomial K := C ⟨c₁ - a₁, K.sub_mem hc₁K ha₁K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₁, K.mul_mem (subfield_natCast_mem K 2) hb₁K⟩ * Polynomial.X + C ⟨c₁ + a₁, K.add_mem hc₁K ha₁K⟩
    let q₂ : Polynomial K := C ⟨-a₁, K.neg_mem ha₁K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₁, K.mul_mem (subfield_natCast_mem K 2) hb₁K⟩ * Polynomial.X + C ⟨a₁, ha₁K⟩
    let q₃ : Polynomial K := C ⟨-a₂, K.neg_mem ha₂K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₂, K.mul_mem (subfield_natCast_mem K 2) hb₂K⟩ * Polynomial.X + C ⟨a₂, ha₂K⟩
    let pK : Polynomial K := q₁ ^ 2 * (Polynomial.X ^ 2 + 1) - C (2 : K) * q₁ * q₂ * q₃ +
      C ⟨d₂, hd₂K⟩ * q₂ ^ 2 * (Polynomial.X ^ 2 + 1)
    have hpK_eval : ∀ τ : ℝ, Polynomial.aeval τ pK = f τ := by
      intro τ
      have hq₁ : Polynomial.aeval τ q₁ = NL τ := by simp [q₁, NL, L₁]; ring
      have hq₂ : Polynomial.aeval τ q₂ = L₁ τ := by simp [q₂, L₁]
      have hq₃ : Polynomial.aeval τ q₃ = a₂ * (1 - τ ^ 2) + 2 * b₂ * τ := by simp [q₃]; ring
      simp only [pK, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, aeval_C, aeval_X,
        hq₁, hq₂, hq₃, subfield_algebraMap_coe, f]
      ring
    have hpK_ne : pK ≠ 0 := by
      intro h0; rcases hfnz with ⟨t₀, ht₀⟩
      have := hpK_eval t₀; rw [h0, map_zero] at this; exact ht₀ this.symm
    have hdeg_pK : pK.natDegree ≤ 6 :=
      natDegree_baragar_sextic_le q₁ q₂ q₃ (natDegree_quad_le _ _ _) (natDegree_quad_le _ _ _)
        (natDegree_quad_le _ _ _) 2 ⟨d₂, hd₂K⟩
    exact inDeg6Tower_adjoin_poly hK pK hpK_ne hdeg_pK (by rw [hpK_eval]; exact hft)

/-- Case 3 (Circle-Line) of Baragar's necessity theorem: `t` lies in a degree-≤6 extension of `K`. -/
private lemma neusis_origin_cl_t {K : Subfield ℝ} (hK : InDeg6Tower K)
    {C₁ Q₁ A₂ B₂ P₁ P₂ : Point} {hne₁ : C₁ ≠ Q₁} {hne₂ : A₂ ≠ B₂}
    (hγ₁ : CurveIn K (Curve.circle C₁ Q₁ hne₁)) (hγ₂ : CurveIn K (Curve.line A₂ B₂ hne₂))
    (hfin : (NeusisSolutions (0, 0) (Curve.circle C₁ Q₁ hne₁) (Curve.line A₂ B₂ hne₂)).Finite)
    (hXγ₁ : OnCurve (Curve.circle C₁ Q₁ hne₁) P₁) (hYγ₂ : OnCurve (Curve.line A₂ B₂ hne₂) P₂)
    {t ρ : ℝ}
    (hX1 : P₁.1 = ρ * ((1 - t ^ 2) / (1 + t ^ 2))) (hX2 : P₁.2 = ρ * (2 * t / (1 + t ^ 2)))
    (hY1 : P₂.1 = (ρ + 1) * ((1 - t ^ 2) / (1 + t ^ 2))) (hY2 : P₂.2 = (ρ + 1) * (2 * t / (1 + t ^ 2))) :
    ∃ K₁ : Subfield ℝ, InDeg6Tower K₁ ∧ K ≤ K₁ ∧ t ∈ K₁ := by
  have ht_den : 1 + t ^ 2 ≠ 0 := by positivity
  rcases hγ₁ with ⟨hC1x, hC1y, hQ1x, hQ1y⟩
  let a₁ := C₁.1; let b₁ := C₁.2
  let d₁ := C₁.1 ^ 2 + C₁.2 ^ 2 - distSq C₁ Q₁
  have ha₁K : a₁ ∈ K := hC1x; have hb₁K : b₁ ∈ K := hC1y
  have hd₁K : d₁ ∈ K := by
    dsimp [d₁]; unfold distSq
    exact K.sub_mem (K.add_mem (K.pow_mem hC1x 2) (K.pow_mem hC1y 2))
      (K.add_mem (K.pow_mem (K.sub_mem hC1x hQ1x) 2) (K.pow_mem (K.sub_mem hC1y hQ1y) 2))
  have hC₁_iff : ∀ p : Point, OnCurve (Curve.circle C₁ Q₁ hne₁) p ↔
      p.1 ^ 2 + p.2 ^ 2 - 2 * a₁ * p.1 - 2 * b₁ * p.2 + d₁ = 0 := by
    intro p; unfold OnCurve; dsimp only [a₁, b₁, d₁]; unfold distSq; constructor <;> intro h <;> linarith
  rcases hγ₂ with ⟨hA2x, hA2y, hB2x, hB2y⟩
  let a₂ : ℝ := B₂.2 - A₂.2
  let b₂ : ℝ := -(B₂.1 - A₂.1)
  let c₂ : ℝ := a₂ * A₂.1 + b₂ * A₂.2
  have ha₂K : a₂ ∈ K := K.sub_mem hB2y hA2y
  have hb₂K : b₂ ∈ K := K.neg_mem (K.sub_mem hB2x hA2x)
  have hc₂K : c₂ ∈ K := K.add_mem (K.mul_mem ha₂K hA2x) (K.mul_mem hb₂K hA2y)
  have hab₂ : a₂ ≠ 0 ∨ b₂ ≠ 0 := by
    by_contra h; push Not at h; apply hne₂
    exact Prod.ext (by dsimp [b₂] at h; linarith) (by dsimp [a₂] at h; linarith)
  have hL₂_iff : ∀ p : Point, OnCurve (Curve.line A₂ B₂ hne₂) p ↔ a₂ * p.1 + b₂ * p.2 = c₂ := by
    intro p; unfold OnCurve Collinear3; dsimp [a₂, b₂, c₂]; constructor <;> intro h <;> linarith
  let L₂ : ℝ → ℝ := fun τ => (-a₂) * τ ^ 2 + (2 * b₂) * τ + a₂
  have hL₂_nz : (-a₂) ≠ 0 ∨ (2 * b₂) ≠ 0 ∨ a₂ ≠ 0 := by
    rcases hab₂ with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr (Or.inl (mul_ne_zero two_ne_zero h))
  have hL₂_t : (ρ + 1) * L₂ t = c₂ * (1 + t ^ 2) := by
    have h2 := (hL₂_iff P₂).mp hYγ₂
    rw [hY1, hY2] at h2
    field_simp [ht_den] at h2; dsimp [L₂]; linarith
  by_cases hL2_0 : L₂ t = 0
  · have hne2 : (-a₂) ≠ 0 ∨ (2 * b₂) ≠ 0 := by
      rcases hab₂ with h | h
      · exact Or.inl (neg_ne_zero.mpr h)
      · exact Or.inr (mul_ne_zero two_ne_zero h)
    exact inDeg6Tower_of_quad hK (K.neg_mem ha₂K) (K.mul_mem (subfield_natCast_mem K 2) hb₂K) ha₂K
        hne2 hL2_0
  · let NL : ℝ → ℝ := fun τ => c₂ * (1 + τ ^ 2) - L₂ τ
    let f : ℝ → ℝ := fun τ =>
      NL τ ^ 2 * (1 + τ ^ 2) - 2 * NL τ * L₂ τ * (a₁ * (1 - τ ^ 2) + 2 * b₁ * τ) +
      d₁ * L₂ τ ^ 2 * (1 + τ ^ 2)
    have hft : f t = 0 := by
      have h1 := (hC₁_iff P₁).mp hXγ₁
      rw [hX1, hX2] at h1
      have hρ_eq : ρ = NL t / L₂ t := by dsimp [NL]; field_simp [hL2_0]; linarith
      have hu : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
        field_simp [ht_den]; ring
      have h1'' : ρ ^ 2 - 2 * ρ * (a₁ * ((1 - t ^ 2) / (1 + t ^ 2)) +
          b₁ * (2 * t / (1 + t ^ 2))) + d₁ = 0 := by
        linear_combination h1 - ρ ^ 2 * hu
      have h1' : ρ ^ 2 * (1 + t ^ 2) - 2 * ρ * (a₁ * (1 - t ^ 2) + 2 * b₁ * t) +
          d₁ * (1 + t ^ 2) = 0 := by
        field_simp [ht_den] at h1''; linarith
      rw [hρ_eq] at h1'; field_simp [hL2_0] at h1'; dsimp [f]; linarith
    have hfnz : ∃ t₀ : ℝ, f t₀ ≠ 0 := by
      apply exists_ne_zero_of_finite_solutions hfin L₂ f (quad_zero_set_finite _ _ _ hL₂_nz)
      intro τ hD hfz
      let r : ℝ := NL τ / L₂ τ
      let v₁ : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)
      let v₂ : ℝ := (2 * τ) / (1 + τ ^ 2)
      have hq : 1 + τ ^ 2 ≠ 0 := by positivity
      have hv : v₁ ^ 2 + v₂ ^ 2 = 1 := by dsimp [v₁, v₂]; field_simp [hq]; ring
      refine ⟨((r * v₁, r * v₂), ((r + 1) * v₁, (r + 1) * v₂)), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hC₁_iff]
        have hsq : (r * v₁) ^ 2 + (r * v₂) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * hv
        rw [hsq]; dsimp only [r, v₁, v₂]; field_simp [hq, hD]
        dsimp only [f] at hfz; linear_combination hfz
      · rw [hL₂_iff]; dsimp only [r, NL, v₁, v₂]; field_simp [hq, hD]; dsimp only [L₂]; ring
      · unfold Collinear3; ring
      · unfold distSq; dsimp only; linear_combination hv
      · ring
      · ring
    let q₁ : Polynomial K := C ⟨c₂ + a₂, K.add_mem hc₂K ha₂K⟩ * Polynomial.X ^ 2 +
      C ⟨-(2 * b₂), K.neg_mem (K.mul_mem (subfield_natCast_mem K 2) hb₂K)⟩ * Polynomial.X +
      C ⟨c₂ - a₂, K.sub_mem hc₂K ha₂K⟩
    let q₂ : Polynomial K := C ⟨-a₂, K.neg_mem ha₂K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₂, K.mul_mem (subfield_natCast_mem K 2) hb₂K⟩ * Polynomial.X + C ⟨a₂, ha₂K⟩
    let q₃ : Polynomial K := C ⟨-a₁, K.neg_mem ha₁K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₁, K.mul_mem (subfield_natCast_mem K 2) hb₁K⟩ * Polynomial.X + C ⟨a₁, ha₁K⟩
    let pK : Polynomial K := q₁ ^ 2 * (Polynomial.X ^ 2 + 1) - C (2 : K) * q₁ * q₂ * q₃ +
      C ⟨d₁, hd₁K⟩ * q₂ ^ 2 * (Polynomial.X ^ 2 + 1)
    have hpK_eval : ∀ τ : ℝ, Polynomial.aeval τ pK = f τ := by
      intro τ
      have hq₁ : Polynomial.aeval τ q₁ = NL τ := by simp [q₁, NL, L₂]; ring
      have hq₂ : Polynomial.aeval τ q₂ = L₂ τ := by simp [q₂, L₂]
      have hq₃ : Polynomial.aeval τ q₃ = a₁ * (1 - τ ^ 2) + 2 * b₁ * τ := by simp [q₃]; ring
      simp only [pK, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, aeval_C, aeval_X,
        hq₁, hq₂, hq₃, subfield_algebraMap_coe, f]
      ring
    have hpK_ne : pK ≠ 0 := by
      intro h0; rcases hfnz with ⟨t₀, ht₀⟩
      have := hpK_eval t₀; rw [h0, map_zero] at this; exact ht₀ this.symm
    have hdeg_pK : pK.natDegree ≤ 6 :=
      natDegree_baragar_sextic_le q₁ q₂ q₃ (natDegree_quad_le _ _ _) (natDegree_quad_le _ _ _)
        (natDegree_quad_le _ _ _) 2 ⟨d₁, hd₁K⟩
    exact inDeg6Tower_adjoin_poly hK pK hpK_ne hdeg_pK (by rw [hpK_eval]; exact hft)

/-- Case 4 (Circle-Circle) of Baragar's necessity theorem: `t` lies in a degree-≤6 extension of `K`. -/
private lemma neusis_origin_cc_t {K : Subfield ℝ} (hK : InDeg6Tower K)
    {C₁ Q₁ C₂ Q₂ P₁ P₂ : Point} {hne₁ : C₁ ≠ Q₁} {hne₂ : C₂ ≠ Q₂}
    (hγ₁ : CurveIn K (Curve.circle C₁ Q₁ hne₁)) (hγ₂ : CurveIn K (Curve.circle C₂ Q₂ hne₂))
    (hfin : (NeusisSolutions (0, 0) (Curve.circle C₁ Q₁ hne₁) (Curve.circle C₂ Q₂ hne₂)).Finite)
    (hXγ₁ : OnCurve (Curve.circle C₁ Q₁ hne₁) P₁) (hYγ₂ : OnCurve (Curve.circle C₂ Q₂ hne₂) P₂)
    {t ρ : ℝ}
    (hX1 : P₁.1 = ρ * ((1 - t ^ 2) / (1 + t ^ 2))) (hX2 : P₁.2 = ρ * (2 * t / (1 + t ^ 2)))
    (hY1 : P₂.1 = (ρ + 1) * ((1 - t ^ 2) / (1 + t ^ 2))) (hY2 : P₂.2 = (ρ + 1) * (2 * t / (1 + t ^ 2))) :
    ∃ K₁ : Subfield ℝ, InDeg6Tower K₁ ∧ K ≤ K₁ ∧ t ∈ K₁ := by
  have ht_den : 1 + t ^ 2 ≠ 0 := by positivity
  rcases hγ₁ with ⟨hC1x, hC1y, hQ1x, hQ1y⟩
  let a₁ := C₁.1; let b₁ := C₁.2
  let d₁ := C₁.1 ^ 2 + C₁.2 ^ 2 - distSq C₁ Q₁
  have ha₁K : a₁ ∈ K := hC1x; have hb₁K : b₁ ∈ K := hC1y
  have hd₁K : d₁ ∈ K := by
    dsimp [d₁]; unfold distSq
    exact K.sub_mem (K.add_mem (K.pow_mem hC1x 2) (K.pow_mem hC1y 2))
      (K.add_mem (K.pow_mem (K.sub_mem hC1x hQ1x) 2) (K.pow_mem (K.sub_mem hC1y hQ1y) 2))
  have hC₁_iff : ∀ p : Point, OnCurve (Curve.circle C₁ Q₁ hne₁) p ↔
      p.1 ^ 2 + p.2 ^ 2 - 2 * a₁ * p.1 - 2 * b₁ * p.2 + d₁ = 0 := by
    intro p; unfold OnCurve; dsimp only [a₁, b₁, d₁]; unfold distSq; constructor <;> intro h <;> linarith
  rcases hγ₂ with ⟨hC2x, hC2y, hQ2x, hQ2y⟩
  let a₂ := C₂.1; let b₂ := C₂.2
  let d₂ := C₂.1 ^ 2 + C₂.2 ^ 2 - distSq C₂ Q₂
  have ha₂K : a₂ ∈ K := hC2x; have hb₂K : b₂ ∈ K := hC2y
  have hd₂K : d₂ ∈ K := by
    dsimp [d₂]; unfold distSq
    exact K.sub_mem (K.add_mem (K.pow_mem hC2x 2) (K.pow_mem hC2y 2))
      (K.add_mem (K.pow_mem (K.sub_mem hC2x hQ2x) 2) (K.pow_mem (K.sub_mem hC2y hQ2y) 2))
  have hC₂_iff : ∀ p : Point, OnCurve (Curve.circle C₂ Q₂ hne₂) p ↔
      p.1 ^ 2 + p.2 ^ 2 - 2 * a₂ * p.1 - 2 * b₂ * p.2 + d₂ = 0 := by
    intro p; unfold OnCurve; dsimp only [a₂, b₂, d₂]; unfold distSq; constructor <;> intro h <;> linarith
  let D : ℝ → ℝ := fun τ => (1 + a₂ - a₁) * τ ^ 2 + (-2 * (b₂ - b₁)) * τ + (1 - a₂ + a₁)
  let N : ℝ → ℝ := fun τ => (d₁ - d₂ - 1 - 2 * a₂) * τ ^ 2 + (4 * b₂) * τ + (d₁ - d₂ - 1 + 2 * a₂)
  have hD_nz : (1 + a₂ - a₁) ≠ 0 ∨ (-2 * (b₂ - b₁)) ≠ 0 ∨ (1 - a₂ + a₁) ≠ 0 := by
    by_contra h; push Not at h; linarith
  have hu : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp [ht_den]; ring
  have h1'' : ρ ^ 2 - 2 * ρ * (a₁ * ((1 - t ^ 2) / (1 + t ^ 2)) +
      b₁ * (2 * t / (1 + t ^ 2))) + d₁ = 0 := by
    have h1 := (hC₁_iff P₁).mp hXγ₁; rw [hX1, hX2] at h1
    linear_combination h1 - ρ ^ 2 * hu
  have h2'' : (ρ + 1) ^ 2 - 2 * (ρ + 1) * (a₂ * ((1 - t ^ 2) / (1 + t ^ 2)) +
      b₂ * (2 * t / (1 + t ^ 2))) + d₂ = 0 := by
    have h2 := (hC₂_iff P₂).mp hYγ₂; rw [hY1, hY2] at h2
    linear_combination h2 - (ρ + 1) ^ 2 * hu
  have hsub_t : 2 * ρ * D t = N t := by
    have hdiff : 2 * ρ + 1 - 2 * ρ * ((a₂ - a₁) * ((1 - t ^ 2) / (1 + t ^ 2)) +
        (b₂ - b₁) * (2 * t / (1 + t ^ 2))) -
        2 * (a₂ * ((1 - t ^ 2) / (1 + t ^ 2)) + b₂ * (2 * t / (1 + t ^ 2))) + (d₂ - d₁) = 0 := by
      linarith
    field_simp [ht_den] at hdiff; dsimp only [D, N]; linear_combination hdiff
  by_cases hD0 : D t = 0
  · have hne2 : (1 + a₂ - a₁) ≠ 0 ∨ (-2 * (b₂ - b₁)) ≠ 0 := by
      by_contra h; push Not at h; dsimp only [D] at hD0; rw [h.1, h.2] at hD0; linarith
    have hd2K : 1 + a₂ - a₁ ∈ K := K.sub_mem (K.add_mem K.one_mem ha₂K) ha₁K
    have hd1K : -2 * (b₂ - b₁) ∈ K := K.mul_mem (K.neg_mem (subfield_natCast_mem K 2)) (K.sub_mem hb₂K hb₁K)
    have hd0K : 1 - a₂ + a₁ ∈ K := K.add_mem (K.sub_mem K.one_mem ha₂K) ha₁K
    exact inDeg6Tower_of_quad hK hd2K hd1K hd0K hne2 hD0
  · let f : ℝ → ℝ := fun τ =>
      N τ ^ 2 * (1 + τ ^ 2) - 4 * N τ * D τ * (a₁ * (1 - τ ^ 2) + 2 * b₁ * τ) +
      4 * d₁ * D τ ^ 2 * (1 + τ ^ 2)
    have hft : f t = 0 := by
      have h1' : ρ ^ 2 * (1 + t ^ 2) - 2 * ρ * (a₁ * (1 - t ^ 2) + 2 * b₁ * t) +
          d₁ * (1 + t ^ 2) = 0 := by
        field_simp [ht_den] at h1''; linarith
      have hρ_eq : ρ = N t / (2 * D t) := by
        have h2D : 2 * D t ≠ 0 := mul_ne_zero two_ne_zero hD0
        field_simp [h2D]; linarith
      rw [hρ_eq] at h1'; field_simp [hD0] at h1'; dsimp [f]; linear_combination h1'
    have hfnz : ∃ t₀ : ℝ, f t₀ ≠ 0 := by
      apply exists_ne_zero_of_finite_solutions hfin D f (quad_zero_set_finite _ _ _ hD_nz)
      intro τ hD hfz
      let r : ℝ := N τ / (2 * D τ)
      let v₁ : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)
      let v₂ : ℝ := (2 * τ) / (1 + τ ^ 2)
      have hq : 1 + τ ^ 2 ≠ 0 := by positivity
      have hv : v₁ ^ 2 + v₂ ^ 2 = 1 := by dsimp [v₁, v₂]; field_simp [hq]; ring
      have hc1_ok : r ^ 2 - 2 * r * (a₁ * v₁ + b₁ * v₂) + d₁ = 0 := by
        dsimp only [r, v₁, v₂]; field_simp [hq, hD]; dsimp only [f] at hfz; linear_combination hfz
      have hc2_ok : (r + 1) ^ 2 - 2 * (r + 1) * (a₂ * v₁ + b₂ * v₂) + d₂ = 0 := by
        have hlin : 2 * r * D τ = N τ := by dsimp only [r]; field_simp [hD]
        have hsub : (r + 1) ^ 2 - 2 * (r + 1) * (a₂ * v₁ + b₂ * v₂) + d₂ -
            (r ^ 2 - 2 * r * (a₁ * v₁ + b₁ * v₂) + d₁) = 0 := by
          dsimp only [v₁, v₂]; field_simp [hq]; dsimp only [D, N] at hlin; linear_combination hlin
        linarith
      refine ⟨((r * v₁, r * v₂), ((r + 1) * v₁, (r + 1) * v₂)), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hC₁_iff]; linear_combination hc1_ok + r ^ 2 * hv
      · rw [hC₂_iff]; linear_combination hc2_ok + (r + 1) ^ 2 * hv
      · unfold Collinear3; ring
      · unfold distSq; dsimp only; linear_combination hv
      · ring
      · ring
    have hn₂K : d₁ - d₂ - 1 - 2 * a₂ ∈ K :=
      K.sub_mem (K.sub_mem (K.sub_mem hd₁K hd₂K) K.one_mem) (K.mul_mem (subfield_natCast_mem K 2) ha₂K)
    have hn₁K : 4 * b₂ ∈ K := K.mul_mem (subfield_natCast_mem K 4) hb₂K
    have hn₀K : d₁ - d₂ - 1 + 2 * a₂ ∈ K :=
      K.add_mem (K.sub_mem (K.sub_mem hd₁K hd₂K) K.one_mem) (K.mul_mem (subfield_natCast_mem K 2) ha₂K)
    have hl₂K : 1 + a₂ - a₁ ∈ K := K.sub_mem (K.add_mem K.one_mem ha₂K) ha₁K
    have hl₁K : -2 * (b₂ - b₁) ∈ K := K.mul_mem (K.neg_mem (subfield_natCast_mem K 2)) (K.sub_mem hb₂K hb₁K)
    have hl₀K : 1 - a₂ + a₁ ∈ K := K.add_mem (K.sub_mem K.one_mem ha₂K) ha₁K
    let q₁ : Polynomial K := C ⟨d₁ - d₂ - 1 - 2 * a₂, hn₂K⟩ * Polynomial.X ^ 2 +
      C ⟨4 * b₂, hn₁K⟩ * Polynomial.X + C ⟨d₁ - d₂ - 1 + 2 * a₂, hn₀K⟩
    let q₂ : Polynomial K := C ⟨1 + a₂ - a₁, hl₂K⟩ * Polynomial.X ^ 2 +
      C ⟨-2 * (b₂ - b₁), hl₁K⟩ * Polynomial.X + C ⟨1 - a₂ + a₁, hl₀K⟩
    let q₃ : Polynomial K := C ⟨-a₁, K.neg_mem ha₁K⟩ * Polynomial.X ^ 2 +
      C ⟨2 * b₁, K.mul_mem (subfield_natCast_mem K 2) hb₁K⟩ * Polynomial.X + C ⟨a₁, ha₁K⟩
    let pK : Polynomial K := q₁ ^ 2 * (Polynomial.X ^ 2 + 1) - C (4 : K) * q₁ * q₂ * q₃ +
      C ⟨4 * d₁, K.mul_mem (subfield_natCast_mem K 4) hd₁K⟩ * q₂ ^ 2 * (Polynomial.X ^ 2 + 1)
    have hpK_eval : ∀ τ : ℝ, Polynomial.aeval τ pK = f τ := by
      intro τ
      have hq₁ : Polynomial.aeval τ q₁ = N τ := by simp [q₁, N]
      have hq₂ : Polynomial.aeval τ q₂ = D τ := by simp [q₂, D]
      have hq₃ : Polynomial.aeval τ q₃ = a₁ * (1 - τ ^ 2) + 2 * b₁ * τ := by simp [q₃]; ring
      simp only [pK, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, aeval_C, aeval_X,
        hq₁, hq₂, hq₃, subfield_algebraMap_coe, f]
      ring
    have hpK_ne : pK ≠ 0 := by
      intro h0; rcases hfnz with ⟨t₀, ht₀⟩
      have := hpK_eval t₀; rw [h0, map_zero] at this; exact ht₀ this.symm
    have hdeg_pK : pK.natDegree ≤ 6 :=
      natDegree_baragar_sextic_le q₁ q₂ q₃ (natDegree_quad_le _ _ _) (natDegree_quad_le _ _ _)
        (natDegree_quad_le _ _ _) 4 ⟨4 * d₁, K.mul_mem (subfield_natCast_mem K 4) hd₁K⟩
    exact inDeg6Tower_adjoin_poly hK pK hpK_ne hdeg_pK (by rw [hpK_eval]; exact hft)

/-- General neusis step over `K` (after translating `P` to `(0, 0)`):
both `X` and `Y` lie in an `InDeg6Tower` extension of `K`. -/
lemma neusis_origin_inDeg6Tower {K : Subfield ℝ} (hK : InDeg6Tower K)
    {P₁ P₂ : Point} {γ₁ γ₂ : Curve}
    (hγ₁ : CurveIn K γ₁) (hγ₂ : CurveIn K γ₂)
    (hfin : (NeusisSolutions (0, 0) γ₁ γ₂).Finite)
    (hsol : (P₁, P₂) ∈ NeusisSolutions (0, 0) γ₁ γ₂) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧
      P₁.1 ∈ K' ∧ P₁.2 ∈ K' ∧ P₂.1 ∈ K' ∧ P₂.2 ∈ K' := by
  rcases hsol with ⟨hXγ₁, hYγ₂, hcol, hdist⟩
  let u₁ : ℝ := P₂.1 - P₁.1
  let u₂ : ℝ := P₂.2 - P₁.2
  have hu_norm : u₁ ^ 2 + u₂ ^ 2 = 1 := by
    unfold distSq at hdist; dsimp [u₁, u₂]; linarith
  have hcol_u : P₁.1 * u₂ = P₁.2 * u₁ := by
    unfold Collinear3 at hcol; dsimp [u₁, u₂]; linarith
  let ρ : ℝ := P₁.1 * u₁ + P₁.2 * u₂
  have hX1 : P₁.1 = ρ * u₁ := by dsimp [ρ]; linear_combination -P₁.1 * hu_norm + u₂ * hcol_u
  have hX2 : P₁.2 = ρ * u₂ := by dsimp [ρ]; linear_combination -P₁.2 * hu_norm - u₁ * hcol_u
  have hY1 : P₂.1 = (ρ + 1) * u₁ := by dsimp [u₁]; linarith
  have hY2 : P₂.2 = (ρ + 1) * u₂ := by dsimp [u₂]; linarith
  by_cases hu1m : u₁ = -1
  · have hu20 : u₂ = 0 := by nlinarith [hu_norm, hu1m]
    exact neusis_origin_from_dir hK le_rfl hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hu_norm hX1 hX2 hY1 hY2
      (by rw [hu1m]; exact K.neg_mem K.one_mem) (by rw [hu20]; exact K.zero_mem)
  have hu1_ne : 1 + u₁ ≠ 0 := fun h => hu1m (by linarith)
  let t : ℝ := u₂ / (1 + u₁)
  have hu1_t : u₁ = (1 - t ^ 2) / (1 + t ^ 2) := by
    dsimp [t]; field_simp [hu1_ne]
    linear_combination (1 + u₁) * hu_norm
  have hu2_t : u₂ = (2 * t) / (1 + t ^ 2) := by
    dsimp [t]; field_simp [hu1_ne]
    linear_combination u₂ * hu_norm
  have hX1t : P₁.1 = ρ * ((1 - t ^ 2) / (1 + t ^ 2)) := by rw [← hu1_t]; exact hX1
  have hX2t : P₁.2 = ρ * (2 * t / (1 + t ^ 2)) := by rw [← hu2_t]; exact hX2
  have hY1t : P₂.1 = (ρ + 1) * ((1 - t ^ 2) / (1 + t ^ 2)) := by rw [← hu1_t]; exact hY1
  have hY2t : P₂.2 = (ρ + 1) * (2 * t / (1 + t ^ 2)) := by rw [← hu2_t]; exact hY2
  have ht_ext : ∃ K₁ : Subfield ℝ, InDeg6Tower K₁ ∧ K ≤ K₁ ∧ t ∈ K₁ := by
    cases γ₁ with
    | line A₁ B₁ hne₁ =>
      cases γ₂ with
      | line A₂ B₂ hne₂ => exact neusis_origin_ll_t hK hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hX1t hX2t hY1t hY2t
      | circle C₂ Q₂ hne₂ => exact neusis_origin_lc_t hK hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hX1t hX2t hY1t hY2t
    | circle C₁ Q₁ hne₁ =>
      cases γ₂ with
      | line A₂ B₂ hne₂ => exact neusis_origin_cl_t hK hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hX1t hX2t hY1t hY2t
      | circle C₂ Q₂ hne₂ => exact neusis_origin_cc_t hK hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hX1t hX2t hY1t hY2t
  rcases ht_ext with ⟨K₁, hK₁, hle₁, htK⟩
  have hqK : 1 + t ^ 2 ∈ K₁ := K₁.add_mem K₁.one_mem (K₁.pow_mem htK 2)
  have hu1K : u₁ ∈ K₁ := by
    rw [hu1_t]; exact K₁.div_mem (K₁.sub_mem K₁.one_mem (K₁.pow_mem htK 2)) hqK
  have hu2K : u₂ ∈ K₁ := by
    rw [hu2_t]; exact K₁.div_mem (K₁.mul_mem (subfield_natCast_mem K₁ 2) htK) hqK
  exact neusis_origin_from_dir hK₁ hle₁ hγ₁ hγ₂ hfin hXγ₁ hYγ₂ hu_norm hX1 hX2 hY1 hY2 hu1K hu2K

/-- Translate a point by `-P`. -/
def shiftPt (P q : Point) : Point := (q.1 - P.1, q.2 - P.2)

/-- Translate a curve by `-P`. -/
def shiftCurve (P : Point) : Curve → Curve
  | Curve.line A B h => Curve.line (shiftPt P A) (shiftPt P B) (by
      intro heq; apply h
      exact Prod.ext (by have h1 : A.1 - P.1 = B.1 - P.1 := congrArg Prod.fst heq; linarith)
        (by have h2 : A.2 - P.2 = B.2 - P.2 := congrArg Prod.snd heq; linarith))
  | Curve.circle C Q h => Curve.circle (shiftPt P C) (shiftPt P Q) (by
      intro heq; apply h
      exact Prod.ext (by have h1 : C.1 - P.1 = Q.1 - P.1 := congrArg Prod.fst heq; linarith)
        (by have h2 : C.2 - P.2 = Q.2 - P.2 := congrArg Prod.snd heq; linarith))

lemma onCurve_shift (P : Point) (γ : Curve) (X : Point) :
    OnCurve (shiftCurve P γ) (shiftPt P X) ↔ OnCurve γ X := by
  cases γ with
  | line A B _ => unfold OnCurve shiftCurve shiftPt Collinear3; simp
  | circle C Q _ => unfold OnCurve shiftCurve shiftPt distSq; simp

lemma curveIn_shift {K : Subfield ℝ} {P : Point} {γ : Curve}
    (hP : P.1 ∈ K ∧ P.2 ∈ K) (hγ : CurveIn K γ) :
    CurveIn K (shiftCurve P γ) := by
  cases γ with
  | line A B _ =>
    rcases hγ with ⟨h1, h2, h3, h4⟩
    exact ⟨K.sub_mem h1 hP.1, K.sub_mem h2 hP.2, K.sub_mem h3 hP.1, K.sub_mem h4 hP.2⟩
  | circle C Q _ =>
    rcases hγ with ⟨h1, h2, h3, h4⟩
    exact ⟨K.sub_mem h1 hP.1, K.sub_mem h2 hP.2, K.sub_mem h3 hP.1, K.sub_mem h4 hP.2⟩

lemma neusis_step_inDeg6Tower {K : Subfield ℝ} (hK : InDeg6Tower K)
    {P X Y : Point} {γ₁ γ₂ : Curve}
    (hP : P.1 ∈ K ∧ P.2 ∈ K) (hγ₁ : CurveIn K γ₁) (hγ₂ : CurveIn K γ₂)
    (hfin : (NeusisSolutions P γ₁ γ₂).Finite)
    (hsol : (X, Y) ∈ NeusisSolutions P γ₁ γ₂) :
    ∃ K' : Subfield ℝ, InDeg6Tower K' ∧ K ≤ K' ∧
      X.1 ∈ K' ∧ X.2 ∈ K' ∧ Y.1 ∈ K' ∧ Y.2 ∈ K' := by
  have hfin' : (NeusisSolutions (0, 0) (shiftCurve P γ₁) (shiftCurve P γ₂)).Finite := by
    let f : Point × Point → Point × Point := fun xy =>
      ((xy.1.1 + P.1, xy.1.2 + P.2), (xy.2.1 + P.1, xy.2.2 + P.2))
    have hinj : Function.Injective f := by
      intro a b h
      have h1 : a.1.1 + P.1 = b.1.1 + P.1 := congrArg (fun p => p.1.1) h
      have h2 : a.1.2 + P.2 = b.1.2 + P.2 := congrArg (fun p => p.1.2) h
      have h3 : a.2.1 + P.1 = b.2.1 + P.1 := congrArg (fun p => p.2.1) h
      have h4 : a.2.2 + P.2 = b.2.2 + P.2 := congrArg (fun p => p.2.2) h
      exact Prod.ext (Prod.ext (by linarith) (by linarith)) (Prod.ext (by linarith) (by linarith))
    refine Set.Finite.of_finite_image ?_ (hinj.injOn)
    refine hfin.subset ?_
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy, hcol, hdist⟩, rfl⟩
    have hx' : shiftPt P (x.1 + P.1, x.2 + P.2) = x := by unfold shiftPt; ext <;> simp
    have hy' : shiftPt P (y.1 + P.1, y.2 + P.2) = y := by unfold shiftPt; ext <;> simp
    refine ⟨(onCurve_shift P γ₁ _).mp (by rwa [hx']),
            (onCurve_shift P γ₂ _).mp (by rwa [hy']), ?_, ?_⟩
    · unfold Collinear3 at hcol ⊢; dsimp only at hcol ⊢; linarith
    · unfold distSq at hdist ⊢; dsimp only at hdist ⊢; linarith
  have hsol' : (shiftPt P X, shiftPt P Y) ∈ NeusisSolutions (0, 0) (shiftCurve P γ₁) (shiftCurve P γ₂) := by
    rcases hsol with ⟨hx, hy, hcol, hdist⟩
    refine ⟨(onCurve_shift P γ₁ X).mpr hx, (onCurve_shift P γ₂ Y).mpr hy, ?_, ?_⟩
    · unfold Collinear3 at hcol ⊢; unfold shiftPt; dsimp only at hcol ⊢; linarith
    · unfold distSq at hdist ⊢; unfold shiftPt; dsimp only at hdist ⊢; linarith
  rcases neusis_origin_inDeg6Tower hK (curveIn_shift hP hγ₁) (curveIn_shift hP hγ₂) hfin' hsol' with
    ⟨K', hK', hle, hX1, hX2, hY1, hY2⟩
  refine ⟨K', hK', hle, ?_, ?_, ?_, ?_⟩
  · have : X.1 = (shiftPt P X).1 + P.1 := by unfold shiftPt; ring
    rw [this]; exact K'.add_mem hX1 (hle hP.1)
  · have : X.2 = (shiftPt P X).2 + P.2 := by unfold shiftPt; ring
    rw [this]; exact K'.add_mem hX2 (hle hP.2)
  · have : Y.1 = (shiftPt P Y).1 + P.1 := by unfold shiftPt; ring
    rw [this]; exact K'.add_mem hY1 (hle hP.1)
  · have : Y.2 = (shiftPt P Y).2 + P.2 := by unfold shiftPt; ring
    rw [this]; exact K'.add_mem hY2 (hle hP.2)

/-- **Baragar's Necessity Theorem (2002)**:
Every neusis-constructible point `(x, y)` lies in a real degree-≤6 tower over `ℚ`. -/
theorem neusisPoint_inDeg6Tower {p : Point} (hp : NeusisPoint p) :
    ∃ K : Subfield ℝ, InDeg6Tower K ∧ p.1 ∈ K ∧ p.2 ∈ K := by
  induction hp with
  | base0 => exact ⟨⊥, InDeg6Tower.base, Subfield.zero_mem _, Subfield.zero_mem _⟩
  | base1 => exact ⟨⊥, InDeg6Tower.base, Subfield.one_mem _, Subfield.zero_mem _⟩
  | @inter_ll A₁ B₁ A₂ B₂ X _ _ _ _ _ _ hnonpar h₁ h₂ ihA₁ ihB₁ ihA₂ ihB₂ =>
    rcases ihA₁ with ⟨K₁, hK₁, hA1x, hA1y⟩
    rcases ihB₁ with ⟨K₂, hK₂, hB1x, hB1y⟩
    rcases ihA₂ with ⟨K₃, hK₃, hA2x, hA2y⟩
    rcases ihB₂ with ⟨K₄, hK₄, hB2x, hB2y⟩
    let K := (K₁ ⊔ K₂) ⊔ (K₃ ⊔ K₄)
    have hK : InDeg6Tower K := inDeg6Tower_sup (inDeg6Tower_sup hK₁ hK₂) (inDeg6Tower_sup hK₃ hK₄)
    have m1 : K₁ ≤ K := le_sup_left.trans le_sup_left
    have m2 : K₂ ≤ K := le_sup_right.trans le_sup_left
    have m3 : K₃ ≤ K := le_sup_left.trans le_sup_right
    have m4 : K₄ ≤ K := le_sup_right.trans le_sup_right
    let Δ := (B₁.1 - A₁.1) * (B₂.2 - A₂.2) - (B₁.2 - A₁.2) * (B₂.1 - A₂.1)
    have hΔ0 : Δ ≠ 0 := sub_ne_zero.mpr hnonpar
    let c₁ := (B₁.2 - A₁.2) * A₁.1 - (B₁.1 - A₁.1) * A₁.2
    let c₂ := (B₂.2 - A₂.2) * A₂.1 - (B₂.1 - A₂.1) * A₂.2
    have hX1 : X.1 = ((B₁.1 - A₁.1) * c₂ - (B₂.1 - A₂.1) * c₁) / Δ := by
      unfold Collinear3 at h₁ h₂
      have hmul : X.1 * Δ = (B₁.1 - A₁.1) * c₂ - (B₂.1 - A₂.1) * c₁ := by
        dsimp [Δ, c₁, c₂]
        linear_combination (B₂.1 - A₂.1) * h₁ - (B₁.1 - A₁.1) * h₂
      exact eq_div_of_mul_eq hΔ0 hmul
    have hX2 : X.2 = ((B₁.2 - A₁.2) * c₂ - (B₂.2 - A₂.2) * c₁) / Δ := by
      unfold Collinear3 at h₁ h₂
      have hmul : X.2 * Δ = (B₁.2 - A₁.2) * c₂ - (B₂.2 - A₂.2) * c₁ := by
        dsimp [Δ, c₁, c₂]
        linear_combination (B₂.2 - A₂.2) * h₁ - (B₁.2 - A₁.2) * h₂
      exact eq_div_of_mul_eq hΔ0 hmul
    have hdx1 : B₁.1 - A₁.1 ∈ K := K.sub_mem (m2 hB1x) (m1 hA1x)
    have hdy1 : B₁.2 - A₁.2 ∈ K := K.sub_mem (m2 hB1y) (m1 hA1y)
    have hdx2 : B₂.1 - A₂.1 ∈ K := K.sub_mem (m4 hB2x) (m3 hA2x)
    have hdy2 : B₂.2 - A₂.2 ∈ K := K.sub_mem (m4 hB2y) (m3 hA2y)
    have hΔK : Δ ∈ K := K.sub_mem (K.mul_mem hdx1 hdy2) (K.mul_mem hdy1 hdx2)
    have hc1K : c₁ ∈ K := K.sub_mem (K.mul_mem hdy1 (m1 hA1x)) (K.mul_mem hdx1 (m1 hA1y))
    have hc2K : c₂ ∈ K := K.sub_mem (K.mul_mem hdy2 (m3 hA2x)) (K.mul_mem hdx2 (m3 hA2y))
    refine ⟨K, hK, ?_, ?_⟩
    · rw [hX1]; exact K.div_mem (K.sub_mem (K.mul_mem hdx1 hc2K) (K.mul_mem hdx2 hc1K)) hΔK
    · rw [hX2]; exact K.div_mem (K.sub_mem (K.mul_mem hdy1 hc2K) (K.mul_mem hdy2 hc1K)) hΔK
  | @inter_lc A B C Q X _ _ hne₁ _ _ _ h₁ h₂ ihA ihB ihC ihQ =>
    rcases ihA with ⟨K₁, hK₁, hAx, hAy⟩
    rcases ihB with ⟨K₂, hK₂, hBx, hBy⟩
    rcases ihC with ⟨K₃, hK₃, hCx, hCy⟩
    rcases ihQ with ⟨K₄, hK₄, hQx, hQy⟩
    let K := (K₁ ⊔ K₂) ⊔ (K₃ ⊔ K₄)
    have hK : InDeg6Tower K := inDeg6Tower_sup (inDeg6Tower_sup hK₁ hK₂) (inDeg6Tower_sup hK₃ hK₄)
    have m1 : K₁ ≤ K := le_sup_left.trans le_sup_left
    have m2 : K₂ ≤ K := le_sup_right.trans le_sup_left
    have m3 : K₃ ≤ K := le_sup_left.trans le_sup_right
    have m4 : K₄ ≤ K := le_sup_right.trans le_sup_right
    rcases inter_lc_inDeg6Tower hK ⟨m1 hAx, m1 hAy⟩ ⟨m2 hBx, m2 hBy⟩ hne₁
        ⟨m3 hCx, m3 hCy⟩ ⟨m4 hQx, m4 hQy⟩ h₁ h₂ with ⟨K', hK', _, hX1, hX2⟩
    exact ⟨K', hK', hX1, hX2⟩
  | @inter_cc C₁ Q₁ C₂ Q₂ X _ _ _ _ _ _ hdiff h₁ h₂ ihC₁ ihQ₁ ihC₂ ihQ₂ =>
    rcases ihC₁ with ⟨K₁, hK₁, hC1x, hC1y⟩
    rcases ihQ₁ with ⟨K₂, hK₂, hQ1x, hQ1y⟩
    rcases ihC₂ with ⟨K₃, hK₃, hC2x, hC2y⟩
    rcases ihQ₂ with ⟨K₄, hK₄, hQ2x, hQ2y⟩
    let K := (K₁ ⊔ K₂) ⊔ (K₃ ⊔ K₄)
    have hK : InDeg6Tower K := inDeg6Tower_sup (inDeg6Tower_sup hK₁ hK₂) (inDeg6Tower_sup hK₃ hK₄)
    have m1 : K₁ ≤ K := le_sup_left.trans le_sup_left
    have m2 : K₂ ≤ K := le_sup_right.trans le_sup_left
    have m3 : K₃ ≤ K := le_sup_left.trans le_sup_right
    have m4 : K₄ ≤ K := le_sup_right.trans le_sup_right
    rcases inter_cc_inDeg6Tower hK ⟨m1 hC1x, m1 hC1y⟩ ⟨m2 hQ1x, m2 hQ1y⟩
        ⟨m3 hC2x, m3 hC2y⟩ ⟨m4 hQ2x, m4 hQ2y⟩ hdiff h₁ h₂ with ⟨K', hK', _, hX1, hX2⟩
    exact ⟨K', hK', hX1, hX2⟩
  | @neusis_left P X Y γ₁ γ₂ _ _ _ _ _ hfin hsol ihP ih11 ih12 ih21 ih22 =>
    rcases ihP with ⟨KP, hKP, hPx, hPy⟩
    rcases ih11 with ⟨K11, hK11, h11x, h11y⟩
    rcases ih12 with ⟨K12, hK12, h12x, h12y⟩
    rcases ih21 with ⟨K21, hK21, h21x, h21y⟩
    rcases ih22 with ⟨K22, hK22, h22x, h22y⟩
    let K := KP ⊔ ((K11 ⊔ K12) ⊔ (K21 ⊔ K22))
    have hK : InDeg6Tower K :=
      inDeg6Tower_sup hKP (inDeg6Tower_sup (inDeg6Tower_sup hK11 hK12) (inDeg6Tower_sup hK21 hK22))
    have mP : KP ≤ K := le_sup_left
    have m11 : K11 ≤ K := (le_sup_left.trans le_sup_left).trans le_sup_right
    have m12 : K12 ≤ K := (le_sup_right.trans le_sup_left).trans le_sup_right
    have m21 : K21 ≤ K := (le_sup_left.trans le_sup_right).trans le_sup_right
    have m22 : K22 ≤ K := (le_sup_right.trans le_sup_right).trans le_sup_right
    have hc₁ : CurveIn K γ₁ := by
      cases γ₁ <;> exact ⟨m11 h11x, m11 h11y, m12 h12x, m12 h12y⟩
    have hc₂ : CurveIn K γ₂ := by
      cases γ₂ <;> exact ⟨m21 h21x, m21 h21y, m22 h22x, m22 h22y⟩
    rcases neusis_step_inDeg6Tower hK ⟨mP hPx, mP hPy⟩ hc₁ hc₂ hfin hsol with
      ⟨K', hK', _, hX1, hX2, _, _⟩
    exact ⟨K', hK', hX1, hX2⟩
  | @neusis_right P X Y γ₁ γ₂ _ _ _ _ _ hfin hsol ihP ih11 ih12 ih21 ih22 =>
    rcases ihP with ⟨KP, hKP, hPx, hPy⟩
    rcases ih11 with ⟨K11, hK11, h11x, h11y⟩
    rcases ih12 with ⟨K12, hK12, h12x, h12y⟩
    rcases ih21 with ⟨K21, hK21, h21x, h21y⟩
    rcases ih22 with ⟨K22, hK22, h22x, h22y⟩
    let K := KP ⊔ ((K11 ⊔ K12) ⊔ (K21 ⊔ K22))
    have hK : InDeg6Tower K :=
      inDeg6Tower_sup hKP (inDeg6Tower_sup (inDeg6Tower_sup hK11 hK12) (inDeg6Tower_sup hK21 hK22))
    have mP : KP ≤ K := le_sup_left
    have m11 : K11 ≤ K := (le_sup_left.trans le_sup_left).trans le_sup_right
    have m12 : K12 ≤ K := (le_sup_right.trans le_sup_left).trans le_sup_right
    have m21 : K21 ≤ K := (le_sup_left.trans le_sup_right).trans le_sup_right
    have m22 : K22 ≤ K := (le_sup_right.trans le_sup_right).trans le_sup_right
    have hc₁ : CurveIn K γ₁ := by
      cases γ₁ <;> exact ⟨m11 h11x, m11 h11y, m12 h12x, m12 h12y⟩
    have hc₂ : CurveIn K γ₂ := by
      cases γ₂ <;> exact ⟨m21 h21x, m21 h21y, m22 h22x, m22 h22y⟩
    rcases neusis_step_inDeg6Tower hK ⟨mP hPx, mP hPy⟩ hc₁ hc₂ hfin hsol with
      ⟨K', hK', _, _, _, hY1, hY2⟩
    exact ⟨K', hK', hY1, hY2⟩

/-- **Baragar's Necessity Theorem for real numbers**:
Every neusis-constructible real number lies in a real degree-≤6 tower over `ℚ`. -/
theorem neusisReal_inDeg6Tower {x : ℝ} (hx : NeusisReal x) : RealInDeg6Tower x := by
  rcases neusisPoint_inDeg6Tower hx with ⟨K, hK, hxK, _⟩
  exact ⟨K, hK, hxK⟩

end Neusis
