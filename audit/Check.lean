import NeusisLean

/-! Reproduce the axiom audit and test the public theorems against concrete geometric claims. -/

open Neusis Polynomial

#print axioms Neusis.neusisPoint_inDeg6Tower
#print axioms Neusis.neusisReal_of_circleCircleValid
#print axioms Neusis.neusisReal_angle_quintisection
#print axioms Neusis.regularPolygonConstructible_25
#print axioms Neusis.neusisReal_of_poly_le6
#print axioms Neusis.neusisReal_iff_inDeg6Tower
#print axioms Neusis.neusisComplex_iff
#print axioms Neusis.regularPolygonConstructible_iff
#print axioms Neusis.neusisReal_of_real_sextic
#print axioms Neusis.neusisComplex_of_real_quintic

namespace NeusisAudit

/-- A common multiple of the six totients gives a short certificate for these examples. -/
private theorem polygonOfTotientDvd600 (n : ℕ) (hn : 3 ≤ n) (h : n.totient ∣ 600) :
    RegularPolygonConstructible n := by
  apply (regularPolygonConstructible_iff hn).2
  intro p hp hd
  have hprod : p ∣ (2 ^ 3 * 3) * 5 ^ 2 := hd.trans h
  rcases hp.dvd_mul.mp hprod with h23 | h5
  · rcases hp.dvd_mul.mp h23 with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  · exact Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h5)

example : RegularPolygonConstructible 25 := polygonOfTotientDvd600 25 (by decide) (by decide)
example : RegularPolygonConstructible 31 := polygonOfTotientDvd600 31 (by decide) (by decide)
example : RegularPolygonConstructible 41 := polygonOfTotientDvd600 41 (by decide) (by decide)
example : RegularPolygonConstructible 61 := polygonOfTotientDvd600 61 (by decide) (by decide)
example : RegularPolygonConstructible 101 := polygonOfTotientDvd600 101 (by decide) (by decide)
example : RegularPolygonConstructible 125 := polygonOfTotientDvd600 125 (by decide) (by decide)

example : ¬ RegularPolygonConstructible 23 := by
  intro h
  have := (regularPolygonConstructible_iff (n := 23) (by decide)).1 h 11
    (by decide) (by decide)
  omega

/-- The specific fifth root asked about by Benjamin and Snyder in 2016. -/
theorem fifthRootTwo : NeusisReal ((2 : ℝ) ^ (1 / 5 : ℝ)) := by
  let P : Polynomial NeusisSubfield := X ^ 5 - C 2
  have hdeg : P.natDegree = 5 := natDegree_X_pow_sub_C 2
  refine neusisReal_of_real_sextic P ?_ (by omega) ?_
  · intro h
    simp [h] at hdeg
  · have hpow : ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    dsimp only [P]
    rw [map_sub, map_pow, aeval_X, aeval_C, hpow, map_ofNat, sub_self]

/-- A complex root of the real quintic X^5 - X - 1, with no reality hypothesis on z. -/
example (z : ℂ) (hz : z ^ 5 - z - 1 = 0) : NeusisComplex z := by
  let P : Polynomial NeusisSubfield := X ^ 5 - (X + C 1)
  have hdeg : P.natDegree = 5 := by
    dsimp only [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_add_C, natDegree_X_pow]
    decide
  refine neusisComplex_of_real_quintic P ?_ (by omega) ?_
  · intro h
    simp [h] at hdeg
  · simpa [P, sub_add_eq_sub_sub] using hz

end NeusisAudit
