import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

namespace Aux

variable {F: Type} [Field F]

protected lemma eq_poly_deg_one {a b c d : F} {x₁ x₂ : F}
  (h1 : a + b * x₁ = c + d * x₁)
  (h2 : a + b * x₂ = c + d * x₂)
  (h1_2 : x₁ ≠ x₂):
  Polynomial.C a + Polynomial.C b * Polynomial.X 
    = Polynomial.C c + Polynomial.C d * Polynomial.X := by
  by_cases h_b_d : b = d
  · aesop
  · exact absurd
            (by apply mul_left_cancel₀ (sub_ne_zero_of_ne (show d ≠ b by aesop))
                linear_combination -(1 * h1) + h2)
            h1_2

end Aux
