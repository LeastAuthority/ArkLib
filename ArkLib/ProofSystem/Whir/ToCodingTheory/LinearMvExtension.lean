import ArkLib.Data.CodingTheory.Basic

/-! Univariate polynomials of degree < 2ᵐ can be writen as degree wise linear
    m-variate polynomials by
    ∑ aᵢ Xⁱ → ∑ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))` -/

namespace LinearMvExtension

variable {F : Type*} [CommSemiring F] {m : ℕ}

/- Given integers `m` and `i` this computes monomial exponents
   ( σ(0), ..., σ(m-1) ) = ( bit₀(i), ..., bitₘ₋₁(i) )
   such that we can do X_0^σ(0)⬝  ⋯  ⬝ X_(m-1)^σ(m-1).
   For i ≥ 2ᵐ this is the bit reprsentation of (i mod 2ᵐ) -/
noncomputable def bitExpo (i : ℕ ): (Fin m) →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun j => if Nat.testBit i j.1 then 1 else 0)
    (by intro j hj; simpa using hj)

/-- The linear map that maps univariate polynomials of degree `< 2ᵐ` onto
    a degree wise linear m-variate polynomial, sending
    `aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`, where `bitⱼ(i)` is the `j`-th binary digit of `i`. -/
noncomputable def linearMvExtension:
    Polynomial.degreeLT F (2 ^ m) →ₗ[F] MvPolynomial (Fin m) F where
  -- p(X) = aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
  toFun p := (p : Polynomial F).sum fun i a =>
    MvPolynomial.monomial (bitExpo i)  a
  map_add' := by
    rintro p q
    simp [Polynomial.sum_add_index]
  map_smul' := by
    rintro c p
    simp [Polynomial.sum_smul_index]
    sorry

/-- the linearized m-variate polynomial -/
noncomputable def linearMvExtended
  (p : Polynomial.degreeLT F (2 ^ m)) : MvPolynomial (Fin m) F :=
    linearMvExtension.toFun p


/- X → (X^(2⁰),X^(2¹),...,X^(2⁽ᵐ⁻¹⁾) -/
noncomputable def pow : Fin m → Polynomial F :=
  fun j : Fin m => (Polynomial.X : Polynomial F) ^ (2 ^ (j : ℕ))

/- For an univariate polynomial of degree < 2ᵐ, we have
   linearMvExtension[p](X^(2⁰),X^(2¹),...,X^(2⁽ᵐ⁻¹⁾) = p(X)-/
lemma pow_is_right_inverse (p : Polynomial.degreeLT F (2 ^ m)) :
  MvPolynomial.eval₂
    (Polynomial.C : F →+* Polynomial F)
    pow
    (linearMvExtended p)
  = (p : Polynomial F) := sorry


end LinearMvExtension
