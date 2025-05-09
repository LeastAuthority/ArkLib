import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Groebner

/-! Univariate polynomials of degree < 2ᵐ can be writen as degree wise linear
    m-variate polynomials by
    ∑ aᵢ Xⁱ → ∑ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))` -/


/- Given integers `m` and `i` this computes monomial exponents
   ( σ(0), ..., σ(m-1) ) = ( bit₀(i), ..., bitₘ₋₁(i) )
   such that we can do X_0^σ(0)⬝  ⋯  ⬝ X_(m-1)^σ(m-1).
   For i ≥ 2ᵐ this is the bit reprsentation of (i mod 2ᵐ) -/
noncomputable def bitExpo
 (m i : ℕ ): (Fin m) →₀ ℕ :=
      Finsupp.onFinset Finset.univ
        (fun j => if Nat.testBit i j.1 then 1 else 0)
        (by intro j hj; simpa using hj)

/-- `linMvExt m p` rewrites the univariate polynomial `p : F^(<2^m)[X]`
     as a degree wise linear multivariate polynomial in the variables
     `X₀ … Xₘ₋₁`, sending `aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`,
     where `bitⱼ(i)` is the `j`-th binary digit of `i`. -/
noncomputable def linMvExt {F : Type*} [Field F]
  (m : ℕ)
  (p : Polynomial F) (_hp : p.degree < (2 ^ m)) : MvPolynomial (Fin m) F :=
    (p : Polynomial F).sum fun i a =>
      -- aᵢ Xⁱ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
      MvPolynomial.monomial (bitExpo m i)  a


/- x → (x^(2⁰),x^(2¹),...,x^(2⁽ᵐ⁻¹⁾) -/
noncomputable def pow {F : Type*} [Field F] (m : ℕ) : Fin m → Polynomial F :=
  fun j : Fin m => (Polynomial.X : Polynomial F) ^ (2 ^ (j : ℕ))

/- Maps m-variate polynomials onto an univariate polynomial by
   invLinMvExt[p](x) := p(x^(2⁰),x^(2¹),...,x^(2⁽ᵐ⁻¹⁾))  -/
noncomputable def leftInvLinMvExt  {F : Type*} [Field F]
  {m : ℕ} (p: MvPolynomial (Fin m) F) : Polynomial F :=
    (MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (pow m) p
    )

/- For an univariate polynomial of degree < 2ᵐ, leftInvLinMvExt is a left inverse to
   linMvExt -/
lemma is_left_inverse
    {F : Type*} [Field F] {m : ℕ}
    (p : Polynomial F) (hp : p.degree < (2 ^ m)) :
      leftInvLinMvExt (linMvExt m p hp) = p := by sorry
