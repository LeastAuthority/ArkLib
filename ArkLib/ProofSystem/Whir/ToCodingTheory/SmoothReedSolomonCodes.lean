import  ArkLib.ProofSystem.Whir.ToCodingTheory.ReedSolomonCodes
import  ArkLib.ProofSystem.Whir.ToCodingTheory.SmoothDom
import  ArkLib.ProofSystem.Whir.ToCodingTheory.LinearMvExtension

structure SmoothReedSolomonCode
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (L : Finset F) (m : ℕ) extends ReedSolomonCode F L (2^m) where
      /-- `L` is a smooth evaluation domain (a 2‑power coset). -/
      smooth_L  : smoothDom L

namespace SmoothReedSolomonCode


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {L : Finset F} {m : ℕ}

noncomputable def mVpoly (C : SmoothReedSolomonCode F L m) (f : C.code) :
    MvPolynomial (Fin m) F :=
  -- Step 1: the univariate interpolation polynomial
  let p : Polynomial F := C.toReedSolomonCode.poly f
  -- proof that it is of degree < 2^m
  have hp : p.degree < (2 ^ m) := by sorry
  -- Step 2: lift to an m‑variate polynomial
  linMvExt m p hp

end SmoothReedSolomonCode
