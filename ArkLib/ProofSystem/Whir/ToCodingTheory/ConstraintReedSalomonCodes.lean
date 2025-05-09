import ArkLib.ProofSystem.Whir.ToCodingTheory.SmoothReedSolomonCodes

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {L : Finset F} {m : ℕ}

/-- The boolens `{0,1}` sitting inside any field `F`. -/
def boolF
  {F : Type*} [Field F] [DecidableEq F] : Finset F := {0, 1}

/-- The binary `m`‐dimensional cube `{0,1}^m` as a `Finset (Fin m → F)`. -/
def hypercube
  {F : Type*} [Field F] [DecidableEq F]
  (m : ℕ) : Finset (Fin m → F) := Fintype.piFinset fun _ => boolF

-- Now you can sum a polynomial `p : MvPolynomial (Fin m) F` over the cube:
example
  (F : Type*) [Field F] [DecidableEq F]
  (m : ℕ) (p : MvPolynomial (Fin m) F) : F :=
  ∑ x in hypercube m, MvPolynomial.eval x p


/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  {F : Type*} [Field F] {m : ℕ}
  (p : MvPolynomial (Fin m) F) (b : Fin m → F) : Fin (m+1) → F
| ⟨0, _⟩       => MvPolynomial.eval b p
| ⟨j+1, hj⟩   => b ⟨j, by simpa using hj⟩

/- THIS IS ANOYING WE NEED A BETTER DEF OF RSC-/
abbrev SmoothReedSolomonCode.codeWord
  (C : SmoothReedSolomonCode F L m) : Type _ :=
{ f // f ∈ C.code }

/-- Predicate expressing the weight constraint on a codeword `f`. -/
def constraint_pred
  (C : SmoothReedSolomonCode F L m)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F)
  (cw : C.codeWord) : Prop :=
let p := C.mVpoly cw
∑ b in hypercube m, w.eval (toWeightAssignment p b) = σ

/-- Constrained Reed–Solomon code as a structure, bundling the underlying code and the weight constraint. -/
structure ConstrainedReedSolomonCode
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F) (m : ℕ)
  (w : MvPolynomial (Fin (m+1)) F) (σ : F)
  extends SmoothReedSolomonCode F L m where
/-- Every codeword satisfies the weight constraint. -/
constrained : ∀ cw : toSmoothReedSolomonCode.codeWord,
  constraint_pred toSmoothReedSolomonCode w σ cw
