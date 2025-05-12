/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.ReedSolomon

namespace SmoothDomain

open Finset

variable {F : Type*} [Semiring F] {n : ℕ} {domain : Fin n ↪ F}

/-- A finite subset `L : Finset F` of a field `F` is smooth if
    1. its cardinality is a power of two, and
    2. it is a coset `a • H` of some subgroup `H ≤ Fˣ` in the group
       of invertibles .
-/
def smoothSubset (L : Finset F) : Prop :=
  ∃ (H : Subgroup (Units F)) (a : Units F) (k : ℕ),
    (L : Set F) = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F)) ∧
    L.card = 2 ^ k

def smoothDomain [DecidableEq F] (domain : Fin n ↪ F) : Prop :=
  smoothSubset (univ.image domain)

/-- The `k`-th power of `domain`,  `domain^k := { x^k | x ∈ domain }`. -/
def powDomain (domain : Fin n ↪ F) (k : ℕ) : Fin n → F :=
  -- not injective in general
  fun i => (domain i) ^ k


-- TODO: I think there is a proof that m = gcd(k,n) ... I have to think about it
/- The fiber `f⁻¹(y)` for the surjection `f : domain → domain^k, x → x^k` and `y ∈ domain^k` -/
def powFiber {domain : Fin n ↪ F} {k : ℕ} {m:ℕ } : Fin m → F := sorry

end SmoothDomain
