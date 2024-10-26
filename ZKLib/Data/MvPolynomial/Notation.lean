/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
  # Notation for Multivariate Polynomials
    We define notation `R[X σ]` to be `MvPolynomial σ R`.

    For a Finset `s` and a natural number `n`, we also define `s ^ᶠ n` to be
    `Fintype.piFinset (fun (_ : Fin n) => s)`. This matches the intuition that `s ^ᶠ n`
    is the set of all tuples of length `n` with elements in `s`.
-/

open MvPolynomial

@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃< " d "⦄[X]" => Polynomial.degreeLT R d
@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃≤ " d "⦄[X]" => Polynomial.degreeLE R d

@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial σ R
@[inherit_doc] scoped[MvPolynomial] notation:9000
  R "⦃≤ " d "⦄[X " σ "]"  => MvPolynomial.restrictDegree σ R d

-- `𝔽⦃≤ 1⦄[X Fin n]` is the set of multilinear polynomials in `n` variables over `𝔽`.

notation:20 set "^ᶠ" pow => Fintype.piFinset (fun (_ : Fin pow) => set)
