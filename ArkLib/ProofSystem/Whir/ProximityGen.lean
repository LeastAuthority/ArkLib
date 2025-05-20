/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.Probability.Notation

namespace Generator

variable  {F : Type*} [Semiring F] [Fintype F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [Nonempty ι]

/-- For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → 𝔽ˡ`and linear
    code `C` the predicate `linear_comb_in_distance(r)` is true, if the linear
    combination f := ∑ⱼ GenFun(r)ⱼ⬝fⱼ is within relative Hamming distance `δ` to the linear
    code `C`.  -/
def linear_comb_in_distance
  {l : ℕ}
  (f : Fin l → ι → F)
  (δ : ℝ )
  (GenFun : F → Fin l → F)
  (C : LinearCode ι F): F → Prop
    | r => δᵣ( (fun x => ∑ j : Fin l, (GenFun r j) • f j x) , C ) ≤ δ


/-- A proximity generator for a linear code `C`  -/
structure ProximityGenerator
  (F : Type*) [Semiring F] [Fintype F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [Nonempty ι] where
  -- Underlying linear code
  C         : LinearCode ι F
  -- Number of functions to combine
  l         : ℕ
  -- Generator function maps sampled randomness `r : 𝔽 ` to `l`-tuples of field elements
  GenFun    : F → Fin l → F
  -- Distance threshold parameter
  BStar     : ℝ
  -- Error function bounding the probability of hitting within distance `δ`
  err       : ℝ → ENNReal
  /- Proximity:
      For all `l`-tuples of functions `fᵢ : ι → 𝔽` and distance parameter `δ ∈ (0, 1-BStar)`:

      If the probability that `linear_comb_in_distance(r)` is true for uniformly random
      sampled  `r ← 𝔽 ` exceeds `err(δ)`, then there exists a  subset `S ⊆ ι ` of size
      `|S| ≥ (1-δ)⬝|ι|`) on which each `fᵢ` agrees with some codeword in `C`. -/
  proximity:
    ∀ (f : Fin l → ι → F)
      (δ : NNReal)
      (_hδ : δ < 1 - BStar) ,
      Pr_{r ← F}[ (linear_comb_in_distance f δ GenFun C) r ] > err δ →
        ∃ S : Finset ι,
          S.card ≥ (1 - (δ : ℝ)) * Fintype.card ι ∧
          ∀ i : Fin l, ∃ u ∈ C, ∀ x ∈ S, f i x = u x

end Generator
