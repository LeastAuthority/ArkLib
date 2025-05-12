import ArkLib.Data.CodingTheory.RelativeHammingDistance

/-!
List‑decodability of a linear code via relative Hamming distance.
-/-

variable {ι : Type*} [Fintype ι]
         {F : Type*} [Semiring F]

namespace ListDecodeability

/--
The set of codewords in the linear code `LC` within relative Hamming
distance `δ` of a received word `f : ι → F`.
-/
def list (LC : LinearCode ι F) (f : ι → F) (δ : ℚ) : Set (ι → F) :=
  { c | c ∈ LC ∧ δᵣ(c, f) ≤ δ }

/--
A linear code `LC` is `(δ, ℓ)`–list decodable if every received word `f`
has at most `ℓ` codewords within relative Hamming distance `δ`.
We convert our `Set` to a `Finset` and compare `.card` against `ℓ`.
-/
def listDecodable (LC : LinearCode ι F) (δ : ℚ) (ℓ : ℕ) : Prop :=
  ∀ f : ι → F, (list LC f δ).toFinset.card ≤ ℓ

end ListDecodeability
