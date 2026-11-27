module

public import Lib.Adelic.Unitary.Defs
public import Lib.General.LinearAlgebra.IntegralLattices
import Lib.Adelic.Adeles.IdeleModulus
import Lib.General.LinearAlgebra.HermiteForm
import Lib.General.LinearAlgebra.UnitaryColumnReduction
import Lib.General.LinearAlgebra.WeightedColumnReduction

/-!
# Normalisation of adelic frames

A rectangular matrix with at most as many columns as rows factors into a frame that is
orthonormal at infinity and primitive at the finite places, times a block triangular matrix.
When the original matrix has a left inverse, the triangular factor is invertible.
-/

@[expose] public section

noncomputable section

open Matrix NumberField

namespace New

variable {E : Type*} [Field E] [NumberField E] {n k : Type*}
  [Fintype n] [Fintype k] [DecidableEq k]

/-- The columns are orthonormal at each infinite place. At the finite places both the matrix and
a left inverse have integral entries. -/
structure IsNormalizedAdelicFrame (X : Matrix n k (𝔸 E)) : Prop where
  orthonormal (w : InfinitePlace E) : (X.map (evalInf w))ᴴ * X.map (evalInf w) = 1
  primitive : IsPrimitiveMatrix (Ô E) (X.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)))

/-- If there are at least as many rows as columns, an arbitrary rectangular adelic matrix is
a normalised frame times a block upper triangular matrix. The triangular factor may be singular. -/
theorem exists_normalizedFrame_mul_blockTriangular [DecidableEq n] {α : Type*} [LinearOrder α]
    (X : Matrix n k (𝔸 E)) (hk : Fintype.card k ≤ Fintype.card n) (wt : k → α) :
    ∃ Q : Matrix n k (𝔸 E), IsNormalizedAdelicFrame Q ∧
      ∃ D : Matrix k k (𝔸 E), D.BlockTriangular wt ∧ X = Q * D := by
  obtain ⟨ι⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  let fin := RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)
  choose u hu r hr harch _ using fun w : InfinitePlace E ↦
    exists_unitary_blockTriangular_factor ι (X.map (evalInf w)) wt
  obtain ⟨v, hv, t, ht, hfinite, -⟩ := exists_blockTriangular_factor_of_clear_col _
    isValuationPair_Ô.exists_clear_col ι (X.map fin) wt
  let Q := (mkAdelicGL (u, v)).val.submatrix id ι
  let D : Matrix k k (𝔸 E) := of fun i j ↦ (fun w ↦ r w i j, t i j)
  refine ⟨Q, ⟨fun w ↦ ?_, ?_⟩, D, fun i j hij ↦ Prod.ext (funext fun w ↦ hr w hij) (ht hij),
    matrix_ext_𝔸 (fun w ↦ ?_) ?_⟩
  · change ((u w).val.submatrix id ι)ᴴ * (u w).val.submatrix id ι = 1
    have hgram : (u w).valᴴ * (u w).val = 1 := by
      simpa [mem_unitaryGroupOf_iff, star_eq_conjTranspose] using hu w
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id, hgram,
      submatrix_one_embedding]
  · obtain ⟨hv₁, hv₂⟩ := mem_intGL.mp hv
    refine ⟨fun i j ↦ hv₁ i (ι j), v.inv.submatrix ι id, fun i j ↦ hv₂ (ι i) j, ?_⟩
    change v.inv.submatrix ι id * v.val.submatrix id ι = 1
    rw [← submatrix_mul _ _ _ id _ Function.bijective_id, v.inv_val, submatrix_one_embedding]
  · rw [Matrix.map_mul]
    exact harch w
  · rw [Matrix.map_mul]
    exact hfinite

/-- The columns of a left-invertible adelic frame can be normalised by a block upper triangular
change of basis for any linearly ordered column weights. -/
theorem exists_blockTriangular_normalizedFrame [DecidableEq n] {X : Matrix n k (𝔸 E)}
    (hX : HasLeftInv X) {α : Type*} [LinearOrder α] (wt : k → α) :
    ∃ b : GL k (𝔸 E), b.val.BlockTriangular wt ∧ IsNormalizedAdelicFrame (X * b.val) := by
  obtain ⟨L, hL⟩ := hX
  obtain ⟨Q, hQ, D, hD, hfac⟩ := exists_normalizedFrame_mul_blockTriangular X
    (card_le_of_surjective (𝔸 E) L.mulVecLin fun v ↦ ⟨X *ᵥ v, by simp [hL]⟩) wt
  obtain ⟨b, hb, hcols⟩ := exists_blockTriangular_change_of_factor hL hD hfac
  exact ⟨b, hb, hcols ▸ hQ⟩

end New
