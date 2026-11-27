module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Lib.General.LinearAlgebra.WeightedColumnReduction
import TauCeti.Analysis.Matrix.GramFactorization.Uniqueness

/-!
# Weighted QR factorization

A unitary row operation concentrates the part of a column on a set of coordinates into its
pivot. Together with weighted column reduction this gives a QR factorization with prescribed
pivot rows, including for rank-deficient matrices.
-/

@[expose] public section

noncomputable section

namespace New

open Matrix Finset WithLp
open scoped InnerProductSpace

variable {𝕜 n k : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A unitary transformation can send `X` to `Z` while fixing the columns of `B` if the two
families have the same Gram matrix and the same inner products with those columns. -/
private lemma exists_unitary_mul_fix_of_gram {ι : Type*} {X Z : Matrix n ι 𝕜} {B : Matrix n k 𝕜}
    (hgram : Xᴴ * X = Zᴴ * Z) (hcross : Xᴴ * B = Zᴴ * B) :
    ∃ W ∈ unitaryGroupOf (1 : Matrix n n 𝕜), W.val * X = Z ∧ W.val * B = B := by
  have hBX : Bᴴ * X = Bᴴ * Z := by simpa using congrArg conjTranspose hcross
  have h : (fromCols X B)ᴴ * fromCols X B = (fromCols Z B)ᴴ * fromCols Z B := by
    simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, hgram, hcross, hBX]
  obtain ⟨u, hu⟩ := TauCeti.conjTranspose_mul_self_eq_iff_exists_unitary_mul.mp h
  rw [mul_fromCols, fromCols_inj.eq_iff] at hu
  exact ⟨Unitary.toUnits u, mem_unitaryGroupOf_iff.mpr (by
    simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp u.property), hu.1.symm, hu.2.symm⟩

private lemma exists_unitary_clear_col (Y : Matrix n k 𝕜) (a : k) {p : n} {t : Finset n}
    (hp : p ∉ t) :
    ∃ W ∈ unitaryGroupOf (1 : Matrix n n 𝕜), (∀ i ∈ t, (W.val * Y) i a = 0) ∧
      ∀ j : k, Y p j = 0 → (∀ i ∈ t, Y i j = 0) → ∀ r : n, (W.val * Y) r j = Y r j := by
  classical
  -- Project onto the coordinates of the pivot and the rows to be cleared.
  let s := insert p t
  let x : n → 𝕜 := fun i ↦ if i ∈ s then Y i a else 0
  let z : n → 𝕜 := Pi.single p (‖toLp 2 x‖ : 𝕜)
  -- The columns of B are the complementary projections, which the row operation fixes.
  let B : Matrix n k 𝕜 := fun i j ↦ if i ∈ s then 0 else Y i j
  let X := replicateCol Unit x
  let Z := replicateCol Unit z
  have hxz : Xᴴ * X = Zᴴ * Z := by
    ext i j
    change star x ⬝ᵥ x = star z ⬝ᵥ z
    rw [dotProduct_comm (star x) x, ← EuclideanSpace.inner_toLp_toLp,
      inner_self_eq_norm_sq_to_K]
    simp [z, dotProduct_single, sq, RCLike.star_def]
  have cross (v : n → 𝕜) (hv : ∀ i ∉ s, v i = 0) : (replicateCol Unit v)ᴴ * B = 0 := by
    ext i j
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r ∈ s <;> simp [B, hr, hv, conjTranspose_apply]
  have hX : Xᴴ * B = 0 := cross x (fun i hi ↦ by simp [x, hi])
  have hZ : Zᴴ * B = 0 := cross z (by
    intro i hi
    have hne : i ≠ p := by
      rintro rfl
      exact hi (mem_insert_self ..)
    simp [z, Pi.single_eq_of_ne hne])
  obtain ⟨W, hW, hWX, hWB⟩ := exists_unitary_mul_fix_of_gram hxz (hX.trans hZ.symm)
  have hx : W.val *ᵥ x = z := congrArg (fun M ↦ Matrix.col M ()) hWX
  have hB (j : k) : W.val *ᵥ B.col j = B.col j := congrArg (fun M ↦ Matrix.col M j) hWB
  have outside (i : n) (j : k) : B.col j i = (if i ∈ s then 0 else Y i j) := rfl
  refine ⟨W, hW, ?_, ?_⟩
  · have hcol : Y.col a = x + B.col a := by
      funext i
      change Y i a = x i + B.col a i
      rw [outside]
      by_cases hi : i ∈ s <;> simp [x, hi]
    intro i hi
    change (W.val *ᵥ Y.col a) i = 0
    rw [hcol, mulVec_add, hx, hB]
    have hip : i ≠ p := ne_of_mem_of_not_mem hi hp
    change z i + B.col a i = 0
    rw [outside]
    simp [z, s, hi, Pi.single_eq_of_ne hip]
  · intro j hj hjt r
    have hcol : Y.col j = B.col j := by
      funext i
      change Y i j = B.col j i
      rw [outside]
      split_ifs with hi
      · obtain rfl | ht := Finset.mem_insert.mp hi
        · exact hj
        · exact hjt i ht
      · rfl
    change (W.val *ᵥ Y.col j) r = Y.col j r
    rw [hcol, hB]

/-- Weighted QR factorization over the real or complex numbers, with prescribed distinct pivot
rows. The triangular factor consists of those rows of the matrix in the new unitary coordinates. -/
theorem exists_unitary_blockTriangular_factor [Fintype k] {α : Type*} [LinearOrder α]
    (ι : k ↪ n) (Y : Matrix n k 𝕜) (wt : k → α) :
    ∃ U ∈ unitaryGroupOf (1 : Matrix n n 𝕜), ∃ D : Matrix k k 𝕜, D.BlockTriangular wt ∧
      Y = U.val.submatrix id ι * D ∧ U⁻¹.val.submatrix ι id * Y = D :=
  exists_blockTriangular_factor_of_clear_col _ exists_unitary_clear_col ι Y wt

end New
