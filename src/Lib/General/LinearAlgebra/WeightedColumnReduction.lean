module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Finset.Max

/-!
# Weighted triangular reduction by clearing one column

The allowed row operations form a subgroup of the general linear group. To triangularize a
rectangular matrix, it suffices to clear a set of rows in one column while fixing each column
that vanishes on those rows and on the pivot. The pivot rows can be prescribed.
-/

@[expose] public section

namespace New

open Matrix Finset

variable {A n k α : Type*} [CommRing A] [Fintype n] [DecidableEq n] [Fintype k] [LinearOrder α]

/-- Factor a rectangular matrix as the selected columns of a group element times a block upper
triangular matrix. The hypothesis clears the rows `t` of column `a` using a pivot outside `t`,
without changing columns that vanish both on `t` and at the pivot. -/
theorem exists_blockTriangular_factor_of_clear_col (G : Subgroup (GL n A))
    (clear : ∀ (Y : Matrix n k A) (a : k) {i₀ : n} {t : Finset n}, i₀ ∉ t →
      ∃ W ∈ G, (∀ i ∈ t, (W.val * Y) i a = 0) ∧
        ∀ j : k, Y i₀ j = 0 → (∀ i ∈ t, Y i j = 0) → ∀ r : n, (W.val * Y) r j = Y r j)
    (ι : k ↪ n) (y : Matrix n k A) (wt : k → α) :
    ∃ U ∈ G, ∃ D : Matrix k k A, D.BlockTriangular wt ∧
      y = U.val.submatrix id ι * D ∧ U⁻¹.val.submatrix ι id * y = D := by
  classical
  -- Treat the columns in order of increasing weight. In each column `j ∈ s` of a reduced `U * y`,
  -- only the rows `ι b` with `b ∈ s` and `wt b ≤ wt j` may be non-zero.
  let IsReduced (s : Finset k) (U : GL n A) : Prop :=
    ∀ j ∈ s, ∀ i : n, (∀ b ∈ s, i = ι b → wt j < wt b) → (U.val * y) i j = 0
  have exists_reduced (s : Finset k) : ∃ U ∈ G, IsReduced s U := by
    induction s using Finset.induction_on_max_value wt with
    | empty => exact ⟨1, one_mem _, by simp [IsReduced]⟩
    | insert a s ha hmax ih =>
      obtain ⟨U, hU, hs⟩ := ih
      -- in the new column `a`, clear the rows outside `ι (insert a s)`
      obtain ⟨W, hW, hcol, hkeep⟩ := clear (U.val * y) a (i₀ := ι a)
        (t := ((insert a s).map ι)ᶜ) (by simp)
      -- these rows and `ι a` vanish in the columns of `s`, so these columns do not change
      have s_cols : ∀ j ∈ s, ∀ r : n, (W.1 * (U.1 * y)) r j = (U.1 * y) r j := by grind [mem_compl]
      refine ⟨W * U, mul_mem hW hU, fun j hj r hr ↦ ?_⟩
      rw [Units.val_mul, Matrix.mul_assoc]
      obtain rfl | hjs := mem_insert.1 hj
      · -- as `wt j` is maximal, `r` is not in `ι (insert j s)`
        exact hcol r (by grind [mem_compl])
      · exact (s_cols j hjs r).trans (hs j hjs r (by grind))
  obtain ⟨U, hU, hzero⟩ := exists_reduced univ
  refine ⟨U⁻¹, inv_mem hU, (U.val * y).submatrix ι id,
    fun i j hij ↦ hzero j (mem_univ j) (ι i) (by simpa), ?_, rfl⟩
  -- only the rows at `ι` of `U * y` contribute to the product `y = U⁻¹ * (U * y)`
  have hrows (i : n) (hi : i ∉ Set.range ι) (j : k) : (U.val * y) i j = 0 :=
    hzero j (mem_univ j) i (by tauto)
  calc y = U⁻¹.val * (U.val * y) := by simp [← Matrix.mul_assoc]
    _ = U⁻¹.val.submatrix id ι * (U.val * y).submatrix ι id := ext fun i j ↦
      (Fintype.sum_of_injective ι ι.injective _ _ (by simp +contextual [hrows]) fun _ ↦ rfl).symm

omit [DecidableEq n] in
/-- In a triangular factorization of a left-invertible matrix, the triangular factor is a unit.
Its inverse is a block triangular change of basis to the given frame. -/
theorem exists_blockTriangular_change_of_factor [DecidableEq k] {X Q : Matrix n k A}
    {L : Matrix k n A} (hL : L * X = 1) {D : Matrix k k A} {wt : k → α}
    (hD : D.BlockTriangular wt) (hfac : X = Q * D) :
    ∃ b : GL k A, b.val.BlockTriangular wt ∧ X * b.val = Q := by
  obtain ⟨d, rfl⟩ : IsUnit D := .of_mul_eq_one_right (L * Q) (by rwa [Matrix.mul_assoc, ← hfac])
  exact ⟨d⁻¹, by simpa using blockTriangular_inv_of_blockTriangular hD,
    by simp [hfac, Matrix.mul_assoc]⟩

end New
