module

public import Lib.Adelic.Reduction.FrameNormalization
import Lib.Adelic.Unitary.ComponentsAndBlockSums

/-!
# Normalising adelic frames only at the places that need it

A frame over the finite adeles with a left inverse is already primitive away from finitely many
places. A weighted adelic change of basis can normalise it while acting by the identity at every
finite place where it is primitive and every infinite place where it is orthonormal.
-/

@[expose] public section

noncomputable section

namespace New
open Matrix NumberField

variable {E : Type*} [Field E] [NumberField E] {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]

omit [Fintype k] in
/-- A finite adelic frame is primitive exactly when it is primitive at each finite place. -/
theorem isPrimitiveMatrix_iff_forall_evalAt {X : Matrix n k (𝔸f E)} :
    IsPrimitiveMatrix (Ô E) X ↔
      ∀ w : FinPlace E, IsPrimitiveMatrix (LocInt w).toSubring (X.map (evalAt w)) := by
  constructor
  · rintro ⟨hX, L, hL, hLX⟩ w
    refine ⟨fun i j ↦ mem_Ô.mp (hX i j) w, L.map (evalAt w), fun i j ↦ mem_Ô.mp (hL i j) w, ?_⟩
    rw [← Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro h
    choose L hL hLX using fun w ↦ (h w).2
    -- Each chosen left inverse is integral, so its entries assemble into finite adeles.
    let l : Matrix k n (𝔸f E) := fun i j ↦
      ⟨fun w ↦ L w i j, Filter.Eventually.of_forall fun w ↦ hL w i j⟩
    refine ⟨fun i j ↦ mem_Ô.mpr fun w ↦ (h w).1 i j, l,
      fun i j ↦ mem_Ô.mpr fun w ↦ hL w i j, matrix_ext_evalAt fun w ↦ ?_⟩
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hLX w

private lemma eventually_isIntMatrix_evalAt {ι κ : Type*} [Finite ι] [Finite κ]
    (A : Matrix ι κ (𝔸f E)) :
    ∀ᶠ w : FinPlace E in Filter.cofinite, IsIntMatrix (LocInt w).toSubring (A.map (evalAt w)) := by
  simp only [IsIntMatrix, Filter.eventually_all]
  exact fun i j ↦ (A i j).property

/-- A frame with a finite adelic left inverse is primitive at all but finitely many places. -/
theorem HasLeftInv.eventually_isPrimitiveMatrix_evalAt {X : Matrix n k (𝔸f E)} (hX : HasLeftInv X) :
    ∀ᶠ w : FinPlace E in Filter.cofinite, IsPrimitiveMatrix (LocInt w).toSubring (X.map (evalAt w)) := by
  obtain ⟨L, hl⟩ := hX
  filter_upwards [eventually_isIntMatrix_evalAt X, eventually_isIntMatrix_evalAt L] with w hwX hwL
  refine ⟨hwX, L.map (evalAt w), hwL, ?_⟩
  rw [← Matrix.map_mul, hl, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Cutting a primitive normalisation down to the finite places where it is needed
preserves its triangular shape and primitivity. -/
private theorem exists_primitive_mul_eq_one_at_primitive {X : Matrix n k (𝔸f E)}
    {α : Type*} [LinearOrder α] {wt : k → α} {a : GL k (𝔸f E)} (ha : a.val.BlockTriangular wt)
    (hprim : IsPrimitiveMatrix (Ô E) (X * a.val)) :
    ∃ b : GL k (𝔸f E), b.val.BlockTriangular wt ∧ IsPrimitiveMatrix (Ô E) (X * b.val) ∧
      ∀ w : FinPlace E, IsPrimitiveMatrix (LocInt w).toSubring (X.map (evalAt w)) →
        b.map (evalAt w) = 1 := by
  classical
  let S : Set (FinPlace E) := {w | ¬ IsPrimitiveMatrix (LocInt w).toSubring (X.map (evalAt w))}
  let b := cutGL (idem_mul_self S) a
  have hcomp (w : FinPlace E) : b.map (evalAt w) = if w ∈ S then a.map (evalAt w) else 1 :=
    map_evalAt_cutGL w S a
  refine ⟨b, ?_, isPrimitiveMatrix_iff_forall_evalAt.mpr fun w ↦ ?_, fun w hw ↦ ?_⟩
  · intro i j hij
    apply DFunLike.ext
    intro w
    have h := congrArg (fun c : GL k (LocField w) ↦ c.val i j) (hcomp w)
    by_cases hw : w ∈ S
    · simpa [hw, ha hij] using h
    · have hne : i ≠ j := fun e ↦ (lt_irrefl _) (e ▸ hij)
      simpa [hw, Matrix.one_apply, hne] using h
  · rw [Matrix.map_mul]
    change IsPrimitiveMatrix (LocInt w).toSubring (X.map (evalAt w) * (b.map (evalAt w)).val)
    by_cases hw : w ∈ S
    · rw [hcomp, ite_eq_left hw]
      have hp := isPrimitiveMatrix_iff_forall_evalAt.mp hprim w
      rwa [Matrix.map_mul] at hp
    · rw [hcomp, ite_eq_right hw, Units.val_one, Matrix.mul_one]
      exact by simpa [S] using hw
  · simp [hcomp, S, hw]

/-- An adelic frame admits a weighted normalisation that acts by the identity at each infinite
place where its columns are already orthonormal and at each finite place where it is primitive. -/
theorem exists_normalizedFrame_eq_one_at_normalized [DecidableEq n] {X : Matrix n k (𝔸 E)}
    (hX : HasLeftInv X) {α : Type*} [LinearOrder α] (wt : k → α) :
    ∃ b : GL k (𝔸 E), b.val.BlockTriangular wt ∧ IsNormalizedAdelicFrame (X * b.val) ∧
      (∀ w : InfinitePlace E, (X.map (evalInf w))ᴴ * X.map (evalInf w) = 1 → b.map (evalInf w) = 1) ∧
      ∀ w : FinPlace E, let f := (evalAt w).comp (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
        IsPrimitiveMatrix (LocInt w).toSubring (X.map f) → b.map f = 1 := by
  classical
  let fin := RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)
  obtain ⟨g, hg, hnorm⟩ := exists_blockTriangular_normalizedFrame hX wt
  have hgfin : (g.map fin).val.BlockTriangular wt := fun i j hij ↦ by
    change fin (g.val i j) = 0
    rw [hg hij, map_zero]
  -- Keep the finite component on the nonprimitive locus.
  have hfin := hnorm.primitive
  rw [Matrix.map_mul] at hfin
  obtain ⟨c, htri, hprim, hc⟩ := exists_primitive_mul_eq_one_at_primitive hgfin hfin
  have arch (w : InfinitePlace E) : ∃ a : GL k ℂ, a.val.BlockTriangular wt ∧
      (X.map (evalInf w) * a.val)ᴴ * (X.map (evalInf w) * a.val) = 1 ∧
      ((X.map (evalInf w))ᴴ * X.map (evalInf w) = 1 → a = 1) := by
    by_cases hw : (X.map (evalInf w))ᴴ * X.map (evalInf w) = 1
    · exact ⟨1, blockTriangular_one, by simpa using hw, fun _ ↦ rfl⟩
    · refine ⟨g.map (evalInf w), fun i j hij ↦ ?_, ?_, fun h ↦ (hw h).elim⟩
      · change evalInf w (g.val i j) = 0
        rw [hg hij, map_zero]
      · have h := hnorm.orthonormal w
        rw [Matrix.map_mul] at h
        exact h
  choose a htri' horth ha using arch
  refine ⟨mkAdelicGL (a, c), fun i j hij ↦ Prod.ext (funext fun w ↦ htri' w hij) (htri hij),
    ⟨fun w ↦ ?_, ?_⟩, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · rw [Matrix.map_mul]
    exact horth w
  · rw [Matrix.map_mul]
    exact hprim
  · exact ha w hw
  · exact hc w hw

end New
