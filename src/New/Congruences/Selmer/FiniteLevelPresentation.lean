module

public import New.Congruences.Selmer.OneSystem

/-!
# Specializing the finite-level Selmer presentation

The matrix for `selmerAtPoint` has coefficient module killed by `a = ℓ ^ M`. Its row lattice
contains the rows of `a • 1`. At a polynomial point where each `(1 + X j) ^ q - 1` evaluates to
a multiple of the level, the corresponding scalar relations already lie in the specialized
row lattice.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Matrix Submodule MvPolynomial

section Rows

variable {Λ O r σ : Type*} [CommRing Λ] [CommRing O]

/-- The block of rows `ω j • eᵢ`, indexed by a relation and a coordinate. -/
def scalarRelationRows (k : Type*) [DecidableEq k] (ω : σ → Λ) : Matrix (σ × k) k Λ :=
  Matrix.of fun p i ↦ ω p.1 * (1 : Matrix k k Λ) p.2 i

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- If every specialized scalar relation is divisible by the level, adjoining its rows before
specialization gives the same finite-level row lattice. -/
theorem rowLattice_map_fromRows_scalarRelationRows (A : Matrix r k Λ) (a : Λ) (ω : σ → Λ)
    (ev : Λ →+* O) (hω : ∀ j, ev a ∣ ev (ω j)) :
    rowLattice ((A.fromRows (scalarRelationRows k ω)).map ev) (ev a) =
      rowLattice (A.map ev) (ev a) := by
  refine le_antisymm (span_le.2 ?_) (span_mono ?_)
  · rintro _ ⟨(i | ⟨j, i⟩) | i, rfl⟩
    · exact subset_span ⟨.inl i, rfl⟩
    · obtain ⟨c, hc⟩ := hω j
      have hrow : ((scalarRelationRows k ω).map ev).row (j, i) =
          ev a • (c • (1 : Matrix k k O).row i) := by
        ext t
        simp [scalarRelationRows, Matrix.row, Matrix.one_apply, apply_ite ev, hc]
      change ((scalarRelationRows k ω).map ev).row (j, i) ∈ rowLattice (A.map ev) (ev a)
      rw [hrow]
      exact smul_mem_rowLattice _ _ _
    · exact subset_span ⟨.inr i, rfl⟩
  · rintro _ ⟨i | i, rfl⟩
    · exact ⟨.inl (.inl i), rfl⟩
    · exact ⟨.inr i, rfl⟩

/-- The identity on the specialized generators identifies the two presented modules. -/
def quotientRowLatticeEquivOfDvd (A : Matrix r k Λ) (a : Λ) (ω : σ → Λ) (ev : Λ →+* O)
    (hω : ∀ j, ev a ∣ ev (ω j)) :
    ((k → O) ⧸ rowLattice ((A.fromRows (scalarRelationRows k ω)).map ev) (ev a)) ≃ₗ[O]
      (k → O) ⧸ rowLattice (A.map ev) (ev a) :=
  Submodule.quotEquivOfEq _ _ (rowLattice_map_fromRows_scalarRelationRows A a ω ev hω)

end Rows

variable {E O n σ : Type} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n]
  [DecidableEq n] [Fintype σ] {q ℓ M : ℕ} [NeZero ℓ] {S : Set (FinPlace E)}
  {h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {ρ : Gal(Ω/E) →* Matrix n n O}

open scoped Classical in
/-- One polynomial matrix presents the pointwise Selmer equations at every point. For this same
matrix the rows imposing the group-ring relations preserve the finite-level row lattice whenever
the coordinates `1 + x j` are `q`-th roots of unity modulo `ℓ ^ M`. -/
theorem exists_matrix_selmerAtPoint_equiv_rowLattice (h_char_const : ∀ j, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    ∃ (r k : Type) (_ : Fintype k) (A : Matrix r k (MvPolynomial σ O)),
      ∀ (O' : Type) [CommRing O'] (e : O →+* O') (x : σ → O'),
        Nonempty (selmerAtPoint ℓ M h ρ S L e x ≃ₗ[O']
          matrixKernel (A.map (eval₂Hom e x)) (QuotSpan (ℓ ^ M : O'))) ∧
        ((∀ j, (ℓ ^ M : O') ∣ (1 + x j) ^ q - 1) →
          rowLattice ((A.fromRows (scalarRelationRows k (fun j : σ ↦ (1 + X j) ^ q - 1))).map
            (eval₂Hom e x)) (ℓ ^ M) = rowLattice (A.map (eval₂Hom e x)) (ℓ ^ M)) := by
  obtain ⟨r, k, _, A, hA⟩ := exists_matrix_selmerAtPoint_equiv h_char_const hρ hS L
  refine ⟨r, k, inferInstance, A, fun O' _ e x ↦ ⟨hA O' e x, fun hx ↦ ?_⟩⟩
  let ω (j : σ) : MvPolynomial σ O := (1 + X j) ^ q - 1
  have hω (j : σ) : eval₂Hom e x (ℓ ^ M : MvPolynomial σ O) ∣ eval₂Hom e x (ω j) := by
    simpa [ω] using hx j
  simpa using rowLattice_map_fromRows_scalarRelationRows A (ℓ ^ M) ω (eval₂Hom e x) hω

end New.Selmer

end
