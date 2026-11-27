module

public import Lib.ClassField.GreenbergWiles.Relations
public import Lib.ClassField.GreenbergWiles.SelmerClasses

/-!
# The Greenberg–Wiles bound for classes in a relation setting

`New.RelationSetting.exists_card_cocycles_le` bounds the cocycles `Z(∅)` that are allowed at the
primes of `S`, vanish at complex conjugations and are unramified outside `S`, against the relations
at split primes. This file states the same bound for the corresponding Selmer classes in
`H¹(Gal(Ω/K), M)`.

* `New.RelationSetting.exists_card_classes_le`: `#H¹_L · #M ^ r₂ · ∏_{v ∈ S} #H⁰_v` is at most
  `#(relations off T) · ∏_{v ∈ S} #L_v`, where `L_v` is the module of classes of the allowed local
  cocycles and `r₂` the number of infinite places.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` for sources.
-/

@[expose] public section

noncomputable section

namespace New.RelationSetting

open NumberField DiscreteModule Finset Fintype Module commutatorElement

variable {K R : Type} [Field K] [EmbeddedNumberField K] [CommRing R] {M : DiscreteModule R Gal(Ω/K)}

variable {m : ℕ} [NeZero m] (D : RelationSetting M m)

/-- The Selmer classes with the local conditions of `D` and extra ramification allowed in `P`. -/
abbrev classes (P : Set (FinPlace K)) : Submodule R (M.H 1) :=
  selmerH1 M D.localPrimes D.place D.allowed P

/-- The classes of the allowed cocycles on the decomposition group at `v`. -/
abbrev localClasses (v : FinPlace K) :=
  classCondition M (D.allowed v)

/-- The elements of the coefficient module fixed by the decomposition group at `v`. -/
abbrev localInvariants (v : FinPlace K) :=
  (M.restrictTo (decompGroup Gal(Ω/K) (D.place v))).ρ.invariants

/-- A bound for the sum of local cocycle lengths gives a bound for the local class lengths.
Passing to classes replaces one copy of the coefficients at each place by the local invariants. -/
lemma sum_length_localClasses_le {b : ℕ∞} (hM : length R M ≠ ⊤)
    (h : ∑ v ∈ D.localPrimes, length R (D.localCocycles v) ≤
      #D.localPrimes • length R M + b) :
    ∑ v ∈ D.localPrimes, length R (D.localClasses v) ≤
      b + ∑ v ∈ D.localPrimes, length R (D.localInvariants v) := by
  have hfin : #D.localPrimes • length R M ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) hM
  apply (ENat.add_le_add_iff_right hfin).mp
  calc (∑ v ∈ D.localPrimes, length R (D.localClasses v)) +
        #D.localPrimes • length R M =
      ∑ v ∈ D.localPrimes, (length R (D.localClasses v) + length R M) := by
        rw [sum_add_distrib, sum_const]
    _ = ∑ v ∈ D.localPrimes,
        (length R (D.localCocycles v) + length R (D.localInvariants v)) :=
      sum_congr rfl fun v hv ↦ selmerH1.length_classCondition_add_length (D.coboundary_le v hv)
    _ ≤ _ := by
      rw [sum_add_distrib]
      exact (add_le_add_left h (∑ v ∈ D.localPrimes, length R (D.localInvariants v))).trans_eq
        (by ac_rfl)

/-- The class of an allowed cocycle satisfies the local Selmer conditions. -/
def toSelmerH1 (P : Set (FinPlace K)) : D.cocycles P →ₗ[R] D.classes P :=
  let incl : D.cocycles P →ₗ[R] Z1 M.ρ := Submodule.inclusion fun _ hz ↦ hz.1.1
  (M.π₁.comp incl).codRestrict _ fun z ↦ by
    change incl z ∈ (D.classes P).comap M.π₁
    rw [classes, selmerH1.comap_π₁_eq D.unramified D.coboundary_le D.ρ_eq_one_of_isComplexConj]
    exact z.property

/-- A Selmer cocycle represents zero exactly when it is a global coboundary. -/
lemma toSelmerH1_eq_zero_iff {P : Set (FinPlace K)} (z : D.cocycles P) :
    D.toSelmerH1 P z = 0 ↔ ∃ b : M, ∀ g, M.ρ g b - b = z.val g := by
  rw [Subtype.ext_iff]
  change M.π₁ ⟨z, z.property.1.1⟩ = 0 ↔ _
  rw [← LinearMap.mem_ker, M.ker_π₁, mem_B1_iff]

/-- Every Selmer class admits a representative in `D.cocycles P`. -/
lemma toSelmerH1_surjective (P : Set (FinPlace K)) : Function.Surjective (D.toSelmerH1 P) := by
  rintro ⟨c, hc⟩
  obtain ⟨z, rfl⟩ := M.π₁_surjective c
  change z ∈ (D.classes P).comap M.π₁ at hc
  rw [classes, selmerH1.comap_π₁_eq D.unramified D.coboundary_le D.ρ_eq_one_of_isComplexConj] at hc
  exact ⟨⟨z, hc⟩, rfl⟩

/-- A case of the formula of Greenberg and Wiles for Selmer classes: the form of
`New.RelationSetting.exists_card_cocycles_le` for classes. Let `K` be totally complex, `M` finite
and killed by `ℓ ^ r` with `r ≠ 0`, and let `σ` fix the `ℓ`-power roots of unity, be central modulo
`U` and fix no nonzero element of `M`. If `p` can be avoided, there is a finite set `T ⊇ S` of
primes not dividing `p` such that the Selmer classes `H¹_L` (`New.selmerH1`) unramified outside `S`
satisfy `#H¹_L · #M ^ r₂ · ∏_{v ∈ S} #H⁰_v ≤ #(relations off T) · ∏_{v ∈ S} #L_v`. Here `H⁰_v`
is the module of invariants of the decomposition group at `v`, `L_v` is the module of classes of
the allowed local cocycles at `v`, and `r₂` is the number of infinite places. -/
theorem exists_card_classes_le {ℓ r : ℕ} [Fact ℓ.Prime] [IsTotallyComplex K] [Finite M]
    (D : RelationSetting M (ℓ ^ r)) (hr : r ≠ 0) {σ : Gal(Ω/K)} (hσ_cyc : cyclotomicChar Ω ℓ σ = 1)
    (hσ_comm : ∀ g : Gal(Ω/K), ⁅σ, g⁆ ∈ D.subgroup) (hσ_fix : ∀ a : M, M.ρ σ a = a → a = 0)
    {p : ℕ} [NeZero p] (hp : D.Avoids p) :
    ∃ T : Finset (FinPlace K), D.localPrimes ⊆ T ∧ (∀ v ∈ T, ↑p ∉ v.asIdeal) ∧
      Nat.card (D.classes ∅) * Nat.card M ^ card (InfinitePlace K) *
          ∏ v ∈ D.localPrimes, Nat.card (D.localInvariants v) ≤
        Nat.card (D.relations T) * ∏ v ∈ D.localPrimes, Nat.card (D.localClasses v) := by
  obtain ⟨T, hST, hTp, h_cocycles⟩ := D.exists_card_cocycles_le hr hσ_cyc hσ_comm hσ_fix hp
  refine ⟨T, hST, hTp, ?_⟩
  rw [selmerH1.card_selmerZ1_eq D.unramified D.coboundary_le D.ρ_eq_one_of_isComplexConj,
    prod_congr rfl fun v hv ↦ selmerH1.card_localCocycles_eq (D.coboundary_le v hv)]
    at h_cocycles
  -- `σ` fixes no nonzero element, so `M` has no nonzero invariants.
  have h_inv : Nat.card M.ρ.invariants = 1 := by
    have h_bot : M.ρ.invariants = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun a ha ↦ hσ_fix a (ha σ)
    rw [h_bot]
    exact Nat.card_unique
  have h := selmerH1.mul_pow_le_of_le D.localPrimes
    (card_B1_mul_card_invariants M.continuous_orbit)
    (fun v _ ↦ card_B1_mul_card_invariants (M.restrictTo _).continuous_orbit) Nat.card_pos
    h_cocycles
  rw [h_inv, mul_one] at h
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := M))
  calc Nat.card M * (Nat.card (selmerH1 M D.localPrimes D.place D.allowed ∅) *
          Nat.card M ^ card (InfinitePlace K) *
          ∏ v ∈ D.localPrimes,
            Nat.card (M.restrictTo (decompGroup Gal(Ω/K) (D.place v))).ρ.invariants)
      = _ := by ring
    _ ≤ _ := h
    _ = _ := by ring

end New.RelationSetting
