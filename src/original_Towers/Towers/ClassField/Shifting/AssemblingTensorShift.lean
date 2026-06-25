import Towers.ClassField.Shifting.TensorAcyclicity
import Towers.ClassField.Shifting.ExceptionalShift
import Towers.ClassField.Shifting.ExceptionalTateTransport
import Towers.ClassField.Shifting.DoubleShift
import Towers.ClassField.Shifting.NormExactSequence

/-!
# Milne, Class Field Theory, Remark II.3.12: assembling the tensor shift

Two adjacent short exact sequences with Tate-acyclic middle terms give a
two-degree shift with arbitrary coefficients.  This file carries out the
splice in every Tate range represented in the project, including the two
exceptional degrees.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep

noncomputable section

universe u

/-- Additive form of exceptional degree-zero transport.  Keeping this
wrapper polymorphic in the scalar ring avoids choosing the competing
canonical `ℤ`-module structure on an additive quotient. -/
noncomputable def tateAddIso
    {k K : Type u} [CommRing k] [Group K] [Fintype K]
    {A B : Rep.{u} k K} (e : A ≅ B) :
    tateCohomologyZero A ≃+ tateCohomologyZero B :=
  (tateZeroIso e).toAddEquiv

/-- Additive form of exceptional degree-minus-one transport. -/
noncomputable def tateCohomologyIso
    {k K : Type u} [CommRing k] [Group K] [Fintype K]
    {A B : Rep.{u} k K} (e : A ≅ B) :
    tateCohomologyOne A ≃+ tateCohomologyOne B :=
  (tateNegIso e).toAddEquiv

/-- Additive form of the boundary `H_T⁰(X₃) ≅ H¹(X₁)`. -/
noncomputable def tateShortExact
    {k K : Type u} [CommRing k] [Group K] [Fintype K]
    {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂))
    (hone : IsZero (groupCohomology X.X₂ 1)) :
    tateCohomologyZero X.X₃ ≃+ groupCohomology X.X₁ 1 :=
  (cohomologyShortExact hX hzero hone).toAddEquiv

/-- Additive form of the boundary `H_T⁻¹(X₃) ≅ H_T⁰(X₁)`. -/
noncomputable def negShortExact
    {k K : Type u} [CommRing k] [Group K] [Fintype K]
    (X : ShortComplex (Rep.{u} k K)) (hX : X.ShortExact)
    (hneg : Subsingleton (tateCohomologyOne X.X₂))
    (hzero : Subsingleton (tateCohomologyZero X.X₂)) :
    tateCohomologyOne X.X₃ ≃+ tateCohomologyZero X.X₁ :=
  (isoShortExact X hX hneg hzero).toAddEquiv

/-- Additive form of the low homology boundary
`H₁(X₃) ≅ H_T⁻¹(X₁)`. -/
noncomputable def homologyShortExact
    {k K : Type u} [CommRing k] [Group K] [Fintype K]
    (X : ShortComplex (Rep.{u} k K)) (hX : X.ShortExact)
    (hH₁ : IsZero (groupHomology X.X₂ 1))
    (hneg : Subsingleton (tateCohomologyOne X.X₂)) :
    groupHomology X.X₃ 1 ≃+ tateCohomologyOne X.X₁ :=
  (homologyNegShort X hX hH₁ hneg).toAddEquiv

variable {G : Type} [Group G] [Fintype G]

/-- A two-degree Tate shift from a coefficient module `A` to a coefficient
module `C`, split into the six ranges represented in the project. -/
structure TSCoeffi (A C : Rep ℤ G) where
  positive : ∀ n : ℕ, 0 < n →
    groupCohomology A n ≃+ groupCohomology C (n + 2)
  zero : tateCohomologyZero A ≃+ groupCohomology C 2
  negOne : tateCohomologyOne A ≃+ groupCohomology C 1
  negTwo : groupHomology A 1 ≃+ tateCohomologyZero C
  negThree : groupHomology A 2 ≃+ tateCohomologyOne C
  lower : ∀ n : ℕ, 0 < n →
    groupHomology A (n + 2) ≃+ groupHomology C n

/-- Transport the source of a two-degree Tate shift across an isomorphism of
representations. -/
noncomputable def TSCoeffi.transSource
    {A A' C : Rep ℤ G} (e : A ≅ A')
    (s : TSCoeffi A' C) :
    TSCoeffi A C := by
  exact
    { positive := fun n hn ↦
      ((groupCohomology.functor ℤ G n).mapIso e).toLinearEquiv.toAddEquiv.trans
        (s.positive n hn)
      zero := (tateAddIso e).trans s.zero
      negOne := (tateCohomologyIso e).trans s.negOne
      negTwo :=
      ((groupHomology.functor ℤ G 1).mapIso e).toLinearEquiv.toAddEquiv.trans
        s.negTwo
      negThree :=
      ((groupHomology.functor ℤ G 2).mapIso e).toLinearEquiv.toAddEquiv.trans
        s.negThree
      lower := fun n hn ↦
      ((groupHomology.functor ℤ G (n + 2)).mapIso e).toLinearEquiv.toAddEquiv.trans
        (s.lower n hn) }

/-- Splice two adjacent short exact sequences with Tate-acyclic middle terms
to obtain the arbitrary-coefficient two-degree shift. -/
noncomputable def shiftSplicedShort
    {X Y : ShortComplex (Rep ℤ G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (e : Y.X₁ ≅ X.X₃)
    (hXAcyclic : TateAcyclic X.X₂) (hYAcyclic : TateAcyclic Y.X₂) :
    TSCoeffi Y.X₃ X.X₁ := by
  have hpositive (n : ℕ) (hn : 0 < n) :
      groupCohomology Y.X₃ n ≃+ groupCohomology X.X₁ (n + 2) :=
    (positiveDoubleShift hX hY e
      hXAcyclic.positiveCohomology hYAcyclic.positiveCohomology n hn).toLinearEquiv.toAddEquiv
  have hzero : tateCohomologyZero Y.X₃ ≃+
      groupCohomology X.X₁ 2 := by
    let e₁ := tateShortExact hY
      hYAcyclic.zero (hYAcyclic.positiveCohomology 1 Nat.zero_lt_one)
    let e₂ := ((groupCohomology.functor ℤ G 1).mapIso e).toLinearEquiv.toAddEquiv
    let e₃ := (COps.dimensionShiftingIso hX
      hXAcyclic.positiveCohomology 1 Nat.zero_lt_one).toLinearEquiv.toAddEquiv
    exact e₁.trans e₂ |>.trans e₃
  have hnegOne : tateCohomologyOne Y.X₃ ≃+
      groupCohomology X.X₁ 1 := by
    let e₁ := negShortExact Y hY
      hYAcyclic.negOne hYAcyclic.zero
    let e₂ := tateAddIso e
    let e₃ := tateShortExact hX
      hXAcyclic.zero (hXAcyclic.positiveCohomology 1 Nat.zero_lt_one)
    exact e₁.trans e₂ |>.trans e₃
  have hnegTwo : groupHomology Y.X₃ 1 ≃+
      tateCohomologyZero X.X₁ := by
    let e₁ := homologyShortExact Y hY
      (hYAcyclic.positiveHomology 1 Nat.zero_lt_one) hYAcyclic.negOne
    let e₂ := tateCohomologyIso e
    let e₃ := negShortExact X hX
      hXAcyclic.negOne hXAcyclic.zero
    exact e₁.trans e₂ |>.trans e₃
  have hnegThree : groupHomology Y.X₃ 2 ≃+
      tateCohomologyOne X.X₁ := by
    let e₁ := (homologyShiftingIso hY
      hYAcyclic.positiveHomology 1 Nat.zero_lt_one).toLinearEquiv
    let e₂ := ((groupHomology.functor ℤ G 1).mapIso e).toLinearEquiv
    let e₃ := homologyShortExact X hX
      (hXAcyclic.positiveHomology 1 Nat.zero_lt_one) hXAcyclic.negOne
    exact e₁.toAddEquiv.trans e₂.toAddEquiv |>.trans e₃
  have hlower (n : ℕ) (hn : 0 < n) :
      groupHomology Y.X₃ (n + 2) ≃+ groupHomology X.X₁ n :=
    (homologyDoubleShift hX hY e
      hXAcyclic.positiveHomology hYAcyclic.positiveHomology n hn).toLinearEquiv.toAddEquiv
  exact
    { positive := hpositive
      zero := hzero
      negOne := hnegOne
      negTwo := hnegTwo
      negThree := hnegThree
      lower := hlower }

/-- On an invariant representative, the degree-zero component of the
spliced two-shift is the composite of the two ordinary connecting maps. -/
theorem shift_spliced_short
    {X Y : ShortComplex (Rep ℤ G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (e : Y.X₁ ≅ X.X₃)
    (hXAcyclic : TateAcyclic X.X₂) (hYAcyclic : TateAcyclic Y.X₂)
    (z : (Rep.invariantsFunctor ℤ G).obj Y.X₃) :
    (shiftSplicedShort hX hY e hXAcyclic hYAcyclic).zero
        (tateCohomologyProjection Y.X₃ z) =
      groupCohomology.δ hX 1 2 rfl
        (groupCohomology.map (MonoidHom.id G) e.hom 1
          (groupCohomology.δ hY 0 1 rfl
            ((groupCohomology.H0Iso Y.X₃).inv z))) := by
  change
    (COps.dimensionShiftingIso hX
      hXAcyclic.positiveCohomology 1 Nat.zero_lt_one).hom
        (groupCohomology.map (MonoidHom.id G) e.hom 1
          (cohomologyShortExact hY
            hYAcyclic.zero
            (hYAcyclic.positiveCohomology 1 Nat.zero_lt_one)
            (tateCohomologyProjection Y.X₃ z))) = _
  rw [short_exact_projection]
  rfl

end

end Towers.CField.Shifting
