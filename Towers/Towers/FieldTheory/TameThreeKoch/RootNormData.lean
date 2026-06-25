import Towers.FieldTheory.TameThreeKoch.PlaceBrauerTransport

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

universe u v w

open NumberField
open Towers.CField.Ideles
open Towers.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The dependent fields repeatedly recover the canonical completion actions.
set_option maxHeartbeats 4000000 in
-- Elaborating the package checks all pullback, inertia, and norm field types together.
/-- The tame local data used to kill the pullback obstruction at one finite place. -/
structure TamePrimitiveData
    {Q G : Type v} [Group Q] [Finite Q] [Group G] [Finite G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    [Fact (FinitePlace.mk P).val.IsNontrivial]
    [IsUltrametricDist (FinitePlace.mk P).val.Completion]
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [Nonempty
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    (I : Subgroup (placeCanonicalGal P w)) [I.Normal]
    (n : ℕ) [NeZero n] where
  hphi : Function.Injective
    ((placeCompletionUnits P w kernelToUnits).comp
      (centralExtensionPullback q
        (placeCompletionGroup P w galoisEquiv)).toMonoidHom)
  eI : Multiplicative (ZMod n) ≃* I
  x : CentralExtensionPullback q
    (placeCompletionGroup P w galoisEquiv)
  hx : extensionPullbackProjection q
      (placeCompletionGroup P w galoisEquiv) x =
    I.subtype
      (eI Towers.CField.LBrauer.CyclicH2.generator)
  horderX : orderOf (extensionPullbackProjection q
    (placeCompletionGroup P w galoisEquiv) x) = n
  y : CentralExtensionPullback q
    (placeCompletionGroup P w galoisEquiv)
  r : ℕ
  hconj : y * x * y⁻¹ = x ^ r
  zeta : w.1.Completionˣ
  hzeta : IsPrimitiveRoot zeta (orderOf x)
  hzetaI : ∀ i : I, i.1 • zeta = zeta
  hzetaY : extensionPullbackProjection q
    (placeCompletionGroup P w galoisEquiv) y • zeta = zeta ^ r
  degree : ℕ
  hdegree : 0 < degree
  horder : orderOf
    (QuotientGroup.mk' (I.comap (extensionPullbackProjection q
      (placeCompletionGroup P w galoisEquiv))) y) = degree
  hgen : Subgroup.zpowers
    (QuotientGroup.mk' (I.comap (extensionPullbackProjection q
      (placeCompletionGroup P w galoisEquiv))) y) = ⊤
  ord : w.1.Completionˣ →* Multiplicative ℤ
  hord : ∀ g : placeCanonicalGal P w,
    ∀ z : w.1.Completionˣ, ord (g • z) = ord z
  hnorm : ∀ c : w.1.Completionˣ,
    (∀ g : placeCanonicalGal P w, g • c = c) →
    ord c = 1 →
    ∃ b : w.1.Completionˣ,
      (∀ i : I, i.1 • b = b) ∧
        (∏ k ∈ Finset.range degree,
          (extensionPullbackProjection q
            (placeCompletionGroup P w galoisEquiv) y) ^ k • b) = c

end TBluepr
end Towers
