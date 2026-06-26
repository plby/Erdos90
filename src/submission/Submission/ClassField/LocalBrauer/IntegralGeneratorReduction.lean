import Submission.NumberTheory.Locals.UnramifiedExtensions
import Submission.ClassField.LocalBrauer.UnramifiedAdjoin

/-!
# Reduction of an integral generator of an unramified model

If `A[e]` is a finite local algebra which is formally unramified over the
discrete valuation ring `A`, then reduction of the integral minimal
polynomial of `e` is irreducible and separable.  This is the converse to the
construction in `UnramifiedAdjoin`: formal unramifiedness identifies the
maximal ideal of `A[e]` with the extended maximal ideal of `A`, and the
power-basis quotient presentation identifies the resulting residue field
with the quotient by the reduced minimal polynomial.
-/

namespace Submission.CField.LBrauer

noncomputable section

open IsLocalRing Polynomial

attribute [local instance] Ideal.Quotient.field

universe u v

/-- The reduction of the minimal polynomial of a generator of a formally
unramified local integral model is irreducible. -/
theorem irreducible_formally_adjoin
    (A : Type u) (E : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing E] [IsDomain E]
    [Algebra A E] [Module.IsTorsionFree A E]
    (e : E) (he : IsIntegral A e)
    (hlocal : IsLocalRing (Algebra.adjoin A ({e} : Set E)))
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E))) :
    Irreducible ((minpoly A e).map (residue A)) := by
  let U := Algebra.adjoin A ({e} : Set E)
  letI : IsLocalRing U := hlocal
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral he
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra.FormallyUnramified A U := hunramified
  let p := maximalIdeal A
  let f := (minpoly A e).map (residue A)
  let pb : PowerBasis A U := Algebra.adjoin.powerBasis' he
  have hminpolyGen : minpoly A pb.gen = minpoly A e := by
    rw [← minpoly.algHom_eq U.val Subtype.val_injective pb.gen]
    congr 2
    simp [pb, Algebra.adjoin.powerBasis'_gen]
  let q : Ideal (Polynomial (A ⧸ p)) := Ideal.span ({f} : Set (Polynomial (A ⧸ p)))
  let equiv := pb.quotientEquivQuotientMinpolyMap p
  have hleft : IsField (U ⧸ p.map (algebraMap A U)) :=
    Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
  have hrightRaw : IsField
      (Polynomial (A ⧸ p) ⧸ Ideal.span
        ({(minpoly A pb.gen).map (Ideal.Quotient.mk p)} :
          Set (Polynomial (A ⧸ p)))) :=
    equiv.symm.toRingEquiv.toMulEquiv.isField hleft
  have hpoly :
      (minpoly A pb.gen).map (Ideal.Quotient.mk p) = f := by
    change (minpoly A pb.gen).map
        (Ideal.Quotient.mk (maximalIdeal A)) =
      (minpoly A e).map (Ideal.Quotient.mk (maximalIdeal A))
    rw [hminpolyGen]
  have hideal :
      Ideal.span ({(minpoly A pb.gen).map (Ideal.Quotient.mk p)} :
        Set (Polynomial (A ⧸ p))) = q := by
    simpa [q] using congrArg
      (fun z ↦ Ideal.span ({z} : Set (Polynomial (A ⧸ p)))) hpoly
  have hright : IsField (Polynomial (A ⧸ p) ⧸ q) := by
    exact (Ideal.quotEquivOfEq hideal).symm.toMulEquiv.isField hrightRaw
  have hqmax : q.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mpr hright
  have hfne : f ≠ 0 := by
    exact (minpoly.monic he).map (residue A) |>.ne_zero
  have hfprime : Prime f := by
    apply (Ideal.span_singleton_prime hfne).mp
    exact hqmax.isPrime
  exact hfprime.irreducible

/-- The reduced integral minimal polynomial is the minimal polynomial of
the residue class of the chosen generator. -/
theorem minpoly_adjoin_generator
    (A : Type u) (E : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing E] [IsDomain E]
    [Algebra A E] [Module.IsTorsionFree A E]
    (e : E) (he : IsIntegral A e)
    (hlocal : IsLocalRing (Algebra.adjoin A ({e} : Set E)))
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E))) :
    let U := Algebra.adjoin A ({e} : Set E)
    letI : Module.Finite A U :=
      Algebra.finite_adjoin_simple_of_isIntegral he
    letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
    letI : IsLocalRing U := hlocal
    letI : IsLocalHom (algebraMap A U) :=
      Algebra.IsIntegral.isLocalHom A U
    minpoly (ResidueField A)
        (residue U ⟨e, Algebra.self_mem_adjoin_singleton A e⟩) =
      (minpoly A e).map (residue A) := by
  let U := Algebra.adjoin A ({e} : Set E)
  letI : IsLocalRing U := hlocal
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral he
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra.FormallyUnramified A U := hunramified
  let eU : U := ⟨e, Algebra.self_mem_adjoin_singleton A e⟩
  have hirred : Irreducible ((minpoly A e).map (residue A)) :=
    irreducible_formally_adjoin
      A E e he hlocal hunramified
  have hcompResidue :
      (algebraMap (ResidueField A) (ResidueField U)).comp (residue A) =
        (residue U).comp (algebraMap A U) := by
    ext x
    exact (IsLocalRing.ResidueField.algebraMap_residue x).symm
  have hevalU : aeval eU (minpoly A e) = 0 := by
    apply Subtype.ext
    rw [Polynomial.aeval_subalgebra_coe]
    simp [eU]
  have hroot :
      aeval (residue U eU) ((minpoly A e).map (residue A)) = 0 := by
    have hx := congrArg (residue U) hevalU
    rw [map_zero] at hx
    exact (map_aeval_eq_aeval_map hcompResidue (minpoly A e) eU).symm.trans hx
  exact (minpoly.eq_of_irreducible_of_monic hirred hroot
    ((minpoly.monic he).map (residue A))).symm

/-- Consequently the reduced minimal polynomial is separable. -/
theorem separable_formally_adjoin
    (A : Type u) (E : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing E] [IsDomain E]
    [Algebra A E] [Module.IsTorsionFree A E]
    (e : E) (he : IsIntegral A e)
    (hlocal : IsLocalRing (Algebra.adjoin A ({e} : Set E)))
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E))) :
    ((minpoly A e).map (residue A)).Separable := by
  let U := Algebra.adjoin A ({e} : Set E)
  letI : IsLocalRing U := hlocal
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral he
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra.FormallyUnramified A U := hunramified
  let eU : U := ⟨e, Algebra.self_mem_adjoin_singleton A e⟩
  rw [← minpoly_adjoin_generator
    A E e he hlocal hunramified]
  exact Algebra.IsSeparable.isSeparable (ResidueField A) (residue U eU)

/-- If `e` also generates the fraction-field extension, the degree of its
reduced integral minimal polynomial is the full field degree. -/
theorem minpoly_adjoin_top
    (A K E : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E]
    [Algebra A E] [IsScalarTower A K E] [Module.Finite K E]
    (e : E) (he : IsIntegral A e)
    (hgen : Algebra.adjoin K ({e} : Set E) = ⊤) :
    ((minpoly A e).map (residue A)).natDegree = Module.finrank K E := by
  have hminpoly : minpoly K e = (minpoly A e).map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K he
  have hgenIF : IntermediateField.adjoin K ({e} : Set E) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ ↦ IsAlgebraic.of_finite K x), IntermediateField.top_toSubalgebra]
    exact hgen
  calc
    ((minpoly A e).map (residue A)).natDegree =
        (minpoly A e).natDegree :=
      (minpoly.monic he).natDegree_map (residue A)
    _ = (minpoly K e).natDegree := by
      rw [hminpoly, (minpoly.monic he).natDegree_map]
    _ = Module.finrank K E :=
      (Field.primitive_element_iff_minpoly_natDegree_eq K e).mp hgenIF

/-- The complete converse package for an integral primitive generator of a
finite unramified local model: its reduced minimal polynomial is
irreducible, separable, and has the full extension degree. -/
theorem minpoly_formally_adjoin
    (A K E : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E]
    [Algebra A E] [IsScalarTower A K E] [Module.Finite K E]
    [Module.IsTorsionFree A E]
    (e : E) (he : IsIntegral A e)
    (hgen : Algebra.adjoin K ({e} : Set E) = ⊤)
    (hlocal : IsLocalRing (Algebra.adjoin A ({e} : Set E)))
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E))) :
    Irreducible ((minpoly A e).map (residue A)) ∧
      ((minpoly A e).map (residue A)).Separable ∧
      ((minpoly A e).map (residue A)).natDegree =
        Module.finrank K E := by
  exact ⟨
    irreducible_formally_adjoin
      A E e he hlocal hunramified,
    separable_formally_adjoin
      A E e he hlocal hunramified,
    minpoly_adjoin_top
      A K E e he hgen⟩

end

end Submission.CField.LBrauer
