import Towers.ClassField.LocalClass.ExpUnitHom
import Towers.ClassField.LocalClass.OpenUnitTransfer

/-!
# Lemma III.2.5: Herbrand quotients of local units and a local field

For a cyclic finite extension `L/K` of nonarchimedean local fields in
characteristic zero, `h(U_L)=1` and `h(Lˣ)=[L:K]`.
-/

namespace Towers.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Towers.CField.Shifting
open Towers.CField.LBrauer

noncomputable section

/-- A representation has Herbrand quotient `q`, including the finiteness
data required for the quotient to be defined. -/
def HerbrandQuotient {G : Type} [CommGroup G] [Fintype G]
    (A : Rep ℤ G) (q : ℚ) : Prop :=
  ∃ (h₁ : Finite (groupCohomology A 1))
      (h₂ : Finite (groupCohomology A 2)),
    letI := h₁
    letI := h₂
    (herbrandQuotient A : ℚ) = q

@[reducible]
private noncomputable def hTrivialInt
    (G : Type) [CommGroup G] [Fintype G] :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  letI : Subsingleton (groupCohomology (Rep.trivial ℤ G ℤ) 1) :=
    ModuleCat.subsingleton_of_isZero (cohomology_trivial_int G)
  infer_instance

@[reducible]
private noncomputable def finiteTrivialInt
    {G : Type} [CommGroup G] [Fintype G]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) 2) := by
  let e₀ := tateCohomologyTrivial G
  letI : Finite (tateCohomologyZero (Rep.trivial ℤ G ℤ)) :=
    Finite.of_equiv (ZMod (Fintype.card G)) e₀.symm.toEquiv
  exact Finite.of_equiv (tateCohomologyZero (Rep.trivial ℤ G ℤ))
    (tateCohomologyTwo
      (Rep.trivial ℤ G ℤ) g hg).toEquiv

/-- Lemma III.2.5 with an explicitly installed valuative relation on the
base local field. -/
theorem local_herbrand_quotients
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] :
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotient (localUnitRepresentation K L) 1 ∧
      HerbrandQuotient (Rep.ofAlgebraAutOnUnits K L)
        (Module.finrank K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A : Subring K :=
    @Valued.integer K _ NNReal _ NormedField.toValued
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨d, hd, hsource, hopen, hnear, hstable, e, hequiv, _⟩ :=
    galois_stable_acyclic K L
  let W := integralNormalSpan A K L d hd
  let U := localExpSubgroup L W.toAddSubgroup hsource
  have hopen' : extensionUnitOpen K L U := by
    change IsOpen (U : Set Lˣ)
    exact hopen
  have hnear' : extensionNearOne K L U := by
    change Units.val '' (U : Set Lˣ) ⊆ Metric.ball 1 1
    exact hnear
  let f := stableUnitInclusion K L U hstable hnear'
  have h₁ : IsZero (groupCohomology
      (stableUnitRepresentation K L U hstable) 1) :=
    cohomology_stable_subgroup A K L d hd U hstable e
      hequiv 1 (by omega)
  have h₂ : IsZero (groupCohomology
      (stableUnitRepresentation K L U hstable) 2) :=
    cohomology_stable_subgroup A K L d hd U hstable e
      hequiv 2 (by omega)
  letI : Subsingleton (groupCohomology
      (stableUnitRepresentation K L U hstable) 1) :=
    ModuleCat.subsingleton_of_isZero h₁
  letI : Subsingleton (groupCohomology
      (stableUnitRepresentation K L U hstable) 2) :=
    ModuleCat.subsingleton_of_isZero h₂
  letI : Finite (groupCohomology
      (stableUnitRepresentation K L U hstable) 1) := inferInstance
  letI : Finite (groupCohomology
      (stableUnitRepresentation K L U hstable) 2) := inferInstance
  letI : Finite ↑(kernel f : Rep ℤ Gal(L/K)) :=
    stable_unit_inclusion K L U hstable hnear'
  letI : Finite ↑(cokernel f : Rep ℤ Gal(L/K)) :=
    cokernel_stable_inclusion K L U hstable hnear' hopen'
  have hfiniteU := herbrand_codomain_cokernel
    f g hg
  letI : Finite (groupCohomology (localUnitRepresentation K L) 1) :=
    hfiniteU.1
  letI : Finite (groupCohomology (localUnitRepresentation K L) 2) :=
    hfiniteU.2
  have hU : (herbrandQuotient (localUnitRepresentation K L) : ℚ) = 1 := by
    have h := cokernel_herbrand_one f g hg h₁ h₂
    change (herbrandQuotient (localUnitRepresentation K L) : ℚ) = 1 at h
    exact h
  constructor
  · exact ⟨hfiniteU.1, hfiniteU.2, hU⟩
  · letI : Finite (groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 1) :=
      hTrivialInt Gal(L/K)
    letI : Finite (groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2) :=
      finiteTrivialInt g hg
    let S := localShortComplex K L
    have hS := local_short_exact K L
    have hfiniteL := herbrand_quotient_middle hS g hg
    letI : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) :=
      hfiniteL.1
    letI : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
      hfiniteL.2
    have hmul := herbrandQuotient_mul hS g hg
    have hmulQ := congrArg (fun z : ℚˣ ↦ (z : ℚ)) hmul
    change (herbrandQuotient (Rep.ofAlgebraAutOnUnits K L) : ℚ) =
      (herbrandQuotient (localUnitRepresentation K L) : ℚ) *
        (herbrandQuotient (Rep.trivial ℤ Gal(L/K) ℤ) : ℚ) at hmulQ
    have hZ : (herbrandQuotient (Rep.trivial ℤ Gal(L/K) ℤ) : ℚ) =
        Fintype.card Gal(L/K) := by
      have h := herbrand_trivial_int g hg
      change (herbrandQuotient (Rep.trivial ℤ Gal(L/K) ℤ) : ℚ) =
        Fintype.card Gal(L/K) at h
      exact h
    have hcard : Fintype.card Gal(L/K) = Module.finrank K L := by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    refine ⟨hfiniteL.1, hfiniteL.2, ?_⟩
    change (herbrandQuotient (Rep.ofAlgebraAutOnUnits K L) : ℚ) =
      Module.finrank K L
    rw [hU, hZ, one_mul, hcard] at hmulQ
    exact hmulQ

/-- **Lemma III.2.5 (canonical characteristic-zero statement).**  The
valuative relation on `K` is fixed internally to the one induced by its
given norm.  Thus the public hypotheses are exactly local-field data,
characteristic zero, finite Galois extension, and cyclicity. -/
theorem herbrand_quotients_canonical
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K] [CharZero K]
    (hK : letI : ValuativeRel K :=
      ValuativeRel.ofValuation (NormedField.valuation (K := K))
      IsNonarchimedeanLocalField K)
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] :
    letI : ValuativeRel K :=
      ValuativeRel.ofValuation (NormedField.valuation (K := K))
    letI : IsNonarchimedeanLocalField K := hK
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotient (localUnitRepresentation K L) 1 ∧
      HerbrandQuotient (Rep.ofAlgebraAutOnUnits K L)
        (Module.finrank K L) := by
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : IsNonarchimedeanLocalField K := hK
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  exact local_herbrand_quotients K L

end

end Towers.CField.LClass
