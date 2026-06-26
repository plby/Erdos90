import Towers.ClassField.Shifting.ExplicitShapiro
import Towers.ClassField.Shifting.ShapiroGenerator
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# The Shapiro image of the restriction unit in degree one

This computes the explicit degree-one Shapiro chain map on the image of a
generator under the finite-index `Res ⊣ Ind` unit.  The resulting finite sum
is the usual sum of transfer correction factors over right cosets.
-/

open CategoryTheory Finsupp MonoidalCategory

namespace Rep

noncomputable section

variable {G : Type} [Group G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open scoped Classical in
/-- The finite right-coset sum defining the `Res ⊣ Ind` unit on trivial
integral coefficients. -/
theorem res_ind_trivial (H : Subgroup G) [H.FiniteIndex]
    (x : ℤ) :
    ((resIndAdjunction ℤ H).unit.app (trivial ℤ G ℤ)).hom x =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        Representation.IndV.mk H.subtype
          (res H.subtype (trivial ℤ G ℤ)).ρ (Quotient.out q) x := by
  rw [resIndAdjunction_unit_app]
  change coindToInd (res H.subtype (trivial ℤ G ℤ))
      (((resCoindAdjunction ℤ H.subtype).unit.app
        (trivial ℤ G ℤ)).hom x) = _
  rw [coindToInd_apply]
  apply Fintype.sum_congr
  intro q
  conv_lhs =>
    rw [show q = Quotient.mk'' (Quotient.out q) from
      (Quotient.out_eq' q).symm]
  rfl

set_option maxRecDepth 2000 in
open scoped Classical in
/-- The explicit Shapiro chain map sends a degree-one generator supported at
the right-coset representative `q.out` to its transfer correction factor. -/
theorem ind_shapiro_coset (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (g : G) :
    ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
        (single (fun _ : Fin 1 => g)
          (Representation.IndV.mk H.subtype (trivial ℤ H ℤ).ρ
            (Quotient.out q) 1)) =
      single
        (fun _ : Fin 1 =>
          rightCosetCorrection H (Quotient.out q * g)) 1 := by
  let a := Representation.IndV.mk H.subtype (trivial ℤ H ℤ).ρ
    (Quotient.out q) (1 : ℤ)
  let y : (barComplex ℤ G).X 1 :=
    single (fun _ : Fin 1 => g) (single (1 : G) 1)
  have hfirst :
      ((groupHomology.inhomogeneousChainsIso
        (ind H.subtype (trivial ℤ H ℤ))).hom.f 1).hom
          (single (fun _ : Fin 1 => g) a) =
        coinvariantsTensorMk (ind H.subtype (trivial ℤ H ℤ))
          ((barComplex ℤ G).X 1) a y := by
    change finsuppToCoinvariantsTensorFree
      (ind H.subtype (trivial ℤ H ℤ)) (Fin 1 → G)
        (single (fun _ : Fin 1 => g) a) = _
    rw [finsuppToCoinvariantsTensorFree_single]
    rfl
  let yq : ((resFunctor H.subtype).obj ((barComplex ℤ G).X 1)) :=
    single (fun _ : Fin 1 => g) (single (Quotient.out q) 1)
  have hyaction : ((barComplex ℤ G).X 1).ρ (Quotient.out q) y = yq := by
    change Representation.free ℤ G (Fin 1 → G) (Quotient.out q)
      (single (fun _ : Fin 1 => g) (single 1 1)) =
        single (fun _ : Fin 1 => g) (single (Quotient.out q) 1)
    rw [Representation.free_single_single]
    simp
  have hsecond :
      ((groupHomology.coinvariantsTensorResProjectiveResolutionIso H
        (trivial ℤ H ℤ) (barResolution ℤ G)).symm.hom.f 1).hom
          (coinvariantsTensorMk (ind H.subtype (trivial ℤ H ℤ))
            ((barComplex ℤ G).X 1) a y) =
        coinvariantsTensorMk (trivial ℤ H ℤ)
          ((resFunctor H.subtype).obj ((barComplex ℤ G).X 1)) 1 yq := by
    change coinvariantsTensorIndHom H.subtype (trivial ℤ H ℤ)
      ((barComplex ℤ G).X 1)
        (coinvariantsTensorMk (ind H.subtype (trivial ℤ H ℤ))
          ((barComplex ℤ G).X 1) a y) = _
    rw [show a = Representation.IndV.mk H.subtype
      (trivial ℤ H ℤ).ρ (Quotient.out q) 1 from rfl]
    rw [coinvariantsTensorIndHom_mk_tmul_indVMk]
    rw [hyaction]
  let zH : (barComplex ℤ H).X 1 :=
    single
      (fun _ : Fin 1 => rightCosetCorrection H (Quotient.out q * g))
      (single (1 : H) 1)
  have hbar : ((barProjection (k := ℤ) H).f 1).hom yq = zH := by
    simpa only [yq, zH] using bar_f_coset H q g 1
  have hthird :
      (((((coinvariantsTensor ℤ H).obj (trivial ℤ H ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (barProjection (k := ℤ) H)).f 1).hom
          (coinvariantsTensorMk (trivial ℤ H ℤ)
            ((resFunctor H.subtype).obj ((barComplex ℤ G).X 1)) 1 yq) =
        coinvariantsTensorMk (trivial ℤ H ℤ)
          ((barComplex ℤ H).X 1) 1 zH := by
    simp only [Functor.mapHomologicalComplex_map_f]
    change (((coinvariantsTensor ℤ H).obj (trivial ℤ H ℤ)).map
      ((barProjection (k := ℤ) H).f 1)).hom
        (coinvariantsTensorMk (trivial ℤ H ℤ)
          ((resFunctor H.subtype).obj ((barComplex ℤ G).X 1)) 1 yq) = _
    let tf := (trivial ℤ H ℤ) ◁ ((barProjection (k := ℤ) H).f 1)
    change Representation.Coinvariants.map _ _ tf.hom
        (Representation.Coinvariants.mk _ ((1 : ℤ) ⊗ₜ[ℤ] yq)) =
      Representation.Coinvariants.mk _ ((1 : ℤ) ⊗ₜ[ℤ] zH)
    rw [Representation.Coinvariants.map_mk]
    congr 1
    change (1 : ℤ) ⊗ₜ[ℤ]
      (((barProjection (k := ℤ) H).f 1).hom yq) =
        (1 : ℤ) ⊗ₜ[ℤ] zH
    rw [hbar]
  have hfourth :
      ((groupHomology.inhomogeneousChainsIso
        (trivial ℤ H ℤ)).inv.f 1).hom
          (coinvariantsTensorMk (trivial ℤ H ℤ)
            ((barComplex ℤ H).X 1) 1 zH) =
        single
          (fun _ : Fin 1 =>
            rightCosetCorrection H (Quotient.out q * g)) 1 := by
    change coinvariantsTensorFreeToFinsupp
      (trivial ℤ H ℤ) (Fin 1 → H)
        (coinvariantsTensorMk (trivial ℤ H ℤ)
          ((barComplex ℤ H).X 1) 1 zH) = _
    change coinvariantsTensorFreeToFinsupp
      (trivial ℤ H ℤ) (Fin 1 → H)
        (Representation.Coinvariants.mk _ ((1 : ℤ) ⊗ₜ[ℤ] zH)) = _
    change coinvariantsTensorFreeToFinsupp
      (trivial ℤ H ℤ) (Fin 1 → H)
        (Representation.Coinvariants.mk
          ((trivial ℤ H ℤ).ρ.tprod
            (Representation.free ℤ H (Fin 1 → H)))
          ((1 : ℤ) ⊗ₜ[ℤ]
            single
              (fun _ : Fin 1 =>
                rightCosetCorrection H (Quotient.out q * g))
              (single (1 : H) 1))) = _
    simpa using
      (coinvariantsTensorFreeToFinsupp_mk_tmul_single
        (A := trivial ℤ H ℤ)
        (x := (1 : ℤ))
        (i := fun _ : Fin 1 =>
          rightCosetCorrection H (Quotient.out q * g))
        (g := (1 : H)) (r := (1 : ℤ)))
  change ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
    (single (fun _ : Fin 1 => g) a) = _
  rw [indShapiroChain]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply]
  rw [hfirst]
  refine (congrArg (fun z =>
    ((groupHomology.inhomogeneousChainsIso
      (trivial ℤ H ℤ)).inv.f 1).hom
      ((((((coinvariantsTensor ℤ H).obj
        (trivial ℤ H ℤ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (barProjection (k := ℤ) H)).f 1).hom z)) hsecond).trans ?_
  refine (congrArg (fun z =>
    ((groupHomology.inhomogeneousChainsIso
      (trivial ℤ H ℤ)).inv.f 1).hom z) hthird).trans ?_
  exact hfourth

open scoped Classical in
/-- The degree-one generator first mapped by the actual restriction unit and
then by explicit Shapiro is the finite sum of transfer correction factors. -/
theorem ind_shapiro_chain
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
        (single (fun _ : Fin 1 => g)
          (((resIndAdjunction ℤ H).unit.app (trivial ℤ G ℤ)).hom (1 : ℤ))) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        single
          (fun _ : Fin 1 =>
            rightCosetCorrection H (Quotient.out q * g)) 1 := by
  rw [res_ind_trivial]
  change ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
      (single (fun _ : Fin 1 => g)
        (∑ q : Quotient (QuotientGroup.rightRel H),
          Representation.IndV.mk H.subtype (trivial ℤ H ℤ).ρ
            (Quotient.out q) 1)) = _
  rw [Finsupp.single_finsetSum]
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel H),
        ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
          (single (fun _ : Fin 1 => g)
            (Representation.IndV.mk H.subtype (trivial ℤ H ℤ).ρ
              (Quotient.out q) 1)) := by
      exact map_sum
        ((indShapiroChain H (trivial ℤ H ℤ)).f 1).hom
        (fun q : Quotient (QuotientGroup.rightRel H) =>
          single (fun _ : Fin 1 => g)
            (Representation.IndV.mk H.subtype (trivial ℤ H ℤ).ρ
              (Quotient.out q) 1)) Finset.univ
    _ = _ := by
      apply Fintype.sum_congr
      intro q
      exact ind_shapiro_coset H q g

end

end Rep
