import Towers.ClassField.Shifting.TateCoverClosure
import Towers.ClassField.Shifting.NormExactSequence

/-!
# Milne, Class Field Theory, Remark II.3.12: the degree-zero shift

The positive long exact cohomology sequence and the norm exact sequence meet
at degree zero.  For a short exact sequence whose middle term has vanishing
degree-zero Tate cohomology and first cohomology, the connecting map therefore
descends to an isomorphism from degree-zero Tate cohomology of the quotient to
first cohomology of the kernel.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The degree-zero cohomology boundary, written on invariant
representatives. -/
private noncomputable def tateBoundaryAux
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    X.X₃.ρ.invariants →ₗ[k] groupCohomology X.X₁ 1 :=
  ((groupCohomology.H0Iso X.X₃).inv ≫
    groupCohomology.δ hX 0 1 rfl).hom

/-- The kernel of the degree-zero boundary on invariant representatives is
exactly the image of the norm. -/
private theorem ker_boundary_aux
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂)) :
    LinearMap.ker (tateBoundaryAux hX) =
      LinearMap.range (normCoinvariantsInvariants X.X₃) := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    let d := groupCohomology.δ hX 0 1 rfl
    let q := (groupCohomology.mapShortComplex₃
      (i := 0) (j := 1) hX rfl).f
    have hex := groupCohomology.mapShortComplex₃_exact
      (i := 0) (j := 1) hX rfl
    have hmem : (groupCohomology.H0Iso X.X₃).inv z ∈
        LinearMap.range q.hom := by
      rw [hex.moduleCat_range_eq_ker]
      change (groupCohomology.δ hX 0 1 rfl).hom
        ((groupCohomology.H0Iso X.X₃).inv z) = 0
      exact hz
    obtain ⟨y, hy⟩ := hmem
    have hinv : z ∈ LinearMap.range
        ((Rep.invariantsFunctor k G).map X.g).hom := by
      refine ⟨(groupCohomology.H0Iso X.X₂).hom y, ?_⟩
      have hnat := groupCohomology.map_id_comp_H0Iso_hom X.g
      have := congrArg (fun f => f y) hnat
      calc
        ((Rep.invariantsFunctor k G).map X.g).hom
            ((groupCohomology.H0Iso X.X₂).hom y) =
            (groupCohomology.H0Iso X.X₃).hom (q y) := this.symm
        _ = z := by rw [hy]; simp
    obtain ⟨y, rfl⟩ := hinv
    have hsurj : Function.Surjective
        (normCoinvariantsInvariants X.X₂) :=
      (coinvariants_invariants_surjective X.X₂).2 hzero
    obtain ⟨y, rfl⟩ := hsurj y
    refine ⟨((Rep.coinvariantsFunctor k G).map X.g).hom y, ?_⟩
    have hnat := (normNatTrans (k := k) (G := G)).naturality X.g
    exact congrArg (fun f => f y) hnat
  · rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective X.X₃.ρ z
    obtain ⟨y, hy⟩ :=
      (Rep.epi_iff_surjective X.g).1 hX.epi_g x
    let q := (groupCohomology.mapShortComplex₃
      (i := 0) (j := 1) hX rfl).f
    have hnat := groupCohomology.map_id_comp_H0Iso_hom X.g
    have hnorm : normCoinvariantsInvariants X.X₃
          (Representation.Coinvariants.mk X.X₃.ρ x) =
        ((Rep.invariantsFunctor k G).map X.g).hom
          (normCoinvariantsInvariants X.X₂
            (Representation.Coinvariants.mk X.X₂.ρ y)) := by
      apply Subtype.ext
      change X.X₃.ρ.norm x = X.g.hom (X.X₂.ρ.norm y)
      rw [← hy]
      exact congrArg (fun f : X.X₂ ⟶ X.X₃ => f.hom y) (Rep.norm_comm X.g)
    rw [hnorm]
    have hH0 : (groupCohomology.H0Iso X.X₃).inv
          (((Rep.invariantsFunctor k G).map X.g).hom
            (normCoinvariantsInvariants X.X₂
              (Representation.Coinvariants.mk X.X₂.ρ y))) =
        q ((groupCohomology.H0Iso X.X₂).inv
          (normCoinvariantsInvariants X.X₂
            (Representation.Coinvariants.mk X.X₂.ρ y))) := by
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.H0Iso X.X₃).hom).1 inferInstance
      let a := normCoinvariantsInvariants X.X₂
        (Representation.Coinvariants.mk X.X₂.ρ y)
      let b := (groupCohomology.H0Iso X.X₂).inv a
      have heval := congrArg (fun f => f b) hnat
      change (groupCohomology.H0Iso X.X₃).hom (q b) =
        ((Rep.invariantsFunctor k G).map X.g).hom
          ((groupCohomology.H0Iso X.X₂).hom b) at heval
      simp only [b, Iso.inv_hom_id_apply] at heval
      simpa only [a, Iso.inv_hom_id_apply] using heval.symm
    let a := normCoinvariantsInvariants X.X₂
      (Representation.Coinvariants.mk X.X₂.ρ y)
    change (groupCohomology.δ hX 0 1 rfl).hom
      ((groupCohomology.H0Iso X.X₃).inv
        (((Rep.invariantsFunctor k G).map X.g).hom a)) = 0
    calc
      (groupCohomology.δ hX 0 1 rfl).hom
          ((groupCohomology.H0Iso X.X₃).inv
            (((Rep.invariantsFunctor k G).map X.g).hom a)) =
          (groupCohomology.δ hX 0 1 rfl).hom
            (q ((groupCohomology.H0Iso X.X₂).inv a)) :=
        congrArg (groupCohomology.δ hX 0 1 rfl).hom hH0
      _ = 0 := congrArg (fun f => f
        ((groupCohomology.H0Iso X.X₂).inv a))
        (groupCohomology.mapShortComplex₃
          (i := 0) (j := 1) hX rfl).zero

/-- The degree-zero connecting map after quotienting invariant
representatives by norms. -/
private noncomputable def tateZeroBoundary
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂)) :
    tateCohomologyZero X.X₃ →ₗ[k] groupCohomology X.X₁ 1 :=
  (LinearMap.range (normCoinvariantsInvariants X.X₃)).liftQ
    (tateBoundaryAux hX) (ker_boundary_aux hX hzero).ge

/-- **Remark II.3.12, exceptional degree zero.** The connecting map of a
short exact sequence induces an equivalence
`H_T⁰(G,X₃) ≃ H¹(G,X₁)` when the middle term has vanishing
`H_T⁰` and `H¹`. -/
noncomputable def cohomologyShortExact
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂))
    (hone : IsZero (groupCohomology X.X₂ 1)) :
    tateCohomologyZero X.X₃ ≃ₗ[k] groupCohomology X.X₁ 1 :=
  LinearEquiv.ofBijective (tateZeroBoundary hX hzero) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot'
        (LinearMap.range (normCoinvariantsInvariants X.X₃))
        (tateBoundaryAux hX) (ker_boundary_aux hX hzero).symm
    · haveI : Epi (groupCohomology.δ hX 0 1 rfl) :=
        groupCohomology.epi_δ_of_isZero hX 0 hone
      intro z
      obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
        (groupCohomology.δ hX 0 1 rfl)).1 inferInstance z
      refine ⟨Submodule.Quotient.mk
        ((groupCohomology.H0Iso X.X₃).hom y), ?_⟩
      simpa [tateZeroBoundary, tateBoundaryAux] using hy

/-- On an invariant representative, the exceptional degree-zero
equivalence is the ordinary degree-zero connecting map. -/
theorem short_exact_mk
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂))
    (hone : IsZero (groupCohomology X.X₂ 1))
    (z : X.X₃.ρ.invariants) :
    cohomologyShortExact hX hzero hone
        (Submodule.Quotient.mk z) =
      groupCohomology.δ hX 0 1 rfl
        ((groupCohomology.H0Iso X.X₃).inv z) := by
  rfl

/-- Projection-form variant of
`short_exact_mk`. -/
theorem short_exact_projection
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hzero : Subsingleton (tateCohomologyZero X.X₂))
    (hone : IsZero (groupCohomology X.X₂ 1))
    (z : X.X₃.ρ.invariants) :
    cohomologyShortExact hX hzero hone
        (tateCohomologyProjection X.X₃ z) =
      groupCohomology.δ hX 0 1 rfl
        ((groupCohomology.H0Iso X.X₃).inv z) := by
  rfl

end

end Towers.CField.Shifting
