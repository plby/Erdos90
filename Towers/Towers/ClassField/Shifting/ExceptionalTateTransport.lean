import Towers.ClassField.Shifting.TateShift

/-!
# Milne, Class Field Theory, Remark II.3.12: exceptional Tate transport

An isomorphism of representations induces linear equivalences on the two
exceptional Tate cohomology groups.  These equivalences are used to remove
the unit objects introduced by tensoring.
-/

namespace Towers.CField.Shifting

open CategoryTheory Rep Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

private noncomputable def coinvariantsLinearEquiv
    {A B : Rep.{u} k G} (e : A ≅ B) :
    A.ρ.Coinvariants ≃ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).mapIso e).toLinearEquiv

private noncomputable def invariantsLinearEquiv
    {A B : Rep.{u} k G} (e : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).mapIso e).toLinearEquiv

private theorem norm_coinvariants_linear
    {A B : Rep.{u} k G} (e : A ≅ B) (x : A.ρ.Coinvariants) :
    normCoinvariantsInvariants B (coinvariantsLinearEquiv e x) =
      invariantsLinearEquiv e (normCoinvariantsInvariants A x) := by
  have h := (normNatTrans (k := k) (G := G)).naturality e.hom
  exact congrArg (fun f => f x) h

private theorem map_normKernel
    {A B : Rep.{u} k G} (e : A ≅ B) :
    (LinearMap.ker (normCoinvariantsInvariants A)).map
        (coinvariantsLinearEquiv e).toLinearMap =
      LinearMap.ker (normCoinvariantsInvariants B) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change normCoinvariantsInvariants A y = 0 at hy
    change normCoinvariantsInvariants B (coinvariantsLinearEquiv e y) = 0
    rw [norm_coinvariants_linear, hy, map_zero]
  · intro hx
    refine ⟨(coinvariantsLinearEquiv e).symm x, ?_, ?_⟩
    · change normCoinvariantsInvariants A
        ((coinvariantsLinearEquiv e).symm x) = 0
      apply (invariantsLinearEquiv e).injective
      rw [← norm_coinvariants_linear]
      simpa using
        (LinearMap.mem_ker.mp hx)
    · exact (coinvariantsLinearEquiv e).apply_symm_apply x

/-- An isomorphism of representations induces an equivalence on
degree-minus-one Tate cohomology. -/
noncomputable def tateNegIso
    {A B : Rep.{u} k G} (e : A ≅ B) :
    tateCohomologyOne A ≃ₗ[k] tateCohomologyOne B :=
  ((coinvariantsLinearEquiv e).submoduleMap
      (LinearMap.ker (normCoinvariantsInvariants A))).trans
    (LinearEquiv.ofEq _ _ (map_normKernel e))

private theorem map_normRange
    {A B : Rep.{u} k G} (e : A ≅ B) :
    (LinearMap.range (normCoinvariantsInvariants A)).map
        (invariantsLinearEquiv e).toLinearMap =
      LinearMap.range (normCoinvariantsInvariants B) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨coinvariantsLinearEquiv e z,
      norm_coinvariants_linear e z⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(invariantsLinearEquiv e).symm
      (normCoinvariantsInvariants B z), ?_, ?_⟩
    · refine ⟨(coinvariantsLinearEquiv e).symm z, ?_⟩
      apply (invariantsLinearEquiv e).injective
      rw [← norm_coinvariants_linear]
      simp
    · simp

/-- An isomorphism of representations induces an equivalence on degree-zero
Tate cohomology. -/
noncomputable def tateZeroIso
    {A B : Rep.{u} k G} (e : A ≅ B) :
    tateCohomologyZero A ≃ₗ[k] tateCohomologyZero B :=
  Submodule.Quotient.equiv
    (LinearMap.range (normCoinvariantsInvariants A))
    (LinearMap.range (normCoinvariantsInvariants B))
    (invariantsLinearEquiv e) (map_normRange e)

/-- The transport on degree-zero Tate cohomology maps an invariant
representative by the underlying representation isomorphism. -/
theorem tate_iso_mk
    {A B : Rep.{u} k G} (e : A ≅ B) (z : A.ρ.invariants) :
    tateZeroIso e (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (((Rep.invariantsFunctor k G).map e.hom).hom z) := by
  rfl

end

end Towers.CField.Shifting
