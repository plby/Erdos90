import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Pi

/-!
# Integral lattices under total-quotient product equivalences

A ring equivalence between an integral ring and a product of integral
rings extends canonically to their chosen total quotient rings.  When the
integral equivalence respects a coefficient ring, this extension carries
the source integral lattice to the product of the factor integral lattices.
-/

namespace Submission.NumberTheory.Milne

open Module Submodule

noncomputable section

universe u v

variable {C A X ι : Type*} (B L : ι → Type u)
  [CommRing C] [CommRing A] [CommRing X]
  [∀ i, CommRing (B i)] [∀ i, CommRing (L i)]
  [Algebra C A] [Algebra A X] [Algebra C X] [IsScalarTower C A X]
  [∀ i, Algebra C (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, Algebra C (L i)] [∀ i, IsScalarTower C (B i) (L i)]
  [IsFractionRing A X]
  [IsFractionRing (∀ i, B i) (∀ i, L i)]

/-- A coefficient-linear equivalence of integral rings induces a
coefficient-linear equivalence of their chosen total quotient rings. -/
noncomputable def fractionRingAlg
    (e₀ : A ≃ₐ[C] (∀ i, B i)) : X ≃ₐ[C] (∀ i, L i) := by
  let e : X ≃+* (∀ i, L i) :=
    IsFractionRing.ringEquivOfRingEquiv e₀.toRingEquiv
  exact AlgEquiv.ofRingEquiv (f := e) fun c => by
    calc
      e (algebraMap C X c) =
          e (algebraMap A X (algebraMap C A c)) := by
        rw [IsScalarTower.algebraMap_apply C A X]
      _ = algebraMap (∀ i, B i) (∀ i, L i)
          (e₀ (algebraMap C A c)) :=
        IsFractionRing.ringEquivOfRingEquiv_algebraMap
          e₀.toRingEquiv (algebraMap C A c)
      _ = algebraMap (∀ i, B i) (∀ i, L i)
          (algebraMap C (∀ i, B i) c) := by rw [e₀.commutes]
      _ = algebraMap C (∀ i, L i) c :=
        (IsScalarTower.algebraMap_apply C (∀ i, B i) (∀ i, L i) c).symm

/-- The total-quotient equivalence induced by an equivalence of integral
rings carries the source unit lattice to the product of the factor unit
lattices.  This is the integral-lattice identity used as `hN` in trace-dual
transport. -/
theorem restrict_scalars_fraction
    (e₀ : A ≃ₐ[C] (∀ i, B i)) :
    ((1 : Submodule A X).restrictScalars C).map
        (fractionRingAlg (X := X) B L e₀).toLinearMap =
      Submodule.pi Set.univ
        (fun i => (1 : Submodule (B i) (L i)).restrictScalars C) := by
  let e := fractionRingAlg (X := X) B L e₀
  ext x
  change (x ∈ ((1 : Submodule A X).restrictScalars C).map
      e.toLinearEquiv.toLinearMap) ↔ _
  rw [Submodule.mem_map_equiv, Submodule.mem_pi]
  constructor
  · intro hx i _
    change e.symm x ∈ (1 : Submodule A X) at hx
    rw [mem_one] at hx
    obtain ⟨a, ha⟩ := hx
    change x i ∈ (1 : Submodule (B i) (L i))
    rw [mem_one]
    refine ⟨e₀ a i, ?_⟩
    have hxe : x = e (algebraMap A X a) := by
      rw [← e.apply_symm_apply x, ha]
    rw [hxe]
    have heq : e (algebraMap A X a) =
        algebraMap (∀ i, B i) (∀ i, L i) (e₀ a) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (K := X) (L := ∀ i, L i) e₀.toRingEquiv a
    simpa using (congrFun heq i).symm
  · intro hx
    choose b hb using fun i => (mem_one.mp (hx i (Set.mem_univ i)))
    let y : ∀ i, B i := fun i => b i
    let a : A := e₀.symm y
    change e.symm x ∈ (1 : Submodule A X)
    rw [mem_one]
    refine ⟨a, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    have heq : e (algebraMap A X a) =
        algebraMap (∀ i, B i) (∀ i, L i) (e₀ a) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (K := X) (L := ∀ i, L i) e₀.toRingEquiv a
    ext i
    rw [heq]
    change algebraMap (B i) (L i) (e₀ a i) = x i
    simpa only [a, y, e₀.apply_symm_apply] using hb i

end

end Submission.NumberTheory.Milne
