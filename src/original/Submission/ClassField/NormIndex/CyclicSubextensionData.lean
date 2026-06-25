import Mathlib.GroupTheory.Solvable
import Submission.ClassField.IdeleCohomology.FinitenessStatement
import Submission.ClassField.NormIndex.HerbrandCardinalityBound

/-!
# Chapter VII, Section 4, Lemma 4.5

Let `L/K` be a finite solvable Galois extension.  Milne's lemma says that if
a subgroup `D ⊆ I_K` is contained in the idèle norm range and `Kˣ D` is
dense in `I_K`, then `L = K`.

For abstract field types, literal type equality is not the right formulation
of the conclusion.  We use the canonical equivalent numerical assertion
`[L : K] = 1`.

The topological and index argument is proved below using Proposition 2.8 and
Corollary 4.4.  Two arithmetic facts not supplied by the current idèle API are
kept as narrow bridges: existence of the cyclic intermediate extension used
in the printed proof, and transitivity of the concrete idèle norm map.
-/

namespace Submission.CField.NIndex

open IsDedekindDomain NumberField Topology
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

/-- A nontrivial cyclic intermediate extension `E/K` inside `L/K`.

The two algebra structures and the scalar-tower field say literally that
`E` is embedded between `K` and `L`.  The remaining fields record exactly
that `E/K` is a nontrivial finite cyclic Galois extension. -/
structure CyclicSubextensionData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] where
  E : Type u
  fieldE : Field E
  numberFieldE : NumberField E
  algebraKE : Algebra K E
  algebraEL : Algebra E L
  scalarTower : IsScalarTower K E L
  finiteDimensionalKE : FiniteDimensional K E
  finiteDimensionalEL : FiniteDimensional E L
  isGaloisKE : IsGalois K E
  isGaloisEL : IsGalois E L
  isCyclicKE : IsCyclic Gal(E/K)
  one_lt_finrank : 1 < Module.finrank K E

/-- The solvable-group/Galois-correspondence step in the source proof: a
nontrivial finite solvable Galois extension has a nontrivial cyclic Galois
intermediate extension over the base. -/
def CyclicSubextensionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsSolvable Gal(L/K)],
    Module.finrank K L ≠ 1 →
      Nonempty (CyclicSubextensionData K L)

/-- Transitivity for the concrete idèle norm maps constructed in Chapter V.
This is exactly the equality

`Nm_{L/K} = Nm_{E/K} ∘ Nm_{L/E}`

used in the source proof. -/
def SubextensionTransitivityBridge : Prop :=
  ∀ (K E L : Type u) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L],
    ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L))

/-- The range of a composite idèle norm is contained in the range of its
outer norm. -/
private theorem idele_subgroup_transitivity
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
    (htrans : ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L))) :
    ideleNormSubgroup (K := K) (L := L) ≤
      ideleNormSubgroup (K := K) (L := E) := by
  rintro x ⟨y, rfl⟩
  refine ⟨ideleNorm (K := E) (L := L) y, ?_⟩
  exact (DFunLike.congr_fun htrans y).symm

/-- A dense open subgroup of a topological group is the whole group. -/
private theorem dense_open_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hdense : Dense (H : Set G))
    (hopen : IsOpen (H : Set G)) :
    H = ⊤ := by
  apply SetLike.coe_injective
  rw [Subgroup.coe_top, ← hdense.closure_eq]
  exact (H.isClosed_of_isOpen hopen).closure_eq.symm

/-- Lemma 4.5 follows from Proposition 2.8, the first inequality, and the two
precise intermediate-field/norm-transitivity facts isolated above. -/
theorem subextension_previous_results
    (hopen : ∀ (K L : Type u) [Field K] [Field L]
      [NumberField K] [NumberField L] [Algebra K L]
      [FiniteDimensional K L],
      IdeleSubgroupOpen (K := K) (L := L))
    (hfirst : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index))
    (hcyclic : CyclicSubextensionBridge.{u})
    (htrans : SubextensionTransitivityBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1) := by
  intro K L _ _ _ _ _ _ _ _ D hD hdense
  by_contra hdegree
  obtain ⟨data⟩ := hcyclic K L hdegree
  letI : Field data.E := data.fieldE
  letI : NumberField data.E := data.numberFieldE
  letI : Algebra K data.E := data.algebraKE
  letI : Algebra data.E L := data.algebraEL
  letI : IsScalarTower K data.E L := data.scalarTower
  letI : FiniteDimensional K data.E := data.finiteDimensionalKE
  letI : FiniteDimensional data.E L := data.finiteDimensionalEL
  letI : IsGalois K data.E := data.isGaloisKE
  letI : IsGalois data.E L := data.isGaloisEL
  letI : IsCyclic Gal(data.E/K) := data.isCyclicKE
  let H : Subgroup (IK K) :=
    principalIdeles (NumberField.RingOfIntegers K) K ⊔
      ideleNormSubgroup (K := K) (L := data.E)
  have hnormLE : ideleNormSubgroup (K := K) (L := L) ≤
      ideleNormSubgroup (K := K) (L := data.E) :=
    idele_subgroup_transitivity
      (htrans K data.E L)
  have hsmall_le_H :
      principalIdeles (NumberField.RingOfIntegers K) K ⊔ D ≤ H := by
    exact sup_le_sup le_rfl (hD.trans hnormLE)
  have hHdense : Dense (H : Set (IK K)) :=
    hdense.mono hsmall_le_H
  have hnormOpen : IsOpen
      (ideleNormSubgroup (K := K) (L := data.E) : Set (IK K)) :=
    hopen K data.E
  have hHopen : IsOpen (H : Set (IK K)) :=
    Subgroup.isOpen_mono le_sup_right hnormOpen
  have hHtop : H = ⊤ :=
    dense_open_top H hHdense hHopen
  have hindexOne : H.index = 1 := by
    rw [hHtop, Subgroup.index_eq_one]
  have hdegreeLe : Module.finrank K data.E ≤ 1 := by
    simpa only [H, hindexOne] using hfirst K data.E
  exact (Nat.not_lt_of_ge hdegreeLe) data.one_lt_finrank

end

end Submission.CField.NIndex
