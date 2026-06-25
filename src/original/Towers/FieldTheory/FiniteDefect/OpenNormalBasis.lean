import Towers.FieldTheory.FiniteDefect.RawQuotientCompletion
import Towers.Group.FinitePQuotient.OpenNormalFamilies


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open ONCofina
open PRFact
open PRQuotie
open RSFact
open TFFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData
namespace CSCone

/--
The open-normal subgroup of the actual initial Galois group cut out by one
raw quotient factor.
-/
def factorOpenSubgroup
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    OpenNormalSubgroup initialGaloisGroup :=
  (C.toQShadow D n).kernelOpenSubgroup

@[simp]
lemma factor_open_normal
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    (C.factorOpenSubgroup D n : Subgroup initialGaloisGroup) =
      (C.factor n).ker := rfl

/--
The raw quotient kernels form a descending family of open-normal subgroups:
passing to a deeper raw Zassenhaus quotient can only shrink the actual
Galois-group kernel.
-/
lemma factor_open_subgroup
    (D : KRData)
    (C : D.CSCone)
    {n m : ℕ}
    (hnm : n ≤ m) :
    C.factorOpenSubgroup D m ≤
      C.factorOpenSubgroup D n := by
  change (C.factor m).ker ≤ (C.factor n).ker
  exact C.factor_kernel D hnm

/--
The raw quotient kernel at one stage is the pullback of the corresponding
coordinate-projection kernel along the raw inverse-limit equivalence.
-/
lemma comap_limit_projection
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    (C.factorOpenSubgroup D n : Subgroup initialGaloisGroup) =
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n).ker.comap
        (C.quotientLimitLift D) := by
  ext y
  have hcoordinate := DFunLike.congr_fun
    (C.limit_lift_coordinate D n)
    y
  change Group.inverseLimitProjection D.ZassenhausRelatorSystem n
      (C.quotientLimitLift D y) =
    C.factor n y at hcoordinate
  change C.factor n y = 1 ↔
    Group.inverseLimitProjection D.ZassenhausRelatorSystem n
      (C.quotientLimitLift D y) = 1
  rw [hcoordinate]
  exact Iff.rfl

/--
The open-normal raw quotient kernels are cofinal among all open-normal
subgroups of the actual initial Galois group.
-/
lemma factor_open_cofinal
    (D : KRData)
    (C : D.CSCone) :
    CofinalOpenFamily (C.factorOpenSubgroup D) := by
  simpa [factorOpenSubgroup] using
    cofinal_open_shadow
      initial_pro_three
      (C.toQShadow D)
      (C.quotient_shadow_cofinal D)

/--
Every identity neighborhood in the actual initial Galois group contains one
raw quotient kernel.
-/
lemma open_subset_nhds
    (D : KRData)
    (C : D.CSCone)
    {U : Set initialGaloisGroup}
    (hU : U ∈ 𝓝 (1 : initialGaloisGroup)) :
    ∃ n : ℕ, (C.factorOpenSubgroup D n : Set initialGaloisGroup) ⊆ U := by
  simpa [factorOpenSubgroup] using
    subset_nhds_cofinal
      initial_pro_three
      (C.toQShadow D)
      (C.quotient_shadow_cofinal D)
      hU

/--
The raw quotient kernels form an open-normal neighborhood basis at `1` in the
actual initial Galois group.
-/
lemma basis_nhds_open
    (D : KRData)
    (C : D.CSCone) :
    (𝓝 (1 : initialGaloisGroup)).HasBasis
      (fun _n : ℕ => True)
      (fun n : ℕ => (C.factorOpenSubgroup D n : Set initialGaloisGroup)) := by
  simpa [factorOpenSubgroup] using
    basis_nhds_cofinal
      initial_pro_three
      (C.toQShadow D)
      (C.quotient_shadow_cofinal D)

/--
The desired finite quotient Koch theorem is equivalent to existence of a raw
canonical quotient cone whose actual Galois-group kernels form an open-normal
neighborhood basis at `1`.
-/
lemma theorem_cone_basis
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ C : D.CSCone,
        (𝓝 (1 : initialGaloisGroup)).HasBasis
          (fun _n : ℕ => True)
          (fun n : ℕ => (C.factorOpenSubgroup D n : Set initialGaloisGroup)) := by
  constructor
  · intro hfactor
    let C := kochFactorizationTheorem D hfactor
    exact ⟨C, C.basis_nhds_open D⟩
  · rintro ⟨C, _hC⟩
    exact koch_theorem_nonempty D ⟨C⟩

end CSCone
end KRData

end TBluepr
end Towers
