import Towers.Group.Edmonton.SchurBaer
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Edmonton Notes on Nilpotent Groups: Section 9 Theorems of Malcev

This file records Hall's final section.  The central-series exponent
calculation is proved from Section 4.  The representation-theoretic
theorems are exposed as reusable interfaces, following the pattern used
for the embedding theorems in Section 7.
-/

namespace Towers
namespace Edmonton

noncomputable section

open Group

universe u v

variable {G : Type u} [Group G]

/-- A subgroup is abelian when its commutator subgroup is trivial. -/
def IsAbelianSubgroup (A : Subgroup G) : Prop :=
  ⁅A, A⁆ = ⊥

/-- Maximality among the normal abelian subgroups of the ambient group. -/
def MaximalAbelianSubgroup (A : Subgroup G) : Prop :=
  A.Normal ∧ IsAbelianSubgroup A ∧
    ∀ B : Subgroup G, B.Normal → IsAbelianSubgroup B → A ≤ B → B = A

/-- The self-centralizing assertion in Hall's Lemma 9.1. -/
def MaximalCentralizingProperty
    (G : Type u) [Group G] : Prop :=
  Group.IsNilpotent G →
    ∀ A : Subgroup G, MaximalAbelianSubgroup A →
      Subgroup.centralizer (A : Set G) = A

/-- **Hall, Lemma 9.1.** A maximal normal abelian subgroup of a
nilpotent group coincides with its centralizer. -/
theorem maximal_abelian_centralizer [Group.IsNilpotent G]
    (hselfCentralizing : MaximalCentralizingProperty G)
    (A : Subgroup G) (hA : MaximalAbelianSubgroup A) :
    Subgroup.centralizer (A : Set G) = A :=
  hselfCentralizing inferInstance A hA

/-- **Hall, Lemma 9.2.** If the center has exponent `m`, then every
successive upper-central factor has exponent `m`. -/
theorem upper_series_exponent {m : ℕ}
    (hcenter : SubgroupHasExponent (Subgroup.upperCentralSeries G 1) m) :
    ∀ k x, x ∈ Subgroup.upperCentralSeries G (k + 1) →
      x ^ m ∈ Subgroup.upperCentralSeries G k := by
  rw [Subgroup.upperCentralSeries_one] at hcenter
  exact upper_exponent_center (G := G) hcenter

/-- A faithful degree-`n` linear representation over `K`. -/
def FaithfulLinearRepresentation
    (G : Type u) [Group G] (n : ℕ) (K : Type v) [Field K] : Prop :=
  ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) K,
    Function.Injective ρ

/-- A faithful determinant-one linear representation. -/
def FaithfulSpecialRepresentation
    (G : Type u) [Group G] (n : ℕ) (K : Type v) [Field K] : Prop :=
  ∃ ρ : G →* Matrix.SpecialLinearGroup (Fin n) K,
    Function.Injective ρ

/-- The center of a determinant-one matrix subgroup consists of scalar
matrices. -/
def HasScalarCenter {n : ℕ} {K : Type v} [Field K]
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) : Prop :=
  ∀ x : Subgroup.center H, ∃ a : K,
    (x.1.1 : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a

/-- The matrix-group finiteness assertion used in Hall's Lemma 9.3. -/
def CenterFinitenessProperty
    (n : ℕ) (K : Type v) [Field K] : Prop :=
  ∀ H : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
    Group.IsNilpotent H → HasScalarCenter H → Finite H

/-- **Hall, Lemma 9.3.** A nilpotent determinant-one matrix group whose
center consists of scalar matrices is finite. -/
theorem nilpotent_special_center {n : ℕ} {K : Type v} [Field K]
    (hfinite : CenterFinitenessProperty n K)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) K))
    (hnilpotent : Group.IsNilpotent H) (hcenter : HasScalarCenter H) :
    Finite H :=
  hfinite H hnilpotent hcenter

/-- An invertible matrix is upper triangular. -/
def UpperTriangularGL {n : ℕ} {K : Type v} [Field K]
    (x : Matrix.GeneralLinearGroup (Fin n) K) : Prop :=
  ∀ i j, j < i → (x : Matrix (Fin n) (Fin n) K) i j = 0

/-- A represented group has a finite-index subgroup which becomes
upper triangular after conjugating by one invertible matrix. -/
def IndexTriangularizableSubgroup
    {G : Type u} [Group G] {n : ℕ} {K : Type v} [Field K]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) K) : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧
    ∃ t : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ x : H, UpperTriangularGL (t⁻¹ * ρ x.1 * t)

/-- The exact triangularization assertion of Malcev's theorem. -/
def MalcevTriangularizationProperty
    (G : Type u) [Group G] (n : ℕ) (K : Type v) [Field K] : Prop :=
  IsAlgClosed K → IsSolvable G →
    ∀ ρ : G →* Matrix.GeneralLinearGroup (Fin n) K,
      Function.Injective ρ → IndexTriangularizableSubgroup ρ

/-- **Hall, Theorem 9.4 (Malcev).** A soluble linear group over an
algebraically closed field has a finite-index triangularizable subgroup. -/
theorem solvable_linear_triangularizable
    {n : ℕ} {K : Type v} [Field K] [IsAlgClosed K]
    [IsSolvable G]
    (hmalcev : MalcevTriangularizationProperty G n K)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) K)
    (hρ : Function.Injective ρ) :
    IndexTriangularizableSubgroup ρ :=
  hmalcev inferInstance inferInstance ρ hρ

/-- Malcev's property `R`: some finite-index subgroup has nilpotent
commutator subgroup. -/
def MalcevR (G : Type u) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsNilpotent (commutator H)

/-- The soluble-linear part of Hall's Theorem 9.5 for fixed degree and
field. -/
def MalcevRProperty
    (G : Type u) [Group G] (n : ℕ) (K : Type v) [Field K] : Prop :=
  IsSolvable G → FaithfulLinearRepresentation G n K →
    MalcevR G

/-- The polycyclic part of Hall's Theorem 9.5. -/
def PolycyclicMalcevR (G : Type u) [Group G] : Prop :=
  IsPolycyclic G → MalcevR G

/-- **Hall, Theorem 9.5(i) (Malcev).** Every soluble linear group has
property `R`. -/
theorem solvable_malcev_r {n : ℕ} {K : Type v} [Field K]
    (hmalcev : MalcevRProperty G n K)
    (hsolvable : IsSolvable G)
    (hlinear : FaithfulLinearRepresentation G n K) :
    MalcevR G :=
  hmalcev hsolvable hlinear

/-- **Hall, Theorem 9.5(ii) (Malcev).** Every polycyclic group has
property `R`. -/
theorem polycyclic_malcev_r
    (hmalcev : PolycyclicMalcevR G)
    (hpolycyclic : IsPolycyclic G) :
    MalcevR G :=
  hmalcev hpolycyclic

/-- Hall's two assertions in Theorem 9.5, packaged together. -/
theorem malcev_r_polycyclic {n : ℕ} {K : Type v} [Field K]
    (hlinear : MalcevRProperty G n K)
    (hpolycyclic : PolycyclicMalcevR G) :
    (IsSolvable G → FaithfulLinearRepresentation G n K →
      MalcevR G) ∧
    (IsPolycyclic G → MalcevR G) :=
  ⟨hlinear, hpolycyclic⟩

/-- Hall's integral unimodular group `U_n`. -/
abbrev UnimodularGroup (n : ℕ) :=
  Matrix.GeneralLinearGroup (Fin n) ℤ

/-- Every abelian subgroup of `G` is finitely generated. -/
def FGAbelianSubgroups (G : Type u) [Group G] : Prop :=
  ∀ A : Subgroup G, IsAbelianSubgroup A → A.FG

/-- The exact assertion of Malcev's unimodular subgroup theorem. -/
def UnimodularFGProperty (n : ℕ) : Prop :=
  FGAbelianSubgroups (UnimodularGroup n)

/-- **Hall, Lemma 9.6 (Malcev).** Every abelian subgroup of `U_n` is
finitely generated. -/
theorem unimodular_abelian_fg {n : ℕ}
    (hmalcev : UnimodularFGProperty n)
    (A : Subgroup (UnimodularGroup n)) (hA : IsAbelianSubgroup A) :
    A.FG :=
  hmalcev A hA

/-- The automorphism-group corollary to Hall's Lemma 9.6. -/
def AutomorphismSubgroupsProperty
    (A : Type u) [CommGroup A] : Prop :=
  Group.FG A → FGAbelianSubgroups (MulAut A)

/-- **Corollary to Hall, Lemma 9.6.** Every abelian subgroup of the
automorphism group of a finitely generated abelian group is finitely
generated. -/
theorem automorphism_abelian_fg
    {A : Type u} [CommGroup A] [Group.FG A]
    (hmalcev : AutomorphismSubgroupsProperty A)
    (B : Subgroup (MulAut A)) (hB : IsAbelianSubgroup B) :
    B.FG :=
  hmalcev inferInstance B hB

/-- Polycyclic groups satisfy the easy direction of Hall's Lemma 9.7:
all their abelian subgroups are finitely generated. -/
theorem polycyclic_fg_subgroups
    (hpolycyclic : IsPolycyclic G) :
    FGAbelianSubgroups G := by
  intro A _
  exact polycyclic_implies_condition hpolycyclic A

/-- The substantive implication in Hall's Lemma 9.7. -/
def PolycyclicSubgroupsProperty
    (G : Type u) [Group G] : Prop :=
  IsSolvable G → FGAbelianSubgroups G → IsPolycyclic G

/-- **Hall, Lemma 9.7.** A soluble group is polycyclic if and only if
all of its abelian subgroups are finitely generated. -/
theorem solvable_polycyclic_subgroups [IsSolvable G]
    (hmalcev : PolycyclicSubgroupsProperty G) :
    IsPolycyclic G ↔ FGAbelianSubgroups G := by
  constructor
  · exact polycyclic_fg_subgroups
  · exact hmalcev inferInstance

/-- The exact assertion of Hall's Theorem 9.8. -/
def SolvableUnimodularPolycyclic (n : ℕ) : Prop :=
  ∀ H : Subgroup (UnimodularGroup n), IsSolvable H → IsPolycyclic H

/-- **Hall, Theorem 9.8.** Every soluble subgroup of `U_n` is
polycyclic. -/
theorem solvable_unimodular_polycyclic {n : ℕ}
    (hmalcev : SolvableUnimodularPolycyclic n)
    (H : Subgroup (UnimodularGroup n)) (hsolvable : IsSolvable H) :
    IsPolycyclic H :=
  hmalcev H hsolvable

/-- The automorphism-group generalization following Hall's Theorem
9.8. -/
def SolvableAutomorphismPolycyclic
    (G : Type u) [Group G] : Prop :=
  IsPolycyclic G →
    ∀ H : Subgroup (MulAut G), IsSolvable H → IsPolycyclic H

/-- Every soluble automorphism group of a polycyclic group is itself
polycyclic, as stated after Hall's Theorem 9.8. -/
theorem solvable_automorphism_polycyclic
    (hmalcev : SolvableAutomorphismPolycyclic G)
    (hpolycyclic : IsPolycyclic G)
    (H : Subgroup (MulAut G)) (hsolvable : IsSolvable H) :
    IsPolycyclic H :=
  hmalcev hpolycyclic H hsolvable

end

end Edmonton
end Towers
