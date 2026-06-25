import Submission.ClassField.HerbrandQuotients.HerbrandIsogeny
import Submission.ClassField.HerbrandQuotients.BaseChangeSpanning
import Submission.ClassField.HerbrandQuotients.FiniteAbovePlaces
import Submission.ClassField.HerbrandQuotients.PlaceLattice
import Submission.ClassField.HerbrandQuotients.UnitLogLattice
import Submission.ClassField.HerbrandQuotients.UnitLogHerbrand

/-!
# Reduced assembly for Proposition VII.3.1

Lemmas VII.3.2 and VII.3.4 are unconditional, so Proposition VII.3.1 now
retains only the two arithmetic lattice constructions from the source proof.
-/

namespace Submission.CField.HQuotie

open Submission.CField.ICohomo

universe u

/-- Compatibility wrapper using the now-proved Lemmas VII.3.2 and VII.3.4. -/
theorem permutation_spanning_lattices
    (hlattices : ArithmeticLatticesBridge.{u}) :
    PlacesHerbrandFormula.{u} :=
  above_places_lattices hlattices

/-- Lemma VII.3.5 is unconditional after scalar descent and the integral
rational-isomorphism comparison. -/
theorem stable_lattice_isogenies :
    (∀ (G V : Type u) [Group G] [Finite G] [IsCyclic G]
          [AddCommGroup V] [Module ℝ V]
          (rho : Representation ℝ G V)
          (M N : Submodule ℤ V)
          (hMstable : ∀ g x, x ∈ M → rho g x ∈ M)
          (hNstable : ∀ g x, x ∈ N → rho g x ∈ N),
          FullRealLattice M → FullRealLattice N →
            letI : Fintype G := Fintype.ofFinite G
            letI : CommGroup G := IsCyclic.commGroup
            let RM := stableLatticeRepresentation rho M hMstable
            let RN := stableLatticeRepresentation rho N hNstable
            ((DefinedHerbrandQuotient RM →
                ∃ q : ℚ,
                  HerbrandQuotientValue RM q ∧
                    HerbrandQuotientValue RN q) ∧
              (DefinedHerbrandQuotient RN →
                ∃ q : ℚ,
                  HerbrandQuotientValue RM q ∧
                    HerbrandQuotientValue RN q))) :=
  stable_representation_isogenies

/-- Proposition VII.3.1 is reduced to its two explicit arithmetic lattice
constructions. -/
theorem permutation_assembly_lattices
    (hlattices : ArithmeticLatticesBridge.{u}) :
    PlacesHerbrandFormula.{u} :=
  permutation_spanning_lattices hlattices

/-- With the place lattice discharged, Proposition VII.3.1 now requires
only Milne's logarithmic `T`-unit lattice. -/
theorem permutation_assembly_log
    (hlog : LogLatticeBridge.{u}) :
    PlacesHerbrandFormula.{u} :=
  permutation_assembly_lattices
    (arithmetic_lattices_lattice hlog)

/-- **Proposition VII.3.1.** For a cyclic extension and a finite set of
places containing all infinite places, the degree times the Herbrand
quotient of the corresponding `T`-unit group is the product of the orders of
the decomposition groups. -/
theorem placesHerbrandFormula :
    PlacesHerbrandFormula.{u} :=
  permutation_assembly_log
    logLatticeBridge

end Submission.CField.HQuotie
