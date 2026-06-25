import Towers.ClassField.CyclicIdeles.AlgebraicIdeleCohomology
import Towers.ClassField.CyclotomicBrauer.IdeleClassRepresentation
import Towers.ClassField.HasseNorm.Class1Vanishing
import Towers.ClassField.HasseNorm.HCompletionProduct

/-!
# The unconditional finite case of Theorem VII.7.1

This file supplies the two earlier results used in Milne's proof rather than
retaining them as hypotheses: Theorem VII.5.1 gives `H¹(G,C_L)=0`, and the
completed restricted-product argument for Proposition VII.2.5(b) gives the
direct-sum decomposition of `H²(G,I_L)`.
-/

namespace Towers.CField.CBrauer

open CategoryTheory CategoryTheory.Limits groupCohomology
open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.CIdeles
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The direct sum of the degree-two cohomology groups of one chosen
completion of `L` above every place of `K`. -/
abbrev ResizedDirectSum
    (completion : HasseCompletionData K L) :=
  DirectSum (NumberFieldPlace K) (fun v ↦
    H2 (chosenUnitsRepresentation
      (K := K) (L := L) completion v))

/-- Proposition VII.2.5(b), followed placewise by Shapiro, in exactly the
form used in Theorem VII.7.1. -/
noncomputable def resizedLocalDecomposition
    (completion : HasseCompletionData K L) :
    H2 (resizedConcreteRepresentation K L) ≃+
      ResizedDirectSum completion :=
  resizedStabilizerDecomposition completion
    (resizedHDecomposition (K := K) (L := L))

/-- The canonical finite global-to-local map on degree-two cohomology,
using the harmless coefficient-ring resizing needed to keep all objects in
one universe. -/
noncomputable def resizedGlobal2
    (completion : HasseCompletionData K L) :
    H2 (resizedRepresentation K L) →+
      ResizedDirectSum completion :=
  (resizedLocalDecomposition completion).toAddMonoidHom.comp
    (groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedShortComplex K L).f 2).hom.toAddMonoidHom

/-- **Theorem VII.7.1, finite case.**  For every finite Galois extension
of number fields and every simultaneous choice of prolongations, the
canonical map

`H²(L/K) → ⨁ v, H²(Lᵛ/K_v)`

is injective.  There are no auxiliary vanishing or decomposition
hypotheses in this statement. -/
theorem finite_unconditional
    (completion : HasseCompletionData K L) :
    Function.Injective (resizedGlobal2 completion) := by
  have hExact := resized_short_exact K L
  have hH1 := short_complex_3
    ideleCohomologyClaims K L
  have hInjective := h_localization_third
    hExact hH1 (resizedLocalDecomposition completion)
  simpa only [resizedGlobal2,
    AddMonoidHom.coe_comp, Function.comp_apply] using hInjective

end

end Towers.CField.CBrauer
