import Towers.ClassField.ReciprocityExistence.FiniteDensePoints

/-!
# Dense agreement of the two finite-orbit completion maps

The maps agree first on the embedded global field and then everywhere by
continuity and density.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Two continuous ring homomorphisms agreeing on a dense map are equal.
Keeping the density argument independent of the completion-place indices
prevents the final dependent ring-hom equality below from re-elaborating the
entire prime-adic target while proving function extensionality. -/
private theorem ring_continuous_range
    {A B X : Type*} [Semiring A] [Semiring B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (i : X → A) (hi : DenseRange i)
    (f g : A →+* B) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f (i x) = g (i x)) : f = g := by
  apply DFunLike.ext _ _
  intro z
  exact congrFun (hi.equalizer hf hg (funext h)) z

set_option maxHeartbeats 5000000 in
-- Continuity on completions and agreement on a dense subfield elaborate together.
set_option maxRecDepth 100000 in
-- Continuity and dense agreement are already opaque checked facts.
/-- The literal-prime and canonical presentations are the same ring map. -/
theorem base_chosen_adic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    baseChosenAdic
        (K := K) (L := L) P w =
      chosenAdicDirect
        (K := K) (L := L) P w := by
  apply ring_continuous_range
    (completionEmbedding (FinitePlace.mk P).val)
    (dense_range_embedding (FinitePlace.mk P).val)
    _ _
    (chosen_adic_continuous
      (K := K) (L := L) P w)
    (chosen_direct_continuous
      (K := K) (L := L) P w)
  exact base_chosen_embedding
    (K := K) (L := L) P w

end


end Towers.CField.RExist
