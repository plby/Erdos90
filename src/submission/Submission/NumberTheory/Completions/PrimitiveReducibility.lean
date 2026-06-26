import Submission.ClassField.IdeleCohomology.CompletionProductAction

/-!
# Reducibility of a primitive polynomial over a completion

A primitive element whose base absolute value has more than one extension
cannot have irreducible minimal polynomial after passage to the completion.
Indeed, irreducibility would make the type of completed irreducible factors a
subsingleton, contrary to the place-factor correspondence.
-/

namespace Submission.NumberTheory.Milne

open AbsoluteValue Polynomial
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- If a nontrivial absolute value of `K` has more than one extension to
`L = K[alpha]`, then the minimal polynomial of `alpha` becomes reducible over
the completion of `K`.

The ultrametric completion instance is the hypothesis required by the
nonarchimedean place-factor correspondence. -/
theorem mapped_minpoly_above
    (v : AbsoluteValue K ℝ) [IsUltrametricDist v.Completion]
    [Fact v.IsNontrivial] [Algebra.IsSeparable K L]
    (alpha : L) (halpha : Algebra.adjoin K {alpha} = ⊤)
    (hplaces : 1 < Nat.card (CompletionPlacesAbove (L := L) v)) :
    ¬ Irreducible ((minpoly K alpha).map (completionEmbedding v)) := by
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extensions v alpha halpha
  intro hirr
  have hmonic : ((minpoly K alpha).map (completionEmbedding v)).Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral alpha)).map
      (completionEmbedding v)
  have hfactors : Subsingleton (CompletedMinpolyFactor v alpha) := ⟨by
    intro g h
    apply Subtype.ext
    have hg : g.1 = (minpoly K alpha).map (completionEmbedding v) :=
      eq_of_monic_of_associated g.2.2.1 hmonic
        (g.2.1.associated_of_dvd hirr g.2.2.2)
    have hh : h.1 = (minpoly K alpha).map (completionEmbedding v) :=
      eq_of_monic_of_associated h.2.2.1 hmonic
        (h.2.1.associated_of_dvd hirr h.2.2.2)
    exact hg.trans hh.symm⟩
  let e := completedMinpolyExtensions v alpha halpha
  have hplacesSubsingleton :
      Subsingleton (CompletionPlacesAbove (L := L) v) :=
    e.subsingleton_congr.mp hfactors
  have hcard : Nat.card (CompletionPlacesAbove (L := L) v) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hplacesSubsingleton
  exact (not_lt_of_ge hcard) hplaces

end

end Submission.NumberTheory.Milne
