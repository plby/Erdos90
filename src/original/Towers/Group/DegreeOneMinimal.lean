import Towers.Group.DegreeOnePresentation
import Towers.Group.FilteredPresentation
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Degree-one minimality for presentations

This file packages the degree-one criteria proved in `DegreeOnePresentation` under
short predicate names.  A presentation is degree-one minimal when the generator
classes are linearly independent in the mod-`p` Frattini quotient; equivalently,
its relators have no degree-one exponent-vector part.
-/

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- Degree-one minimality: the generator map to the mod-`p` Frattini quotient is injective. -/
def degreeOneMinimal : Prop := Function.Injective (degreeOneLinear p P)

/-- Linear independence of the degree-one generator classes. -/
def degreeGeneratorIndependent : Prop :=
  LinearIndependent (ZMod p) (degreeGeneratorClass p P)

/-- Minimality is the same as linear independence of the generator classes. -/
theorem degree_minimal_independent :
    degreeOneMinimal p P ↔ degreeGeneratorIndependent p P := by
  dsimp [degreeOneMinimal, degreeGeneratorIndependent, degreeOneLinear]
  rw [linearIndependent_iff_ker]
  exact LinearMap.ker_eq_bot.symm

/-- Minimality is equivalent to zero relator exponent-span. -/
theorem degree_minimal_bot :
    degreeOneMinimal p P ↔ degreeRelatorSpan p P = ⊥ :=
  degree_span_bot p P

/-- Constructor for minimality from independence of the generator classes. -/
theorem minimal_generator_independent
    (h : degreeGeneratorIndependent p P) : degreeOneMinimal p P :=
  (degree_minimal_independent p P).2 h

/-- Generator-class independence extracted from degree-one minimality. -/
theorem generator_independent_minimal
    (h : degreeOneMinimal p P) : degreeGeneratorIndependent p P :=
  (degree_minimal_independent p P).1 h

/-- Constructor for minimality from vanishing of the degree-one relator span. -/
theorem minimal_span_bot
    (h : degreeRelatorSpan p P = ⊥) : degreeOneMinimal p P :=
  (degree_minimal_bot p P).2 h

/-- The degree-one relator span vanishes in a minimal presentation. -/
theorem relator_bot_minimal
    (h : degreeOneMinimal p P) : degreeRelatorSpan p P = ⊥ :=
  (degree_minimal_bot p P).1 h

/-- Minimality is equivalent to every relator being exponent-vector silent. -/
theorem minimal_vector_silent :
    degreeOneMinimal p P ↔ exponentVectorSilent p P :=
  exponent_vector_silent p P

/-- A constructor for minimality from an explicit silence proof. -/
theorem degree_minimal_silent (h : exponentVectorSilent p P) :
    degreeOneMinimal p P :=
  (minimal_vector_silent p P).2 h

/-- In a degree-one minimal presentation, each relator has zero exponent vector. -/
theorem vector_silent_minimal (h : degreeOneMinimal p P) :
    exponentVectorSilent p P :=
  (minimal_vector_silent p P).1 h

end
end Presentation
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Degree-one minimality for a filtered presentation, ignoring the extra depth data. -/
def degreeOneMinimal : Prop :=
  FP.toPresentation.degreeOneMinimal p

/-- Generator-class independence for the underlying presentation of a filtered presentation. -/
def degreeGeneratorIndependent : Prop :=
  Presentation.degreeGeneratorIndependent p FP.toPresentation

/-- Exponent-vector silence for the underlying presentation of a filtered presentation. -/
def exponentVectorSilent : Prop :=
  Presentation.exponentVectorSilent p FP.toPresentation

/-- Filtered minimality is equivalent to independence of the underlying generator classes. -/
theorem degree_minimal_independent :
    FP.degreeOneMinimal ↔ FP.degreeGeneratorIndependent :=
  Presentation.degree_minimal_independent p FP.toPresentation

/-- Constructor for filtered minimality from generator-class independence. -/
theorem minimal_generator_independent
    (h : FP.degreeGeneratorIndependent) : FP.degreeOneMinimal :=
  (FP.degree_minimal_independent).2 h

/-- Extract generator-class independence from filtered minimality. -/
theorem generator_independent_minimal
    (h : FP.degreeOneMinimal) : FP.degreeGeneratorIndependent :=
  (FP.degree_minimal_independent).1 h

/-- The filtered wrapper inherits the same minimality/silence criterion. -/
theorem minimal_vector_silent :
    FP.degreeOneMinimal ↔ FP.exponentVectorSilent :=
  Presentation.minimal_vector_silent p FP.toPresentation

/-- Constructor for filtered degree-one minimality from exponent-vector silence. -/
theorem degree_minimal_silent
    (h : FP.exponentVectorSilent) : FP.degreeOneMinimal :=
  (FP.minimal_vector_silent).2 h

/-- Extract exponent-vector silence from filtered degree-one minimality. -/
theorem vector_silent_minimal
    (h : FP.degreeOneMinimal) : FP.exponentVectorSilent :=
  (FP.minimal_vector_silent).1 h

/-- Filtered minimality is equivalent to vanishing of the underlying relator span. -/
theorem degree_minimal_bot :
    FP.degreeOneMinimal ↔
      Presentation.degreeRelatorSpan p FP.toPresentation = ⊥ :=
  Presentation.degree_minimal_bot p FP.toPresentation

/-- Constructor for filtered minimality from vanishing of the underlying relator span. -/
theorem minimal_span_bot
    (h : Presentation.degreeRelatorSpan p FP.toPresentation = ⊥) :
    FP.degreeOneMinimal :=
  (FP.degree_minimal_bot).2 h

/-- The underlying relator span vanishes for a filtered minimal presentation. -/
theorem relator_bot_minimal
    (h : FP.degreeOneMinimal) :
    Presentation.degreeRelatorSpan p FP.toPresentation = ⊥ :=
  (FP.degree_minimal_bot).1 h

end
end FPres
end Towers
