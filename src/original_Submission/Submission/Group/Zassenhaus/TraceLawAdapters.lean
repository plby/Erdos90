import Submission.Group.Zassenhaus.TriangularGHLaw
import Submission.Group.Zassenhaus.CompatiblePacketRouting

/-!
# Free-truncation trace-law adapters

The arbitrary-depth collection theorem in `FinitePGroupCollection` uses the
classical Hall-Petresco Lemma 4 as a trace-law input.  This file records the
checked bridges from two existing formal interfaces to that input:

* a direct family of bare `FExp`s;
* the operational-compatible collection kernels that construct such
  expansions.
-/

namespace Submission
namespace TCTex

universe u

open CSAdmiss
open CDAggreg
open CSAggreg

/--
A uniform proof of Hall-Petresco Lemma 4 gives the trace law used in the free
lower-central truncation collection argument.
-/
theorem free_law_expansion
    (p d n : ℕ) [Fact p.Prime]
    (collectionExistence :
      ∀ M N : ℕ, 0 < M → 0 < N →
        Nonempty (HACoeff.FExp M N)) :
    FreeTruncationLaw.{u} p d n := by
  intro x y a b
  exact
    HACoeff.nonempty_trace
      collectionExistence p x y a b

/--
The admissible operational collection kernel constructs the `FExp`
input needed by the trace law.
-/
theorem law_admissible_collection
    (p d n : ℕ) [Fact p.Prime]
    (kernel : OCAdmissa) :
    FreeTruncationLaw.{u} p d n :=
  free_law_expansion p d n <| by
    intro M N _hM _hN
    exact ⟨kernel.freeExpansion M N⟩

/--
Diagonal shape-block certificates imply the admissible operational kernel, and
hence the trace law.
-/
theorem law_diagonal_collection
    (p d n : ℕ) [Fact p.Prime]
    (kernel : ODColl) :
    FreeTruncationLaw.{u} p d n :=
  law_admissible_collection p d n
    kernel.admissibleCollectionKernel

/--
Signed-block certificates also imply the admissible operational kernel, and
hence the trace law.
-/
theorem free_truncation_law
    (p d n : ℕ) [Fact p.Prime]
    (kernel : OCColl) :
    FreeTruncationLaw.{u} p d n :=
  law_admissible_collection p d n
    kernel.admissibleCollectionKernel

end TCTex
end Submission
