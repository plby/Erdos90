import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Milne, Class Field Theory, Statement II.2.4

A short exact sequence of `G`-modules induces a functorial long exact sequence
in group homology.
-/

namespace Submission.CField.TCohomo

open CategoryTheory

variable {G : Type} [Group G]

/-- The connecting homomorphism in the long exact homology sequence associated
to a short exact sequence. -/
noncomputable abbrev groupHomologyConnecting
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  groupHomology.δ hX i j hij

/-- **Statement II.2.4, exactness at `H_j(G,X₁)`.** -/
theorem homology_long_exact₁
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    {i j : ℕ} (hij : j + 1 = i) :
    (groupHomology.mapShortComplex₁ hX hij).Exact :=
  groupHomology.mapShortComplex₁_exact hX hij

/-- **Statement II.2.4, exactness at `H_i(G,X₂)`.** -/
theorem homology_long_exact₂
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (i : ℕ) :
    (groupHomology.mapShortComplex₂ X i).Exact :=
  groupHomology.mapShortComplex₂_exact hX i

/-- **Statement II.2.4, exactness at `H_i(G,X₃)`.** -/
theorem homology_long_exact₃
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    {i j : ℕ} (hij : j + 1 = i) :
    (groupHomology.mapShortComplex₃ hX hij).Exact :=
  groupHomology.mapShortComplex₃_exact hX hij

/-- The degree-zero map `H₀(G,X₂) ⟶ H₀(G,X₃)` is the final surjection in
the long exact sequence. -/
theorem epi_homology_zero
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) :
    Epi (groupHomology.map (MonoidHom.id G) X.g 0) := by
  letI := hX.epi_g
  infer_instance

/-- **Statement II.2.4, functoriality.** A morphism of short exact sequences
commutes with the connecting homomorphisms in every degree. -/
theorem homology_connecting_naturality
    {X Y : ShortComplex (Rep ℤ G)} (φ : X ⟶ Y)
    (hX : X.ShortExact) (hY : Y.ShortExact)
    {i j : ℕ} (hij : j + 1 = i) :
    groupHomologyConnecting hX i j hij ≫
        groupHomology.map (MonoidHom.id G) φ.τ₁ j =
      groupHomology.map (MonoidHom.id G) φ.τ₃ i ≫
        groupHomologyConnecting hY i j hij := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((groupHomology.chainsFunctor ℤ G).mapShortComplex.map φ)
    (groupHomology.map_chainsFunctor_shortExact hX)
    (groupHomology.map_chainsFunctor_shortExact hY) i j hij

end Submission.CField.TCohomo
