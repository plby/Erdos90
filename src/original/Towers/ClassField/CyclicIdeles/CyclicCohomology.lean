import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Towers.ClassField.Shifting.LowTateCohomology

/-!
# Chapter VII, Section 5: cyclic cohomology in low degrees

Lemma 5.2 uses periodicity of the cohomology of a finite cyclic group.  The
periodic resolution is available in Mathlib and identifies odd cohomology
with the homology of

`A --(rho(g) - 1)--> A --N--> A`

and positive even cohomology with the homology of

`A --N--> A --(rho(g) - 1)--> A`.

The declarations below specialize these results to degrees one and two.  The
second complex is the numerator/denominator description of degree-zero Tate
cohomology used in Lemma 5.2.

The arithmetic statements of Theorem 5.1 and Lemmas 5.3--5.4 are formalized
in the subsequent source-statement files.  They use the actual idèle-class
representation, restriction and inflation, and the Herbrand quotient of
`C_L`; the declarations here remain the reusable cyclic-cohomology core.
-/

namespace Towers.CField.CIdeles

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- **Lemma VII.5.2, degree-one cyclic input.** For a finite cyclic group,
`H^1(G,A)` is computed by the odd part of the standard periodic complex. -/
noncomputable def cyclicHIso
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology A 1 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology :=
  Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by simp)

/-- **Lemma VII.5.2, degree-two cyclic input.** For a finite cyclic group,
`H^2(G,A)` is computed by the positive-even part of the standard periodic
complex.  This is the complex whose homology is degree-zero Tate cohomology. -/
noncomputable def cyclic2Iso
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology A 2 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
  Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by simp)

/-- Positive even cohomology of a finite cyclic group is two-periodic.  This
is the explicit degree-two/degree-four instance used implicitly in the
cyclic reduction arguments of Section 5. -/
noncomputable def cyclicIso4
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology A 2 ≅ groupCohomology A 4 :=
  (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by simp)).trans
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 4
      (by exact ⟨2, by norm_num⟩)).symm

end

end Towers.CField.CIdeles
