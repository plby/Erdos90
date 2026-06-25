import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree


/-!
# Explicit transgression classes

This file develops the elementary factor-set construction used in
Efrat--Chapman, Section 9.  It avoids any appeal to a Hochschild--Serre API:
for a normal subgroup `N` of a group `F`, a quotient section produces the
usual factor set, and every conjugation-invariant additive homomorphism
`N → R` produces an actual class in `H²(F/N, R)`.
-/

noncomputable section

namespace EChapma
namespace MTransg

universe u

variable {F R : Type u} [Group F] [CommRing R]
variable (N : Subgroup F) [N.Normal]

/-- The quotient used by the presentation transgression. -/
abbrev Quotient := F ⧸ N

local instance quotientSMul : SMul (Quotient N) R where
  smul _ r := r

omit [CommRing R] [N.Normal] in
@[simp]
theorem quotient_smul (q : Quotient N) (r : R) : q • r = r :=
  rfl

/-- A choice of representative in `F` for every quotient element. -/
def quotientSection (q : Quotient N) : F :=
  Classical.choose (QuotientGroup.mk'_surjective N q)

@[simp]
theorem quotientSection_spec (q : Quotient N) :
    QuotientGroup.mk' N (quotientSection N q) = q :=
  Classical.choose_spec (QuotientGroup.mk'_surjective N q)

/-- Conjugation by an ambient group element, restricted to a normal
subgroup. -/
def normalConjugate (g : F) (x : N) : N :=
  ⟨g * x.1 * g⁻¹,
    (inferInstance : N.Normal).conj_mem x.1 x.2 g⟩

/-- Additive homomorphisms on `N` fixed by ambient conjugation. -/
def invariantHom : Submodule R (Additive N →+ R) where
  carrier := {f | ∀ g x, f (Additive.ofMul (normalConjugate N g x)) =
      f (Additive.ofMul x)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a x
    simp [hf a x, hg a x]
  smul_mem' := by
    intro r f hf a x
    simp [hf a x]

/-- The factor set associated to the chosen quotient section. -/
def factorSet (q r : Quotient N) : N :=
  ⟨quotientSection N q * quotientSection N r *
      (quotientSection N (q * r))⁻¹,
    (QuotientGroup.eq_one_iff _).mp (by
      change
        QuotientGroup.mk' N (quotientSection N q) *
              QuotientGroup.mk' N (quotientSection N r) *
              (QuotientGroup.mk' N
                (quotientSection N (q * r)))⁻¹ =
          1
      rw [quotientSection_spec, quotientSection_spec,
        quotientSection_spec]
      group)⟩

/-- The standard factor-set identity. -/
theorem factor_set_mul
    (q r s : Quotient N) :
    factorSet N q r * factorSet N (q * r) s =
      normalConjugate N (quotientSection N q) (factorSet N r s) *
        factorSet N q (r * s) := by
  apply Subtype.ext
  simp only [factorSet, normalConjugate, Subgroup.coe_mul,
    Subgroup.coe_mk]
  group

/-- The factor-set cochain attached to an invariant homomorphism. -/
def transgressionCochain
    (f : invariantHom (R := R) N) :
    Quotient N × Quotient N → R :=
  fun qr => f.1 (Additive.ofMul (factorSet N qr.1 qr.2))

theorem transgression_cochain_cocycle
    (f : invariantHom (R := R) N) :
    groupCohomology.IsCocycle₂
      (transgressionCochain (R := R) N f) := by
  intro q r s
  change
    f.1 (Additive.ofMul (factorSet N (q * r) s)) +
        f.1 (Additive.ofMul (factorSet N q r)) =
      f.1 (Additive.ofMul (factorSet N r s)) +
        f.1 (Additive.ofMul (factorSet N q (r * s)))
  have h :=
    congrArg
      (fun x : N => f.1 (Additive.ofMul x))
      (factor_set_mul N q r s)
  have h' :
      f.1 (Additive.ofMul (factorSet N q r)) +
          f.1 (Additive.ofMul (factorSet N (q * r) s)) =
        f.1 (Additive.ofMul
            (normalConjugate N (quotientSection N q)
              (factorSet N r s))) +
          f.1 (Additive.ofMul (factorSet N q (r * s))) := by
    rw [← f.1.map_add, ← f.1.map_add]
    exact h
  calc
    f.1 (Additive.ofMul (factorSet N (q * r) s)) +
          f.1 (Additive.ofMul (factorSet N q r)) =
        f.1 (Additive.ofMul (factorSet N q r)) +
          f.1 (Additive.ofMul (factorSet N (q * r) s)) := add_comm _ _
    _ =
        f.1 (Additive.ofMul
            (normalConjugate N (quotientSection N q)
              (factorSet N r s))) +
          f.1 (Additive.ofMul (factorSet N q (r * s))) := h'
    _ =
        f.1 (Additive.ofMul (factorSet N r s)) +
          f.1 (Additive.ofMul (factorSet N q (r * s))) := by
            rw [f.2 (quotientSection N q) (factorSet N r s)]

/-- The factor-set cocycle as a low-degree group-cohomology cocycle. -/
def transgressionCocycle
    (f : invariantHom (R := R) N) :
    groupCohomology.cocycles₂
      (Rep.trivial R (Quotient N) R) :=
  ⟨transgressionCochain (R := R) N f, by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro q r s
    simpa using
      transgression_cochain_cocycle (R := R) N f q r s⟩

/-- The explicit transgression class in `H²(F/N, R)`. -/
def transgressionClass
    (f : invariantHom (R := R) N) :
    groupCohomology.H2 (Rep.trivial R (Quotient N) R) :=
  groupCohomology.H2π (Rep.trivial R (Quotient N) R)
    (transgressionCocycle (R := R) N f)

/-- The factor-set cocycle depends linearly on the invariant homomorphism. -/
def transgressionCocycleLinear :
    invariantHom (R := R) N →ₗ[R]
      groupCohomology.cocycles₂
        (Rep.trivial R (Quotient N) R) where
  toFun := transgressionCocycle (R := R) N
  map_add' := by
    intro f g
    ext q r
    rfl
  map_smul' := by
    intro a f
    ext q r
    rfl

/-- The low-degree coboundaries, regarded as a submodule of the
2-cocycles. -/
def coboundariesInCocycles :
    Submodule R
      (groupCohomology.cocycles₂
        (Rep.trivial R (Quotient N) R)) where
  carrier := {c |
    (c.1 : Quotient N × Quotient N → R) ∈
      groupCohomology.coboundaries₂
        (Rep.trivial R (Quotient N) R)}
  zero_mem' := by
    change
      (0 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R)
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    change
      ((f + g).1 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R)
    change
      (f.1 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R) at hf
    change
      (g.1 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R) at hg
    exact Submodule.add_mem _ hf hg
  smul_mem' := by
    intro r f hf
    change
      ((r • f).1 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R)
    change
      (f.1 : Quotient N × Quotient N → R) ∈
        groupCohomology.coboundaries₂
          (Rep.trivial R (Quotient N) R) at hf
    exact Submodule.smul_mem _ r hf

/-- The explicit low-degree model `Z²/B²` of `H²(F/N,R)`. -/
abbrev ExplicitH2 :=
  groupCohomology.cocycles₂
      (Rep.trivial R (Quotient N) R) ⧸
    coboundariesInCocycles (R := R) N

/-- The factor-set transgression in the explicit quotient model of `H²`. -/
def explicitTransgressionLinear :
    invariantHom (R := R) N →ₗ[R] ExplicitH2 (R := R) N :=
  (Submodule.mkQ (coboundariesInCocycles (R := R) N)).comp
    (transgressionCocycleLinear (R := R) N)

/-- The remainder of an ambient element after removing the chosen quotient
representative. -/
def sectionRemainder (g : F) : N :=
  ⟨g * (quotientSection N (QuotientGroup.mk' N g))⁻¹,
    (QuotientGroup.eq_one_iff _).mp (by
      change
        QuotientGroup.mk' N g *
              (QuotientGroup.mk' N
                (quotientSection N (QuotientGroup.mk' N g)))⁻¹ =
          1
      rw [quotientSection_spec]
      group)⟩

theorem sectionRemainder_mul
    (g h : F) :
    sectionRemainder N (g * h) =
      sectionRemainder N g *
        normalConjugate N
          (quotientSection N (QuotientGroup.mk' N g))
          (sectionRemainder N h) *
        factorSet N
          (QuotientGroup.mk' N g)
          (QuotientGroup.mk' N h) := by
  apply Subtype.ext
  simp only [sectionRemainder, normalConjugate, factorSet,
    Subgroup.coe_mul, Subgroup.coe_mk]
  rw [map_mul]
  group

/-- If a transgression cocycle is a coboundary, its defining invariant
homomorphism extends to the ambient group. -/
theorem extension_coboundary
    (f : invariantHom (R := R) N)
    (h :
      groupCohomology.IsCoboundary₂
        (transgressionCochain (R := R) N f)) :
    ∃ b : Additive F →+ R,
      ∀ x : N, b (Additive.ofMul x.1) = f.1 (Additive.ofMul x) := by
  obtain ⟨a, ha⟩ := h
  let b : Additive F → R := fun g =>
    f.1 (Additive.ofMul (sectionRemainder N g.toMul)) +
      a (QuotientGroup.mk' N g.toMul)
  have hbadd (g h : F) :
      b (Additive.ofMul (g * h)) =
        b (Additive.ofMul g) + b (Additive.ofMul h) := by
    dsimp [b]
    rw [sectionRemainder_mul]
    let u := sectionRemainder N g
    let v :=
      normalConjugate N
        (quotientSection N (QuotientGroup.mk' N g))
        (sectionRemainder N h)
    let w :=
      factorSet N
        (QuotientGroup.mk' N g)
        (QuotientGroup.mk' N h)
    have hfprod :
        f.1 (Additive.ofMul (u * v * w)) =
          f.1 (Additive.ofMul u) +
            f.1 (Additive.ofMul v) +
              f.1 (Additive.ofMul w) := by
      calc
        f.1 (Additive.ofMul (u * v * w)) =
            f.1 (Additive.ofMul (u * v)) +
              f.1 (Additive.ofMul w) :=
          f.1.map_add (Additive.ofMul (u * v)) (Additive.ofMul w)
        _ =
            f.1 (Additive.ofMul u) +
                f.1 (Additive.ofMul v) +
              f.1 (Additive.ofMul w) := by
                exact congrArg
                  (fun z => z + f.1 (Additive.ofMul w))
                  (f.1.map_add
                    (Additive.ofMul u) (Additive.ofMul v))
    change
      f.1 (Additive.ofMul (u * v * w)) +
          a (QuotientGroup.mk' N (g * h)) =
        f.1 (Additive.ofMul u) +
            a (QuotientGroup.mk' N g) +
          (f.1 (Additive.ofMul (sectionRemainder N h)) +
            a (QuotientGroup.mk' N h))
    rw [hfprod]
    rw [f.2
      (quotientSection N (QuotientGroup.mk' N g))
      (sectionRemainder N h)]
    have hcob := ha
      (QuotientGroup.mk' N g)
      (QuotientGroup.mk' N h)
    change
      a (QuotientGroup.mk' N h) -
          a (QuotientGroup.mk' N (g * h)) +
          a (QuotientGroup.mk' N g) =
        f.1
          (Additive.ofMul
            (factorSet N
              (QuotientGroup.mk' N g)
              (QuotientGroup.mk' N h))) at hcob
    rw [← hcob]
    abel
  let bhom : Additive F →+ R := {
    toFun := b
    map_zero' := by
      have hzero := hbadd 1 1
      have hone : Additive.ofMul (1 : F) = 0 := rfl
      have honeMul : Additive.ofMul ((1 : F) * 1) = 0 := by
        rw [mul_one]
        exact hone
      rw [hone, honeMul] at hzero
      apply add_left_cancel (a := b 0)
      simpa using hzero.symm
    map_add' := by
      intro g h
      exact hbadd g.toMul h.toMul
  }
  refine ⟨bhom, ?_⟩
  intro x
  have hquot :
      QuotientGroup.mk' N x.1 = 1 :=
    (QuotientGroup.eq_one_iff x.1).mpr x.2
  have hdecomp :
      sectionRemainder N x.1 =
        x * sectionRemainder N 1 := by
    apply Subtype.ext
    simp [sectionRemainder, hquot]
  have hzero : bhom (Additive.ofMul (1 : F)) = 0 := map_zero bhom
  change
    f.1 (Additive.ofMul (sectionRemainder N x.1)) +
        a (QuotientGroup.mk' N x.1) =
      f.1 (Additive.ofMul x)
  rw [hquot, hdecomp]
  have hfdecomp :=
    f.1.map_add
      (Additive.ofMul x)
      (Additive.ofMul (sectionRemainder N 1))
  change
    f.1 (Additive.ofMul (x * sectionRemainder N 1)) =
      f.1 (Additive.ofMul x) +
        f.1 (Additive.ofMul (sectionRemainder N 1)) at hfdecomp
  rw [hfdecomp]
  change
    f.1 (Additive.ofMul x) +
          f.1 (Additive.ofMul (sectionRemainder N 1)) +
        a 1 =
      f.1 (Additive.ofMul x)
  have hconstant :
      f.1 (Additive.ofMul (sectionRemainder N 1)) + a 1 = 0 := by
    exact hzero
  rw [add_assoc, hconstant, add_zero]

set_option maxHeartbeats 1000000 in
-- The quotient witness carries several nested subtype coercions.
/-- Injectivity criterion for explicit transgression: it is enough that every
ambient additive homomorphism vanish on `N`. -/
theorem explicit_transgression_injective
    (hvanish :
      ∀ b : Additive F →+ R,
        ∀ x : N, b (Additive.ofMul x.1) = 0) :
    Function.Injective
      (explicitTransgressionLinear (R := R) N) := by
  intro f g hfg
  have hzero :
      explicitTransgressionLinear (R := R) N (f - g) = 0 := by
    calc
      explicitTransgressionLinear (R := R) N (f - g) =
          explicitTransgressionLinear (R := R) N f -
            explicitTransgressionLinear (R := R) N g :=
        (explicitTransgressionLinear (R := R) N).map_sub f g
      _ = 0 := sub_eq_zero.mpr hfg
  change
    Submodule.Quotient.mk
        (transgressionCocycle (R := R) N (f - g)) =
      0 at hzero
  rw [Submodule.Quotient.mk_eq_zero] at hzero
  have hcob :
      groupCohomology.IsCoboundary₂
        (transgressionCochain (R := R) N (f - g)) := by
    obtain ⟨a, ha⟩ := hzero
    refine ⟨a, ?_⟩
    intro q r
    have hqr := congrFun ha (q, r)
    simpa [groupCohomology.d₁₂_hom_apply] using hqr
  obtain ⟨b, hb⟩ :=
    extension_coboundary (R := R) N (f - g) hcob
  apply Subtype.ext
  ext x
  have hdiff :
      (f - g).1 (Additive.ofMul x) = 0 :=
    (hb x).symm.trans (hvanish b x)
  exact sub_eq_zero.mp hdiff

end MTransg
end EChapma
