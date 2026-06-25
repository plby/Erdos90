import Towers.Group.Presentation
import Towers.Group.FrattiniFunctor
import Towers.Group.DegreeOne
import Towers.Group.ExponentVector
import Towers.Group.ExponentVectorFrattini
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

open scoped commutatorElement

/-!
# Degree-one linear map attached to a presentation

The images of presentation generators in the mod-`p` Frattini quotient give a canonical
linear map from the free `ZMod p`-module on the generator type.  Later relator/Fox
machinery will identify its kernel and refinements; this file only sets up the honest
bottom-layer map and its basic simp lemmas.
-/

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The free `ZMod p`-module on the generators of a presentation. -/
abbrev degreeFreeModule : Type _ := P.Gen →₀ ZMod p

instance : AddCommGroup (degreeFreeModule p P) := inferInstance
instance : Module (ZMod p) (degreeFreeModule p P) := inferInstance

/-- The class of a presentation generator in the additive mod-`p` Frattini quotient. -/
def degreeGeneratorClass (x : P.Gen) : mFAdditi p P.Group :=
  Additive.ofMul (mFQuot.mk p P.Group (P.of x))

/-- The linear map from the free module on generators to the degree-one quotient. -/
noncomputable def degreeOneLinear :
    degreeFreeModule p P →ₗ[ZMod p] mFAdditi p P.Group :=
  Finsupp.linearCombination (ZMod p) (degreeGeneratorClass p P)

@[simp] theorem degree_one_single (x : P.Gen) (a : ZMod p) :
    degreeOneLinear p P (Finsupp.single x a) =
      a • degreeGeneratorClass p P x := by
  exact Finsupp.linearCombination_single (R := ZMod p)
    (v := degreeGeneratorClass p P) a x

@[simp] theorem degree_linear_single (x : P.Gen) :
    degreeOneLinear p P (Finsupp.single x (1 : ZMod p)) =
      degreeGeneratorClass p P x := by
  simp [degree_one_single]

end

end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

@[simp] theorem degree_single_nat (x : P.Gen) (n : ℕ) :
    degreeOneLinear p P (Finsupp.single x (n : ZMod p)) =
      Additive.ofMul ((mFQuot.mk p P.Group (P.of x)) ^ n) := by
  rw [degree_one_single]
  exact smul_frattini_additive (p := p) (G := P.Group) n
    (mFQuot.mk p P.Group (P.of x))

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The multiplicative word map from the free group of a presentation to its degree-one quotient. -/
def degreeOneWord : P.Free →* mFQuot p P.Group :=
  (mFQuot.mk p P.Group).comp P.quotientMap

@[simp] theorem degree_word_rel {r : P.Free} (hr : r ∈ P.rels) :
    degreeOneWord p P r = 1 := by
  dsimp [degreeOneWord]
  rw [P.quotient_rel_one hr]
  simp

@[simp] theorem degree_word_gen (x : P.Gen) :
    degreeOneWord p P (FreeGroup.of x) =
      mFQuot.mk p P.Group (P.of x) := by
  rfl

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- Every element of the degree-one quotient lies in the span of the presentation generators. -/
theorem degree_generator_range (g : P.Group) :
    Additive.ofMul (mFQuot.mk p P.Group g) ∈
      LinearMap.range (degreeOneLinear p P) := by
  let L : Submodule (ZMod p) (mFAdditi p P.Group) :=
    LinearMap.range (degreeOneLinear p P)
  change Additive.ofMul (mFQuot.mk p P.Group g) ∈ L
  have hgTop : g ∈ Subgroup.closure (Set.range P.of) := by
    rw [P.closure_range_of]
    trivial
  refine Subgroup.closure_induction (k := Set.range P.of)
    (p := fun z _ => Additive.ofMul (mFQuot.mk p P.Group z) ∈ L)
    ?mem ?one ?mul ?inv hgTop
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨Finsupp.single x (1 : ZMod p), ?_⟩
    simp [degreeGeneratorClass]
  · simp [L]
  · intro x y hx hy hxL hyL
    change Additive.ofMul (mFQuot.mk p P.Group (x * y)) ∈ L
    rw [map_mul]
    change Additive.ofMul (mFQuot.mk p P.Group x) +
      Additive.ofMul (mFQuot.mk p P.Group y) ∈ L
    exact L.add_mem hxL hyL
  · intro x hx hxL
    change Additive.ofMul (mFQuot.mk p P.Group x⁻¹) ∈ L
    rw [map_inv]
    change - Additive.ofMul (mFQuot.mk p P.Group x) ∈ L
    exact L.neg_mem hxL

/-- The generator degree-one map is surjective. -/
theorem degree_linear_surjective :
    Function.Surjective (degreeOneLinear p P) := by
  intro x
  induction x using Additive.rec with
  | ofMul q =>
    refine QuotientGroup.induction_on q ?_
    intro g
    exact degree_generator_range p P g

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The exponent vector realizes the degree-one word map after applying the generator linear map. -/
theorem degree_exponent_vector (w : P.Free) :
    degreeOneLinear p P (exponentVector p P.Gen w) =
      Additive.ofMul (degreeOneWord p P w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp [degreeOneWord]
  | of x =>
      have hq : P.quotientMap (FreeGroup.of x) = P.of x := rfl
      simp [degreeOneWord, degreeGeneratorClass, hq]
  | inv_of x hx =>
      have hq : P.quotientMap (FreeGroup.of x) = P.of x := rfl
      simp [degreeOneWord, degreeGeneratorClass, hq]
  | mul u v hu hv =>
      simp [degreeOneWord, hu, hv]

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The mod-`p` exponent vector of any relator lies in the kernel of the degree-one map. -/
theorem vector_rel_ker {r : P.Free} (hr : r ∈ P.rels) :
    exponentVector p P.Gen r ∈ LinearMap.ker (degreeOneLinear p P) := by
  rw [LinearMap.mem_ker]
  rw [degree_exponent_vector]
  simp [degree_word_rel (p := p) (P := P) hr]

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The submodule generated by mod-`p` exponent vectors of relators. -/
def degreeRelatorSpan : Submodule (ZMod p) (degreeFreeModule p P) :=
  Submodule.span (ZMod p) (Set.image (fun r : P.Free => exponentVector p P.Gen r) P.rels)

/-- Replacing relators by the empty set gives the zero degree-one relator span. -/
@[simp] theorem degree_relators_empty :
    degreeRelatorSpan p (P.withRelators (∅ : Set P.Free)) = ⊥ := by
  dsimp [degreeRelatorSpan]
  simp

/-- Degree-one relator spans are monotone under enlarging a fixed relator set. -/
theorem degree_relators_mono {S T : Set P.Free} (hST : S ⊆ T) :
    degreeRelatorSpan p (P.withRelators S) ≤
      degreeRelatorSpan p (P.withRelators T) := by
  dsimp [degreeRelatorSpan]
  apply Submodule.span_mono
  intro v hv
  rcases hv with ⟨r, hr, rfl⟩
  exact ⟨r, hST hr, rfl⟩

/-- Equal fixed relator sets have equal degree-one relator spans. -/
theorem degree_relators_congr {S T : Set P.Free} (hST : S = T) :
    degreeRelatorSpan p (P.withRelators S) =
      degreeRelatorSpan p (P.withRelators T) := by
  subst T
  rfl

/-- The degree-one relator span of a union is the supremum of the two spans. -/
theorem degree_relators_union (S T : Set P.Free) :
    degreeRelatorSpan p (P.withRelators (S ∪ T)) =
      degreeRelatorSpan p (P.withRelators S) ⊔
        degreeRelatorSpan p (P.withRelators T) := by
  dsimp [degreeRelatorSpan]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · have hm : exponentVector p P.Gen r ∈
          Submodule.span (ZMod p)
            ((fun r : P.Free => exponentVector p P.Gen r) '' S) :=
        Submodule.subset_span ⟨r, hr, rfl⟩
      exact (le_sup_left : _ ≤
        (Submodule.span (ZMod p) ((fun r : P.Free => exponentVector p P.Gen r) '' S) ⊔
          Submodule.span (ZMod p) ((fun r : P.Free => exponentVector p P.Gen r) '' T))) hm
    · have hm : exponentVector p P.Gen r ∈
          Submodule.span (ZMod p)
            ((fun r : P.Free => exponentVector p P.Gen r) '' T) :=
        Submodule.subset_span ⟨r, hr, rfl⟩
      exact (le_sup_right : _ ≤
        (Submodule.span (ZMod p) ((fun r : P.Free => exponentVector p P.Gen r) '' S) ⊔
          Submodule.span (ZMod p) ((fun r : P.Free => exponentVector p P.Gen r) '' T))) hm
  · apply sup_le
    · apply Submodule.span_mono
      intro v hv
      rcases hv with ⟨r, hr, rfl⟩
      exact ⟨r, Or.inl hr, rfl⟩
    · apply Submodule.span_mono
      intro v hv
      rcases hv with ⟨r, hr, rfl⟩
      exact ⟨r, Or.inr hr, rfl⟩

/-- Adding a batch of relators adds (supremums) its degree-one exponent span. -/
theorem degree_relator_relators (S : Set P.Free) :
    degreeRelatorSpan p (P.addRelators S) =
      degreeRelatorSpan p P ⊔ degreeRelatorSpan p (P.withRelators S) := by
  dsimp [degreeRelatorSpan, addRelators]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · have hm : exponentVector p P.Gen r ∈
          Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' P.rels) :=
        Submodule.subset_span ⟨r, hr, rfl⟩
      exact (le_sup_left : _ ≤
        (Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' P.rels) ⊔
          Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' S))) hm
    · have hm : exponentVector p P.Gen r ∈
          Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' S) :=
        Submodule.subset_span ⟨r, hr, rfl⟩
      exact (le_sup_right : _ ≤
        (Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' P.rels) ⊔
          Submodule.span (ZMod p)
            ((fun r : FreeGroup P.Gen => exponentVector p P.Gen r) '' S))) hm
  · apply sup_le
    · apply Submodule.span_mono
      intro v hv
      rcases hv with ⟨r, hr, rfl⟩
      exact ⟨r, Or.inl hr, rfl⟩
    · apply Submodule.span_mono
      intro v hv
      rcases hv with ⟨r, hr, rfl⟩
      exact ⟨r, Or.inr hr, rfl⟩

/-- The degree-one span after adding relators is zero exactly when both old and new
batch spans are zero. -/
theorem degree_relators_bot (S : Set P.Free) :
    degreeRelatorSpan p (P.addRelators S) = ⊥ ↔
      degreeRelatorSpan p P = ⊥ ∧
        degreeRelatorSpan p (P.withRelators S) = ⊥ := by
  rw [degree_relator_relators]
  constructor
  · intro h
    constructor
    · apply le_antisymm
      · intro x hx
        have hle : degreeRelatorSpan p P ≤
            degreeRelatorSpan p P ⊔ degreeRelatorSpan p (P.withRelators S) :=
          le_sup_left
        have hx' : x ∈ degreeRelatorSpan p P ⊔
            degreeRelatorSpan p (P.withRelators S) := hle hx
        rw [h] at hx'
        simpa using hx'
      · exact bot_le
    · apply le_antisymm
      · intro x hx
        have hle : degreeRelatorSpan p (P.withRelators S) ≤
            degreeRelatorSpan p P ⊔ degreeRelatorSpan p (P.withRelators S) :=
          le_sup_right
        have hx' : x ∈ degreeRelatorSpan p P ⊔
            degreeRelatorSpan p (P.withRelators S) := hle hx
        rw [h] at hx'
        simpa using hx'
      · exact bot_le
  · rintro ⟨hP, hS⟩
    rw [hP, hS, bot_sup_eq]
    rfl

/-- The old relator span embeds into the span after adding relators. -/
theorem degree_span_relators (S : Set P.Free) :
    degreeRelatorSpan p P ≤ degreeRelatorSpan p (P.addRelators S) := by
  rw [degree_relator_relators]
  exact le_sup_left

/-- The newly added batch span embeds into the span after adding relators. -/
theorem degree_relators_add (S : Set P.Free) :
    degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p (P.addRelators S) := by
  rw [degree_relator_relators]
  exact le_sup_right

/-- Relator exponent vectors generate a submodule contained in the kernel of the degree-one map. -/
theorem degree_span_ker :
    degreeRelatorSpan p P ≤ LinearMap.ker (degreeOneLinear p P) := by
  dsimp [degreeRelatorSpan]
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hv with ⟨r, hr, rfl⟩
  exact vector_rel_ker p P hr

/-- The relation-quotient module obtained by imposing degree-one relator exponent sums. -/
abbrev dRQuot : Type _ :=
  degreeFreeModule p P ⧸ degreeRelatorSpan p P

/-- Equal degree-one relator spans on two fixed-generator relator replacements give
canonically equivalent relation quotients. -/
noncomputable def relation_relators_span
    {S T : Set P.Free}
    (h : degreeRelatorSpan p (P.withRelators S) =
      degreeRelatorSpan p (P.withRelators T)) :
    dRQuot p (P.withRelators S) ≃ₗ[ZMod p]
      dRQuot p (P.withRelators T) :=
  Submodule.quotEquivOfEq _ _ h

@[simp] theorem relators_span_mk
    {S T : Set P.Free}
    (h : degreeRelatorSpan p (P.withRelators S) =
      degreeRelatorSpan p (P.withRelators T))
    (v : degreeFreeModule p (P.withRelators S)) :
    relation_relators_span p P h
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  dsimp [relation_relators_span]
  exact Submodule.quotEquivOfEq_mk _ _ h v

@[simp] theorem degree_relators_mk
    {S T : Set P.Free}
    (h : degreeRelatorSpan p (P.withRelators S) =
      degreeRelatorSpan p (P.withRelators T))
    (v : degreeFreeModule p (P.withRelators T)) :
    (relation_relators_span p P h).symm
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  change Submodule.quotEquivOfEq _ _ h.symm (Submodule.Quotient.mk v) =
    Submodule.Quotient.mk v
  exact Submodule.quotEquivOfEq_mk _ _ h.symm v

/-- Equal fixed-generator relator sets give canonically equivalent relation quotients. -/
noncomputable def degree_relators_set
    {S T : Set P.Free} (hST : S = T) :
    dRQuot p (P.withRelators S) ≃ₗ[ZMod p]
      dRQuot p (P.withRelators T) :=
  relation_relators_span p P
    (degree_relators_congr p P hST)

@[simp] theorem relators_set_mk
    {S T : Set P.Free} (hST : S = T)
    (v : degreeFreeModule p (P.withRelators S)) :
    degree_relators_set p P hST
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  simp [degree_relators_set]

/-- The quotient map on degree-one relation modules induced by enlarging a fixed relator set. -/
noncomputable def relation_relators_subset {S T : Set P.Free}
    (hST : S ⊆ T) :
    dRQuot p (P.withRelators S) →ₗ[ZMod p]
      dRQuot p (P.withRelators T) :=
  Submodule.mapQ (degreeRelatorSpan p (P.withRelators S))
    (degreeRelatorSpan p (P.withRelators T))
    (LinearMap.id : degreeFreeModule p (P.withRelators S) →ₗ[ZMod p]
      degreeFreeModule p (P.withRelators S))
    (by
      intro x hx
      change x ∈ degreeRelatorSpan p (P.withRelators T)
      exact degree_relators_mono p P hST hx)

@[simp] theorem degree_subset_mk
    {S T : Set P.Free} (hST : S ⊆ T)
    (v : degreeFreeModule p (P.withRelators S)) :
    relation_relators_subset p P hST (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk v := by
  dsimp [relation_relators_subset]
  change Submodule.Quotient.mk v = Submodule.Quotient.mk v
  rfl

/-- Subset-induced quotient maps are functorial under composition. -/
@[simp] theorem degree_subset_comp
    {S T U : Set P.Free} (hST : S ⊆ T) (hTU : T ⊆ U) :
    (relation_relators_subset p P hTU).comp
        (relation_relators_subset p P hST) =
      relation_relators_subset p P
        (fun x hx => show x ∈ U from hTU (hST hx)) := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  change (relation_relators_subset p P hTU)
      (relation_relators_subset p P hST (Submodule.Quotient.mk v)) =
    relation_relators_subset p P
      (fun x hx => show x ∈ U from hTU (hST hx)) (Submodule.Quotient.mk v)
  dsimp [relation_relators_subset]
  rfl

/-- Enlarging a relator set gives a surjective map on relation quotients. -/
theorem relators_subset_surjective
    {S T : Set P.Free} (hST : S ⊆ T) :
    Function.Surjective (relation_relators_subset p P hST) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  refine ⟨Submodule.Quotient.mk v, ?_⟩
  change relation_relators_subset p P hST
      (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
  rfl

/-- Kernel of the quotient map induced by enlarging relators: it is the image of the
larger span in the smaller quotient. -/
theorem degree_subset_ker
    {S T : Set P.Free} (hST : S ⊆ T) :
    LinearMap.ker (relation_relators_subset p P hST) =
      (degreeRelatorSpan p (P.withRelators T)).map
        (Submodule.mkQ (degreeRelatorSpan p (P.withRelators S))) := by
  dsimp [relation_relators_subset]
  simpa using
    (Submodule.ker_mapQ (p := degreeRelatorSpan p (P.withRelators S))
      (q := degreeRelatorSpan p (P.withRelators T))
      (f := (LinearMap.id : degreeFreeModule p (P.withRelators S) →ₗ[ZMod p]
        degreeFreeModule p (P.withRelators S)))
      (by
        intro x hx
        change x ∈ degreeRelatorSpan p (P.withRelators T)
        exact degree_relators_mono p P hST hx))

/-- A representative lies in the kernel of the relator-enlargement quotient map exactly
when its vector already belongs to the larger relator span.  This is often more convenient
than rewriting by the submodule-image description of the kernel. -/
@[simp] theorem subset_mk_ker
    {S T : Set P.Free} (hST : S ⊆ T)
    (v : degreeFreeModule p (P.withRelators S)) :
    Submodule.Quotient.mk v ∈
        LinearMap.ker (relation_relators_subset p P hST) ↔
      v ∈ degreeRelatorSpan p (P.withRelators T) := by
  change relation_relators_subset p P hST
      (Submodule.Quotient.mk v) = 0 ↔ _
  rw [degree_subset_mk]
  exact (Submodule.Quotient.mk_eq_zero
    (p := degreeRelatorSpan p (P.withRelators T)))

/-- Two representatives have the same image under a relator-enlargement quotient map
exactly when their difference lies in the larger relator span. -/
@[simp] theorem relators_subset_mk
    {S T : Set P.Free} (hST : S ⊆ T)
    (v w : degreeFreeModule p (P.withRelators S)) :
    relation_relators_subset p P hST
        (Submodule.Quotient.mk v) =
      relation_relators_subset p P hST
        (Submodule.Quotient.mk w) ↔
      -v + w ∈ degreeRelatorSpan p (P.withRelators T) := by
  rw [degree_subset_mk,
    degree_subset_mk]
  exact (Submodule.Quotient.eq' (p := degreeRelatorSpan p (P.withRelators T)))

/-- Kernel membership for the relator-enlargement quotient map, expressed by choosing a
representative in the larger span. -/
theorem relators_subset_ker
    {S T : Set P.Free} (hST : S ⊆ T)
    (q : dRQuot p (P.withRelators S)) :
    q ∈ LinearMap.ker (relation_relators_subset p P hST) ↔
      ∃ v : degreeFreeModule p (P.withRelators S),
        q = Submodule.Quotient.mk v ∧
          v ∈ degreeRelatorSpan p (P.withRelators T) := by
  refine Quotient.inductionOn' q ?_
  intro v
  constructor
  · intro hv
    exact ⟨v, rfl,
      (subset_mk_ker
        p P hST v).1 hv⟩
  · rintro ⟨w, hw, hwmem⟩
    change Submodule.Quotient.mk v ∈
      LinearMap.ker (relation_relators_subset p P hST)
    have hwker : Submodule.Quotient.mk w ∈
        LinearMap.ker (relation_relators_subset p P hST) :=
      (subset_mk_ker
        p P hST w).2 hwmem
    change Quotient.mk'' v ∈
      LinearMap.ker (relation_relators_subset p P hST)
    rw [hw]
    exact hwker

/-- The subset-induced quotient map has full range. -/
theorem relators_subset_top
    {S T : Set P.Free} (hST : S ⊆ T) :
    LinearMap.range (relation_relators_subset p P hST) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (relators_subset_surjective p P hST)

/-- The subset-induced quotient map for a reflexive inclusion is the identity. -/
@[simp] theorem relators_subset_refl
    (S : Set P.Free) :
    relation_relators_subset p P (fun x (hx : x ∈ S) => hx) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  change relation_relators_subset p P (fun x (hx : x ∈ S) => hx)
      (Submodule.Quotient.mk v) = (LinearMap.id : _ →ₗ[ZMod p] _) (Submodule.Quotient.mk v)
  dsimp [relation_relators_subset]

/-- When an inclusion of relator sets does not change the degree-one span, its quotient
map is the canonical span-equality equivalence. -/
theorem degree_relators_subset
    {S T : Set P.Free} (hST : S ⊆ T)
    (hspan : degreeRelatorSpan p (P.withRelators S) =
      degreeRelatorSpan p (P.withRelators T)) :
    relation_relators_subset p P hST =
      (relation_relators_span p P hspan).toLinearMap := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  change relation_relators_subset p P hST
      (Submodule.Quotient.mk v) =
    relation_relators_span p P hspan
      (Submodule.Quotient.mk v)
  dsimp [relation_relators_subset,
    relation_relators_span]
  rfl

/-- The inclusion-induced quotient map is injective exactly when the two degree-one
spans are equal. -/
theorem relators_subset_span
    {S T : Set P.Free} (hST : S ⊆ T) :
    Function.Injective (relation_relators_subset p P hST) ↔
      degreeRelatorSpan p (P.withRelators S) =
        degreeRelatorSpan p (P.withRelators T) := by
  constructor
  · intro hinj
    apply le_antisymm
    · exact degree_relators_mono p P hST
    · intro x hx
      have hker : LinearMap.ker
          (relation_relators_subset p P hST) = ⊥ :=
        LinearMap.ker_eq_bot.mpr hinj
      rw [degree_subset_ker] at hker
      have hxmap : Submodule.Quotient.mk x ∈
          (degreeRelatorSpan p (P.withRelators T)).map
            (Submodule.mkQ (degreeRelatorSpan p (P.withRelators S))) :=
        ⟨x, hx, rfl⟩
      rw [hker] at hxmap
      have hzero : (Submodule.Quotient.mk x :
          dRQuot p (P.withRelators S)) = 0 := by
        simpa using hxmap
      exact (Submodule.Quotient.mk_eq_zero
        (p := degreeRelatorSpan p (P.withRelators S))).1 hzero
  · intro hspan
    rw [degree_relators_subset p P hST hspan]
    exact (relation_relators_span p P hspan).injective

/-- Since inclusion-induced quotient maps are always surjective, bijectivity is the same
as equality of degree-one spans. -/
theorem subset_bijective_span
    {S T : Set P.Free} (hST : S ⊆ T) :
    Function.Bijective (relation_relators_subset p P hST) ↔
      degreeRelatorSpan p (P.withRelators S) =
        degreeRelatorSpan p (P.withRelators T) := by
  constructor
  · intro h
    exact (relators_subset_span
      p P hST).1 h.1
  · intro h
    exact ⟨(relators_subset_span
      p P hST).2 h,
      relators_subset_surjective p P hST⟩

/-- If two relator sets include each other, the two induced quotient maps compose to the
identity in the forward direction.  This avoids having to rewrite by set extensionality in
staged relator arguments. -/
@[simp] theorem relators_subset_antisymm
    {S T : Set P.Free} (hST : S ⊆ T) (hTS : T ⊆ S) :
    (relation_relators_subset p P hTS).comp
        (relation_relators_subset p P hST) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  change (relation_relators_subset p P hTS)
      (relation_relators_subset p P hST (Submodule.Quotient.mk v)) =
    (LinearMap.id : _ →ₗ[ZMod p] _) (Submodule.Quotient.mk v)
  dsimp [relation_relators_subset]
  change Submodule.Quotient.mk
      ((LinearMap.id : _ →ₗ[ZMod p] _) ((LinearMap.id : _ →ₗ[ZMod p] _) v)) =
    Submodule.Quotient.mk v
  simp

/-- The reverse composition of mutually inverse relator-enlargement quotient maps is the
identity. -/
@[simp] theorem subset_comp_antisymm
    {S T : Set P.Free} (hST : S ⊆ T) (hTS : T ⊆ S) :
    (relation_relators_subset p P hST).comp
        (relation_relators_subset p P hTS) =
      LinearMap.id := by
  exact relators_subset_antisymm
    p P hTS hST

/-- The quotient map attached to mutually equal relator sets is bijective. -/
theorem subset_bijective_antisymm
    {S T : Set P.Free} (hST : S ⊆ T) (hTS : T ⊆ S) :
    Function.Bijective (relation_relators_subset p P hST) := by
  refine (subset_bijective_span
    p P hST).2 ?_
  exact degree_relators_congr p P (Set.Subset.antisymm hST hTS)

/-- The quotient map on degree-one relation modules induced by adding relators to `P`. -/
noncomputable def degree_relation_relators (S : Set P.Free) :
    dRQuot p P →ₗ[ZMod p]
      dRQuot p (P.addRelators S) :=
  Submodule.mapQ (degreeRelatorSpan p P)
    (degreeRelatorSpan p (P.addRelators S))
    (LinearMap.id : degreeFreeModule p P →ₗ[ZMod p] degreeFreeModule p P)
    (by
      intro x hx
      change x ∈ degreeRelatorSpan p (P.addRelators S)
      exact degree_span_relators p P S hx)

@[simp] theorem degree_relation_mk (S : Set P.Free)
    (v : degreeFreeModule p P) :
    degree_relation_relators p P S (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk v := by
  dsimp [degree_relation_relators]
  change Submodule.Quotient.mk v = Submodule.Quotient.mk v
  rfl

/-- Adding relators gives a surjective map on relation quotients. -/
theorem degree_relators_surjective (S : Set P.Free) :
    Function.Surjective (degree_relation_relators p P S) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  refine ⟨Submodule.Quotient.mk v, ?_⟩
  change degree_relation_relators p P S (Submodule.Quotient.mk v) =
    Submodule.Quotient.mk v
  rfl

/-- Kernel of the quotient map induced by adding relators: the enlarged span modulo the
old span. -/
theorem relation_relators_ker (S : Set P.Free) :
    LinearMap.ker (degree_relation_relators p P S) =
      (degreeRelatorSpan p (P.addRelators S)).map
        (Submodule.mkQ (degreeRelatorSpan p P)) := by
  dsimp [degree_relation_relators]
  simpa using
    (Submodule.ker_mapQ (p := degreeRelatorSpan p P)
      (q := degreeRelatorSpan p (P.addRelators S))
      (f := (LinearMap.id : degreeFreeModule p P →ₗ[ZMod p]
        degreeFreeModule p P))
      (by
        intro x hx
        change x ∈ degreeRelatorSpan p (P.addRelators S)
        exact degree_span_relators p P S hx))

/-- A representative lies in the kernel of the add-relators quotient map exactly when
its vector belongs to the enlarged relator span. -/
@[simp] theorem relators_mk_ker
    (S : Set P.Free) (v : degreeFreeModule p P) :
    Submodule.Quotient.mk v ∈
        LinearMap.ker (degree_relation_relators p P S) ↔
      v ∈ degreeRelatorSpan p (P.addRelators S) := by
  change degree_relation_relators p P S
      (Submodule.Quotient.mk v) = 0 ↔ _
  rw [degree_relation_mk]
  exact (Submodule.Quotient.mk_eq_zero
    (p := degreeRelatorSpan p (P.addRelators S)))

/-- Two representatives have the same image under the add-relators quotient map exactly
when their difference lies in the enlarged relator span. -/
@[simp] theorem relation_relators_mk
    (S : Set P.Free) (v w : degreeFreeModule p P) :
    degree_relation_relators p P S (Submodule.Quotient.mk v) =
      degree_relation_relators p P S (Submodule.Quotient.mk w) ↔
      -v + w ∈ degreeRelatorSpan p (P.addRelators S) := by
  rw [degree_relation_mk,
    degree_relation_mk]
  exact (Submodule.Quotient.eq' (p := degreeRelatorSpan p (P.addRelators S)))

/-- Kernel membership for the add-relators quotient map, expressed by a representative
whose vector lies in the enlarged relator span. -/
theorem degree_relators_ker
    (S : Set P.Free) (q : dRQuot p P) :
    q ∈ LinearMap.ker (degree_relation_relators p P S) ↔
      ∃ v : degreeFreeModule p P,
        q = Submodule.Quotient.mk v ∧ v ∈ degreeRelatorSpan p (P.addRelators S) := by
  refine Quotient.inductionOn' q ?_
  intro v
  constructor
  · intro hv
    exact ⟨v, rfl,
      (relators_mk_ker p P S v).1 hv⟩
  · rintro ⟨w, hw, hwmem⟩
    change Submodule.Quotient.mk v ∈
      LinearMap.ker (degree_relation_relators p P S)
    have hwker : Submodule.Quotient.mk w ∈
        LinearMap.ker (degree_relation_relators p P S) :=
      (relators_mk_ker p P S w).2 hwmem
    change Quotient.mk'' v ∈
      LinearMap.ker (degree_relation_relators p P S)
    rw [hw]
    exact hwker

/-- The add-relators quotient map has full range. -/
theorem relators_range_top (S : Set P.Free) :
    LinearMap.range (degree_relation_relators p P S) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (degree_relators_surjective p P S)

/-- If the newly added relator batch contributes no new degree-one span, adding it
induces a canonical equivalence on relation quotients. -/
noncomputable def degree_relation_span
    (S : Set P.Free)
    (hS : degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P) :
    dRQuot p P ≃ₗ[ZMod p]
      dRQuot p (P.addRelators S) :=
  let hspan : degreeRelatorSpan p P = degreeRelatorSpan p (P.addRelators S) := by
    rw [degree_relator_relators]
    exact (sup_eq_left.mpr hS).symm
  Submodule.quotEquivOfEq _ _ hspan

@[simp] theorem degree_span_mk
    (S : Set P.Free)
    (hS : degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P)
    (v : degreeFreeModule p P) :
    degree_relation_span p P S hS
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  dsimp [degree_relation_span]
  exact Submodule.quotEquivOfEq_mk _ _ _ v

@[simp] theorem relators_symm_mk
    (S : Set P.Free)
    (hS : degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P)
    (v : degreeFreeModule p (P.addRelators S)) :
    (degree_relation_span p P S hS).symm
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  let hspan : degreeRelatorSpan p P = degreeRelatorSpan p (P.addRelators S) := by
    rw [degree_relator_relators]
    exact (sup_eq_left.mpr hS).symm
  change Submodule.quotEquivOfEq _ _ hspan.symm (Submodule.Quotient.mk v) =
    Submodule.Quotient.mk v
  exact Submodule.quotEquivOfEq_mk _ _ hspan.symm v

/-- Under the same redundancy hypothesis, the add-relators quotient map is the equivalence. -/
theorem degree_relators_span
    (S : Set P.Free)
    (hS : degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P) :
    degree_relation_relators p P S =
      (degree_relation_span p P S hS).toLinearMap := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro v
  change degree_relation_relators p P S (Submodule.Quotient.mk v) =
    degree_relation_span p P S hS
      (Submodule.Quotient.mk v)
  dsimp [degree_relation_relators,
    degree_relation_span]
  rfl


/-- The add-relators quotient map is injective exactly when the added batch contributes
no new degree-one span. -/
theorem relators_injective_span
    (S : Set P.Free) :
    Function.Injective (degree_relation_relators p P S) ↔
      degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P := by
  constructor
  · intro hinj x hx
    have hker : LinearMap.ker (degree_relation_relators p P S) = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    rw [relation_relators_ker] at hker
    have hxadd : x ∈ degreeRelatorSpan p (P.addRelators S) :=
      degree_relators_add p P S hx
    have hxmap : Submodule.Quotient.mk x ∈
        (degreeRelatorSpan p (P.addRelators S)).map
          (Submodule.mkQ (degreeRelatorSpan p P)) :=
      ⟨x, hxadd, rfl⟩
    rw [hker] at hxmap
    have hzero : (Submodule.Quotient.mk x : dRQuot p P) = 0 := by
      exact (Submodule.mem_bot (ZMod p)).1 hxmap
    exact (Submodule.Quotient.mk_eq_zero (p := degreeRelatorSpan p P)).1 hzero
  · intro hS
    rw [degree_relators_span p P S hS]
    exact (degree_relation_span p P S hS).injective

/-- Since add-relator quotient maps are always surjective, bijectivity is equivalent to
redundancy of the added degree-one span. -/
theorem relators_bijective_span
    (S : Set P.Free) :
    Function.Bijective (degree_relation_relators p P S) ↔
      degreeRelatorSpan p (P.withRelators S) ≤ degreeRelatorSpan p P := by
  constructor
  · intro h
    exact (relators_injective_span p P S).1 h.1
  · intro h
    exact ⟨(relators_injective_span p P S).2 h,
      degree_relators_surjective p P S⟩

/-- The degree-one map descends to the quotient by relator exponent vectors. -/
def degreeOneRelation :
    dRQuot p P →ₗ[ZMod p] mFAdditi p P.Group :=
  (degreeRelatorSpan p P).liftQ (degreeOneLinear p P)
    (degree_span_ker p P)

@[simp] theorem degree_one_mk (v : degreeFreeModule p P) :
    degreeOneRelation p P (Submodule.Quotient.mk v) = degreeOneLinear p P v := by
  rfl

/-- The descended relation map remains surjective. -/
theorem degree_relation_surjective : Function.Surjective (degreeOneRelation p P) := by
  intro y
  rcases degree_linear_surjective p P y with ⟨v, rfl⟩
  exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- The generator degree-one map has full range. -/
theorem linear_range_top :
    LinearMap.range (degreeOneLinear p P) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _ (degree_linear_surjective p P)

/-- The descended relation map has full range. -/
theorem degree_range_top :
    LinearMap.range (degreeOneRelation p P) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _ (degree_relation_surjective p P)

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- Predicate that all relators have zero mod-`p` exponent vector. -/
def exponentVectorSilent : Prop :=
  ∀ ⦃r : P.Free⦄, r ∈ P.rels → exponentVector p P.Gen r = 0

/-- For a fixed-generator replacement, relator silence is pointwise silence on the set. -/
theorem vector_silent_relators (S : Set P.Free) :
    exponentVectorSilent p (P.withRelators S) ↔
      ∀ ⦃r : P.Free⦄, r ∈ S → exponentVector p P.Gen r = 0 := by
  rfl

/-- Relator silence after adding a batch splits into old and new silence. -/
theorem exponent_silent_relators (S : Set P.Free) :
    exponentVectorSilent p (P.addRelators S) ↔
      exponentVectorSilent p P ∧ exponentVectorSilent p (P.withRelators S) := by
  constructor
  · intro h
    constructor
    · intro r hr; exact h (Or.inl hr)
    · intro r hr; exact h (Or.inr hr)
  · rintro ⟨hP, hS⟩ r (hr | hr)
    · exact hP hr
    · exact hS hr


/-- If all relators are exponent-vector silent, the degree-one relator span is zero. -/
theorem degree_vector_silent
    (h : exponentVectorSilent p P) : degreeRelatorSpan p P = ⊥ := by
  apply le_antisymm
  · dsimp [degreeRelatorSpan]
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases hv with ⟨r, hr, rfl⟩
    change exponentVector p P.Gen r ∈ (⊥ : Submodule (ZMod p) (degreeFreeModule p P))
    rw [h hr]
    exact Submodule.zero_mem _
  · exact bot_le

/-- If a newly added batch is exponent-vector silent, it is redundant on the degree-one
relation quotient. -/
noncomputable def degree_batch_silent
    (S : Set P.Free) (hS : exponentVectorSilent p (P.withRelators S)) :
    dRQuot p P ≃ₗ[ZMod p]
      dRQuot p (P.addRelators S) :=
  degree_relation_span p P S (by
    rw [degree_vector_silent p (P.withRelators S) hS]
    exact bot_le)

@[simp] theorem batch_silent_mk
    (S : Set P.Free) (hS : exponentVectorSilent p (P.withRelators S))
    (v : degreeFreeModule p P) :
    degree_batch_silent p P S hS
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  simp [degree_batch_silent]

/-- The add-relators quotient map is an equivalence when the added batch is silent. -/
theorem relators_batch_silent
    (S : Set P.Free) (hS : exponentVectorSilent p (P.withRelators S)) :
    degree_relation_relators p P S =
      (degree_batch_silent p P S hS).toLinearMap := by
  dsimp [degree_batch_silent]
  exact degree_relators_span p P S _

/-- Pointwise-silent added relators give the same degree-one relation quotient. -/
noncomputable def relators_pointwise_silent
    (S : Set P.Free)
    (hS : ∀ ⦃r : P.Free⦄, r ∈ S → exponentVector p P.Gen r = 0) :
    dRQuot p P ≃ₗ[ZMod p]
      dRQuot p (P.addRelators S) :=
  degree_batch_silent p P S
    ((vector_silent_relators p P S).2 hS)

@[simp] theorem pointwise_silent_mk
    (S : Set P.Free)
    (hS : ∀ ⦃r : P.Free⦄, r ∈ S → exponentVector p P.Gen r = 0)
    (v : degreeFreeModule p P) :
    relators_pointwise_silent p P S hS
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  simp [relators_pointwise_silent]

/-- In the exponent-silent case, the relation quotient is canonically the free module. -/
def degreeRelationFree (h : exponentVectorSilent p P) :
    dRQuot p P ≃ₗ[ZMod p] degreeFreeModule p P :=
  (degreeRelatorSpan p P).quotEquivOfEqBot
    (degree_vector_silent p P h)

@[simp] theorem degree_free_mk
    (h : exponentVectorSilent p P) (v : degreeFreeModule p P) :
    degreeRelationFree p P h (Submodule.Quotient.mk v) = v := by
  simp [degreeRelationFree]

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The presentation degree-one map is the free-group degree-one equivalence map followed by
functoriality along the quotient map. -/
theorem degree_comp_exponent :
    degreeOneLinear p P =
      (mFAdditi.mapLinear (p := p) P.quotientMap).comp
        (freeLinear p P.Gen) := by
  apply LinearMap.ext
  intro v
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [degreeOneLinear, freeLinear]
  | add f g hf hg => simp [map_add, hf, hg]
  | single a r =>
      have hq : P.quotientMap (FreeGroup.of a) = P.of a := rfl
      simp [degreeOneLinear, freeLinear, degreeGeneratorClass, hq]

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The relator exponent-span, viewed multiplicatively. -/
def degreeSpanMul : Subgroup (Multiplicative (degreeFreeModule p P)) where
  carrier := {m | Multiplicative.toAdd m ∈ degreeRelatorSpan p P}
  one_mem' := by
    change (0 : degreeFreeModule p P) ∈ degreeRelatorSpan p P
    exact Submodule.zero_mem _
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd x + Multiplicative.toAdd y ∈ degreeRelatorSpan p P
    exact (degreeRelatorSpan p P).add_mem hx hy
  inv_mem' := by
    intro x hx
    change - Multiplicative.toAdd x ∈ degreeRelatorSpan p P
    exact (degreeRelatorSpan p P).neg_mem hx

/-- Words in the normal closure of the relators have exponent vector in the relator span. -/
theorem exponent_vector_closure {w : P.Free}
    (hw : w ∈ P.rNClos) :
    exponentVector p P.Gen w ∈ degreeRelatorSpan p P := by
  let K : Subgroup P.Free := (degreeSpanMul p P).comap (exponentVectorHom p P.Gen)
  have hle : P.rNClos ≤ K := by
    dsimp [rNClos]
    refine Subgroup.normalClosure_le_normal ?_
    intro r hr
    change exponentVectorHom p P.Gen r ∈ degreeSpanMul p P
    change exponentVector p P.Gen r ∈ degreeRelatorSpan p P
    exact Submodule.subset_span ⟨r, hr, rfl⟩
  have hk : w ∈ K := hle hw
  exact hk

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The exponent-vector map into the relation quotient, before imposing the
presentation quotient. -/
def relationWordHom :
    P.Free →* Multiplicative (dRQuot p P) where
  toFun w := Multiplicative.ofAdd (Submodule.Quotient.mk (exponentVector p P.Gen w))
  map_one' := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk (0 : degreeFreeModule p P)) = 1
    rfl
  map_mul' u v := by
    change Multiplicative.ofAdd
        (Submodule.Quotient.mk (exponentVector p P.Gen (u * v))) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (exponentVector p P.Gen u)) *
        Multiplicative.ofAdd (Submodule.Quotient.mk (exponentVector p P.Gen v))
    rw [exponentVector_mul]
    rfl

/-- The exponent-vector map descends from the free group to the presented group after quotienting
by the relator exponent span. -/
def relationQuotientHom :
    P.Group →* Multiplicative (dRQuot p P) :=
  QuotientGroup.lift P.rNClos (relationWordHom p P) (by
    intro w hw
    change Multiplicative.ofAdd
        (Submodule.Quotient.mk (exponentVector p P.Gen w)) = 1
    change Submodule.Quotient.mk (exponentVector p P.Gen w) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := degreeRelatorSpan p P)).2
      (exponent_vector_closure p P hw))

@[simp] theorem relation_hom_mk (w : P.Free) :
    relationQuotientHom p P (P.quotientMap w) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (exponentVector p P.Gen w)) := by
  rfl

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

@[simp] theorem relation_pow_p (w : P.Free) :
    relationWordHom p P (w ^ p) = 1 := by
  change Multiplicative.ofAdd
      (Submodule.Quotient.mk (exponentVector p P.Gen (w ^ p))) = 1
  rw [exponentVector_pow]
  change Submodule.Quotient.mk (p • exponentVector p P.Gen w) = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod p)]
  simp

@[simp] theorem relation_hom_commutator (u v : P.Free) :
    relationWordHom p P ⁅u, v⁆ = 1 := by
  change Multiplicative.ofAdd
      (Submodule.Quotient.mk (exponentVector p P.Gen ⁅u, v⁆)) = 1
  rw [exponentVector_commutator]
  rfl

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

@[simp] theorem relation_hom_p (g : P.Group) :
    relationQuotientHom p P (g ^ p) = 1 := by
  refine QuotientGroup.induction_on g ?_
  intro w
  change relationQuotientHom p P (P.quotientMap w ^ p) = 1
  rw [← map_pow P.quotientMap]
  change relationQuotientHom p P (P.quotientMap (w ^ p)) = 1
  rw [relation_hom_mk]
  exact relation_pow_p p P w

@[simp] theorem relation_quotient_commutator (g h : P.Group) :
    relationQuotientHom p P ⁅g, h⁆ = 1 := by
  refine QuotientGroup.induction_on g ?_
  intro u
  refine QuotientGroup.induction_on h ?_
  intro v
  change relationQuotientHom p P ⁅P.quotientMap u, P.quotientMap v⁆ = 1
  rw [← map_commutatorElement]
  rw [relation_hom_mk]
  exact relation_hom_commutator p P u v

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The relation-quotient exponent map factors through the mod-`p` Frattini quotient. -/
def relationFrattiniHom :
    mFQuot p P.Group →* Multiplicative (dRQuot p P) :=
  QuotientGroup.lift (modPFrattini p P.Group) (relationQuotientHom p P) (by
    intro g hg
    have hker : modPFrattini p P.Group ≤ MonoidHom.ker (relationQuotientHom p P) := by
      dsimp [modPFrattini]
      apply sup_le
      · refine Subgroup.normalClosure_le_normal ?_
        intro x hx
        rcases hx with ⟨y, rfl⟩
        change relationQuotientHom p P (y ^ p) = 1
        exact relation_hom_p p P y
      · rw [_root_.commutator_def]
        rw [Subgroup.commutator_le]
        intro x _ y _
        change relationQuotientHom p P ⁅x, y⁆ = 1
        exact relation_quotient_commutator p P x y
    exact (MonoidHom.mem_ker).1 (hker hg))

@[simp] theorem relation_frattini_mk (g : P.Group) :
    relationFrattiniHom p P (mFQuot.mk p P.Group g) =
      relationQuotientHom p P g := by
  rfl

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- Additive form of the map from the presented Frattini quotient to the relation quotient. -/
def relationFrattiniAdd :
    mFAdditi p P.Group →+ dRQuot p P where
  toFun q := Multiplicative.toAdd (relationFrattiniHom p P (Additive.toMul q))
  map_zero' := by rfl
  map_add' x y := by
    change Multiplicative.toAdd
        (relationFrattiniHom p P (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl

/-- Linear form of the map from the presented Frattini quotient to the relation quotient. -/
def relationFrattiniLinear :
    mFAdditi p P.Group →ₗ[ZMod p] dRQuot p P :=
  (relationFrattiniAdd p P).toZModLinearMap p

@[simp] theorem relation_frattini_linear (w : P.Free) :
    relationFrattiniLinear p P
      (Additive.ofMul (mFQuot.mk p P.Group (P.quotientMap w))) =
    Submodule.Quotient.mk (exponentVector p P.Gen w) := by
  rfl

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The map back from the Frattini quotient is a left inverse to the descended relation map. -/
theorem relation_frattini_comp
    (q : dRQuot p P) :
    relationFrattiniLinear p P (degreeOneRelation p P q) = q := by
  refine Submodule.Quotient.induction_on (p := degreeRelatorSpan p P) q ?_
  intro v
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [degreeOneRelation]
  | add f g hf hg =>
      have hf' : relationFrattiniLinear p P (degreeOneLinear p P f) =
          Submodule.Quotient.mk f := by
        simpa [degreeOneRelation] using hf
      have hg' : relationFrattiniLinear p P (degreeOneLinear p P g) =
          Submodule.Quotient.mk g := by
        simpa [degreeOneRelation] using hg
      simp [map_add, hf', hg']
  | single x a =>
      have hbase : relationFrattiniLinear p P (degreeGeneratorClass p P x) =
          Submodule.Quotient.mk (Finsupp.single x (1 : ZMod p)) := by
        simpa [degreeGeneratorClass, Presentation.of, Presentation.quotientMap]
          using relation_frattini_linear p P (FreeGroup.of x)
      rw [degree_one_mk, degree_one_single, map_smul, hbase]
      rw [← Submodule.Quotient.mk_smul]
      simp

end
end Presentation
end Towers

namespace Towers
namespace Presentation

open GroupAlgebra

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The descended relation map is also a left inverse to the map from the Frattini quotient. -/
theorem degree_frattini_linear
    (y : mFAdditi p P.Group) :
    degreeOneRelation p P (relationFrattiniLinear p P y) = y := by
  induction y using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro g
      rcases P.quotientMap_surjective g with ⟨w, rfl⟩
      change degreeOneRelation p P
          (relationFrattiniLinear p P
            (Additive.ofMul (mFQuot.mk p P.Group (P.quotientMap w)))) =
        Additive.ofMul (mFQuot.mk p P.Group (P.quotientMap w))
      rw [relation_frattini_linear, degree_one_mk,
        degree_exponent_vector]
      rfl

/-- The degree-one relation quotient is linearly equivalent to the mod-`p` Frattini quotient. -/
def degreeRelationFrattini :
    dRQuot p P ≃ₗ[ZMod p] mFAdditi p P.Group where
  toFun := degreeOneRelation p P
  invFun := relationFrattiniLinear p P
  left_inv := relation_frattini_comp p P
  right_inv := degree_frattini_linear p P
  map_add' := by intro x y; exact (degreeOneRelation p P).map_add x y
  map_smul' := by intro a x; exact (degreeOneRelation p P).map_smul a x

/-- Conditional presentation-level comparison with the first Zassenhaus quotient.
The only additional input is the reverse degree-one containment `D₂ ≤ G^p [G,G]`. -/
def degreeLinearReverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    dRQuot p P ≃ₗ[ZMod p] zTAdditi p P.Group :=
  (degreeRelationFrattini p P).trans
    (mFAdditi.zass_twolin_equivreverse p P.Group hrev)

@[simp] theorem degree_linear_frattini
    (q : dRQuot p P) :
    degreeRelationFrattini p P q = degreeOneRelation p P q := rfl

/-- The descended relation map is injective (with explicit inverse above). -/
theorem degree_relation_injective : Function.Injective (degreeOneRelation p P) := by
  intro x y hxy
  have h := congrArg (relationFrattiniLinear p P) hxy
  simpa [relation_frattini_comp] using h

/-- The descended relation map has trivial kernel. -/
theorem degree_relation_bot :
    LinearMap.ker (degreeOneRelation p P) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective (degree_relation_injective p P)

@[simp] theorem degree_relation_frattini :
    (degreeRelationFrattini p P).toLinearMap = degreeOneRelation p P := rfl

@[simp] theorem linear_frattini_symm
    (y : mFAdditi p P.Group) :
    (degreeRelationFrattini p P).symm y =
      relationFrattiniLinear p P y := rfl

@[simp] theorem relation_frattini_symm
    (q : dRQuot p P) :
    (degreeRelationFrattini p P).symm (degreeOneRelation p P q) = q := by
  exact relation_frattini_comp p P q

@[simp] theorem equiv_frattini_symm
    (y : mFAdditi p P.Group) :
    degreeOneRelation p P ((degreeRelationFrattini p P).symm y) = y := by
  exact degree_frattini_linear p P y

/-- Equality to the presentation degree-one map, rewritten through the inverse equivalence. -/
theorem degree_frattini_symm
    (q : dRQuot p P) (y : mFAdditi p P.Group) :
    degreeOneRelation p P q = y ↔
      q = (degreeRelationFrattini p P).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (relation_frattini_symm p P q).symm
  · intro h
    rw [h]
    exact equiv_frattini_symm p P y

@[simp] theorem degree_two_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P) :
    degreeLinearReverse p P hrev q =
      mFAdditi.zass_two_lin p P.Group (degreeOneRelation p P q) := rfl

@[simp] theorem degree_linear_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    (degreeLinearReverse p P hrev).toLinearMap =
      (mFAdditi.zass_two_lin p P.Group).comp
        (degreeOneRelation p P) := by
  apply LinearMap.ext
  intro q
  rfl

@[simp] theorem relation_reverse_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P) :
    (degreeLinearReverse p P hrev).symm
        (mFAdditi.zass_two_lin p P.Group
          (degreeOneRelation p P q)) = q := by
  exact (degreeLinearReverse p P hrev).left_inv q

@[simp] theorem degree_zassenhaus_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (y : zTAdditi p P.Group) :
    mFAdditi.zass_two_lin p P.Group
        (degreeOneRelation p P
          ((degreeLinearReverse p P hrev).symm y)) = y := by
  change degreeLinearReverse p P hrev
      ((degreeLinearReverse p P hrev).symm y) = y
  exact (degreeLinearReverse p P hrev).right_inv y

/-- Equality to the conditional Zassenhaus presentation map, rewritten through its inverse. -/
theorem degree_two_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P) (y : zTAdditi p P.Group) :
    mFAdditi.zass_two_lin p P.Group (degreeOneRelation p P q) = y ↔
      q = (degreeLinearReverse p P hrev).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (relation_reverse_symm p P hrev q).symm
  · intro h
    rw [h]
    exact degree_zassenhaus_symm p P hrev y

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The kernel of the generator degree-one map is exactly the span of relator exponent vectors. -/
theorem degree_relator_span :
    LinearMap.ker (degreeOneLinear p P) = degreeRelatorSpan p P := by
  apply le_antisymm
  · intro v hv
    have h := relation_frattini_comp p P
      (Submodule.Quotient.mk v)
    rw [degree_one_mk, LinearMap.mem_ker.mp hv, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero (p := degreeRelatorSpan p P)).1 h.symm
  · exact degree_span_ker p P

/-- The generator degree-one map is injective exactly when relator exponent vectors span zero. -/
theorem degree_span_bot :
    Function.Injective (degreeOneLinear p P) ↔ degreeRelatorSpan p P = ⊥ := by
  rw [← LinearMap.ker_eq_bot, degree_relator_span]

end
end Presentation
end Towers

namespace Towers
namespace Presentation

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- Relator silence is equivalent to the relator exponent-span being zero. -/
theorem bot_vector_silent :
    degreeRelatorSpan p P = ⊥ ↔ exponentVectorSilent p P := by
  constructor
  · intro h r hr
    have hm : exponentVector p P.Gen r ∈ degreeRelatorSpan p P := by
      dsimp [degreeRelatorSpan]
      exact Submodule.subset_span ⟨r, hr, rfl⟩
    rw [h] at hm
    simpa using hm
  · intro h
    exact degree_vector_silent p P h

/-- A presentation has injective degree-one generator map exactly when all relators are
exponent-vector silent. -/
theorem exponent_vector_silent :
    Function.Injective (degreeOneLinear p P) ↔ exponentVectorSilent p P := by
  rw [degree_span_bot,
    bot_vector_silent]

/-- For a fixed-generator relator replacement, degree-one injectivity is pointwise
silence of the chosen relators. -/
theorem degree_injective_relators (S : Set P.Free) :
    Function.Injective (degreeOneLinear p (P.withRelators S)) ↔
      ∀ ⦃r : P.Free⦄, r ∈ S → exponentVector p P.Gen r = 0 := by
  rw [exponent_vector_silent,
    vector_silent_relators]

/-- Adding a batch preserves degree-one injectivity exactly when both the old presentation
and the batch-only presentation are degree-one injective. -/
theorem degree_linear_relators (S : Set P.Free) :
    Function.Injective (degreeOneLinear p (P.addRelators S)) ↔
      Function.Injective (degreeOneLinear p P) ∧
        Function.Injective (degreeOneLinear p (P.withRelators S)) := by
  rw [degree_span_bot,
    degree_relators_bot,
    ← degree_span_bot,
    ← degree_span_bot]


end
end Presentation
end Towers

namespace Towers
namespace Presentation

open GroupAlgebra

noncomputable section

variable (p : ℕ) (P : Presentation) [Fact p.Prime]

/-- Conditional presentation-level comparison with the first Zassenhaus layer kernel.
This is the layer-kernel analogue of `degreeLinearReverse`. -/
def degreeRelationReverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    dRQuot p P ≃ₗ[ZMod p]
      Additive (zLKern p P.Group 1) :=
  (degreeRelationFrattini p P).trans
    (mFAdditi.zasslayer_onelin_equivreverse p P.Group hrev)

@[simp] theorem relation_linear_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P) :
    degreeRelationReverse p P hrev q =
      mFAdditi.zass_layer_onelin p P.Group
        (degreeOneRelation p P q) := rfl

@[simp] theorem degree_relation_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    (degreeRelationReverse p P hrev).toLinearMap =
      (mFAdditi.zass_layer_onelin p P.Group).comp
        (degreeOneRelation p P) := by
  apply LinearMap.ext
  intro q
  rfl

@[simp] theorem degree_reverse_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P) :
    (degreeRelationReverse p P hrev).symm
        (mFAdditi.zass_layer_onelin p P.Group
          (degreeOneRelation p P q)) = q := by
  exact (degreeRelationReverse p P hrev).left_inv q

@[simp] theorem degree_layer_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (y : Additive (zLKern p P.Group 1)) :
    mFAdditi.zass_layer_onelin p P.Group
        (degreeOneRelation p P
          ((degreeRelationReverse p P hrev).symm y)) = y := by
  change degreeRelationReverse p P hrev
      ((degreeRelationReverse p P hrev).symm y) = y
  exact (degreeRelationReverse p P hrev).right_inv y

/-- Equality to the conditional first-layer presentation map, rewritten through its inverse. -/
theorem degree_relation_symm
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group)
    (q : dRQuot p P)
    (y : Additive (zLKern p P.Group 1)) :
    mFAdditi.zass_layer_onelin p P.Group (degreeOneRelation p P q) = y ↔
      q = (degreeRelationReverse p P hrev).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (degree_reverse_symm p P hrev q).symm
  · intro h
    rw [h]
    exact degree_layer_symm p P hrev y

end
end Presentation
end Towers

namespace Towers
namespace Presentation

open GroupAlgebra

noncomputable section

variable (p : ℕ) (P : Presentation)

/-- The conditional presentation map to `G/D₂` has trivial kernel. -/
theorem relation_bot_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    LinearMap.ker
      ((mFAdditi.zass_two_lin p P.Group).comp
        (degreeOneRelation p P)) = ⊥ := by
  rw [← degree_linear_reverse (p := p) (P := P) hrev]
  exact LinearMap.ker_eq_bot_of_injective
    (degreeLinearReverse p P hrev).injective

/-- The conditional presentation map to `G/D₂` has full range. -/
theorem range_top_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    LinearMap.range
      ((mFAdditi.zass_two_lin p P.Group).comp
        (degreeOneRelation p P)) = ⊤ := by
  rw [← degree_linear_reverse (p := p) (P := P) hrev]
  exact LinearMap.range_eq_top_of_surjective _
    (degreeLinearReverse p P hrev).surjective

end
end Presentation
end Towers

namespace Towers
namespace Presentation

open GroupAlgebra

noncomputable section

variable (p : ℕ) (P : Presentation) [Fact p.Prime]

/-- The conditional presentation map to the first Zassenhaus layer has trivial kernel. -/
theorem degree_bot_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    LinearMap.ker
      ((mFAdditi.zass_layer_onelin p P.Group).comp
        (degreeOneRelation p P)) = ⊥ := by
  rw [
    ← degree_relation_reverse
      (p := p) (P := P) hrev]
  exact LinearMap.ker_eq_bot_of_injective
    (degreeRelationReverse p P hrev).injective

/-- The conditional presentation map to the first Zassenhaus layer has full range. -/
theorem degree_top_reverse
    (hrev : zSubgro p P.Group 2 ≤ modPFrattini p P.Group) :
    LinearMap.range
      ((mFAdditi.zass_layer_onelin p P.Group).comp
        (degreeOneRelation p P)) = ⊤ := by
  rw [
    ← degree_relation_reverse
      (p := p) (P := P) hrev]
  exact LinearMap.range_eq_top_of_surjective _
    (degreeRelationReverse p P hrev).surjective

end
end Presentation
end Towers
