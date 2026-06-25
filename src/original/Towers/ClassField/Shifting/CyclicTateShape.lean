import Mathlib.Algebra.Category.Grp.IsFinite
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Towers.ClassField.Shifting.HerbrandExactHexagon
import Towers.ClassField.Shifting.GroupPeriodicityOdd

/-!
# Milne, Class Field Theory, Proposition II.3.6

The Herbrand quotient is multiplicative in short exact sequences.  We model
the two-periodic cyclic resolution by a complex indexed by `Bool`; the long
exact homology sequence is then literally an exact hexagon.
-/

namespace Towers.CField.Shifting

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- The cyclic shape with one arrow in each direction. -/
private def cyclicTateShape : ComplexShape Bool where
  Rel i j := j = !i
  next_eq h h' := h.trans h'.symm
  prev_eq := by
    intro i i' j h h'
    cases i <;> cases i' <;> simp_all

set_option linter.flexible false in
/-- The two-periodic complex with alternating differentials `g - 1` and the
norm.  Its homology at `false` is even cyclic cohomology and its homology at
`true` is odd cyclic cohomology. -/
private noncomputable def cyclicTateComplex (A : Rep k G) (g : G) :
    HomologicalComplex (ModuleCat k) cyclicTateShape where
  X _ := ModuleCat.of k A
  d i j :=
    match i, j with
    | false, true => ModuleCat.ofHom (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
    | true, false => ModuleCat.ofHom A.norm.hom.toLinearMap
    | _, _ => 0
  shape i j hij := by
    cases i <;> cases j <;> simp [cyclicTateShape] at hij ⊢
  d_comp_d' i j l hij hjl := by
    cases i <;> cases j <;> cases l <;>
      simp [cyclicTateShape] at hij hjl ⊢
    all_goals
      ext x
      simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]

/-- A morphism of representations acts degreewise on the cyclic Tate
complex. -/
private noncomputable def cyclicTateMap {A B : Rep k G} (φ : A ⟶ B) (g : G) :
    cyclicTateComplex A g ⟶ cyclicTateComplex B g where
  f _ := φ.toModuleCatHom
  comm' i j hij := by
    cases i <;> cases j <;> simp [cyclicTateShape] at hij
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      dsimp [cyclicTateComplex, Rep.sub_hom, Rep.applyAsHom]
      change A at x
      change B.ρ g (φ.hom x) - φ.hom x = φ.hom (A.ρ g x - x)
      rw [map_sub, Rep.hom_comm_apply φ g x]
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      dsimp [cyclicTateComplex, Rep.norm, Representation.norm]
      change A at x
      change (∑ h : G, B.ρ h) (φ.hom x) = φ.hom ((∑ h : G, A.ρ h) x)
      rw [LinearMap.sum_apply Finset.univ (fun h : G => B.ρ h) (φ.hom x),
        LinearMap.sum_apply Finset.univ (fun h : G => A.ρ h) x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro h _
      exact (Rep.hom_comm_apply φ h x).symm

@[simp]
private theorem cyclic_tate_id (A : Rep k G) (g : G) :
    cyclicTateMap (𝟙 A) g = 𝟙 (cyclicTateComplex A g) := by
  ext i
  rfl

@[simp]
private theorem cyclic_tate_comp {A B C : Rep k G}
    (φ : A ⟶ B) (ψ : B ⟶ C) (g : G) :
    cyclicTateMap (φ ≫ ψ) g = cyclicTateMap φ g ≫ cyclicTateMap ψ g := by
  ext i
  rfl

@[simp]
private theorem cyclic_tate_zero (A B : Rep k G) (g : G) :
    cyclicTateMap (0 : A ⟶ B) g = 0 := by
  ext i
  rfl

/-- A short complex of representations induces a short complex of cyclic
Tate complexes. -/
private noncomputable def cyclicShortComplex
    (X : ShortComplex (Rep k G)) (g : G) :
    ShortComplex (HomologicalComplex (ModuleCat k) cyclicTateShape) :=
  ShortComplex.mk (cyclicTateMap X.f g) (cyclicTateMap X.g g) <| by
    rw [← cyclic_tate_comp, X.zero, cyclic_tate_zero]

/-- Degreewise short exactness of a coefficient sequence gives short
exactness of its two-periodic cyclic complex. -/
private theorem cyclic_short_exact
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G) :
    (cyclicShortComplex X g).ShortExact := by
  letI : Mono X.f := hX.mono_f
  letI : Epi X.g := hX.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  simpa [cyclicShortComplex, cyclicTateComplex, cyclicTateMap] using
    hX.map (forget₂ (Rep k G) (ModuleCat k))

private abbrev cyclicTateEven (A : Rep k G) (g : G) :=
  (cyclicTateComplex A g).homology false

private abbrev cyclicTateOdd (A : Rep k G) (g : G) :=
  (cyclicTateComplex A g).homology true

private noncomputable def evenScIso (A : Rep k G) (g : G) :
    (cyclicTateComplex A g).sc' true false true ≅
      Rep.FiniteCyclicGroup.normHomCompSub A g :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [cyclicTateComplex]) (by simp [cyclicTateComplex])

private noncomputable def oddScIso (A : Rep k G) (g : G) :
    (cyclicTateComplex A g).sc' false true false ≅
      Rep.FiniteCyclicGroup.subCompNormHom A g :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [cyclicTateComplex]) (by simp [cyclicTateComplex])

/-- The even vertex of the cyclic Tate complex computes `H²`. -/
private noncomputable def cyclicEvenIso
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicTateEven A g ≅ groupCohomology A 2 :=
  (cyclicTateComplex A g).homologyIsoSc' true false true
      (cyclicTateShape.prev_eq' (show cyclicTateShape.Rel true false from rfl))
      (cyclicTateShape.next_eq' (show cyclicTateShape.Rel false true from rfl)) ≪≫
    ShortComplex.homologyMapIso (evenScIso A g) ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm

/-- The odd vertex of the cyclic Tate complex computes `H¹`. -/
private noncomputable def cyclicOddIso
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicTateOdd A g ≅ groupCohomology A 1 :=
  (cyclicTateComplex A g).homologyIsoSc' false true false
      (cyclicTateShape.prev_eq' (show cyclicTateShape.Rel false true from rfl))
      (cyclicTateShape.next_eq' (show cyclicTateShape.Rel true false from rfl)) ≪≫
    ShortComplex.homologyMapIso (oddScIso A g) ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm

private noncomputable abbrev cyclicOddF
    (X : ShortComplex (Rep k G)) (g : G) :
    cyclicTateOdd X.X₁ g ⟶ cyclicTateOdd X.X₂ g :=
  HomologicalComplex.homologyMap (cyclicTateMap X.f g) true

private noncomputable abbrev cyclicOddG
    (X : ShortComplex (Rep k G)) (g : G) :
    cyclicTateOdd X.X₂ g ⟶ cyclicTateOdd X.X₃ g :=
  HomologicalComplex.homologyMap (cyclicTateMap X.g g) true

private noncomputable abbrev cyclicEvenF
    (X : ShortComplex (Rep k G)) (g : G) :
    cyclicTateEven X.X₁ g ⟶ cyclicTateEven X.X₂ g :=
  HomologicalComplex.homologyMap (cyclicTateMap X.f g) false

private noncomputable abbrev cyclicEvenG
    (X : ShortComplex (Rep k G)) (g : G) :
    cyclicTateEven X.X₂ g ⟶ cyclicTateEven X.X₃ g :=
  HomologicalComplex.homologyMap (cyclicTateMap X.g g) false

private noncomputable abbrev oddEvenBoundary
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G) :
    cyclicTateOdd X.X₃ g ⟶ cyclicTateEven X.X₁ g :=
  (cyclic_short_exact hX g).δ true false rfl

private noncomputable abbrev evenOddBoundary
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G) :
    cyclicTateEven X.X₃ g ⟶ cyclicTateOdd X.X₁ g :=
  (cyclic_short_exact hX g).δ false true rfl

/-- The two-periodic homology sequence attached to a short exact coefficient
sequence is an exact hexagon. -/
private theorem cyclic_exact_hexagon
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G) :
    Function.Exact (cyclicOddF X g) (cyclicOddG X g) ∧
      Function.Exact (cyclicOddG X g) (oddEvenBoundary hX g) ∧
      Function.Exact (oddEvenBoundary hX g) (cyclicEvenF X g) ∧
      Function.Exact (cyclicEvenF X g) (cyclicEvenG X g) ∧
      Function.Exact (cyclicEvenG X g) (evenOddBoundary hX g) ∧
      Function.Exact (evenOddBoundary hX g) (cyclicOddF X g) := by
  let hS := cyclic_short_exact hX g
  have hOddMiddle := hS.homology_exact₂ true
  have hOddRight := hS.homology_exact₃ true false rfl
  have hEvenLeft := hS.homology_exact₁ true false rfl
  have hEvenMiddle := hS.homology_exact₂ false
  have hEvenRight := hS.homology_exact₃ false true rfl
  have hOddLeft := hS.homology_exact₁ false true rfl
  exact ⟨
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hOddMiddle,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hOddRight,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hEvenLeft,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hEvenMiddle,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hEvenRight,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hOddLeft⟩

/-- In an exact pair of additive homomorphisms, finiteness of the two outer
groups implies finiteness of the middle group. -/
private theorem finite_exact_ends
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C] (f : A →+ B) (g : B →+ C)
    (h : Function.Exact f g) : Finite B := by
  rw [AddMonoidHom.finite_iff_finite_ker_range g]
  constructor
  · rw [h.addMonoidHom_ker_eq]
    exact Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  · exact Finite.of_injective Subtype.val Subtype.val_injective

/-- If the odd and even Tate groups of the two ends of a short exact
sequence are finite, then those of the middle term are finite. -/
private theorem cyclic_tate_middle
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)] [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₃ g)] [Finite (cyclicTateEven X.X₃ g)] :
    Finite (cyclicTateOdd X.X₂ g) ∧ Finite (cyclicTateEven X.X₂ g) := by
  obtain ⟨h₁, _, _, h₄, _, _⟩ := cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (cyclicOddF X g).hom.toAddMonoidHom
      (cyclicOddG X g).hom.toAddMonoidHom h₁,
    finite_exact_ends
      (cyclicEvenF X g).hom.toAddMonoidHom
      (cyclicEvenG X g).hom.toAddMonoidHom h₄⟩

/-- If the odd and even Tate groups of the middle and right terms are
finite, then those of the left term are finite. -/
private theorem cyclic_tate_left
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₂ g)] [Finite (cyclicTateEven X.X₂ g)]
    [Finite (cyclicTateOdd X.X₃ g)] [Finite (cyclicTateEven X.X₃ g)] :
    Finite (cyclicTateOdd X.X₁ g) ∧ Finite (cyclicTateEven X.X₁ g) := by
  obtain ⟨_, _, h₃, _, _, h₆⟩ := cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (evenOddBoundary hX g).hom.toAddMonoidHom
      (cyclicOddF X g).hom.toAddMonoidHom h₆,
    finite_exact_ends
      (oddEvenBoundary hX g).hom.toAddMonoidHom
      (cyclicEvenF X g).hom.toAddMonoidHom h₃⟩

/-- If the odd and even Tate groups of the left and middle terms are finite,
then those of the right term are finite. -/
private theorem cyclic_tate_right
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)] [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₂ g)] [Finite (cyclicTateEven X.X₂ g)] :
    Finite (cyclicTateOdd X.X₃ g) ∧ Finite (cyclicTateEven X.X₃ g) := by
  obtain ⟨_, h₂, _, _, h₅, _⟩ := cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (cyclicOddG X g).hom.toAddMonoidHom
      (oddEvenBoundary hX g).hom.toAddMonoidHom h₂,
    finite_exact_ends
      (cyclicEvenG X g).hom.toAddMonoidHom
      (evenOddBoundary hX g).hom.toAddMonoidHom h₅⟩

/-- For a cyclic group, the Herbrand quotient is the order of `H²` divided
by the order of `H¹`; Proposition II.3.4 identifies `H²` with `H_T⁰`. -/
def herbrandQuotient (A : Rep k G)
    [Finite (groupCohomology A 2)] [Finite (groupCohomology A 1)] : ℚˣ :=
  addCardUnit (groupCohomology A 2) /
    addCardUnit (groupCohomology A 1)

private theorem cyclic_herbrand_mul
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)] [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₂ g)] [Finite (cyclicTateEven X.X₂ g)]
    [Finite (cyclicTateOdd X.X₃ g)] [Finite (cyclicTateEven X.X₃ g)] :
    addCardUnit (cyclicTateEven X.X₂ g) /
        addCardUnit (cyclicTateOdd X.X₂ g) =
      (addCardUnit (cyclicTateEven X.X₁ g) /
          addCardUnit (cyclicTateOdd X.X₁ g)) *
        (addCardUnit (cyclicTateEven X.X₃ g) /
          addCardUnit (cyclicTateOdd X.X₃ g)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := cyclic_exact_hexagon hX g
  have hcard := card_exact_hexagon
    (cyclicOddF X g).hom.toAddMonoidHom
    (cyclicOddG X g).hom.toAddMonoidHom
    (oddEvenBoundary hX g).hom.toAddMonoidHom
    (cyclicEvenF X g).hom.toAddMonoidHom
    (cyclicEvenG X g).hom.toAddMonoidHom
    (evenOddBoundary hX g).hom.toAddMonoidHom
    h₁ h₂ h₃ h₄ h₅ h₆
  simp only [div_eq_mul_inv]
  calc
    addCardUnit (cyclicTateEven X.X₂ g) *
          (addCardUnit (cyclicTateOdd X.X₂ g))⁻¹ =
        ((addCardUnit (cyclicTateOdd X.X₁ g) *
              addCardUnit (cyclicTateOdd X.X₃ g))⁻¹ *
            (addCardUnit (cyclicTateOdd X.X₁ g) *
              addCardUnit (cyclicTateOdd X.X₃ g) *
                addCardUnit (cyclicTateEven X.X₂ g))) *
          (addCardUnit (cyclicTateOdd X.X₂ g))⁻¹ := by group
    _ = ((addCardUnit (cyclicTateOdd X.X₁ g) *
              addCardUnit (cyclicTateOdd X.X₃ g))⁻¹ *
            (addCardUnit (cyclicTateOdd X.X₂ g) *
              addCardUnit (cyclicTateEven X.X₁ g) *
                addCardUnit (cyclicTateEven X.X₃ g))) *
          (addCardUnit (cyclicTateOdd X.X₂ g))⁻¹ := by rw [hcard]
    _ = (addCardUnit (cyclicTateEven X.X₁ g) *
            (addCardUnit (cyclicTateOdd X.X₁ g))⁻¹) *
          (addCardUnit (cyclicTateEven X.X₃ g) *
            (addCardUnit (cyclicTateOdd X.X₃ g))⁻¹) := by
      simp [mul_assoc, mul_left_comm, mul_comm]

private theorem card_unit_iso
    {A B : ModuleCat k} [Finite A] [Finite B] (e : A ≅ B) :
    addCardUnit A = addCardUnit B := by
  apply Units.ext
  simp only [card_unit_val]
  exact_mod_cast Nat.card_congr e.toLinearEquiv.toEquiv

set_option linter.unusedFintypeInType false in
/-- If the Herbrand quotients of the two end terms are defined, then the
Herbrand quotient of the middle term is defined. -/
theorem herbrand_quotient_middle
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    Finite (groupCohomology X.X₂ 1) ∧ Finite (groupCohomology X.X₂ 2) := by
  letI : Finite (cyclicTateOdd X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 1)
      (cyclicOddIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 2)
      (cyclicEvenIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 1)
      (cyclicOddIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 2)
      (cyclicEvenIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  obtain ⟨hOdd, hEven⟩ := cyclic_tate_middle hX g
  letI : Finite (cyclicTateOdd X.X₂ g) := hOdd
  letI : Finite (cyclicTateEven X.X₂ g) := hEven
  exact ⟨
    Finite.of_equiv (cyclicTateOdd X.X₂ g)
      (cyclicOddIso X.X₂ g hg).toLinearEquiv.toEquiv,
    Finite.of_equiv (cyclicTateEven X.X₂ g)
      (cyclicEvenIso X.X₂ g hg).toLinearEquiv.toEquiv⟩

set_option linter.unusedFintypeInType false in
/-- If the Herbrand quotients of the middle and right terms are defined,
then the Herbrand quotient of the left term is defined. -/
theorem herbrand_quotient_left
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₂ 1)] [Finite (groupCohomology X.X₂ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    Finite (groupCohomology X.X₁ 1) ∧ Finite (groupCohomology X.X₁ 2) := by
  letI : Finite (cyclicTateOdd X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 1)
      (cyclicOddIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 2)
      (cyclicEvenIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 1)
      (cyclicOddIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 2)
      (cyclicEvenIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  obtain ⟨hOdd, hEven⟩ := cyclic_tate_left hX g
  letI : Finite (cyclicTateOdd X.X₁ g) := hOdd
  letI : Finite (cyclicTateEven X.X₁ g) := hEven
  exact ⟨
    Finite.of_equiv (cyclicTateOdd X.X₁ g)
      (cyclicOddIso X.X₁ g hg).toLinearEquiv.toEquiv,
    Finite.of_equiv (cyclicTateEven X.X₁ g)
      (cyclicEvenIso X.X₁ g hg).toLinearEquiv.toEquiv⟩

set_option linter.unusedFintypeInType false in
/-- If the Herbrand quotients of the left and middle terms are defined, then
the Herbrand quotient of the right term is defined. -/
theorem herbrand_quotient_right
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₂ 1)] [Finite (groupCohomology X.X₂ 2)] :
    Finite (groupCohomology X.X₃ 1) ∧ Finite (groupCohomology X.X₃ 2) := by
  letI : Finite (cyclicTateOdd X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 1)
      (cyclicOddIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 2)
      (cyclicEvenIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateOdd X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 1)
      (cyclicOddIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 2)
      (cyclicEvenIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  obtain ⟨hOdd, hEven⟩ := cyclic_tate_right hX g
  letI : Finite (cyclicTateOdd X.X₃ g) := hOdd
  letI : Finite (cyclicTateEven X.X₃ g) := hEven
  exact ⟨
    Finite.of_equiv (cyclicTateOdd X.X₃ g)
      (cyclicOddIso X.X₃ g hg).toLinearEquiv.toEquiv,
    Finite.of_equiv (cyclicTateEven X.X₃ g)
      (cyclicEvenIso X.X₃ g hg).toLinearEquiv.toEquiv⟩

set_option linter.unusedFintypeInType false in
/-- **Proposition II.3.6.** The Herbrand quotient is multiplicative in a
short exact sequence of modules for a finite cyclic group. -/
theorem herbrandQuotient_mul
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₂ 1)] [Finite (groupCohomology X.X₂ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    herbrandQuotient X.X₂ = herbrandQuotient X.X₁ * herbrandQuotient X.X₃ := by
  letI : Finite (cyclicTateOdd X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 1)
      (cyclicOddIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₁ g) := Finite.of_equiv
    (groupCohomology X.X₁ 2)
      (cyclicEvenIso X.X₁ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateOdd X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 1)
      (cyclicOddIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₂ g) := Finite.of_equiv
    (groupCohomology X.X₂ 2)
      (cyclicEvenIso X.X₂ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 1)
      (cyclicOddIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) := Finite.of_equiv
    (groupCohomology X.X₃ 2)
      (cyclicEvenIso X.X₃ g hg).symm.toLinearEquiv.toEquiv
  have hmul := cyclic_herbrand_mul hX g
  have hOdd₁ := card_unit_iso
    (cyclicOddIso X.X₁ g hg)
  have hEven₁ := card_unit_iso
    (cyclicEvenIso X.X₁ g hg)
  have hOdd₂ := card_unit_iso
    (cyclicOddIso X.X₂ g hg)
  have hEven₂ := card_unit_iso
    (cyclicEvenIso X.X₂ g hg)
  have hOdd₃ := card_unit_iso
    (cyclicOddIso X.X₃ g hg)
  have hEven₃ := card_unit_iso
    (cyclicEvenIso X.X₃ g hg)
  simpa only [herbrandQuotient, hOdd₁, hEven₁, hOdd₂, hEven₂, hOdd₃, hEven₃]
    using hmul

end

end Towers.CField.Shifting
