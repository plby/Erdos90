import Towers.Algebra.TruncatedJennings.MonomialBasis


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

universe u v

namespace Towers

/-- The basis indices whose weight survives modulo the cutoff `n`. -/
abbrev basisLowIndex
    {κ : Type v}
    (wt : κ → ℕ)
    (n : ℕ) : Type v :=
  { e : κ // wt e < n }

/-- Pulling a finitely supported function on a subtype back to the subtype after extending by
zero is the identity. -/
lemma finsupp_subtype_emb
    {α : Type u}
    {R : Type v}
    [Zero R]
    (p : α → Prop)
    (f : Subtype p →₀ R) :
    Finsupp.subtypeDomain p
        (Finsupp.embDomain (Function.Embedding.subtype p) f) =
      f := by
  ext i
  rw [Finsupp.subtypeDomain_apply, Finsupp.embDomain_apply]
  split
  · rename_i h
    have hchoose : h.choose = i := Subtype.ext h.choose_spec
    rw [hchoose]
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

/-- The coordinate map retaining exactly the basis coordinates of weight below `n`. -/
def basisLowCoordinate
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ) :
    denseGroupAlgebra p Q →ₗ[ZMod p]
      basisLowIndex wt n →₀ ZMod p where
  toFun x :=
    Finsupp.subtypeDomain (fun e : κ => wt e < n) (B.repr x)
  map_add' x y := by
    ext e
    simp [Finsupp.subtypeDomain_apply]
  map_smul' c x := by
    ext e
    simp [Finsupp.subtypeDomain_apply]

@[simp]
lemma basis_low_coordinate
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (x : denseGroupAlgebra p Q)
    (e : basisLowIndex wt n) :
    basisLowCoordinate (p := p) (Q := Q) B wt n x e =
      B.repr x e.1 := by
  rfl

/-- The low-coordinate map has kernel exactly the high-weight basis span. -/
lemma low_high_span
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ) :
    (basisLowCoordinate (p := p) (Q := Q) B wt n).ker =
      basisHighSpan (p := p) (Q := Q) B wt n := by
  ext x
  constructor
  · intro hx
    rw [basis_high_repr (B := B) (wt := wt)]
    intro e he
    change basisLowCoordinate (p := p) (Q := Q) B wt n x = 0 at hx
    have hcoord :=
      congrArg
        (fun f : basisLowIndex wt n →₀ ZMod p => f ⟨e, he⟩)
        hx
    simpa using hcoord
  · intro hx
    rw [basis_high_repr (B := B) (wt := wt)] at hx
    change basisLowCoordinate (p := p) (Q := Q) B wt n x = 0
    ext e
    exact hx e.1 e.2

/-- The low-coordinate map is onto: extend a finitely supported low-coordinate vector by zero
and reconstruct the ambient vector using the original basis. -/
lemma basis_low_surjective
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ) :
    Function.Surjective
      (basisLowCoordinate (p := p) (Q := Q) B wt n) := by
  intro f
  refine
    ⟨B.repr.symm
      (Finsupp.embDomain
        (Function.Embedding.subtype (fun e : κ => wt e < n)) f), ?_⟩
  change
    Finsupp.subtypeDomain (fun e : κ => wt e < n)
        (B.repr
          (B.repr.symm
            (Finsupp.embDomain
              (Function.Embedding.subtype (fun e : κ => wt e < n)) f))) =
      f
  rw [LinearEquiv.apply_symm_apply]
  exact
    finsupp_subtype_emb
      (fun e : κ => wt e < n) f

/-- The quotient coordinate map induced by low coordinates, for any quotient submodule known
to be the high-weight tail. -/
def basisLowRepr
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    (denseGroupAlgebra p Q ⧸ N) →ₗ[ZMod p]
      basisLowIndex wt n →₀ ZMod p :=
  N.liftQ
    (basisLowCoordinate (p := p) (Q := Q) B wt n)
    (by
      intro x hx
      have hxW :
          x ∈ basisHighSpan (p := p) (Q := Q) B wt n := by
        simpa [hN] using hx
      change
        x ∈ (basisLowCoordinate (p := p) (Q := Q) B wt n).ker
      simpa [low_high_span
        (p := p) (Q := Q) B wt n] using hxW)

@[simp]
lemma basis_low_repr
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n)
    (x : denseGroupAlgebra p Q) :
    basisLowRepr (p := p) (Q := Q) B wt n N hN
        (Submodule.Quotient.mk x) =
      basisLowCoordinate (p := p) (Q := Q) B wt n x := by
  simp [basisLowRepr]

lemma low_repr_injective
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    Function.Injective
      (basisLowRepr (p := p) (Q := Q) B wt n N hN) := by
  rw [← LinearMap.ker_eq_bot]
  ext q
  constructor
  · intro hq
    change
      basisLowRepr (p := p) (Q := Q) B wt n N hN q = 0 at hq
    induction q using Submodule.Quotient.induction_on with
    | H x =>
        have hlow :
            basisLowCoordinate (p := p) (Q := Q) B wt n x = 0 := by
          simpa using hq
        have hxW :
            x ∈ basisHighSpan (p := p) (Q := Q) B wt n := by
          have hxker :
              x ∈
                (basisLowCoordinate (p := p) (Q := Q) B wt n).ker := by
            exact hlow
          simpa [low_high_span
            (p := p) (Q := Q) B wt n] using hxker
        have hxN : x ∈ N := by
          simpa [hN] using hxW
        have hmk :
            (Submodule.Quotient.mk x :
              denseGroupAlgebra p Q ⧸ N) = 0 :=
          (Submodule.Quotient.mk_eq_zero N).mpr hxN
        simp [hmk]
  · intro hq
    have hzero : q = 0 := (Submodule.mem_bot (ZMod p)).mp hq
    simp [hzero]

lemma low_repr_surjective
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    Function.Surjective
      (basisLowRepr (p := p) (Q := Q) B wt n N hN) := by
  intro f
  obtain ⟨x, hx⟩ :=
    basis_low_surjective
      (p := p) (Q := Q) B wt n f
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  simpa [basis_low_repr] using hx

/-- The quotient by the high-weight tail is identified with the low-weight coordinate space. -/
def basisLowEquiv
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    (denseGroupAlgebra p Q ⧸ N) ≃ₗ[ZMod p]
      basisLowIndex wt n →₀ ZMod p :=
  LinearEquiv.ofBijective
    (basisLowRepr (p := p) (Q := Q) B wt n N hN)
    ⟨low_repr_injective
      (p := p) (Q := Q) B wt n N hN,
     low_repr_surjective
      (p := p) (Q := Q) B wt n N hN⟩

@[simp]
lemma basis_low_mk
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n)
    (x : denseGroupAlgebra p Q) :
    basisLowEquiv (p := p) (Q := Q) B wt n N hN
        (Submodule.Quotient.mk x) =
      basisLowCoordinate (p := p) (Q := Q) B wt n x := by
  rfl

/-- The surviving low-weight basis vectors form a basis of the quotient by the high-weight
tail. -/
def basisLowQuotient
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    Module.Basis (basisLowIndex wt n) (ZMod p)
      (denseGroupAlgebra p Q ⧸ N) :=
  Module.Basis.ofRepr
    (basisLowEquiv (p := p) (Q := Q) B wt n N hN)

@[simp]
lemma low_repr_mk
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n)
    (x : denseGroupAlgebra p Q) :
    (basisLowQuotient (p := p) (Q := Q) B wt n N hN).repr
        (Submodule.Quotient.mk x) =
      basisLowCoordinate (p := p) (Q := Q) B wt n x := by
  rfl

@[simp]
lemma basis_low_quotient
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n)
    (e : basisLowIndex wt n) :
    basisLowQuotient (p := p) (Q := Q) B wt n N hN e =
      Submodule.Quotient.mk (B e.1) := by
  apply
    (basisLowQuotient
      (p := p) (Q := Q) B wt n N hN).repr.injective
  rw [Module.Basis.repr_self]
  rw [low_repr_mk]
  ext f
  by_cases hfe : f = e
  · subst f
    simp [basisLowCoordinate]
  · have hval : (f : κ) ≠ e.1 := by
      intro h
      exact hfe (Subtype.ext h)
    simp [basisLowCoordinate, hfe, hval]

/-- The image of the high-weight span of cutoff `m` in the quotient by the cutoff `n` is exactly
the span of surviving basis vectors whose weights are at least `m`. -/
lemma high_q_low
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (m n : ℕ)
    (N : Submodule (ZMod p) (denseGroupAlgebra p Q))
    (hN : N = basisHighSpan (p := p) (Q := Q) B wt n) :
    Submodule.map (N.mkQ)
        (basisHighSpan (p := p) (Q := Q) B wt m) =
      Submodule.span (ZMod p)
        (basisLowQuotient (p := p) (Q := Q) B wt n N hN ''
          { e : basisLowIndex wt n | m ≤ wt e.1 }) := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    rw [
      (basisLowQuotient
        (p := p) (Q := Q) B wt n N hN).mem_span_image]
    intro e he
    by_contra hnot
    have hlt : wt e.1 < m := Nat.lt_of_not_ge hnot
    have hcoord :
        (basisLowQuotient
            (p := p) (Q := Q) B wt n N hN).repr
          (N.mkQ x) e = 0 := by
      rw [Submodule.mkQ_apply, low_repr_mk]
      exact
        basis_repr_high
          (B := B) (wt := wt) hx hlt
    have hne :
        (basisLowQuotient
            (p := p) (Q := Q) B wt n N hN).repr
          (N.mkQ x) e ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using he
    exact hne hcoord
  · apply Submodule.span_le.mpr
    rintro q ⟨e, he, rfl⟩
    rw [basis_low_quotient]
    change N.mkQ (B e.1) ∈
      Submodule.map (N.mkQ)
        (basisHighSpan (p := p) (Q := Q) B wt m)
    exact
      ⟨B e.1,
        basis_high_weight
          (B := B) (wt := wt) he,
        rfl⟩

/-- At cutoff zero, the high-weight span is the whole space. -/
lemma basis_high_top
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ) :
    basisHighSpan (p := p) (Q := Q) B wt 0 = ⊤ := by
  unfold basisHighSpan
  simp

/-- The zeroth augmentation power is the whole group algebra. -/
lemma augmentation_ideal_top
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] :
    augmentationIdealPower p Q 0 = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Submodule.mem_top
  · intro _hx
    change
      x ∈
        Submodule.restrictScalars (ZMod p)
          ((denseGeneratorsIdeal p Q) ^ 0)
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

namespace TJennin

namespace MBData

namespace HMData

/-- Step 11 equality for every augmentation power, including the zeroth one. -/
lemma high_weight_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (s : ℕ) :
    augmentationIdealPower p Q s = B.highWeightSpan s := by
  cases s with
  | zero =>
      rw [augmentation_ideal_top]
      change
        (⊤ : Submodule (ZMod p) (denseGroupAlgebra p Q)) =
          basisHighSpan (p := p) (Q := Q) B.basis B.weight 0
      exact
        (basis_high_top
          (p := p) (Q := Q) (B := B.basis) (wt := B.weight)).symm
  | succ s =>
      exact M.augmentation_high_span s

/-- The quotient basis in `F_p[Q] / I^n` given by low-weight ordered Jennings monomials. -/
def augmentationQuotientBasis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (n : ℕ) :
    Module.Basis (basisLowIndex B.weight n) (ZMod p)
      (denseGroupAlgebra p Q ⧸ augmentationIdealPower p Q n) :=
  basisLowQuotient
    (p := p) (Q := Q) B.basis B.weight n
    (augmentationIdealPower p Q n)
    (M.high_weight_span n)

@[simp]
lemma augmentation_quotient_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (n : ℕ)
    (e : basisLowIndex B.weight n) :
    M.augmentationQuotientBasis n e =
      Submodule.Quotient.mk (B.basis e.1) := by
  simp [augmentationQuotientBasis]

/-- In concrete Jennings coordinates, each quotient basis vector is the image of the ordered
monomial `∏ᵢ ([hᵢ]-1)^{bᵢ}`. -/
lemma jennings_monomial_fin
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (n : ℕ)
    (e : basisLowIndex B.weight n) :
    M.augmentationQuotientBasis n e =
      Submodule.Quotient.mk
        (jenningsMonomialFin p Q R.gen (B.monomialIndex e.1)) := by
  rw [augmentation_quotient_basis]
  congr
  exact B.basis_apply e.1

/-- The image of `I^m` in `F_p[Q] / I^n` is exactly the span of those surviving ordered
Jennings monomials whose Hall/Jennings weight is at least `m`. -/
theorem image_span_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {cutoff : ℕ}
    {R : OZReps p Q cutoff}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (m n : ℕ) :
    Submodule.map (Submodule.mkQ (augmentationIdealPower p Q n))
        (augmentationIdealPower p Q m) =
      Submodule.span (ZMod p)
        (M.augmentationQuotientBasis n ''
          { e : basisLowIndex B.weight n | m ≤ B.weight e.1 }) := by
  have hbase :=
    high_q_low
      (p := p) (Q := Q) B.basis B.weight m n
      (augmentationIdealPower p Q n)
      (M.high_weight_span n)
  simpa [augmentationQuotientBasis,
    M.high_weight_span m] using hbase

end HMData

/-- Filtered Hall--PBW description modulo the augmentation filtration.

The basis is indexed by exponent vectors of Hall/Jennings weight `< n`; the basis vector is the
image of the corresponding ordered monomial. The image of `I^m` is the span of exactly the
surviving basis vectors of weight at least `m`. -/
structure FPDescri
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {cutoff : ℕ}
    {R : OZReps p Q cutoff}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (n : ℕ) :
    Type (max (u + 1) (v + 1)) where
  quotientBasis :
    Module.Basis (basisLowIndex B.weight n) (ZMod p)
      (denseGroupAlgebra p Q ⧸ augmentationIdealPower p Q n)
  quotientBasis_apply :
    ∀ e : basisLowIndex B.weight n,
      quotientBasis e =
        Submodule.Quotient.mk
          (jenningsMonomialFin p Q R.gen (B.monomialIndex e.1))
  image_augmentation_span :
    ∀ m : ℕ,
      Submodule.map (Submodule.mkQ (augmentationIdealPower p Q n))
          (augmentationIdealPower p Q m) =
        Submodule.span (ZMod p)
          (quotientBasis ''
            { e : basisLowIndex B.weight n | m ≤ B.weight e.1 })

namespace FPDescri

/-- Lowest Hall-weight detection in the quotient expansion.

Writing `z` in the quotient basis from the filtered Hall--PBW description, membership in the
image of `I^m` is equivalent to the vanishing of all coefficients whose Hall/Jennings weight is
strictly below `m`. -/
theorem coefficients_vanish_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {cutoff : ℕ}
    {R : OZReps p Q cutoff}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    {n : ℕ}
    (D : FPDescri (p := p) (Q := Q) B n)
    (m : ℕ)
    (z : denseGroupAlgebra p Q ⧸ augmentationIdealPower p Q n) :
    z ∈
        Submodule.map (Submodule.mkQ (augmentationIdealPower p Q n))
          (augmentationIdealPower p Q m) ↔
      ∀ e : basisLowIndex B.weight n,
        B.weight e.1 < m → D.quotientBasis.repr z e = 0 := by
  rw [D.image_augmentation_span m]
  rw [D.quotientBasis.mem_span_image]
  constructor
  · intro hspan e he
    by_contra hcoeff
    have hsupp : e ∈ (D.quotientBasis.repr z).support := by
      simpa [Finsupp.mem_support_iff] using hcoeff
    exact (not_le_of_gt he) (hspan hsupp)
  · intro hvanish e he
    by_contra hnot
    have hlt : B.weight e.1 < m := Nat.lt_of_not_ge hnot
    have hcoeff_zero : D.quotientBasis.repr z e = 0 := hvanish e hlt
    have hcoeff_ne : D.quotientBasis.repr z e ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using he
    exact hcoeff_ne hcoeff_zero

end FPDescri

namespace HMData

/-- Construct the filtered Hall--PBW quotient description from the multiplicative high-weight
Jennings data. -/
def filteredPBWDescription
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {cutoff : ℕ}
    {R : OZReps p Q cutoff}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (n : ℕ) :
    FPDescri (p := p) (Q := Q) B n where
  quotientBasis := M.augmentationQuotientBasis n
  quotientBasis_apply := by
    intro e
    exact M.jennings_monomial_fin n e
  image_augmentation_span := by
    intro m
    exact M.image_span_basis m n

/-- Lowest Hall-weight detection for the constructed quotient Hall--PBW basis. -/
theorem lowestWeightDetection
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {cutoff : ℕ}
    {R : OZReps p Q cutoff}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (m n : ℕ)
    (z : denseGroupAlgebra p Q ⧸ augmentationIdealPower p Q n) :
    z ∈
        Submodule.map (Submodule.mkQ (augmentationIdealPower p Q n))
          (augmentationIdealPower p Q m) ↔
      ∀ e : basisLowIndex B.weight n,
        B.weight e.1 < m → (M.augmentationQuotientBasis n).repr z e = 0 := by
  exact
    (M.filteredPBWDescription n).coefficients_vanish_below
      m z

end HMData

end MBData

end TJennin

end Towers
