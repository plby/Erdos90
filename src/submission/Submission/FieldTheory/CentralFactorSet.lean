import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.CrossedProducts.CohomologyRestriction
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# Factor sets of central embedding problems

This file gives the elementary nonabelian algebra used in the central cubic
embedding step.  A normalized set-theoretic section of a surjective
homomorphism with central kernel determines a factor set.  Trivializing that
factor set is equivalent to splitting the homomorphism.
-/

noncomputable section

universe u v

open Submission.CField.CProduca

namespace Submission.CField.CProduca

namespace NMCocycl₂

/-- Map the coefficients of a normalized multiplicative cocycle along an
equivariant homomorphism.  Unlike the transport construction in class field
theory, this does not require the coefficient map to be an isomorphism. -/
def mapCoefficients
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    NMCocycl₂ (G := G) (M := N) where
  toFun p := f (c p)
  isMulCocycle₂ g h j := by
    calc
      f (c (g * h, j)) * f (c (g, h)) =
          f (c (g * h, j) * c (g, h)) := (map_mul f _ _).symm
      _ = f ((g • c (h, j)) * c (g, h * j)) := by
        rw [c.isMulCocycle₂]
      _ = f (g • c (h, j)) * f (c (g, h * j)) := map_mul f _ _
      _ = (g • f (c (h, j))) * f (c (g, h * j)) := by rw [hf]
  map_one_fst g := by simp
  map_one_snd g := by simp

@[simp]
theorem mapCoefficients_apply
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (c : NMCocycl₂ (G := G) (M := M)) (p : G × G) :
    mapCoefficients f hf c p = f (c p) :=
  rfl

/-- Mapping coefficients is multiplicative on normalized cocycles. -/
def mapCoefficientsHom
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m) :
    NMCocycl₂ (G := G) (M := M) →*
      NMCocycl₂ (G := G) (M := N) where
  toFun := mapCoefficients f hf
  map_one' := by
    apply ext
    intro p
    simp
  map_mul' c d := by
    apply ext
    intro p
    simp

end NMCocycl₂

namespace MHTwo

/-- The morphism of additive representations underlying an equivariant
multiplicative coefficient homomorphism. -/
def coefficientRepHom
    {G M N : Type} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m) :
    Rep.ofMulDistribMulAction G M ⟶ Rep.ofMulDistribMulAction G N :=
  Rep.ofHom
    { toLinearMap := (MonoidHom.toAdditive f).toIntLinearMap
      isIntertwining' := fun g ↦ by
        ext m
        exact congrArg Additive.ofMul (hf g m.toMul) }

/-- An equivariant coefficient homomorphism preserves cohomology of
normalized multiplicative cocycles. -/
theorem cohomologous_coefficients
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) :
    IsCohomologous
      (NMCocycl₂.mapCoefficients f hf c)
      (NMCocycl₂.mapCoefficients f hf d) := by
  obtain ⟨x, hx⟩ := hcd
  refine ⟨fun g ↦ f (x g), ?_⟩
  intro g h
  calc
    g • f (x h) / f (x (g * h)) * f (x g) =
        f (g • x h) / f (x (g * h)) * f (x g) := by rw [hf]
    _ = f ((g • x h) / x (g * h) * x g) := by
      rw [map_mul, map_div]
    _ = f (c (g, h) / d (g, h)) := by rw [hx]
    _ = f (c (g, h)) / f (d (g, h)) := map_div f _ _

/-- An equivariant coefficient homomorphism induces a homomorphism on
multiplicative second cohomology. -/
def mapCoefficientsHom
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m) :
    MHTwo G M →* MHTwo G N where
  toFun := Quotient.map
    (NMCocycl₂.mapCoefficients f hf)
    (fun _ _ h ↦ cohomologous_coefficients f hf h)
  map_one' := congrArg mk
    ((NMCocycl₂.mapCoefficientsHom f hf).map_one)
  map_mul' x y := by
    induction x, y using Quotient.inductionOn₂ with
    | _ c d =>
        exact congrArg mk
          ((NMCocycl₂.mapCoefficientsHom f hf).map_mul c d)

@[simp]
theorem coefficients_hom_mk
    {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    mapCoefficientsHom f hf (mk c) =
      mk (NMCocycl₂.mapCoefficients f hf c) :=
  rfl

/-- Equivariant transport is natural in the coefficient module. -/
theorem transport_coefficients_hom
    {G H M N M' N' : Type*}
    [Group G] [Group H]
    [CommGroup M] [CommGroup N] [CommGroup M'] [CommGroup N']
    [MulDistribMulAction G M] [MulDistribMulAction H N]
    [MulDistribMulAction G M'] [MulDistribMulAction H N']
    (eG : G ≃* H) (eM : M ≃* N) (eM' : M' ≃* N')
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m)
    (heq' : ∀ (g : G) (m : M'), eM' (g • m) = eG g • eM' m)
    (f : M →* M') (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (f' : N →* N') (hf' : ∀ (h : H) (n : N), f' (h • n) = h • f' n)
    (hcomm : ∀ m : M, eM' (f m) = f' (eM m))
    (x : MHTwo G M) :
    Submission.CField.LBrauer.MHTrans.h2Equiv
        eG eM' heq' (mapCoefficientsHom f hf x) =
      mapCoefficientsHom f' hf'
        (Submission.CField.LBrauer.MHTrans.h2Equiv
          eG eM heq x) := by
  induction x using Quotient.inductionOn with
  | _ c =>
      apply congrArg MHTwo.mk
      apply NMCocycl₂.ext
      rintro ⟨h, j⟩
      exact hcomm (c (eG.symm h, eG.symm j))

/-- Restricting a class and then changing coefficients agrees with changing
coefficients first and then restricting. -/
theorem restriction_hom_coefficients
    {H G M N : Type*}
    [Group H] [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H M]
    [MulDistribMulAction G N] [MulDistribMulAction H N]
    (r : H →* G)
    (hM : ∀ h : H, ∀ m : M, h • m = r h • m)
    (hN : ∀ h : H, ∀ n : N, h • n = r h • n)
    (f : M →* N)
    (fG : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (fH : ∀ h : H, ∀ m : M, f (h • m) = h • f m)
    (x : MHTwo G M) :
    restrictionHom r hN (mapCoefficientsHom f fG x) =
      mapCoefficientsHom f fH (restrictionHom r hM x) := by
  induction x using Quotient.inductionOn with
  | _ c => rfl

/-- Successive equivariant changes of coefficients agree with their
composite. -/
theorem coefficients_hom_comp
    {G M N P : Type*}
    [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [MulDistribMulAction G P]
    (f : M →* N) (g : N →* P)
    (fG : ∀ σ : G, ∀ m : M, f (σ • m) = σ • f m)
    (gG : ∀ σ : G, ∀ n : N, g (σ • n) = σ • g n)
    (gfG : ∀ σ : G, ∀ m : M, (g.comp f) (σ • m) = σ • (g.comp f) m)
    (x : MHTwo G M) :
    mapCoefficientsHom g gG (mapCoefficientsHom f fG x) =
      mapCoefficientsHom (g.comp f) gfG x := by
  induction x using Quotient.inductionOn with
  | _ c => rfl

/-- A coefficient homomorphism that is pointwise trivial induces the trivial
map on multiplicative second cohomology. -/
theorem coefficients_hom_forall
    {G M N : Type*}
    [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N)
    (hf : ∀ σ : G, ∀ m : M, f (σ • m) = σ • f m)
    (htrivial : ∀ m : M, f m = 1)
    (x : MHTwo G M) :
    mapCoefficientsHom f hf x = 1 := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change mk (NMCocycl₂.mapCoefficients f hf c) = mk 1
      apply congrArg mk
      ext p
      exact htrivial (c p)

/-- An equivariant multiplicative equivalence gives an injective change of
coefficients map on multiplicative second cohomology. -/
theorem coefficients_hom_injective
    {G M N : Type*}
    [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (e : M ≃* N)
    (he : ∀ g : G, ∀ m : M, e (g • m) = g • e m) :
    Function.Injective (mapCoefficientsHom e.toMonoidHom he) := by
  let he' : ∀ g : G, ∀ n : N, e.symm (g • n) = g • e.symm n := by
    intro g n
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  intro x y hxy
  have hleft (z : MHTwo G M) :
      mapCoefficientsHom e.symm.toMonoidHom he'
          (mapCoefficientsHom e.toMonoidHom he z) = z := by
    induction z using Quotient.inductionOn with
    | _ c =>
        apply congrArg mk
        apply NMCocycl₂.ext
        intro p
        exact e.symm_apply_apply (c p)
  have h := congrArg
    (mapCoefficientsHom e.symm.toMonoidHom he') hxy
  rwa [hleft x, hleft y] at h

/-- In particular, changing coefficients along an equivariant
multiplicative equivalence detects the trivial class. -/
theorem coefficients_hom_equiv
    {G M N : Type*}
    [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (e : M ≃* N)
    (he : ∀ g : G, ∀ m : M, e (g • m) = g • e m)
    (x : MHTwo G M) :
    mapCoefficientsHom e.toMonoidHom he x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply coefficients_hom_injective e he
    simpa using hx
  · rintro rfl
    exact map_one _

/-- The ordinary degree-two group-cohomology class represented by a
normalized multiplicative cocycle. -/
noncomputable def groupCohomologyRepresentative
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : NMCocycl₂ (G := G) (M := M)) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G M) :=
  groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
    (groupCohomology.cocyclesOfIsMulCocycle₂ c.isMulCocycle₂)

theorem group_repre_cohom
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) :
    groupCohomologyRepresentative c =
      groupCohomologyRepresentative d := by
  unfold groupCohomologyRepresentative
  rw [groupCohomology.H2π_eq_iff]
  change
    (Additive.ofMul ∘ c) - (Additive.ofMul ∘ d) ∈
      groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G M)
  have hboundary :=
    (groupCohomology.coboundariesOfIsMulCoboundary₂ hcd).property
  convert hboundary using 1

/-- Multiplicative `H²` maps canonically to Mathlib's ordinary
degree-two group cohomology of the associated additive representation. -/
noncomputable def toGroupCohomology
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    MHTwo G M →
      groupCohomology.H2 (Rep.ofMulDistribMulAction G M) :=
  Quotient.lift groupCohomologyRepresentative
    (fun _ _ h ↦ group_repre_cohom h)

@[simp]
theorem group_cohomology_mk
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : NMCocycl₂ (G := G) (M := M)) :
    toGroupCohomology (mk c) = groupCohomologyRepresentative c :=
  rfl

/-- The comparison from normalized multiplicative `H²` to ordinary group
cohomology is natural in the coefficient module. -/
theorem cohomology_coefficients_hom
    {G M N : Type} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (x : MHTwo G M) :
    toGroupCohomology (mapCoefficientsHom f hf x) =
      groupCohomology.map (MonoidHom.id G)
        (coefficientRepHom f hf) 2
        (toGroupCohomology x) := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change groupCohomology.H2π (Rep.ofMulDistribMulAction G N) _ =
        groupCohomology.map (MonoidHom.id G) _ 2
          (groupCohomology.H2π (Rep.ofMulDistribMulAction G M) _)
      rw [groupCohomology.H2π_comp_map_apply]
      congr 1

/-- The comparison with ordinary group cohomology detects the zero
multiplicative `H²` class. -/
theorem group_cohomology_zero
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (x : MHTwo G M) :
    toGroupCohomology x = 0 ↔ x = 1 := by
  obtain ⟨c, rfl⟩ := exists_mk_eq x
  rw [group_cohomology_mk]
  rw [show (1 : MHTwo G M) = mk 1 from rfl]
  rw [mk_eq_iff]
  unfold groupCohomologyRepresentative
  rw [groupCohomology.H2π_eq_zero_iff]
  change
    (Additive.ofMul ∘ c) ∈
        groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G M) ↔
      groupCohomology.IsMulCoboundary₂ (fun p ↦ c p / (1 : NMCocycl₂
        (G := G) (M := M)) p)
  constructor
  · intro hc
    simpa using
      (groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
        (M := M) (Additive.ofMul ∘ c) hc)
  · intro hc
    simpa using
      (groupCohomology.coboundariesOfIsMulCoboundary₂
        (show groupCohomology.IsMulCoboundary₂ c from by simpa using hc)).property

end MHTwo

/-- If an `n`-torsion multiplicative two-cocycle is the coboundary of a
cochain `b`, then the pointwise `n`th powers of `b` form a one-cocycle.  This
is the elementary Kummer calculation preceding Hilbert 90. -/
theorem groupCohomology.isMulCocycle₁_pow_of_coboundary_eq_torsion
    {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (n : ℕ)
    (c : NMCocycl₂ (G := G) (M := M))
    (b : G → M)
    (hb : ∀ g h : G,
      g • b h / b (g * h) * b g = c (g, h))
    (hc : ∀ g h : G, c (g, h) ^ n = 1) :
    groupCohomology.IsMulCocycle₁ (fun g => b g ^ n) := by
  intro g h
  have heq : b (g * h) * c (g, h) = (g • b h) * b g := by
    calc
      b (g * h) * c (g, h) =
          b (g * h) * ((g • b h / b (g * h)) * b g) := by rw [hb]
      _ = (b (g * h) * (b (g * h))⁻¹) * ((g • b h) * b g) := by
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = (g • b h) * b g := by simp
  calc
    b (g * h) ^ n = b (g * h) ^ n * c (g, h) ^ n := by rw [hc, mul_one]
    _ = (b (g * h) * c (g, h)) ^ n := (mul_pow _ _ _).symm
    _ = ((g • b h) * b g) ^ n := by rw [heq]
    _ = (g • b h) ^ n * b g ^ n := mul_pow _ _ _
    _ = g • b h ^ n * b g ^ n := by rw [smul_pow']

end Submission.CField.CProduca

namespace Submission
namespace TBluepr

open scoped commutatorElement

/-- The Koch relation is equivalent to the usual tame conjugation relation. -/
theorem tame_relation_conjugation
    {G : Type*} [Group G] (x y : G) {n : ℕ} (hn : 1 ≤ n) :
    x ^ (n - 1) * ⁅x, y⁆ = 1 ↔ y * x * y⁻¹ = x ^ n := by
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpow : x ^ (n - 1) * x = x ^ n := by
    rw [← pow_succ, hsucc]
  constructor
  · intro hrelation
    have hword : x ^ n * y * x⁻¹ * y⁻¹ = 1 := by
      calc
        x ^ n * y * x⁻¹ * y⁻¹ =
            (x ^ (n - 1) * x) * y * x⁻¹ * y⁻¹ := by rw [hpow]
        _ = x ^ (n - 1) * (x * y * x⁻¹ * y⁻¹) := by group
        _ = x ^ (n - 1) * ⁅x, y⁆ := by
          rw [commutatorElement_def]
        _ = 1 := hrelation
    apply eq_of_mul_inv_eq_one
    calc
      (y * x * y⁻¹) * (x ^ n)⁻¹ =
          (x ^ n * y * x⁻¹ * y⁻¹)⁻¹ := by group
      _ = 1 := by rw [hword, inv_one]
  · intro hconj
    rw [commutatorElement_def]
    calc
      x ^ (n - 1) * (x * y * x⁻¹ * y⁻¹) =
          (x ^ (n - 1) * x) * y * x⁻¹ * y⁻¹ := by group
      _ = x ^ n * y * x⁻¹ * y⁻¹ := by rw [hpow]
      _ = (y * x * y⁻¹) * y * x⁻¹ * y⁻¹ := by rw [hconj]
      _ = 1 := by group

/-- The trivial multiplicative action, made explicit so that central kernels
can be used as coefficient groups in multiplicative cohomology. -/
@[implicit_reducible]
def trivialDistribAction
    (G K : Type*) [Group G] [Monoid K] : MulDistribMulAction G K where
  smul := fun _ k => k
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_mul := fun _ _ _ => rfl
  smul_one := fun _ => rfl

@[simp]
theorem trivial_distrib_smul
    (G K : Type*) [Group G] [Monoid K] (g : G) (k : K) :
    @HSMul.hSMul G K K
        (@instHSMul G K (trivialDistribAction G K).toSMul) g k = k :=
  rfl

/-- A normalized factor set for a central extension with trivial action on its
kernel.  The cocycle identity is written in the order arising from
`s(g) * s(h) = c(g,h) * s(gh)`. -/
structure CFSet
    (G K : Type*) [Group G] [Group K] where
  toFun : G × G → K
  map_one_fst : ∀ g, toFun (1, g) = 1
  map_one_snd : ∀ g, toFun (g, 1) = 1
  cocycle : ∀ g h j,
    toFun (g, h) * toFun (g * h, j) =
      toFun (h, j) * toFun (g, h * j)

namespace CFSet

instance {G K : Type*} [Group G] [Group K] :
    CoeFun (CFSet G K) (fun _ => G × G → K) :=
  ⟨toFun⟩

@[simp]
theorem apply_one_fst
    {G K : Type*} [Group G] [Group K]
    (c : CFSet G K) (g : G) :
    c (1, g) = 1 :=
  c.map_one_fst g

@[simp]
theorem apply_one_snd
    {G K : Type*} [Group G] [Group K]
    (c : CFSet G K) (g : G) :
    c (g, 1) = 1 :=
  c.map_one_snd g

/-- A central factor set is a normalized multiplicative two-cocycle whenever
the coefficient group carries the trivial action. -/
def normalizedMulCocycle
    {G K : Type*} [Group G] [CommGroup K]
    [MulDistribMulAction G K]
    (c : CFSet G K)
    (htrivialAction : ∀ g : G, ∀ k : K, g • k = k) :
    @NMCocycl₂ G K _ _ _ where
  toFun := c
  isMulCocycle₂ g h j := by
    rw [htrivialAction]
    calc
      c (g * h, j) * c (g, h) =
          c (g, h) * c (g * h, j) := mul_comm _ _
      _ = c (h, j) * c (g, h * j) := c.cocycle g h j
  map_one_fst := c.map_one_fst
  map_one_snd := c.map_one_snd

@[simp]
theorem normalized_mul_cocycle
    {G K : Type*} [Group G] [CommGroup K]
    [MulDistribMulAction G K]
    (c : CFSet G K)
    (htrivialAction : ∀ g : G, ∀ k : K, g • k = k)
    (p : G × G) :
    c.normalizedMulCocycle htrivialAction p = c p :=
  rfl

end CFSet

/-- A chosen right inverse of a surjective homomorphism, normalized to send
the identity to the identity. -/
noncomputable def normalizedSurjInv
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (g : G) : E :=
  by
    classical
    exact if g = 1 then 1 else Function.surjInv hq g

@[simp]
theorem normalized_surj_inv
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) :
    normalizedSurjInv q hq 1 = 1 := by
  simp [normalizedSurjInv]

@[simp]
theorem normalized_surj_maps
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (g : G) :
    q (normalizedSurjInv q hq g) = g := by
  classical
  by_cases hg : g = 1
  · simp [normalizedSurjInv, hg]
  · simp [normalizedSurjInv, hg, Function.surjInv_eq hq]

/-- The kernel element measuring the failure of the normalized section to be
a homomorphism. -/
noncomputable def centralExtensionValue
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (g h : G) : q.ker :=
  ⟨normalizedSurjInv q hq g * normalizedSurjInv q hq h *
      (normalizedSurjInv q hq (g * h))⁻¹,
    by
      change q (normalizedSurjInv q hq g * normalizedSurjInv q hq h *
        (normalizedSurjInv q hq (g * h))⁻¹) = 1
      rw [map_mul, map_mul, map_inv, normalized_surj_maps,
        normalized_surj_maps, normalized_surj_maps]
      group⟩

@[simp]
theorem central_value_coe
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (g h : G) :
    (centralExtensionValue q hq g h : E) =
      normalizedSurjInv q hq g * normalizedSurjInv q hq h *
        (normalizedSurjInv q hq (g * h))⁻¹ :=
  rfl

/-- The kernel coordinate of an element relative to the normalized section. -/
noncomputable def centralExtensionCoordinate
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (e : E) : q.ker :=
  ⟨e * (normalizedSurjInv q hq (q e))⁻¹, by
    change q (e * (normalizedSurjInv q hq (q e))⁻¹) = 1
    rw [map_mul, map_inv, normalized_surj_maps]
    exact mul_inv_cancel (q e)⟩

@[simp]
theorem central_extension_coe
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (e : E) :
    (centralExtensionCoordinate q hq e : E) =
      e * (normalizedSurjInv q hq (q e))⁻¹ :=
  rfl

/-- Kernel coordinate times the chosen section recovers the original
element. -/
theorem central_extension_section
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (e : E) :
    (centralExtensionCoordinate q hq e : E) *
        normalizedSurjInv q hq (q e) = e := by
  simp [centralExtensionCoordinate]

/-- In a central extension, kernel coordinates multiply with the normalized
factor set. -/
theorem central_extension_mul
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E) (e f : E) :
    centralExtensionCoordinate q hq (e * f) =
      centralExtensionCoordinate q hq e *
        centralExtensionCoordinate q hq f *
          centralExtensionValue q hq (q e) (q f) := by
  apply Subtype.ext
  have hcomm :
      (centralExtensionCoordinate q hq f : E) *
          normalizedSurjInv q hq (q e) =
        normalizedSurjInv q hq (q e) *
          (centralExtensionCoordinate q hq f : E) :=
    (Subgroup.mem_center_iff.mp
      (hcentral (centralExtensionCoordinate q hq f).property)
      (normalizedSurjInv q hq (q e))).symm
  change
    e * f * (normalizedSurjInv q hq (q (e * f)))⁻¹ =
      (centralExtensionCoordinate q hq e : E) *
        (centralExtensionCoordinate q hq f : E) *
          (centralExtensionValue q hq (q e) (q f) : E)
  rw [map_mul]
  calc
    e * f * (normalizedSurjInv q hq (q e * q f))⁻¹ =
        ((centralExtensionCoordinate q hq e : E) *
            normalizedSurjInv q hq (q e)) *
          ((centralExtensionCoordinate q hq f : E) *
            normalizedSurjInv q hq (q f)) *
              (normalizedSurjInv q hq (q e * q f))⁻¹ := by
                rw [central_extension_section,
                  central_extension_section]
    _ = (centralExtensionCoordinate q hq e : E) *
          (centralExtensionCoordinate q hq f : E) *
            (normalizedSurjInv q hq (q e) *
              normalizedSurjInv q hq (q f) *
                (normalizedSurjInv q hq (q e * q f))⁻¹) := by
          calc
            ((centralExtensionCoordinate q hq e : E) *
                normalizedSurjInv q hq (q e)) *
              ((centralExtensionCoordinate q hq f : E) *
                normalizedSurjInv q hq (q f)) *
                  (normalizedSurjInv q hq (q e * q f))⁻¹ =
                (centralExtensionCoordinate q hq e : E) *
                  (normalizedSurjInv q hq (q e) *
                    (centralExtensionCoordinate q hq f : E)) *
                      normalizedSurjInv q hq (q f) *
                        (normalizedSurjInv q hq (q e * q f))⁻¹ := by group
            _ = (centralExtensionCoordinate q hq e : E) *
                  ((centralExtensionCoordinate q hq f : E) *
                    normalizedSurjInv q hq (q e)) *
                      normalizedSurjInv q hq (q f) *
                        (normalizedSurjInv q hq (q e * q f))⁻¹ := by rw [hcomm]
            _ = (centralExtensionCoordinate q hq e : E) *
                  (centralExtensionCoordinate q hq f : E) *
                    (normalizedSurjInv q hq (q e) *
                      normalizedSurjInv q hq (q f) *
                        (normalizedSurjInv q hq (q e * q f))⁻¹) := by group
    _ = (centralExtensionCoordinate q hq e : E) *
          (centralExtensionCoordinate q hq f : E) *
            (centralExtensionValue q hq (q e) (q f) : E) := rfl

/-- The kernel of a central extension is itself commutative. -/
theorem central_center_top
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hcentral : q.ker ≤ Subgroup.center E) :
    Subgroup.center q.ker = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hcentral x.property) y

/-- The commutative-group structure on the kernel of a central extension. -/
@[implicit_reducible]
def centralExtensionComm
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hcentral : q.ker ≤ Subgroup.center E) :
    CommGroup q.ker :=
  Group.commGroupOfCenterEqTop
    (central_center_top q hcentral)

/-- The normalized central factor set attached to a surjection and a proof
that its kernel is central. -/
noncomputable def centralExtensionSet
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E) :
    CFSet G q.ker where
  toFun p := centralExtensionValue q hq p.1 p.2
  map_one_fst g := by
    apply Subtype.ext
    simp [centralExtensionValue]
  map_one_snd g := by
    apply Subtype.ext
    simp [centralExtensionValue]
  cocycle g h j := by
    apply Subtype.ext
    have hc (x : q.ker) (e : E) : (x : E) * e = e * (x : E) := by
      exact (Subgroup.mem_center_iff.mp (hcentral x.property) e).symm
    let s : G → E := normalizedSurjInv q hq
    let c : G → G → q.ker := fun a b =>
      centralExtensionValue q hq a b
    have hsection (a b : G) :
        s a * s b = (c a b : E) * s (a * b) := by
      change normalizedSurjInv q hq a * normalizedSurjInv q hq b =
        (normalizedSurjInv q hq a * normalizedSurjInv q hq b *
          (normalizedSurjInv q hq (a * b))⁻¹) *
            normalizedSurjInv q hq (a * b)
      group
    change (c g h : E) * (c (g * h) j : E) =
      (c h j : E) * (c g (h * j) : E)
    suffices
        ((c g h : E) * (c (g * h) j : E)) * s (g * h * j) =
          ((c h j : E) * (c g (h * j) : E)) * s (g * h * j) by
      exact mul_right_cancel this
    calc
      ((c g h : E) * (c (g * h) j : E)) *
          s (g * h * j) =
          (c g h : E) * ((c (g * h) j : E) * s (g * h * j)) := by
            rw [mul_assoc]
      _ = (c g h : E) * (s (g * h) * s j) := by
            rw [hsection (g * h) j]
      _ = (s g * s h) * s j := by
            rw [hsection g h]
            group
      _ = s g * (s h * s j) := mul_assoc _ _ _
      _ = s g * ((c h j : E) * s (h * j)) := by rw [hsection h j]
      _ = (c h j : E) * (s g * s (h * j)) := by
        calc
          s g * ((c h j : E) * s (h * j)) =
              (s g * (c h j : E)) * s (h * j) := by group
          _ = ((c h j : E) * s g) * s (h * j) := by
                rw [hc (c h j) (s g)]
          _ = (c h j : E) * (s g * s (h * j)) := by group
      _ = ((c h j : E) * (c g (h * j) : E)) *
          s (g * (h * j)) := by
            rw [hsection g (h * j)]
            group
      _ = ((c h j : E) * (c g (h * j) : E)) *
          s (g * h * j) := by
            rw [mul_assoc g h j]

/-- A cochain trivializes a central factor set when modifying the chosen
section by that cochain makes it multiplicative. -/
def CFSet.IsTrivial
    {G K : Type*} [Group G] [Group K]
    (c : CFSet G K) : Prop :=
  ∃ a : G → K, a 1 = 1 ∧
    ∀ g h, a (g * h) = a g * a h * c (g, h)

namespace CFSet

/-- Triviality of a central factor set is exactly vanishing of its class in
multiplicative `H²` with trivial coefficients. -/
theorem trivial_multiplicative_h
    {G K : Type*} [Group G] [CommGroup K]
    [MulDistribMulAction G K]
    (c : CFSet G K)
    (htrivialAction : ∀ g : G, ∀ k : K, g • k = k) :
    c.IsTrivial ↔
      MHTwo.mk
          (c.normalizedMulCocycle htrivialAction) = 1 := by
  rw [show (1 : MHTwo G K) = MHTwo.mk 1 from rfl]
  rw [MHTwo.mk_eq_iff]
  simp only [MHTwo.IsCohomologous,
    NMCocycl₂.one_apply, div_one,
    normalized_mul_cocycle]
  constructor
  · rintro ⟨a, _ha1, ha⟩
    refine ⟨fun g => (a g)⁻¹, ?_⟩
    intro g h
    rw [htrivialAction]
    change (a h)⁻¹ / (a (g * h))⁻¹ * (a g)⁻¹ = c (g, h)
    simp only [div_eq_mul_inv, inv_inv]
    rw [ha]
    calc
      (a h)⁻¹ * (a g * a h * c (g, h)) * (a g)⁻¹ =
          ((a h)⁻¹ * a h) * (a g * (a g)⁻¹) * c (g, h) := by
            ac_rfl
      _ = c (g, h) := by simp
  · rintro ⟨x, hx⟩
    refine ⟨fun g => (x g)⁻¹, ?_, ?_⟩
    · have hx11 : x 1 = 1 := by
        simpa [htrivialAction] using hx 1 1
      exact inv_eq_one.mpr hx11
    · intro g h
      have hxc := hx g h
      simp only [htrivialAction] at hxc
      change (x (g * h))⁻¹ =
        (x g)⁻¹ * (x h)⁻¹ * c (g, h)
      calc
        (x (g * h))⁻¹ =
            (x g)⁻¹ * (x h)⁻¹ *
              (x h / x (g * h) * x g) := by
                simp only [div_eq_mul_inv]
                calc
                  (x (g * h))⁻¹ =
                      ((x g)⁻¹ * x g) * ((x h)⁻¹ * x h) *
                        (x (g * h))⁻¹ := by simp
                  _ = (x g)⁻¹ * (x h)⁻¹ *
                      (x h * (x (g * h))⁻¹ * x g) := by ac_rfl
        _ = (x g)⁻¹ * (x h)⁻¹ * c (g, h) := by rw [hxc]

end CFSet

/-- The multiplicative `H²` obstruction class of a central extension. -/
noncomputable def extensionObstructionClass
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo G q.ker := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  exact MHTwo.mk
    ((centralExtensionSet q hq hcentral).normalizedMulCocycle
      (fun _ _ ↦ rfl))

/-- The factor set of a central extension is trivial exactly when its
multiplicative `H²` obstruction class vanishes. -/
theorem set_trivial_obstruction
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E) :
    (centralExtensionSet q hq hcentral).IsTrivial ↔
      letI : CommGroup q.ker :=
        centralExtensionComm q hcentral
      letI : MulDistribMulAction G q.ker :=
        trivialDistribAction G q.ker
      extensionObstructionClass q hq hcentral = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  exact CFSet.trivial_multiplicative_h
    (centralExtensionSet q hq hcentral) (fun _ _ ↦ rfl)

/-- Vanishing of ordinary degree-two group cohomology with coefficients in
the central kernel kills the central-extension factor set. -/
theorem central_set_trivial
    {E G : Type} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (hzero :
      letI : CommGroup q.ker :=
        centralExtensionComm q hcentral
      letI : MulDistribMulAction G q.ker :=
        trivialDistribAction G q.ker
      ∀ x : groupCohomology.H2
          (Rep.ofMulDistribMulAction G q.ker), x = 0) :
    (centralExtensionSet q hq hcentral).IsTrivial := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  apply
    (set_trivial_obstruction
      q hq hcentral).2
  apply (MHTwo.group_cohomology_zero _).1
  exact hzero _

/-- A trivialization of the factor set produces a homomorphic splitting of
the original central extension. -/
noncomputable def splittingSetTrivial
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (htrivial : (centralExtensionSet q hq hcentral).IsTrivial) :
    G →* E := by
  classical
  choose a ha1 ha using htrivial
  let s : G → E := normalizedSurjInv q hq
  exact
    { toFun := fun g => (a g : E) * s g
      map_one' := by simp [ha1, s]
      map_mul' := by
        intro g h
        have hc (x : q.ker) (e : E) : (x : E) * e = e * (x : E) := by
          exact (Subgroup.mem_center_iff.mp (hcentral x.property) e).symm
        have hsection :
            s g * s h =
              ((centralExtensionSet q hq hcentral) (g, h) : E) *
                s (g * h) := by
          change normalizedSurjInv q hq g * normalizedSurjInv q hq h =
            (normalizedSurjInv q hq g * normalizedSurjInv q hq h *
              (normalizedSurjInv q hq (g * h))⁻¹) *
                normalizedSurjInv q hq (g * h)
          group
        rw [ha]
        simp only [Subgroup.coe_mul]
        calc
          (a g : E) * (a h : E) *
                ((centralExtensionSet q hq hcentral) (g, h) : E) *
              s (g * h) =
              (a g : E) * (a h : E) * (s g * s h) := by
                rw [hsection]
                group
          _ = (a g : E) * ((a h : E) * s g) * s h := by group
          _ = (a g : E) * (s g * (a h : E)) * s h := by
                rw [hc (a h) (s g)]
          _ = ((a g : E) * s g) * ((a h : E) * s h) := by group }

@[simp]
theorem splitting_trivial_maps
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (htrivial : (centralExtensionSet q hq hcentral).IsTrivial) :
    q.comp (splittingSetTrivial
      q hq hcentral htrivial) = MonoidHom.id G := by
  ext g
  change q ((Classical.choose htrivial g : E) *
    normalizedSurjInv q hq g) = g
  rw [map_mul, show q (Classical.choose htrivial g : E) = 1 by
    exact (Classical.choose htrivial g).property,
    normalized_surj_maps, one_mul]

/-- A homomorphic splitting trivializes the factor set attached to the
normalized chosen section. -/
theorem set_trivial_splitting
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (t : G →* E) (ht : q.comp t = MonoidHom.id G) :
    (centralExtensionSet q hq hcentral).IsTrivial := by
  let s : G → E := normalizedSurjInv q hq
  let a : G → q.ker := fun g =>
    ⟨t g * (s g)⁻¹, by
      change q (t g * (s g)⁻¹) = 1
      have htg := DFunLike.congr_fun ht g
      change q (t g) = g at htg
      rw [map_mul, map_inv, htg]
      change g * (q (normalizedSurjInv q hq g))⁻¹ = 1
      rw [normalized_surj_maps]
      exact mul_inv_cancel g⟩
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    simp [a, s]
  · intro g h
    apply Subtype.ext
    have hc (x : q.ker) (e : E) : (x : E) * e = e * (x : E) := by
      exact (Subgroup.mem_center_iff.mp (hcentral x.property) e).symm
    have hsection :
        s g * s h =
          ((centralExtensionSet q hq hcentral) (g, h) : E) *
            s (g * h) := by
      change normalizedSurjInv q hq g * normalizedSurjInv q hq h =
        (normalizedSurjInv q hq g * normalizedSurjInv q hq h *
          (normalizedSurjInv q hq (g * h))⁻¹) *
            normalizedSurjInv q hq (g * h)
      group
    change t (g * h) * (s (g * h))⁻¹ =
      (a g : E) * (a h : E) *
        ((centralExtensionSet q hq hcentral) (g, h) : E)
    rw [map_mul]
    change t g * t h * (s (g * h))⁻¹ =
      (t g * (s g)⁻¹) * (t h * (s h)⁻¹) *
        ((centralExtensionSet q hq hcentral) (g, h) : E)
    have hah_comm : (a h : E) * s g = s g * (a h : E) := hc (a h) (s g)
    calc
      t g * t h * (s (g * h))⁻¹ =
          ((a g : E) * s g) * ((a h : E) * s h) *
            (s (g * h))⁻¹ := by
              dsimp [a]
              group
      _ = (a g : E) * (s g * (a h : E)) * s h *
          (s (g * h))⁻¹ := by group
      _ = (a g : E) * ((a h : E) * s g) * s h *
          (s (g * h))⁻¹ := by rw [hah_comm]
      _ = (a g : E) * (a h : E) * (s g * s h) *
          (s (g * h))⁻¹ := by group
      _ = (a g : E) * (a h : E) *
          (((centralExtensionSet q hq hcentral) (g, h) : E) *
            s (g * h)) * (s (g * h))⁻¹ := by rw [hsection]
      _ = (a g : E) * (a h : E) *
          ((centralExtensionSet q hq hcentral) (g, h) : E) := by group

/-- Splitting a central surjection is equivalent to triviality of its explicit
normalized factor set. -/
theorem splits_set_trivial
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E) :
    (∃ t : G →* E, q.comp t = MonoidHom.id G) ↔
      (centralExtensionSet q hq hcentral).IsTrivial := by
  constructor
  · rintro ⟨t, ht⟩
    exact set_trivial_splitting q hq hcentral t ht
  · intro htrivial
    exact ⟨splittingSetTrivial q hq hcentral htrivial,
      splitting_trivial_maps
        q hq hcentral htrivial⟩

/-- A lift after restriction along `f` kills the restricted central-extension
obstruction. -/
theorem obstruction_restrict_lift
    {E G H : Type*} [Group E] [Group G] [Group H]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (f : H →* G) (t : H →* E) (ht : q.comp t = f) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction H q.ker :=
      trivialDistribAction H q.ker
    MHTwo.restrictionHom f (fun _ _ => rfl)
        (extensionObstructionClass q hq hcentral) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker :=
    trivialDistribAction H q.ker
  let cG := centralExtensionSet q hq hcentral
  let cH : CFSet H q.ker :=
    { toFun := fun p => cG (f p.1, f p.2)
      map_one_fst := by intro h; simp [cG]
      map_one_snd := by intro h; simp [cG]
      cocycle := by
        intro g h j
        simpa only [map_mul] using cG.cocycle (f g) (f h) (f j) }
  let s : H → E := fun h => normalizedSurjInv q hq (f h)
  let a : H → q.ker := fun h =>
    ⟨t h * (s h)⁻¹, by
      change q (t h * (s h)⁻¹) = 1
      have hth := DFunLike.congr_fun ht h
      change q (t h) = f h at hth
      rw [map_mul, map_inv, hth]
      change f h * (q (normalizedSurjInv q hq (f h)))⁻¹ = 1
      rw [normalized_surj_maps]
      exact mul_inv_cancel (f h)⟩
  have hcH : cH.IsTrivial := by
    refine ⟨a, ?_, ?_⟩
    · apply Subtype.ext
      simp [a, s]
    · intro g h
      apply Subtype.ext
      have hc (x : q.ker) (e : E) : (x : E) * e = e * (x : E) := by
        exact (Subgroup.mem_center_iff.mp (hcentral x.property) e).symm
      have hsection :
          s g * s h = (cH (g, h) : E) * s (g * h) := by
        change normalizedSurjInv q hq (f g) * normalizedSurjInv q hq (f h) =
          (centralExtensionValue q hq (f g) (f h) : E) *
            normalizedSurjInv q hq (f (g * h))
        rw [map_mul]
        simp only [central_value_coe]
        group
      change t (g * h) * (s (g * h))⁻¹ =
        (a g : E) * (a h : E) * (cH (g, h) : E)
      rw [map_mul]
      change t g * t h * (s (g * h))⁻¹ =
        (t g * (s g)⁻¹) * (t h * (s h)⁻¹) * (cH (g, h) : E)
      have hah_comm : (a h : E) * s g = s g * (a h : E) :=
        hc (a h) (s g)
      calc
        t g * t h * (s (g * h))⁻¹ =
            ((a g : E) * s g) * ((a h : E) * s h) *
              (s (g * h))⁻¹ := by dsimp [a]; group
        _ = (a g : E) * (s g * (a h : E)) * s h *
            (s (g * h))⁻¹ := by group
        _ = (a g : E) * ((a h : E) * s g) * s h *
            (s (g * h))⁻¹ := by rw [hah_comm]
        _ = (a g : E) * (a h : E) * (s g * s h) *
            (s (g * h))⁻¹ := by group
        _ = (a g : E) * (a h : E) *
            ((cH (g, h) : E) * s (g * h)) *
              (s (g * h))⁻¹ := by rw [hsection]
        _ = (a g : E) * (a h : E) * (cH (g, h) : E) := by group
  change MHTwo.mk
      (NMCocycl₂.restrict f (fun _ _ => rfl)
        (cG.normalizedMulCocycle (fun _ _ => rfl))) = 1
  have hzero :=
    (CFSet.trivial_multiplicative_h cH
      (fun _ _ => rfl)).1 hcH
  exact hzero

/-- Vanishing of the restricted obstruction constructs a lift along the
homomorphism used for restriction.  This is the converse of
`obstruction_restrict_lift`. -/
theorem lift_obstruction_restrict
    {E G H : Type*} [Group E] [Group G] [Group H]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (f : H →* G)
    (hzero :
      letI : CommGroup q.ker :=
        centralExtensionComm q hcentral
      letI : MulDistribMulAction G q.ker :=
        trivialDistribAction G q.ker
      letI : MulDistribMulAction H q.ker :=
        trivialDistribAction H q.ker
      MHTwo.restrictionHom f (fun _ _ => rfl)
          (extensionObstructionClass q hq hcentral) = 1) :
    ∃ t : H →* E, q.comp t = f := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker :=
    trivialDistribAction H q.ker
  let cG := centralExtensionSet q hq hcentral
  let cH : CFSet H q.ker :=
    { toFun := fun p => cG (f p.1, f p.2)
      map_one_fst := by intro h; simp [cG]
      map_one_snd := by intro h; simp [cG]
      cocycle := by
        intro g h j
        simpa only [map_mul] using cG.cocycle (f g) (f h) (f j) }
  have hcH : cH.IsTrivial := by
    apply (CFSet.trivial_multiplicative_h cH
      (fun _ _ => rfl)).2
    change MHTwo.mk
      (NMCocycl₂.restrict f (fun _ _ => rfl)
        (cG.normalizedMulCocycle (fun _ _ => rfl))) = 1 at hzero
    exact hzero
  choose a ha1 ha using hcH
  let s : H → E := fun h => normalizedSurjInv q hq (f h)
  let t : H →* E :=
    { toFun := fun h => (a h : E) * s h
      map_one' := by simp [ha1, s]
      map_mul' := by
        intro g h
        have hc (x : q.ker) (e : E) : (x : E) * e = e * (x : E) := by
          exact (Subgroup.mem_center_iff.mp (hcentral x.property) e).symm
        have hsection :
            s g * s h = (cH (g, h) : E) * s (g * h) := by
          change normalizedSurjInv q hq (f g) * normalizedSurjInv q hq (f h) =
            (centralExtensionValue q hq (f g) (f h) : E) *
              normalizedSurjInv q hq (f (g * h))
          rw [map_mul]
          simp only [central_value_coe]
          group
        rw [ha]
        simp only [Subgroup.coe_mul]
        calc
          (a g : E) * (a h : E) * (cH (g, h) : E) * s (g * h) =
              (a g : E) * (a h : E) * (s g * s h) := by
                rw [hsection]
                group
          _ = (a g : E) * ((a h : E) * s g) * s h := by group
          _ = (a g : E) * (s g * (a h : E)) * s h := by
                rw [hc (a h) (s g)]
          _ = ((a g : E) * s g) * ((a h : E) * s h) := by group }
  refine ⟨t, ?_⟩
  ext h
  change q ((a h : E) * normalizedSurjInv q hq (f h)) = f h
  rw [map_mul, show q (a h : E) = 1 by exact (a h).property,
    normalized_surj_maps, one_mul]

/-- The subgroup upstairs lying over a subgroup of the quotient. -/
def centralExtensionPreimage
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (H : Subgroup G) : Subgroup E :=
  H.comap q

/-- Restriction of a surjection to the full preimage of a subgroup. -/
def centralPreimageProjection
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (H : Subgroup G) :
    centralExtensionPreimage q H →* H where
  toFun e := ⟨q e.1, e.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- Compatible maps to the total and quotient groups assemble into a map to
the full preimage of the quotient map's range. -/
def compatiblePreimageLift
    {Γ E G : Type*} [Group Γ] [Group E] [Group G]
    (q : E →* G) (alpha : Γ →* E) (beta : Γ →* G)
    (hcompat : q.comp alpha = beta) :
    Γ →* centralExtensionPreimage q beta.range where
  toFun gamma :=
    ⟨alpha gamma, by
      change q (alpha gamma) ∈ beta.range
      have hgamma := DFunLike.congr_fun hcompat gamma
      change q (alpha gamma) = beta gamma at hgamma
      rw [hgamma]
      exact ⟨gamma, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem compatible_preimage_coe
    {Γ E G : Type*} [Group Γ] [Group E] [Group G]
    (q : E →* G) (alpha : Γ →* E) (beta : Γ →* G)
    (hcompat : q.comp alpha = beta) (gamma : Γ) :
    (compatiblePreimageLift q alpha beta hcompat gamma : E) =
      alpha gamma :=
  rfl

@[simp]
theorem compatible_preimage_projection
    {Γ E G : Type*} [Group Γ] [Group E] [Group G]
    (q : E →* G) (alpha : Γ →* E) (beta : Γ →* G)
    (hcompat : q.comp alpha = beta) (gamma : Γ) :
    centralPreimageProjection q beta.range
        (compatiblePreimageLift q alpha beta hcompat gamma) =
      beta.rangeRestrict gamma := by
  apply Subtype.ext
  exact DFunLike.congr_fun hcompat gamma

theorem compatible_preimage_comp
    {Γ E G : Type*} [Group Γ] [Group E] [Group G]
    (q : E →* G) (alpha : Γ →* E) (beta : Γ →* G)
    (hcompat : q.comp alpha = beta) :
    (centralPreimageProjection q beta.range).comp
        (compatiblePreimageLift q alpha beta hcompat) =
      beta.rangeRestrict := by
  ext gamma
  exact congrArg Subtype.val
    (compatible_preimage_projection
      q alpha beta hcompat gamma)

theorem preimage_projection_surjective
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q) (H : Subgroup G) :
    Function.Surjective (centralPreimageProjection q H) := by
  rintro ⟨g, hg⟩
  obtain ⟨e, rfl⟩ := hq g
  exact ⟨⟨e, hg⟩, rfl⟩

/-- Restricting an extension to the full preimage of a subgroup leaves its
kernel unchanged. -/
def extensionPreimageProjection
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (H : Subgroup G) :
    q.ker ≃* (centralPreimageProjection q H).ker where
  toFun z :=
    ⟨⟨(z : E), by
        change q (z : E) ∈ H
        rw [z.property]
        exact H.one_mem⟩,
      by
        apply Subtype.ext
        exact z.property⟩
  invFun z :=
    ⟨(z.1.1 : E), by
      exact congrArg Subtype.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem extension_preimage_projection
    {E G : Type*} [Group E] [Group G]
    (q : E →* G) (H : Subgroup G)
    (hcentral : q.ker ≤ Subgroup.center E) :
    (centralPreimageProjection q H).ker ≤
      Subgroup.center (centralExtensionPreimage q H) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  change y.1 * x.1 = x.1 * y.1
  have hxq : x.1 ∈ q.ker := by
    change q x.1 = 1
    exact congrArg Subtype.val hx
  exact Subgroup.mem_center_iff.mp (hcentral hxq) y.1

end TBluepr
end Submission
