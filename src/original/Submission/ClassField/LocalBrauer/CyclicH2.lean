import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic
import Submission.ClassField.UnramifiedCohom.ValAddCarry
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.LocalBrauer.CyclicCarryCocycle


/-!
# Chapter IV, Section 4: second cohomology of a cyclic group

For a cyclic group `C = Z/nZ` acting on a commutative group `M`, this file
identifies normalized multiplicative `H²(C,M)` with the invariant elements of
`M` modulo norms.  The inverse sends an invariant element to Milne's carry
cocycle from Example IV.4.2.
-/

namespace Submission.CField.LBrauer

noncomputable section

open scoped BigOperators
open CProduca
open groupCohomology

namespace CyclicH2

variable {n : ℕ} [NeZero n]

abbrev C := Multiplicative (ZMod n)

variable {M : Type*} [CommGroup M] [MulDistribMulAction (C (n := n)) M]

/-- The subgroup of elements fixed by the cyclic action. -/
def invariants : Subgroup M where
  carrier := {x | ∀ g : C (n := n), g • x = x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy g
    simp only [smul_mul', hx g, hy g]
  inv_mem' := by
    intro x hx g
    simp only [smul_inv', hx g]

omit [NeZero n] in
@[simp]
theorem mem_invariants_iff (x : M) :
    x ∈ invariants (n := n) (M := M) ↔ ∀ g : C (n := n), g • x = x :=
  Iff.rfl

/-- The multiplicative norm of an element under the cyclic action. -/
def norm : M →* invariants (n := n) (M := M) where
  toFun x := ⟨∏ g : C (n := n), g • x, by
    intro h
    change (MulDistribMulAction.toMonoidHom M h)
        (∏ g : C (n := n), g • x) = _
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft h)
      (fun g : C (n := n) ↦ h • g • x) (fun g : C (n := n) ↦ g • x)
      (fun g ↦ (mul_smul h g x).symm) ⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (∏ g : C (n := n), g • (x * y)) =
      (∏ g : C (n := n), g • x) * (∏ g : C (n := n), g • y)
    simp only [smul_mul', Finset.prod_mul_distrib]

@[simp]
theorem norm_coe (x : M) :
    ((norm (n := n) (M := M) x : invariants (n := n) (M := M)) : M) =
      ∏ g : C (n := n), g • x :=
  rfl

/-- The quotient of invariant elements by the image of the norm. -/
abbrev invariantsModNorm :=
  invariants (n := n) (M := M) ⧸ (norm (n := n) (M := M)).range

/-- The standard generator of `Multiplicative (ZMod n)`. -/
def generator : C (n := n) :=
  Multiplicative.ofAdd (1 : ZMod n)

theorem generator_pow_val (g : C (n := n)) :
    g = generator (n := n) ^ g.toAdd.val := by
  apply Multiplicative.ext
  simp [generator]

/-- The cyclic parameter of a normalized cocycle, obtained by multiplying its
values on `(g, sigma)` over the cyclic group. -/
def parameter
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) : M :=
  ∏ g : C (n := n), c (g, generator (n := n))

theorem parameter_mul
    (c d : NMCocycl₂ (G := C (n := n)) (M := M)) :
    parameter (c * d) = parameter c * parameter d := by
  simp [parameter, Finset.prod_mul_distrib]

@[simp]
theorem parameter_one :
    parameter (1 : NMCocycl₂ (G := C (n := n)) (M := M)) = 1 := by
  simp [parameter]

theorem parameter_inv
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) :
    parameter c⁻¹ = (parameter c)⁻¹ := by
  simp [parameter]

theorem generator_smul_parameter
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) :
    generator (n := n) • parameter c = parameter c := by
  let s : C (n := n) := generator (n := n)
  change (MulDistribMulAction.toMonoidHom M s) (parameter c) = parameter c
  rw [parameter, map_prod]
  calc
    ∏ g : C (n := n), s • c (g, s) =
        ∏ g : C (n := n),
          (c (s * g, s) * c (s, g)) / c (s, g * s) := by
            apply Finset.prod_congr rfl
            intro g _
            rw [c.isMulCocycle₂ s g s]
            simp
    _ = (∏ g : C (n := n), c (s * g, s)) *
          (∏ g : C (n := n), c (s, g)) *
          (∏ g : C (n := n), c (s, g * s))⁻¹ := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
              Finset.prod_inv_distrib]
    _ = ∏ g : C (n := n), c (g, s) := by
          have hleft : (∏ g : C (n := n), c (s * g, s)) =
              ∏ g : C (n := n), c (g, s) :=
            Fintype.prod_equiv (Equiv.mulLeft s) _ _ (fun _ ↦ rfl)
          have hright : (∏ g : C (n := n), c (s, g * s)) =
              ∏ g : C (n := n), c (s, g) :=
            Fintype.prod_equiv (Equiv.mulRight s) _ _ (fun _ ↦ rfl)
          rw [hleft, hright]
          simp

/-- The cyclic parameter of a cocycle is fixed by the whole cyclic group. -/
theorem parameter_mem_invariants
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) :
    parameter c ∈ invariants (n := n) (M := M) := by
  intro g
  rw [generator_pow_val g]
  induction g.toAdd.val with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_smul, generator_smul_parameter, ih]

/-- Cohomologous cocycles have cyclic parameters differing by a norm. -/
theorem parameter_div_cohomologous
    {c d : NMCocycl₂ (G := C (n := n)) (M := M)}
    (h : MHTwo.IsCohomologous c d) :
    ∃ z : M, parameter c / parameter d =
      (norm (n := n) (M := M) z : M) := by
  obtain ⟨x, hx⟩ := h
  let s : C (n := n) := generator (n := n)
  refine ⟨x s, ?_⟩
  rw [parameter, parameter, ← Finset.prod_div_distrib]
  calc
    ∏ g : C (n := n), c (g, s) / d (g, s) =
        ∏ g : C (n := n), (g • x s / x (g * s)) * x g := by
          apply Finset.prod_congr rfl
          intro g _
          exact (hx g s).symm
    _ = (∏ g : C (n := n), g • x s) *
          (∏ g : C (n := n), x (g * s))⁻¹ *
          (∏ g : C (n := n), x g) := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
              Finset.prod_inv_distrib]
    _ = ∏ g : C (n := n), g • x s := by
          have hright : (∏ g : C (n := n), x (g * s)) =
              ∏ g : C (n := n), x g :=
            Fintype.prod_equiv (Equiv.mulRight s) _ _ (fun _ ↦ rfl)
          rw [hright]
          simp

private def finEquivC : Fin n ≃ C (n := n) where
  toFun i := Multiplicative.ofAdd (i : ZMod n)
  invFun g := ⟨g.toAdd.val, g.toAdd.val_lt⟩
  left_inv i := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv g := by
    simp

/-- Milne's carry cocycle has cyclic parameter equal to the element used to
define it. -/
theorem parameter_factorSet (hn : 1 < n)
    (pi : M) (hpi : ∀ g : C (n := n), g • pi = pi) :
    parameter (CCarry.factorSet pi hpi) = pi := by
  rw [parameter]
  calc
    ∏ g : C (n := n), CCarry.factorSet pi hpi (g, generator (n := n)) =
        ∏ i : Fin n, CCarry.factorSet pi hpi
          (finEquivC i, generator (n := n)) :=
      (Fintype.prod_equiv (finEquivC (n := n)) _ _ (fun _ ↦ rfl)).symm
    _ = ∏ i : Fin n, CCarry.factorSet pi hpi
          (generator (n := n) ^ (i : ℕ), generator (n := n)) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
      apply Multiplicative.ext
      change ((i : ℕ) : ZMod n) = (i : ℕ) • (1 : ZMod n)
      simp
    _ = ∏ i ∈ Finset.range n, CCarry.factorSet pi hpi
          (generator (n := n) ^ i, generator (n := n)) :=
      Fin.prod_univ_eq_prod_range
        (fun i : ℕ ↦ CCarry.factorSet pi hpi
          (generator (n := n) ^ i, generator (n := n))) n
    _ = pi := by
      simpa [generator, CCarry.factorSet, CCarry.carry,
        UCohom.FCarry.factorSet,
        UCohom.FCarry.carry, add_comm] using
        (UCohom.FCarry.prod_set_generator
          (n := n) pi hn)

private theorem parameter_prod_range
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) :
    parameter c = ∏ i ∈ Finset.range n,
      c (generator (n := n) ^ i, generator (n := n)) := by
  rw [parameter]
  calc
    ∏ g : C (n := n), c (g, generator (n := n)) =
        ∏ i : Fin n, c (finEquivC i, generator (n := n)) :=
      (Fintype.prod_equiv (finEquivC (n := n)) _ _ (fun _ ↦ rfl)).symm
    _ = ∏ i : Fin n,
        c (generator (n := n) ^ (i : ℕ), generator (n := n)) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
      apply Multiplicative.ext
      change ((i : ℕ) : ZMod n) = (i : ℕ) • (1 : ZMod n)
      simp
    _ = ∏ i ∈ Finset.range n,
        c (generator (n := n) ^ i, generator (n := n)) :=
      Fin.prod_univ_eq_prod_range
        (fun i : ℕ ↦ c
          (generator (n := n) ^ i, generator (n := n))) n

private theorem norm_prod_range (z : M) :
    (norm (n := n) (M := M) z : M) = ∏ i ∈ Finset.range n,
      generator (n := n) ^ i • z := by
  rw [norm_coe]
  calc
    ∏ g : C (n := n), g • z = ∏ i : Fin n, finEquivC i • z :=
      (Fintype.prod_equiv (finEquivC (n := n)) _ _ (fun _ ↦ rfl)).symm
    _ = ∏ i : Fin n, generator (n := n) ^ (i : ℕ) • z := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      apply Multiplicative.ext
      change ((i : ℕ) : ZMod n) = (i : ℕ) • (1 : ZMod n)
      simp
    _ = ∏ i ∈ Finset.range n, generator (n := n) ^ i • z :=
      Fin.prod_univ_eq_prod_range
        (fun i : ℕ ↦ generator (n := n) ^ i • z) n

/-- The cochain obtained by successively trivializing a cocycle along the
chosen cyclic generator. -/
private def normalizingCochain
    (c : NMCocycl₂ (G := C (n := n)) (M := M))
    (z : M) (g : C (n := n)) : M :=
  ∏ i ∈ Finset.range g.toAdd.val,
    (c (generator (n := n) ^ i, generator (n := n)))⁻¹ *
      (generator (n := n) ^ i • z)

omit [NeZero n] in
@[simp]
private theorem normalizingCochain_one
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) (z : M) :
    normalizingCochain c z (1 : C (n := n)) = 1 := by
  simp [normalizingCochain]

omit [NeZero n] in
private theorem normalizingCochain_generator (hn : 1 < n)
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) (z : M) :
    normalizingCochain c z (generator (n := n)) = z := by
  letI : Fact (1 < n) := ⟨hn⟩
  rw [normalizingCochain]
  change (∏ i ∈ Finset.range (1 : ZMod n).val,
    (c (generator (n := n) ^ i, generator (n := n)))⁻¹ *
      (generator (n := n) ^ i • z)) = z
  rw [ZMod.val_one]
  simp

omit [NeZero n] in
private theorem generator_pow_n (_hn : 1 < n) :
    generator (n := n) ^ n = (1 : C (n := n)) := by
  apply Multiplicative.ext
  simp [generator]

private theorem normal_cocha_gener (hn : 1 < n)
    (c : NMCocycl₂ (G := C (n := n)) (M := M))
    (z : M) (hparameter : parameter c = (norm (n := n) (M := M) z : M))
    (g : C (n := n)) :
    normalizingCochain c z (g * generator (n := n)) =
      (c (g, generator (n := n)))⁻¹ * (g • z) *
        normalizingCochain c z g := by
  let s : C (n := n) := generator (n := n)
  letI : Fact (1 < n) := ⟨hn⟩
  by_cases hnowrap : g.toAdd.val + 1 < n
  · have hval : (g * s).toAdd.val = g.toAdd.val + 1 := by
      change (g.toAdd + 1).val = g.toAdd.val + 1
      calc
        (g.toAdd + 1).val = g.toAdd.val + (1 : ZMod n).val :=
          ZMod.val_add_of_lt (by simpa only [ZMod.val_one] using hnowrap)
        _ = g.toAdd.val + 1 := by rw [ZMod.val_one]
    rw [normalizingCochain, normalizingCochain, hval,
      Finset.prod_range_succ]
    rw [← generator_pow_val g]
    ac_rfl
  · have hnpos : 0 < n := by omega
    have hval : g.toAdd.val = n - 1 := by
      have hglt := g.toAdd.val_lt
      omega
    have hg : g = s ^ (n - 1) := by
      rw [generator_pow_val g, hval]
    have hgs : g * s = 1 := by
      rw [hg, ← pow_succ, Nat.sub_add_cancel hnpos, generator_pow_n hn]
    rw [hgs, normalizingCochain_one]
    have hp :
        (∏ i ∈ Finset.range n, c (s ^ i, s)) =
          ∏ i ∈ Finset.range n, s ^ i • z := by
      rw [← parameter_prod_range, ← norm_prod_range]
      exact hparameter
    have hp' :
        (∏ i ∈ Finset.range ((n - 1) + 1), c (s ^ i, s)) =
          ∏ i ∈ Finset.range ((n - 1) + 1), s ^ i • z := by
      simpa only [Nat.sub_add_cancel hnpos] using hp
    rw [Finset.prod_range_succ, Finset.prod_range_succ] at hp'
    change 1 = (c (g, s))⁻¹ * (g • z) * normalizingCochain c z g
    rw [normalizingCochain, hval, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, hg]
    symm
    calc
      (c (s ^ (n - 1), s))⁻¹ * (s ^ (n - 1) • z) *
          ((∏ x ∈ Finset.range (n - 1), c (s ^ x, s))⁻¹ *
            ∏ x ∈ Finset.range (n - 1), s ^ x • z) =
          ((∏ x ∈ Finset.range (n - 1), c (s ^ x, s)) *
          c (s ^ (n - 1), s))⁻¹ *
          ((∏ x ∈ Finset.range (n - 1), s ^ x • z) *
            (s ^ (n - 1) • z)) := by
              rw [mul_inv_rev]
              ac_rfl
      _ = 1 := by rw [hp']; simp

/-- The normalized cocycle attached to a cochain which is one at the group
identity. -/
private def coboundaryCocycle (x : C (n := n) → M) (hx : x 1 = 1) :
    NMCocycl₂ (G := C (n := n)) (M := M) where
  toFun p := p.1 • x p.2 / x (p.1 * p.2) * x p.1
  isMulCocycle₂ := by
    intro g h j
    simp only [div_eq_mul_inv, smul_mul', smul_inv', mul_smul, mul_assoc]
    simp [mul_assoc, mul_left_comm, mul_comm]
  map_one_fst g := by simp [hx]
  map_one_snd g := by simp [hx]

private theorem cocycle_ext_generator
    {c d : NMCocycl₂ (G := C (n := n)) (M := M)}
    (h : ∀ g : C (n := n),
      c (g, generator (n := n)) = d (g, generator (n := n))) :
    c = d := by
  apply NMCocycl₂.ext
  rintro ⟨g, j⟩
  rw [generator_pow_val j]
  induction j.toAdd.val with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      let s : C (n := n) := generator (n := n)
      let t : C (n := n) := s ^ k
      have hc := c.isMulCocycle₂ g t s
      have hd := d.isMulCocycle₂ g t s
      apply mul_left_cancel (a := g • c (t, s))
      calc
        g • c (t, s) * c (g, t * s) = c (g * t, s) * c (g, t) := hc.symm
        _ = d (g * t, s) * d (g, t) := by rw [h, ih]
        _ = g • d (t, s) * d (g, t * s) := hd
        _ = g • c (t, s) * d (g, t * s) := by rw [h]

/-- A normalized cyclic cocycle whose parameter is a norm is a
multiplicative coboundary. -/
theorem isMulCoboundary₂_of_parameter_eq_norm (hn : 1 < n)
    (c : NMCocycl₂ (G := C (n := n)) (M := M))
    (z : M) (hparameter : parameter c = (norm (n := n) (M := M) z : M)) :
    IsMulCoboundary₂ c := by
  let x : C (n := n) → M := normalizingCochain c z
  have hxone : x 1 = 1 := normalizingCochain_one c z
  have hxgenerator : x (generator (n := n)) = z :=
    normalizingCochain_generator hn c z
  have hrec := normal_cocha_gener hn c z hparameter
  have heq : coboundaryCocycle x hxone = c := by
    apply cocycle_ext_generator
    intro g
    change g • x (generator (n := n)) /
        x (g * generator (n := n)) * x g =
      c (g, generator (n := n))
    rw [hxgenerator]
    change g • z /
        normalizingCochain c z (g * generator (n := n)) *
          normalizingCochain c z g = _
    rw [hrec g]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    simp [mul_left_comm, mul_comm]
  refine ⟨x, ?_⟩
  intro g h
  exact congrArg (fun q ↦ q (g, h)) heq

/-- The cyclic normalization can be carried out inside any coefficient
subgroup stable under the action.  This retains unit-valued information that
is lost by merely recording that the ambient cohomology class vanishes. -/
theorem mul_coboundary₂_cochain_mem_subgroup
    (hn : 1 < n) (U : Subgroup M)
    (hstable : ∀ g : C (n := n), ∀ u : M, u ∈ U → g • u ∈ U)
    (c : NMCocycl₂ (G := C (n := n)) (M := M))
    (hc : ∀ g h, c (g, h) ∈ U)
    (z : M) (hz : z ∈ U)
    (hparameter : parameter c = (norm (n := n) (M := M) z : M)) :
    ∃ x : C (n := n) → M,
      (∀ g, x g ∈ U) ∧
        ∀ g h, g • x h / x (g * h) * x g = c (g, h) := by
  let x : C (n := n) → M := normalizingCochain c z
  have hxU : ∀ g, x g ∈ U := by
    intro g
    apply Subgroup.prod_mem
    intro i hi
    exact U.mul_mem (U.inv_mem (hc _ _)) (hstable _ z hz)
  have hxone : x 1 = 1 := normalizingCochain_one c z
  have hxgenerator : x (generator (n := n)) = z :=
    normalizingCochain_generator hn c z
  have hrec := normal_cocha_gener hn c z hparameter
  have heq : coboundaryCocycle x hxone = c := by
    apply cocycle_ext_generator
    intro g
    change g • x (generator (n := n)) /
        x (g * generator (n := n)) * x g =
      c (g, generator (n := n))
    rw [hxgenerator]
    change g • z /
        normalizingCochain c z (g * generator (n := n)) *
          normalizingCochain c z g = _
    rw [hrec g]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    simp [mul_left_comm, mul_comm]
  refine ⟨x, hxU, ?_⟩
  intro g h
  exact congrArg (fun q ↦ q (g, h)) heq

/-- Two normalized cyclic cocycles are cohomologous exactly when the quotient
of their parameters is a norm. -/
theorem cohomologous_parameter_div (hn : 1 < n)
    (c d : NMCocycl₂ (G := C (n := n)) (M := M)) :
    MHTwo.IsCohomologous c d ↔
      ∃ z : M, parameter c / parameter d =
        (norm (n := n) (M := M) z : M) := by
  constructor
  · exact parameter_div_cohomologous
  · rintro ⟨z, hz⟩
    let q := c * d⁻¹
    have hq : parameter q = (norm (n := n) (M := M) z : M) := by
      rw [parameter_mul, parameter_inv]
      simpa only [div_eq_mul_inv] using hz
    have hb := isMulCoboundary₂_of_parameter_eq_norm hn q z hq
    simpa [MHTwo.IsCohomologous, q, div_eq_mul_inv] using hb

/-- The cyclic parameter, regarded as a homomorphism into the invariant
subgroup. -/
def parameterHom :
    NMCocycl₂ (G := C (n := n)) (M := M) →*
      invariants (n := n) (M := M) where
  toFun c := ⟨parameter c, parameter_mem_invariants c⟩
  map_one' := by apply Subtype.ext; exact parameter_one
  map_mul' c d := by apply Subtype.ext; exact parameter_mul c d

/-- The parameter modulo norms is well-defined on multiplicative `H²`. -/
def classParameter :
    MHTwo (C (n := n)) M → invariantsModNorm (n := n) (M := M) :=
  Quotient.lift
    (fun c ↦ QuotientGroup.mk' (norm (n := n) (M := M)).range
      (parameterHom c))
    (by
      intro c d hcd
      change QuotientGroup.mk' (norm (n := n) (M := M)).range (parameterHom c) =
        QuotientGroup.mk' (norm (n := n) (M := M)).range (parameterHom d)
      apply QuotientGroup.eq_iff_div_mem.mpr
      obtain ⟨z, hz⟩ := parameter_div_cohomologous hcd
      change parameterHom c / parameterHom d ∈
        (norm (n := n) (M := M)).range
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact hz.symm)

@[simp]
theorem classParameter_mk
    (c : NMCocycl₂ (G := C (n := n)) (M := M)) :
    classParameter (MHTwo.mk c) =
      QuotientGroup.mk' (norm (n := n) (M := M)).range (parameterHom c) :=
  rfl

/-- The parameter modulo norms as a homomorphism on multiplicative `H²`. -/
def classParameterHom :
    MHTwo (C (n := n)) M →*
      invariantsModNorm (n := n) (M := M) where
  toFun := classParameter
  map_one' := by
    change QuotientGroup.mk' (norm (n := n) (M := M)).range
      (parameterHom 1) = 1
    rw [map_one]
    exact map_one (QuotientGroup.mk' (norm (n := n) (M := M)).range)
  map_mul' x y := by
    induction x, y using Quotient.inductionOn₂ with
    | _ c d =>
        change QuotientGroup.mk' _ (parameterHom (c * d)) =
          QuotientGroup.mk' _ (parameterHom c) *
            QuotientGroup.mk' _ (parameterHom d)
        rw [map_mul]
        exact map_mul (QuotientGroup.mk' (norm (n := n) (M := M)).range)
          (parameterHom c) (parameterHom d)

private theorem class_parameter_injective (hn : 1 < n) :
    Function.Injective (classParameterHom (n := n) (M := M)) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  obtain ⟨d, rfl⟩ := MHTwo.exists_mk_eq y
  change QuotientGroup.mk' (norm (n := n) (M := M)).range (parameterHom c) =
    QuotientGroup.mk' (norm (n := n) (M := M)).range (parameterHom d) at hxy
  have hxy' :
      ((parameterHom c : invariants (n := n) (M := M)) :
          invariantsModNorm (n := n) (M := M)) =
        ((parameterHom d : invariants (n := n) (M := M)) :
          invariantsModNorm (n := n) (M := M)) := hxy
  rw [QuotientGroup.eq_iff_div_mem] at hxy'
  change parameterHom c / parameterHom d ∈
    (norm (n := n) (M := M)).range at hxy'
  obtain ⟨z, hz⟩ := hxy'
  rw [MHTwo.mk_eq_iff,
    cohomologous_parameter_div hn]
  refine ⟨z, ?_⟩
  exact congrArg Subtype.val hz.symm

private theorem class_parameter_surjective (hn : 1 < n) :
    Function.Surjective (classParameterHom (n := n) (M := M)) := by
  intro q
  obtain ⟨pi, rfl⟩ :=
    QuotientGroup.mk'_surjective (norm (n := n) (M := M)).range q
  let c := CCarry.factorSet pi.1 pi.2
  refine ⟨MHTwo.mk c, ?_⟩
  change QuotientGroup.mk' _ (parameterHom c) = QuotientGroup.mk' _ pi
  apply congrArg (QuotientGroup.mk' (norm (n := n) (M := M)).range)
  apply Subtype.ext
  exact parameter_factorSet hn pi.1 pi.2

/-- **Cyclic multiplicative `H²` calculation.** For a cyclic group of order
`n > 1`, multiplicative second cohomology is the group of invariant elements
modulo norms. -/
noncomputable def mulInvariantsMod (hn : 1 < n) :
    MHTwo (C (n := n)) M ≃*
      invariantsModNorm (n := n) (M := M) :=
  MulEquiv.ofBijective (classParameterHom (n := n) (M := M))
    ⟨class_parameter_injective hn, class_parameter_surjective hn⟩

/-- Under the cyclic `H²` equivalence, the inverse of an invariant class is
represented by Milne's carry cocycle. -/
theorem symm_mk_carry (hn : 1 < n)
    (pi : invariants (n := n) (M := M)) :
    (mulInvariantsMod (n := n) (M := M) hn).symm
        (QuotientGroup.mk' (norm (n := n) (M := M)).range pi) =
      MHTwo.mk (CCarry.factorSet pi.1 pi.2) := by
  apply (mulInvariantsMod (n := n) (M := M) hn).injective
  simp only [MulEquiv.apply_symm_apply]
  change QuotientGroup.mk' _ pi =
    classParameterHom (MHTwo.mk (CCarry.factorSet pi.1 pi.2))
  change QuotientGroup.mk' _ pi =
    QuotientGroup.mk' _ (parameterHom (CCarry.factorSet pi.1 pi.2))
  apply congrArg (QuotientGroup.mk' (norm (n := n) (M := M)).range)
  apply Subtype.ext
  exact (parameter_factorSet hn pi.1 pi.2).symm

end CyclicH2

end

end Submission.CField.LBrauer
