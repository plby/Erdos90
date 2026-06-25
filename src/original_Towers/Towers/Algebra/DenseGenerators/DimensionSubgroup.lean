import Mathlib
import Towers.Algebra.DenseGenerators.WeightedFiltration


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

/-- The dimension subgroup defined by the finite augmentation filtration. -/
def dSubgro
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (n : ℕ) :
    Subgroup G where
  carrier :=
    { g : G |
      groupAlgebraSub p G g ∈ augmentationIdealPower p G n }
  one_mem' := by
    simp [groupAlgebraSub, augmentationIdealPower]
  mul_mem' := by
    intro a b ha hb
    let I : Ideal (denseGroupAlgebra p G) :=
      denseGeneratorsIdeal p G
    have haI :
        groupAlgebraSub p G a ∈ I ^ n := by
      exact
        (Submodule.restrictScalars_mem (ZMod p) (I ^ n)
          (groupAlgebraSub p G a)).mp (by simpa [augmentationIdealPower, I] using ha)
    have hbI :
        groupAlgebraSub p G b ∈ I ^ n := by
      exact
        (Submodule.restrictScalars_mem (ZMod p) (I ^ n)
          (groupAlgebraSub p G b)).mp (by simpa [augmentationIdealPower, I] using hb)
    have hmul :
        groupAlgebraSub p G (a * b) =
          denseGeneratorsElement p G a *
              groupAlgebraSub p G b +
            groupAlgebraSub p G a := by
      simpa [groupAlgebraSub] using
        dense_element_sub
          (p := p) (Λ := G) a b
    have hmemI :
        groupAlgebraSub p G (a * b) ∈ I ^ n := by
      rw [hmul]
      exact (I ^ n).add_mem ((I ^ n).mul_mem_left _ hbI) haI
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ n)
        (groupAlgebraSub p G (a * b))).mpr (by simpa [I] using hmemI)
  inv_mem' := by
    intro a ha
    let I : Ideal (denseGroupAlgebra p G) :=
      denseGeneratorsIdeal p G
    have haI :
        groupAlgebraSub p G a ∈ I ^ n := by
      exact
        (Submodule.restrictScalars_mem (ZMod p) (I ^ n)
          (groupAlgebraSub p G a)).mp (by simpa [augmentationIdealPower, I] using ha)
    have hinv :
        groupAlgebraSub p G a⁻¹ =
          -((denseGeneratorsElement p G a⁻¹) *
            groupAlgebraSub p G a) := by
      simpa [groupAlgebraSub] using
        dense_element_inv
          (p := p) (Λ := G) a
    have hmemI :
        groupAlgebraSub p G a⁻¹ ∈ I ^ n := by
      rw [hinv]
      exact (I ^ n).neg_mem ((I ^ n).mul_mem_left _ haI)
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ n)
        (groupAlgebraSub p G a⁻¹)).mpr (by simpa [I] using hmemI)

/-- The augmentation powers are decreasing. -/
lemma augmentation_ideal_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {m n : ℕ}
    (hmn : m ≤ n) :
    augmentationIdealPower p G n ≤ augmentationIdealPower p G m := by
  intro x hx
  let I : Ideal (denseGroupAlgebra p G) :=
    denseGeneratorsIdeal p G
  have hxI : x ∈ I ^ n := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ n) x).mp
        (by simpa [augmentationIdealPower, I] using hx)
  have hle : I ^ n ≤ I ^ m :=
    Ideal.pow_le_pow_right hmn
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ m) x).mpr
      (by simpa [I] using hle hxI)

/-- Elements of the lower central series have the expected augmentation depth. -/
lemma lower_series_sub
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {i : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    groupAlgebraSub p G x ∈
      augmentationIdealPower p G (i + 1) := by
  have hxcong :
      dDCongru p G (i + 1) x :=
    dense_generators_pow
      (p := p) (Λ := G) hx
  exact
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p G ^ (i + 1))
      (groupAlgebraSub p G x)).mpr
      (by simpa [groupAlgebraSub, dDCongru]
        using hxcong)

/-- Taking a `p^j`th power multiplies augmentation depth by `p^j`. -/
lemma algebra_sub_ideal
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r j : ℕ} {x : G}
    (hx :
      groupAlgebraSub p G x ∈ augmentationIdealPower p G r) :
    groupAlgebraSub p G (x ^ (p ^ j)) ∈
      augmentationIdealPower p G (r * p ^ j) := by
  have hxcong :
      dDCongru p G r x := by
    have hxI :
        groupAlgebraSub p G x ∈
          denseGeneratorsIdeal p G ^ r :=
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p G ^ r)
        (groupAlgebraSub p G x)).mp
        (by simpa [augmentationIdealPower] using hx)
    simpa [groupAlgebraSub, dDCongru] using hxI
  have hxpower :
      dDCongru p G (r * p ^ j) (x ^ (p ^ j)) :=
    dDCongru.pow_prime_power
      (p := p) (Λ := G) (r := r) (j := j) hxcong
  exact
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p G ^ (r * p ^ j))
      (groupAlgebraSub p G (x ^ (p ^ j)))).mpr
      (by simpa [groupAlgebraSub, dDCongru]
        using hxpower)

/-- Each Zassenhaus generator lies in the matching dimension subgroup. -/
lemma set_dimension_subgroup
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} :
    zassenhausGeneratorSet p G n ≤
      (dSubgro p G n : Set G) := by
  intro g hg
  rcases hg with ⟨i, j, x, hx_lcs, hle, rfl⟩
  have hx_depth :
      groupAlgebraSub p G x ∈
        augmentationIdealPower p G (i + 1) :=
    lower_series_sub
      (p := p) hx_lcs
  have hx_power :
      groupAlgebraSub p G (x ^ (p ^ j)) ∈
        augmentationIdealPower p G ((i + 1) * p ^ j) :=
    algebra_sub_ideal
      (p := p) hx_depth
  exact augmentation_ideal_antitone
    (p := p) (G := G) hle hx_power

/-- Easy inclusion: `D_n(G) ≤ {g : [g] - [1] ∈ I^n}`. -/
lemma filtration_dimension_subgroup
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (n : ℕ) :
    zassenhausFiltration p G n ≤ dSubgro p G n := by
  rw [zassenhausFiltration]
  exact
    (Subgroup.closure_le (dSubgro p G n)).2
      (set_dimension_subgroup (p := p) (G := G) (n := n))

/-- Abbreviation for the ordinary group algebra over `ZMod p`. -/
abbrev FG
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] :=
  MonoidAlgebra (ZMod p) G

/-- Abbreviation for the `n`th Zassenhaus subgroup. -/
abbrev D
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (n : ℕ) :
    Subgroup G :=
  zassenhausFiltration p G n

/-- Abbreviation for the `n`th augmentation-ideal power. -/
abbrev Ipow
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (n : ℕ) :
    Submodule (ZMod p) (FG p G) :=
  augmentationIdealPower p G n

/-- Easy direction of the dimension-subgroup theorem: `g ∈ D_n` implies `[g] - [1] ∈ I^n`. -/
lemma zassenhaus_implies_sub
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} {g : G}
    (hg : g ∈ D p G n) :
    groupAlgebraSub p G g ∈ Ipow p G n :=
  filtration_dimension_subgroup (p := p) (G := G) n hg

/-- Consecutive Zassenhaus filtration terms are nested. -/
lemma d_le_d
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (n : ℕ) :
    D p G (n + 1) ≤ D p G n :=
  zassenhaus_filtration_succ p G n

/-- The augmentation powers are decreasing, in the local abbreviation. -/
lemma Ipow_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {m n : ℕ}
    (hmn : m ≤ n) :
    Ipow p G n ≤ Ipow p G m :=
  augmentation_ideal_antitone (p := p) (G := G) hmn

/-- The equivalence relation on `D_n` whose quotient is morally `D_n / D_(n+1)`.

We use right-coset style: `x ~ y` iff `x * y⁻¹ ∈ D_(n+1)`. -/
def zassenhausLayerSetoid
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G]
    (n : ℕ) :
    Setoid (D p G n) where
  r x y :=
    ((x : G) * (y : G)⁻¹) ∈ D p G (n + 1)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      simp
    · intro x y hxy
      have hinv :
          (((x : G) * (y : G)⁻¹)⁻¹) ∈ D p G (n + 1) :=
        (D p G (n + 1)).inv_mem hxy
      simpa [mul_inv_rev] using hinv
    · intro x y z hxy hyz
      have hmul :
          (((x : G) * (y : G)⁻¹) * ((y : G) * (z : G)⁻¹))
            ∈ D p G (n + 1) :=
        (D p G (n + 1)).mul_mem hxy hyz
      simpa [mul_assoc] using hmul

/-- The `n`th Zassenhaus layer, modeled as the raw quotient `D_n / D_(n+1)`. -/
def zLayer
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G]
    (n : ℕ) :
    Type u :=
  Quotient (zassenhausLayerSetoid p G n)

namespace zLayer

/-- The class of an element `g ∈ D_n` in the abstract layer `D_n / D_(n+1)`. -/
def mk
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} {g : G}
    (hg : g ∈ D p G n) :
    zLayer p G n :=
  Quotient.mk (zassenhausLayerSetoid p G n) ⟨g, hg⟩

/-- The identity class in `D_n / D_(n+1)`. -/
def one
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) :
    zLayer p G n :=
  mk (p := p) (G := G) (n := n) (g := 1) ((D p G n).one_mem)

/-- The kernel criterion for the quotient map `D_n → D_n / D_(n+1)`. -/
lemma mk_one_iff
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} {g : G}
    (hg : g ∈ D p G n) :
    mk (p := p) (G := G) (n := n) (g := g) hg =
      one (p := p) (G := G) n ↔
      g ∈ D p G (n + 1) := by
  constructor
  · intro h
    have hrel := Quotient.exact h
    change (g * (1 : G)⁻¹) ∈ D p G (n + 1) at hrel
    simpa using hrel
  · intro hg_next
    apply Quotient.sound
    change (g * (1 : G)⁻¹) ∈ D p G (n + 1)
    simpa using hg_next

end zLayer

/-- The equivalence relation on `I^n` whose quotient is morally `I^n / I^(n+1)`.

We use `a ~ b` iff `a - b ∈ I^(n+1)`. -/
def gradedPieceSetoid
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G]
    (n : ℕ) :
    Setoid (Ipow p G n) where
  r a b :=
    ((a : FG p G) - (b : FG p G)) ∈ Ipow p G (n + 1)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro a
      simp
    · intro a b hab
      have hneg :
          -((a : FG p G) - (b : FG p G)) ∈ Ipow p G (n + 1) :=
        (Ipow p G (n + 1)).neg_mem hab
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    · intro a b c hab hbc
      have hsum :
          (((a : FG p G) - (b : FG p G)) +
            ((b : FG p G) - (c : FG p G))) ∈ Ipow p G (n + 1) :=
        (Ipow p G (n + 1)).add_mem hab hbc
      convert hsum using 1
      abel

/-- The `n`th augmentation graded piece, modeled as the raw quotient `I^n / I^(n+1)`. -/
def aGPiece
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G]
    (n : ℕ) :
    Type u :=
  Quotient (gradedPieceSetoid p G n)

namespace aGPiece

/-- The class of an element of `I^n` in the abstract graded piece `I^n / I^(n+1)`. -/
def mk
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    {a : FG p G}
    (ha : a ∈ Ipow p G n) :
    aGPiece p G n :=
  Quotient.mk (gradedPieceSetoid p G n) ⟨a, ha⟩

/-- The zero class in `I^n / I^(n+1)`. -/
def zero
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) :
    aGPiece p G n :=
  mk (p := p) (G := G) (n := n) (a := 0) ((Ipow p G n).zero_mem)

/-- The quotient-kernel criterion for `I^n → I^n / I^(n+1)`. -/
lemma mk_zero_iff
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    {a : FG p G}
    (ha : a ∈ Ipow p G n) :
    mk (p := p) (G := G) (n := n) (a := a) ha =
      zero (p := p) (G := G) n ↔
      a ∈ Ipow p G (n + 1) := by
  constructor
  · intro h
    have hrel := Quotient.exact h
    change (a - (0 : FG p G)) ∈ Ipow p G (n + 1) at hrel
    simpa using hrel
  · intro ha_next
    apply Quotient.sound
    change (a - (0 : FG p G)) ∈ Ipow p G (n + 1)
    simpa using ha_next

end aGPiece

/-- If `x * y⁻¹ ∈ D_(n+1)`, then `[x] - [1]` and `[y] - [1]` have the same
class in `I^n / I^(n+1)`. -/
lemma sub_next_inv
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} {x y : G}
    (hxy : x * y⁻¹ ∈ D p G (n + 1)) :
    groupAlgebraSub p G x - groupAlgebraSub p G y
      ∈ Ipow p G (n + 1) := by
  let I : Ideal (FG p G) :=
    denseGeneratorsIdeal p G
  have hyinvx :
      y⁻¹ * x ∈ D p G (n + 1) := by
    have hnormal : (D p G (n + 1)).Normal :=
      zassenhausFiltration_normal p G (n + 1)
    have hconj :
        y⁻¹ * (x * y⁻¹) * (y⁻¹)⁻¹ ∈ D p G (n + 1) :=
      hnormal.conj_mem (x * y⁻¹) hxy y⁻¹
    simpa [mul_assoc] using hconj
  have hyinvx_sub :
      groupAlgebraSub p G (y⁻¹ * x) ∈ Ipow p G (n + 1) :=
    zassenhaus_implies_sub
      (p := p) (G := G) (n := n + 1) hyinvx
  have hyinvx_I :
      groupAlgebraSub p G (y⁻¹ * x) ∈ I ^ (n + 1) := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ (n + 1))
        (groupAlgebraSub p G (y⁻¹ * x))).mp
        (by simpa [Ipow, augmentationIdealPower, I] using hyinvx_sub)
  have hmul_I :
      denseGeneratorsElement p G y *
          groupAlgebraSub p G (y⁻¹ * x) ∈ I ^ (n + 1) :=
    (I ^ (n + 1)).mul_mem_left
      (denseGeneratorsElement p G y) hyinvx_I
  have hcanonical_mul :
      denseGeneratorsElement p G y *
          denseGeneratorsElement p G (y⁻¹ * x) =
        denseGeneratorsElement p G x := by
    rw [← dense_element_mul]
    simp
  have hidentity :
      groupAlgebraSub p G x - groupAlgebraSub p G y =
        denseGeneratorsElement p G y *
          groupAlgebraSub p G (y⁻¹ * x) := by
    simp only [groupAlgebraSub]
    rw [mul_sub, hcanonical_mul]
    noncomm_ring
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ (n + 1))
      (groupAlgebraSub p G x - groupAlgebraSub p G y)).mpr
      (by simpa [Ipow, augmentationIdealPower, I, hidentity] using hmul_I)

/-- The ordinary identity `[1] - [1] = 0`. -/
lemma algebra_sub_one
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] :
    groupAlgebraSub p G (1 : G) = 0 := by
  simp [groupAlgebraSub]

@[simp]
lemma algebra_canonical_one
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] :
    denseGeneratorsElement p G (1 : G) =
      (1 : denseGroupAlgebra p G) := by
  simp

@[simp]
lemma algebra_canonical_mul
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x y : G) :
    denseGeneratorsElement p G (x * y) =
      denseGeneratorsElement p G x *
        denseGeneratorsElement p G y := by
  simp

@[simp]
lemma algebra_canonical_pow
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G) (k : ℕ) :
    denseGeneratorsElement p G (x ^ k) =
      denseGeneratorsElement p G x ^ k := by
  simp

lemma algebra_sub_left
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x y : G) :
    groupAlgebraSub p G (x * y) =
      denseGeneratorsElement p G x *
          groupAlgebraSub p G y +
        groupAlgebraSub p G x := by
  simpa [groupAlgebraSub] using
    dense_element_sub
      (p := p) (Λ := G) x y

lemma algebra_sub_right
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x y : G) :
    groupAlgebraSub p G (x * y) =
      groupAlgebraSub p G x *
          denseGeneratorsElement p G y +
        groupAlgebraSub p G y := by
  simp only [groupAlgebraSub, dense_element_mul]
  noncomm_ring

lemma algebra_sub_inv
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G) :
    groupAlgebraSub p G x⁻¹ =
      -denseGeneratorsElement p G x⁻¹ *
        groupAlgebraSub p G x := by
  simpa [groupAlgebraSub] using
    dense_element_inv
      (p := p) (Λ := G) x

/-- In characteristic `p`, the `p`th power of an augmentation letter is the letter attached to
the `p`th group power. -/
lemma algebra_sub_prime
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G) :
    groupAlgebraSub p G x ^ p =
      groupAlgebraSub p G (x ^ p) := by
  simpa [groupAlgebraSub, pow_one] using
    (dense_generators_element
      (p := p) (Λ := G) (j := 1) (x := x)).symm

/-- Swapping two augmentation letters produces the group-algebra commutator difference
`[xy] - [yx]`. -/
lemma algebra_sub_swap
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x y : G) :
    groupAlgebraSub p G x * groupAlgebraSub p G y -
        groupAlgebraSub p G y * groupAlgebraSub p G x =
      denseGeneratorsElement p G (x * y) -
        denseGeneratorsElement p G (y * x) := by
  simp only [groupAlgebraSub]
  rw [
    dense_element_mul,
    dense_element_mul
  ]
  noncomm_ring

/-- The swap defect is controlled by the augmentation letter of the group commutator. -/
lemma sub_swap_commutator
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x y : G) :
    groupAlgebraSub p G x * groupAlgebraSub p G y -
        groupAlgebraSub p G y * groupAlgebraSub p G x =
      groupAlgebraSub p G (x * y * x⁻¹ * y⁻¹) *
        denseGeneratorsElement p G (y * x) := by
  have hcomm : (x * y * x⁻¹ * y⁻¹) * (y * x) = x * y := by
    group
  calc
    groupAlgebraSub p G x * groupAlgebraSub p G y -
        groupAlgebraSub p G y * groupAlgebraSub p G x =
      denseGeneratorsElement p G (x * y) -
        denseGeneratorsElement p G (y * x) := by
        exact algebra_sub_swap p G x y
    _ =
      denseGeneratorsElement p G ((x * y * x⁻¹ * y⁻¹) * (y * x)) -
        denseGeneratorsElement p G (y * x) := by
        rw [hcomm]
    _ =
      denseGeneratorsElement p G (x * y * x⁻¹ * y⁻¹) *
          denseGeneratorsElement p G (y * x) -
        denseGeneratorsElement p G (y * x) := by
        rw [dense_element_mul]
    _ =
      groupAlgebraSub p G (x * y * x⁻¹ * y⁻¹) *
        denseGeneratorsElement p G (y * x) := by
        simp only [groupAlgebraSub]
        noncomm_ring

lemma group_sub_ideal
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G) :
    groupAlgebraSub p G x ∈
      denseGeneratorsIdeal p G := by
  simpa [groupAlgebraSub] using
    dense_element_ideal
      (p := p) (Λ := G) x

lemma group_algebra_sub
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G) :
    groupAlgebraSub p G x ∈ augmentationIdealPower p G 1 := by
  let I : Ideal (denseGroupAlgebra p G) :=
    denseGeneratorsIdeal p G
  have hxI : groupAlgebraSub p G x ∈ I ^ 1 := by
    rw [Submodule.pow_one]
    exact group_sub_ideal p G x
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ 1)
      (groupAlgebraSub p G x)).mpr
      (by simpa [I, augmentationIdealPower] using hxI)

lemma augmentation_ideal_left
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    {n : ℕ}
    (r : denseGroupAlgebra p G)
    {a : denseGroupAlgebra p G}
    (ha : a ∈ augmentationIdealPower p G n) :
    r * a ∈ augmentationIdealPower p G n := by
  let I : Ideal (denseGroupAlgebra p G) :=
    denseGeneratorsIdeal p G
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  have haI : a ∈ I ^ n := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ n) a).mp
        (by simpa [I, augmentationIdealPower] using ha)
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ n) (r * a)).mpr
      (by exact (I ^ n).mul_mem_left r haI)

lemma augmentation_ideal_right
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    {n : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ augmentationIdealPower p G n)
    (r : denseGroupAlgebra p G) :
    a * r ∈ augmentationIdealPower p G n := by
  let I : Ideal (denseGroupAlgebra p G) :=
    denseGeneratorsIdeal p G
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  have haI : a ∈ I ^ n := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ n) a).mp
        (by simpa [I, augmentationIdealPower] using ha)
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ n) (a * r)).mpr
      (by exact (I ^ n).mul_mem_right r haI)

lemma augmentation_ideal_mul
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    {a b : denseGroupAlgebra p G}
    {r s : ℕ}
    (ha : a ∈ augmentationIdealPower p G r)
    (hb : b ∈ augmentationIdealPower p G s) :
    a * b ∈ augmentationIdealPower p G (r + s) := by
  let I : Ideal (denseGroupAlgebra p G) :=
    denseGeneratorsIdeal p G
  letI : I.IsTwoSided := by
    dsimp [I]
    rw [dense_generators_ker]
    infer_instance
  have haI : a ∈ I ^ r := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ r) a).mp
        (by simpa [I, augmentationIdealPower] using ha)
  have hbI : b ∈ I ^ s := by
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ s) b).mp
        (by simpa [I, augmentationIdealPower] using hb)
  have hmul : a * b ∈ I ^ (r + s) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul haI hbI
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ (r + s)) (a * b)).mpr
      (by simpa [I] using hmul)

/-- Conjugating an element of augmentation depth `r` by a group element of augmentation depth
`w` changes it only in depth `r + w`. -/
lemma conj_ga_add
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    {x : G}
    {a : denseGroupAlgebra p G}
    {r w : ℕ}
    (hx : groupAlgebraSub p G x ∈ augmentationIdealPower p G w)
    (ha : a ∈ augmentationIdealPower p G r) :
    conjGA p G x a - a ∈ augmentationIdealPower p G (r + w) := by
  have hleft :
      groupAlgebraSub p G x * a ∈ augmentationIdealPower p G (w + r) :=
    augmentation_ideal_mul p G hx ha
  have hleft' :
      groupAlgebraSub p G x * a ∈ augmentationIdealPower p G (r + w) := by
    simpa [Nat.add_comm] using hleft
  have hright :
      a * groupAlgebraSub p G x ∈ augmentationIdealPower p G (r + w) :=
    augmentation_ideal_mul p G ha hx
  have hdiff :
      groupAlgebraSub p G x * a - a * groupAlgebraSub p G x ∈
        augmentationIdealPower p G (r + w) :=
    (augmentationIdealPower p G (r + w)).sub_mem hleft' hright
  have hidentity :
      conjGA p G x a - a =
        (groupAlgebraSub p G x * a - a * groupAlgebraSub p G x) *
          ga p G x⁻¹ := by
    simp only [conjGA, groupAlgebraSub, ga]
    have hright_inv :
        denseGeneratorsElement p G x *
            denseGeneratorsElement p G x⁻¹ =
          (1 : denseGroupAlgebra p G) := by
      rw [← dense_element_mul]
      simp
    noncomm_ring [hright_inv]
  rw [hidentity]
  exact augmentation_ideal_right p G hdiff (ga p G x⁻¹)

/-- Pointwise antitonicity for the Zassenhaus filtration. -/
lemma zassenhaus_filtration
    (p : ℕ)
    (G : Type u) [Group G]
    {m n : ℕ}
    (hmn : m ≤ n)
    {x : G}
    (hx : x ∈ zassenhausFiltration p G n) :
    x ∈ zassenhausFiltration p G m :=
  zassenhausFiltration_antitone p G hmn hx

/-- If a Zassenhaus level is trivial, every element of that level is equal to `1`. -/
lemma one_filtration_bot
    (p : ℕ)
    (G : Type u) [Group G]
    {m : ℕ}
    (hbot : zassenhausFiltration p G m = ⊥)
    {x : G}
    (hx : x ∈ zassenhausFiltration p G m) :
    x = 1 := by
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hbot] using hx
  exact Subgroup.mem_bot.mp hxbot

/-- If `D_m` is trivial, then every element lying in a later Zassenhaus level is equal to `1`. -/
lemma zassenhaus_filtration_bot
    (p : ℕ)
    (G : Type u) [Group G]
    {m r : ℕ}
    (hbot : zassenhausFiltration p G m = ⊥)
    (hmr : m ≤ r)
    {x : G}
    (hx : x ∈ zassenhausFiltration p G r) :
    x = 1 :=
  one_filtration_bot
    p G hbot
    (zassenhaus_filtration p G hmr hx)

end Towers
