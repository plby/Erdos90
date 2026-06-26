import Towers.Group.DimensionSubgroup
import Towers.Group.RestrictedSeries
import Towers.Group.PresentationData
import Towers.Group.GolodShafarevichCore
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

open scoped commutatorElement

/-!
# Mod-`p` Zassenhaus filtration (dimension-subgroup model)

This file fixes the coefficient ring convention for the Zassenhaus filtration used
throughout the project: the `n`th term is the dimension subgroup defined by the
augmentation ideal in `(ZMod p)[G]`.  For prime `p` this is the usual mod-`p`
Zassenhaus filtration; we keep the definitions available for any natural `p` so
that basic API does not carry unnecessary primality hypotheses.
-/

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (p : ℕ) (G : Type*) [Group G]

/-- The group algebra over `ZMod p` has characteristic `p` when `p` is prime. -/
theorem char_monoid_zmod [Fact p.Prime] :
    CharP (MonoidAlgebra (ZMod p) G) p := by
  have hinj : Function.Injective
      (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G)) := by
    intro a b h
    have hc := congrArg (fun f : MonoidAlgebra (ZMod p) G => f 1) h
    simpa [MonoidAlgebra.coe_algebraMap] using hc
  exact charP_of_injective_algebraMap hinj p

/-- The mod-`p` Zassenhaus subgroup, defined via augmentation powers in `(ZMod p)[G]`.
For prime `p`, this is the standard dimension-subgroup definition of the
Zassenhaus filtration. -/
def zSubgro (n : ℕ) : Subgroup G :=
  dSubgro (ZMod p) G n

@[simp] theorem mem_zassenhausSubgroup {n : ℕ} {g : G} :
    g ∈ zSubgro p G n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 : MonoidAlgebra (ZMod p) G) ∈
        augmentationPower (ZMod p) G n :=
  Iff.rfl

/-- The mod-`p` Zassenhaus terms as a bundled descending filtration. -/
def zassenhausFiltration : DFilt G :=
  dimensionFiltration (ZMod p) G

@[simp] theorem zassenhaus_subgroup_top : zSubgro p G 0 = ⊤ := by
  ext g
  rw [mem_zassenhausSubgroup]
  simp [augmentationPower_zero]

@[simp] theorem zassenhaus_one_top : zSubgro p G 1 = ⊤ := by
  exact dimension_one_top (ZMod p) G

/-- Zassenhaus terms are normal subgroups. -/
theorem zassenhausSubgroup_normal (n : ℕ) : (zSubgro p G n).Normal :=
  dimensionSubgroup_normal (ZMod p) G n

instance zSubgro.instNormal (n : ℕ) : (zSubgro p G n).Normal :=
  zassenhausSubgroup_normal p G n

/-- The Zassenhaus filtration is descending in the index. -/
theorem zassenhausSubgroup_antitone : Antitone (zSubgro p G) :=
  dimensionSubgroup_antitone (ZMod p) G

/-- Consecutive Zassenhaus terms are nested. -/
theorem zassenhaus_subgroup_succ (n : ℕ) :
    zSubgro p G (n + 1) ≤ zSubgro p G n :=
  dimension_subgroup_succ (ZMod p) G n



/-- Any Zassenhaus term of index at most one is top. -/
theorem zassenhaus_top_one {n : ℕ} (hn : n ≤ 1) :
    zSubgro p G n = ⊤ := by
  interval_cases n <;> simp

/-- Joins of two Zassenhaus terms are the term at the smaller index. -/
theorem zassenhaus_sup_min (m n : ℕ) :
    zSubgro p G m ⊔ zSubgro p G n =
      zSubgro p G (min m n) := by
  exact dimension_sup_min (ZMod p) G m n

/-- Intersections of two Zassenhaus terms are the term at the larger index. -/
theorem zassenhaus_inf_max (m n : ℕ) :
    zSubgro p G m ⊓ zSubgro p G n =
      zSubgro p G (max m n) := by
  exact dimension_inf_max (ZMod p) G m n

/-- Comparable-intersection orientation for Zassenhaus terms. -/
theorem zassenhaus_inf_right {m n : ℕ} (h : m ≤ n) :
    zSubgro p G m ⊓ zSubgro p G n = zSubgro p G n := by
  rw [zassenhaus_inf_max]
  simp [max_eq_right h]

/-- Symmetric comparable-intersection orientation for Zassenhaus terms. -/
theorem zassenhaus_inf_left {m n : ℕ} (h : n ≤ m) :
    zSubgro p G m ⊓ zSubgro p G n = zSubgro p G m := by
  rw [zassenhaus_inf_max]
  simp [max_eq_left h]

/-- Comparable-join orientation for Zassenhaus terms. -/
theorem zassenhaus_sup_left {m n : ℕ} (h : m ≤ n) :
    zSubgro p G m ⊔ zSubgro p G n = zSubgro p G m := by
  rw [zassenhaus_sup_min]
  simp [min_eq_left h]

/-- Symmetric comparable-join orientation for Zassenhaus terms. -/
theorem zassenhaus_sup_right {m n : ℕ} (h : n ≤ m) :
    zSubgro p G m ⊔ zSubgro p G n = zSubgro p G n := by
  rw [zassenhaus_sup_min]
  simp [min_eq_right h]

@[simp] theorem zassenhausFiltration_term (n : ℕ) :
    (zassenhausFiltration p G).term n = zSubgro p G n := rfl


/-- Group homomorphisms preserve Zassenhaus terms. -/
theorem zassenhaus_subgroup_comap {H : Type*} [Group H] (φ : G →* H) (n : ℕ) :
    zSubgro p G n ≤ (zSubgro p H n).comap φ :=
  dimension_subgroup_comap (R := ZMod p) φ n

/-- If a Zassenhaus term vanishes in a quotient, then the source term lies in the
quotient kernel. -/
theorem zassenhaus_subgroup_bot
    {N : Subgroup G} [N.Normal] {n : ℕ}
    (hQ : zSubgro p (G ⧸ N) n = ⊥) :
    zSubgro p G n ≤ N := by
  intro g hg
  have hq :
      QuotientGroup.mk' N g ∈ zSubgro p (G ⧸ N) n :=
    zassenhaus_subgroup_comap p G (QuotientGroup.mk' N) n hg
  have hqBot : QuotientGroup.mk' N g ∈ (⊥ : Subgroup (G ⧸ N)) := by
    simpa [hQ] using hq
  exact (QuotientGroup.eq_one_iff g).mp (by simpa using hqBot)

/-- Zassenhaus terms commute with finite binary products. -/
theorem zassenhausSubgroup_prod (H : Type*) [Group H] (n : ℕ) :
    zSubgro p (G × H) n =
      (zSubgro p G n).prod (zSubgro p H n) :=
  dimensionSubgroup_prod (R := ZMod p) G H n

/-- Concrete multiplicative equivalence behind the product formula for Zassenhaus terms. -/
noncomputable def zassenhausProdEquiv (H : Type*) [Group H] (n : ℕ) :
    zSubgro p (G × H) n ≃*
      (zSubgro p G n × zSubgro p H n) :=
  dimensionSubgroupProd (ZMod p) G H n



/-- For any termwise-onto map of Zassenhaus filtrations, the preimage of a target term
is the source term times the ordinary kernel. -/
theorem comap_sup_onto {H : Type*} [Group H]
    (φ : G →* H) (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    (zSubgro p H n).comap φ = zSubgro p G n ⊔ φ.ker :=
  DFilt.MapsOnto.comap_eq_supker honto n


/-- For a termwise-onto map of Zassenhaus filtrations, exact preimage at a term is
equivalent to kernel containment in that term. -/
theorem comap_maps_onto {H : Type*} [Group H]
    (φ : G →* H) (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    (zSubgro p H n).comap φ = zSubgro p G n ↔
      φ.ker ≤ zSubgro p G n :=
  DFilt.MapsOnto.comap_eqiff_kerle honto n

/-- For a split epimorphism, the preimage of a Zassenhaus term is the source term
multiplied by the kernel. -/
theorem comap_sup_inverse {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    (zSubgro p H n).comap φ = zSubgro p G n ⊔ φ.ker :=
  dimension_comap_sup (ZMod p) φ σ hσ n


/-- A split epimorphism maps each Zassenhaus term onto the corresponding target term. -/
theorem zassenhaus_right_inverse {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    (zSubgro p G n).map φ = zSubgro p H n :=
  dimension_right_inverse (ZMod p) φ σ hσ n


/-- If a split epimorphism is injective, its preimage of each Zassenhaus term is exactly
the corresponding source term. -/
theorem comap_inverse_injective {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (zSubgro p H n).comap φ = zSubgro p G n :=
  dimension_comap_injective (ZMod p) φ σ hσ hinj n

/-- Split epimorphisms are termwise onto for Zassenhaus filtrations. -/
theorem filtration_maps_inverse {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ :=
  dimension_filtration_inverse (ZMod p) φ σ hσ


/-- A surjective homomorphism is termwise onto for Zassenhaus filtrations if the
preimage of every target term is contained in the corresponding source term. -/
theorem filtration_maps_comap {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (zSubgro p H n).comap φ ≤ zSubgro p G n) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ :=
  DFilt.MapsOnto.surj_comap_le
    (dimensionFiltration_preserves (ZMod p) φ) hs hpre

/-- Equality of all Zassenhaus-term preimages is a convenient sufficient condition for
termwise onto compatibility under a surjective homomorphism. -/
theorem filtration_surjective_comap {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (zSubgro p H n).comap φ = zSubgro p G n) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ :=
  DFilt.MapsOnto.surj_comap_eq
    (dimensionFiltration_preserves (ZMod p) φ) hs hpre


/-- Exact preimages of all Zassenhaus terms imply termwise onto compatibility for a
surjective homomorphism, with preservation inferred automa. -/
theorem filtration_comap_exact {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ)
    (hpre : ∀ n, (zSubgro p H n).comap φ = zSubgro p G n) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ :=
  DFilt.MapsOnto.surj_comap_eqexact hs hpre

/-- Surjective-map preimage criterion for target Zassenhaus membership, expressed via
the source augmentation power plus the kernel-relation ideal. -/
theorem image_sup_surjective
    {H : Type*} [Group H] (φ : G →* H) (hs : Function.Surjective φ)
    (n : ℕ) (g : G) :
    φ g ∈ zSubgro p H n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 : MonoidAlgebra (ZMod p) G) ∈
        augmentationPower (ZMod p) G n ⊔ kRIdeal (R := ZMod p) φ := by
  exact dimension_sup_surjective
    (R := ZMod p) φ hs n g

/-- Zassenhaus terms are characteristic subgroups. -/
instance zSubgro.instCharacteristic (n : ℕ) :
    (zSubgro p G n).Characteristic where
  fixed e := by
    ext g
    constructor
    · intro hg
      change e g ∈ zSubgro p G n at hg
      have h := zassenhaus_subgroup_comap p G e.symm.toMonoidHom n hg
      simpa using h
    · intro hg
      change e g ∈ zSubgro p G n
      exact zassenhaus_subgroup_comap p G e.toMonoidHom n hg

/-- Automorphisms preserve membership in each Zassenhaus term.  This is often the
most convenient pointwise form of characteristicity. -/
theorem zassenhaus_subgroup (n : ℕ) (e : G ≃* G) (g : G) :
    e g ∈ zSubgro p G n ↔ g ∈ zSubgro p G n := by
  let H := zSubgro p G n
  have hchar : H.Characteristic := inferInstance
  have hf := hchar.fixed e
  change g ∈ H.comap e.toMonoidHom ↔ g ∈ H
  rw [hf]

/-- Automorphisms map a Zassenhaus term onto itself. -/
theorem zassenhaus_self_equiv (n : ℕ) (e : G ≃* G) :
    (zSubgro p G n).map e.toMonoidHom = zSubgro p G n := by
  let H := zSubgro p G n
  have hchar : H.Characteristic := inferInstance
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hf := hchar.fixed e.symm
    have hy' : e.symm (e y) ∈ H := by simpa using hy
    have hxcomap : e y ∈ H.comap e.symm.toMonoidHom := hy'
    rwa [hf] at hxcomap
  · intro hx
    refine ⟨e.symm x, ?_, ?_⟩
    · have hf := hchar.fixed e
      have hx' : e (e.symm x) ∈ H := by simpa using hx
      have hxcomap : e.symm x ∈ H.comap e.toMonoidHom := hx'
      rwa [hf] at hxcomap
    · simp

/-- Automorphisms pull each Zassenhaus term back to itself.  This is the explicit
self-equivalence specialization of characteristicity. -/
theorem zassenhaus_comap_self (n : ℕ) (e : G ≃* G) :
    (zSubgro p G n).comap e.toMonoidHom = zSubgro p G n := by
  let H := zSubgro p G n
  have hchar : H.Characteristic := inferInstance
  exact hchar.fixed e

/-- Membership is also invariant under the inverse automorphism. -/
theorem zassenhaus_subgroup_symm (n : ℕ) (e : G ≃* G) (g : G) :
    e.symm g ∈ zSubgro p G n ↔ g ∈ zSubgro p G n := by
  simpa using (zassenhaus_subgroup (p := p) (G := G) n e.symm g)

/-- The Zassenhaus filtration is functorial for group homomorphisms. -/
theorem zassenhausFiltration_preserves {H : Type*} [Group H] (φ : G →* H) :
    DFilt.Preserves (zassenhausFiltration p G) (zassenhausFiltration p H) φ := by
  intro n
  rw [Subgroup.map_le_iff_le_comap]
  exact zassenhaus_subgroup_comap p G φ n

/-- A group equivalence is termwise onto for the Zassenhaus filtrations. -/
theorem filtration_maps_onto {H : Type*} [Group H] (e : G ≃* H) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H)
      e.toMonoidHom :=
  DFilt.MapsOnto.of_equiv e
    (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
    (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom)

/-- An automorphism is termwise onto for the Zassenhaus filtration on one group. -/
theorem filtration_onto_self (e : G ≃* G) :
    DFilt.MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p G)
      e.toMonoidHom :=
  filtration_maps_onto (p := p) (G := G) e


/-- `p`th powers lie in the second mod-`p` Zassenhaus term.  The proof uses the
geometric-series identity and the fact that the augmentation of a length-`p` sum is
`p = 0` in `ZMod p`. -/
theorem pow_subgroup_two (g : G) :
    g ^ p ∈ zSubgro p G 2 := by
  rw [mem_zassenhausSubgroup]
  let x : MonoidAlgebra (ZMod p) G := _root_.MonoidAlgebra.of (ZMod p) G g
  let I := augmentationIdeal (ZMod p) G
  let J := augmentationPower (ZMod p) G 2
  change (_root_.MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 :
      MonoidAlgebra (ZMod p) G) ∈ J
  have hxpow : _root_.MonoidAlgebra.of (ZMod p) G (g ^ p) = x ^ p := by
    change _root_.MonoidAlgebra.of (ZMod p) G (g ^ p) =
      (_root_.MonoidAlgebra.of (ZMod p) G g) ^ p
    exact map_pow (_root_.MonoidAlgebra.of (ZMod p) G) g p
  rw [hxpow]
  let S : MonoidAlgebra (ZMod p) G := ∑ i ∈ Finset.range p, x ^ i
  have hgeom : x ^ p - 1 = S * (x - 1) := by
    dsimp [S]
    have h := geom_sum_mul_add (x - 1) p
    have h' : (∑ i ∈ Finset.range p, x ^ i) * (x - 1) + 1 = x ^ p := by
      simpa [sub_add_cancel] using h
    exact sub_eq_iff_eq_add.mpr h'.symm
  rw [hgeom]
  have hS : S ∈ I := by
    dsimp [S, I, augmentationIdeal]
    rw [RingHom.mem_ker]
    simp [x, map_sum]
  have hxI : x - 1 ∈ I := by
    simp [x, I]
  have hJ : J = I * I := by
    dsimp [J, I, augmentationPower]
    change augmentationIdeal (ZMod p) G ^ (1 + 1) = _
    rw [Submodule.pow_succ, Submodule.pow_one]
  rw [hJ]
  exact Ideal.mul_mem_mul hS hxI



/-- The characteristic-`p` power estimate for the Zassenhaus filtration:
if `g ∈ D_n`, then `g^p ∈ D_{np}`. -/
theorem pow_subgroup_self [Fact p.Prime] {n : ℕ} {g : G}
    (hg : g ∈ zSubgro p G n) :
    g ^ p ∈ zSubgro p G (n * p) := by
  let A := MonoidAlgebra (ZMod p) G
  haveI : CharP A p := char_monoid_zmod p G
  rw [mem_zassenhausSubgroup] at hg ⊢
  let x : A := _root_.MonoidAlgebra.of (ZMod p) G g
  let a : A := x - 1
  change (_root_.MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 : A) ∈
    augmentationPower (ZMod p) G (n * p)
  have hxpow : _root_.MonoidAlgebra.of (ZMod p) G (g ^ p) = x ^ p := by
    change _root_.MonoidAlgebra.of (ZMod p) G (g ^ p) =
      (_root_.MonoidAlgebra.of (ZMod p) G g) ^ p
    exact map_pow (_root_.MonoidAlgebra.of (ZMod p) G) g p
  rw [hxpow]
  have hx_eq : x = 1 + a := by
    dsimp [a]
    abel
  have hfresh : x ^ p = 1 + a ^ p := by
    rw [hx_eq]
    have hc : Commute (1 : A) a := Commute.one_left a
    simpa [one_pow] using (add_pow_char_of_commute (R := A) p hc)
  rw [hfresh]
  have ha : a ∈ augmentationPower (ZMod p) G n := by
    simpa [a, x] using hg
  have hap : a ^ p ∈ augmentationPower (ZMod p) G (n * p) :=
    pow_power_mul (R := ZMod p) (G := G) ha
  simpa using hap


/-- Conventional left-multiplied-index form of the characteristic-`p` power estimate. -/
theorem pow_prime_mul [Fact p.Prime] {n : ℕ} {g : G}
    (hg : g ∈ zSubgro p G n) :
    g ^ p ∈ zSubgro p G (p * n) := by
  simpa [Nat.mul_comm] using pow_subgroup_self (p := p) (G := G) hg

/-- Restricted Zassenhaus power law, elementwise form: `g ∈ D_n` implies
`g^p ∈ D_{n+1}`. -/
theorem pow_succ_self [Fact p.Prime] {n : ℕ} {g : G}
    (hg : g ∈ zSubgro p G n) :
    g ^ p ∈ zSubgro p G (n + 1) := by
  cases n with
  | zero =>
      rw [zassenhaus_one_top]
      trivial
  | succ k =>
      have hp2 : 2 ≤ p := Nat.Prime.two_le (Fact.out)
      have hpw : g ^ p ∈ zSubgro p G ((k + 1) * p) :=
        pow_subgroup_self (p := p) (G := G) hg
      exact zassenhausSubgroup_antitone p G (by
        have htwo : (k + 1) + 1 ≤ (k + 1) * 2 := by omega
        have hmul : (k + 1) * 2 ≤ (k + 1) * p :=
          Nat.mul_le_mul_left (k + 1) hp2
        exact le_trans htwo hmul) hpw

/-- Restricted Zassenhaus power law: the subgroup generated by the `p`th powers
of elements of `D_n` is contained in `D_{n+1}`. -/
theorem closure_succ_self [Fact p.Prime] (n : ℕ) :
    Subgroup.closure {y : G | ∃ g ∈ zSubgro p G n, g ^ p = y} ≤
      zSubgro p G (n + 1) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact pow_succ_self (p := p) (G := G) hg

/-- Iterating the characteristic-`p` power estimate multiplies depth by `p ^ j`. -/
theorem pow_zassenhaus_subgroup [Fact p.Prime] {n j : ℕ} {g : G}
    (hg : g ∈ zSubgro p G n) :
    g ^ (p ^ j) ∈ zSubgro p G (n * p ^ j) := by
  induction j with
  | zero => simpa
  | succ j ih =>
      simpa [pow_succ, pow_mul, Nat.mul_assoc] using
        (pow_subgroup_self (p := p) (G := G) ih)

/-- A prime-power iterate belongs to every shallower Zassenhaus term. -/
theorem p_zassenhaus_subgroup [Fact p.Prime]
    {m n j : ℕ} {g : G}
    (hg : g ∈ zSubgro p G m)
    (hle : n ≤ m * p ^ j) :
    g ^ (p ^ j) ∈ zSubgro p G n :=
  zassenhausSubgroup_antitone p G hle
    (pow_zassenhaus_subgroup (p := p) (G := G) hg)

/-- Commutators lie in the second mod-`p` Zassenhaus term. -/
theorem commutator_subgroup_two (g h : G) :
    ⁅g, h⁆ ∈ zSubgro p G 2 :=
  commutator_dimension_two (ZMod p) G g h


/-- All-index commutator estimate for the mod-`p` Zassenhaus filtration. -/
theorem commutator_add_any {m n : ℕ} {g h : G}
    (hg : g ∈ zSubgro p G m) (hh : h ∈ zSubgro p G n) :
    ⁅g, h⁆ ∈ zSubgro p G (m + n) :=
  commutator_dimension_any (ZMod p) G hg hh

/-- Subgroup form of the all-index Zassenhaus commutator estimate. -/
theorem commutator_subgroup_any {m n : ℕ} :
    ⁅zSubgro p G m, zSubgro p G n⁆ ≤
      zSubgro p G (m + n) :=
  dimension_add_any (ZMod p) G

/-- Positive-index commutator estimate for the mod-`p` Zassenhaus filtration. -/
theorem commutator_subgroup_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {g h : G} (hg : g ∈ zSubgro p G m) (hh : h ∈ zSubgro p G n) :
    ⁅g, h⁆ ∈ zSubgro p G (m + n) :=
  commutator_dimension_add (ZMod p) G hm hn hg hh

/-- Subgroup form of the positive-index Zassenhaus commutator estimate. -/
theorem commutator_zassenhaus_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⁅zSubgro p G m, zSubgro p G n⁆ ≤
      zSubgro p G (m + n) :=
  dimension_subgroup_add (ZMod p) G hm hn

/-- Restricted Zassenhaus commutator law: `[D_n, D_n] ≤ D_{n+1}`. -/
theorem commutator_subgroup_self (n : ℕ) :
    ⁅zSubgro p G n, zSubgro p G n⁆ ≤
      zSubgro p G (n + 1) := by
  cases n with
  | zero =>
      rw [zassenhaus_one_top]
      exact le_top
  | succ k =>
      exact
        (commutator_zassenhaus_add p G
          (by omega : k + 1 ≠ 0) (by omega : k + 1 ≠ 0)).trans
          (zassenhausSubgroup_antitone p G
            (by omega : (k + 1) + 1 ≤ (k + 1) + (k + 1)))

/-- Elementwise form of the restricted Zassenhaus commutator law. -/
theorem commutator_succ_self {n : ℕ} {g h : G}
    (hg : g ∈ zSubgro p G n) (hh : h ∈ zSubgro p G n) :
    ⁅g, h⁆ ∈ zSubgro p G (n + 1) :=
  commutator_subgroup_self p G n
    (Subgroup.commutator_mem_commutator hg hh)

/-- Predicate form useful for relator-depth bookkeeping: `g` has Zassenhaus depth at
least `n`. -/
def zassenhausDepthLeast (g : G) (n : ℕ) : Prop :=
  g ∈ zSubgro p G n

@[simp] theorem zassenhaus_least {g : G} {n : ℕ} :
    zassenhausDepthLeast p G g n ↔ g ∈ zSubgro p G n := Iff.rfl


/-- Predicate form of the max/intersection rule for Zassenhaus depth. -/
theorem depth_least_max {g : G} {m n : ℕ} :
    zassenhausDepthLeast p G g (max m n) ↔
      zassenhausDepthLeast p G g m ∧ zassenhausDepthLeast p G g n := by
  change g ∈ zSubgro p G (max m n) ↔
    g ∈ zSubgro p G m ∧ g ∈ zSubgro p G n
  rw [← zassenhaus_inf_max (p := p) (G := G) m n]
  simp


/-- Predicate form of the min/join rule for Zassenhaus depth. -/
theorem depth_least_min {g : G} {m n : ℕ} :
    zassenhausDepthLeast p G g (min m n) ↔
      zassenhausDepthLeast p G g m ∨ zassenhausDepthLeast p G g n := by
  rcases le_total m n with hmn | hnm
  · simp only [min_eq_left hmn]
    constructor
    · intro hg; exact Or.inl hg
    · rintro (hg | hg)
      · exact hg
      · exact zassenhausSubgroup_antitone p G hmn hg
  · simp only [min_eq_right hnm]
    constructor
    · intro hg; exact Or.inr hg
    · rintro (hg | hg)
      · exact zassenhausSubgroup_antitone p G hnm hg
      · exact hg

/-- Every element has Zassenhaus depth at least zero. -/
@[simp] theorem depth_least_zero (g : G) :
    zassenhausDepthLeast p G g 0 := by
  change g ∈ zSubgro p G 0
  simp

/-- Every element has Zassenhaus depth at least one. -/
@[simp] theorem depth_least_one (g : G) :
    zassenhausDepthLeast p G g 1 := by
  change g ∈ zSubgro p G 1
  simp

/-- Homomorphisms preserve Zassenhaus depth certificates. -/
theorem zassenhaus_depth {H : Type*} [Group H] (φ : G →* H)
    {g : G} {n : ℕ} (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p H (φ g) n := by
  change φ g ∈ zSubgro p H n
  exact zassenhaus_subgroup_comap p G φ n hg

/-- An isomorphism reflects and preserves Zassenhaus depth. -/
theorem zassenhaus_depth_least {H : Type*} [Group H] (e : G ≃* H)
    {g : G} {n : ℕ} :
    zassenhausDepthLeast p H (e g) n ↔ zassenhausDepthLeast p G g n := by
  constructor
  · intro h
    have h' := zassenhaus_depth (p := p) (G := H) e.symm.toMonoidHom h
    simpa using h'
  · intro h
    exact zassenhaus_depth (p := p) (G := G) e.toMonoidHom h

/-- Predicate-level product criterion for Zassenhaus depth. -/
theorem depth_least_prod (H : Type*) [Group H]
    (g : G) (h : H) (n : ℕ) :
    zassenhausDepthLeast p (G × H) (g, h) n ↔
      zassenhausDepthLeast p G g n ∧ zassenhausDepthLeast p H h n := by
  change (g, h) ∈ zSubgro p (G × H) n ↔
    g ∈ zSubgro p G n ∧ h ∈ zSubgro p H n
  rw [zassenhausSubgroup_prod (p := p) (G := G) H n, Subgroup.mem_prod]

/-- Left product inclusion preserves Zassenhaus depth, in predicate form. -/
theorem depth_least_inl {H : Type*} [Group H]
    {g : G} {n : ℕ} (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p (G × H) (g, 1) n := by
  exact (depth_least_prod (p := p) (G := G) H g 1 n).2
    ⟨hg, (zSubgro p H n).one_mem⟩

/-- Right product inclusion preserves Zassenhaus depth, in predicate form. -/
theorem depth_least_inr {H : Type*} [Group H]
    {h : H} {n : ℕ} (hh : zassenhausDepthLeast p H h n) :
    zassenhausDepthLeast p (G × H) (1, h) n := by
  exact (depth_least_prod (p := p) (G := G) H 1 h n).2
    ⟨(zSubgro p G n).one_mem, hh⟩

/-- First projection of a product-depth certificate. -/
theorem depth_least_fst {H : Type*} [Group H]
    {x : G × H} {n : ℕ}
    (hx : zassenhausDepthLeast p (G × H) x n) :
    zassenhausDepthLeast p G x.1 n := by
  rcases x with ⟨g, h⟩
  exact ((depth_least_prod (p := p) (G := G) H g h n).1 hx).1

/-- Second projection of a product-depth certificate. -/
theorem depth_least_snd {H : Type*} [Group H]
    {x : G × H} {n : ℕ}
    (hx : zassenhausDepthLeast p (G × H) x n) :
    zassenhausDepthLeast p H x.2 n := by
  rcases x with ⟨g, h⟩
  exact ((depth_least_prod (p := p) (G := G) H g h n).1 hx).2

/-- Swapping product coordinates preserves and reflects Zassenhaus depth. -/
theorem depth_least_swap {H : Type*} [Group H]
    (g : G) (h : H) (n : ℕ) :
    zassenhausDepthLeast p (H × G) (h, g) n ↔
      zassenhausDepthLeast p (G × H) (g, h) n := by
  rw [depth_least_prod (p := p) (G := H) G h g n,
    depth_least_prod (p := p) (G := G) H g h n]
  exact and_comm

/-- Diagonal product depth is exactly the original Zassenhaus depth. -/
theorem depth_least_diag (g : G) (n : ℕ) :
    zassenhausDepthLeast p (G × G) (g, g) n ↔
      zassenhausDepthLeast p G g n := by
  rw [depth_least_prod (p := p) (G := G) G g g n]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- Same-depth certificates are closed under multiplication. -/
theorem depth_least_mul {g h : G} {n : ℕ}
    (hg : zassenhausDepthLeast p G g n) (hh : zassenhausDepthLeast p G h n) :
    zassenhausDepthLeast p G (g * h) n :=
  (zSubgro p G n).mul_mem hg hh


/-- Depth bookkeeping version of the characteristic-`p` power estimate. -/
theorem depth_least_prime [Fact p.Prime] {n : ℕ} {g : G}
    (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G (g ^ p) (n * p) :=
  pow_subgroup_self (p := p) (G := G) hg

/-- Predicate form of the all-index Zassenhaus commutator estimate. -/
theorem zassenhaus_least_any {m n : ℕ} {g h : G}
    (hg : zassenhausDepthLeast p G g m) (hh : zassenhausDepthLeast p G h n) :
    zassenhausDepthLeast p G ⁅g, h⁆ (m + n) :=
  commutator_add_any p G hg hh

/-- Commutators have Zassenhaus depth at least two. -/
theorem depth_least_two (g h : G) :
    zassenhausDepthLeast p G ⁅g, h⁆ 2 :=
  commutator_subgroup_two p G g h

/-- Depth bookkeeping version of the positive-index commutator estimate. -/
theorem depth_least_commutator {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {g h : G} (hg : zassenhausDepthLeast p G g m)
    (hh : zassenhausDepthLeast p G h n) :
    zassenhausDepthLeast p G ⁅g, h⁆ (m + n) :=
  commutator_subgroup_add p G hm hn hg hh

/-- Commuting a positive-depth element with an arbitrary element raises Zassenhaus depth by one. -/
theorem depth_least_any {n : ℕ} (hn : n ≠ 0)
    {g : G} (hg : zassenhausDepthLeast p G g n) (h : G) :
    zassenhausDepthLeast p G ⁅g, h⁆ (n + 1) := by
  have hh : zassenhausDepthLeast p G h 1 := by
    change h ∈ zSubgro p G 1
    simp [zassenhaus_one_top]
  exact depth_least_commutator p G hn (by decide : (1 : ℕ) ≠ 0) hg hh

/-- Commuting an arbitrary element with a positive-depth element raises Zassenhaus depth by one. -/
theorem least_commutator_any {n : ℕ} (hn : n ≠ 0)
    (h : G) {g : G} (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G ⁅h, g⁆ (1 + n) := by
  have hh : zassenhausDepthLeast p G h 1 := by
    change h ∈ zSubgro p G 1
    simp [zassenhaus_one_top]
  exact depth_least_commutator p G (by decide : (1 : ℕ) ≠ 0) hn hh hg



/-- The identity element has every Zassenhaus depth. -/
@[simp] theorem depth_least_elem (n : ℕ) :
    zassenhausDepthLeast p G (1 : G) n :=
  (zSubgro p G n).one_mem

/-- Inverses preserve a Zassenhaus depth certificate. -/
theorem depth_least_inv {g : G} {n : ℕ}
    (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G g⁻¹ n :=
  (zSubgro p G n).inv_mem hg

/-- Conjugation preserves a Zassenhaus depth certificate. -/
theorem zassenhaus_least_conj {g x : G} {n : ℕ}
    (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G (x * g * x⁻¹) n := by
  exact (zassenhausSubgroup_normal p G n).conj_mem g hg x


/-- Conjugation preserves and reflects Zassenhaus depth. -/
theorem depth_least_conj {g x : G} {n : ℕ} :
    zassenhausDepthLeast p G (x * g * x⁻¹) n ↔ zassenhausDepthLeast p G g n := by
  constructor
  · intro h
    have h' := zassenhaus_least_conj (p := p) (G := G)
      (g := x * g * x⁻¹) (x := x⁻¹) h
    simpa [mul_assoc] using h'
  · intro h
    exact zassenhaus_least_conj (p := p) (G := G) (x := x) h

/-- Products preserve the minimum of two Zassenhaus depth certificates. -/
theorem zassenhaus_least_min {g h : G} {m n : ℕ}
    (hg : zassenhausDepthLeast p G g m) (hh : zassenhausDepthLeast p G h n) :
    zassenhausDepthLeast p G (g * h) (min m n) := by
  have hg' : g ∈ zSubgro p G (min m n) :=
    zassenhausSubgroup_antitone p G (Nat.min_le_left m n) hg
  have hh' : h ∈ zSubgro p G (min m n) :=
    zassenhausSubgroup_antitone p G (Nat.min_le_right m n) hh
  exact (zSubgro p G (min m n)).mul_mem hg' hh'

/-- Quotients of same-depth elements preserve Zassenhaus depth. -/
theorem depth_least_div {g h : G} {n : ℕ}
    (hg : zassenhausDepthLeast p G g n) (hh : zassenhausDepthLeast p G h n) :
    zassenhausDepthLeast p G (g / h) n :=
  (zSubgro p G n).div_mem hg hh

/-- Integer powers preserve a fixed Zassenhaus depth certificate. -/
theorem depth_least_zpow {g : G} {n : ℕ} (k : ℤ)
    (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G (g ^ k) n :=
  (zSubgro p G n).zpow_mem hg k

/-- Ordinary natural powers preserve any fixed Zassenhaus depth certificate. -/
theorem depth_least_pow {g : G} {n k : ℕ}
    (hg : zassenhausDepthLeast p G g n) :
    zassenhausDepthLeast p G (g ^ k) n := by
  induction k with
  | zero => simp [zassenhausDepthLeast]
  | succ k ih =>
      simpa [pow_succ] using
        (zSubgro p G n).mul_mem ih hg

/-- Depth-at-least is antitone in the requested depth: deeper membership implies
shallower membership. -/
theorem depth_least {g : G} {m n : ℕ} (hmn : m ≤ n)
    (hg : zassenhausDepthLeast p G g n) : zassenhausDepthLeast p G g m := by
  exact zassenhausSubgroup_antitone p G hmn hg



/-- The quotient of a group by its `n`th Zassenhaus term. -/
abbrev zQuot (n : ℕ) : Type _ := G ⧸ zSubgro p G n

/-- The zeroth Zassenhaus quotient is trivial. -/
theorem zQuot.subsingleton_zero :
    Subsingleton (zQuot p G 0) := by
  change Subsingleton (G ⧸ zSubgro p G 0)
  rw [zassenhaus_subgroup_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- The first Zassenhaus quotient is trivial. -/
theorem zQuot.subsingleton_one :
    Subsingleton (zQuot p G 1) := by
  change Subsingleton (G ⧸ zSubgro p G 1)
  rw [zassenhaus_one_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- Every element of the zeroth Zassenhaus quotient is trivial. -/
theorem zQuot.eq_one_zero (x : zQuot p G 0) : x = 1 := by
  haveI : Subsingleton (zQuot p G 0) :=
    zQuot.subsingleton_zero (p := p) (G := G)
  exact Subsingleton.elim x 1

/-- Every element of the first Zassenhaus quotient is trivial. -/
theorem zQuot.eq_one_one (x : zQuot p G 1) : x = 1 := by
  haveI : Subsingleton (zQuot p G 1) :=
    zQuot.subsingleton_one (p := p) (G := G)
  exact Subsingleton.elim x 1

/-- The quotient of a product by its `n`th Zassenhaus term is canonically the product
of the two `n`th Zassenhaus quotients. -/
noncomputable def zQuot.prodEquiv (H : Type*) [Group H] (n : ℕ) :
    zQuot p (G × H) n ≃*
      (zQuot p G n × zQuot p H n) :=
  (QuotientGroup.quotientMulEquivOfEq (zassenhausSubgroup_prod p (G := G) H n)).trans
    (Towers.quotientProdEquiv (zSubgro p G n) (zSubgro p H n))

@[simp] theorem zQuot.prodEquiv_mk (H : Type*) [Group H] (n : ℕ)
    (g : G) (h : H) :
    zQuot.prodEquiv p G H n
        (QuotientGroup.mk' (zSubgro p (G × H) n) (g, h)) =
      (QuotientGroup.mk' (zSubgro p G n) g,
        QuotientGroup.mk' (zSubgro p H n) h) := rfl


@[simp] theorem zQuot.prod_equiv_symmmk (H : Type*) [Group H] (n : ℕ)
    (g : G) (h : H) :
    (zQuot.prodEquiv p G H n).symm
        (QuotientGroup.mk' (zSubgro p G n) g,
          QuotientGroup.mk' (zSubgro p H n) h) =
      QuotientGroup.mk' (zSubgro p (G × H) n) (g, h) := by
  apply (zQuot.prodEquiv p G H n).injective
  simp only [MulEquiv.apply_symm_apply]
  change (QuotientGroup.mk' (zSubgro p G n) g,
      QuotientGroup.mk' (zSubgro p H n) h) = _
  rw [zQuot.prodEquiv_mk]

/-- Cardinality formula for Zassenhaus quotients of products, stated with `Nat.card`. -/
theorem nat_quotient_prod (H : Type*) [Group H] (n : ℕ) :
    Nat.card (zQuot p (G × H) n) =
      Nat.card (zQuot p G n) * Nat.card (zQuot p H n) := by
  rw [Nat.card_congr (zQuot.prodEquiv p G H n).toEquiv, Nat.card_prod]

/-- The map induced by a group homomorphism on the `n`th Zassenhaus quotient. -/
noncomputable def zQuot.map {H : Type*} [Group H] (φ : G →* H) (n : ℕ) :
    zQuot p G n →* zQuot p H n :=
  DFilt.quotientMap (zassenhausFiltration_preserves p G φ) n

/-- Maps into the zeroth Zassenhaus quotient are trivial. -/
theorem zQuot.map_applyeq_onezero {H : Type*} [Group H]
    (φ : G →* H) (x : zQuot p G 0) :
    zQuot.map p G φ 0 x = 1 :=
  zQuot.eq_one_zero (p := p) (G := H) _

/-- At level zero, the induced map on Zassenhaus quotients is the trivial hom. -/
theorem zQuot.map_eq_onezero {H : Type*} [Group H]
    (φ : G →* H) :
    zQuot.map p G φ 0 = 1 := by
  ext x
  exact zQuot.map_applyeq_onezero (p := p) (G := G) φ x

/-- The kernel of the level-zero Zassenhaus quotient map is the whole source. -/
theorem zQuot.ker_mapzero_eqtop {H : Type*} [Group H]
    (φ : G →* H) :
    MonoidHom.ker (zQuot.map p G φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, zQuot.map_applyeq_onezero (p := p) (G := G) φ x]

/-- The range of the level-zero Zassenhaus quotient map is the bottom subgroup. -/
theorem zQuot.range_mapzero_eqbot {H : Type*} [Group H]
    (φ : G →* H) :
    (zQuot.map p G φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [zQuot.map_applyeq_onezero (p := p) (G := G) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

/-- Maps into the first Zassenhaus quotient are trivial. -/
theorem zQuot.map_applyeq_oneone {H : Type*} [Group H]
    (φ : G →* H) (x : zQuot p G 1) :
    zQuot.map p G φ 1 x = 1 :=
  zQuot.eq_one_one (p := p) (G := H) _

/-- At level one, the induced map on Zassenhaus quotients is the trivial hom. -/
theorem zQuot.map_eq_oneone {H : Type*} [Group H]
    (φ : G →* H) :
    zQuot.map p G φ 1 = 1 := by
  ext x
  exact zQuot.map_applyeq_oneone (p := p) (G := G) φ x

/-- The kernel of the level-one Zassenhaus quotient map is the whole source. -/
theorem zQuot.ker_mapone_eqtop {H : Type*} [Group H]
    (φ : G →* H) :
    MonoidHom.ker (zQuot.map p G φ 1) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, zQuot.map_applyeq_oneone (p := p) (G := G) φ x]

/-- The range of the level-one Zassenhaus quotient map is the bottom subgroup. -/
theorem zQuot.range_mapone_eqbot {H : Type*} [Group H]
    (φ : G →* H) :
    (zQuot.map p G φ 1).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [zQuot.map_applyeq_oneone (p := p) (G := G) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem zQuot.map_mk {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (g : G) :
    zQuot.map p G φ n (QuotientGroup.mk' (zSubgro p G n) g) =
      QuotientGroup.mk' (zSubgro p H n) (φ g) := rfl

@[simp] theorem zQuot.map_id (n : ℕ) :
    zQuot.map p G (MonoidHom.id G) n =
      MonoidHom.id (zQuot p G n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem zQuot.map_comp {H K : Type*} [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zQuot.map p G (ψ.comp φ) n =
      (zQuot.map p H ψ n).comp (zQuot.map p G φ n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl




/-- The first projection after the product equivalence on Zassenhaus quotients is the
map induced by the first projection of groups. -/
@[simp] theorem zQuot.prodEquiv_fst (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp (zQuot.prodEquiv p G H n).toMonoidHom =
      zQuot.map p (G × H) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  cases x
  rfl

/-- The second projection after the product equivalence on Zassenhaus quotients is the
map induced by the second projection of groups. -/
@[simp] theorem zQuot.prodEquiv_snd (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp (zQuot.prodEquiv p G H n).toMonoidHom =
      zQuot.map p (G × H) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  cases x
  rfl


/-- Product equivalence on Zassenhaus quotients is pointwise the pair of projections. -/
@[simp] theorem zQuot.prodEquiv_apply (H : Type*) [Group H] (n : ℕ)
    (x : zQuot p (G × H) n) :
    zQuot.prodEquiv p G H n x =
      (zQuot.map p (G × H) (MonoidHom.fst G H) n x,
        zQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : zQuot p (G × H) n →*
        zQuot p G n => f x)
      (zQuot.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : zQuot p (G × H) n →*
        zQuot p H n => f x)
      (zQuot.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h

/-- The product equivalence carries the quotient map induced by the left inclusion to
the left inclusion of Zassenhaus quotient factors. -/
@[simp] theorem zQuot.prodEquiv_inl (H : Type*) [Group H] (n : ℕ) :
    (zQuot.prodEquiv p G H n).toMonoidHom.comp
        (zQuot.map p G (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- The product equivalence carries the quotient map induced by the right inclusion to
the right inclusion of Zassenhaus quotient factors. -/
@[simp] theorem zQuot.prodEquiv_inr (H : Type*) [Group H] (n : ℕ) :
    (zQuot.prodEquiv p G H n).toMonoidHom.comp
        (zQuot.map p H (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl


/-- The inverse product equivalence sends a left-factor Zassenhaus quotient element to
the map induced by the left product inclusion. -/
@[simp] theorem zQuot.prod_equiv_symminl (H : Type*) [Group H] (n : ℕ)
    (x : zQuot p G n) :
    (zQuot.prodEquiv p G H n).symm (x, 1) =
      zQuot.map p G (MonoidHom.inl G H) n x := by
  apply (zQuot.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : zQuot p G n →*
      (zQuot p G n × zQuot p H n) => f x)
    (zQuot.prodEquiv_inl (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor Zassenhaus quotient element to
the map induced by the right product inclusion. -/
@[simp] theorem zQuot.prod_equiv_symminr (H : Type*) [Group H] (n : ℕ)
    (x : zQuot p H n) :
    (zQuot.prodEquiv p G H n).symm (1, x) =
      zQuot.map p H (MonoidHom.inr G H) n x := by
  apply (zQuot.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : zQuot p H n →*
      (zQuot p G n × zQuot p H n) => f x)
    (zQuot.prodEquiv_inr (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- Every product Zassenhaus quotient element splits into projected inclusion components. -/
theorem zQuot.eq_inl_mulinr (H : Type*) [Group H] (n : ℕ)
    (x : zQuot p (G × H) n) :
    x = zQuot.map p G (MonoidHom.inl G H) n
          (zQuot.map p (G × H) (MonoidHom.fst G H) n x) *
        zQuot.map p H (MonoidHom.inr G H) n
          (zQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
  let e := zQuot.prodEquiv p G H n
  have hf : (e x).1 = zQuot.map p (G × H) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : zQuot p (G × H) n →*
        zQuot p G n => f x)
      (zQuot.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = zQuot.map p (G × H) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : zQuot p (G × H) n →*
        zQuot p H n => f x)
      (zQuot.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = zQuot.map p G (MonoidHom.inl G H) n
          (zQuot.map p (G × H) (MonoidHom.fst G H) n x) *
        zQuot.map p H (MonoidHom.inr G H) n
          (zQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]

/-- Left- and right-inclusion images commute in a product Zassenhaus quotient. -/
theorem zQuot.map_inlmul_inrcomm (H : Type*) [Group H] (n : ℕ)
    (x : zQuot p G n) (y : zQuot p H n) :
    zQuot.map p G (MonoidHom.inl G H) n x *
        zQuot.map p H (MonoidHom.inr G H) n y =
      zQuot.map p H (MonoidHom.inr G H) n y *
        zQuot.map p G (MonoidHom.inl G H) n x := by
  let e := zQuot.prodEquiv p G H n
  apply e.injective
  have hx : e (zQuot.map p G (MonoidHom.inl G H) n x) = (x, 1) := by
    have h := congrArg (fun f : zQuot p G n →*
        (zQuot p G n × zQuot p H n) => f x)
      (zQuot.prodEquiv_inl (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (zQuot.map p H (MonoidHom.inr G H) n y) = (1, y) := by
    have h := congrArg (fun f : zQuot p H n →*
        (zQuot p G n × zQuot p H n) => f y)
      (zQuot.prodEquiv_inr (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first Zassenhaus quotient factor is trivial. -/
@[simp] theorem zQuot.map_fst_compinr (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.fst G H) n).comp
        (zQuot.map p H (MonoidHom.inr G H) n) =
      (1 : zQuot p H n →* zQuot p G n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : zQuot p H n →*
      (zQuot p G n × zQuot p H n) => f x)
    (zQuot.prodEquiv_inr (p := p) (G := G) H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, zQuot.prodEquiv_apply] using hf

/-- Projecting the left-inclusion map to the second Zassenhaus quotient factor is trivial. -/
@[simp] theorem zQuot.map_snd_compinl (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.snd G H) n).comp
        (zQuot.map p G (MonoidHom.inl G H) n) =
      (1 : zQuot p G n →* zQuot p H n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : zQuot p G n →*
      (zQuot p G n × zQuot p H n) => f x)
    (zQuot.prodEquiv_inl (p := p) (G := G) H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, zQuot.prodEquiv_apply] using hs

@[simp] theorem zQuot.map_fst_inrapply (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p H n) :
    zQuot.map p (G × H) (MonoidHom.fst G H) n
        (zQuot.map p H (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : zQuot p H n →*
      zQuot p G n => f x)
    (zQuot.map_fst_compinr (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem zQuot.map_snd_inlapply (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p G n) :
    zQuot.map p (G × H) (MonoidHom.snd G H) n
        (zQuot.map p G (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : zQuot p G n →*
      zQuot p H n => f x)
    (zQuot.map_snd_compinl (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product Zassenhaus quotient element lies in the right-inclusion range iff its first
projection is trivial. -/
theorem zQuot.memrange_inriffmap_fsteqone (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    x ∈ (zQuot.map p H (MonoidHom.inr G H) n).range ↔
      zQuot.map p (G × H) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : zQuot p H n →*
        zQuot p G n => f y)
      (zQuot.map_fst_compinr (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zQuot.map p (G × H) (MonoidHom.snd G H) n x, ?_⟩
    have h := zQuot.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product Zassenhaus quotient element lies in the left-inclusion range iff its second
projection is trivial. -/
theorem zQuot.memrange_inliffmap_sndeqone (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    x ∈ (zQuot.map p G (MonoidHom.inl G H) n).range ↔
      zQuot.map p (G × H) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : zQuot p G n →*
        zQuot p H n => f y)
      (zQuot.map_snd_compinl (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zQuot.map p (G × H) (MonoidHom.fst G H) n x, ?_⟩
    have h := zQuot.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product Zassenhaus quotient is the
right-inclusion range. -/
theorem zQuot.kermap_fsteq_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.fst G H) n).ker =
      (zQuot.map p H (MonoidHom.inr G H) n).range := by
  ext x
  exact (zQuot.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).symm

/-- The kernel of the second projection on a product Zassenhaus quotient is the
left-inclusion range. -/
theorem zQuot.kermap_sndeq_rangeinl (H : Type*) [Group H]
    (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.snd G H) n).ker =
      (zQuot.map p G (MonoidHom.inl G H) n).range := by
  ext x
  exact (zQuot.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).symm

/-- The left- and right-inclusion ranges in a product Zassenhaus quotient meet only at `1`. -/
theorem zQuot.eqone_memrangeinl_memrangeinr (H : Type*) [Group H]
    (n : ℕ) {x : zQuot p (G × H) n}
    (hxL : x ∈ (zQuot.map p G (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (zQuot.map p H (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (zQuot.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).1 hxR
  have hsnd := (zQuot.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).1 hxL
  have h := zQuot.eq_inl_mulinr (p := p) (G := G) H n x
  simpa [hfst, hsnd] using h

/-- The left- and right-inclusion ranges in a product Zassenhaus quotient are disjoint. -/
theorem zQuot.disjoint_rangeinl_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    Disjoint (zQuot.map p G (MonoidHom.inl G H) n).range
      (zQuot.map p H (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact zQuot.eqone_memrangeinl_memrangeinr
    (p := p) (G := G) H n hxL hxR

/-- Projecting after the left-inclusion map on Zassenhaus quotients is the identity. -/
@[simp] theorem zQuot.map_fst_compinl (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.fst G H) n).comp
        (zQuot.map p G (MonoidHom.inl G H) n) =
      MonoidHom.id (zQuot p G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← zQuot.map_comp (p := p) (G := G) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, zQuot.map_id]

/-- Projecting after the right-inclusion map on Zassenhaus quotients is the identity. -/
@[simp] theorem zQuot.map_snd_compinr (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.snd G H) n).comp
        (zQuot.map p H (MonoidHom.inr G H) n) =
      MonoidHom.id (zQuot p H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← zQuot.map_comp (p := p) (G := H) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, zQuot.map_id]


/-- The Zassenhaus quotient map induced by the first product projection is surjective. -/
theorem zQuot.map_fst_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zQuot.map p (G × H) (MonoidHom.fst G H) n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  refine ⟨QuotientGroup.mk' (zSubgro p (G × H) n) (g, 1), ?_⟩
  rfl

/-- The Zassenhaus quotient map induced by the second product projection is surjective. -/
theorem zQuot.map_snd_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zQuot.map p (G × H) (MonoidHom.snd G H) n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  refine ⟨QuotientGroup.mk' (zSubgro p (G × H) n) (1, h), ?_⟩
  rfl

/-- The first projection map on product Zassenhaus quotients has full range. -/
theorem zQuot.range_mapfst_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zQuot.map_fst_surjective (p := p) (G := G) H n)

/-- The second projection map on product Zassenhaus quotients has full range. -/
theorem zQuot.range_mapsnd_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p (G × H) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zQuot.map_snd_surjective (p := p) (G := G) H n)

/-- The Zassenhaus quotient map induced by the left product inclusion is injective. -/
theorem zQuot.map_inl_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zQuot.map p G (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (zQuot.map p (G × H) (MonoidHom.fst G H) n)
      (zQuot.map p G (MonoidHom.inl G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  exact hleft.injective

/-- The Zassenhaus quotient map induced by the right product inclusion is injective. -/
theorem zQuot.map_inr_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zQuot.map p H (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (zQuot.map p (G × H) (MonoidHom.snd G H) n)
      (zQuot.map p H (MonoidHom.inr G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro h
    rfl
  exact hleft.injective

/-- The left product-inclusion map on Zassenhaus quotients has trivial kernel. -/
theorem zQuot.ker_mapinl_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p G (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zQuot.map_inl_injective (p := p) (G := G) H n)

/-- The right product-inclusion map on Zassenhaus quotients has trivial kernel. -/
theorem zQuot.ker_mapinr_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zQuot.map p H (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zQuot.map_inr_injective (p := p) (G := G) H n)

/-- Naturality of the Zassenhaus-quotient product equivalence. -/
theorem zQuot.prodEquiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zQuot.prodEquiv p G₂ H₂ n).toMonoidHom.comp
        (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (zQuot.map p G₁ f n)
        (zQuot.map p H₁ g n)).comp
        (zQuot.prodEquiv p G₁ H₁ n).toMonoidHom := by
  ext x <;> rfl

/-- Associator followed by its inverse is identity on Zassenhaus quotients. -/
@[simp] theorem zQuot.mapprod_assocsymm_prodassoc
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    zQuot.map p (G × H × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (zQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zQuot.map_comp (p := p) (G := (G × H) × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zQuot p ((G × H) × K) n →*
      zQuot p ((G × H) × K) n => f x)
    (zQuot.map_id (p := p) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on Zassenhaus quotients. -/
@[simp] theorem zQuot.mapprod_assocprod_assocsymm
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p (G × H × K) n) :
    zQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (zQuot.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zQuot.map_comp (p := p) (G := G × H × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zQuot p (G × H × K) n →*
      zQuot p (G × H × K) n => f x)
    (zQuot.map_id (p := p) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Associativity coherence for Zassenhaus quotient product equivalences. -/
theorem zQuot.prod_equiv_assocnatural
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap (MonoidHom.id (zQuot p G n))
        (zQuot.prodEquiv p H K n).toMonoidHom).comp
      (zQuot.prodEquiv p G (H × K) n).toMonoidHom).comp
        (zQuot.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        (zQuot p G n × zQuot p H n) ×
          zQuot p K n ≃*
        zQuot p G n × zQuot p H n ×
          zQuot p K n).toMonoidHom).comp
      ((MonoidHom.prodMap (zQuot.prodEquiv p G H n).toMonoidHom
        (MonoidHom.id (zQuot p K n))).comp
        (zQuot.prodEquiv p (G × H) K n).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro ghk
  rfl

/-- Pointwise associativity coherence for Zassenhaus quotient product equivalences. -/
@[simp] theorem zQuot.prod_equiv_assocapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    (MonoidHom.prodMap (MonoidHom.id (zQuot p G n))
        (zQuot.prodEquiv p H K n).toMonoidHom)
      (zQuot.prodEquiv p G (H × K) n
        (zQuot.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        (zQuot p G n × zQuot p H n) ×
          zQuot p K n ≃*
        zQuot p G n × zQuot p H n ×
          zQuot p K n)
        ((MonoidHom.prodMap (zQuot.prodEquiv p G H n).toMonoidHom
          (MonoidHom.id (zQuot p K n)))
          (zQuot.prodEquiv p (G × H) K n x)) := by
  have h := congrArg (fun f : zQuot p ((G × H) × K) n →*
      (zQuot p G n × zQuot p H n ×
        zQuot p K n) => f x)
    (zQuot.prod_equiv_assocnatural (p := p) (G := G) H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Inverse-form associativity coherence for Zassenhaus quotient product equivalences. -/
@[simp] theorem zQuot.prod_equivassoc_symmapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (a : zQuot p G n) (b : zQuot p H n)
    (c : zQuot p K n) :
    zQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((zQuot.prodEquiv p (G × H) K n).symm
        ((zQuot.prodEquiv p G H n).symm (a, b), c)) =
      (zQuot.prodEquiv p G (H × K) n).symm
        (a, (zQuot.prodEquiv p H K n).symm (b, c)) := by
  apply (zQuot.prodEquiv p G (H × K) n).injective
  let x : zQuot p ((G × H) × K) n :=
    (zQuot.prodEquiv p (G × H) K n).symm
      ((zQuot.prodEquiv p G H n).symm (a, b), c)
  have h := zQuot.prod_equiv_assocapply (p := p) (G := G) H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (zQuot.prodEquiv p H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Pointwise form of naturality for Zassenhaus quotient product equivalences. -/
@[simp] theorem zQuot.prod_equiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zQuot p (G₁ × H₁) n) :
    zQuot.prodEquiv p G₂ H₂ n
        (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      (zQuot.map p G₁ f n
          (zQuot.prodEquiv p G₁ H₁ n x).1,
        zQuot.map p H₁ g n
          (zQuot.prodEquiv p G₁ H₁ n x).2) := by
  have h := congrArg (fun F : zQuot p (G₁ × H₁) n →*
      (zQuot p G₂ n × zQuot p H₂ n) => F x)
    (zQuot.prodEquiv_naturality (p := p) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality on inverse product representatives for Zassenhaus quotients. -/
@[simp] theorem zQuot.prod_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : zQuot p G₁ n × zQuot p H₁ n) :
    zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zQuot.prodEquiv p G₁ H₁ n).symm y) =
      (zQuot.prodEquiv p G₂ H₂ n).symm
        (zQuot.map p G₁ f n y.1,
          zQuot.map p H₁ g n y.2) := by
  apply (zQuot.prodEquiv p G₂ H₂ n).injective
  have h := zQuot.prod_equiv_naturalapply (p := p) f g n
    ((zQuot.prodEquiv p G₁ H₁ n).symm y)
  simpa using h

/-- Product-commuting the factors is compatible with the Zassenhaus-quotient product equivalence. -/
theorem zQuot.prod_equiv_swapnatural (H : Type*) [Group H] (n : ℕ) :
    (zQuot.prodEquiv p H G n).toMonoidHom.comp
        (zQuot.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm : zQuot p G n × zQuot p H n ≃*
          zQuot p H n × zQuot p G n).toMonoidHom).comp
        (zQuot.prodEquiv p G H n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro gh
  rfl

/-- Applying the product-commuting map twice on Zassenhaus quotients is the identity. -/
@[simp] theorem zQuot.map_prodcomm_prodcomm (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.map p (H × G)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zQuot.map_comp (p := p) (G := G × H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zQuot p (G × H) n →*
      zQuot p (G × H) n => f x)
    (zQuot.map_id (p := p) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Pointwise form of swap-naturality for Zassenhaus quotient product equivalences. -/
@[simp] theorem zQuot.prod_equiv_swapapply (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodEquiv p H G n
        (zQuot.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((zQuot.prodEquiv p G H n x).2,
        (zQuot.prodEquiv p G H n x).1) := by
  have h := congrArg (fun f : zQuot p (G × H) n →*
      (zQuot p H n × zQuot p G n) => f x)
    (zQuot.prod_equiv_swapnatural (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h

/-- Representative equality criterion for induced maps on Zassenhaus quotients. -/
theorem zQuot.map_mkeq_mkiff {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x y : G) :
    zQuot.map p G φ n
        (QuotientGroup.mk' (zSubgro p G n) x) =
      zQuot.map p G φ n
        (QuotientGroup.mk' (zSubgro p G n) y) ↔
      x⁻¹ * y ∈ (zSubgro p H n).comap φ := by
  change (φ x : zQuot p H n) =
      (φ y : zQuot p H n) ↔ _
  rw [QuotientGroup.eq]
  have hmap : (φ x)⁻¹ * φ y = φ (x⁻¹ * y) := by simp
  rw [hmap]
  rfl

/-- Representative kernel criterion for induced maps on Zassenhaus quotients. -/
@[simp] theorem zQuot.map_mkeq_oneiff {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : G) :
    zQuot.map p G φ n
        (QuotientGroup.mk' (zSubgro p G n) x) = 1 ↔
      x ∈ (zSubgro p H n).comap φ := by
  change (φ x : zQuot p H n) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff (N := zSubgro p H n) (φ x)]
  rfl

/-- Kernel of the induced map on a Zassenhaus quotient, as the image of the
preimage of the target term in the source quotient. -/
theorem zQuot.ker_mapeq_mapcomap {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    MonoidHom.ker (zQuot.map p G φ n) =
      ((zSubgro p H n).comap φ).map
        (QuotientGroup.mk' (zSubgro p G n)) :=
  DFilt.ker_quotient_comap
    (zassenhausFiltration_preserves p G φ) n

/-- The kernel of a Zassenhaus quotient map as a quotient of the preimage term. -/
noncomputable def zQuot.kernelEquiv {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    ((zSubgro p H n).comap φ) ⧸
      ((zSubgro p G n).subgroupOf ((zSubgro p H n).comap φ)) ≃*
        MonoidHom.ker (zQuot.map p G φ n) :=
  DFilt.quotientKernelEquiv (zassenhausFiltration_preserves p G φ) n

/-- A surjective group homomorphism induces surjective maps on Zassenhaus quotients. -/
theorem zQuot.map_surjective {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) (n : ℕ) :
    Function.Surjective (zQuot.map p G φ n) :=
  DFilt.quotientMap_surjective (zassenhausFiltration_preserves p G φ) hs n

/-- Range form of surjectivity on Zassenhaus quotients. -/
theorem zQuot.map_rangeeq_topsurj {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) (n : ℕ) :
    (zQuot.map p G φ n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (zQuot.map_surjective p G φ hs n)

/-- An induced map on Zassenhaus quotients is injective when the target term has no
extra preimage beyond the source term. -/
theorem zQuot.map_inj_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ}
    (hker : (zSubgro p H n).comap φ ≤ zSubgro p G n) :
    Function.Injective (zQuot.map p G φ n) :=
  DFilt.quotient_comap
    (zassenhausFiltration_preserves p G φ) hker

/-- Injectivity of the induced map on a Zassenhaus quotient is exactly the
absence of extra preimages of the target Zassenhaus term. -/
theorem zQuot.map_injiff_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ} :
    Function.Injective (zQuot.map p G φ n) ↔
      (zSubgro p H n).comap φ ≤ zSubgro p G n :=
  DFilt.quotient_injective_comap
    (zassenhausFiltration_preserves p G φ)

/-- For a surjective homomorphism, bijectivity on a Zassenhaus quotient is
equivalent to the exact preimage condition for the target term. -/
theorem zQuot.mapbij_iffcomap_lesurj {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) {n : ℕ} :
    Function.Bijective (zQuot.map p G φ n) ↔
      (zSubgro p H n).comap φ ≤ zSubgro p G n :=
  DFilt.quotient_bijective_comap
    (zassenhausFiltration_preserves p G φ) hs


/-- For any termwise-onto map of Zassenhaus filtrations, injectivity on a quotient
is equivalent to kernel containment in the source term. -/
theorem zQuot.mapinj_iffker_lemapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ} :
    Function.Injective (zQuot.map p G φ n) ↔
      φ.ker ≤ zSubgro p G n := by
  simpa [zQuot.map] using
    DFilt.injective_maps_onto honto (n := n)

/-- For any termwise-onto map of Zassenhaus filtrations, bijectivity on a quotient
is equivalent to kernel containment in the source term. -/
theorem zQuot.mapbij_iffker_lemapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ} :
    Function.Bijective (zQuot.map p G φ n) ↔
      φ.ker ≤ zSubgro p G n := by
  simpa [zQuot.map] using
    DFilt.bijective_ker_onto honto (n := n)

/-- A termwise-onto map of Zassenhaus filtrations whose kernel lies in the source term
induces an equivalence on Zassenhaus quotients. -/
noncomputable def zQuot.equiv_mapsonto_kerle {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) :
    zQuot p G n ≃* zQuot p H n :=
  DFilt.quotientMapsKer honto hker

@[simp] theorem zQuot.equivmaps_ontoker_leapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (x : zQuot p G n) :
    zQuot.equiv_mapsonto_kerle p G φ honto hker x =
      zQuot.map p G φ n x := rfl

@[simp] theorem zQuot.equivmaps_ontoker_lemonoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) :
    (zQuot.equiv_mapsonto_kerle p G φ honto hker).toMonoidHom =
      zQuot.map p G φ n := rfl

/-- Inverse-characterization for Zassenhaus quotient equivalences from termwise-onto maps
with kernel contained in the source term. -/
theorem zQuot.equivmaps_ontokerle_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n)
    (y : zQuot p H n) (x : zQuot p G n) :
    (zQuot.equiv_mapsonto_kerle p G φ honto hker).symm y = x ↔
      y = zQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on all earlier
Zassenhaus quotients. -/
noncomputable def zQuot.equivmaps_ontoker_lele {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n) :
    zQuot p G m ≃* zQuot p H m :=
  DFilt.quotientOntoKer honto hker hmn

@[simp] theorem zQuot.equivmaps_ontoker_leleapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (x : zQuot p G m) :
    zQuot.equivmaps_ontoker_lele p G φ honto hker hmn x =
      zQuot.map p G φ m x := rfl

@[simp] theorem zQuot.equivmaps_ontokerle_lemonoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n) :
    (zQuot.equivmaps_ontoker_lele p G φ honto hker hmn).toMonoidHom =
      zQuot.map p G φ m := rfl

/-- Inverse-characterization for monotone-kernel Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_symma {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (y : zQuot p H m) (x : zQuot p G m) :
    (zQuot.equivmaps_ontoker_lele p G φ honto hker hmn).symm y = x ↔
      y = zQuot.map p G φ m x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- For a split epimorphism, injectivity on a Zassenhaus quotient is equivalent to
its ordinary kernel lying in the source Zassenhaus term. -/
theorem zQuot.mapinj_iffker_lerightinv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (zQuot.map p G φ n) ↔
      φ.ker ≤ zSubgro p G n :=
  DFilt.injective_ker_inverse
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ

/-- For a split epimorphism, bijectivity on a Zassenhaus quotient is equivalent to
its ordinary kernel lying in the source Zassenhaus term. -/
theorem zQuot.mapbij_iffker_lerightinv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (zQuot.map p G φ n) ↔
      φ.ker ≤ zSubgro p G n :=
  DFilt.bijective_ker_inverse
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ


/-- A split epimorphism that is also injective induces bijections on Zassenhaus quotients. -/
theorem zQuot.map_bijright_invinj {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (zQuot.map p G φ n) := by
  simpa [zQuot.map] using
    DFilt.quotient_bijective_injective
      (filtration_maps_inverse p G φ σ hσ) hinj n

/-- A split epimorphism whose kernel lies in `Dₙ` gives an equivalence on `n`th
Zassenhaus quotients. -/
noncomputable def zQuot.rightInverseEquiv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) :
    zQuot p G n ≃* zQuot p H n :=
  MulEquiv.ofBijective (zQuot.map p G φ n)
    ((zQuot.mapbij_iffker_lerightinv p G φ σ hσ).2 hker)

@[simp] theorem zQuot.equiv_right_invapply {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) (x : zQuot p G n) :
    zQuot.rightInverseEquiv p G φ σ hσ hker x =
      zQuot.map p G φ n x := rfl


@[simp] theorem zQuot.equiv_rightinv_monoidhom
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n) :
    (zQuot.rightInverseEquiv p G φ σ hσ hker).toMonoidHom =
      zQuot.map p G φ n := rfl

/-- Inverse-characterization for the kernel-contained split-epi Zassenhaus quotient equivalence. -/
theorem zQuot.equivright_invsymm_applyeq
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G n)
    (y : zQuot p H n) (x : zQuot p G n) :
    (zQuot.rightInverseEquiv p G φ σ hσ hker).symm y = x ↔
      y = zQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl



/-- A multiplicative equivalence carries each Zassenhaus term onto the corresponding term. -/
theorem zassenhaus_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zSubgro p G n).map e.toMonoidHom = zSubgro p H n := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact zassenhaus_subgroup_comap p G e.toMonoidHom n
  · intro h hh
    refine ⟨e.symm h, ?_, ?_⟩
    · have hinv := zassenhaus_subgroup_comap p H e.symm.toMonoidHom n hh
      simpa using hinv
    · simp

/-- A multiplicative equivalence pulls back each Zassenhaus term to the corresponding term. -/
theorem zassenhaus_comap_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zSubgro p H n).comap e.toMonoidHom = zSubgro p G n := by
  apply le_antisymm
  · intro g hg
    have h := zassenhaus_subgroup_comap p H e.symm.toMonoidHom n hg
    simpa using h
  · exact zassenhaus_subgroup_comap p G e.toMonoidHom n

/-- Membership in a Zassenhaus term is invariant under a group equivalence.  This
non-simp iff is a compact way to transport depth hypotheses without unfolding
the term map/comap statements. -/
theorem zassenhaus_subgroup_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (g : G) :
    e g ∈ zSubgro p H n ↔ g ∈ zSubgro p G n := by
  constructor
  · intro hg
    have h := zassenhaus_subgroup_comap p H e.symm.toMonoidHom n hg
    simpa using h
  · intro hg
    exact zassenhaus_subgroup_comap p G e.toMonoidHom n hg

/-- Symmetric form of `zassenhaus_subgroup_equiv`, useful when the element
already lives in the target group. -/
theorem zassenhaus_equiv_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (h : H) :
    e.symm h ∈ zSubgro p G n ↔ h ∈ zSubgro p H n := by
  simpa using (zassenhaus_subgroup_equiv (p := p) (G := H) e.symm n h)

/-- Symmetric predicate-level transport of Zassenhaus depth across a group equivalence. -/
theorem depth_least_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (h : H) :
    zassenhausDepthLeast p G (e.symm h) n ↔ zassenhausDepthLeast p H h n := by
  exact zassenhaus_equiv_symm (p := p) (G := G) e n h

/-- A multiplicative equivalence induces equivalences on Zassenhaus quotients. -/
noncomputable def zQuot.congr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    zQuot p G n ≃* zQuot p H n :=
  QuotientGroup.congr (zSubgro p G n) (zSubgro p H n) e
    (zassenhaus_equiv p G e n)

@[simp] theorem zQuot.congr_mk {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (g : G) :
    zQuot.congr p G e n
        (QuotientGroup.mk' (zSubgro p G n) g) =
      QuotientGroup.mk' (zSubgro p H n) (e g) := rfl

@[simp] theorem zQuot.congr_monoid_hom {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zQuot.congr p G e n).toMonoidHom =
      zQuot.map p G e.toMonoidHom n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- The quotient map induced by a group equivalence is bijective. -/
theorem zQuot.map_bijective_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Function.Bijective (zQuot.map p G e.toMonoidHom n) := by
  simpa [zQuot.congr_monoid_hom] using
    (zQuot.congr p G e n).bijective

/-- The quotient map induced by a group equivalence is injective. -/
theorem zQuot.map_injective_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Function.Injective (zQuot.map p G e.toMonoidHom n) :=
  (zQuot.map_bijective_equiv (p := p) (G := G) e n).1

/-- The quotient map induced by a group equivalence is surjective. -/
theorem zQuot.map_surjective_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Function.Surjective (zQuot.map p G e.toMonoidHom n) :=
  (zQuot.map_bijective_equiv (p := p) (G := G) e n).2

@[simp] theorem zQuot.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zQuot.congr p G e n).symm =
      zQuot.congr p H e.symm n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl

/-- Inverse-application criterion for congruences of Zassenhaus quotients. -/
theorem zQuot.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (y : zQuot p H n)
    (x : zQuot p G n) :
    (zQuot.congr p G e n).symm y = x ↔
      y = zQuot.congr p G e n x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem zQuot.congr_refl (n : ℕ) :
    zQuot.congr p G (MulEquiv.refl G) n =
      MulEquiv.refl (zQuot p G n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem zQuot.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zQuot.congr p G e n).trans (zQuot.congr p H f n) =
      zQuot.congr p G (e.trans f) n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Automorphisms of `G` act on each Zassenhaus quotient. -/
noncomputable def zQuot.mulAutMap (n : ℕ) :
    MulAut G →* MulAut (zQuot p G n) where
  toFun e := zQuot.congr p G e n
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl

@[simp] theorem zQuot.mul_autmap_applymk (n : ℕ)
    (e : MulAut G) (g : G) :
    zQuot.mulAutMap p G n e
        (QuotientGroup.mk' (zSubgro p G n) g) =
      QuotientGroup.mk' (zSubgro p G n) (e g) := rfl


/-- The first nontrivial Zassenhaus quotient `G/D₂` is abelian. -/
theorem zassenhaus_two_comm (a b : zQuot p G 2) :
    a * b = b * a := by
  refine QuotientGroup.induction_on a ?_
  intro g
  refine QuotientGroup.induction_on b ?_
  intro h
  apply (commutatorElement_eq_one_iff_mul_comm).1
  change ⁅QuotientGroup.mk' (zSubgro p G 2) g,
      QuotientGroup.mk' (zSubgro p G 2) h⁆ = 1
  rw [← map_commutatorElement]
  change QuotientGroup.mk' (zSubgro p G 2) ⁅g, h⁆ = 1
  exact (QuotientGroup.eq_one_iff ⁅g, h⁆).mpr
    (commutator_subgroup_two p G g h)

/-- The first nontrivial Zassenhaus quotient has exponent dividing `p`. -/
@[simp] theorem zassenhaus_pow_one (x : zQuot p G 2) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro g
  change QuotientGroup.mk' (zSubgro p G 2) (g ^ p) = 1
  exact (QuotientGroup.eq_one_iff (g ^ p)).mpr (pow_subgroup_two p G g)

/-- Commutative-group structure on `G/D₂`. -/
instance zQTwo.instCommGroup : CommGroup (zQuot p G 2) :=
  { (inferInstance : Group (zQuot p G 2)) with
    mul_comm := zassenhaus_two_comm p G }

/-- Additive avatar of the first nontrivial Zassenhaus quotient. -/
abbrev zTAdditi : Type _ := Additive (zQuot p G 2)

/-- The additive first quotient is killed by `p`. -/
@[simp] theorem additive_nsmul_zero
    (x : zTAdditi p G) : p • x = 0 := by
  induction x using Additive.rec with
  | ofMul q =>
      change Additive.ofMul (q ^ p) = 0
      simp [zassenhaus_pow_one]

/-- The canonical `ZMod p`-module structure on the additive first Zassenhaus quotient. -/
noncomputable instance zTAdditi.moduleZMod :
    Module (ZMod p) (zTAdditi p G) :=
  AddCommGroup.zmodModule (n := p) (additive_nsmul_zero p G)

/-- Natural scalars on `G/D₂` are represented by powers. -/
@[simp] theorem cast_smul_additive (n : ℕ)
    (q : zQuot p G 2) :
    (n : ZMod p) • (Additive.ofMul q : zTAdditi p G) =
      Additive.ofMul (q ^ n) := by
  rw [Nat.cast_smul_eq_nsmul]
  rfl

/-- Additive map on first Zassenhaus quotients induced by a group homomorphism. -/
def zTAdditi.mapAdd {H : Type*} [Group H] (φ : G →* H) :
    zTAdditi p G →+ zTAdditi p H :=
  (zQuot.map p G φ 2).toAdditive

@[simp] theorem zTAdditi.map_add_mul {H : Type*} [Group H]
    (φ : G →* H) (q : zQuot p G 2) :
    zTAdditi.mapAdd p G φ (Additive.ofMul q) =
      Additive.ofMul (zQuot.map p G φ 2 q) := rfl

/-- Linear map on first Zassenhaus quotients induced by a group homomorphism. -/
noncomputable def zTAdditi.mapLinear {H : Type*} [Group H]
    (φ : G →* H) :
    zTAdditi p G →ₗ[ZMod p] zTAdditi p H :=
  (zTAdditi.mapAdd p G φ).toZModLinearMap p

@[simp] theorem zTAdditi.mapLinear_apply {H : Type*} [Group H]
    (φ : G →* H) (x : zTAdditi p G) :
    zTAdditi.mapLinear p G φ x =
      zTAdditi.mapAdd p G φ x := rfl

@[simp] theorem zTAdditi.mapLinear_id :
    zTAdditi.mapLinear p G (MonoidHom.id G) = LinearMap.id := by
  ext x
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro g
      rfl

/-- A surjective group homomorphism induces a surjective additive map on `G/D₂`. -/
theorem zTAdditi.mapAdd_surjective {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Function.Surjective (zTAdditi.mapAdd p G φ) := by
  intro y
  induction y using Additive.rec with
  | ofMul q =>
      rcases zQuot.map_surjective p G φ hs 2 q with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- A surjective group homomorphism induces a surjective `ZMod p`-linear map on `G/D₂`. -/
theorem zTAdditi.mapLinear_surjective {H : Type*} [Group H]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Function.Surjective (zTAdditi.mapLinear p G φ) := by
  simpa [zTAdditi.mapLinear_apply] using
    zTAdditi.mapAdd_surjective (p := p) (G := G) φ hs

@[simp] theorem zTAdditi.mapLinear_comp {H K : Type*}
    [Group H] [Group K] (φ : G →* H) (ψ : H →* K) :
    zTAdditi.mapLinear p G (ψ.comp φ) =
      (zTAdditi.mapLinear p H ψ).comp
        (zTAdditi.mapLinear p G φ) := by
  ext x
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro g
      rfl

/-- An automorphism of `G` induces a linear automorphism of the first Zassenhaus quotient. -/
noncomputable def zTAdditi.congrLinear (e : MulAut G) :
    zTAdditi p G ≃ₗ[ZMod p] zTAdditi p G :=
{ zTAdditi.mapLinear p G e.toMonoidHom with
  invFun := zTAdditi.mapLinear p G e.symm.toMonoidHom
  left_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        change QuotientGroup.mk' (zSubgro p G 2) (e.symm (e g)) =
          QuotientGroup.mk' (zSubgro p G 2) g
        simp
  right_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        change QuotientGroup.mk' (zSubgro p G 2) (e (e.symm g)) =
          QuotientGroup.mk' (zSubgro p G 2) g
        simp }

/-- The induced linear action of automorphisms on `G/D₂`. -/
noncomputable def zTAdditi.linearAutMap :
    MulAut G →* (zTAdditi p G ≃ₗ[ZMod p]
      zTAdditi p G) where
  toFun e := zTAdditi.congrLinear p G e
  map_one' := by
    ext x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        rfl
  map_mul' e f := by
    ext x
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro g
        rfl

/-- Transition map between Zassenhaus quotients for `m ≤ n` (so `D_n ≤ D_m`). -/
noncomputable def zassenhaus {m n : ℕ} (hmn : m ≤ n) :
    G ⧸ zSubgro p G n →* G ⧸ zSubgro p G m := by
  refine QuotientGroup.lift (zSubgro p G n)
    (QuotientGroup.mk' (zSubgro p G m)) ?_
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mpr ((zassenhausSubgroup_antitone p G hmn) hx)

@[simp] theorem zassenhaus_quotient_mk {m n : ℕ} (hmn : m ≤ n) (g : G) :
    zassenhaus p G hmn
      (QuotientGroup.mk' (zSubgro p G n) g) =
    QuotientGroup.mk' (zSubgro p G m) g := rfl

@[simp] theorem zassenhaus_quotient_refl {n : ℕ} :
    zassenhaus p G (le_rfl : n ≤ n) =
      MonoidHom.id (G ⧸ zSubgro p G n) := by
  ext g
  rfl

@[simp] theorem zassenhaus_quotient_comp {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (zassenhaus p G hlm).comp (zassenhaus p G hmn) =
      zassenhaus p G (le_trans hlm hmn) := by
  ext g
  rfl


/-- The explicit Zassenhaus transition map agrees with the generic transition map of the
bundled descending filtration. -/
theorem zassenhaus_filtration_transition {m n : ℕ} (hmn : m ≤ n) :
    zassenhaus p G hmn =
      DFilt.quotientTransition (zassenhausFiltration p G) hmn := by
  ext g
  rfl

/-- Representative criterion for the kernel of an arbitrary Zassenhaus quotient transition. -/
@[simp] theorem ker_zassenhaus_mk {m n : ℕ}
    (hmn : m ≤ n) (g : G) :
    QuotientGroup.mk' (zSubgro p G n) g ∈
        MonoidHom.ker (zassenhaus p G hmn) ↔
      g ∈ zSubgro p G m := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff g

/-- Kernel of an arbitrary Zassenhaus quotient transition as the image of the target term. -/
theorem zassenhaus_ker {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (zassenhaus p G hmn) =
      (zSubgro p G m).map (QuotientGroup.mk' (zSubgro p G n)) := by
  rw [zassenhaus_filtration_transition]
  exact DFilt.ker_quotient_transition (zassenhausFiltration p G) hmn

/-- Zassenhaus quotient transition maps are surjective. -/
theorem zassenhaus_quotient_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (zassenhaus p G hmn) := by
  rw [zassenhaus_filtration_transition]
  exact DFilt.quotientTransition_surjective (zassenhausFiltration p G) hmn

/-- The deeper Zassenhaus term, viewed as a subgroup of the shallower one. -/
abbrev zTSubgro {m n : ℕ} (hmn : m ≤ n) :
    Subgroup (zSubgro p G m) :=
  DFilt.tSOf (zassenhausFiltration p G) hmn

instance zassenhaus_term_normal {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro p G hmn).Normal :=
  DFilt.term_subgroup_normal (zassenhausFiltration p G) hmn

@[simp] theorem zassenhaus_term {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m) :
    x ∈ zTSubgro p G hmn ↔
      (x : G) ∈ zSubgro p G n := by
  exact DFilt.mem_term_of (zassenhausFiltration p G) hmn x

/-- First-isomorphism-theorem form of an arbitrary Zassenhaus transition kernel. -/
noncomputable def zassenhausTransitionEquiv {m n : ℕ} (hmn : m ≤ n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      MonoidHom.ker (zassenhaus p G hmn) := by
  rw [zassenhaus_filtration_transition]
  exact DFilt.transitionKernelEquiv (zassenhausFiltration p G) hmn

@[simp] theorem transition_mk_coe {m n : ℕ}
    (hmn : m ≤ n) (x : zSubgro p G m) :
    ((zassenhausTransitionEquiv p G hmn
        (QuotientGroup.mk' (zTSubgro p G hmn) x) :
        MonoidHom.ker (zassenhaus p G hmn)) :
        G ⧸ zSubgro p G n) =
      QuotientGroup.mk' (zSubgro p G n) (x : G) := by
  simpa [zassenhausTransitionEquiv,
    zassenhaus_filtration_transition]
    using DFilt.transition_kernel_coe
      (zassenhausFiltration p G) hmn x

/-- Characterize the inverse of the arbitrary Zassenhaus transition-kernel equivalence. -/
theorem transition_quotient_symm {m n : ℕ}
    (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p G hmn))
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (zassenhausTransitionEquiv p G hmn).symm y = x ↔
      y = zassenhausTransitionEquiv p G hmn x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem transition_symm_mk {m n : ℕ}
    (hmn : m ≤ n) (g : G) (hg : g ∈ zSubgro p G m) :
    (zassenhausTransitionEquiv p G hmn).symm
        ⟨QuotientGroup.mk' (zSubgro p G n) g, by
          rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff g).2 hg⟩ =
      QuotientGroup.mk' (zTSubgro p G hmn)
        (⟨g, hg⟩ : zSubgro p G m) := by
  simpa [zassenhausTransitionEquiv,
    zassenhaus_filtration_transition]
    using DFilt.transition_kernel_mk
      (zassenhausFiltration p G) hmn g hg

/-- A homomorphism induces maps on arbitrary concrete Zassenhaus-term quotients. -/
noncomputable def zassenhausTerm {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) →*
      (zSubgro p H m ⧸ zTSubgro p H hmn) :=
  DFilt.termQuotient
    (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn

@[simp] theorem zassenhaus_term_mk {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m) :
    zassenhausTerm p G φ hmn
        (QuotientGroup.mk' (zTSubgro p G hmn) x) =
      QuotientGroup.mk' (zTSubgro p H hmn)
        (DFilt.termMap
          (zassenhausFiltration_preserves (p := p) (G := G) φ) m x) := rfl

@[simp] theorem zassenhaus_term_id {m n : ℕ} (hmn : m ≤ n) :
    zassenhausTerm p G (MonoidHom.id G) hmn =
      MonoidHom.id
        (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  ext x
  rfl

@[simp] theorem zassenhaus_term_comp {H K : Type*}
    [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    zassenhausTerm p G (ψ.comp φ) hmn =
      (zassenhausTerm p H ψ hmn).comp
        (zassenhausTerm p G φ hmn) := by
  ext x
  rfl

/-- A group isomorphism induces an isomorphism on arbitrary Zassenhaus-term quotients. -/
noncomputable def zTQuot.congr {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      (zSubgro p H m ⧸ zTSubgro p H hmn) where
  toFun := zassenhausTerm p G e.toMonoidHom hmn
  invFun := zassenhausTerm p H e.symm.toMonoidHom hmn
  left_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change zassenhausTerm p H e.symm.toMonoidHom hmn
        (zassenhausTerm p G e.toMonoidHom hmn
          (QuotientGroup.mk' (zTSubgro p G hmn) x)) = _
    rw [← MonoidHom.comp_apply]
    rw [← zassenhaus_term_comp p G e.toMonoidHom e.symm.toMonoidHom hmn]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext g; simp
    rw [he]
    simp
  right_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change zassenhausTerm p G e.toMonoidHom hmn
        (zassenhausTerm p H e.symm.toMonoidHom hmn
          (QuotientGroup.mk' (zTSubgro p H hmn) x)) = _
    rw [← MonoidHom.comp_apply]
    rw [← zassenhaus_term_comp p H e.symm.toMonoidHom e.toMonoidHom hmn]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext h; simp
    rw [he]
    simp
  map_mul' x y := map_mul _ x y

@[simp] theorem zTQuot.congr_apply {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) (q) :
    zTQuot.congr p G e hmn q =
      zassenhausTerm p G e.toMonoidHom hmn q := rfl

@[simp] theorem zTQuot.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p G e hmn).symm =
      zTQuot.congr p H e.symm hmn := by
  ext q
  rfl

/-- Inverse-application criterion for congruences of Zassenhaus term quotients. -/
theorem zTQuot.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (zTQuot.congr p G e hmn).symm y = x ↔
      y = zTQuot.congr p G e hmn x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem zTQuot.congr_refl {m n : ℕ} (hmn : m ≤ n) :
    zTQuot.congr p G (MulEquiv.refl G) hmn =
      MulEquiv.refl (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zTQuot.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p G e hmn).trans
        (zTQuot.congr p H f hmn) =
      zTQuot.congr p G (e.trans f) hmn := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zTQuot.congr_mk {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) (x : zSubgro p G m) :
    zTQuot.congr p G e hmn
        (QuotientGroup.mk' (zTSubgro p G hmn) x) =
      QuotientGroup.mk' (zTSubgro p H hmn)
        (DFilt.termMap
          (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom) m x) := rfl

/-- Automorphisms act on arbitrary Zassenhaus-term quotients. -/
noncomputable def zTQuot.mulAutMap {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut
      (zSubgro p G m ⧸ zTSubgro p G hmn) where
  toFun e := zTQuot.congr p G e hmn
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl

@[simp] theorem zTQuot.mul_aut_mapapply {m n : ℕ} (hmn : m ≤ n)
    (e : MulAut G) (q) :
    zTQuot.mulAutMap p G hmn e q =
      zTQuot.congr p G e hmn q := rfl

/-- A homomorphism induces maps on kernels of arbitrary Zassenhaus quotient transitions. -/
noncomputable def transitionKernel {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (zassenhaus p G hmn) →*
      MonoidHom.ker (zassenhaus p H hmn) where
  toFun y :=
    ⟨zQuot.map p G φ n (y : zQuot p G n), by
      rw [MonoidHom.mem_ker]
      have hy : zassenhaus p G hmn
          (y : zQuot p G n) = 1 := (MonoidHom.mem_ker).1 y.property
      have hnat := congrArg
        (fun f : (zQuot p G n) →* (zQuot p H m) =>
          f (y : zQuot p G n))
        (DFilt.quotientTransition_naturality
          (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn)
      calc
        zassenhaus p H hmn
            (zQuot.map p G φ n (y : zQuot p G n)) =
            zQuot.map p G φ m
              (zassenhaus p G hmn
                (y : zQuot p G n)) := by
          simpa [MonoidHom.comp_apply, zQuot.map,
            zassenhaus_filtration_transition] using hnat
        _ = zQuot.map p G φ m 1 := by rw [hy]
        _ = 1 := map_one _⟩
  map_one' := by
    ext
    simp [zQuot.map]
  map_mul' x y := by
    ext
    simp [zQuot.map]

@[simp] theorem zassenhaus_transition_coe {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p G hmn)) :
    ((transitionKernel p G φ hmn y :
        MonoidHom.ker (zassenhaus p H hmn)) :
        zQuot p H n) =
      zQuot.map p G φ n (y : zQuot p G n) := rfl

@[simp] theorem zassenhaus_transition_id {m n : ℕ} (hmn : m ≤ n) :
    transitionKernel p G (MonoidHom.id G) hmn =
      MonoidHom.id (MonoidHom.ker (zassenhaus p G hmn)) := by
  ext y
  simp

@[simp] theorem zassenhaus_kernel_comp {H K : Type*}
    [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    transitionKernel p G (ψ.comp φ) hmn =
      (transitionKernel p H ψ hmn).comp
        (transitionKernel p G φ hmn) := by
  ext y
  simp [zQuot.map_comp]

/-- A group isomorphism induces an isomorphism on arbitrary Zassenhaus transition kernels. -/
noncomputable def zTKern.congr {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (zassenhaus p G hmn) ≃*
      MonoidHom.ker (zassenhaus p H hmn) where
  toFun := transitionKernel p G e.toMonoidHom hmn
  invFun := transitionKernel p H e.symm.toMonoidHom hmn
  left_inv y := by
    rw [← MonoidHom.comp_apply]
    rw [← zassenhaus_kernel_comp p G e.toMonoidHom e.symm.toMonoidHom hmn]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext g; simp
    rw [he]
    simp
  right_inv y := by
    rw [← MonoidHom.comp_apply]
    rw [← zassenhaus_kernel_comp p H e.symm.toMonoidHom e.toMonoidHom hmn]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext h; simp
    rw [he]
    simp
  map_mul' x y := map_mul _ x y

@[simp] theorem zTKern.congr_apply {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.congr p G e hmn y =
      transitionKernel p G e.toMonoidHom hmn y := rfl

@[simp] theorem zTKern.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p G e hmn).symm =
      zTKern.congr p H e.symm hmn := by
  ext y
  rfl

/-- Inverse-application criterion for congruences of Zassenhaus transition kernels. -/
theorem zTKern.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p H hmn))
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (zTKern.congr p G e hmn).symm y = x ↔
      y = zTKern.congr p G e hmn x := by
  rw [MulEquiv.symm_apply_eq]


/-- A split epimorphism that is also injective induces bijections on arbitrary
Zassenhaus term quotients. -/
theorem bijective_inverse_injective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (zassenhausTerm p G φ hmn) := by
  simpa [zassenhausTerm] using
    DFilt.term_bijective_injective
      (filtration_maps_inverse p G φ σ hσ) hinj hmn

/-- A split epimorphism that is also injective induces bijections on arbitrary
Zassenhaus transition kernels. -/
theorem transition_bijective_injective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (transitionKernel p G φ hmn) := by
  simpa [transitionKernel] using
    DFilt.kernel_bijective_injective
      (filtration_maps_inverse p G φ σ hσ) hinj hmn


/-- Termwise-onto maps induce surjections on Zassenhaus term quotients. -/
theorem surjective_maps_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (zassenhausTerm p G φ hmn) := by
  simpa [zassenhausTerm] using
    DFilt.term_surjective_onto honto hmn

/-- Range form of surjectivity on Zassenhaus term quotients. -/
theorem top_maps_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (zassenhausTerm p G φ hmn).range = ⊤ := by
  simpa [zassenhausTerm] using
    DFilt.term_top_onto honto hmn

/-- Termwise-onto maps induce surjections on Zassenhaus transition kernels. -/
theorem transition_surjective_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (transitionKernel p G φ hmn) := by
  simpa [transitionKernel] using
    DFilt.transition_surjective_maps honto hmn

/-- Range form of surjectivity on Zassenhaus transition kernels. -/
theorem range_top_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (transitionKernel p G φ hmn).range = ⊤ := by
  simpa [transitionKernel] using
    DFilt.transition_top_onto honto hmn

/-- Bijectivity on Zassenhaus term quotients from termwise-onto plus kernel containment. -/
theorem bijective_maps_onto {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    Function.Bijective (zassenhausTerm p G φ hmn) := by
  simpa [zassenhausTerm] using
    DFilt.term_bijective_maps
      honto hmn hker

/-- Deeper kernel containment gives bijectivity on earlier Zassenhaus term quotients. -/
theorem bijective_onto_ker {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    Function.Bijective (zassenhausTerm p G φ hmn) := by
  simpa [zassenhausTerm] using
    DFilt.term_bijective_ker
      honto hmn hker hnk

/-- Termwise-onto injective maps give bijectivity on Zassenhaus term quotients. -/
theorem bijective_onto_injective {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (zassenhausTerm p G φ hmn) := by
  simpa [zassenhausTerm] using
    DFilt.term_bijective_injective
      honto hinj hmn

/-- Bijectivity on Zassenhaus transition kernels from termwise-onto plus kernel containment. -/
theorem transition_bijective_maps {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    Function.Bijective (transitionKernel p G φ hmn) := by
  simpa [transitionKernel] using
    DFilt.transition_kernel_bijective
      honto hmn hker

/-- Deeper kernel containment gives bijectivity on earlier Zassenhaus transition kernels. -/
theorem bijective_maps_ker {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    Function.Bijective (transitionKernel p G φ hmn) := by
  simpa [transitionKernel] using
    DFilt.transition_bijective_ker
      honto hmn hker hnk

/-- Termwise-onto injective maps give bijectivity on Zassenhaus transition kernels. -/
theorem zassenhaus_bijective_injective {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (transitionKernel p G φ hmn) := by
  simpa [transitionKernel] using
    DFilt.kernel_bijective_injective
      honto hinj hmn

/-- A termwise-onto map of Zassenhaus filtrations with kernel contained in the deeper
term induces an equivalence on the corresponding term quotient. -/
noncomputable def zassenhausOntoKer {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      (zSubgro p H m ⧸ zTSubgro p H hmn) :=
  DFilt.termMapsOnto honto hmn hker

@[simp] theorem zassenhaus_quotient_ker {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausOntoKer p G φ honto hmn hker x =
      zassenhausTerm p G φ hmn x := rfl

@[simp] theorem maps_onto_monoid {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    (zassenhausOntoKer p G φ honto hmn hker).toMonoidHom =
      zassenhausTerm p G φ hmn := rfl

/-- Inverse-characterization for Zassenhaus term quotient equivalences from termwise-onto
maps with kernel contained in the deeper term. -/
theorem quotient_ker_symm {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (zassenhausOntoKer p G φ honto hmn hker).symm y = x ↔
      y = zassenhausTerm p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
Zassenhaus term quotients. -/
noncomputable def termOntoKer {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      (zSubgro p H m ⧸ zTSubgro p H hmn) :=
  DFilt.termMapsKer honto hmn hker hnk

@[simp] theorem zassenhaus_term_maps {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoKer p G φ honto hmn hker hnk x =
      zassenhausTerm p G φ hmn x := rfl

@[simp] theorem onto_monoid_hom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    (termOntoKer p G φ honto hmn hker hnk).toMonoidHom =
      zassenhausTerm p G φ hmn := rfl

theorem zassenhaus_maps_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (termOntoKer p G φ honto hmn hker hnk).symm y = x ↔
      y = zassenhausTerm p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of Zassenhaus filtrations with kernel contained in the deeper
term induces an equivalence on the corresponding transition kernels. -/
noncomputable def transitionMapsKer {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    MonoidHom.ker (zassenhaus p G hmn) ≃*
      MonoidHom.ker (zassenhaus p H hmn) :=
  DFilt.transitionMapsOnto honto hmn hker

@[simp] theorem zassenhaus_kernel_ker {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionMapsKer p G φ honto hmn hker x =
      transitionKernel p G φ hmn x := rfl

@[simp] theorem ker_monoid_hom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n) :
    (transitionMapsKer p G φ honto hmn hker).toMonoidHom =
      transitionKernel p G φ hmn := rfl

/-- Inverse-characterization for Zassenhaus transition-kernel equivalences from termwise-onto
maps with kernel contained in the deeper term. -/
theorem equiv_onto_symm {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G n)
    (y : MonoidHom.ker (zassenhaus p H hmn))
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (transitionMapsKer p G φ honto hmn hker).symm y = x ↔
      y = transitionKernel p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
Zassenhaus transition kernels. -/
noncomputable def mapsOntoKer {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    MonoidHom.ker (zassenhaus p G hmn) ≃*
      MonoidHom.ker (zassenhaus p H hmn) :=
  DFilt.transitionOntoKer honto hmn hker hnk

@[simp] theorem kernel_maps_ker {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoKer p G φ honto hmn hker hnk x =
      transitionKernel p G φ hmn x := rfl

@[simp] theorem transition_monoid_hom
    {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k) :
    (mapsOntoKer p G φ honto hmn hker hnk).toMonoidHom =
      transitionKernel p G φ hmn := rfl

theorem zassenhaus_maps_symm {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (y : MonoidHom.ker (zassenhaus p H hmn))
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (mapsOntoKer p G φ honto hmn hker hnk).symm y = x ↔
      y = transitionKernel p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A termwise-onto injective map induces an equivalence on Zassenhaus quotients. -/
noncomputable def zQuot.equiv_maps_ontoinj {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    zQuot p G n ≃* zQuot p H n :=
  DFilt.quotientOntoInjective honto hinj n

@[simp] theorem zQuot.equiv_mapsonto_injapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : zQuot p G n) :
    zQuot.equiv_maps_ontoinj p G φ honto hinj n x =
      zQuot.map p G φ n x := rfl

@[simp] theorem zQuot.equivmaps_ontoinj_monoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zQuot.equiv_maps_ontoinj p G φ honto hinj n).toMonoidHom =
      zQuot.map p G φ n := rfl

theorem zQuot.equivmaps_ontoinj_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zQuot p H n) (x : zQuot p G n) :
    (zQuot.equiv_maps_ontoinj p G φ honto hinj n).symm y = x ↔
      y = zQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto injective map induces an equivalence on Zassenhaus term quotients. -/
noncomputable def termOntoInjective {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      (zSubgro p H m ⧸ zTSubgro p H hmn) :=
  DFilt.termMapsInjective honto hinj hmn

@[simp] theorem zassenhaus_term_injective {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoInjective p G φ honto hinj hmn x =
      zassenhausTerm p G φ hmn x := rfl

@[simp] theorem maps_injective_monoid {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (termOntoInjective p G φ honto hinj hmn).toMonoidHom =
      zassenhausTerm p G φ hmn := rfl

theorem term_injective_symm {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (termOntoInjective p G φ honto hinj hmn).symm y = x ↔
      y = zassenhausTerm p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto injective map induces an equivalence on Zassenhaus transition kernels. -/
noncomputable def mapsOntoInjective {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    MonoidHom.ker (zassenhaus p G hmn) ≃*
      MonoidHom.ker (zassenhaus p H hmn) :=
  DFilt.transitionOntoInjective honto hinj hmn

@[simp] theorem kernel_maps_injective {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoInjective p G φ honto hinj hmn x =
      transitionKernel p G φ hmn x := rfl

@[simp] theorem onto_injective_monoid
    {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n) :
    (mapsOntoInjective p G φ honto hinj hmn).toMonoidHom =
      transitionKernel p G φ hmn := rfl

theorem zassenhaus_injective_symm {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) {m n : ℕ}
    (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p H hmn))
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (mapsOntoInjective p G φ honto hinj hmn).symm y = x ↔
      y = transitionKernel p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- A termwise-onto injective map identifies corresponding Zassenhaus subgroup terms. -/
noncomputable def zSubgro.equiv_maps_ontoinj {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    zSubgro p G n ≃* zSubgro p H n :=
  DFilt.termEquivInjective honto hinj n

@[simp] theorem zSubgro.equivmaps_ontoinj_applycoe
    {H : Type*} [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : zSubgro p G n) :
    ((zSubgro.equiv_maps_ontoinj p G φ honto hinj n x :
        zSubgro p H n) : H) = φ (x : G) := rfl


/-- The inverse of the Zassenhaus-term equivalence chooses a preimage under the map. -/
theorem zSubgro.equivmaps_ontoinj_symmapplycoe {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zSubgro p H n) :
    φ (((zSubgro.equiv_maps_ontoinj p G φ honto hinj n).symm y :
        zSubgro p G n) : G) = (y : H) :=
  DFilt.term_symm_coe honto hinj n y

/-- Inverse characterization for the Zassenhaus-subgroup term equivalence. -/
theorem zSubgro.equivmaps_ontoinj_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zSubgro p H n) (x : zSubgro p G n) :
    (zSubgro.equiv_maps_ontoinj p G φ honto hinj n).symm y = x ↔
      y = DFilt.termMap (DFilt.MapsOnto.preserves honto) n x := by
  exact DFilt.maps_symm honto hinj n y x

/-- A split epimorphism that is also injective induces an equivalence on Zassenhaus
quotients. -/
noncomputable def zQuot.equiv_right_invinj {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    zQuot p G n ≃* zQuot p H n :=
  MulEquiv.ofBijective (zQuot.map p G φ n)
    (zQuot.map_bijright_invinj p G φ σ hσ hinj n)

@[simp] theorem zQuot.equiv_rightinv_injapply {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : zQuot p G n) :
    zQuot.equiv_right_invinj p G φ σ hσ hinj n x =
      zQuot.map p G φ n x := rfl

@[simp] theorem zQuot.equivright_invinj_monoidhom
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zQuot.equiv_right_invinj p G φ σ hσ hinj n).toMonoidHom =
      zQuot.map p G φ n := rfl

/-- A split epimorphism that is also injective induces an equivalence on arbitrary
Zassenhaus term quotients. -/
noncomputable def termInverseInjective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
      (zSubgro p H m ⧸ zTSubgro p H hmn) :=
  MulEquiv.ofBijective (zassenhausTerm p G φ hmn)
    (bijective_inverse_injective p G φ σ hσ hinj hmn)

@[simp] theorem term_inverse_injective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termInverseInjective p G φ σ hσ hinj hmn x =
      zassenhausTerm p G φ hmn x := rfl

@[simp] theorem inverse_monoid_hom
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (termInverseInjective p G φ σ hσ hinj hmn).toMonoidHom =
      zassenhausTerm p G φ hmn := rfl

/-- A split epimorphism that is also injective induces an equivalence on arbitrary
Zassenhaus transition kernels. -/
noncomputable def transitionInverseInjective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (zassenhaus p G hmn) ≃*
      MonoidHom.ker (zassenhaus p H hmn) :=
  MulEquiv.ofBijective (transitionKernel p G φ hmn)
    (transition_bijective_injective p G φ σ hσ hinj hmn)

@[simp] theorem transition_inverse_injective
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionInverseInjective p G φ σ hσ hinj hmn x =
      transitionKernel p G φ hmn x := rfl

@[simp] theorem injective_monoid_hom
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (transitionInverseInjective p G φ σ hσ hinj hmn).toMonoidHom =
      transitionKernel p G φ hmn := rfl


/-- Inverse-characterization for the split-epi/injective Zassenhaus quotient equivalence. -/
theorem zQuot.equivright_invinj_symmapplyeq
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zQuot p H n) (x : zQuot p G n) :
    (zQuot.equiv_right_invinj p G φ σ hσ hinj n).symm y = x ↔
      y = zQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the split-epi/injective Zassenhaus term-quotient equivalence. -/
theorem inverse_injective_symm
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (termInverseInjective p G φ σ hσ hinj hmn).symm y = x ↔
      y = zassenhausTerm p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the split-epi/injective Zassenhaus
transition-kernel equivalence. -/
theorem transition_injective_symm
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p H hmn))
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (transitionInverseInjective p G φ σ hσ hinj hmn).symm y = x ↔
      y = transitionKernel p G φ hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

@[simp] theorem zTKern.congr_refl {m n : ℕ} (hmn : m ≤ n) :
    zTKern.congr p G (MulEquiv.refl G) hmn =
      MulEquiv.refl (MonoidHom.ker (zassenhaus p G hmn)) := by
  ext y
  simp [zTKern.congr_apply]

@[simp] theorem zTKern.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p G e hmn).trans
        (zTKern.congr p H f hmn) =
      zTKern.congr p G (e.trans f) hmn := by
  ext y
  change zQuot.map p H f.toMonoidHom n
      (zQuot.map p G e.toMonoidHom n (y : zQuot p G n)) =
    zQuot.map p G (f.toMonoidHom.comp e.toMonoidHom) n y
  have h := congrArg (fun u : zQuot p G n →* zQuot p K n =>
      u (y : zQuot p G n))
    (zQuot.map_comp p G e.toMonoidHom f.toMonoidHom n)
  simpa only [MonoidHom.comp_apply] using h.symm

@[simp] theorem zTKern.congr_coe {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p G hmn)) :
    ((zTKern.congr p G e hmn y :
        MonoidHom.ker (zassenhaus p H hmn)) :
        zQuot p H n) =
      zQuot.map p G e.toMonoidHom n (y : zQuot p G n) := rfl

/-- Automorphisms act on arbitrary Zassenhaus transition kernels. -/
noncomputable def zTKern.mulAutMap {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut (MonoidHom.ker (zassenhaus p G hmn)) where
  toFun e := zTKern.congr p G e hmn
  map_one' := by
    ext y
    change zQuot.map p G (1 : MulAut G).toMonoidHom n
        (y : zQuot p G n) = (y : zQuot p G n)
    refine QuotientGroup.induction_on (y : zQuot p G n) ?_
    intro g
    rfl
  map_mul' e f := by
    ext y
    change zQuot.map p G (e * f).toMonoidHom n
        (y : zQuot p G n) =
      zQuot.map p G e.toMonoidHom n
        (zQuot.map p G f.toMonoidHom n (y : zQuot p G n))
    refine QuotientGroup.induction_on (y : zQuot p G n) ?_
    intro g
    rfl

@[simp] theorem zTKern.mul_aut_mapapply {m n : ℕ} (hmn : m ≤ n)
    (e : MulAut G) (y) :
    zTKern.mulAutMap p G hmn e y =
      zTKern.congr p G e hmn y := rfl

/-- Naturality of the arbitrary Zassenhaus transition-kernel quotient equivalence. -/
theorem zassenhaus_transition_naturality {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (q : zSubgro p G m ⧸ zTSubgro p G hmn) :
    transitionKernel p G φ hmn
        (zassenhausTransitionEquiv p G hmn q) =
      zassenhausTransitionEquiv p H hmn
        (zassenhausTerm p G φ hmn q) := by
  simpa [transitionKernel, zassenhausTransitionEquiv,
    zassenhausTerm, zassenhaus_filtration_transition]
    using DFilt.transition_kernel_naturality
      (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn q

/-- The quotient-kernel equivalence is compatible with isomorphism-induced congruences. -/
theorem zassenhaus_transition_congr {H : Type*} [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTKern.congr p G e hmn
        (zassenhausTransitionEquiv p G hmn q) =
      zassenhausTransitionEquiv p H hmn
        (zTQuot.congr p G e hmn q) := by
  simpa [zTKern.congr_apply, zTQuot.congr_apply]
    using zassenhaus_transition_naturality (p := p) (G := G)
      e.toMonoidHom hmn q

/-- Equivariance of the quotient-kernel equivalence for automorphisms. -/
theorem zassenhaus_transition_aut {m n : ℕ} (hmn : m ≤ n)
    (e : MulAut G) (q : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTKern.mulAutMap p G hmn e
        (zassenhausTransitionEquiv p G hmn q) =
      zassenhausTransitionEquiv p G hmn
        (zTQuot.mulAutMap p G hmn e q) := by
  simpa [zTKern.mul_aut_mapapply,
    zTQuot.mul_aut_mapapply]
    using zassenhaus_transition_congr (p := p) (G := G) e hmn q

/-- Zassenhaus quotient maps are natural with respect to truncation transitions. -/
theorem zassenhaus_quotient_naturality {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    (zassenhaus p H hmn).comp (zQuot.map p G φ n) =
      (zQuot.map p G φ m).comp (zassenhaus p G hmn) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- The same naturality square, phrased via the generic filtration transition maps. -/
theorem quotient_transition_naturality {H : Type*} [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    (DFilt.quotientTransition (zassenhausFiltration p H) hmn).comp
        (zQuot.map p G φ n) =
      (zQuot.map p G φ m).comp
        (DFilt.quotientTransition (zassenhausFiltration p G) hmn) := by
  simpa [← zassenhaus_filtration_transition]
    using zassenhaus_quotient_naturality (p := p) (G := G) φ hmn


/-- A homomorphism restricts to a map between corresponding Zassenhaus terms. -/
noncomputable def zSubgro.termMap {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    zSubgro p G n →* zSubgro p H n :=
  DFilt.termMap (zassenhausFiltration_preserves p G φ) n

@[simp] theorem zSubgro.termMap_coe {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zSubgro p G n) :
    ((zSubgro.termMap p G φ n x : zSubgro p H n) : H) =
      φ (x : G) := rfl

@[simp] theorem zSubgro.termMap_id (n : ℕ) :
    zSubgro.termMap p G (MonoidHom.id G) n =
      MonoidHom.id (zSubgro p G n) :=
  DFilt.termMap_id (zassenhausFiltration p G) n

@[simp] theorem zSubgro.termMap_comp {H K : Type*} [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zSubgro.termMap p G (ψ.comp φ) n =
      (zSubgro.termMap p H ψ n).comp
        (zSubgro.termMap p G φ n) :=
  DFilt.termMap_comp (zassenhausFiltration_preserves p G φ)
    (zassenhausFiltration_preserves p H ψ) n

/-- Termwise-onto maps induce surjections on Zassenhaus subgroup terms. -/
theorem zSubgro.term_surjective_maps {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    Function.Surjective (zSubgro.termMap p G φ n) := by
  simpa [zSubgro.termMap] using
    DFilt.term_surjective_maps honto n

/-- Range form of termwise onto for Zassenhaus subgroup terms. -/
theorem zSubgro.term_range_onto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    (zSubgro.termMap p G φ n).range = ⊤ := by
  simpa [zSubgro.termMap] using
    DFilt.term_range_onto honto n

@[simp] theorem zSubgro.equivmaps_ontoinj_monoidhom
    {H : Type*} [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zSubgro.equiv_maps_ontoinj p G φ honto hinj n).toMonoidHom =
      zSubgro.termMap p G φ n := rfl

/-- A split epimorphism restricts to surjective maps on all Zassenhaus terms. -/
theorem zSubgro.term_mapsurj_rightinv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (zSubgro.termMap p G φ n) :=
  DFilt.term_surjective_maps
    (filtration_maps_inverse p G φ σ hσ) n

/-- Injective homomorphisms restrict injectively to Zassenhaus terms. -/
theorem zSubgro.term_map_of {H : Type*} [Group H]
    (φ : G →* H) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Injective (zSubgro.termMap p G φ n) :=
  DFilt.term_map_of
    (zassenhausFiltration_preserves p G φ) hinj n

/-- A group isomorphism restricts to an isomorphism of corresponding Zassenhaus terms. -/
noncomputable def zSubgro.congr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    zSubgro p G n ≃* zSubgro p H n :=
{ toFun := zSubgro.termMap p G e.toMonoidHom n
  invFun := zSubgro.termMap p H e.symm.toMonoidHom n
  left_inv := by
    intro x
    ext
    change e.symm (e (x : G)) = (x : G)
    simp
  right_inv := by
    intro x
    ext
    change e (e.symm (x : H)) = (x : H)
    simp
  map_mul' := by
    intro x y
    exact map_mul (zSubgro.termMap p G e.toMonoidHom n) x y }

@[simp] theorem zSubgro.congr_apply {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (x : zSubgro p G n) :
    zSubgro.congr p G e n x =
      zSubgro.termMap p G e.toMonoidHom n x := rfl


@[simp] theorem zSubgro.congr_apply_coe {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (x : zSubgro p G n) :
    ((zSubgro.congr p G e n x : zSubgro p H n) : H) =
      e (x : G) := rfl

@[simp] theorem zSubgro.congr_monoid_hom {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zSubgro.congr p G e n).toMonoidHom =
      zSubgro.termMap p G e.toMonoidHom n := rfl

@[simp] theorem zSubgro.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zSubgro.congr p G e n).symm =
      zSubgro.congr p H e.symm n := by
  ext x
  rfl

/-- Inverse-application criterion for congruences of Zassenhaus terms. -/
theorem zSubgro.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (y : zSubgro p H n)
    (x : zSubgro p G n) :
    (zSubgro.congr p G e n).symm y = x ↔
      y = zSubgro.congr p G e n x := by
  rw [MulEquiv.symm_apply_eq]

@[simp] theorem zSubgro.congr_refl (n : ℕ) :
    zSubgro.congr p G (MulEquiv.refl G) n =
      MulEquiv.refl (zSubgro p G n) := by
  ext x
  rfl

@[simp] theorem zSubgro.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zSubgro.congr p G e n).trans (zSubgro.congr p H f n) =
      zSubgro.congr p G (e.trans f) n := by
  ext x
  rfl

/-- The `n`th layer, represented as the kernel of the transition
`G/D_{n+1} → G/D_n`. -/
def zLKern (n : ℕ) : Subgroup (zQuot p G (n + 1)) :=
  MonoidHom.ker (zassenhaus p G (Nat.le_succ n))


/-- The zeroth Zassenhaus layer kernel is trivial. -/
theorem zLKern.subsingleton_zero :
    Subsingleton (zLKern p G 0) := by
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  haveI : Subsingleton (zQuot p G 1) :=
    zQuot.subsingleton_one (p := p) (G := G)
  exact Subsingleton.elim (x : zQuot p G 1)
    (y : zQuot p G 1)

/-- Every element of the zeroth Zassenhaus layer kernel is trivial. -/
theorem zLKern.eq_one_zero (x : zLKern p G 0) : x = 1 := by
  haveI : Subsingleton (zLKern p G 0) :=
    zLKern.subsingleton_zero (p := p) (G := G)
  exact Subsingleton.elim x 1

/-- The Zassenhaus layer kernel is the generic layer kernel of the bundled
Zassenhaus filtration. -/
theorem zassenhaus_layer_filtration (n : ℕ) :
    zLKern p G n =
      DFilt.lKern (zassenhausFiltration p G) n := rfl

/-- The canonical map from a Zassenhaus term to its layer kernel. -/
noncomputable def zLKern.ofTerm (n : ℕ) :
    zSubgro p G n →* zLKern p G n :=
  DFilt.layerOfTerm (zassenhausFiltration p G) n

@[simp] theorem zLKern.ofTerm_coe (n : ℕ)
    (x : zSubgro p G n) :
    ((zLKern.ofTerm p G n x : zLKern p G n) :
        zQuot p G (n + 1)) =
      QuotientGroup.mk' (zSubgro p G (n + 1)) (x : G) := rfl

/-- Every layer-kernel element is represented by an element of the corresponding
Zassenhaus term. -/
theorem zLKern.ofTerm_surjective (n : ℕ) :
    Function.Surjective (zLKern.ofTerm p G n) :=
  DFilt.layer_term_surjective (zassenhausFiltration p G) n

@[simp] theorem zLKern.mem_ker_term (n : ℕ)
    (x : zSubgro p G n) :
    x ∈ MonoidHom.ker (zLKern.ofTerm p G n) ↔
      (x : G) ∈ zSubgro p G (n + 1) :=
  DFilt.ker_term (zassenhausFiltration p G) n x

/-- First-isomorphism-theorem form of a Zassenhaus layer: quotient a term by the
kernel of the term-to-layer map (identified above with the next term). -/
noncomputable def zLKern.termQuotientEquiv (n : ℕ) :
    (zSubgro p G n ⧸
        MonoidHom.ker (zLKern.ofTerm p G n)) ≃*
      zLKern p G n :=
  DFilt.layerQuotientEquiv (zassenhausFiltration p G) n

@[simp] theorem zLKern.term_quot_equivmk (n : ℕ)
    (x : zSubgro p G n) :
    zLKern.termQuotientEquiv p G n
        (QuotientGroup.mk' (MonoidHom.ker (zLKern.ofTerm p G n)) x) =
      zLKern.ofTerm p G n x := rfl

/-- The next Zassenhaus term, viewed as a subgroup of the current term. -/
def zNTerm (n : ℕ) : Subgroup (zSubgro p G n) :=
  DFilt.nextTermSubgroup (zassenhausFiltration p G) n

@[simp] theorem zassenhaus_next_term (n : ℕ)
    (x : zSubgro p G n) :
    x ∈ zNTerm p G n ↔
      (x : G) ∈ zSubgro p G (n + 1) :=
  DFilt.next_term_subgroup (zassenhausFiltration p G) n x

instance next_term_normal (n : ℕ) :
    (zNTerm p G n).Normal :=
  DFilt.next_subgroup_normal (zassenhausFiltration p G) n

/-- Concrete quotient description `Dₙ/Dₙ₊₁ ≃` the `n`th Zassenhaus layer kernel. -/
noncomputable def zLKern.nextQuotientEquiv (n : ℕ) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      zLKern p G n :=
  DFilt.layerNextEquiv (zassenhausFiltration p G) n

/-- The zeroth consecutive Zassenhaus quotient is trivial. -/
theorem zNQuot.subsingleton_zero :
    Subsingleton (zSubgro p G 0 ⧸ zNTerm p G 0) := by
  refine ⟨fun x y => ?_⟩
  apply (zLKern.nextQuotientEquiv p G 0).injective
  haveI : Subsingleton (zLKern p G 0) :=
    zLKern.subsingleton_zero (p := p) (G := G)
  exact Subsingleton.elim _ _

/-- Every element of the zeroth consecutive Zassenhaus quotient is trivial. -/
theorem zNQuot.eq_one_zero
    (x : zSubgro p G 0 ⧸ zNTerm p G 0) : x = 1 := by
  haveI : Subsingleton (zSubgro p G 0 ⧸ zNTerm p G 0) :=
    zNQuot.subsingleton_zero (p := p) (G := G)
  exact Subsingleton.elim x 1

@[simp] theorem zLKern.next_quot_equivmk (n : ℕ)
    (x : zSubgro p G n) :
    zLKern.nextQuotientEquiv p G n
        (QuotientGroup.mk' (zNTerm p G n) x) =
      zLKern.ofTerm p G n x := rfl

/-- Characterize the inverse of the concrete Zassenhaus layer quotient equivalence. -/
theorem zLKern.nextquot_equivsymm_applyeq (n : ℕ)
    (y : zLKern p G n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zLKern.nextQuotientEquiv p G n).symm y = x ↔
      y = zLKern.nextQuotientEquiv p G n x := by
  rw [MulEquiv.symm_apply_eq]


/-- The map induced by a homomorphism on the concrete quotients `Dₙ/Dₙ₊₁`. -/
noncomputable def zNQuot.map {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    (zSubgro p G n ⧸ zNTerm p G n) →*
      (zSubgro p H n ⧸ zNTerm p H n) :=
  DFilt.nextTermQuotient (zassenhausFiltration_preserves p G φ) n

/-- Maps into the zeroth consecutive Zassenhaus quotient are trivial. -/
theorem zNQuot.map_applyeq_onezero {H : Type*} [Group H]
    (φ : G →* H)
    (x : zSubgro p G 0 ⧸ zNTerm p G 0) :
    zNQuot.map p G φ 0 x = 1 :=
  zNQuot.eq_one_zero (p := p) (G := H) _

/-- At level zero, the induced map on consecutive Zassenhaus quotients is the trivial hom. -/
theorem zNQuot.map_eq_onezero {H : Type*} [Group H]
    (φ : G →* H) :
    zNQuot.map p G φ 0 = 1 := by
  ext x
  exact zNQuot.map_applyeq_onezero (p := p) (G := G) φ x

/-- The kernel of the level-zero consecutive Zassenhaus quotient map is the whole source. -/
theorem zNQuot.ker_mapzero_eqtop {H : Type*} [Group H]
    (φ : G →* H) :
    MonoidHom.ker (zNQuot.map p G φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, zNQuot.map_applyeq_onezero (p := p) (G := G) φ x]

/-- The range of the level-zero consecutive Zassenhaus quotient map is the bottom subgroup. -/
theorem zNQuot.range_mapzero_eqbot {H : Type*} [Group H]
    (φ : G →* H) :
    (zNQuot.map p G φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [zNQuot.map_applyeq_onezero (p := p) (G := G) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem zNQuot.map_mk {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zSubgro p G n) :
    zNQuot.map p G φ n
        (QuotientGroup.mk' (zNTerm p G n) x) =
      QuotientGroup.mk' (zNTerm p H n)
        (zSubgro.termMap p G φ n x) := rfl

/-- Kernel membership for represented elements of the map on `Dₙ/Dₙ₊₁`. -/
@[simp] theorem zNQuot.mem_ker_mapmk {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zSubgro p G n) :
    QuotientGroup.mk' (zNTerm p G n) x ∈
        MonoidHom.ker (zNQuot.map p G φ n) ↔
      φ (x : G) ∈ zSubgro p H (n + 1) :=
  DFilt.ker_next_mk
    (zassenhausFiltration_preserves p G φ) n x

/-- Kernel of the map on concrete consecutive Zassenhaus quotients, as an image
of the exact preimage subgroup inside the source term. -/
theorem zNQuot.ker_mapeq_mapcomap {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    MonoidHom.ker (zNQuot.map p G φ n) =
      ((zNTerm p H n).comap (zSubgro.termMap p G φ n)).map
        (QuotientGroup.mk' (zNTerm p G n)) :=
  DFilt.ker_next_comap
    (zassenhausFiltration_preserves p G φ) n

/-- The kernel of a concrete consecutive Zassenhaus quotient map as a quotient
of the exact preimage subgroup inside the source term. -/
noncomputable def zNQuot.kernelEquiv {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    ((zNTerm p H n).comap (zSubgro.termMap p G φ n)) ⧸
      ((zNTerm p G n).subgroupOf
        ((zNTerm p H n).comap (zSubgro.termMap p G φ n))) ≃*
        MonoidHom.ker (zNQuot.map p G φ n) :=
  DFilt.nextTermEquiv
    (zassenhausFiltration_preserves p G φ) n

@[simp] theorem zNQuot.map_id (n : ℕ) :
    zNQuot.map p G (MonoidHom.id G) n =
      MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n) :=
  DFilt.next_term_id (zassenhausFiltration p G) n

@[simp] theorem zNQuot.map_comp {H K : Type*} [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zNQuot.map p G (ψ.comp φ) n =
      (zNQuot.map p H ψ n).comp
        (zNQuot.map p G φ n) :=
  DFilt.next_quotient_comp
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H ψ) n

/-- A split epimorphism induces surjective maps on concrete consecutive Zassenhaus quotients. -/
theorem zNQuot.map_surj_rightinv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (zNQuot.map p G φ n) :=
  DFilt.next_surjective_onto
    (filtration_maps_inverse p G φ σ hσ) n

/-- Injectivity criterion for maps on concrete consecutive Zassenhaus quotients. -/
theorem zNQuot.map_inj_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ}
    (hpre : (zSubgro p H (n + 1)).comap φ ≤
      zSubgro p G (n + 1)) :
    Function.Injective (zNQuot.map p G φ n) :=
  DFilt.next_injective_comap
    (zassenhausFiltration_preserves p G φ) hpre

/-- Exact injectivity criterion for maps on concrete consecutive Zassenhaus quotients,
phrased inside the source and target terms. -/
theorem zNQuot.map_injiff_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ} :
    Function.Injective (zNQuot.map p G φ n) ↔
      (zNTerm p H n).comap (zSubgro.termMap p G φ n) ≤
        zNTerm p G n :=
  DFilt.next_term_comap
    (zassenhausFiltration_preserves p G φ)

/-- For a split epimorphism, injectivity on consecutive Zassenhaus quotients is
controlled by the kernel intersection with the current term. -/
theorem zNQuot.mapinj_iffinfker_lerightinv
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (zNQuot.map p G φ n) ↔
      φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1) :=
  DFilt.next_inf_inverse
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ

/-- For a split epimorphism, bijectivity on consecutive Zassenhaus quotients is
controlled by the kernel intersection with the current term. -/
theorem zNQuot.mapbij_iffinfker_lerightinv
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (zNQuot.map p G φ n) ↔
      φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1) :=
  DFilt.next_bijective_inf
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ

/-- A termwise-onto injective map induces an equivalence on consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.equiv_maps_ontoinj {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      (zSubgro p H n ⧸ zNTerm p H n) :=
  DFilt.nextOntoInjective honto hinj n

@[simp] theorem zNQuot.equiv_mapsonto_injapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equiv_maps_ontoinj p G φ honto hinj n x =
      zNQuot.map p G φ n x := rfl

@[simp] theorem zNQuot.equivmaps_ontoinj_monoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zNQuot.equiv_maps_ontoinj p G φ honto hinj n).toMonoidHom =
      zNQuot.map p G φ n := rfl

theorem zNQuot.equivmaps_ontoinj_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zSubgro p H n ⧸ zNTerm p H n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equiv_maps_ontoinj p G φ honto hinj n).symm y = x ↔
      y = zNQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of Zassenhaus filtrations whose kernel lies in the next
source term induces an equivalence on consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.equiv_mapsonto_kerle {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      (zSubgro p H n ⧸ zNTerm p H n) :=
  DFilt.nextMapsKer honto n hker

@[simp] theorem zNQuot.equivmaps_ontoker_leapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equiv_mapsonto_kerle p G φ honto n hker x =
      zNQuot.map p G φ n x := rfl

@[simp] theorem zNQuot.equivmaps_ontoker_lemonoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    (zNQuot.equiv_mapsonto_kerle p G φ honto n hker).toMonoidHom =
      zNQuot.map p G φ n := rfl

/-- Inverse-characterization for consecutive Zassenhaus quotient equivalences from
termwise-onto maps with kernel in the next source term. -/
theorem zNQuot.equivmaps_ontokerle_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1))
    (y : zSubgro p H n ⧸ zNTerm p H n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equiv_mapsonto_kerle p G φ honto n hker).symm y = x ↔
      y = zNQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.equivmaps_ontoker_lele {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      (zSubgro p H n ⧸ zNTerm p H n) :=
  DFilt.nextOntoKer honto n hker hnk

@[simp] theorem zNQuot.equivmaps_ontoker_leleapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equivmaps_ontoker_lele p G φ honto n hker hnk x =
      zNQuot.map p G φ n x := rfl

@[simp] theorem zNQuot.equivmaps_ontokerle_lemonoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    (zNQuot.equivmaps_ontoker_lele p G φ honto n hker hnk).toMonoidHom =
      zNQuot.map p G φ n := rfl

/-- Inverse-characterization for monotone-kernel consecutive Zassenhaus quotient equivalences. -/
theorem zNQuot.equivm_kerle_symma {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k)
    (y : zSubgro p H n ⧸ zNTerm p H n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equivmaps_ontoker_lele p G φ honto n hker hnk).symm y = x ↔
      y = zNQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A split epimorphism induces an equivalence on consecutive Zassenhaus quotients
when its kernel meets `Dₙ` inside `Dₙ₊₁`. -/
noncomputable def zNQuot.rightInverseEquiv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      (zSubgro p H n ⧸ zNTerm p H n) :=
  MulEquiv.ofBijective (zNQuot.map p G φ n)
    ((zNQuot.mapbij_iffinfker_lerightinv
      p G φ σ hσ).2 hker)

@[simp] theorem zNQuot.equiv_right_invapply {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1))
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.rightInverseEquiv p G φ σ hσ hker x =
      zNQuot.map p G φ n x := rfl

@[simp] theorem zNQuot.equiv_rightinv_monoidhom {H : Type*}
    [Group H] (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    (zNQuot.rightInverseEquiv p G φ σ hσ hker).toMonoidHom =
      zNQuot.map p G φ n := rfl

/-- Inverse-characterization for the split-epi consecutive Zassenhaus quotient equivalence. -/
theorem zNQuot.equivright_invsymm_applyeq {H : Type*}
    [Group H] (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1))
    (y : zSubgro p H n ⧸ zNTerm p H n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.rightInverseEquiv p G φ σ hσ hker).symm y = x ↔
      y = zNQuot.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl



/-- A multiplicative equivalence induces an equivalence on consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.congr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zSubgro p G n ⧸ zNTerm p G n) ≃*
      (zSubgro p H n ⧸ zNTerm p H n) :=
{ toFun := zNQuot.map p G e.toMonoidHom n
  invFun := zNQuot.map p H e.symm.toMonoidHom n
  left_inv := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (zNTerm p G n)
        (zSubgro.termMap p H e.symm.toMonoidHom n
          (zSubgro.termMap p G e.toMonoidHom n x)) =
      QuotientGroup.mk' (zNTerm p G n) x
    congr 1
    ext
    simp
  right_inv := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (zNTerm p H n)
        (zSubgro.termMap p G e.toMonoidHom n
          (zSubgro.termMap p H e.symm.toMonoidHom n x)) =
      QuotientGroup.mk' (zNTerm p H n) x
    congr 1
    ext
    simp
  map_mul' := by
    intro a b
    exact map_mul (zNQuot.map p G e.toMonoidHom n) a b }

@[simp] theorem zNQuot.congr_mk {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (x : zSubgro p G n) :
    zNQuot.congr p G e n
        (QuotientGroup.mk' (zNTerm p G n) x) =
      QuotientGroup.mk' (zNTerm p H n)
        (zSubgro.termMap p G e.toMonoidHom n x) := rfl

@[simp] theorem zNQuot.congr_monoid_hom {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zNQuot.congr p G e n).toMonoidHom =
      zNQuot.map p G e.toMonoidHom n := rfl

@[simp] theorem zNQuot.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zNQuot.congr p G e n).symm =
      zNQuot.congr p H e.symm n := by
  ext q
  rfl

/-- Inverse-application criterion for congruences of consecutive Zassenhaus quotients. -/
theorem zNQuot.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ)
    (y : zSubgro p H n ⧸ zNTerm p H n)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.congr p G e n).symm y = x ↔
      y = zNQuot.congr p G e n x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem zNQuot.congr_refl (n : ℕ) :
    zNQuot.congr p G (MulEquiv.refl G) n =
      MulEquiv.refl (zSubgro p G n ⧸ zNTerm p G n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zNQuot.congr_trans {H K : Type*} [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zNQuot.congr p G e n).trans
        (zNQuot.congr p H f n) =
      zNQuot.congr p G (e.trans f) n := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Automorphisms of `G` act on the concrete consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.mulAutMap (n : ℕ) :
    MulAut G →* MulAut (zSubgro p G n ⧸ zNTerm p G n) where
  toFun e := zNQuot.congr p G e n
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  map_mul' e f := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl

/-- A group homomorphism induces a homomorphism on each Zassenhaus layer kernel. -/
noncomputable def zLKern.map {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    zLKern p G n →* zLKern p H n :=
  DFilt.layerMap (zassenhausFiltration_preserves p G φ) n

/-- Maps into the zeroth Zassenhaus layer kernel are trivial. -/
theorem zLKern.map_applyeq_onezero {H : Type*} [Group H]
    (φ : G →* H) (x : zLKern p G 0) :
    zLKern.map p G φ 0 x = 1 :=
  zLKern.eq_one_zero (p := p) (G := H) _

/-- At level zero, the induced map on Zassenhaus layer kernels is the trivial hom. -/
theorem zLKern.map_eq_onezero {H : Type*} [Group H]
    (φ : G →* H) :
    zLKern.map p G φ 0 = 1 := by
  ext x
  exact congrArg (fun y : zLKern p H 0 =>
      (y : zQuot p H (0 + 1)))
    (zLKern.map_applyeq_onezero (p := p) (G := G) φ x)

/-- The kernel of the level-zero Zassenhaus layer-kernel map is the whole source. -/
theorem zLKern.ker_mapzero_eqtop {H : Type*} [Group H]
    (φ : G →* H) :
    MonoidHom.ker (zLKern.map p G φ 0) = ⊤ := by
  ext x
  simp [MonoidHom.mem_ker, zLKern.map_applyeq_onezero (p := p) (G := G) φ x]

/-- The range of the level-zero Zassenhaus layer-kernel map is the bottom subgroup. -/
theorem zLKern.range_mapzero_eqbot {H : Type*} [Group H]
    (φ : G →* H) :
    (zLKern.map p G φ 0).range = ⊥ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [zLKern.map_applyeq_onezero (p := p) (G := G) φ x]
  · intro hy
    have hy1 : y = 1 := by simpa using hy
    refine ⟨1, ?_⟩
    simp [hy1]

@[simp] theorem zLKern.map_coe {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zLKern p G n) :
    ((zLKern.map p G φ n x : zLKern p H n) :
        zQuot p H (n + 1)) =
      zQuot.map p G φ (n + 1)
        (x : zQuot p G (n + 1)) := rfl

/-- The concrete quotient equivalence is natural for homomorphisms. -/
theorem zLKern.next_quot_equivnatural {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ)
    (q : zSubgro p G n ⧸ zNTerm p G n) :
    zLKern.nextQuotientEquiv p H n
        (zNQuot.map p G φ n q) =
      zLKern.map p G φ n
        (zLKern.nextQuotientEquiv p G n q) :=
  DFilt.layer_next_naturality
    (zassenhausFiltration_preserves p G φ) n q

/-- The term-to-layer maps are natural for group homomorphisms. -/
theorem zLKern.ofTerm_naturality {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    (zLKern.map p G φ n).comp (zLKern.ofTerm p G n) =
      (zLKern.ofTerm p H n).comp
        (zSubgro.termMap p G φ n) :=
  DFilt.layer_term_naturality (zassenhausFiltration_preserves p G φ) n

/-- Kernel membership for term-represented Zassenhaus layer elements. -/
@[simp] theorem zLKern.mem_ker_mapterm {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zSubgro p G n) :
    zLKern.ofTerm p G n x ∈
        MonoidHom.ker (zLKern.map p G φ n) ↔
      φ (x : G) ∈ zSubgro p H (n + 1) :=
  DFilt.ker_layer_term
    (zassenhausFiltration_preserves p G φ) n x

@[simp] theorem zLKern.map_id (n : ℕ) :
    zLKern.map p G (MonoidHom.id G) n =
      MonoidHom.id (zLKern p G n) := by
  apply MonoidHom.ext
  intro x
  ext
  change DFilt.quotientMap
      (zassenhausFiltration_preserves p G (MonoidHom.id G)) (n + 1)
      (x : zQuot p G (n + 1)) =
    (x : zQuot p G (n + 1))
  rw [DFilt.quotientMap_id]
  rfl

@[simp] theorem zLKern.map_comp {H K : Type*} [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zLKern.map p G (ψ.comp φ) n =
      (zLKern.map p H ψ n).comp (zLKern.map p G φ n) := by
  apply MonoidHom.ext
  intro x
  ext
  change DFilt.quotientMap
      (zassenhausFiltration_preserves p G (ψ.comp φ)) (n + 1)
      (x : zQuot p G (n + 1)) =
    DFilt.quotientMap (zassenhausFiltration_preserves p H ψ) (n + 1)
      (DFilt.quotientMap (zassenhausFiltration_preserves p G φ) (n + 1)
        (x : zQuot p G (n + 1)))
  refine QuotientGroup.induction_on (x : zQuot p G (n + 1)) ?_
  intro g
  rfl

/-- A split epimorphism induces surjective maps on Zassenhaus layer kernels. -/
theorem zLKern.map_surj_rightinv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) (n : ℕ) :
    Function.Surjective (zLKern.map p G φ n) :=
  DFilt.layer_surjective_onto
    (filtration_maps_inverse p G φ σ hσ) n

/-- Injectivity criterion for maps on Zassenhaus layer kernels. -/
theorem zLKern.map_inj_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ}
    (hpre : (zSubgro p H (n + 1)).comap φ ≤
      zSubgro p G (n + 1)) :
    Function.Injective (zLKern.map p G φ n) :=
  DFilt.layer_injective_comap
    (zassenhausFiltration_preserves p G φ) hpre

/-- Exact injectivity criterion for maps on Zassenhaus layer kernels, phrased
inside consecutive Zassenhaus terms. -/
theorem zLKern.map_injiff_comaple {H : Type*} [Group H]
    (φ : G →* H) {n : ℕ} :
    Function.Injective (zLKern.map p G φ n) ↔
      (zNTerm p H n).comap (zSubgro.termMap p G φ n) ≤
        zNTerm p G n :=
  DFilt.layer_comap
    (zassenhausFiltration_preserves p G φ)

/-- For a split epimorphism, injectivity on Zassenhaus layer kernels is controlled
by the kernel intersection with the current term. -/
theorem zLKern.mapinj_iffinfker_lerightinv
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (zLKern.map p G φ n) ↔
      φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1) :=
  DFilt.injective_inf_inverse
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ

/-- For a split epimorphism, bijectivity on Zassenhaus layer kernels is controlled
by the kernel intersection with the current term. -/
theorem zLKern.mapbij_iffinfker_lerightinv
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (zLKern.map p G φ n) ↔
      φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1) :=
  DFilt.bijective_inf_inverse
    (zassenhausFiltration_preserves p G φ) (zassenhausFiltration_preserves p H σ) hσ

/-- Termwise-onto maps induce surjections on consecutive Zassenhaus quotients. -/
theorem zNQuot.map_surj_mapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    Function.Surjective (zNQuot.map p G φ n) := by
  simpa [zNQuot.map] using
    DFilt.next_surjective_onto honto n

/-- Range form of surjectivity on consecutive Zassenhaus quotients. -/
theorem zNQuot.maprange_eqtop_mapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    (zNQuot.map p G φ n).range = ⊤ := by
  simpa [zNQuot.map] using
    DFilt.next_top_onto honto n

/-- Termwise-onto maps induce surjections on Zassenhaus layer kernels. -/
theorem zLKern.map_surj_mapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    Function.Surjective (zLKern.map p G φ n) := by
  simpa [zLKern.map] using
    DFilt.layer_surjective_onto honto n

/-- Range form of surjectivity on Zassenhaus layer kernels. -/
theorem zLKern.maprange_eqtop_mapsonto {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) :
    (zLKern.map p G φ n).range = ⊤ := by
  simpa [zLKern.map] using
    DFilt.layer_top_onto honto n

/-- Bijectivity on consecutive Zassenhaus quotients from termwise-onto plus kernel
containment in the next source term. -/
theorem zNQuot.mapbij_mapsonto_kerle {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    Function.Bijective (zNQuot.map p G φ n) := by
  simpa [zNQuot.map] using
    DFilt.next_bijective_maps honto hker

/-- Bijectivity on Zassenhaus layer kernels from termwise-onto plus kernel containment
in the next source term. -/
theorem zLKern.mapbij_mapsonto_kerle {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {n : ℕ}
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    Function.Bijective (zLKern.map p G φ n) := by
  simpa [zLKern.map] using
    DFilt.layer_bijective_maps honto hker

/-- Deeper kernel containment gives bijectivity on earlier consecutive Zassenhaus quotients. -/
theorem zNQuot.mapbij_mapsonto_kerlele {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    Function.Bijective (zNQuot.map p G φ n) := by
  simpa [zNQuot.map] using
    DFilt.next_bijective_ker
      honto n hker hnk

/-- Deeper kernel containment gives bijectivity on earlier Zassenhaus layer kernels. -/
theorem zLKern.mapbij_mapsonto_kerlele {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    Function.Bijective (zLKern.map p G φ n) := by
  simpa [zLKern.map] using
    DFilt.layer_bijective_ker honto n hker hnk

/-- Termwise-onto injective maps give bijectivity on consecutive Zassenhaus quotients. -/
theorem zNQuot.map_bijmaps_ontoinj {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (zNQuot.map p G φ n) := by
  simpa [zNQuot.map] using
    DFilt.next_bijective_injective honto hinj n

/-- Termwise-onto injective maps give bijectivity on Zassenhaus layer kernels. -/
theorem zLKern.map_bijmaps_ontoinj {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (zLKern.map p G φ n) := by
  simpa [zLKern.map] using
    DFilt.layer_bijective_injective honto hinj n

/-- A termwise-onto injective map induces an equivalence on Zassenhaus layer kernels. -/
noncomputable def zLKern.equiv_maps_ontoinj {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    zLKern p G n ≃* zLKern p H n :=
  DFilt.layerOntoInjective honto hinj n

@[simp] theorem zLKern.equiv_mapsonto_injapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : zLKern p G n) :
    zLKern.equiv_maps_ontoinj p G φ honto hinj n x =
      zLKern.map p G φ n x := rfl

@[simp] theorem zLKern.equivmaps_ontoinj_monoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ) :
    (zLKern.equiv_maps_ontoinj p G φ honto hinj n).toMonoidHom =
      zLKern.map p G φ n := rfl

theorem zLKern.equivmaps_ontoinj_symmapplyeq {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : zLKern p H n) (x : zLKern p G n) :
    (zLKern.equiv_maps_ontoinj p G φ honto hinj n).symm y = x ↔
      y = zLKern.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A termwise-onto map of Zassenhaus filtrations whose kernel lies in the next
source term induces an equivalence on Zassenhaus layer kernels. -/
noncomputable def zLKern.equiv_mapsonto_kerle {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    zLKern p G n ≃* zLKern p H n :=
  DFilt.layerMapsKer honto n hker

@[simp] theorem zLKern.equivmaps_ontoker_leapply {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1)) (x : zLKern p G n) :
    zLKern.equiv_mapsonto_kerle p G φ honto n hker x =
      zLKern.map p G φ n x := rfl

@[simp] theorem zLKern.equivmaps_ontoker_lemonoidhom {H : Type*} [Group H]
    (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1)) :
    (zLKern.equiv_mapsonto_kerle p G φ honto n hker).toMonoidHom =
      zLKern.map p G φ n := rfl

/-- A split epimorphism induces an equivalence on Zassenhaus layer kernels under
the same kernel-intersection condition as for consecutive quotients. -/
noncomputable def zLKern.rightInverseEquiv {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    zLKern p G n ≃* zLKern p H n :=
  MulEquiv.ofBijective (zLKern.map p G φ n)
    ((zLKern.mapbij_iffinfker_lerightinv
      p G φ σ hσ).2 hker)

@[simp] theorem zLKern.equiv_right_invapply {H : Type*} [Group H]
    (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1))
    (x : zLKern p G n) :
    zLKern.rightInverseEquiv p G φ σ hσ hker x =
      zLKern.map p G φ n x := rfl

@[simp] theorem zLKern.equiv_rightinv_monoidhom {H : Type*}
    [Group H] (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    (zLKern.rightInverseEquiv p G φ σ hσ hker).toMonoidHom =
      zLKern.map p G φ n := rfl

/-- Inverse-characterization for the split-epi Zassenhaus layer equivalence. -/
theorem zLKern.equivright_invsymm_applyeq {H : Type*}
    [Group H] (φ : G →* H) (σ : H →* G) (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1))
    (y : zLKern p H n) (x : zLKern p G n) :
    (zLKern.rightInverseEquiv p G φ σ hσ hker).symm y = x ↔
      y = zLKern.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Inverse-characterization for the small-kernel Zassenhaus layer equivalence. -/
theorem zLKern.equivmaps_ontokerle_symmapplyeq {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ)
    (hker : φ.ker ≤ zSubgro p G (n + 1))
    (y : zLKern p H n) (x : zLKern p G n) :
    (zLKern.equiv_mapsonto_kerle p G φ honto n hker).symm y = x ↔
      y = zLKern.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A sufficiently deeper kernel-containment hypothesis induces equivalences on earlier
Zassenhaus layer kernels. -/
noncomputable def zLKern.equivmaps_ontoker_lele {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    zLKern p G n ≃* zLKern p H n :=
  DFilt.layerOntoKer honto n hker hnk

@[simp] theorem zLKern.equivmaps_ontoker_leleapply {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k)
    (x : zLKern p G n) :
    zLKern.equivmaps_ontoker_lele p G φ honto n hker hnk x =
      zLKern.map p G φ n x := rfl

@[simp] theorem zLKern.equivmaps_ontokerle_lemonoidhom {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k) :
    (zLKern.equivmaps_ontoker_lele p G φ honto n hker hnk).toMonoidHom =
      zLKern.map p G φ n := rfl

/-- Inverse-characterization for monotone-kernel Zassenhaus layer equivalences. -/
theorem zLKern.equivm_kerle_symma {H : Type*}
    [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n + 1 ≤ k)
    (y : zLKern p H n) (x : zLKern p G n) :
    (zLKern.equivmaps_ontoker_lele p G φ honto n hker hnk).symm y = x ↔
      y = zLKern.map p G φ n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl



/-- Additive version of the induced map on Zassenhaus layer kernels. -/
def zLKern.mapAdd {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    Additive (zLKern p G n) →+
      Additive (zLKern p H n) :=
  (zLKern.map p G φ n).toAdditive

@[simp] theorem zLKern.map_add_mul {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) (x : zLKern p G n) :
    zLKern.mapAdd p G φ n (Additive.ofMul x) =
      Additive.ofMul (zLKern.map p G φ n x) := rfl

/-- A multiplicative equivalence induces equivalences on Zassenhaus layer kernels. -/
noncomputable def zLKern.congr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    zLKern p G n ≃* zLKern p H n :=
{ zLKern.map p G e.toMonoidHom n with
  invFun := zLKern.map p H e.symm.toMonoidHom n
  left_inv := by
    intro x
    have h := congrArg
      (fun f : zLKern p G n →* zLKern p G n => f x)
      (zLKern.map_comp (p := p) (G := G)
        e.toMonoidHom e.symm.toMonoidHom n)
    change zLKern.map p G (e.symm.toMonoidHom.comp e.toMonoidHom) n x = _ at h
    simpa using h.symm
  right_inv := by
    intro x
    have h := congrArg
      (fun f : zLKern p H n →* zLKern p H n => f x)
      (zLKern.map_comp (p := p) (G := H)
        e.symm.toMonoidHom e.toMonoidHom n)
    change zLKern.map p H (e.toMonoidHom.comp e.symm.toMonoidHom) n x = _ at h
    simpa using h.symm }

@[simp] theorem zLKern.congr_apply {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (x : zLKern p G n) :
    zLKern.congr p G e n x =
      zLKern.map p G e.toMonoidHom n x := rfl

@[simp] theorem zLKern.congr_monoid_hom {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zLKern.congr p G e n).toMonoidHom =
      zLKern.map p G e.toMonoidHom n := rfl

@[simp] theorem zLKern.congr_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zLKern.congr p G e n).symm =
      zLKern.congr p H e.symm n := by
  ext x
  rfl

@[simp] theorem zLKern.congr_refl (n : ℕ) :
    zLKern.congr p G (MulEquiv.refl G) n =
      MulEquiv.refl (zLKern p G n) := by
  ext x
  have h := congrArg (fun u : zLKern p G n →* zLKern p G n => u x)
    (zLKern.map_id (p := p) (G := G) n)
  exact congrArg (fun y : zLKern p G n =>
      (y : zQuot p G (n + 1))) h

@[simp] theorem zLKern.congr_trans {H K : Type*}
    [Group H] [Group K] (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zLKern.congr p G e n).trans
        (zLKern.congr p H f n) =
      zLKern.congr p G (e.trans f) n := by
  ext x
  have h := congrArg (fun u : zLKern p G n →* zLKern p K n => u x)
    (zLKern.map_comp (p := p) (G := G) e.toMonoidHom f.toMonoidHom n)
  exact congrArg (fun y : zLKern p K n =>
      (y : zQuot p K (n + 1))) h.symm

@[simp] theorem zLKern.congr_coe {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (x : zLKern p G n) :
    ((zLKern.congr p G e n x : zLKern p H n) :
        zQuot p H (n + 1)) =
      zQuot.map p G e.toMonoidHom (n + 1)
        (x : zQuot p G (n + 1)) := by
  rw [zLKern.congr_apply, zLKern.map_coe]

/-- Inverse-application criterion for the layer-kernel congruence induced by an equivalence. -/
theorem zLKern.congr_symm_applyeq {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) (y : zLKern p H n)
    (x : zLKern p G n) :
    (zLKern.congr p G e n).symm y = x ↔
      y = zLKern.congr p G e n x := by
  rw [MulEquiv.symm_apply_eq]

/-- The concrete consecutive-quotient equivalence is compatible with equivalences of groups. -/
theorem zLKern.next_quot_equivcongr {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ)
    (q : zSubgro p G n ⧸ zNTerm p G n) :
    zLKern.nextQuotientEquiv p H n
        (zNQuot.congr p G e n q) =
      zLKern.congr p G e n
        (zLKern.nextQuotientEquiv p G n q) :=
  zLKern.next_quot_equivnatural p G e.toMonoidHom n q

/-- Automorphisms of `G` act on each Zassenhaus layer kernel. -/
noncomputable def zLKern.mulAutMap (n : ℕ) :
    MulAut G →* MulAut (zLKern p G n) where
  toFun e := zLKern.congr p G e n
  map_one' := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl
  map_mul' e f := by
    ext x
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    rfl

@[simp] theorem zLKern.mul_aut_mapapply {n : ℕ}
    (e : MulAut G) (x : zLKern p G n) :
    zLKern.mulAutMap p G n e x =
      zLKern.congr p G e n x := rfl

@[simp] theorem zassenhaus_layer_mk (n : ℕ) (g : G) :
    QuotientGroup.mk' (zSubgro p G (n + 1)) g ∈
      zLKern p G n ↔
    g ∈ zSubgro p G n := by
  dsimp [zLKern]
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff g

/-- The kernel of the successive Zassenhaus quotient transition is the layer kernel. -/
@[simp] theorem zassenhaus_succ_ker (n : ℕ) :
    MonoidHom.ker (zassenhaus p G (Nat.le_succ n)) =
      zLKern p G n := by
  rw [zassenhaus_filtration_transition]
  rfl

/-- Representative criterion for the successive-transition kernel. -/
@[simp] theorem ker_succ_mk (n : ℕ) (g : G) :
    QuotientGroup.mk' (zSubgro p G (n + 1)) g ∈
        MonoidHom.ker (zassenhaus p G (Nat.le_succ n)) ↔
      g ∈ zSubgro p G n := by
  rw [zassenhaus_succ_ker]
  exact zassenhaus_layer_mk p G n g

@[simp] theorem zassenhaus_layer_top :
    zLKern p G 0 = ⊤ := by
  ext q
  simp only [Subgroup.mem_top, iff_true]
  refine QuotientGroup.induction_on q ?_
  intro g
  exact (zassenhaus_layer_mk p G 0 g).2 (by
    simp [zassenhaus_subgroup_top])

/-- The first layer is all of `G/D₂`, since `D₁ = G`. -/
@[simp] theorem zassenhaus_kernel_top :
    zLKern p G 1 = ⊤ := by
  ext q
  simp only [Subgroup.mem_top, iff_true]
  refine QuotientGroup.induction_on q ?_
  intro g
  exact (zassenhaus_layer_mk p G 1 g).2 (by
    simp [zassenhaus_one_top])

/-- The first layer kernel is multiplicatively equivalent to the ambient quotient
`G/D₂` (it is the top subgroup there). -/
def zassenhausLayerEquiv :
    zLKern p G 1 ≃* zQuot p G 2 where
  toFun x := x.1
  invFun q := ⟨q, by rw [zassenhaus_kernel_top]; trivial⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_mul' := by intro x y; rfl

/-- The positive Zassenhaus layers are abelian: commutators of two elements in the
kernel of `G/D_{n+1} → G/D_n` vanish in `G/D_{n+1}`. -/
theorem zassenhaus_commutator_one {n : ℕ} (hn : 1 ≤ n)
    {q r : zQuot p G (n + 1)}
    (hq : q ∈ zLKern p G n)
    (hr : r ∈ zLKern p G n) :
    ⁅q, r⁆ = 1 := by
  refine QuotientGroup.induction_on q ?_ hq
  intro g hqg
  refine QuotientGroup.induction_on r ?_ hr
  intro h hrh
  have hg : g ∈ zSubgro p G n :=
    (zassenhaus_layer_mk p G n g).1 hqg
  have hh : h ∈ zSubgro p G n :=
    (zassenhaus_layer_mk p G n h).1 hrh
  change QuotientGroup.mk' (zSubgro p G (n + 1)) ⁅g, h⁆ = 1
  apply (QuotientGroup.eq_one_iff ⁅g, h⁆).mpr
  have hc : ⁅g, h⁆ ∈ zSubgro p G (n + n) :=
    commutator_subgroup_add p G (by omega) (by omega) hg hh
  exact zassenhausSubgroup_antitone p G (by omega : n + 1 ≤ n + n) hc

/-- Equivalently, elements of a positive Zassenhaus layer commute in the truncated
quotient. -/
theorem zassenhaus_layer_comm {n : ℕ} (hn : 1 ≤ n)
    {q r : zQuot p G (n + 1)}
    (hq : q ∈ zLKern p G n)
    (hr : r ∈ zLKern p G n) :
    q * r = r * q := by
  exact (commutatorElement_eq_one_iff_mul_comm).1
    (zassenhaus_commutator_one p G hn hq hr)

/-- Positive Zassenhaus layers have exponent `p` (for prime `p`).  Together with
commutativity, this is the elementary-abelian structure of the graded pieces. -/
theorem zassenhaus_layer_one [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    {q : zQuot p G (n + 1)}
    (hq : q ∈ zLKern p G n) :
    q ^ p = 1 := by
  refine QuotientGroup.induction_on q ?_ hq
  intro g hqg
  have hg : g ∈ zSubgro p G n :=
    (zassenhaus_layer_mk p G n g).1 hqg
  have hp2 : 2 ≤ p := Nat.Prime.two_le (Fact.out)
  change QuotientGroup.mk' (zSubgro p G (n + 1)) (g ^ p) = 1
  apply (QuotientGroup.eq_one_iff (g ^ p)).mpr
  have hpw : g ^ p ∈ zSubgro p G (n * p) :=
    pow_subgroup_self (p := p) (G := G) hg
  exact zassenhausSubgroup_antitone p G (by
    have htwo : n + 1 ≤ n * 2 := by omega
    have hmul : n * 2 ≤ n * p := Nat.mul_le_mul_left n hp2
    exact le_trans htwo hmul) hpw

/-- Layer elements commute for every index.  The zero-index case is trivial because
`D₁ = G`; positive indices are the usual graded-commutativity estimate. -/
theorem zassenhaus_comm_any {n : ℕ}
    {q r : zQuot p G (n + 1)}
    (hq : q ∈ zLKern p G n)
    (hr : r ∈ zLKern p G n) :
    q * r = r * q := by
  cases n with
  | zero =>
      refine QuotientGroup.induction_on q ?_ hq
      intro g _
      refine QuotientGroup.induction_on r ?_ hr
      intro h _
      change QuotientGroup.mk' (zSubgro p G 1) (g * h) =
        QuotientGroup.mk' (zSubgro p G 1) (h * g)
      have hl : QuotientGroup.mk' (zSubgro p G 1) (g * h) = 1 := by
        apply (QuotientGroup.eq_one_iff (g * h)).mpr
        simp [zassenhaus_one_top]
      have hr' : QuotientGroup.mk' (zSubgro p G 1) (h * g) = 1 := by
        apply (QuotientGroup.eq_one_iff (h * g)).mpr
        simp [zassenhaus_one_top]
      exact hl.trans hr'.symm
  | succ k =>
      exact zassenhaus_layer_comm p G (Nat.succ_pos k) hq hr

/-- Every layer has exponent `p` for prime `p`; at index zero this is again
trivial because `G/D₁` is trivial. -/
theorem zassenhaus_layer_any [Fact p.Prime] {n : ℕ}
    {q : zQuot p G (n + 1)}
    (hq : q ∈ zLKern p G n) :
    q ^ p = 1 := by
  cases n with
  | zero =>
      refine QuotientGroup.induction_on q ?_ hq
      intro g _
      change QuotientGroup.mk' (zSubgro p G 1) (g ^ p) = 1
      apply (QuotientGroup.eq_one_iff (g ^ p)).mpr
      simp [zassenhaus_one_top]
  | succ k =>
      exact zassenhaus_layer_one p G (Nat.succ_pos k) hq

/-- Each Zassenhaus layer kernel is a commutative group.  We keep the multiplicative
presentation for compatibility with quotient groups; use `Additive` for linear algebra. -/
instance instCommKernel (n : ℕ) :
    CommGroup (zLKern p G n) := by
  let base : Group (zLKern p G n) := inferInstance
  refine { base with mul_comm := ?_ }
  intro a b
  ext
  exact zassenhaus_comm_any p G a.property b.property

/-- As an additive group, a prime Zassenhaus layer is naturally a `ZMod p`-module. -/
instance instZAdditive [Fact p.Prime] (n : ℕ) :
    Module (ZMod p) (Additive (zLKern p G n)) := by
  apply AddCommGroup.zmodModule
  intro x
  cases x with
  | ofMul a =>
      change Additive.ofMul (a ^ p) = 0
      ext
      exact zassenhaus_layer_any p G a.property

/-- Natural scalars on an additive Zassenhaus layer are represented by powers. -/
@[simp] theorem nat_cast_smul [Fact p.Prime] (k n : ℕ)
    (a : zLKern p G k) :
    (n : ZMod p) • (Additive.ofMul a : Additive (zLKern p G k)) =
      Additive.ofMul (a ^ n) := by
  rw [Nat.cast_smul_eq_nsmul]
  rfl

/-- For prime `p`, the induced map on additive Zassenhaus layers is `ZMod p`-linear. -/
noncomputable def zLKern.mapLinear [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (n : ℕ) :
    Additive (zLKern p G n) →ₗ[ZMod p]
      Additive (zLKern p H n) :=
  (zLKern.mapAdd p G φ n).toZModLinearMap p

@[simp] theorem zLKern.mapLinear_apply [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.mapLinear p G φ n x =
      zLKern.mapAdd p G φ n x := rfl

@[simp] theorem zLKern.mapLinear_id [Fact p.Prime] (n : ℕ) :
    zLKern.mapLinear p G (MonoidHom.id G) n = LinearMap.id := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.mapLinear]

@[simp] theorem zLKern.mapLinear_comp [Fact p.Prime]
    {H K : Type*} [Group H] [Group K] (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zLKern.mapLinear p G (ψ.comp φ) n =
      (zLKern.mapLinear p H ψ n).comp
        (zLKern.mapLinear p G φ n) := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.mapLinear]

/-- A split epimorphism satisfying the layer kernel-intersection criterion induces a
bijective linear map on prime Zassenhaus layers. -/
theorem zLKern.map_linbij_rightinv [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    Function.Bijective (zLKern.mapLinear p G φ n) := by
  have hb : Function.Bijective (zLKern.map p G φ n) :=
    (zLKern.mapbij_iffinfker_lerightinv
      p G φ σ hσ).2 hker
  constructor
  · intro x y hxy
    cases x with
    | ofMul x' =>
      cases y with
      | ofMul y' =>
        apply congrArg Additive.ofMul
        apply hb.1
        change Additive.ofMul (zLKern.map p G φ n x') =
          Additive.ofMul (zLKern.map p G φ n y') at hxy
        exact congrArg Additive.toMul hxy
  · intro y
    cases y with
    | ofMul y' =>
      rcases hb.2 y' with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- The corresponding linear equivalence on prime Zassenhaus layers for a split
epimorphism satisfying the kernel-intersection criterion. -/
noncomputable def zLKern.rinvLinearEquiv [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    Additive (zLKern p G n) ≃ₗ[ZMod p]
      Additive (zLKern p H n) :=
  LinearEquiv.ofBijective (zLKern.mapLinear p G φ n)
    (zLKern.map_linbij_rightinv p G φ σ hσ hker)

@[simp] theorem zLKern.rinvEquiv_apply [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) {n : ℕ}
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1))
    (x : Additive (zLKern p G n)) :
    zLKern.rinvLinearEquiv p G φ σ hσ hker x =
      zLKern.mapLinear p G φ n x := rfl


/-- An automorphism of `G` induces a linear automorphism of each prime Zassenhaus layer. -/
noncomputable def zLKern.congrLinear [Fact p.Prime]
    (e : MulAut G) (n : ℕ) :
    Additive (zLKern p G n) ≃ₗ[ZMod p]
      Additive (zLKern p G n) :=
{ zLKern.mapLinear p G e.toMonoidHom n with
  invFun := zLKern.mapLinear p G e.symm.toMonoidHom n
  left_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul y =>
        apply congrArg Additive.ofMul
        change zLKern.map p G e.symm.toMonoidHom n
            (zLKern.map p G e.toMonoidHom n y) = y
        have h := congrArg
          (fun f : zLKern p G n →* zLKern p G n => f y)
          (zLKern.map_comp (p := p) (G := G)
            e.toMonoidHom e.symm.toMonoidHom n)
        change zLKern.map p G (e.symm.toMonoidHom.comp e.toMonoidHom) n y = _ at h
        simpa using h.symm
  right_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul y =>
        apply congrArg Additive.ofMul
        change zLKern.map p G e.toMonoidHom n
            (zLKern.map p G e.symm.toMonoidHom n y) = y
        have h := congrArg
          (fun f : zLKern p G n →* zLKern p G n => f y)
          (zLKern.map_comp (p := p) (G := G)
            e.symm.toMonoidHom e.toMonoidHom n)
        change zLKern.map p G (e.toMonoidHom.comp e.symm.toMonoidHom) n y = _ at h
        simpa using h.symm }

/-- Additive version of the equivalence between the first layer kernel and `G/D₂`. -/
def zassenhausAddEquiv :
    Additive (zLKern p G 1) ≃+ zTAdditi p G :=
  MulEquiv.toAdditive (zassenhausLayerEquiv p G)

/-- For prime `p`, the first-layer equivalence is `ZMod p`-linear. -/
noncomputable def zassenhausLinearEquiv [Fact p.Prime] :
    Additive (zLKern p G 1) ≃ₗ[ZMod p]
      zTAdditi p G :=
  LinearEquiv.ofBijective
    ((zassenhausAddEquiv p G).toAddMonoidHom.toZModLinearMap p) <| by
      constructor
      · intro x y h
        exact (zassenhausAddEquiv p G).injective h
      · intro y
        rcases (zassenhausAddEquiv p G).surjective y with ⟨x, hx⟩
        exact ⟨x, hx⟩

/-- The first-layer equivalence is natural for homomorphisms of groups. -/
theorem zassenhaus_linear_naturality [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) :
    (zassenhausLinearEquiv p H).toLinearMap.comp
        (zLKern.mapLinear p G φ 1) =
      (zTAdditi.mapLinear p G φ).comp
        (zassenhausLinearEquiv p G).toLinearMap := by
  ext x
  induction x using Additive.rec with
  | ofMul y =>
      rfl

/-- The mod-`p` Zassenhaus filtration as a restricted N-series (for prime `p`). -/
def restrictedNSeries [Fact p.Prime] : RNSeries p G where
  term := zSubgro p G
  antitone' := zassenhausSubgroup_antitone p G
  normal' := zassenhausSubgroup_normal p G
  one_eq_top' := zassenhaus_one_top p G
  commutator_le' := by
    intro m n hm hn
    exact commutator_zassenhaus_add p G hm hn
  pow_mem' := by
    intro n g hg
    exact pow_subgroup_self (p := p) (G := G) hg

@[simp] theorem restricted_n_term [Fact p.Prime] (n : ℕ) :
    (restrictedNSeries p G) n = zSubgro p G n := rfl

/-- Consecutive Zassenhaus term quotients are abelian for prime `p`. -/
theorem next_mul_comm [Fact p.Prime] (n : ℕ)
    (a b : zSubgro p G n ⧸ zNTerm p G n) :
    a * b = b * a :=
  RNSeries.next_quotient_comm (restrictedNSeries p G) n a b

/-- A commutative group structure on `Dₙ/Dₙ₊₁` for the prime Zassenhaus series. -/
noncomputable instance zNQuot.commGroup [Fact p.Prime] (n : ℕ) :
    CommGroup (zSubgro p G n ⧸ zNTerm p G n) :=
{ (inferInstance : Group (zSubgro p G n ⧸ zNTerm p G n)) with
  mul_comm := next_mul_comm p G n }

/-- Consecutive Zassenhaus term quotients have exponent `p` for prime `p`. -/
theorem zassenhaus_next_one [Fact p.Prime] (n : ℕ)
    (a : zSubgro p G n ⧸ zNTerm p G n) :
    a ^ p = 1 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le (Fact.out)
  exact RNSeries.next_quotient_two
    (restrictedNSeries p G) hp2 n a

/-- The additive group of `Dₙ/Dₙ₊₁` is naturally a `ZMod p`-module. -/
noncomputable instance instZNext [Fact p.Prime]
    (n : ℕ) : Module (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  apply AddCommGroup.zmodModule
  intro x
  cases x with
  | ofMul a =>
      change Additive.ofMul (a ^ p) = 0
      ext
      exact zassenhaus_next_one p G n a

/-- The induced map on additive consecutive Zassenhaus quotients is `ZMod p`-linear. -/
noncomputable def zNQuot.mapLinear [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (n : ℕ) :
    Additive (zSubgro p G n ⧸ zNTerm p G n) →ₗ[ZMod p]
      Additive (zSubgro p H n ⧸ zNTerm p H n) :=
  (zNQuot.map p G φ n).toAdditive.toZModLinearMap p

@[simp] theorem zNQuot.mapLinear_apply [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (n : ℕ)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.mapLinear p G φ n x =
      (zNQuot.map p G φ n).toAdditive x := rfl

@[simp] theorem zNQuot.mapLinear_id [Fact p.Prime] (n : ℕ) :
    zNQuot.mapLinear p G (MonoidHom.id G) n = LinearMap.id := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.mapLinear]

@[simp] theorem zNQuot.mapLinear_comp [Fact p.Prime]
    {H K : Type*} [Group H] [Group K] (φ : G →* H) (ψ : H →* K) (n : ℕ) :
    zNQuot.mapLinear p G (ψ.comp φ) n =
      (zNQuot.mapLinear p H ψ n).comp
        (zNQuot.mapLinear p G φ n) := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.mapLinear]

/-- A group isomorphism induces a linear equivalence on prime consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.congrLinear [Fact p.Prime]
    {H : Type*} [Group H] (e : G ≃* H) (n : ℕ) :
    Additive (zSubgro p G n ⧸ zNTerm p G n) ≃ₗ[ZMod p]
      Additive (zSubgro p H n ⧸ zNTerm p H n) :=
{ zNQuot.mapLinear p G e.toMonoidHom n with
  invFun := zNQuot.mapLinear p H e.symm.toMonoidHom n
  left_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        apply congrArg Additive.ofMul
        change zNQuot.map p H e.symm.toMonoidHom n
            (zNQuot.map p G e.toMonoidHom n q) = q
        exact (zNQuot.congr p G e n).left_inv q
  right_inv := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
        apply congrArg Additive.ofMul
        change zNQuot.map p G e.toMonoidHom n
            (zNQuot.map p H e.symm.toMonoidHom n q) = q
        exact (zNQuot.congr p G e n).right_inv q }

@[simp] theorem zNQuot.congrLinear_apply [Fact p.Prime]
    {H : Type*} [Group H] (e : G ≃* H) (n : ℕ)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G e n x =
      zNQuot.mapLinear p G e.toMonoidHom n x := rfl

/-- The concrete quotient-to-layer equivalence is linear over `ZMod p`. -/
noncomputable def zLKern.next_quot_linequiv [Fact p.Prime] (n : ℕ) :
    Additive (zSubgro p G n ⧸ zNTerm p G n) ≃ₗ[ZMod p]
      Additive (zLKern p G n) :=
  let e := MulEquiv.toAdditive (zLKern.nextQuotientEquiv p G n)
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) <| by
    constructor
    · intro x y h
      exact e.injective h
    · intro y
      rcases e.surjective y with ⟨x, hx⟩
      exact ⟨x, hx⟩

/-- Naturality of the linear equivalence from `Dₙ/Dₙ₊₁` to the layer kernel. -/
theorem zLKern.next_quotlin_equivnatural [Fact p.Prime]
    {H : Type*} [Group H] (φ : G →* H) (n : ℕ) :
    (zLKern.next_quot_linequiv p H n).toLinearMap.comp
        (zNQuot.mapLinear p G φ n) =
      (zLKern.mapLinear p G φ n).comp
        (zLKern.next_quot_linequiv p G n).toLinearMap := by
  ext x
  cases x with
  | ofMul q =>
      simp [zLKern.next_quot_linequiv,
        zNQuot.mapLinear, zLKern.mapLinear,
        zLKern.next_quot_equivnatural]

end
end GroupAlgebra
end Towers
