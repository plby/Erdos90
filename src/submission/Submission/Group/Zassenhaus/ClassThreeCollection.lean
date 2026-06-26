import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.ClassTwoCollection
import Submission.Group.Zassenhaus.ClassTwo

/-!
# Finite class-three power collection

At cutoff four, triple commutators are central.  This file records the first
class-three repeated-power identity: an explicit Hall-Petresco expansion for
the power of a product of two elements.

The correction exponents remain in the binomial language used by the
symbolic Hall-power collector.  In particular, the left triple correction has
multiplicity `choose q 2 + 2 * choose q 3`.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace cPFactor

/-- The multiplicity of the left triple correction in `(x * y) ^ q`. -/
def leftTripleMultiplicity
    (q : ℕ) :
    ℕ :=
  Nat.choose q 2 + 2 * Nat.choose q 3

/-- Pascal's identity for the degree-two natural binomial coefficient. -/
lemma choose_add_one
    (q : ℕ) :
    Nat.choose (q + 1) 2 = Nat.choose q 2 + q := by
  rw [show q + 1 = Nat.succ q by omega,
    show 2 = Nat.succ 1 by omega, Nat.choose_succ_succ,
    Nat.choose_one_right, Nat.add_comm]

/-- Pascal's identity for the degree-three natural binomial coefficient. -/
lemma choose_add_three
    (q : ℕ) :
    Nat.choose (q + 1) 3 = Nat.choose q 3 + Nat.choose q 2 := by
  rw [show q + 1 = Nat.succ q by omega,
    show 3 = Nat.succ 2 by omega, Nat.choose_succ_succ, Nat.add_comm]

/-- The square increment is the first two layers of Pascal's triangle. -/
lemma sq_self_choose
    (q : ℕ) :
    q * q = q + 2 * Nat.choose q 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [choose_add_one]
      calc
        (q + 1) * (q + 1) =
            q * q + 2 * q + 1 := by ring
        _ = (q + 2 * Nat.choose q 2) + 2 * q + 1 := by rw [ih]
        _ = (q + 1) + 2 * (Nat.choose q 2 + q) := by omega

/-- The left triple multiplicity has square successive difference. -/
lemma left_triple_multiplicity
    (q : ℕ) :
    leftTripleMultiplicity (q + 1) =
      leftTripleMultiplicity q + q * q := by
  rw [leftTripleMultiplicity, leftTripleMultiplicity,
    choose_add_one, choose_add_three,
    sq_self_choose]
  omega

/--
At cutoff at most four, powers of a two-factor product have an explicit
class-three Hall-Petresco expansion.
-/
lemma mul_pow_eq
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (q : ℕ) :
    (x * y) ^ q =
      ⁅x, ⁅y, x⁆⁆ ^ leftTripleMultiplicity q *
        ⁅y, ⁅y, x⁆⁆ ^ Nat.choose q 3 *
          ⁅y, x⁆ ^ Nat.choose q 2 *
            x ^ q * y ^ q := by
  let C := ⁅y, x⁆
  let D := ⁅x, C⁆
  let E := ⁅y, C⁆
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hC :
      C ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [C] using element_lower_series hy hx
  have hD :
      D ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [D] using element_lower_series hx hC
  have hE :
      E ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [E] using element_lower_series hy hC
  have hcentralD :
      ∀ z :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        Commute z D :=
    fun z =>
      HCThree.commute_series_four
        hn4 z hD
  have hcentralE :
      ∀ z :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        Commute z E :=
    fun z =>
      HCThree.commute_series_four
        hn4 z hE
  have hyPowSwap :
      ∀ q : ℕ,
        y ^ q * x = E ^ Nat.choose q 2 * C ^ q * x * y ^ q := by
    intro q
    have hcommutator :
        ⁅y ^ q, x⁆ = E ^ Nat.choose q 2 * C ^ q := by
      simpa only [Int.ofNat_eq_natCast, Ring.choose_natCast, zpow_natCast]
        using
          (HCThree.commutator_element_zpow
            y x (hcentralE y) (hcentralE C) (q : ℤ))
    calc
      y ^ q * x = ⁅y ^ q, x⁆ * x * y ^ q := by
        simp only [commutatorElement_def]
        group
      _ = E ^ Nat.choose q 2 * C ^ q * x * y ^ q := by
        rw [hcommutator]
  have hxPowCPowSwap :
      ∀ q : ℕ,
        x ^ q * C ^ q = D ^ (q * q) * C ^ q * x ^ q := by
    intro q
    have hleft :
        ⁅x ^ q, C⁆ = D ^ q := by
      simpa [D] using
        (element_left_commute (hcentralD x) q)
    have hright :
        Commute C ⁅x ^ q, C⁆ := by
      rw [hleft]
      exact (hcentralD C).pow_right q
    have hcommutator :
        ⁅x ^ q, C ^ q⁆ = D ^ (q * q) := by
      calc
        ⁅x ^ q, C ^ q⁆ = ⁅x ^ q, C⁆ ^ q :=
          commutator_element_commute hright q
        _ = (D ^ q) ^ q := by rw [hleft]
        _ = D ^ (q * q) := by rw [pow_mul]
    calc
      x ^ q * C ^ q = ⁅x ^ q, C ^ q⁆ * C ^ q * x ^ q := by
        simp only [commutatorElement_def]
        group
      _ = D ^ (q * q) * C ^ q * x ^ q := by
        rw [hcommutator]
  induction q with
  | zero =>
      simp [leftTripleMultiplicity]
  | succ q ih =>
      rw [pow_succ, ih]
      change
        D ^ leftTripleMultiplicity q *
                E ^ Nat.choose q 3 *
                  C ^ Nat.choose q 2 *
                    x ^ q * y ^ q * (x * y) =
          D ^ leftTripleMultiplicity (q + 1) *
              E ^ Nat.choose (q + 1) 3 *
                C ^ Nat.choose (q + 1) 2 *
                  x ^ (q + 1) * y ^ (q + 1)
      calc
        D ^ leftTripleMultiplicity q *
                E ^ Nat.choose q 3 *
                  C ^ Nat.choose q 2 *
                    x ^ q * y ^ q * (x * y) =
            D ^ leftTripleMultiplicity q *
                E ^ Nat.choose q 3 *
                  C ^ Nat.choose q 2 *
                    x ^ q *
                      (E ^ Nat.choose q 2 * C ^ q * x * y ^ q) * y := by
              rw [← hyPowSwap q]
              group
        _ =
            D ^ leftTripleMultiplicity q *
                E ^ (Nat.choose q 3 + Nat.choose q 2) *
                  C ^ Nat.choose q 2 *
                    (x ^ q * C ^ q) * x * (y ^ q * y) := by
              rw [pow_add]
              calc
                D ^ leftTripleMultiplicity q *
                        E ^ Nat.choose q 3 *
                          C ^ Nat.choose q 2 *
                            x ^ q *
                              (E ^ Nat.choose q 2 * C ^ q * x * y ^ q) * y =
                    D ^ leftTripleMultiplicity q *
                        E ^ Nat.choose q 3 *
                          C ^ Nat.choose q 2 *
                            (x ^ q * E ^ Nat.choose q 2) *
                              C ^ q * x * y ^ q * y := by
                          group
                _ =
                    D ^ leftTripleMultiplicity q *
                        E ^ Nat.choose q 3 *
                          C ^ Nat.choose q 2 *
                            (E ^ Nat.choose q 2 * x ^ q) *
                              C ^ q * x * y ^ q * y := by
                          rw [((hcentralE (x ^ q)).pow_right
                            (Nat.choose q 2)).eq]
                _ =
                    D ^ leftTripleMultiplicity q *
                        E ^ Nat.choose q 3 *
                          (C ^ Nat.choose q 2 * E ^ Nat.choose q 2) *
                            (x ^ q * C ^ q) * x * (y ^ q * y) := by
                          group
                _ =
                    D ^ leftTripleMultiplicity q *
                        E ^ Nat.choose q 3 *
                          (E ^ Nat.choose q 2 * C ^ Nat.choose q 2) *
                            (x ^ q * C ^ q) * x * (y ^ q * y) := by
                          rw [((hcentralE (C ^ Nat.choose q 2)).pow_right
                            (Nat.choose q 2)).eq]
                _ =
                    D ^ leftTripleMultiplicity q *
                        (E ^ Nat.choose q 3 * E ^ Nat.choose q 2) *
                          C ^ Nat.choose q 2 *
                            (x ^ q * C ^ q) * x * (y ^ q * y) := by
                          group
        _ =
            D ^ leftTripleMultiplicity q *
                E ^ (Nat.choose q 3 + Nat.choose q 2) *
                  C ^ Nat.choose q 2 *
                    (D ^ (q * q) * C ^ q * x ^ q) *
                      x * (y ^ q * y) := by
              rw [hxPowCPowSwap q]
        _ =
            D ^ (leftTripleMultiplicity q + q * q) *
                E ^ (Nat.choose q 3 + Nat.choose q 2) *
                  C ^ (Nat.choose q 2 + q) *
                    x ^ (q + 1) * y ^ (q + 1) := by
              calc
                D ^ leftTripleMultiplicity q *
                        E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          C ^ Nat.choose q 2 *
                            (D ^ (q * q) * C ^ q * x ^ q) *
                              x * (y ^ q * y) =
                    D ^ leftTripleMultiplicity q *
                        E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          (C ^ Nat.choose q 2 * D ^ (q * q)) *
                            C ^ q * x ^ q * x * (y ^ q * y) := by
                          group
                _ =
                    D ^ leftTripleMultiplicity q *
                        E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          (D ^ (q * q) * C ^ Nat.choose q 2) *
                            C ^ q * x ^ q * x * (y ^ q * y) := by
                          rw [((hcentralD (C ^ Nat.choose q 2)).pow_right
                            (q * q)).eq]
                _ =
                    D ^ leftTripleMultiplicity q *
                        (E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          D ^ (q * q)) *
                            C ^ Nat.choose q 2 * C ^ q *
                              (x ^ q * x) * (y ^ q * y) := by
                          group
                _ =
                    D ^ leftTripleMultiplicity q *
                        (D ^ (q * q) *
                          E ^ (Nat.choose q 3 + Nat.choose q 2)) *
                            C ^ Nat.choose q 2 * C ^ q *
                              (x ^ q * x) * (y ^ q * y) := by
                          rw [((hcentralD
                            (E ^ (Nat.choose q 3 + Nat.choose q 2))).pow_right
                              (q * q)).eq]
                _ =
                    D ^ leftTripleMultiplicity q * D ^ (q * q) *
                        E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          (C ^ Nat.choose q 2 * C ^ q) *
                            (x ^ q * x) * (y ^ q * y) := by
                          group
                _ =
                    D ^ (leftTripleMultiplicity q + q * q) *
                        E ^ (Nat.choose q 3 + Nat.choose q 2) *
                          C ^ (Nat.choose q 2 + q) *
                            x ^ (q + 1) * y ^ (q + 1) := by
                          rw [← pow_add, ← pow_add, ← pow_succ, ← pow_succ]
        _ =
            D ^ leftTripleMultiplicity (q + 1) *
                E ^ Nat.choose (q + 1) 3 *
                  C ^ Nat.choose (q + 1) 2 *
                    x ^ (q + 1) * y ^ (q + 1) := by
              rw [left_triple_multiplicity,
                choose_add_three, choose_add_one]

/--
The recursive finite class-three factor list.  The tail-product commutators
remain grouped at this value-level boundary; a symbolic Hall-word source can
expand them separately.
-/
def factors
    {G : Type*}
    [Group G]
    (q : ℕ) :
    List G → List G
  | [] => []
  | x :: L =>
      [⁅x, ⁅L.prod, x⁆⁆ ^ leftTripleMultiplicity q,
        ⁅L.prod, ⁅L.prod, x⁆⁆ ^ Nat.choose q 3,
        ⁅L.prod, x⁆ ^ Nat.choose q 2,
        x ^ q] ++
          factors q L

/--
At cutoff at most four, the recursive finite class-three factor list
evaluates to the power of the original ordered product.
-/
lemma factors_prod_pow
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (q : ℕ) :
    ∀ L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      (factors q L).prod = L.prod ^ q := by
  intro L
  induction L with
  | nil =>
      simp [factors]
  | cons x L ih =>
      simp only [factors, List.prod_append, List.prod_cons, List.prod_nil,
        mul_one, ih]
      simpa only [mul_assoc] using (mul_pow_eq hn4 x L.prod q).symm

end cPFactor

end TCTex
end Submission

/-!
# Central multilinearity for class-three power collection

At cutoff four, triple commutators are central.  This file records the
list-product expansions that flatten a triple commutator once either nested
input is already an atomic pair commutator.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace cPFactor

/--
If every individual commutator with one fixed left input is central, then the
commutator with a raw list product is the product of those individual
commutators in the original list order.
-/
lemma element_forall_center
    {G : Type u} [Group G]
    (g : G)
    (L : List G)
    (hL : ∀ x ∈ L, ⁅g, x⁆ ∈ Subgroup.center G) :
    ⁅g, L.prod⁆ = (L.map fun x => ⁅g, x⁆).prod := by
  induction L with
  | nil =>
      simp
  | cons x L ih =>
      have htail :
          ∀ y ∈ L, ⁅g, y⁆ ∈ Subgroup.center G := by
        intro y hy
        exact hL y (by simp [hy])
      have htailProdCenter :
          (L.map fun y => ⁅g, y⁆).prod ∈ Subgroup.center G := by
        apply Subgroup.list_prod_mem
        intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact htail z hz
      have hconj :
          x * (L.map fun y => ⁅g, y⁆).prod * x⁻¹ =
            (L.map fun y => ⁅g, y⁆).prod := by
        rw [Subgroup.mem_center_iff.mp htailProdCenter x, mul_inv_cancel_right]
      rw [List.prod_cons, element_mul_right, ih htail,
        List.map_cons, List.prod_cons]
      calc
        ⁅g, x⁆ * x * (L.map fun y => ⁅g, y⁆).prod * x⁻¹ =
            ⁅g, x⁆ * (x * (L.map fun y => ⁅g, y⁆).prod * x⁻¹) := by
              group
        _ = ⁅g, x⁆ * (L.map fun y => ⁅g, y⁆).prod := by
              rw [hconj]

/--
Triple commutators are central in every free lower-central truncation with
cutoff at most four.
-/
lemma triple_center_four
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y z :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅x, ⁅y, z⁆⁆ ∈
      Subgroup.center
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hz :
      z ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hyz :
      ⁅y, z⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using element_lower_series hy hz
  have hxyz :
      ⁅x, ⁅y, z⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hx hyz
  rw [Subgroup.mem_center_iff]
  intro a
  exact
    (HCThree.commute_series_four
      hn4 a hxyz).eq

/-- Expand a triple commutator whose outer left input is a list product. -/
lemma element_prod_pair
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅L.prod, ⁅x, y⁆⁆ =
      (L.map fun z => ⁅z, ⁅x, y⁆⁆).prod := by
  apply commutator_forall_center
  intro z hz
  exact triple_center_four hn4 z x y

/-- Expand a triple commutator whose outer right input is a list product. -/
lemma commutator_element_pair
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)) :
    ⁅⁅x, y⁆, L.prod⁆ =
      (L.map fun z => ⁅⁅x, y⁆, z⁆).prod := by
  apply element_forall_center
  intro z hz
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hz' :
      z ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using element_lower_series hx hy
  have hxyz :
      ⁅⁅x, y⁆, z⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hxy hz'
  rw [Subgroup.mem_center_iff]
  intro a
  exact
    (HCThree.commute_series_four
      hn4 a hxyz).eq

/--
Expand the pair commutator of a list product with one fixed right input.
The correction triples precede the recursively expanded pair factors.
-/
def leftPairFactors
    {G : Type*}
    [Group G]
    (x : G) :
    List G → List G
  | [] => []
  | y :: L =>
      (L.reverse.map fun z => ⁅y, ⁅z, x⁆⁆) ++
        leftPairFactors x L ++ [⁅y, x⁆]

/--
At cutoff four, the nested bracket with a pair commutator of a list product
is additive over the reversed list.
-/
lemma element_nested_reverse
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∀ (L :
        List
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
      (x :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      ⁅y, ⁅L.prod, x⁆⁆ =
        (L.reverse.map fun z => ⁅y, ⁅z, x⁆⁆).prod := by
  intro L
  induction L with
  | nil =>
      intro x
      simp
  | cons z L ih =>
      intro x
      let T := ⁅z, ⁅L.prod, x⁆⁆
      let A := ⁅L.prod, x⁆
      let B := ⁅z, x⁆
      have hTCenter :
          T ∈
            Subgroup.center
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
        exact triple_center_four hn4 z L.prod x
      have hyTOne :
          ⁅y, T⁆ = 1 := by
        apply commutatorElement_eq_one_iff_commute.mpr
        exact Subgroup.mem_center_iff.mp hTCenter y
      have hyTCenter :
          ⁅y, T⁆ ∈
            Subgroup.center
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
        rw [hyTOne]
        exact Subgroup.one_mem _
      have hyACenter :
          ⁅y, A⁆ ∈
            Subgroup.center
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
        exact triple_center_four hn4 y L.prod x
      have hyBCenter :
          ⁅y, B⁆ ∈
            Subgroup.center
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
        exact triple_center_four hn4 y z x
      have hsplit :
          ⁅y, T * (A * B)⁆ = ⁅y, T⁆ * (⁅y, A⁆ * ⁅y, B⁆) := by
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one] using
          (element_forall_center
            y [T, A, B] (by
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl | rfl
              · exact hyTCenter
              · exact hyACenter
              · exact hyBCenter))
      have hconj :
          z * A * z⁻¹ = T * A := by
        simp only [T, A, commutatorElement_def]
        group
      rw [List.prod_cons, element_mul_left, hconj]
      change ⁅y, T * A * B⁆ =
        ((z :: L).reverse.map fun w => ⁅y, ⁅w, x⁆⁆).prod
      rw [show T * A * B = T * (A * B) by group,
        hsplit, hyTOne, one_mul, ih]
      simp [List.reverse_cons, List.map_append, List.prod_append, B]

/--
At cutoff four, `leftPairFactors` evaluates to the pair commutator of
the original list product.
-/
lemma pair_factors_prod
    {d n : ℕ}
    (hn4 : n ≤ 4) :
    ∀ (L :
        List
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
      (x :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      (leftPairFactors x L).prod = ⁅L.prod, x⁆ := by
  intro L
  induction L with
  | nil =>
      intro x
      simp [leftPairFactors]
  | cons y L ih =>
      intro x
      simp only [leftPairFactors, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one]
      rw [ih, ← element_nested_reverse
        hn4 y L x]
      simp only [commutatorElement_def]
      group

/-- Every flattened pair factor remains in the second one-based lower-central layer. -/
lemma left_pair_factors
    {d n : ℕ}
    {x factor :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n} :
    ∀ {L :
        List
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)},
      factor ∈ leftPairFactors x L →
        factor ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
  intro L hfactor
  induction L with
  | nil =>
      simp [leftPairFactors] at hfactor
  | cons y L ih =>
      change factor ∈
        ((L.reverse.map fun z => ⁅y, ⁅z, x⁆⁆) ++
          leftPairFactors x L) ++ [⁅y, x⁆] at hfactor
      rcases List.mem_append.mp hfactor with hfactor | hfactor
      · rcases List.mem_append.mp hfactor with hfactor | hfactor
        · rcases List.mem_map.mp hfactor with ⟨z, hz, rfl⟩
          have hy :
              y ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
            simp
          have hz' :
              z ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
            simp
          have hx :
              x ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
            simp
          have hzx :
              ⁅z, x⁆ ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
            simpa using element_lower_series hz' hx
          have hyzx :
              ⁅y, ⁅z, x⁆⁆ ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
            simpa using element_lower_series hy hzx
          exact Subgroup.lowerCentralSeries_antitone (by omega) hyzx
        · exact ih hfactor
      · simp only [List.mem_singleton] at hfactor
        subst factor
        have hy :
            y ∈ Subgroup.lowerCentralSeries
              (LowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
          simp
        have hx :
            x ∈ Subgroup.lowerCentralSeries
              (LowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
          simp
        simpa using element_lower_series hy hx

/--
Every commutator of a raw list product with one flattened pair factor is
central at cutoff four.
-/
lemma element_pair_center
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (M :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    {x factor :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    {L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)}
    (hfactor : factor ∈ leftPairFactors x L) :
    ⁅M.prod, factor⁆ ∈
      Subgroup.center
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
  have hM :
      M.prod ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hfactor' :
      factor ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 :=
    left_pair_factors hfactor
  have hbracket :
      ⁅M.prod, factor⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hM hfactor'
  rw [Subgroup.mem_center_iff]
  intro a
  exact
    (HCThree.commute_series_four
      hn4 a hbracket).eq

/-- A raw list product commutes with every central triple commutator. -/
lemma element_prod_triple
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (M :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (y z x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅M.prod, ⁅y, ⁅z, x⁆⁆⁆ = 1 := by
  apply commutatorElement_eq_one_iff_commute.mpr
  exact
    Subgroup.mem_center_iff.mp
      (triple_center_four hn4 y z x) M.prod

/-- A list of outer commutators with central triple factors multiplies to one. -/
lemma list_element_triple
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (M :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (y x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∀ L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      (L.map fun z => ⁅M.prod, ⁅y, ⁅z, x⁆⁆⁆).prod = 1 := by
  intro L
  induction L with
  | nil =>
      simp
  | cons z L ih =>
      simp [element_prod_triple hn4 M y z x, ih]

/--
Flatten an outer list-product commutator with the atomic pair-factor expansion
of an inner list-product commutator.
-/
lemma commutator_element_factors
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (M :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)) :
    ∀ (L :
        List
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
      (x :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      ⁅M.prod, (leftPairFactors x L).prod⁆ =
        (L.reverse.flatMap fun z =>
          M.map fun y => ⁅y, ⁅z, x⁆⁆).prod := by
  intro L
  induction L with
  | nil =>
      intro x
      simp [leftPairFactors]
  | cons z L ih =>
      intro x
      rw [element_forall_center
        M.prod (leftPairFactors x (z :: L)) (by
          intro factor hfactor
          exact
            element_pair_center
              hn4 M hfactor)]
      simp only [leftPairFactors, List.map_append, List.prod_append,
        List.map_map, Function.comp_def, List.map_singleton, List.prod_cons,
        List.prod_nil, mul_one, List.reverse_cons, List.flatMap_append,
        List.flatMap_singleton]
      rw [list_element_triple hn4 M z x L.reverse,
        one_mul,
        ← element_forall_center
          M.prod (leftPairFactors x L) (by
            intro factor hfactor
            exact
              element_pair_center
                hn4 M hfactor),
        ih x,
        element_prod_pair hn4 M z x]

/-- Fully flatten the double list-product triple correction in the finite power collector. -/
lemma nested_self_flat
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅L.prod, ⁅L.prod, x⁆⁆ =
      (L.reverse.flatMap fun z =>
        L.map fun y => ⁅y, ⁅z, x⁆⁆).prod := by
  rw [← pair_factors_prod hn4 L x]
  exact
    commutator_element_factors
      hn4 L L x

end cPFactor

end TCTex
end Submission

/-!
# Atomic finite class-three power collection

The value-level class-three collector initially retains commutators involving
tail products.  This file expands those grouped commutators into finite lists
of atomic pair and triple commutators.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace cPFactor

/--
Elements of the second one-based lower-central layer commute at cutoff at most
four: their bracket lands in the vanishing fourth one-based layer.
-/
lemma commute_n_four
    {d n : ℕ}
    (hn4 : n ≤ 4)
    {x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1) :
    Commute x y := by
  have hbracket :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 3 := by
    simpa using element_lower_series hx hy
  rw [← commutatorElement_eq_one_iff_commute]
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega) hbracket

/-- Powers distribute over lists contained in the second one-based lower-central layer. -/
lemma list_prod_series
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (q : ℕ)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (hL :
      ∀ x ∈ L,
        x ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1) :
    L.prod ^ q = (L.map fun x => x ^ q).prod := by
  let S :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1
  letI : IsMulCommutative S :=
    cTFactor.mul_commutative_commute S S le_rfl
      (fun hx hy =>
        commute_n_four hn4 hx hy)
  exact cTFactor.list_prod_pow S q L hL

/-- Every atomic triple commutator belongs to the second one-based lower-central layer. -/
lemma triple_element_series
    {d n : ℕ}
    (x y z :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅x, ⁅y, z⁆⁆ ∈ Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hz :
      z ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hyz :
      ⁅y, z⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using element_lower_series hy hz
  have hxyz :
      ⁅x, ⁅y, z⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hx hyz
  exact Subgroup.lowerCentralSeries_antitone (by omega) hxyz

/-- Fully atomic finite factors for the class-three power of an ordered list product. -/
def atomicFactors
    {G : Type*}
    [Group G]
    (q : ℕ) :
    List G → List G
  | [] => []
  | x :: L =>
      (L.reverse.map fun z =>
        ⁅x, ⁅z, x⁆⁆ ^ leftTripleMultiplicity q) ++
      (L.reverse.flatMap fun z =>
        L.map fun y => ⁅y, ⁅z, x⁆⁆ ^ Nat.choose q 3) ++
      ((leftPairFactors x L).map fun factor =>
        factor ^ Nat.choose q 2) ++
      [x ^ q] ++ atomicFactors q L

/-- The fully atomic factor list evaluates to the grouped finite class-three collector. -/
lemma atomic_factors_prod
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (q : ℕ) :
    ∀ L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      (atomicFactors q L).prod = (factors q L).prod := by
  intro L
  induction L with
  | nil =>
      simp [atomicFactors, factors]
  | cons x L ih =>
      have hleft :
          ∀ factor ∈ (L.reverse.map fun z => ⁅x, ⁅z, x⁆⁆),
            factor ∈ Subgroup.lowerCentralSeries
              (LowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
        intro factor hfactor
        rcases List.mem_map.mp hfactor with ⟨z, hz, rfl⟩
        exact triple_element_series x z x
      have hdouble :
          ∀ factor ∈ (L.reverse.flatMap fun z =>
              L.map fun y => ⁅y, ⁅z, x⁆⁆),
            factor ∈ Subgroup.lowerCentralSeries
              (LowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
        intro factor hfactor
        rcases List.mem_flatMap.mp hfactor with ⟨z, hz, hfactor⟩
        rcases List.mem_map.mp hfactor with ⟨y, hy, rfl⟩
        exact triple_element_series y z x
      have hpair :
          ∀ factor ∈ leftPairFactors x L,
            factor ∈ Subgroup.lowerCentralSeries
              (LowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
        intro factor hfactor
        exact left_pair_factors hfactor
      have hleftPow :
          (L.reverse.map fun z =>
              ⁅x, ⁅z, x⁆⁆ ^ leftTripleMultiplicity q).prod =
            (L.reverse.map fun z => ⁅x, ⁅z, x⁆⁆).prod ^
              leftTripleMultiplicity q := by
        simpa only [List.map_map, Function.comp_def] using
          (list_prod_series
            hn4 (leftTripleMultiplicity q)
            (L.reverse.map fun z => ⁅x, ⁅z, x⁆⁆) hleft).symm
      have hdoublePow :
          (L.reverse.flatMap fun z =>
              L.map fun y => ⁅y, ⁅z, x⁆⁆ ^ Nat.choose q 3).prod =
            (L.reverse.flatMap fun z =>
              L.map fun y => ⁅y, ⁅z, x⁆⁆).prod ^ Nat.choose q 3 := by
        simpa only [List.map_flatMap, List.map_map, Function.comp_def] using
          (list_prod_series
            hn4 (Nat.choose q 3)
            (L.reverse.flatMap fun z =>
              L.map fun y => ⁅y, ⁅z, x⁆⁆) hdouble).symm
      have hpairPow :
          ((leftPairFactors x L).map fun factor =>
              factor ^ Nat.choose q 2).prod =
            (leftPairFactors x L).prod ^ Nat.choose q 2 := by
        exact
          (list_prod_series
            hn4 (Nat.choose q 2) (leftPairFactors x L) hpair).symm
      simp only [atomicFactors, factors, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, ih]
      rw [hleftPow,
        ← element_nested_reverse
            hn4 x L x,
        hdoublePow,
        ← nested_self_flat
            hn4 L x,
        hpairPow,
        pair_factors_prod hn4 L x]
      group

/-- The fully atomic finite class-three factor list evaluates to the powered original product. -/
lemma atomic_factors_pow
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (q : ℕ)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)) :
    (atomicFactors q L).prod = L.prod ^ q := by
  rw [atomic_factors_prod hn4 q L]
  exact factors_prod_pow hn4 q L

end cPFactor

end TCTex
end Submission

/-!
# Symbolic atomic class-three power sources

This file starts the symbolic lift of the atomic finite class-three power
collector.  Its first bridge is exact integral trilinearity of a triple
commutator at cutoff four.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace cPFactor

/--
At cutoff four, an atomic triple commutator is exactly trilinear in arbitrary
integral powers of its three inputs.
-/
lemma triple_element_zpow
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y z :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (a b c : ℤ) :
    ⁅x ^ a, ⁅y ^ b, z ^ c⁆⁆ = ⁅x, ⁅y, z⁆⁆ ^ (a * b * c) := by
  let C := ⁅y, z⁆
  let D := ⁅y, C⁆
  let E := ⁅z, C⁆
  let T := ⁅x, C⁆
  have hDCenter :
      D ∈
        Subgroup.center
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
    exact triple_center_four hn4 y y z
  have hECenter :
      E ∈
        Subgroup.center
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
    exact triple_center_four hn4 z y z
  have hTCenter :
      T ∈
        Subgroup.center
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
    exact triple_center_four hn4 x y z
  have hinner :
      ⁅y ^ b, z ^ c⁆ =
        D ^ (Ring.choose b 2 * c) *
          C ^ (b * c) *
            E ^ (b * Ring.choose c 2) := by
    simpa [C, D, E] using
      (HCThree.element_zpow_class
        hn4 y z b c)
  have hDPowCenter :
      D ^ (Ring.choose b 2 * c) ∈
        Subgroup.center
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :=
    (Subgroup.center
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)).zpow_mem
        hDCenter _
  have hEPowCenter :
      E ^ (b * Ring.choose c 2) ∈
        Subgroup.center
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :=
    (Subgroup.center
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)).zpow_mem
        hECenter _
  have hleftSide :
      ⁅x ^ a,
        D ^ (Ring.choose b 2 * c) *
          C ^ (b * c) *
            E ^ (b * Ring.choose c 2)⁆ =
        ⁅x ^ a, C ^ (b * c)⁆ := by
    let DP := D ^ (Ring.choose b 2 * c)
    let EP := E ^ (b * Ring.choose c 2)
    have hxDP :
        Commute (x ^ a) DP :=
      Subgroup.mem_center_iff.mp hDPowCenter (x ^ a)
    have hxEP :
        Commute (x ^ a) EP :=
      Subgroup.mem_center_iff.mp hEPowCenter (x ^ a)
    have hconjDP :
        DP * ⁅x ^ a, C ^ (b * c) * EP⁆ * DP⁻¹ =
          ⁅x ^ a, C ^ (b * c) * EP⁆ := by
      rw [(Subgroup.mem_center_iff.mp hDPowCenter
        ⁅x ^ a, C ^ (b * c) * EP⁆).symm, mul_inv_cancel_right]
    have hconjC :
        C ^ (b * c) * ⁅x ^ a, EP⁆ * (C ^ (b * c))⁻¹ =
          ⁅x ^ a, EP⁆ := by
      rw [commutatorElement_eq_one_iff_commute.mpr hxEP]
      simp
    rw [show
      D ^ (Ring.choose b 2 * c) *
            C ^ (b * c) *
              E ^ (b * Ring.choose c 2) =
        DP * (C ^ (b * c) * EP) by
          simp only [DP, EP]
          group]
    rw [element_mul_right,
      commutatorElement_eq_one_iff_commute.mpr hxDP, one_mul, hconjDP,
      element_mul_right]
    calc
      ⁅x ^ a, C ^ (b * c)⁆ *
            C ^ (b * c) * ⁅x ^ a, EP⁆ * (C ^ (b * c))⁻¹ =
          ⁅x ^ a, C ^ (b * c)⁆ *
            (C ^ (b * c) * ⁅x ^ a, EP⁆ * (C ^ (b * c))⁻¹) := by
              group
      _ = ⁅x ^ a, C ^ (b * c)⁆ * ⁅x ^ a, EP⁆ := by
            rw [hconjC]
      _ = ⁅x ^ a, C ^ (b * c)⁆ := by
            rw [commutatorElement_eq_one_iff_commute.mpr hxEP, mul_one]
  have hleft :
      ⁅x ^ a, C⁆ = T ^ a := by
    apply commutator_zpow_commute
    exact Subgroup.mem_center_iff.mp hTCenter x
  have hright :
      Commute C ⁅x ^ a, C⁆ := by
    rw [hleft]
    have hCT : Commute C T :=
      Subgroup.mem_center_iff.mp hTCenter C
    exact hCT.zpow_right a
  rw [hinner, hleftSide,
    zpow_commute_collection hright,
    hleft, zpow_mul]
  simp only [T, C, zpow_mul]

end cPFactor

namespace SSAtom

/--
One selected binomial packet attached to an atomic triple commutator word.
The coefficient is left arbitrary so the same constructor can represent both
direct triple corrections and the side terms in a powered pair correction.
-/
def selectedTripleFactor
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (first second third : SSAtom H 1)
    (coefficient : ℤ)
    (k : ℕ)
    (hk : 0 < k)
    (hk3 : k ≤ 3) :
    SPFactora H 1 where
  word :=
    .commutator (.atom first.address)
      (.commutator (.atom second.address) (.atom third.address))
  coefficient := coefficient
  recipe :=
    BBRecipe.select 1
      (PEAddres.weight first.address +
        (PEAddres.weight second.address +
          PEAddres.weight third.address))
      k hk (by
        have hfirst := first.inputWeight_le
        have hsecond := second.inputWeight_le
        have hthird := third.inputWeight_le
        omega)

/-- Evaluation formula for one selected atomic triple-word packet. -/
@[simp] lemma selected_triple_factor
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (first second third : SSAtom H 1)
    (coefficient : ℤ)
    (k : ℕ)
    (hk : 0 < k)
    (hk3 : k ≤ 3)
    (q : ℕ) :
    (selectedTripleFactor first second third coefficient k hk hk3).eval
        (n := n) q =
      ⁅PEAddres.freeLowerTruncation
          (n := n) first.address,
        ⁅PEAddres.freeLowerTruncation
            (n := n) second.address,
          PEAddres.freeLowerTruncation
            (n := n) third.address⁆⁆ ^
        (coefficient * (Nat.choose q k : ℤ)) := by
  simp [selectedTripleFactor, SPFactora.eval,
    SPFactora.wordValue, SPFactora.exponent,
    BBRecipe.eval, BBRecipe.select,
    PBRecipe.eval_select]

/-- Direct selected packet for a triple commutator of three source-atom values. -/
def tripleCorrection
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (first second third : SSAtom H 1)
    (k : ℕ)
    (hk : 0 < k)
    (hk3 : k ≤ 3) :
    SPFactora H 1 :=
  selectedTripleFactor first second third
    (first.coefficient * second.coefficient * third.coefficient) k hk hk3

/-- Direct triple packets evaluate to the expected selected power of the source-atom bracket. -/
lemma eval_tripleCorrection
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (first second third : SSAtom H 1)
    (k : ℕ)
    (hk : 0 < k)
    (hk3 : k ≤ 3)
    (q : ℕ) :
    (tripleCorrection first second third k hk hk3).eval (n := n) q =
      ⁅first.value (n := n), ⁅second.value (n := n), third.value (n := n)⁆⁆ ^
        Nat.choose q k := by
  rw [tripleCorrection, selected_triple_factor]
  simp only [value]
  rw [cPFactor.triple_element_zpow
    hn4
    (PEAddres.freeLowerTruncation
      (n := n) first.address)
    (PEAddres.freeLowerTruncation
      (n := n) second.address)
    (PEAddres.freeLowerTruncation
      (n := n) third.address)
    first.coefficient second.coefficient third.coefficient]
  simp only [← zpow_natCast, ← zpow_mul]

/-- Raw evaluation of the basic `choose q 2` pair-word packet. -/
@[simp] lemma pair_correction_raw
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (later earlier : SSAtom H 1)
    (q : ℕ) :
    (later.pairCorrection earlier).eval (n := n) q =
      ⁅PEAddres.freeLowerTruncation
          (n := n) later.address,
        PEAddres.freeLowerTruncation
          (n := n) earlier.address⁆ ^
        ((later.coefficient * earlier.coefficient) *
          (Nat.choose q 2 : ℤ)) := by
  simp [pairCorrection, SPFactora.eval,
    SPFactora.wordValue, SPFactora.exponent,
    BBRecipe.eval, BBRecipe.select,
    PBRecipe.eval_select]

/--
The enriched cutoff-four packet for the `choose q 2` power of a pair
commutator of source-atom values.
-/
def pairValueChoose
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (later earlier : SSAtom H 1) :
    List (SPFactora H 1) :=
  [selectedTripleFactor later later earlier
      (Ring.choose later.coefficient 2 * earlier.coefficient)
      2 (by omega) (by omega),
    later.pairCorrection earlier,
    selectedTripleFactor earlier later earlier
      (later.coefficient * Ring.choose earlier.coefficient 2)
      2 (by omega) (by omega)]

/-- The enriched pair packet evaluates to the expected selected power of the source-atom pair. -/
lemma value_choose_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (later earlier : SSAtom H 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (pairValueChoose later earlier) =
      ⁅later.value (n := n), earlier.value (n := n)⁆ ^ Nat.choose q 2 := by
  let B :=
    PEAddres.freeLowerTruncation
      (n := n) later.address
  let A :=
    PEAddres.freeLowerTruncation
      (n := n) earlier.address
  let C := ⁅B, A⁆
  let D := ⁅B, C⁆
  let E := ⁅A, C⁆
  have hB :
      B ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hA :
      A ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hC :
      C ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [C] using element_lower_series hB hA
  have hD :
      D ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    exact Subgroup.lowerCentralSeries_antitone (show 1 ≤ 2 by omega) (by
      simpa [D] using element_lower_series hB hC)
  have hE :
      E ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    exact Subgroup.lowerCentralSeries_antitone (show 1 ≤ 2 by omega) (by
      simpa [E] using element_lower_series hA hC)
  have hformula :
      ⁅B ^ later.coefficient, A ^ earlier.coefficient⁆ =
        D ^ (Ring.choose later.coefficient 2 * earlier.coefficient) *
          C ^ (later.coefficient * earlier.coefficient) *
            E ^ (later.coefficient * Ring.choose earlier.coefficient 2) := by
    simpa [C, D, E] using
      (HCThree.element_zpow_class
        hn4 B A later.coefficient earlier.coefficient)
  have hdistribute :
      (D ^ (Ring.choose later.coefficient 2 * earlier.coefficient) *
            C ^ (later.coefficient * earlier.coefficient) *
              E ^ (later.coefficient * Ring.choose earlier.coefficient 2)) ^
          Nat.choose q 2 =
        (D ^ (Ring.choose later.coefficient 2 * earlier.coefficient)) ^
            Nat.choose q 2 *
          (C ^ (later.coefficient * earlier.coefficient)) ^ Nat.choose q 2 *
            (E ^ (later.coefficient * Ring.choose earlier.coefficient 2)) ^
              Nat.choose q 2 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.map_cons,
      List.map_nil, mul_assoc] using
      (cPFactor.list_prod_series
        hn4 (Nat.choose q 2)
        [D ^ (Ring.choose later.coefficient 2 * earlier.coefficient),
          C ^ (later.coefficient * earlier.coefficient),
          E ^ (later.coefficient * Ring.choose earlier.coefficient 2)] (by
            intro factor hfactor
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hfactor
            rcases hfactor with rfl | rfl | rfl
            · exact
                (Subgroup.lowerCentralSeries
                  (LowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} d)) n) 1).zpow_mem hD _
            · exact
                (Subgroup.lowerCentralSeries
                  (LowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} d)) n) 1).zpow_mem hC _
            · exact
                (Subgroup.lowerCentralSeries
                  (LowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} d)) n) 1).zpow_mem hE _))
  simp only [pairValueChoose, SPFactora.listEval_cons,
    SPFactora.listEval_nil, selected_triple_factor,
    pair_correction_raw, mul_one]
  simp only [value]
  rw [← mul_assoc]
  change
    D ^ ((Ring.choose later.coefficient 2 * earlier.coefficient) *
          (Nat.choose q 2 : ℤ)) *
        C ^ ((later.coefficient * earlier.coefficient) *
          (Nat.choose q 2 : ℤ)) *
      E ^ ((later.coefficient * Ring.choose earlier.coefficient 2) *
          (Nat.choose q 2 : ℤ)) =
      ⁅B ^ later.coefficient, A ^ earlier.coefficient⁆ ^ Nat.choose q 2
  calc
    D ^ ((Ring.choose later.coefficient 2 * earlier.coefficient) *
            (Nat.choose q 2 : ℤ)) *
          C ^ ((later.coefficient * earlier.coefficient) *
            (Nat.choose q 2 : ℤ)) *
        E ^ ((later.coefficient * Ring.choose earlier.coefficient 2) *
            (Nat.choose q 2 : ℤ)) =
        (D ^ (Ring.choose later.coefficient 2 * earlier.coefficient)) ^
              Nat.choose q 2 *
            (C ^ (later.coefficient * earlier.coefficient)) ^ Nat.choose q 2 *
          (E ^ (later.coefficient * Ring.choose earlier.coefficient 2)) ^
            Nat.choose q 2 := by
              simp only [← zpow_natCast, ← zpow_mul]
    _ =
        (D ^ (Ring.choose later.coefficient 2 * earlier.coefficient) *
              C ^ (later.coefficient * earlier.coefficient) *
            E ^ (later.coefficient * Ring.choose earlier.coefficient 2)) ^
          Nat.choose q 2 := hdistribute.symm
    _ = ⁅B ^ later.coefficient, A ^ earlier.coefficient⁆ ^ Nat.choose q 2 := by
          rw [hformula]

end SSAtom

end TCTex
end Submission

/-!
# Finite symbolic class-three power source

This file assembles the atomic symbolic packets into a finite source for the
power of an ordered source-atom block at cutoff four.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SSAtom

/--
The left triple correction has multiplicity
`choose q 2 + 2 * choose q 3`, represented by three bounded packets.
-/
def leftTripleFactors
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (x z : SSAtom H 1) :
    List (SPFactora H 1) :=
  [tripleCorrection x z x 2 (by omega) (by omega),
    tripleCorrection x z x 3 (by omega) (by omega),
    tripleCorrection x z x 3 (by omega) (by omega)]

/-- The three left-triple packets evaluate to the required combined multiplicity. -/
lemma list_triple_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (x z : SSAtom H 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q (leftTripleFactors x z) =
      ⁅x.value (n := n), ⁅z.value (n := n), x.value (n := n)⁆⁆ ^
        cPFactor.leftTripleMultiplicity q := by
  simp only [leftTripleFactors, SPFactora.listEval_cons,
    SPFactora.listEval_nil, eval_tripleCorrection hn4, mul_one]
  rw [cPFactor.leftTripleMultiplicity, pow_add]
  have htwo :
      2 * Nat.choose q 3 = Nat.choose q 3 + Nat.choose q 3 := by
    omega
  rw [htwo, pow_add]

/-- Evaluate a finite list of left-triple packet families. -/
lemma flat_triple_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (x : SSAtom H 1)
    (q : ℕ) :
    ∀ L : List (SSAtom H 1),
      SPFactora.listEval (n := n) q
          (L.flatMap fun z => leftTripleFactors x z) =
        (L.map fun z =>
          ⁅x.value (n := n), ⁅z.value (n := n), x.value (n := n)⁆⁆ ^
            cPFactor.leftTripleMultiplicity q).prod := by
  intro L
  induction L with
  | nil =>
      simp
  | cons z L ih =>
      simp [SPFactora.listEval_append,
        list_triple_factors hn4, ih]

/-- Evaluate the finite Cartesian family of direct `choose q 3` triple packets. -/
lemma flat_triple_choose
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (x : SSAtom H 1)
    (q : ℕ) :
    ∀ outer inner : List (SSAtom H 1),
      SPFactora.listEval (n := n) q
          (outer.flatMap fun z =>
            inner.map fun y => tripleCorrection y z x 3 (by omega) (by omega)) =
        (outer.flatMap fun z =>
          inner.map fun y =>
            ⁅y.value (n := n), ⁅z.value (n := n), x.value (n := n)⁆⁆ ^
              Nat.choose q 3).prod := by
  intro outer inner
  induction outer with
  | nil =>
      simp
  | cons z outer ih =>
      simp only [List.flatMap_cons, SPFactora.listEval_append,
        List.prod_append]
      rw [ih]
      have hhead :
          SPFactora.listEval (n := n) q
              (inner.map fun y =>
                tripleCorrection y z x 3 (by omega) (by omega)) =
            (inner.map fun y =>
              ⁅y.value (n := n), ⁅z.value (n := n), x.value (n := n)⁆⁆ ^
                Nat.choose q 3).prod := by
        simp only [SPFactora.listEval, List.map_map]
        apply congrArg List.prod
        apply List.map_congr_left
        intro y _hy
        exact eval_tripleCorrection hn4 y z x 3 (by omega) (by omega) q
      rw [hhead]

/--
The symbolic image of the flattened pair factors, with each value-level atom
raised to `choose q 2`.
-/
def pairChooseFactors
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (x : SSAtom H 1) :
    List (SSAtom H 1) →
      List (SPFactora H 1)
  | [] => []
  | y :: L =>
      (L.reverse.map fun z => tripleCorrection y z x 2 (by omega) (by omega)) ++
        pairChooseFactors x L ++
          pairValueChoose y x

/-- The symbolic flattened pair list evaluates to the powered value-level flattened pair list. -/
lemma pair_choose_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (x : SSAtom H 1)
    (q : ℕ) :
    ∀ L : List (SSAtom H 1),
      SPFactora.listEval (n := n) q
          (pairChooseFactors x L) =
        ((cPFactor.leftPairFactors
          (x.value (n := n)) (L.map fun atom => atom.value (n := n))).map
            fun factor => factor ^ Nat.choose q 2).prod := by
  intro L
  induction L with
  | nil =>
      simp [pairChooseFactors,
        cPFactor.leftPairFactors]
  | cons y L ih =>
      simp only [pairChooseFactors,
        cPFactor.leftPairFactors,
        SPFactora.listEval_append, List.map_cons,
        List.map_append, List.prod_append]
      rw [ih, value_choose_factors hn4]
      simp [SPFactora.listEval, eval_tripleCorrection hn4,
        List.map_reverse, List.map_map, Function.comp_def]

/-- The finite symbolic class-three source for the power of an ordered source-atom block. -/
def classThreeFactors
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    List (SSAtom H 1) →
      List (SPFactora H 1)
  | [] => []
  | x :: L =>
      (L.reverse.flatMap fun z => leftTripleFactors x z) ++
        (L.reverse.flatMap fun z =>
          L.map fun y => tripleCorrection y z x 3 (by omega) (by omega)) ++
        pairChooseFactors x L ++
        [x.factor] ++
        classThreeFactors L

/-- The symbolic source evaluates to the fully atomic value-level collector. -/
lemma factors_atomic_prod
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (q : ℕ) :
    ∀ L : List (SSAtom H 1),
      SPFactora.listEval (n := n) q (classThreeFactors L) =
        (cPFactor.atomicFactors q
          (L.map fun atom => atom.value (n := n))).prod := by
  intro L
  induction L with
  | nil =>
      simp [classThreeFactors, cPFactor.atomicFactors]
  | cons x L ih =>
      simp only [classThreeFactors, cPFactor.atomicFactors,
        List.map_cons, SPFactora.listEval_append,
        SPFactora.listEval_cons,
        SPFactora.listEval_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [flat_triple_factors hn4 x q L.reverse,
        flat_triple_choose hn4 x q L.reverse L,
        pair_choose_factors hn4 x q L, eval_factor, ih]
      simp only [List.map_reverse, List.map_map, mul_left_inj]
      have hreverse :
          (L.map fun atom => atom.value (n := n)).reverse =
            L.reverse.map fun atom => atom.value (n := n) := by
        simp
      rw [hreverse, List.flatMap_map]
      rfl

/-- The finite symbolic class-three source evaluates to the power of its source-atom block. -/
lemma list_three_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (q : ℕ)
    (L : List (SSAtom H 1)) :
    SPFactora.listEval (n := n) q (classThreeFactors L) =
      (L.map fun atom => atom.value (n := n)).prod ^ q := by
  rw [factors_atomic_prod hn4]
  exact cPFactor.atomic_factors_pow hn4 q _

end SSAtom

end TCTex
end Submission
