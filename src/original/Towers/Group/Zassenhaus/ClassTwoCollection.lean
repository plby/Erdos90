import Towers.Group.Zassenhaus.HighWeightSources

/-!
# Finite class-two power collection

For elements in a subgroup `S`, suppose every binary commutator belongs to a
subgroup `T`, every element of `S` commutes with every element of `T`, and
`T ≤ S`.  Then powers of finite products can be collected explicitly: for
each head element, emit one `choose q 2` power of every commutator with a later
element, retain the powered head, and recurse on the tail.

The lower-central specialization applies this to
`S = gamma_inputWeight` and `T = gamma_(2 * inputWeight)` inside
`F / gamma_n(F)` whenever `n ≤ 3 * inputWeight`.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement IsMulCommutative

/--
The explicit class-two factors representing the power of a finite ordered
product.  Later factors cross the powered head from right to left, hence the
reversal in the emitted commutator list.
-/
def cTFactor
    {G : Type*}
    [Group G]
    (q : ℕ) :
    List G → List G
  | [] => []
  | x :: L =>
      (L.reverse.map fun y => ⁅y, x⁆ ^ Nat.choose q 2) ++
        [x ^ q] ++ cTFactor q L

namespace cTFactor

/-- A central subgroup of a larger subgroup is commutative. -/
@[reducible] def mul_commutative_commute
    {G : Type*}
    [Group G]
    (S T : Subgroup G)
    (hTS : T ≤ S)
    (hcentral : ∀ {x z : G}, x ∈ S → z ∈ T → Commute x z) :
    IsMulCommutative T :=
  ⟨⟨fun x y => Subtype.ext (hcentral (hTS x.property) y.property).eq⟩⟩

/-- Powers distribute over finite products whose entries lie in a commutative subgroup. -/
lemma list_prod_pow
    {G : Type*}
    [Group G]
    (T : Subgroup G)
    [IsMulCommutative T]
    (q : ℕ) :
    ∀ (L : List G),
      (∀ x ∈ L, x ∈ T) →
        L.prod ^ q = (L.map fun x => x ^ q).prod := by
  intro L hL
  induction L with
  | nil =>
      simp
  | cons x L ih =>
      have hx : x ∈ T := hL x (by simp)
      have htail : ∀ y ∈ L, y ∈ T := by
        intro y hy
        exact hL y (by simp [hy])
      have htailProd : L.prod ∈ T :=
        Subgroup.list_prod_mem T htail
      have hcommute : Commute x L.prod := by
        exact congrArg Subtype.val
          (mul_comm (⟨x, hx⟩ : T) (⟨L.prod, htailProd⟩ : T))
      simp only [List.prod_cons, List.map_cons]
      rw [hcommute.mul_pow, ih htail]

/-- Commutators with a finite product split in reverse list order. -/
lemma commutator_element_reverse
    {G : Type*}
    [Group G]
    (S T : Subgroup G)
    (hbracket : ∀ {x y : G}, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ T)
    (hcentral : ∀ {x z : G}, x ∈ S → z ∈ T → Commute x z)
    (a : G)
    (ha : a ∈ S) :
    ∀ (L : List G),
      (∀ x ∈ L, x ∈ S) →
        ⁅L.prod, a⁆ = (L.reverse.map fun x => ⁅x, a⁆).prod := by
  intro L hL
  induction L with
  | nil =>
      simp
  | cons x L ih =>
      have hx : x ∈ S := hL x (by simp)
      have htail : ∀ y ∈ L, y ∈ S := by
        intro y hy
        exact hL y (by simp [hy])
      have htailProd : L.prod ∈ S :=
        Subgroup.list_prod_mem S htail
      have htailBracket : ⁅L.prod, a⁆ ∈ T :=
        hbracket htailProd ha
      rw [List.prod_cons, element_mul_left,
        (hcentral hx htailBracket).eq, mul_inv_cancel_right, ih htail]
      simp [List.reverse_cons, List.map_append, List.prod_append]

/--
The `choose q 2` power of a finite-product commutator splits into the explicit
reverse-ordered pair corrections.
-/
lemma commutator_element_choose
    {G : Type*}
    [Group G]
    (S T : Subgroup G)
    (hTS : T ≤ S)
    (hbracket : ∀ {x y : G}, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ T)
    (hcentral : ∀ {x z : G}, x ∈ S → z ∈ T → Commute x z)
    (a : G)
    (ha : a ∈ S)
    (L : List G)
    (hL : ∀ x ∈ L, x ∈ S)
    (q : ℕ) :
    ⁅L.prod, a⁆ ^ Nat.choose q 2 =
      (L.reverse.map fun x => ⁅x, a⁆ ^ Nat.choose q 2).prod := by
  letI : IsMulCommutative T :=
    mul_commutative_commute S T hTS hcentral
  rw [commutator_element_reverse S T
    hbracket hcentral a ha L hL]
  simpa only [List.map_map, Function.comp_apply] using
    (list_prod_pow T (Nat.choose q 2)
      (L.reverse.map fun x => ⁅x, a⁆) (by
        intro z hz
        rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
        exact hbracket (hL x (List.mem_reverse.mp hx)) ha))

/--
The class-two Hall identity for the power of two factors, oriented for moving
the right factor leftward across the next repeated block.
-/
lemma element_choose_two
    {G : Type*}
    [Group G]
    (S T : Subgroup G)
    (hbracket : ∀ {x y : G}, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ T)
    (hcentral : ∀ {x z : G}, x ∈ S → z ∈ T → Commute x z)
    {x y : G}
    (hx : x ∈ S)
    (hy : y ∈ S)
    (q : ℕ) :
    (x * y) ^ q = ⁅y, x⁆ ^ Nat.choose q 2 * x ^ q * y ^ q := by
  have hc : ⁅y, x⁆ ∈ T := hbracket hy hx
  have hxc : Commute x ⁅y, x⁆ := hcentral hx hc
  have hyc : Commute y ⁅y, x⁆ := hcentral hy hc
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hchoose :
          Nat.choose (q + 1) 2 = Nat.choose q 2 + q := by
        rw [show q + 1 = Nat.succ q by omega,
          show 2 = Nat.succ 1 by omega, Nat.choose_succ_succ,
          Nat.choose_one_right, Nat.add_comm]
      have hswap :
          y ^ q * x = ⁅y, x⁆ ^ q * x * y ^ q := by
        calc
          y ^ q * x = ⁅y ^ q, x⁆ * x * y ^ q := by
            simp only [commutatorElement_def]
            group
          _ = ⁅y, x⁆ ^ q * x * y ^ q := by
            rw [element_left_commute hyc q]
      rw [pow_succ, ih]
      calc
        ⁅y, x⁆ ^ Nat.choose q 2 * x ^ q * y ^ q * (x * y) =
            ⁅y, x⁆ ^ Nat.choose q 2 * x ^ q *
              (⁅y, x⁆ ^ q * x * y ^ q) * y := by
                rw [← hswap]
                group
        _ = ⁅y, x⁆ ^ (Nat.choose q 2 + q) * x ^ (q + 1) * y ^ (q + 1) := by
              calc
                ⁅y, x⁆ ^ Nat.choose q 2 * x ^ q *
                      (⁅y, x⁆ ^ q * x * y ^ q) * y =
                    ⁅y, x⁆ ^ Nat.choose q 2 *
                      (x ^ q * ⁅y, x⁆ ^ q) * x * y ^ q * y := by
                        group
                _ = ⁅y, x⁆ ^ Nat.choose q 2 *
                      (⁅y, x⁆ ^ q * x ^ q) * x * y ^ q * y := by
                        rw [(hxc.pow_pow q q).eq]
                _ = ⁅y, x⁆ ^ (Nat.choose q 2 + q) * x ^ (q + 1) * y ^ (q + 1) := by
                        rw [pow_add, pow_succ, pow_succ]
                        group
        _ = ⁅y, x⁆ ^ Nat.choose (q + 1) 2 * x ^ (q + 1) * y ^ (q + 1) := by
              rw [hchoose]

/--
The recursive finite class-two factor list evaluates to the power of the
original ordered product.
-/
lemma prod_eq_pow
    {G : Type*}
    [Group G]
    (S T : Subgroup G)
    (hTS : T ≤ S)
    (hbracket : ∀ {x y : G}, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ T)
    (hcentral : ∀ {x z : G}, x ∈ S → z ∈ T → Commute x z)
    (q : ℕ) :
    ∀ (L : List G),
      (∀ x ∈ L, x ∈ S) →
        (cTFactor q L).prod = L.prod ^ q := by
  intro L hL
  induction L with
  | nil =>
      simp [cTFactor]
  | cons x L ih =>
      have hx : x ∈ S := hL x (by simp)
      have htail : ∀ y ∈ L, y ∈ S := by
        intro y hy
        exact hL y (by simp [hy])
      have htailProd : L.prod ∈ S :=
        Subgroup.list_prod_mem S htail
      simp only [cTFactor, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one]
      rw [ih htail,
        ← commutator_element_choose
          S T hTS hbracket hcentral x hx L htail q,
        ← element_choose_two
          S T hbracket hcentral hx htailProd q]

end cTFactor

/--
In `F / gamma_n(F)`, the explicit class-two factors collect powers of lists in
`gamma_inputWeight` whenever triple commutators have reached the cutoff.
-/
lemma class_initial_series
    {d n inputWeight : ℕ}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (q : ℕ)
    (L :
      List
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (hL :
      ∀ x ∈ L,
        x ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (inputWeight - 1)) :
    (cTFactor q L).prod = L.prod ^ q := by
  let N :=
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let S : Subgroup N := Subgroup.lowerCentralSeries N (inputWeight - 1)
  let T : Subgroup N := Subgroup.lowerCentralSeries N (2 * inputWeight - 1)
  apply cTFactor.prod_eq_pow S T
  · intro x hx
    exact Subgroup.lowerCentralSeries_antitone (by omega) hx
  · intro x y hx hy
    exact Subgroup.lowerCentralSeries_antitone (by omega)
      (element_lower_series hx hy)
  · intro x z hx hz
    rw [← commutatorElement_eq_one_iff_commute]
    apply eq_bot_iff.mp
      SPFactora.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega)
      (element_lower_series hx hz)
  · exact hL

end TCTex
end Towers
