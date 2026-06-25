import Towers.Group.NilpotentProducts.GeneralPolynomialCoordinates
import Towers.Group.NilpotentProducts.TwoInvolutions


/-!
# Struik's Lemma 3 and equation (30)

The paper numbers the lower central series starting with `G₁ = G`, while
`Subgroup.lowerCentralSeries G 0 = ⊤` in the library.  This file uses the one-based
wrapper `lowerCentralTerm`.

The main theorem below proves the first unconditional depth shift in
Lemma 3 for every canonical Hall commutator.  Its proof is Struik's
descending induction: collect after powering one occurring generator, use
the polynomial degree bound from Lemma H2, and recursively absorb every
higher correction below the target depth.
-/

namespace Struik
namespace P1960

open Towers
open Towers.HallTree
open Towers.TCTex

universe u

/-- The one-based lower-central term used in Struik's paper. -/
def lowerCentralTerm (G : Type u) [Group G] (r : ℕ) : Subgroup G :=
  Subgroup.lowerCentralSeries G (r - 1)

@[simp] theorem lower_central_term
    (G : Type u) [Group G] :
    lowerCentralTerm G 1 = ⊤ := by
  simp [lowerCentralTerm]

/-- Mapping a fixed Hall weight block into a subgroup reduces to checking
its individual powered factors. -/
private theorem mapped_weight_product
    {t n r : ℕ} (order : Fin t → ℕ)
    (S : Subgroup (NilpotentCyclicProduct order n))
    (e : (standardHallFamily.{u} t r).index → ℤ)
    (hfactor :
      ∀ j : (standardHallFamily.{u} t r).index,
        inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t r).commutator j
              |>.freeLowerTruncation (n := n)) ^ e j ∈
          S) :
    inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) e) ∈
      S := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  apply Subgroup.list_prod_mem
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  rcases hx with ⟨j, _hj, rfl⟩
  change
    inverseFreeTruncation.{u} order n
        (((standardHallFamily.{u} t r).commutator j
          |>.freeLowerTruncation (n := n)) ^ e j) ∈
      S
  rw [map_zpow]
  exact hfactor j

/-- A specified leaf occurrence witnesses use of its own label. -/
private theorem uses_leaf_occurrence
    {α : Type*} :
    ∀ {tree : HallTree α} (leaf : HallTree.LOccur tree),
      hallTreeUses leaf.label tree
  | .atom _, .atom _ => rfl
  | .commutator _ _, .left leaf =>
      Or.inl (uses_leaf_occurrence leaf)
  | .commutator _ _, .right leaf =>
      Or.inr (uses_leaf_occurrence leaf)

/-- The logarithmic loss in a prime-power value of an integer-valued
polynomial is paid for by the distance from its leading weight. -/
theorem prime_log_sub
    (p m : ℕ)
    [Fact p.Prime]
    (hm : 0 < m) :
    Nat.log p m * (p - 1) ≤ m - 1 := by
  let l := Nat.log p m
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hlinearPow : 1 + l * (p - 1) ≤ p ^ l := by
    induction l with
    | zero =>
        simp
    | succ l ih =>
        have hpowOne : 1 ≤ p ^ l :=
          Nat.one_le_pow l p hp.pos
        calc
          1 + (l + 1) * (p - 1) =
              (1 + l * (p - 1)) + (p - 1) := by ring
          _ ≤ p ^ l + (p - 1) := Nat.add_le_add_right ih _
          _ ≤ p ^ l + p ^ l * (p - 1) := by
            gcongr
            simpa using Nat.mul_le_mul_right (p - 1) hpowOne
          _ = p ^ (l + 1) := by
            rw [pow_succ]
            calc
              p ^ l + p ^ l * (p - 1) =
                  p ^ l * (1 + (p - 1)) := by
                rw [Nat.mul_add, Nat.mul_one]
              _ = p ^ l * p := by congr 1 ; omega
  have hpowLog : p ^ l ≤ m :=
    Nat.pow_log_le_self p hm.ne'
  change l * (p - 1) ≤ m - 1
  omega

/-- A canonical Hall commutator powered by `p^(α+j)`, where an occurring
generator has order `p^α`, gains `(j+1)(p-1)` one-based lower-central
levels.  This is equation (30) for canonical Hall factors. -/
theorem standard_factor_shift
    {t n p α r : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (horder : order leaf.label.down = p ^ α)
    (j : ℕ) :
    inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        (p ^ (α + j)) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n)
        (r + (j + 1) * (p - 1)) := by
  let P : ℕ → Prop := fun k =>
    ∀ (r : ℕ), 1 ≤ r → r < n → n - r = k →
      ∀ (i : (standardHallFamily.{u} t r).index)
        (leaf : HallTree.LOccur (concreteBasicTree i)),
        order leaf.label.down = p ^ α →
          ∀ j : ℕ,
          inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t r).commutator i
                  |>.freeLowerTruncation (n := n)) ^
              (p ^ (α + j)) ∈
            lowerCentralTerm
              (NilpotentCyclicProduct order n)
              (r + (j + 1) * (p - 1))
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro r hr hrn hkr i leaf horder j
        let generatorOrder := p ^ α
        let a := p ^ (α + j)
        let tree := concreteBasicTree i
        let g :=
          inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t r).commutator i
              |>.freeLowerTruncation (n := n))
        let y :=
          HallTree.leafOccurrencePow
            (freeTruncationValue t n) a tree leaf
        let e := standardHallCoordinates t n hn y
        let target : ℕ := r + (j + 1) * (p - 1)
        let S : Subgroup (NilpotentCyclicProduct order n) :=
          lowerCentralTerm (NilpotentCyclicProduct order n) target
        letI : S.Normal := by
          dsimp [S, lowerCentralTerm]
          infer_instance
        let q :
            NilpotentCyclicProduct order n →*
              NilpotentCyclicProduct order n ⧸ S :=
          QuotientGroup.mk' S
        have hp : 1 < p := (Fact.out : p.Prime).one_lt
        have hcoordinatesLow :=
          powered_coordinates_leading
            hn hr hrn i leaf a
        change
          (∀ (s : ℕ), 1 ≤ s → s < r → s < n → e s = 0) ∧
            (∀ j : (standardHallFamily.{u} t r).index,
              e r j = if j = i then (a : ℤ) else 0) at hcoordinatesLow
        rcases hcoordinatesLow with ⟨hbelow, hleading⟩
        have hmapY :
            inverseFreeTruncation.{u} order n y = 1 := by
          rw [show
              inverseFreeTruncation.{u} order n y =
                HallTree.leafOccurrencePow
                  (fun j =>
                    inverseFreeTruncation.{u} order n
                      (freeTruncationValue t n j))
                  a tree leaf by
                simp [y]]
          apply HallTree.eval_leaf_occurrence
          change
            inverseFreeTruncation.{u} order n
                (lowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} t)) n
                  (FreeGroup.of leaf.label)) ^ a =
              1
          rw [inverse_truncation_generator]
          have hgenerator :
              (nilpotentCyclicGenerator order n leaf.label.down)⁻¹ ^
                  generatorOrder =
                1 := by
            simpa [generatorOrder, horder] using congrArg Inv.inv
              (nilpotent_cyclic_generator
                order n leaf.label.down)
          rw [show a = generatorOrder * p ^ j by
            simp [a, generatorOrder, pow_add], pow_mul, hgenerator, one_pow]
        have hblockMem :
            ∀ s : ℕ, 1 ≤ s → s < n → s ≠ r →
              inverseFreeTruncation.{u} order n
                  ((standardHallFamily.{u} t s).collectedWeightProduct
                    (n := n) (e s)) ∈
                S := by
          intro s hs hsn hsr
          rcases lt_or_gt_of_ne hsr with hlt | hgt
          · rw [hbelow s hs hlt hsn,
              BCWta.collected_weight_productzero,
              map_one]
            exact S.one_mem
          · by_cases hsTarget : target ≤ s
            · have hsource :
                  (standardHallFamily.{u} t s).collectedWeightProduct
                      (n := n) (e s) ∈
                    Subgroup.lowerCentralSeries
                      (LowerCentralTruncation
                        (FreeGroup (FreeGenerator.{u} t)) n) (s - 1) :=
                (standardHallFamily.{u} t s
                  ).collectedweight_productmem_lowecentseri (e s)
              have hmapped :
                  inverseFreeTruncation.{u} order n
                      ((standardHallFamily.{u} t s).collectedWeightProduct
                        (n := n) (e s)) ∈
                    Subgroup.lowerCentralSeries
                      (NilpotentCyclicProduct order n) (s - 1) :=
                Subgroup.lowerCentralSeries.map
                  (inverseFreeTruncation.{u} order n) (s - 1)
                  (Subgroup.mem_map_of_mem
                    (inverseFreeTruncation.{u} order n) hsource)
              exact Subgroup.lowerCentralSeries_antitone (by
                dsimp [S, lowerCentralTerm, target]
                omega) hmapped
            · have hsBelowTarget : s < target := Nat.lt_of_not_ge hsTarget
              apply mapped_weight_product order S (e s)
              intro factorIndex
              by_cases huses :
                  hallTreeUses leaf.label
                    (concreteBasicTree factorIndex)
              · obtain ⟨leafJ, hleafJ⟩ :=
                  leaf_occurrence_uses huses
                let m := s - (r - 1)
                let ell := Nat.log p m
                let j' := j - ell
                have hmPos : 0 < m := by
                  dsimp [m]
                  omega
                have hdistance :
                    ell * (p - 1) ≤ m - 1 := by
                  exact prime_log_sub p m hmPos
                have hmBelowTarget :
                    m - 1 < (j + 1) * (p - 1) := by
                  dsimp [m, target] at hsBelowTarget
                  omega
                have hellLe : ell ≤ j := by
                  have hpSubPos : 0 < p - 1 := by omega
                  by_contra hell
                  have hjell : j + 1 ≤ ell := by omega
                  have hmul :=
                    Nat.mul_le_mul_right (p - 1) hjell
                  omega
                have htargetLe :
                    target ≤ s + (j' + 1) * (p - 1) := by
                  have hrSplit : r - 1 + 1 = r :=
                    Nat.sub_add_cancel hr
                  have hrs : r - 1 ≤ s := by omega
                  have hsSplit : r - 1 + m = s := by
                    dsimp [m]
                    omega
                  have hjSplit : ell + j' = j := by
                    dsimp [j']
                    omega
                  calc
                    target =
                        (r - 1) + 1 +
                          (ell * (p - 1) +
                            (j' + 1) * (p - 1)) := by
                      dsimp [target]
                      congr 1
                      · exact hrSplit.symm
                      · rw [show j + 1 = ell + (j' + 1) by omega,
                          Nat.add_mul]
                    _ ≤ (r - 1) + m +
                          (j' + 1) * (p - 1) := by
                      omega
                    _ = s + (j' + 1) * (p - 1) := by
                      rw [hsSplit]
                have hfactorShift :=
                  ih (n - s) (by omega) s hs hsn rfl factorIndex leafJ (by
                    simpa [hleafJ] using horder) j'
                have hfactorMemS :
                    inverseFreeTruncation.{u} order n
                          ((standardHallFamily.{u} t s).commutator
                              factorIndex
                            |>.freeLowerTruncation (n := n)) ^
                        (p ^ (α + j')) ∈
                      S := by
                  exact Subgroup.lowerCentralSeries_antitone (by
                    dsimp [S, lowerCentralTerm] at hfactorShift ⊢
                    exact Nat.sub_le_sub_right htargetLe 1) hfactorShift
                have hf :=
                  powered_data_general
                    t n hn r hr hrn i leaf s hgt hsn factorIndex
                have hf0 :
                    standardHallCoordinates t n hn
                        (HallTree.leafOccurrencePow
                          (freeTruncationValue t n) 0
                          tree leaf)
                        s factorIndex =
                      0 := by
                  have hy0 :
                      HallTree.leafOccurrencePow
                          (freeTruncationValue t n) 0
                          tree leaf =
                        1 :=
                    HallTree.eval_leaf_occurrence
                      (freeTruncationValue t n)
                      0 leaf (by simp)
                  rw [hy0]
                  simpa [standardHallCoordinates] using
                    coordinate_one_zero
                      hn (standardHallFamily.{u} t)
                      (fun w _hw hwn =>
                        standard_forms_associated
                          t n w (by omega) hwn)
                      hs hsn factorIndex
                have hdivRaw :=
                  integer_valued_dvd
                    (p := p) hf hf0 (α + j)
                have hexponent :
                    α + j - ell = α + j' := by
                  dsimp [j']
                  omega
                have hdiv :
                    ((p ^ (α + j') : ℕ) : ℤ) ∣ e s factorIndex := by
                  simpa [e, y, tree, m, ell, hexponent] using hdivRaw
                rcases hdiv with ⟨z, hz⟩
                rw [hz, zpow_mul]
                exact S.zpow_mem hfactorMemS z
              · have hzero :=
                  poweredLeafData
                    t n hn r hr hrn i leaf a s hgt hsn factorIndex huses
                rw [show e s factorIndex = 0 by
                  simpa [e, y, tree] using hzero, zpow_zero]
                exact S.one_mem
        have hmapWeight :
            inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t r).collectedWeightProduct
                  (n := n) (e r)) =
              g ^ (a : ℤ) := by
          rw [mapped_standard_single order (e r) i]
          · rw [hleading i, if_pos rfl]
          · intro j hji
            rw [hleading j, if_neg hji, zpow_zero]
        have hmapProductMod :
            q (inverseFreeTruncation.{u} order n
                (standardHallProduct t n e)) =
              q (inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t r).collectedWeightProduct
                  (n := n) (e r))) := by
          unfold standardHallProduct collectedHallProduct
            collectedPrefixProduct
          rw [map_list_prod, map_list_prod]
          let f : ℕ →
              NilpotentCyclicProduct order n ⧸ S :=
            fun j =>
              q (inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t (j + 1)).collectedWeightProduct
                  (n := n) (e (j + 1))))
          have hrIndex : r - 1 ∈ List.range (n - 1) := by
            simp
            omega
          have hresult :
              ((List.range (n - 1)).map f).prod = f (r - 1) := by
            apply list_prod_except
            · exact hrIndex
            · exact List.nodup_range
            · intro j hj hjr
              have hjlt : j < n - 1 := List.mem_range.mp hj
              have hweightNe : j + 1 ≠ r := by omega
              exact (QuotientGroup.eq_one_iff (N := S) _).mpr
                (hblockMem (j + 1) (by omega) (by omega) hweightNe)
          have hrsub : r - 1 + 1 = r := by omega
          rw [← hrsub]
          simpa [f, List.map_map, Function.comp_apply] using hresult
        have heval : standardHallProduct t n e = y :=
          standard_product_coordinates t n hn y
        have hq :
            q (g ^ a) = 1 := by
          rw [← zpow_natCast, ← hmapWeight, ← hmapProductMod,
            heval, hmapY, map_one]
        exact (QuotientGroup.eq_one_iff (N := S) _).mp hq
  exact hP (n - r) r hr hrn rfl i leaf horder j

/-- The first line of equation (30) for canonical Hall factors. -/
theorem standard_prime_shift
    {t n p α r : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (horder : order leaf.label.down = p ^ α) :
    inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        (p ^ α) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n) (r + (p - 1)) := by
  simpa using
    standard_factor_shift
      order hn hr hrn i leaf horder 0

/-- Both displayed depth-shift conclusions of Lemma 3 for a canonical
Hall factor containing a generator of order `p^α`. -/
theorem standardHallFactor
    {t n p α r : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (horder : order leaf.label.down = p ^ α) :
    (inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        (p ^ α) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n) (r + (p - 1))) ∧
      ∀ j : ℕ,
        inverseFreeTruncation.{u} order n
              ((standardHallFamily.{u} t r).commutator i
                |>.freeLowerTruncation (n := n)) ^
            (p ^ (α + j)) ∈
          lowerCentralTerm
            (NilpotentCyclicProduct order n)
            (r + (j + 1) * (p - 1)) := by
  exact ⟨standard_prime_shift
      order hn hr hrn i leaf horder,
    standard_factor_shift
      order hn hr hrn i leaf horder⟩

/-- An arbitrary parenthesized commutator powered by `p^(α+j)`, where one
occurring generator has order `p^α`, gains `(j+1)(p-1)` one-based
lower-central levels.

Unlike `standard_factor_shift`, the source tree need
not itself be a standard Hall basic commutator.  The exact Lemma H2
recollection reduces its correction to higher standard Hall factors, to
which the canonical theorem applies. -/
theorem tree_add_shift
    {t n p α : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (horder : order leaf.label.down = p ^ α)
    (j : ℕ) :
    inverseFreeTruncation.{u} order n
          (tree.toCWord.eval
            (freeTruncationValue t n)) ^
        (p ^ (α + j)) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n)
        (tree.weight + (j + 1) * (p - 1)) := by
  let a := p ^ (α + j)
  let base :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  let powered :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) a tree leaf
  let target := tree.weight + (j + 1) * (p - 1)
  let S : Subgroup (NilpotentCyclicProduct order n) :=
    lowerCentralTerm (NilpotentCyclicProduct order n) target
  obtain ⟨correction, hcorrectionEq, hcorrectionLow,
      hcorrectionSupport, hcorrectionPolynomial⟩ :=
    standardCorrectionCoordinates t n hn tree leaf
  have hcorrectionZeroProduct :
      standardHallProduct t n (correction 0) = 1 := by
    have hzero := hcorrectionEq 0
    have hpoweredZero :
        HallTree.leafOccurrencePow
            (freeTruncationValue t n) 0 tree leaf =
          1 := by
      exact HallTree.eval_leaf_occurrence
        (freeTruncationValue t n) 0 leaf (by simp)
    rw [hpoweredZero, pow_zero, one_mul] at hzero
    exact hzero.symm
  have hcorrectionZero :
      ∀ (s : ℕ), 1 ≤ s → s < n →
        ∀ factorIndex : (standardHallFamily.{u} t s).index,
          correction 0 s factorIndex = 0 := by
    intro s hs hsn factorIndex
    have hcoordinates :=
      congrFun
        (standard_coordinates_product
          t n hn (correction 0) 1 hcorrectionZeroProduct s hs hsn)
        factorIndex
    calc
      correction 0 s factorIndex =
          standardHallCoordinates t n hn 1 s factorIndex :=
        hcoordinates.symm
      _ = 0 := by
        simpa [standardHallCoordinates] using
          coordinate_one_zero
            hn (standardHallFamily.{u} t)
            (fun w _hw hwn =>
              standard_forms_associated
                t n w (by omega) hwn)
            hs hsn factorIndex
  have hmapPowered :
      inverseFreeTruncation.{u} order n powered = 1 := by
    rw [show
        inverseFreeTruncation.{u} order n powered =
          HallTree.leafOccurrencePow
            (fun i =>
              inverseFreeTruncation.{u} order n
                (freeTruncationValue t n i))
            a tree leaf by
          simp [powered]]
    apply HallTree.eval_leaf_occurrence
    change
      inverseFreeTruncation.{u} order n
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n
            (FreeGroup.of leaf.label)) ^ a =
        1
    rw [inverse_truncation_generator]
    have hgenerator :
        (nilpotentCyclicGenerator order n leaf.label.down)⁻¹ ^
            (p ^ α) =
          1 := by
      simpa [horder] using congrArg Inv.inv
        (nilpotent_cyclic_generator
          order n leaf.label.down)
    rw [show a = p ^ α * p ^ j by simp [a, pow_add],
      pow_mul, hgenerator, one_pow]
  have hblockMem :
      ∀ s : ℕ, 1 ≤ s → s < n →
        inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t s).collectedWeightProduct
              (n := n) (correction a s)) ∈
          S := by
    intro s hs hsn
    by_cases hsLow : s < tree.weight + 1
    · rw [hcorrectionLow a s hs hsLow hsn,
        BCWta.collected_weight_productzero,
        map_one]
      exact S.one_mem
    · have hsAbove : tree.weight < s := by omega
      by_cases hsTarget : target ≤ s
      · have hsource :
            (standardHallFamily.{u} t s).collectedWeightProduct
                (n := n) (correction a s) ∈
              Subgroup.lowerCentralSeries
                (LowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} t)) n) (s - 1) :=
          (standardHallFamily.{u} t s
            ).collectedweight_productmem_lowecentseri (correction a s)
        have hmapped :
            inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t s).collectedWeightProduct
                  (n := n) (correction a s)) ∈
              Subgroup.lowerCentralSeries
                (NilpotentCyclicProduct order n) (s - 1) :=
          Subgroup.lowerCentralSeries.map
            (inverseFreeTruncation.{u} order n) (s - 1)
            (Subgroup.mem_map_of_mem
              (inverseFreeTruncation.{u} order n) hsource)
        exact Subgroup.lowerCentralSeries_antitone (by
          dsimp [S, lowerCentralTerm, target]
          omega) hmapped
      · have hsBelowTarget : s < target := Nat.lt_of_not_ge hsTarget
        apply mapped_weight_product order S (correction a s)
        intro factorIndex
        by_cases huses :
            hallTreeUses leaf.label (concreteBasicTree factorIndex)
        · obtain ⟨factorLeaf, hfactorLeaf⟩ :=
            leaf_occurrence_uses huses
          let m := s - (tree.weight - 1)
          let ell := Nat.log p m
          let j' := j - ell
          have hmPos : 0 < m := by
            dsimp [m]
            omega
          have hdistance :
              ell * (p - 1) ≤ m - 1 :=
            prime_log_sub p m hmPos
          have hmBelowTarget :
              m - 1 < (j + 1) * (p - 1) := by
            dsimp [m, target] at hsBelowTarget
            omega
          have hellLe : ell ≤ j := by
            have hpSubPos : 0 < p - 1 := by
              exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
            by_contra hell
            have hjell : j + 1 ≤ ell := by omega
            have hmul := Nat.mul_le_mul_right (p - 1) hjell
            omega
          have htargetLe :
              target ≤ s + (j' + 1) * (p - 1) := by
            have hrSplit :
                tree.weight - 1 + 1 = tree.weight :=
              Nat.sub_add_cancel tree.weight_pos
            have hrs : tree.weight - 1 ≤ s := by omega
            have hsSplit : tree.weight - 1 + m = s := by
              dsimp [m]
              omega
            have hjSplit : ell + j' = j := by
              dsimp [j']
              omega
            calc
              target =
                  (tree.weight - 1) + 1 +
                    (ell * (p - 1) +
                      (j' + 1) * (p - 1)) := by
                dsimp [target]
                congr 1
                · exact hrSplit.symm
                · rw [show j + 1 = ell + (j' + 1) by omega,
                    Nat.add_mul]
              _ ≤ (tree.weight - 1) + m +
                    (j' + 1) * (p - 1) := by
                omega
              _ = s + (j' + 1) * (p - 1) := by
                rw [hsSplit]
          have hfactorShift :=
            standard_factor_shift
              order hn hs hsn factorIndex factorLeaf (by
                simpa [hfactorLeaf] using horder) j'
          have hfactorMemS :
              inverseFreeTruncation.{u} order n
                    ((standardHallFamily.{u} t s).commutator factorIndex
                      |>.freeLowerTruncation (n := n)) ^
                  (p ^ (α + j')) ∈
                S := by
            exact Subgroup.lowerCentralSeries_antitone (by
              dsimp [S, lowerCentralTerm] at hfactorShift ⊢
              exact Nat.sub_le_sub_right htargetLe 1) hfactorShift
          have hf :=
            hcorrectionPolynomial s hs hsn factorIndex
          have hdivRaw :=
            integer_valued_dvd
              (p := p) hf
              (hcorrectionZero s hs hsn factorIndex) (α + j)
          have hexponent :
              α + j - ell = α + j' := by
            dsimp [j']
            omega
          have hdiv :
              ((p ^ (α + j') : ℕ) : ℤ) ∣
                correction a s factorIndex := by
            simpa [a, m, ell, hexponent] using hdivRaw
          rcases hdiv with ⟨z, hz⟩
          rw [hz, zpow_mul]
          exact S.zpow_mem hfactorMemS z
        · rw [hcorrectionSupport a leaf.label
              (uses_leaf_occurrence leaf)
              s hs hsn factorIndex huses,
            zpow_zero]
          exact S.one_mem
  have hcorrectionMem :
      inverseFreeTruncation.{u} order n
          (standardHallProduct t n (correction a)) ∈
        S := by
    unfold standardHallProduct collectedHallProduct
      collectedPrefixProduct
    rw [map_list_prod]
    apply Subgroup.list_prod_mem
    intro x hx
    simp only [List.map_map, List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    have hklt : k < n - 1 := List.mem_range.mp hk
    exact hblockMem (k + 1) (by omega) (by omega)
  have hrelation :
      inverseFreeTruncation.{u} order n base ^ a *
          inverseFreeTruncation.{u} order n
            (standardHallProduct t n (correction a)) =
        1 := by
    calc
      inverseFreeTruncation.{u} order n base ^ a *
            inverseFreeTruncation.{u} order n
              (standardHallProduct t n (correction a)) =
          inverseFreeTruncation.{u} order n
            (base ^ a * standardHallProduct t n (correction a)) := by
              simp
      _ = inverseFreeTruncation.{u} order n powered := by
        simpa [base, powered] using congrArg
          (inverseFreeTruncation.{u} order n) (hcorrectionEq a).symm
      _ = 1 := hmapPowered
  have hbasePower :
      inverseFreeTruncation.{u} order n base ^ a =
        (inverseFreeTruncation.{u} order n
          (standardHallProduct t n (correction a)))⁻¹ := by
    calc
      inverseFreeTruncation.{u} order n base ^ a =
          (inverseFreeTruncation.{u} order n base ^ a *
              inverseFreeTruncation.{u} order n
                (standardHallProduct t n (correction a))) *
            (inverseFreeTruncation.{u} order n
              (standardHallProduct t n (correction a)))⁻¹ := by group
      _ = (inverseFreeTruncation.{u} order n
              (standardHallProduct t n (correction a)))⁻¹ := by
        rw [hrelation, one_mul]
  change inverseFreeTruncation.{u} order n base ^ a ∈ S
  rw [hbasePower]
  exact S.inv_mem hcorrectionMem

/-- The first line of equation (30) for an arbitrary parenthesized
commutator tree. -/
theorem hall_tree_shift
    {t n p α : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (horder : order leaf.label.down = p ^ α) :
    inverseFreeTruncation.{u} order n
          (tree.toCWord.eval
            (freeTruncationValue t n)) ^
        (p ^ α) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n)
        (tree.weight + (p - 1)) := by
  simpa using
    tree_add_shift
      order hn tree leaf horder 0

/-- Both conclusions of Lemma 3 for every arbitrary parenthesized
commutator, hence in particular for every displayed left-normed
commutator. -/
theorem hallTree
    {t n p α : ℕ}
    [Fact p.Prime]
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (horder : order leaf.label.down = p ^ α) :
    (inverseFreeTruncation.{u} order n
          (tree.toCWord.eval
            (freeTruncationValue t n)) ^
        (p ^ α) ∈
      lowerCentralTerm
        (NilpotentCyclicProduct order n)
        (tree.weight + (p - 1))) ∧
      ∀ j : ℕ,
        inverseFreeTruncation.{u} order n
              (tree.toCWord.eval
                (freeTruncationValue t n)) ^
            (p ^ (α + j)) ∈
          lowerCentralTerm
            (NilpotentCyclicProduct order n)
            (tree.weight + (j + 1) * (p - 1)) := by
  exact ⟨hall_tree_shift
      order hn tree leaf horder,
    tree_add_shift
      order hn tree leaf horder⟩

/-- The paper's final arbitrary-`w` sentence cannot use the minimum exponent
from some unrelated commutator as a global parameter.  In the abelian cyclic
group of order nine, the generator belongs to `G₁`, but its third power does
not belong to `G₃ = 1`. -/
theorem arbitrary_minimum_counterexample :
    let G := Multiplicative (ZMod 9)
    let w : G := Multiplicative.ofAdd 1
    w ∈ lowerCentralTerm G 1 ∧
      w ^ 3 ∉ lowerCentralTerm G 3 := by
  dsimp only
  constructor
  · simp [lowerCentralTerm]
  · have hgammaOne :
        Subgroup.lowerCentralSeries (Multiplicative (ZMod 9)) 1 = ⊥ := by
      simpa using
        (Subgroup.lowerCentralSeries_succ_eq_bot
          (G := Multiplicative (ZMod 9)) (n := 0) (by
            intro x _hx
            exact Subgroup.mem_center_iff.mpr fun y => mul_comm y x))
    have hgammaTwo :
        Subgroup.lowerCentralSeries (Multiplicative (ZMod 9)) 2 = ⊥ := by
      have hle :=
        Subgroup.lowerCentralSeries_antitone
          (G := Multiplicative (ZMod 9)) (show 1 ≤ 2 by omega)
      rw [hgammaOne] at hle
      exact le_antisymm hle bot_le
    rw [lowerCentralTerm, show 3 - 1 = 2 by omega, hgammaTwo]
    simp only [Subgroup.mem_bot]
    intro h
    have hthree : (3 : ZMod 9) ≠ 0 := by
      intro hzero
      have hdvd : 9 ∣ 3 :=
        (ZMod.natCast_eq_zero_iff 3 9).mp hzero
      norm_num at hdvd
    apply hthree
    simpa [← ofAdd_nsmul] using congrArg Multiplicative.toAdd h

/-- The first line of equation (30), abstracted from the cyclic-product
presentation: a `p^α` power gains `p - 1` one-based lower-central levels. -/
def InitialDepthShift
    (G : Type u) [Group G] (p α : ℕ) : Prop :=
  ∀ (r : ℕ) (w : G),
    w ∈ lowerCentralTerm G r →
      w ^ (p ^ α) ∈ lowerCentralTerm G (r + (p - 1))

/-- The repeatable step used in the induction in equation (30): one
additional `p`th power gains another `p - 1` levels. -/
def PrimeDepthShift
    (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∀ (r : ℕ) (w : G),
    w ∈ lowerCentralTerm G r →
      w ^ p ∈ lowerCentralTerm G (r + (p - 1))

/-- Iterating the repeatable prime-depth shift. -/
theorem depth_shift_iterate
    {G : Type u} [Group G] {p : ℕ}
    (hshift : PrimeDepthShift G p)
    (r : ℕ) (w : G)
    (hw : w ∈ lowerCentralTerm G r) :
    ∀ j : ℕ,
      w ^ (p ^ j) ∈
        lowerCentralTerm G (r + j * (p - 1)) := by
  intro j
  induction j with
  | zero =>
      simpa using hw
  | succ j ih =>
      have hnext :=
        hshift (r + j * (p - 1)) (w ^ (p ^ j)) ih
      rw [← pow_mul] at hnext
      simpa [pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using hnext

/-- Equation (30): after the initial `p^α` jump, each additional `p`th
power gains another `p - 1` lower-central levels. -/
theorem primePowerShift
    {G : Type u} [Group G] {p α r : ℕ} {w : G}
    (hinitial : InitialDepthShift G p α)
    (hshift : PrimeDepthShift G p)
    (hw : w ∈ lowerCentralTerm G r) :
    (w ^ (p ^ α) ∈ lowerCentralTerm G (r + (p - 1))) ∧
      ∀ j : ℕ,
        w ^ (p ^ (α + j)) ∈
          lowerCentralTerm G (r + (j + 1) * (p - 1)) := by
  have hfirst := hinitial r w hw
  refine ⟨hfirst, ?_⟩
  intro j
  have hiter :=
    depth_shift_iterate hshift
      (r + (p - 1)) (w ^ (p ^ α)) hfirst j
  rw [← pow_mul] at hiter
  have hindex :
      (r + (p - 1)) + j * (p - 1) =
        r + (j + 1) * (p - 1) := by
    ring
  simpa [pow_add, hindex] using hiter

/-- Equation (30) for Struik's nilpotent product `F/Fₙ`, once its two
collection estimates have been established.

The paper's final sentence says that an arbitrary `w ∈ Gᵣ` may replace the
displayed commutator.  For such a product, however, the preceding definition
of `α` as the minimum exponent among the leaves of one commutator no longer
determines a number.  The two explicit hypotheses below are the unambiguous
content needed for that substitution: the initial `p^α` jump must hold
uniformly on `Gᵣ`, and the subsequent `p`th-power jump must be repeatable. -/
theorem nilpotentCyclicProduct
    {t n p α r : ℕ} (order : Fin t → ℕ)
    {w : NilpotentCyclicProduct order n}
    (hinitial :
      InitialDepthShift
        (NilpotentCyclicProduct order n) p α)
    (hshift :
      PrimeDepthShift
        (NilpotentCyclicProduct order n) p)
    (hw :
      w ∈ lowerCentralTerm
        (NilpotentCyclicProduct order n) r) :
    (w ^ (p ^ α) ∈
        lowerCentralTerm
          (NilpotentCyclicProduct order n) (r + (p - 1))) ∧
      ∀ j : ℕ,
        w ^ (p ^ (α + j)) ∈
          lowerCentralTerm
            (NilpotentCyclicProduct order n)
            (r + (j + 1) * (p - 1)) :=
  primePowerShift hinitial hshift hw

/-- There is always a shift far enough to cross the nilpotency cutoff when
`p > 1`. -/
theorem exists_conjecturalShift
    {p n r : ℕ} (hp : 1 < p) :
    ∃ j : ℕ, n < r + (j + 1) * (p - 1) := by
  refine ⟨n + 1, ?_⟩
  have hp' : 1 ≤ p - 1 := by omega
  nlinarith

/-- The least `j` occurring in Struik's closing conjecture. -/
noncomputable def conjecturalShift
    (p n r : ℕ) (hp : 1 < p) : ℕ :=
  Nat.find (exists_conjecturalShift (p := p) (n := n) (r := r) hp)

theorem conjecturalShift_spec
    (p n r : ℕ) (hp : 1 < p) :
    n < r + (conjecturalShift p n r hp + 1) * (p - 1) :=
  Nat.find_spec
    (exists_conjecturalShift (p := p) (n := n) (r := r) hp)

theorem conjecturalShift_minimal
    (p n r : ℕ) (hp : 1 < p) {j : ℕ}
    (hj : n < r + (j + 1) * (p - 1)) :
    conjecturalShift p n r hp ≤ j :=
  Nat.find_min' _ hj

/-- Struik's closing conjecture, stated for an element `v` with the
parameters of Lemma 3. -/
def StruikConjecture
    {G : Type u} [Group G]
    (v : G) (p α n r : ℕ) (hp : 1 < p) : Prop :=
  orderOf v = p ^ (α + conjecturalShift p n r hp)

/-- The closing conjecture is false with its printed strict inequality.
For the paper's own two-involution example with `p = 2`, `α = r = 1`,
and `n = 3`, the strict inequality selects `j = 2` and predicts order
eight, while the rotation `ab` has exact order four. -/
theorem struik_involution_counterexample :
    ¬StruikConjecture
      (nilpotentCyclicGenerator orderTwoPair 3 0 *
        nilpotentCyclicGenerator orderTwoPair 3 1)
      2 1 3 1 (by omega) := by
  have hshift :
      conjecturalShift 2 3 1 (by omega) = 2 := by
    apply Nat.le_antisymm
    · exact
        conjecturalShift_minimal 2 3 1 (by omega)
          (j := 2) (by norm_num)
    · have hspec :=
        conjecturalShift_spec 2 3 1 (by omega)
      omega
  intro hconjecture
  rw [StruikConjecture,
    pair_nilpotent_rotation 3 (by omega),
    hshift] at hconjecture
  norm_num at hconjecture

end P1960
end Struik
