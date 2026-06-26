import Submission.Group.Zassenhaus.ArbitraryRankDescent
import Submission.Group.DenseGenerators.ZassenhausJenningsReduction
import Submission.Group.Zassenhaus.Core

/-!
# Paper-facing Chapman--Efrat/Zassenhaus adapters

This file records the two interfaces for the mod-`p` Zassenhaus filtration that
are used in the Hall--Zassenhaus collection argument:

* the augmentation/dimension-subgroup membership criterion; and
* the Chapman--Efrat lower-central product formula, in the recursive
  `qZassenhausFiltration` model already formalized in the `EChapma`
  namespace.
-/

open scoped Pointwise commutatorElement

namespace Submission

universe u

namespace GroupAlgebra

variable (p : ℕ) (G : Type u) [Group G]

/-- The augmentation-ideal description of the mod-`p` Zassenhaus term:
`g ∈ D_n(G)` iff `[g] - 1` lies in the `n`th power of the augmentation ideal
of `(ZMod p)[G]`. -/
theorem mod_p_sub
    (n : ℕ) (g : G) :
    g ∈ zSubgro p G n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 :
        _root_.MonoidAlgebra (ZMod p) G) ∈
        augmentationPower (ZMod p) G n := by
  exact mem_zassenhausSubgroup (p := p) (G := G)

/-- The product-form Zassenhaus filtration is contained in the augmentation
dimension subgroup.  This is the easy inclusion in the Jennings--Brauer--Lazard
description, stated with the standard `GroupAlgebra.dSubgro` API. -/
theorem explicit_filtration_dimension
    [Fact p.Prime] (n : ℕ) :
    _root_.Submission.zassenhausFiltration p G n ≤ dSubgro (ZMod p) G n := by
  exact _root_.Submission.filtration_dimension_zmod
    (p := p) (Q := G) n

/-- Under the finite killed-layer exact-generator commutator laws, the
explicit lower-central-product Zassenhaus filtration agrees with the mod-`p`
dimension subgroup.  This is the paper-facing bridge between the product
formula side of Chapman--Efrat and the augmentation-ideal side of
Jennings--Brauer--Lazard. -/
theorem explicit_filtration_laws
    [Fact p.Prime] {n : ℕ} (hn : 1 < n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ _root_.Submission.exactGeneratorSet p Q r →
            y ∈ _root_.Submission.exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ _root_.Submission.zassenhausFiltration p Q (r + s)) :
    _root_.Submission.zassenhausFiltration p G n =
      dSubgro (ZMod p) G n := by
  have hreverse :
      dSubgro (ZMod p) G n ≤
        _root_.Submission.zassenhausFiltration p G n :=
    zmod_filtration_law
      (p := p) (G := G) (n := n) hn hsucc hexact
  exact le_antisymm
    (explicit_filtration_dimension
      (p := p) (G := G) n)
    hreverse

/-- Augmentation-ideal membership for the explicit lower-central-product
Zassenhaus filtration, under the finite killed-layer exact-generator laws. -/
theorem explicit_exact_laws
    [Fact p.Prime] {n : ℕ} (hn : 1 < n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ _root_.Submission.exactGeneratorSet p Q r →
            y ∈ _root_.Submission.exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ _root_.Submission.zassenhausFiltration p Q (r + s))
    (g : G) :
    g ∈ _root_.Submission.zassenhausFiltration p G n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 :
        _root_.MonoidAlgebra (ZMod p) G) ∈
        augmentationPower (ZMod p) G n := by
  rw [explicit_filtration_laws
    (p := p) (G := G) hn hsucc hexact]
  exact
    mod_p_sub
      (p := p) (G := G) n g

end GroupAlgebra

namespace CEfrat

variable {G : Type u} [Group G]

/-- Chapman--Efrat Theorem 8.3, as formalized in the `EChapma`
development: the recursive `q`-Zassenhaus filtration for `q = p^r` is the
closed lower-central product with logarithmic exponents. -/
theorem q_logarithmic_product
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    EChapma.qZassenhausFiltration G p (p ^ r) hp n =
      EChapma.logarithmicLowerProduct (G := G) p r hp n :=
  EChapma.filtration_logarithmic_arbitrary
    (G := G) p r n hp hr hn

/-- The `q = p` specialization of Chapman--Efrat Theorem 8.3. -/
theorem p_filtration_logarithmic
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    EChapma.qZassenhausFiltration G p p hp n =
      EChapma.logarithmicLowerProduct (G := G) p 1 hp n := by
  simpa using
    q_logarithmic_product
      (G := G) p 1 n hp (by norm_num) hn

/-- The explicit lower-central-product Zassenhaus filtration used in `Submission`
is the same positive-level product as the Chapman--Efrat logarithmic
lower-central formula for `q = p`. -/
theorem explicit_logarithmic_product
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    _root_.Submission.zassenhausFiltration p G n =
      EChapma.logarithmicLowerProduct (G := G) p 1 hp n := by
  apply le_antisymm
  · rw [_root_.Submission.zassenhausFiltration, Subgroup.closure_le]
    intro g hg
    rcases hg with ⟨i, j, x, hx, hlevel, hpow⟩
    let w : ℕ := i + 1
    by_cases hle : w ≤ n
    · let c := EChapma.MDescen.ceilingLogExponent
        p hp n w
      have hwpos : 1 ≤ w := Nat.succ_le_succ (Nat.zero_le i)
      have hcj : c ≤ j :=
        EChapma.MDescen.ceiling_log
          p hp hwpos hlevel
      let idx : {s : ℕ // 1 ≤ s ∧ s ≤ n} := ⟨w, hwpos, hle⟩
      have hxw : x ∈ Subgroup.lowerCentralSeries G (w - 1) := by
        simpa [w] using hx
      have hmem :
          x ^ (p ^ j) ∈
            EChapma.subgroupPower
              (Subgroup.lowerCentralSeries G (w - 1)) (p ^ c) := by
        have hy :
            x ^ (p ^ (j - c)) ∈ Subgroup.lowerCentralSeries G (w - 1) :=
          (Subgroup.lowerCentralSeries G (w - 1)).pow_mem hxw (p ^ (j - c))
        have hpow_eq : (x ^ (p ^ (j - c))) ^ (p ^ c) = x ^ (p ^ j) := by
          rw [← pow_mul]
          have hexp : p ^ (j - c) * p ^ c = p ^ j := by
            rw [← pow_add, Nat.sub_add_cancel hcj]
          rw [hexp]
        simpa [hpow_eq] using
            EChapma.pow_subgroup_power
              (Subgroup.lowerCentralSeries G (w - 1)) (p ^ c) hy
      have hmem' :
          x ^ (p ^ j) ∈
            EChapma.subgroupPower
              (Subgroup.lowerCentralSeries G (idx.1 - 1))
              (EChapma.MDescen.logarithmicPrimePower
                p 1 hp n idx.1) := by
        simpa [idx, c, EChapma.MDescen.logarithmic_prime_power]
          using hmem
      have hle_iSup :
          EChapma.subgroupPower
              (Subgroup.lowerCentralSeries G (idx.1 - 1))
              (EChapma.MDescen.logarithmicPrimePower
                p 1 hp n idx.1) ≤
            EChapma.logarithmicLowerProduct (G := G) p 1 hp n := by
        unfold EChapma.logarithmicLowerProduct
        exact le_iSup (fun idx : {s : ℕ // 1 ≤ s ∧ s ≤ n} =>
          EChapma.subgroupPower
            (Subgroup.lowerCentralSeries G (idx.1 - 1))
            (EChapma.MDescen.logarithmicPrimePower
              p 1 hp n idx.1)) idx
      simpa [hpow] using hle_iSup hmem'
    · let idx : {s : ℕ // 1 ≤ s ∧ s ≤ n} := ⟨n, hn, le_rfl⟩
      have hni : n - 1 ≤ i := by
        dsimp [w] at hle
        omega
      have hxdeep : x ∈ Subgroup.lowerCentralSeries G (n - 1) :=
        Subgroup.lowerCentralSeries_antitone hni hx
      have hxpow : x ^ (p ^ j) ∈ Subgroup.lowerCentralSeries G (n - 1) :=
        (Subgroup.lowerCentralSeries G (n - 1)).pow_mem hxdeep (p ^ j)
      have hmem :
          x ^ (p ^ j) ∈
            EChapma.subgroupPower
              (Subgroup.lowerCentralSeries G (idx.1 - 1))
              (EChapma.MDescen.logarithmicPrimePower
                p 1 hp n idx.1) := by
        have hcoeff :
            EChapma.MDescen.logarithmicPrimePower
              p 1 hp n idx.1 = 1 := by
          change p ^ (1 *
              EChapma.MDescen.ceilingLogExponent
                p hp n n) = 1
          rw [EChapma.MDescen.ceiling_log_diagonal
            p hp hn]
          simp
        rw [hcoeff]
        simpa using hxpow
      have hle_iSup :
          EChapma.subgroupPower
              (Subgroup.lowerCentralSeries G (idx.1 - 1))
              (EChapma.MDescen.logarithmicPrimePower
                p 1 hp n idx.1) ≤
            EChapma.logarithmicLowerProduct (G := G) p 1 hp n := by
        unfold EChapma.logarithmicLowerProduct
        exact le_iSup (fun idx : {s : ℕ // 1 ≤ s ∧ s ≤ n} =>
          EChapma.subgroupPower
            (Subgroup.lowerCentralSeries G (idx.1 - 1))
            (EChapma.MDescen.logarithmicPrimePower
              p 1 hp n idx.1)) idx
      simpa [hpow] using hle_iSup hmem
  · unfold EChapma.logarithmicLowerProduct
    apply iSup_le
    intro idx
    letI : (_root_.Submission.zassenhausFiltration p G n).Normal :=
      _root_.Submission.zassenhausFiltration_normal p G n
    unfold EChapma.subgroupPower
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨x, hx, rfl⟩
    apply Subgroup.subset_closure
    refine
      ⟨idx.1 - 1,
        EChapma.MDescen.ceilingLogExponent
          p hp n idx.1,
        x, hx, ?_, ?_⟩
    · have hlevel :=
        EChapma.MDescen.mul_ceiling_log
          p hp n idx.1 idx.2.1
      simpa [Nat.sub_add_cancel idx.2.1] using hlevel
    · simp [EChapma.MDescen.logarithmic_prime_power]

/-- Membership form of
`explicit_logarithmic_product`. -/
theorem explicit_filtration_logarithmic
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (g : G) :
    g ∈ _root_.Submission.zassenhausFiltration p G n ↔
      g ∈ EChapma.logarithmicLowerProduct (G := G) p 1 hp n := by
  rw [explicit_logarithmic_product
    (G := G) p n hp hn]

end CEfrat

namespace Ctex

variable {G : Type u} [Group G]

open GroupAlgebra

/--
Paper-facing augmentation-ideal membership criterion for the mod-`p`
Zassenhaus subgroup.
-/
theorem chapman_efrat_criterion
    (p n : ℕ) (g : G) :
    g ∈ _root_.Submission.GroupAlgebra.zSubgro p G n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 :
        _root_.MonoidAlgebra (ZMod p) G) ∈
        _root_.Submission.GroupAlgebra.augmentationPower (ZMod p) G n :=
  GroupAlgebra.mod_p_sub
    (p := p) (G := G) n g

/--
Paper-facing `q = p` Chapman--Efrat lower-central product formula for the
explicit Zassenhaus filtration used by `Submission`.
-/
theorem chapman_efrat_zassenhaus
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    _root_.Submission.zassenhausFiltration p G n =
      EChapma.logarithmicLowerProduct (G := G) p 1 hp n :=
  CEfrat.explicit_logarithmic_product
    (G := G) p n hp hn

/-- Membership form of `chapman_efrat_zassenhaus`. -/
theorem chapman_efrat_formula
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (g : G) :
    g ∈ _root_.Submission.zassenhausFiltration p G n ↔
      g ∈ EChapma.logarithmicLowerProduct (G := G) p 1 hp n :=
  CEfrat.explicit_filtration_logarithmic
    (G := G) p n hp hn g

/--
Paper-facing augmentation criterion for the explicit product-form
Zassenhaus filtration, stated with the exact-generator laws currently used by
the Submission dimension-subgroup API.
-/
theorem chapman_efrat_laws
    {p n : ℕ} [Fact p.Prime] (hn : 1 < n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        _root_.Submission.zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ _root_.Submission.exactGeneratorSet p Q r →
            y ∈ _root_.Submission.exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ _root_.Submission.zassenhausFiltration p Q (r + s))
    (g : G) :
    g ∈ _root_.Submission.zassenhausFiltration p G n ↔
      (_root_.MonoidAlgebra.of (ZMod p) G g - 1 :
        _root_.MonoidAlgebra (ZMod p) G) ∈
        _root_.Submission.GroupAlgebra.augmentationPower (ZMod p) G n :=
  by
    exact
      explicit_exact_laws
        (p := p) (G := G) hn hsucc hexact g

end Ctex

end Submission
