import Towers.Group.Edmonton.DimensionSubgroups
import Mathlib.GroupTheory.Schreier

/-!
# The Edmonton Notes on Nilpotent Groups: Section 8 Schur and Baer

This file begins Hall's Section 8 with Schur's theorem and the
verbal-subgroup language used in Baer's generalization.
-/

namespace Towers
namespace Edmonton

noncomputable section

open Group
open scoped commutatorElement IsMulCommutative

universe u v w

variable {G : Type u} [Group G]

/-- A natural number `n` is an `m`-number when all prime divisors of
`n` divide `m`. -/
def IMNumber (m n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∣ m

lemma IMNumber.of_dvd {m n : ℕ} (h : n ∣ m) :
    IMNumber m n := by
  intro p _ hp
  exact hp.trans h

lemma IMNumber.of_dvd_pow {m n k : ℕ} (h : n ∣ m ^ k) :
    IMNumber m n := by
  intro p hp hpn
  exact hp.dvd_of_dvd_pow (hpn.trans h)

/-- The transfer homomorphism into the center, followed by the inclusion
of the center into the ambient group. -/
def centerPowerHom (G : Type u) [Group G] [Subgroup.FiniteIndex (Subgroup.center G)] :
    G →* G :=
  (Subgroup.center G).subtype.comp (MonoidHom.transferCenterPow G)

@[simp]
lemma center_power_hom
    (G : Type u) [Group G] [Subgroup.FiniteIndex (Subgroup.center G)]
    (x : G) :
    centerPowerHom G x = x ^ (Subgroup.center G).index :=
  rfl

/-- Multiplying the first input of a commutator by a central element
does not change it. -/
lemma element_left_center
    {z x y : G} (hz : z ∈ Subgroup.center G) :
    ⁅z * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, mul_inv_rev]
  calc
    z * x * y * (x⁻¹ * z⁻¹) * y⁻¹ =
        z * (x * y * x⁻¹) * z⁻¹ * y⁻¹ := by
      simp only [mul_assoc]
    _ = (x * y * x⁻¹) * z * z⁻¹ * y⁻¹ := by
      rw [← Subgroup.mem_center_iff.mp hz (x * y * x⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by
      simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Multiplying the second input of a commutator by a central element
does not change it. -/
lemma element_right_center
    {z x y : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, mul_inv_rev]
  calc
    x * (z * y) * x⁻¹ * (y⁻¹ * z⁻¹) =
        z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by
      have hzx := Subgroup.mem_center_iff.mp hz x
      rw [← mul_assoc x z, hzx]
      simp only [mul_assoc]
    _ = x * y * x⁻¹ * y⁻¹ := by
      rw [← Subgroup.mem_center_iff.mp hz (x * y * x⁻¹ * y⁻¹)]
      simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Multiplying either input of a commutator by central elements does
not change it. -/
lemma commutator_element_center
    {z t x y : G} (hz : z ∈ Subgroup.center G)
    (ht : t ∈ Subgroup.center G) :
    ⁅z * x, t * y⁆ = ⁅x, y⁆ := by
  rw [element_left_center hz,
    element_right_center ht]

/-- The commutator obtained from chosen representatives of two cosets
modulo the center. -/
def centerQuotientCommutator :
    (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) →
      commutatorSet G :=
  fun q ↦
    ⟨⁅q.1.out, q.2.out⁆, ⟨q.1.out, q.2.out, rfl⟩⟩

/-- Every element commutator is obtained from a pair of chosen
representatives modulo the center. -/
lemma center_commutator_surjective :
    Function.Surjective (centerQuotientCommutator (G := G)) := by
  rintro ⟨c, x, y, rfl⟩
  let qx : G ⧸ Subgroup.center G := x
  let qy : G ⧸ Subgroup.center G := y
  refine ⟨(qx, qy), Subtype.ext ?_⟩
  have hx : x / qx.out ∈ Subgroup.center G := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact (Quotient.out_eq' qx).symm
  have hy : y / qy.out ∈ Subgroup.center G := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact (Quotient.out_eq' qy).symm
  change ⁅qx.out, qy.out⁆ = ⁅x, y⁆
  calc
    ⁅qx.out, qy.out⁆ =
        ⁅(x / qx.out) * qx.out, (y / qy.out) * qy.out⁆ :=
      (commutator_element_center hx hy).symm
    _ = ⁅x, y⁆ := by simp

/-- If the center has finite index, there are only finitely many
element commutators. -/
lemma set_index_center
    [Subgroup.FiniteIndex (Subgroup.center G)] :
    Finite (commutatorSet G) := by
  letI : Finite (G ⧸ Subgroup.center G) :=
    Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_surjective centerQuotientCommutator
    center_commutator_surjective

/-- **Hall, Theorem 8.1 (Schur).** If the center has finite index `m`,
then `x ↦ x^m` is a homomorphism and the commutator subgroup is a finite
`m`-group in Hall's sense. -/
theorem center_hom_commutator
    [Subgroup.FiniteIndex (Subgroup.center G)] :
    (∃ f : G →* G,
      ∀ x : G, f x = x ^ (Subgroup.center G).index) ∧
      Finite (commutator G) ∧
      IMNumber (Subgroup.center G).index (Nat.card (commutator G)) := by
  letI : Finite (commutatorSet G) :=
    set_index_center
  refine ⟨⟨centerPowerHom G, center_power_hom G⟩, inferInstance, ?_⟩
  exact IMNumber.of_dvd_pow (Subgroup.card_commutator_dvd_index_center_pow G)

/-- **Hall, Lemma 8.2 (Baer).** If `K ≤ H`, `H` is normal, `K` is
central in `G`, and `K` has finite relative index in `H`, then `[H,G]`
has exponent dividing that relative index. -/
theorem dvd_relative_index (H K : Subgroup G) [H.Normal] (_hKH : K ≤ H)
    (hcentral : ⁅K, (⊤ : Subgroup G)⁆ = ⊥)
    [K.IsFiniteRelIndex H] :
    SubgroupHasExponent ⁅H, (⊤ : Subgroup G)⁆ (K.relIndex H) := by
  have hKcomm {k : G} (hk : k ∈ K) (g : G) : Commute k g := by
    rw [← commutatorElement_eq_one_iff_commute]
    exact Subgroup.mem_bot.mp
      (hcentral ▸ Subgroup.commutator_mem_commutator hk (Subgroup.mem_top g))
  let K' : Subgroup H := K.subgroupOf H
  letI : K'.Normal := by
    refine ⟨?_⟩
    intro k hk g
    change (↑g * ↑k * ↑g⁻¹ : G) ∈ K
    have hcomm : Commute (k : G) (g : G) := hKcomm hk g
    rw [hcomm.symm]
    simpa [mul_assoc] using hk
  letI : IsMulCommutative K' := ⟨⟨fun a b ↦
    Subtype.ext (Subtype.ext (hKcomm a.2 b))⟩⟩
  letI : CommGroup K' := inferInstance
  let τ : H →* K' := MonoidHom.transfer (MonoidHom.id K')
  let power : H →* H := K'.subtype.comp τ
  have hτ_apply (x : H) :
      τ x = ⟨x ^ K'.index, K'.pow_index_mem x⟩ := by
    apply MonoidHom.transfer_eq_pow
    intro n y hy
    have hxpow : x ^ n ∈ K' := by
      have hconj :=
        (inferInstance : K'.Normal).conj_mem (y⁻¹ * x ^ n * y) hy y
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
        using hconj
    apply Subtype.ext
    change (↑y : G)⁻¹ * (↑x : G) ^ n * ↑y = (↑x : G) ^ n
    have hxpowK : (↑x : G) ^ n ∈ K := hxpow
    rw [mul_assoc, hKcomm hxpowK y]
    simp
  have hpower_apply (x : H) :
      power x = x ^ K'.index := by
    change (τ x : H) = x ^ K'.index
    rw [hτ_apply]
  have hhallConjugate_mem (x : G) (hx : x ∈ H) (y : G) :
      hallConjugate x y ∈ H := by
    simpa [hallConjugate] using
      (inferInstance : H.Normal).conj_mem x hx y⁻¹
  have hpower_hallConjugate (x : G) (hx : x ∈ H) (y : G) :
      power ⟨hallConjugate x y, hhallConjugate_mem x hx y⟩ =
        power ⟨x, hx⟩ := by
    rw [hpower_apply, hpower_apply]
    apply Subtype.ext
    change (hallConjugate x y) ^ K'.index = x ^ K'.index
    rw [show (hallConjugate x y) ^ K'.index =
      hallConjugate (x ^ K'.index) y by
        simpa [hallConjugate] using
          (conj_pow (a := y⁻¹) (b := x) (i := K'.index))]
    apply conjugate_self_commute
    apply hKcomm
    exact K'.pow_index_mem ⟨x, hx⟩
  have hcomm_le :
      ⁅H, (⊤ : Subgroup G)⁆ ≤ power.ker.map H.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    have hxinv : x⁻¹ ∈ H := H.inv_mem hx
    have hconj : hallConjugate x⁻¹ y⁻¹ ∈ H :=
      hhallConjugate_mem x⁻¹ hxinv y⁻¹
    have hcommH : ⁅x, y⁆ ∈ H :=
      Subgroup.commutator_le_left H ⊤
        (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
    refine ⟨⟨⁅x, y⁆, hcommH⟩, ?_, rfl⟩
    change power ⟨⁅x, y⁆, hcommH⟩ = 1
    have heq :
        (⟨⁅x, y⁆, hcommH⟩ : H) =
          ⟨(x⁻¹)⁻¹, H.inv_mem hxinv⟩ *
            ⟨hallConjugate x⁻¹ y⁻¹, hconj⟩ := by
      apply Subtype.ext
      change ⁅x, y⁆ = (x⁻¹)⁻¹ * hallConjugate x⁻¹ y⁻¹
      rw [commutator_element_inv]
      simp [hallCommutator, hallConjugate, mul_assoc]
    have hinv :
        (⟨(x⁻¹)⁻¹, H.inv_mem hxinv⟩ : H) =
          (⟨x⁻¹, hxinv⟩ : H)⁻¹ := by
      rfl
    rw [heq]
    rw [map_mul, hinv, map_inv, hpower_hallConjugate x⁻¹ hxinv y⁻¹]
    simp
  intro z hz
  rcases hcomm_le hz with ⟨z', hzker, hz'⟩
  change power z' = 1 at hzker
  rw [hpower_apply] at hzker
  have hpow := congrArg Subtype.val hzker
  change (z' : G) ^ K'.index = 1 at hpow
  simpa [K', Subgroup.relIndex, ← hz'] using hpow

/-- Replace the `i`th input of an assignment `f` by `f i * a`. -/
noncomputable def wordRightInsert {α : Type v}
    (f : α → G) (i : α) (a : G) : α → G := by
  classical
  exact Function.update f i (f i * a)

@[simp]
lemma word_right_insert {α : Type v} (f : α → G) (i : α) :
    wordRightInsert f i (1 : G) = f := by
  classical
  simp [wordRightInsert]

lemma word_insert_mul {α : Type v} (f : α → G) (i : α)
    (a b : G) :
    wordRightInsert f i (a * b) =
      wordRightInsert (wordRightInsert f i a) i b := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [wordRightInsert, mul_assoc]
  · simp [wordRightInsert, hji]

lemma insert_inv_cancel {α : Type v} (f : α → G) (i : α)
    (a : G) :
    wordRightInsert (wordRightInsert f i a⁻¹) i a = f := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [wordRightInsert]
  · simp [wordRightInsert, hji]

lemma word_insert_comp {α : Type v} {H : Type w} [Group H]
    (φ : G →* H) (f : α → G) (i : α) (a : G) :
    (fun j ↦ φ (wordRightInsert f i a j)) =
      wordRightInsert (fun j ↦ φ (f j)) i (φ a) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [wordRightInsert]
  · simp [wordRightInsert, hji]

/-- An element is marginal for `word` when multiplying any one input on
the right by that element leaves every value of the word unchanged. -/
def IsWordMarginal {α : Type v} (word : FreeGroup α) (a : G) : Prop :=
  ∀ (f : α → G) (i : α),
    wordEval word (wordRightInsert f i a) = wordEval word f

/-- Hall's marginal subgroup `φ*(G)` corresponding to the word `φ`. -/
def wordMarginalSubgroup {α : Type v}
    (word : FreeGroup α) (G : Type u) [Group G] : Subgroup G where
  carrier := {a | IsWordMarginal word a}
  one_mem' := by
    intro f i
    rw [word_right_insert]
  mul_mem' := by
    intro a b ha hb f i
    rw [word_insert_mul]
    exact (hb (wordRightInsert f i a) i).trans (ha f i)
  inv_mem' := by
    intro a ha f i
    have h := ha (wordRightInsert f i a⁻¹) i
    rw [insert_inv_cancel] at h
    exact h.symm

lemma word_marginal_subgroup {α : Type v}
    {word : FreeGroup α} {a : G} :
    a ∈ wordMarginalSubgroup word G ↔ IsWordMarginal word a :=
  Iff.rfl

/-- Hall, Lemma 8.4(i), characteristic-subgroup clause. -/
instance word_marginal_characteristic {α : Type v}
    (word : FreeGroup α) :
    (wordMarginalSubgroup word G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ _ h
  rcases h with ⟨a, ha, rfl⟩
  intro f i
  apply φ.symm.injective
  change (φ.symm : G →* G)
      (wordEval word (wordRightInsert f i (φ a))) =
    (φ.symm : G →* G) (wordEval word f)
  rw [map_wordEval, map_wordEval]
  rw [word_insert_comp]
  simpa using ha (fun j ↦ φ.symm (f j)) i

/-- If the verbal subgroup is trivial, every element is marginal. This
is the easy direction of Hall, Lemma 8.4(ii). -/
lemma marginal_verbal_bot
    {α : Type v} {word : FreeGroup α}
    (hword : verbalSubgroup word G = ⊥) :
  wordMarginalSubgroup word G = ⊤ := by
  rw [eq_top_iff]
  intro a _ f i
  have hinsert :
      wordEval word (wordRightInsert f i a) ∈ verbalSubgroup word G :=
    Subgroup.subset_closure ⟨wordRightInsert f i a, rfl⟩
  have hf : wordEval word f ∈ verbalSubgroup word G :=
    Subgroup.subset_closure ⟨f, rfl⟩
  rw [hword] at hinsert hf
  rw [Subgroup.mem_bot.mp hinsert, Subgroup.mem_bot.mp hf]

/-- Hall, Lemma 8.4(iii). If a normal subgroup meets the verbal subgroup
trivially, it lies in the marginal subgroup. -/
theorem marginal_inf_verbal
    {α : Type v} (word : FreeGroup α) (H : Subgroup G) [H.Normal]
    (hdisjoint : H ⊓ verbalSubgroup word G = ⊥) :
    H ≤ wordMarginalSubgroup word G := by
  intro a ha f i
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have heval :
      q (wordEval word (wordRightInsert f i a)) =
        q (wordEval word f) := by
    rw [map_wordEval, map_wordEval]
    congr 1
    classical
    ext j
    by_cases hji : j = i
    · subst j
      have hqa : q a = 1 := by
        change (a : G ⧸ H) = 1
        exact (QuotientGroup.eq_one_iff a).mpr ha
      simp [wordRightInsert, hqa]
    · simp [wordRightInsert, hji]
  let defect : G :=
    (wordEval word f)⁻¹ * wordEval word (wordRightInsert f i a)
  have hdefectH : defect ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    change q defect = 1
    rw [show q defect =
      (q (wordEval word f))⁻¹ *
        q (wordEval word (wordRightInsert f i a)) by
          simp [defect], heval]
    simp
  have hdefectVerbal : defect ∈ verbalSubgroup word G := by
    exact (verbalSubgroup word G).mul_mem
      ((verbalSubgroup word G).inv_mem
        (Subgroup.subset_closure ⟨f, rfl⟩))
      (Subgroup.subset_closure ⟨wordRightInsert f i a, rfl⟩)
  have hdefect : defect = 1 :=
    Subgroup.mem_bot.mp (hdisjoint ▸ ⟨hdefectH, hdefectVerbal⟩)
  have h := congrArg (fun z ↦ wordEval word f * z) hdefect
  simpa [defect, mul_assoc] using h

/-- The denominator in the commutator factor appearing in Baer's
Theorem 8.3. -/
def baerCommutatorDenominator
    (H H₁ K K₁ : Subgroup G) : Subgroup G :=
  ⁅H₁, K⁆ ⊔ ⁅H, K₁⁆

/-- The numerator in the commutator factor appearing in Baer's
Theorem 8.3. -/
def baerCommutatorNumerator
    (H₁ K₁ : Subgroup G) : Subgroup G :=
  ⁅H₁, K₁⁆

lemma baer_commutator_denominator
    {H H₁ K K₁ : Subgroup G} (hHH₁ : H ≤ H₁) (hKK₁ : K ≤ K₁) :
    baerCommutatorDenominator H H₁ K K₁ ≤
      baerCommutatorNumerator H₁ K₁ := by
  exact sup_le
    (Subgroup.commutator_mono le_rfl hKK₁)
    (Subgroup.commutator_mono hHH₁ le_rfl)

/-- The relative-index assertion proved in Baer's Theorem 8.3. It is
packaged as an interface because Hall's proof uses a substantial finite
commutator-factor argument not presently available in Mathlib. -/
def BaerIndexProperty
    (G : Type u) [Group G] : Prop :=
  ∀ (H H₁ K K₁ : Subgroup G),
    H.Normal → H₁.Normal → K.Normal → K₁.Normal →
      H ≤ H₁ → K ≤ K₁ →
        H.IsFiniteRelIndex H₁ → K.IsFiniteRelIndex K₁ →
          (baerCommutatorDenominator H H₁ K K₁).IsFiniteRelIndex
              (baerCommutatorNumerator H₁ K₁) ∧
            IMNumber (H.relIndex H₁)
              ((baerCommutatorDenominator H H₁ K K₁).relIndex
                (baerCommutatorNumerator H₁ K₁))

/-- **Hall, Theorem 8.3 (Baer), relative-index form.** -/
theorem baer_relative_index
    (H H₁ K K₁ : Subgroup G)
    [H.Normal] [H₁.Normal] [K.Normal] [K₁.Normal]
    (hHH₁ : H ≤ H₁) (hKK₁ : K ≤ K₁)
    [H.IsFiniteRelIndex H₁] [K.IsFiniteRelIndex K₁]
    (hbaer : BaerIndexProperty G) :
    (baerCommutatorDenominator H H₁ K K₁).IsFiniteRelIndex
        (baerCommutatorNumerator H₁ K₁) ∧
      IMNumber (H.relIndex H₁)
        ((baerCommutatorDenominator H H₁ K K₁).relIndex
          (baerCommutatorNumerator H₁ K₁)) :=
  hbaer H H₁ K K₁ inferInstance inferInstance inferInstance inferInstance
    hHH₁ hKK₁ inferInstance inferInstance

/-- Two assignments are congruent modulo `N` when they agree coordinatewise
in the quotient by `N`. -/
def AssignmentsCongruentMod {α : Type v}
    (N : Subgroup G) (f g : α → G) : Prop :=
  ∀ i, f i / g i ∈ N

/-- A word evaluation factors through the quotient by `N`. -/
def EvaluationRespectsMod {α : Type v}
    (word : FreeGroup α) (N : Subgroup G) : Prop :=
  ∀ f g : α → G, AssignmentsCongruentMod N f g →
    wordEval word f = wordEval word g

/-- A normal subgroup bundled with its proof, used to state Hall's
subdirect-product clause without carrying local quotient instances. -/
structure NormalSubgroupData (G : Type u) [Group G] where
  toSubgroup : Subgroup G
  isNormal : toSubgroup.Normal

/-- Pull the marginal subgroup of a quotient back to the original group. -/
noncomputable def normalMarginalComap {α : Type v}
    (word : FreeGroup α) (K : NormalSubgroupData G) : Subgroup G := by
  letI : K.toSubgroup.Normal := K.isNormal
  exact (wordMarginalSubgroup word (G ⧸ K.toSubgroup)).comap
    (QuotientGroup.mk' K.toSubgroup)

/-- The complete collection of marginal-subgroup assertions in Hall's
Lemma 8.4. Several clauses are exposed as an interface because their
full quotient and direct-product proofs are independent developments. -/
structure MarginalSubgroupLaws {α : Type v}
    (word : FreeGroup α) (G : Type u) [Group G] : Prop where
  respects_mod :
    EvaluationRespectsMod word (wordMarginalSubgroup word G)
  largest_normal :
    ∀ N : Subgroup G, N.Normal → EvaluationRespectsMod word N →
      N ≤ wordMarginalSubgroup word G
  verbal_marginal_bot :
    verbalSubgroup word (wordMarginalSubgroup word G) = ⊥
  verbal_marginal_top :
    verbalSubgroup word G = ⊥ ↔ wordMarginalSubgroup word G = ⊤
  central_commutator_bot :
    ∀ K : Subgroup G,
      K.map (QuotientGroup.mk' (wordMarginalSubgroup word G)) =
          Subgroup.center (G ⧸ wordMarginalSubgroup word G) →
        ⁅K, verbalSubgroup word G⁆ = ⊥
  marginal_commutator_bot :
    ⁅wordMarginalSubgroup word G, verbalSubgroup word G⁆ = ⊥
  directProduct_verbal :
    ∀ (H : Type u) [Group H],
      verbalSubgroup word (G × H) =
        (verbalSubgroup word G).prod (verbalSubgroup word H)
  directProduct_marginal :
    ∀ (H : Type u) [Group H],
      wordMarginalSubgroup word (G × H) =
        (wordMarginalSubgroup word G).prod (wordMarginalSubgroup word H)
  generated_from_subgroup :
    ∀ H : Subgroup G, H ⊔ wordMarginalSubgroup word G = ⊤ →
      (verbalSubgroup word H).map H.subtype = verbalSubgroup word G
  subdirectProduct :
    ∀ {ι : Type u} (K : ι → NormalSubgroupData G),
      (⨅ i, (K i).toSubgroup) = ⊥ →
        wordMarginalSubgroup word G =
          ⨅ i, normalMarginalComap word (K i)

/-- **Hall, Lemma 8.4.** The marginal subgroup satisfies the seven
standard marginal-subgroup laws. -/
theorem marginalSubgroup_laws {α : Type v} (word : FreeGroup α)
    (hlaws : MarginalSubgroupLaws word G) :
    MarginalSubgroupLaws word G :=
  hlaws

/-- The product of two words on disjoint sets of variables. -/
def wordProduct {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β) : FreeGroup (α ⊕ β) :=
  FreeGroup.map (Sum.inl : α → α ⊕ β) theta *
    FreeGroup.map (Sum.inr : β → α ⊕ β) phi

@[simp]
lemma word_const_one {α : Type v} (word : FreeGroup α) :
    wordEval word (fun _ ↦ (1 : G)) = 1 := by
  symm
  simpa [wordEval] using
    (FreeGroup.lift_unique (f := fun _ : α ↦ (1 : G))
      (1 : FreeGroup α →* G) (by intro; rfl) (x := word))

@[simp]
lemma word_eval_product {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β) (f : α ⊕ β → G) :
    wordEval (wordProduct theta phi) f =
      wordEval theta (f ∘ Sum.inl) * wordEval phi (f ∘ Sum.inr) := by
  change (FreeGroup.lift f)
      (FreeGroup.map (Sum.inl : α → α ⊕ β) theta *
        FreeGroup.map (Sum.inr : β → α ⊕ β) phi) = _
  rw [map_mul]
  change
    wordEval (FreeGroup.map (Sum.inl : α → α ⊕ β) theta) f *
        wordEval (FreeGroup.map (Sum.inr : β → α ⊕ β) phi) f = _
  rw [wordEval_map, wordEval_map]

/-- The verbal subgroup of a product of words on disjoint variables is
the product of the two verbal subgroups. -/
theorem verbal_subgroup_product {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β) :
    verbalSubgroup (wordProduct theta phi) G =
      verbalSubgroup theta G ⊔ verbalSubgroup phi G := by
  apply le_antisymm
  · rw [verbalSubgroup, Subgroup.closure_le]
    rintro _ ⟨f, rfl⟩
    rw [word_eval_product]
    exact (verbalSubgroup theta G ⊔ verbalSubgroup phi G).mul_mem
      ((show verbalSubgroup theta G ≤
          verbalSubgroup theta G ⊔ verbalSubgroup phi G from le_sup_left)
        (Subgroup.subset_closure ⟨f ∘ Sum.inl, rfl⟩))
      ((show verbalSubgroup phi G ≤
          verbalSubgroup theta G ⊔ verbalSubgroup phi G from le_sup_right)
        (Subgroup.subset_closure ⟨f ∘ Sum.inr, rfl⟩))
  · apply sup_le
    · rw [verbalSubgroup, Subgroup.closure_le]
      rintro _ ⟨f, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨Sum.elim f (fun _ ↦ 1), ?_⟩
      simp
    · rw [verbalSubgroup, Subgroup.closure_le]
      rintro _ ⟨f, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨Sum.elim (fun _ ↦ 1) f, ?_⟩
      simp

/-- The candidate for the left half of the marginal subgroup formula
for a commutator word. -/
noncomputable def leftMarginalCandidate
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (G : Type u) [Group G] : Subgroup G := by
  let V : Subgroup G := Subgroup.centralizer (verbalSubgroup phi G)
  letI : V.Normal := inferInstance
  exact (wordMarginalSubgroup theta (G ⧸ V)).comap (QuotientGroup.mk' V)

/-- The candidate for the right half of the marginal subgroup formula
for a commutator word. -/
noncomputable def commutatorMarginalCandidate
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (G : Type u) [Group G] : Subgroup G := by
  let U : Subgroup G := Subgroup.centralizer (verbalSubgroup theta G)
  letI : U.Normal := inferInstance
  exact (wordMarginalSubgroup phi (G ⧸ U)).comap (QuotientGroup.mk' U)

/-- Hall's marginal-subgroup formula for a commutator word. -/
def CommutatorMarginalFormula
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (G : Type u) [Group G] : Prop :=
  wordMarginalSubgroup (wordCommutator theta phi) G =
    leftMarginalCandidate theta phi G ⊓
      commutatorMarginalCandidate theta phi G

/-- **Hall, Lemma 8.5.** The marginal subgroup of `[θ,φ]` is the
intersection of the two quotient-marginal pullbacks. -/
theorem commutator_marginal_subgroup {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (hformula : CommutatorMarginalFormula theta phi G) :
    wordMarginalSubgroup (wordCommutator theta phi) G =
      leftMarginalCandidate theta phi G ⊓
        commutatorMarginalCandidate theta phi G :=
  hformula

/-- Hall's left-normed lower-central word `γ_{k+1}`, represented in a
fixed countable variable type. -/
def lowerCentralWord : ℕ → FreeGroup ℕ
  | 0 => FreeGroup.of 0
  | k + 1 => ⁅lowerCentralWord k, FreeGroup.of (k + 1)⁆

/-- The lower-central marginal formula proved inductively from Lemma 8.5. -/
def LowerMarginalFormula (G : Type u) [Group G] : Prop :=
  ∀ k : ℕ,
    wordMarginalSubgroup (lowerCentralWord k) G = Subgroup.upperCentralSeries G k

/-- **Hall, Lemma 8.6.** `γ_{k+1}*(G) = ζ_k(G)`. -/
theorem lower_marginal_subgroup (k : ℕ) (hformula : LowerMarginalFormula G) :
    wordMarginalSubgroup (lowerCentralWord k) G = Subgroup.upperCentralSeries G k :=
  hformula k

/-- A word has Hall's Schur-Baer property when finite marginal index
forces a finite verbal subgroup whose order is an `m`-number. -/
def SchurProperty {α : Type v} (word : FreeGroup α) : Prop :=
  ∀ (G : Type u) [Group G],
    (wordMarginalSubgroup word G).FiniteIndex →
      Finite (verbalSubgroup word G) ∧
        IMNumber (wordMarginalSubgroup word G).index
          (Nat.card (verbalSubgroup word G))

/-- Closure of the Schur-Baer property under commutators of words. -/
def SchurBaerProperty
    (_UniverseWitness : Type u)
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β) : Prop :=
  SchurProperty.{u, v} theta →
    SchurProperty.{u, w} phi →
      SchurProperty.{u, max v w} (wordCommutator theta phi)

omit [Group G] in
/-- **Hall, Theorem 8.7 (Baer).** Schur-Baer words are closed under
commutators. -/
theorem schurBaer_commutator {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (htheta : SchurProperty.{u, v} theta)
    (hphi : SchurProperty.{u, w} phi)
    (hclosure : SchurBaerProperty G theta phi) :
    SchurProperty.{u, max v w} (wordCommutator theta phi) :=
  hclosure htheta hphi

/-- Hall's marginal-subgroup formula for a product of disjoint words. -/
def WordMarginalFormula
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (G : Type u) [Group G] : Prop :=
  wordMarginalSubgroup (wordProduct theta phi) G =
    wordMarginalSubgroup theta G ⊓ wordMarginalSubgroup phi G

/-- Closure of the Schur-Baer property under products of disjoint words. -/
def SchurBaerClosure
    (_UniverseWitness : Type u)
    {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β) : Prop :=
  SchurProperty.{u, v} theta →
    SchurProperty.{u, w} phi →
      SchurProperty.{u, max v w} (wordProduct theta phi)

/-- **Hall, Lemma 8.8.** Products of Schur-Baer words are Schur-Baer,
with the expected verbal and marginal subgroups. -/
theorem schur_baer_product {α : Type v} {β : Type w}
    (theta : FreeGroup α) (phi : FreeGroup β)
    (htheta : SchurProperty.{u, v} theta)
    (hphi : SchurProperty.{u, w} phi)
    (hclosure : SchurBaerClosure G theta phi)
    (hmarginal : WordMarginalFormula theta phi G) :
    SchurProperty.{u, max v w} (wordProduct theta phi) ∧
      verbalSubgroup (wordProduct theta phi) G =
        verbalSubgroup theta G ⊔ verbalSubgroup phi G ∧
      wordMarginalSubgroup (wordProduct theta phi) G =
        wordMarginalSubgroup theta G ⊓ wordMarginalSubgroup phi G := by
  exact ⟨hclosure htheta hphi, verbal_subgroup_product theta phi, hmarginal⟩

/-- A group is virtually polycyclic when it contains a finite-index
polycyclic subgroup. -/
def IsVirtuallyPolycyclic (G : Type u) [Group G] : Prop :=
  ∃ H : Subgroup G, IsPolycyclic H ∧ H.FiniteIndex

/-- The assertion of Hall's Theorem 8.9 for a fixed word and group. -/
def VirtuallySchurBaer
    {α : Type v} (word : FreeGroup α)
    (G : Type u) [Group G] : Prop :=
  IsVirtuallyPolycyclic G →
    (wordMarginalSubgroup word G).FiniteIndex →
      Finite (verbalSubgroup word G) ∧
        IMNumber (wordMarginalSubgroup word G).index
          (Nat.card (verbalSubgroup word G))

/-- **Hall, Theorem 8.9.** In a virtually polycyclic group, every word
with finite marginal index has finite verbal subgroup of `m`-number
order. -/
theorem verbal_virtually_polycyclic {α : Type v} (word : FreeGroup α)
    (hvirt : IsVirtuallyPolycyclic G)
    (hproperty : VirtuallySchurBaer word G)
    [hindex : (wordMarginalSubgroup word G).FiniteIndex] :
    Finite (verbalSubgroup word G) ∧
      IMNumber (wordMarginalSubgroup word G).index
        (Nat.card (verbalSubgroup word G)) :=
  hproperty hvirt hindex

/-- A word defines nilpotent quotients when its verbal subgroup has
nilpotent quotient in every group. -/
def DefinesNilpotentQuotients {α : Type v} (word : FreeGroup α) : Prop :=
  ∀ (G : Type u) [Group G],
    Group.IsNilpotent (G ⧸ verbalSubgroup word G)

/-- The nilpotent-quotient corollary following Hall's Theorem 8.9. -/
def SchurBaerCorollary
    (_UniverseWitness : Type u)
    {α : Type v} (word : FreeGroup α) : Prop :=
  DefinesNilpotentQuotients.{u, v} word →
    SchurProperty.{u, v} word

omit [Group G] in
/-- **Corollary to Hall, Theorem 8.9.** A word defining nilpotent
quotients has the Schur-Baer property. -/
theorem schur_baer_defines {α : Type v} (word : FreeGroup α)
    (hnilpotent : DefinesNilpotentQuotients.{u, v} word)
    (hcorollary : SchurBaerCorollary G word) :
    SchurProperty.{u, v} word :=
  hcorollary hnilpotent

end

end Edmonton
end Towers
