import Submission.Group.ZassenhausFrattini

namespace Submission

open scoped commutatorElement

namespace GroupAlgebra

noncomputable section

variable {R G : Type*} [CommRing R] [Group G]

/-! Basic augmentation-ideal lemmas. -/

instance instSidedIdeal :
    (augmentationIdeal R G).IsTwoSided := by
  exact augmentation_ideal_sided R G

instance instSidedPower (n : ℕ) :
    (augmentationPower R G n).IsTwoSided := by
  exact augmentation_two_sided R G n

theorem mem_augmentation_iff (x : MonoidAlgebra R G) :
    x ∈ augmentationIdeal R G ↔ augmentation R G x = 0 := by
  exact mem_augmentationIdeal R G

theorem augmentation_span_sub :
    augmentationIdeal R G =
      Ideal.span (Set.range (fun g : G =>
        (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G))) := by
  simpa only [augmentationGeneratorIdeal, Set.range, eq_comm] using
    (augmentation_generator_ideal R G).symm

theorem augmentation_two_ideal :
    augmentationPower R G 2 ≤ augmentationIdeal R G := by
  simpa using (augmentationPower_antitone R G (by norm_num : 1 ≤ 2))

theorem mul_augmentation_ideal
    {x y : MonoidAlgebra R G}
    (hx : x ∈ augmentationIdeal R G)
    (hy : y ∈ augmentationIdeal R G) :
    x * y ∈ augmentationPower R G 2 := by
  simpa using
    (mul_augmentation_add (R := R) (G := G) (m := 1) (n := 1)
      (by simpa using hx) (by simpa using hy))

theorem mk_augmentation_power
    {n : ℕ} (x : MonoidAlgebra R G) :
    Ideal.Quotient.mk (augmentationPower R G n) x = 0 ↔
      x ∈ augmentationPower R G n := by
  exact Ideal.Quotient.eq_zero_iff_mem

/-! The basic congruences modulo `I^2`. -/

theorem of_sub_eq (g h : G) :
    (_root_.MonoidAlgebra.of R G (g * h) - 1 : MonoidAlgebra R G) =
      (_root_.MonoidAlgebra.of R G g - 1) *
        (_root_.MonoidAlgebra.of R G h - 1) +
      (_root_.MonoidAlgebra.of R G g - 1) +
      (_root_.MonoidAlgebra.of R G h - 1) := by
  rw [map_mul]
  noncomm_ring

theorem sub_sum_square (g h : G) :
    ((_root_.MonoidAlgebra.of R G (g * h) - 1 -
        ((_root_.MonoidAlgebra.of R G g - 1) +
         (_root_.MonoidAlgebra.of R G h - 1)) : MonoidAlgebra R G) ∈
      augmentationPower R G 2) := by
  convert mul_augmentation_ideal
    (R := R) (G := G)
    (sub_augmentation_ideal R G g)
    (sub_augmentation_ideal R G h) using 1
  rw [of_sub_eq]
  abel

theorem mk_sub_one (g h : G) :
    Ideal.Quotient.mk (augmentationPower R G 2)
        ((_root_.MonoidAlgebra.of R G (g * h) - 1 : MonoidAlgebra R G)) =
      Ideal.Quotient.mk (augmentationPower R G 2)
        ((_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G)) +
      Ideal.Quotient.mk (augmentationPower R G 2)
        ((_root_.MonoidAlgebra.of R G h - 1 : MonoidAlgebra R G)) := by
  rw [← sub_eq_zero]
  change Ideal.Quotient.mk (augmentationPower R G 2)
      ((_root_.MonoidAlgebra.of R G (g * h) - 1) -
        ((_root_.MonoidAlgebra.of R G g - 1) +
         (_root_.MonoidAlgebra.of R G h - 1))) = 0
  exact
    (mk_augmentation_power
      (R := R) (G := G) _).2
      (sub_sum_square (R := R) (G := G) g h)

theorem mk_sub_nsmul (m : ℕ) (g : G) :
    Ideal.Quotient.mk (augmentationPower R G 2)
        ((_root_.MonoidAlgebra.of R G (g ^ m) - 1 : MonoidAlgebra R G)) =
      m •
        (Ideal.Quotient.mk (augmentationPower R G 2)
          ((_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G))) := by
  induction m with
  | zero =>
      rw [pow_zero, map_one]
      simp
  | succ m ih =>
      rw [pow_succ, mk_sub_one, ih]
      exact (succ_nsmul _ _).symm

theorem sub_smul_square (m : ℕ) (g : G) :
    ((_root_.MonoidAlgebra.of R G (g ^ m) - 1 -
        m • (_root_.MonoidAlgebra.of R G g - 1) :
      MonoidAlgebra R G) ∈
      augmentationPower R G 2) := by
  rw [← mk_augmentation_power, map_sub,
    mk_sub_nsmul]
  simp

/-! Dimension subgroups. -/

theorem mem_dimension_iff {n : ℕ} {g : G} :
    g ∈ dSubgro R G n ↔
      (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
        augmentationPower R G n := by
  exact mem_dimensionSubgroup R G

theorem dimension_subgroup_conj {n : ℕ} {g : G}
    (hg : g ∈ dSubgro R G n) (h : G) :
    h * g * h⁻¹ ∈ dSubgro R G n := by
  exact (dimensionSubgroup_normal R G n).conj_mem g hg h

theorem dimension_map_le {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    Subgroup.map φ (dSubgro R G n) ≤
      dSubgro R H n := by
  rw [Subgroup.map_le_iff_le_comap]
  exact dimension_subgroup_comap R φ n

/-! The additive first-order map `g ↦ g - 1 mod I^2`. -/

def dimensionOneMap (R G : Type*) [CommRing R] [Group G] :
    G →* Multiplicative ((MonoidAlgebra R G) ⧸ augmentationPower R G 2) where
  toFun g :=
    Multiplicative.ofAdd
      (Ideal.Quotient.mk (augmentationPower R G 2)
        ((_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G)))
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    rw [map_one]
    simp
  map_mul' := by
    intro g h
    exact congrArg Multiplicative.ofAdd
      (mk_sub_one (R := R) (G := G) g h)

@[simp]
theorem dimension_map_apply (g : G) :
    dimensionOneMap R G g =
      Multiplicative.ofAdd
        (Ideal.Quotient.mk (augmentationPower R G 2)
          ((_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G))) := by
  rfl

theorem dimension_one (g : G) :
    dimensionOneMap R G g = 1 ↔
      (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
        augmentationPower R G 2 := by
  change Ideal.Quotient.mk (augmentationPower R G 2)
      ((_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G)) = 0 ↔ _
  exact mk_augmentation_power _

theorem one_ker :
    (dimensionOneMap R G).ker = dSubgro R G 2 := by
  ext g
  rw [MonoidHom.mem_ker, dimension_one, mem_dimension_iff]

/-! Specialization to `ZMod p`. -/

variable {p : ℕ}

theorem mk_pth_zmod (g : G) :
    Ideal.Quotient.mk (augmentationPower (ZMod p) G 2)
        ((_root_.MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 :
          MonoidAlgebra (ZMod p) G)) = 0 := by
  rw [mk_sub_nsmul]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod p)]
  simp

theorem pth_aug_zmod (g : G) :
    (_root_.MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 :
        MonoidAlgebra (ZMod p) G) ∈
      augmentationPower (ZMod p) G 2 := by
  exact
    (mk_augmentation_power _).1
      (mk_pth_zmod g)

theorem pth_subgroup_two (g : G) :
    g ^ p ∈ zSubgro p G 2 := by
  rw [mem_zassenhausSubgroup]
  exact pth_aug_zmod g

theorem element_dimension_two (g h : G) :
    ⁅g, h⁆ ∈ dSubgro R G 2 := by
  exact commutator_dimension_two R G g h

theorem commutator_dimension_subgroup :
    _root_.commutator G ≤ dSubgro R G 2 := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g _ h _
  exact element_dimension_two g h

theorem commutator_element_two (g h : G) :
    ⁅g, h⁆ ∈ zSubgro p G 2 := by
  exact commutator_subgroup_two p G g h

theorem commutator_zassenhaus_two :
    _root_.commutator G ≤ zSubgro p G 2 := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g _ h _
  exact commutator_element_two g h

theorem zassenhaus_map_le {H : Type*} [Group H]
    (φ : G →* H) (n : ℕ) :
    Subgroup.map φ (zSubgro p G n) ≤
      zSubgro p H n := by
  rw [Subgroup.map_le_iff_le_comap]
  exact GroupAlgebra.zassenhaus_subgroup_comap p G φ n

theorem zassenhaus_dimension_one (g : G) :
    g ∈ zSubgro p G 2 ↔
      dimensionOneMap (ZMod p) G g = 1 := by
  rw [mem_zassenhausSubgroup, dimension_one]

theorem dimension_ker_zmod :
    (dimensionOneMap (ZMod p) G).ker = zSubgro p G 2 := by
  ext g
  rw [MonoidHom.mem_ker, ← zassenhaus_dimension_one]

theorem p_commutator_aux :
    Subgroup.map (QuotientGroup.mk' (_root_.commutator G))
        (_root_.Submission.pPowerSubgroup p G) =
      _root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G) := by
  let q := QuotientGroup.mk' (_root_.commutator G)
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g, rfl⟩
    change q (g ^ p) ∈ _root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G)
    simpa using _root_.Submission.p_power_subgroup p (G ⧸ _root_.commutator G) (q g)
  · haveI :
        (Subgroup.map q (_root_.Submission.pPowerSubgroup p G)).Normal :=
      Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (_root_.commutator G) x with ⟨g, rfl⟩
    simpa using
      (Subgroup.mem_map_of_mem q (_root_.Submission.p_power_subgroup p G g))

theorem abelianization_preimage_aux :
    Subgroup.comap (QuotientGroup.mk' (_root_.commutator G))
        (_root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G)) =
      _root_.Submission.modPFrattini p G := by
  rw [← p_commutator_aux,
    QuotientGroup.comap_map_mk', sup_comm]
  rfl

theorem zassenhaus_frattini_aux :
    zSubgro p G 2 ≤ _root_.Submission.modPFrattini p G := by
  apply zassenhaus_subgroup_bot p G
  letI : IsMulCommutative (G ⧸ _root_.Submission.modPFrattini p G) :=
    ⟨⟨fun x y => _root_.Submission.mod_mul_comm p G x y⟩⟩
  apply le_antisymm
  · exact _root_.Submission.Theorems.bot_comm_exponent
      p (_root_.Submission.mod_frattini_one p G)
  · exact bot_le

theorem p_two_aux :
    _root_.Submission.pPowerSubgroup p G ≤ zSubgro p G 2 := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, rfl⟩
  exact pth_subgroup_two g

theorem mod_frattini_aux :
    _root_.Submission.modPFrattini p G ≤ zSubgro p G 2 := by
  exact sup_le p_two_aux
    commutator_zassenhaus_two

theorem p_frattini_aux :
    zSubgro p G 2 = _root_.Submission.modPFrattini p G :=
  le_antisymm zassenhaus_frattini_aux
    mod_frattini_aux

/-!
This is the key algebraic lemma packaging the standard identification

`I / I^2 ≃ (ZMod p) ⊗ G_ab`.

It says exactly that `g - 1 ∈ I^2` iff the image of `g` in the
abelianization is a `p`-th power.
-/
theorem aug_abelianization_p (g : G) :
    ((_root_.MonoidAlgebra.of (ZMod p) G g - 1 :
        MonoidAlgebra (ZMod p) G) ∈
      augmentationPower (ZMod p) G 2) ↔
      QuotientGroup.mk' (_root_.commutator G) g ∈
        _root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G) := by
  change g ∈ zSubgro p G 2 ↔ _
  rw [p_frattini_aux,
    ← abelianization_preimage_aux]
  rfl

theorem dimension_abelianization_p (g : G) :
    dimensionOneMap (ZMod p) G g = 1 ↔
      QuotientGroup.mk' (_root_.commutator G) g ∈
        _root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G) := by
  rw [dimension_one,
    aug_abelianization_p]

theorem abelianization_p_power (g : G) :
    g ∈ zSubgro p G 2 ↔
      QuotientGroup.mk' (_root_.commutator G) g ∈
        _root_.Submission.pPowerSubgroup p (G ⧸ _root_.commutator G) := by
  rw [mem_zassenhausSubgroup,
    aug_abelianization_p]

/-! Useful isolated consequence: elementary abelian quotients have trivial `D₂`. -/

theorem bot_forall_commute
    (hcomm : ∀ a b : G, a * b = b * a)
    (hpow : ∀ a : G, a ^ p = 1) :
    zSubgro p G 2 = ⊥ := by
  letI : IsMulCommutative G := ⟨⟨fun a b => hcomm a b⟩⟩
  exact le_antisymm
    (_root_.Submission.Theorems.bot_comm_exponent p hpow)
    bot_le

end

end GroupAlgebra

noncomputable section

open GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-! Group-theoretic lemmas about the mod-`p` Frattini subgroup. -/

instance instPSubgroup (p : ℕ) (G : Type*) [Group G] :
    Subgroup.Normal (pPowerSubgroup p G) := by
  exact p_subgroup_normal p G

instance instPFrattini (p : ℕ) (G : Type*) [Group G] :
    Subgroup.Normal (modPFrattini p G) := by
  exact mod_frattini_normal p G

theorem pth_p_subgroup (g : G) :
    g ^ p ∈ pPowerSubgroup p G := by
  exact p_power_subgroup p G g

theorem pth_p_frattini (g : G) :
    g ^ p ∈ modPFrattini p G := by
  exact pow_mod_frattini p G g

theorem p_mod_frattini :
    pPowerSubgroup p G ≤ modPFrattini p G := by
  exact le_sup_left

theorem commutator_p_frattini :
    _root_.commutator G ≤ modPFrattini p G := by
  exact le_sup_right

theorem commutator_element_frattini (g h : G) :
    ⁅g, h⁆ ∈ modPFrattini p G := by
  exact commutator_mod_frattini p G g h

theorem frattini_mul_comm
    (x y : G ⧸ modPFrattini p G) :
    x * y = y * x := by
  exact mod_mul_comm p G x y

theorem p_frattini_pow
    (x : G ⧸ modPFrattini p G) :
    x ^ p = 1 := by
  exact mod_frattini_one p G x

theorem mk_mod_frattini (g : G) :
    QuotientGroup.mk' (modPFrattini p G) g = 1 ↔
      g ∈ modPFrattini p G := by
  exact QuotientGroup.eq_one_iff (N := modPFrattini p G) g

/-! Relating `modPFrattini` to the abelianization. -/

theorem abelianization_preimage_frattini :
    Subgroup.comap (QuotientGroup.mk' (_root_.commutator G))
        (pPowerSubgroup p (G ⧸ _root_.commutator G)) =
      modPFrattini p G := by
  exact GroupAlgebra.abelianization_preimage_aux

theorem mod_frattini_abelianization (g : G) :
    g ∈ modPFrattini p G ↔
      QuotientGroup.mk' (_root_.commutator G) g ∈
        pPowerSubgroup p (G ⧸ _root_.commutator G) := by
  change g ∈ modPFrattini p G ↔
    g ∈ Subgroup.comap (QuotientGroup.mk' (_root_.commutator G))
      (pPowerSubgroup p (G ⧸ _root_.commutator G))
  rw [abelianization_preimage_frattini]

theorem p_bot_forall
    (hpow : ∀ g : G, g ^ p = 1) :
    pPowerSubgroup p G = ⊥ := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g, rfl⟩
    simp [hpow g]
  · exact bot_le

theorem commutator_forall_commute
    (hcomm : ∀ a b : G, a * b = b * a) :
    _root_.commutator G = ⊥ := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a b)
  · exact bot_le

theorem mod_forall_commute
    (hcomm : ∀ a b : G, a * b = b * a)
    (hpow : ∀ a : G, a ^ p = 1) :
    modPFrattini p G = ⊥ := by
  simp [modPFrattini, p_bot_forall hpow,
    commutator_forall_commute hcomm]

/-!
Alternative quotient-based route to the desired inclusion.

Let `Q = G / modPFrattini`. Then `Q` is abelian and every element has
`p`-th power equal to `1`, hence `D₂(Q) = ⊥`.
Functoriality of dimension subgroups then forces `D₂(G)` into the kernel
of `G → Q`, namely `modPFrattini`.
-/

theorem p_frattini_bot :
    GroupAlgebra.zSubgro p (G ⧸ modPFrattini p G) 2 = ⊥ := by
  exact
    GroupAlgebra.bot_forall_commute
      frattini_mul_comm p_frattini_pow

theorem comap_p_frattini (n : ℕ) :
    GroupAlgebra.zSubgro p G n ≤
      Subgroup.comap (QuotientGroup.mk' (modPFrattini p G))
        (GroupAlgebra.zSubgro p (G ⧸ modPFrattini p G) n) := by
  exact GroupAlgebra.zassenhaus_subgroup_comap p G
    (QuotientGroup.mk' (modPFrattini p G)) n

theorem two_mod_frattini :
    GroupAlgebra.zSubgro p G 2 ≤ modPFrattini p G := by
  exact GroupAlgebra.zassenhaus_frattini_aux

/-! The reverse inclusion, giving the stronger equality. -/

theorem p_subgroup_two :
    pPowerSubgroup p G ≤ GroupAlgebra.zSubgro p G 2 := by
  exact GroupAlgebra.p_two_aux

theorem commutator_zassenhaus_two :
    _root_.commutator G ≤ GroupAlgebra.zSubgro p G 2 := by
  exact GroupAlgebra.commutator_zassenhaus_two

theorem mod_frattini_two :
    modPFrattini p G ≤ GroupAlgebra.zSubgro p G 2 := by
  exact sup_le p_subgroup_two
    commutator_zassenhaus_two

theorem zassenhaus_mod_frattini :
    GroupAlgebra.zSubgro p G 2 = modPFrattini p G := by
  exact le_antisymm two_mod_frattini
    mod_frattini_two

theorem zassenhaus_p_frattini (g : G) :
    g ∈ GroupAlgebra.zSubgro p G 2 ↔
      g ∈ modPFrattini p G := by
  rw [zassenhaus_mod_frattini]

theorem dimension_zmod_frattini :
    (GroupAlgebra.dimensionOneMap (ZMod p) G).ker = modPFrattini p G := by
  rw [GroupAlgebra.dimension_ker_zmod,
    zassenhaus_mod_frattini]

end

end Submission
