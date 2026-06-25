import Submission.Group.Zassenhaus
import Submission.Group.Frattini
import Mathlib.Algebra.TrivSqZeroExt.Basic

open scoped commutatorElement

namespace Submission
namespace Theorems

open GroupAlgebra

noncomputable section

universe u

lemma bot_comm_exponent
    (p : ℕ) {Q : Type u} [Group Q] [IsMulCommutative Q]
    (hpQ : ∀ q : Q, q ^ p = 1) :
    zSubgro p Q 2 ≤ ⊥ := by
  classical
  letI : AddCommGroup (Additive Q) :=
    { (inferInstance : AddGroup (Additive Q)) with
      add_comm := by
        intro x y
        change Additive.ofMul (Additive.toMul x * Additive.toMul y) =
          Additive.ofMul (Additive.toMul y * Additive.toMul x)
        rw [IsMulCommutative.is_comm.comm (Additive.toMul x) (Additive.toMul y)] }
  letI : Module (ZMod p) (Additive Q) := by
    apply AddCommGroup.zmodModule
    intro x
    change Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul (1 : Q)
    simp [hpQ (Additive.toMul x)]
  letI : Module (ZMod p)ᵐᵒᵖ (Additive Q) :=
    Module.compHom _ ((RingHom.id (ZMod p)).fromOpposite mul_comm)
  haveI : IsCentralScalar (ZMod p) (Additive Q) := ⟨fun _ _ => rfl⟩
  let S := TrivSqZeroExt (ZMod p) (Additive Q)
  let j : Q →* S :=
  { toFun := fun q => ⟨1, Additive.ofMul q⟩
    map_one' := by
      ext <;> simp
    map_mul' := by
      intro q r
      ext
      · simp [S]
      · simpa [S] using (IsMulCommutative.is_comm.comm q r) }
  let π : S →ₐ[ZMod p] ZMod p :=
    TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (Additive Q)
  let F : MonoidAlgebra (ZMod p) Q →ₐ[ZMod p] S :=
    _root_.MonoidAlgebra.lift (ZMod p) S Q j
  have hπF : π.comp F = augmentation (ZMod p) Q := by
    ext q
    simp [π, F, augmentation, trivialCharacter, j, S]
  let I := augmentationIdeal (ZMod p) Q
  have hfst_zero : ∀ a ∈ I, (F a).fst = 0 := by
    intro a ha
    have ha0 : (augmentation (ZMod p) Q) a = 0 := by
      simpa [I, augmentationIdeal] using ha
    have hπa : π (F a) = 0 := by
      change (π.comp F) a = 0
      rw [hπF]
      exact ha0
    simpa [π] using hπa
  have hmul_zero : ∀ z w : S, z.fst = 0 → w.fst = 0 → z * w = 0 := by
    intro z w hz hw
    ext
    · simp [S, hz, hw]
    · simp [S, hz, hw]
  have hker : I ^ 2 ≤ RingHom.ker F.toRingHom := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, Submodule.pow_succ, Submodule.pow_one]
    rw [Ideal.mul_le]
    intro a ha b hb
    change F (a * b) = 0
    rw [map_mul]
    exact hmul_zero (F a) (F b) (hfst_zero a ha) (hfst_zero b hb)
  intro q hq
  change (_root_.MonoidAlgebra.of (ZMod p) Q q - 1 :
      MonoidAlgebra (ZMod p) Q) ∈ augmentationPower (ZMod p) Q 2 at hq
  have hx : (_root_.MonoidAlgebra.of (ZMod p) Q q - 1 :
      MonoidAlgebra (ZMod p) Q) ∈ I ^ 2 := by
    simpa [I, augmentationPower] using hq
  have hFzero : F (_root_.MonoidAlgebra.of (ZMod p) Q q - 1) = 0 := by
    change F (_root_.MonoidAlgebra.of (ZMod p) Q q - 1) = 0
    exact hker hx
  have hsnd_zero :
      (F (_root_.MonoidAlgebra.of (ZMod p) Q q - 1)).snd = 0 := by
    rw [hFzero]
    simp
  have hsnd_calc :
      (F (_root_.MonoidAlgebra.of (ZMod p) Q q - 1)).snd = Additive.ofMul q := by
    simp [F, j, S]
  have hq0 : Additive.ofMul q = 0 := by
    rw [← hsnd_calc]
    exact hsnd_zero
  change q = 1
  simpa using congrArg Additive.toMul hq0

theorem zassenhaus_two_frattini
    (p : ℕ) (G : Type u) [Group G] [Fact p.Prime] :
    zSubgro p G 2 ≤ modPFrattini p G := by
  classical
  intro g hg
  let N : Subgroup G := modPFrattini p G
  haveI : N.Normal := by
    dsimp [N]
    infer_instance
  let Q := G ⧸ N
  have hcomm_le_N : _root_.commutator G ≤ N := by
    dsimp [N, modPFrattini]
    exact le_sup_right
  haveI : IsMulCommutative Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mpr hcomm_le_N
  let q : G →* Q := QuotientGroup.mk' N
  have hpQ : ∀ x : Q, x ^ p = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    have hp_mem : a ^ p ∈ pPowerSubgroup p G := by
      dsimp [pPowerSubgroup]
      exact Subgroup.subset_normalClosure ⟨a, rfl⟩
    have hmemN : a ^ p ∈ N := by
      dsimp [N, modPFrattini]
      exact
        (show pPowerSubgroup p G ≤ pPowerSubgroup p G ⊔ _root_.commutator G from
          le_sup_left) hp_mem
    have hmk : (QuotientGroup.mk' N) (a ^ p) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := N) (a ^ p)).mpr hmemN
    simpa using hmk
  have hgQ : q g ∈ zSubgro p Q 2 := by
    exact zassenhaus_subgroup_comap p G q 2 hg
  have hbot : zSubgro p Q 2 ≤ (⊥ : Subgroup Q) :=
    bot_comm_exponent (p := p) (Q := Q) hpQ
  have hq_bot : q g ∈ (⊥ : Subgroup Q) := hbot hgQ
  have hq_one : q g = 1 := by
    simpa only [Subgroup.mem_bot] using hq_bot
  have hq_one' : (QuotientGroup.mk' N) g = 1 := by
    simpa only [q] using hq_one
  change g ∈ N
  exact (QuotientGroup.eq_one_iff (N := N) g).mp hq_one'

/-- The mod-`p` Frattini subgroup is contained in the second
augmentation-defined Zassenhaus subgroup. -/
theorem mod_p_two
    (p : ℕ) (G : Type u) [Group G] :
    modPFrattini p G ≤ zSubgro p G 2 := by
  haveI : (zSubgro p G 2).Normal := by infer_instance
  dsimp [modPFrattini]
  refine sup_le ?_ ?_
  · dsimp [pPowerSubgroup]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨g, rfl⟩
    exact pow_subgroup_two p G g
  · rw [_root_.commutator_def]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with ⟨g, _hg, h, _hh, hx⟩
    rw [← hx]
    exact commutator_subgroup_two p G g h

/-- The second augmentation-defined Zassenhaus subgroup is the mod-`p`
Frattini subgroup `G^p [G,G]`. -/
theorem zassenhaus_mod_frattini
    (p : ℕ) (G : Type u) [Group G] [Fact p.Prime] :
    zSubgro p G 2 = modPFrattini p G :=
  le_antisymm
    (zassenhaus_two_frattini p G)
    (mod_p_two p G)

end

end Theorems
end Submission
