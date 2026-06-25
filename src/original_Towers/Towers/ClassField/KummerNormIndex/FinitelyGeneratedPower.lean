import Towers.ClassField.KummerNormIndex.PowerIndex
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Power-subgroup indices in finitely generated abelian groups

This file extends the finite-group kernel/image calculation in `PowerIndex`
to an arbitrary finitely generated commutative group.  The free part contributes
one factor of `n` for each generator, while the finite part contributes the
cardinality of the kernel of the `n`th-power map.
-/

namespace Towers.CField.KNIndex

noncomputable section

private theorem multiplicative_int_index (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  rw [← Subgroup.index_toAddSubgroup]
  change (nsmulAddMonoidHom n : ℤ →+ ℤ).range.index = n
  rw [Int.range_nsmulAddMonoidHom, Int.index_zmultiples]
  simp

private theorem powerRange_prod (A B : Type*) [CommGroup A] [CommGroup B] (n : ℕ) :
    (powMonoidHom n : A × B →* A × B).range =
      (powMonoidHom n : A →* A).range.prod
        (powMonoidHom n : B →* B).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    ext <;> assumption

private theorem powerRange_pi (j : Type*) (n : ℕ) :
    (powMonoidHom n : (j → Multiplicative ℤ) →* (j → Multiplicative ℤ)).range =
      Subgroup.pi Set.univ (fun _ ↦
        (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i _
    exact ⟨y i, rfl⟩
  · intro hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    refine ⟨y, ?_⟩
    funext i
    exact hy i

private theorem free_pi_index (j : Type*) [Fintype j] (n : ℕ) :
    (powMonoidHom n : (j → Multiplicative ℤ) →* (j → Multiplicative ℤ)).range.index =
      n ^ Fintype.card j := by
  rw [powerRange_pi, Subgroup.index_pi]
  simp [multiplicative_int_index]

private theorem pow_free_pi {j : Type*} {n : ℕ} (hn : n ≠ 0)
    (x : j → Multiplicative ℤ) (hx : x ^ n = 1) : x = 1 := by
  funext a
  have ha := congrFun hx a
  change Multiplicative.ofAdd (n * (x a).toAdd) = 1 at ha
  apply Multiplicative.ofAdd.injective at ha
  change n * (x a).toAdd = 0 at ha
  exact mul_eq_zero.mp ha |>.resolve_left (by exact_mod_cast hn)

/-- Let `G` be a finitely generated commutative group and let `n` be nonzero.
The index of the subgroup of `n`th powers is `n` to the torsion-free rank of
`G`, multiplied by the number of elements killed by the `n`th-power map. -/
theorem fg_index_formula
    (G : Type*) [CommGroup G] [Group.FG G]
    (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ Module.finrank ℤ (Additive G) *
        Nat.card (powMonoidHom n : G →* G).ker := by
  classical
  letI : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨ι, j, fι, fj, q, hq, d, ⟨e⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  letI : Fintype ι := fι
  letI : Fintype j := fj
  let F := (i : ι) → Multiplicative (ZMod (q i ^ d i))
  let A := j → Multiplicative ℤ
  letI (i : ι) : NeZero (q i ^ d i) :=
    ⟨pow_ne_zero _ (hq i).ne_zero⟩
  have htransport := MulEquiv.map_range_powMonoidHom e n
  have hindexTransport :
      (powMonoidHom n : (A × F) →* (A × F)).range.index =
        (powMonoidHom n : G →* G).range.index := by
    rw [← htransport, Subgroup.index_map_equiv]
  have hFfinite : Finite F := by
    dsimp [F]
    infer_instance
  letI : Finite F := hFfinite
  have hkernel : Nat.card (powMonoidHom n : F →* F).ker =
      Nat.card (powMonoidHom n : G →* G).ker := by
    let ek : (powMonoidHom n : G →* G).ker ≃
        (powMonoidHom n : F →* F).ker :=
      { toFun := fun x => ⟨(e x.1).2, by
            have hx := congrArg e x.2
            change (e x.1).2 ^ n = 1
            simpa using congrArg Prod.snd hx⟩
        invFun := fun y => ⟨e.symm (1, y.1), by
            apply e.injective
            change e ((e.symm (1, y.1)) ^ n) = e 1
            rw [map_pow, e.apply_symm_apply, map_one]
            apply Prod.ext
            · simp
            · exact y.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          change e.symm (1, (e x.1).2) = x.1
          apply e.injective
          rw [e.apply_symm_apply]
          apply Prod.ext
          · symm
            apply pow_free_pi hn (e x.1).1
            have hx := congrArg e x.2
            change e (x.1 ^ n) = e 1 at hx
            rw [map_pow, map_one] at hx
            exact congrArg Prod.fst hx
          · rfl
        right_inv := fun y => by
          apply Subtype.ext
          change (e (e.symm (1, y.1))).2 = y.1
          rw [e.apply_symm_apply] }
    exact Nat.card_congr ek.symm
  have hfinrank : Module.finrank ℤ (Additive G) = Fintype.card j := by
    have heRank := LinearEquiv.finrank_eq
      (AddEquiv.toIntLinearEquiv e.toAdditive)
    rw [heRank]
    change Module.finrank ℤ ((Additive A) × (Additive F)) = Fintype.card j
    have hAfinrank : Module.finrank ℤ (Additive A) = Fintype.card j := by
      let ea : Additive A ≃ₗ[ℤ] (j → ℤ) :=
        AddEquiv.toIntLinearEquiv <|
          (AddEquiv.piAdditive (fun _ : j => Multiplicative ℤ)).trans <|
            AddEquiv.arrowCongr (Equiv.refl j) (AddEquiv.additiveMultiplicative ℤ)
      rw [ea.finrank_eq, Module.finrank_pi]
    have hFfinrank : Module.finrank ℤ (Additive F) = 0 := by
      apply Module.finrank_eq_zero_iff.mpr
      intro x
      refine ⟨(Nat.card F : ℤ), ?_, ?_⟩
      · exact_mod_cast (Nat.card_pos.ne' : Nat.card F ≠ 0)
      · simpa only [Nat.cast_smul_eq_nsmul] using
          (card_nsmul_eq_zero' (G := Additive F) (x := x))
    let snd : Additive A × Additive F →ₗ[ℤ] Additive F :=
      LinearMap.snd ℤ (Additive A) (Additive F)
    have hrank := (LinearMap.ker snd).finrank_quotient_add_finrank
    rw [(snd.quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq,
      LinearMap.ker_snd,
      ← (LinearEquiv.ofInjective (LinearMap.inl ℤ (Additive A) (Additive F))
        LinearMap.inl_injective).finrank_eq,
      hAfinrank, hFfinrank, zero_add] at hrank
    exact hrank.symm
  rw [← hindexTransport]
  rw [powerRange_prod, Subgroup.index_prod, free_pi_index]
  rw [subgroup_index_card]
  rw [hkernel, hfinrank]

end

end Towers.CField.KNIndex
