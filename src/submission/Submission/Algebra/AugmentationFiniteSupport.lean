import Submission.Algebra.Augmentation
import Mathlib.GroupTheory.Finiteness

/-!
# Finite-support lifting for augmentation powers

An element of a group algebra, and more specifically a witness in a power of the
augmentation ideal, already lives over a finitely generated subgroup.  The proofs below
keep that subgroup explicit so arbitrary-group dimension-subgroup arguments can reduce
individual witnesses to finitely generated groups.
-/

namespace Submission
namespace GroupAlgebra

noncomputable section

variable {R G : Type*} [CommRing R] [Group G]

/-- Every group-algebra element is induced from the group algebra of a finitely generated
subgroup. -/
theorem fg_subgroup_lift (a : MonoidAlgebra R G) :
    ∃ H : Subgroup G, H.FG ∧
      ∃ b : MonoidAlgebra R H,
        (MonoidAlgebra.mapDomainAlgHom R R H.subtype) b = a := by
  classical
  refine MonoidAlgebra.induction_on
    (p := fun a : MonoidAlgebra R G =>
      ∃ H : Subgroup G, H.FG ∧
        ∃ b : MonoidAlgebra R H,
          (MonoidAlgebra.mapDomainAlgHom R R H.subtype) b = a)
    a ?_ ?_ ?_
  · intro g
    let H : Subgroup G := Subgroup.closure ({g} : Set G)
    have hg : g ∈ H := Subgroup.subset_closure (by simp)
    refine ⟨H, ?_, _root_.MonoidAlgebra.of R H ⟨g, hg⟩, ?_⟩
    · exact ⟨{g}, by simp [H]⟩
    · simp [H]
  · rintro x y ⟨Hx, hHx, bx, hbx⟩ ⟨Hy, hHy, cy, hcy⟩
    let H : Subgroup G := Hx ⊔ Hy
    let ix : Hx →* H := Subgroup.inclusion le_sup_left
    let iy : Hy →* H := Subgroup.inclusion le_sup_right
    have hix : H.subtype.comp ix = Hx.subtype := by
      ext z
      rfl
    have hiy : H.subtype.comp iy = Hy.subtype := by
      ext z
      rfl
    refine ⟨H, hHx.sup hHy,
      (MonoidAlgebra.mapDomainAlgHom R R ix) bx +
        (MonoidAlgebra.mapDomainAlgHom R R iy) cy, ?_⟩
    rw [map_add, ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hix, hbx,
      ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hiy, hcy]
  · rintro r x ⟨H, hH, b, hb⟩
    refine ⟨H, hH, r • b, ?_⟩
    simp [hb]

/-- Augmentation-ideal membership can be retained in a finitely generated subgroup lift. -/
theorem fg_lift_ideal
    {a : MonoidAlgebra R G}
    (ha : a ∈ augmentationIdeal R G) :
    ∃ H : Subgroup G, H.FG ∧
      ∃ b : MonoidAlgebra R H,
        b ∈ augmentationIdeal R H ∧
          (MonoidAlgebra.mapDomainAlgHom R R H.subtype) b = a := by
  rcases fg_subgroup_lift (R := R) a with ⟨H, hH, b, hb⟩
  refine ⟨H, hH, b, ?_, hb⟩
  rw [mem_augmentationIdeal,
    ← augmentation_domain (R := R) (G := H) H.subtype b, hb]
  exact (mem_augmentationIdeal (R := R) (G := G)).mp ha

/-- Membership in an augmentation power can be retained in a finitely generated subgroup
lift. -/
theorem fg_lift_power
    {n : ℕ} {a : MonoidAlgebra R G}
    (ha : a ∈ augmentationPower R G n) :
    ∃ H : Subgroup G, H.FG ∧
      ∃ b : MonoidAlgebra R H,
        b ∈ augmentationPower R H n ∧
          (MonoidAlgebra.mapDomainAlgHom R R H.subtype) b = a := by
  induction n generalizing a with
  | zero =>
      rcases fg_subgroup_lift (R := R) a with ⟨H, hH, b, hb⟩
      exact ⟨H, hH, b, by simp, hb⟩
  | succ n ih =>
      change a ∈ augmentationIdeal R G ^ n.succ at ha
      rw [show augmentationIdeal R G ^ n.succ =
          augmentationIdeal R G * augmentationIdeal R G ^ n by
        simpa only [Nat.succ_eq_add_one] using
          (Ideal.IsTwoSided.pow_succ (I := augmentationIdeal R G) n)] at ha
      refine Submodule.smul_induction_on ha ?_ ?_
      · intro m hm x hx
        rcases fg_lift_ideal (R := R) hm with
          ⟨Hm, hHm, bm, hbmm, hbm⟩
        rcases ih hx with ⟨Hx, hHx, bx, hbxi, hbx⟩
        let H : Subgroup G := Hm ⊔ Hx
        let im : Hm →* H := Subgroup.inclusion le_sup_left
        let ix : Hx →* H := Subgroup.inclusion le_sup_right
        have him : H.subtype.comp im = Hm.subtype := by
          ext z
          rfl
        have hix : H.subtype.comp ix = Hx.subtype := by
          ext z
          rfl
        have hbm_mem :
            (MonoidAlgebra.mapDomainAlgHom R R im) bm ∈ augmentationIdeal R H := by
          exact
            (augmentation_ideal_domain (R := R) (G := Hm) im)
              (Ideal.mem_map_of_mem _ hbmm)
        have hbx_mem :
            (MonoidAlgebra.mapDomainAlgHom R R ix) bx ∈ augmentationPower R H n := by
          exact
            (augmentation_power_domain (R := R) (G := Hx) ix n)
              (Ideal.mem_map_of_mem _ hbxi)
        refine ⟨H, hHm.sup hHx,
          (MonoidAlgebra.mapDomainAlgHom R R im) bm *
            (MonoidAlgebra.mapDomainAlgHom R R ix) bx, ?_, ?_⟩
        · change
            (MonoidAlgebra.mapDomainAlgHom R R im) bm *
                (MonoidAlgebra.mapDomainAlgHom R R ix) bx ∈
              augmentationIdeal R H ^ n.succ
          rw [show augmentationIdeal R H ^ n.succ =
              augmentationIdeal R H * augmentationIdeal R H ^ n by
            simpa only [Nat.succ_eq_add_one] using
              (Ideal.IsTwoSided.pow_succ (I := augmentationIdeal R H) n)]
          exact Ideal.mul_mem_mul hbm_mem hbx_mem
        · rw [map_mul, ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, him, hbm,
            ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hix, hbx]
          simp
      · rintro x y ⟨Hx, hHx, bx, hbxi, hbx⟩ ⟨Hy, hHy, cy, hcyi, hcy⟩
        let H : Subgroup G := Hx ⊔ Hy
        let ix : Hx →* H := Subgroup.inclusion le_sup_left
        let iy : Hy →* H := Subgroup.inclusion le_sup_right
        have hix : H.subtype.comp ix = Hx.subtype := by
          ext z
          rfl
        have hiy : H.subtype.comp iy = Hy.subtype := by
          ext z
          rfl
        have hbx_mem :
            (MonoidAlgebra.mapDomainAlgHom R R ix) bx ∈ augmentationPower R H n.succ := by
          exact
            (augmentation_power_domain (R := R) (G := Hx) ix n.succ)
              (Ideal.mem_map_of_mem _ hbxi)
        have hcy_mem :
            (MonoidAlgebra.mapDomainAlgHom R R iy) cy ∈ augmentationPower R H n.succ := by
          exact
            (augmentation_power_domain (R := R) (G := Hy) iy n.succ)
              (Ideal.mem_map_of_mem _ hcyi)
        refine ⟨H, hHx.sup hHy,
          (MonoidAlgebra.mapDomainAlgHom R R ix) bx +
            (MonoidAlgebra.mapDomainAlgHom R R iy) cy,
          (augmentationPower R H n.succ).add_mem hbx_mem hcy_mem, ?_⟩
        rw [map_add, ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hix, hbx,
          ← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hiy, hcy]

/-- If `g - 1` lies in an augmentation power, the witness already lives over a finitely
generated subgroup containing `g`. -/
theorem fg_sub_power
    {n : ℕ} (g : G)
    (hg : (_root_.MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
      augmentationPower R G n) :
    ∃ H : Subgroup G, H.FG ∧
      ∃ gH : H,
        (gH : G) = g ∧
          (_root_.MonoidAlgebra.of R H gH - 1 : MonoidAlgebra R H) ∈
            augmentationPower R H n := by
  rcases fg_lift_power (R := R) hg with
    ⟨H₀, hH₀, b, hbmem, hb⟩
  let Hg : Subgroup G := Subgroup.closure ({g} : Set G)
  let H : Subgroup G := H₀ ⊔ Hg
  let i : H₀ →* H := Subgroup.inclusion le_sup_left
  have hH : H.FG := by
    exact hH₀.sup ⟨{g}, by simp [Hg]⟩
  have hgH : g ∈ H := by
    change g ∈ H₀ ⊔ Hg
    exact (le_sup_right : Hg ≤ H₀ ⊔ Hg) (Subgroup.subset_closure (by simp))
  let gH : H := ⟨g, hgH⟩
  have hi : H.subtype.comp i = H₀.subtype := by
    ext z
    rfl
  have hbmem' :
      (MonoidAlgebra.mapDomainAlgHom R R i) b ∈ augmentationPower R H n := by
    exact
      (augmentation_power_domain (R := R) (G := H₀) i n)
        (Ideal.mem_map_of_mem _ hbmem)
  have hb' :
      (MonoidAlgebra.mapDomainAlgHom R R H.subtype)
          ((MonoidAlgebra.mapDomainAlgHom R R i) b) =
        _root_.MonoidAlgebra.of R G g - 1 := by
    rw [← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp, hi, hb]
  have hof :
      (MonoidAlgebra.mapDomainAlgHom R R H.subtype)
          (_root_.MonoidAlgebra.of R H gH - 1) =
        _root_.MonoidAlgebra.of R G g - 1 := by
    rw [map_sub, map_one]
    simp [MonoidAlgebra.mapDomainAlgHom, _root_.MonoidAlgebra.of, gH]
  have heq :
      (MonoidAlgebra.mapDomainAlgHom R R i) b =
        _root_.MonoidAlgebra.of R H gH - 1 := by
    apply MonoidAlgebra.mapDomain_injective (R := R) H.subtype_injective
    change
      (MonoidAlgebra.mapDomainAlgHom R R H.subtype)
          ((MonoidAlgebra.mapDomainAlgHom R R i) b) =
        (MonoidAlgebra.mapDomainAlgHom R R H.subtype)
          (_root_.MonoidAlgebra.of R H gH - 1)
    rw [hb', hof]
  exact ⟨H, hH, gH, rfl, heq ▸ hbmem'⟩

end

end GroupAlgebra
end Submission
