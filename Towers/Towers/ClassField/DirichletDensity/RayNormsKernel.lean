import Towers.ClassField.DirichletDensity.SecondInequality

/-!
# Chapter VI, Section 4, Corollary 4.10
-/

namespace Towers.CField.DDensit

open Filter IsDedekindDomain NumberField
open Towers.CField.RCGroups
open Towers.CField.ARecip
open Towers.CField.PDensit

noncomputable section

universe u

/-- The condition `Nm_{L/K} C_{m,L} ⊆ ker(chi)`, expressed before passing
to the ray-class quotient: every prime-to-`m` ideal norm is killed by the
lift of `chi` to `I^{S(m)}`. -/
def RayNormsCharacter
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ) : Prop :=
  L.idealNormSubgroup m.finiteSupport ≤
    (chi.comp (QuotientGroup.mk' (rayPrincipalSubgroup K m))).ker

/-- A ray-class character which kills the norm subgroup descends to the
quotient by the ray-principal-times-norm subgroup. -/
def rayClassCharacter
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ)
    (hNorm : RayNormsCharacter L m chi) :
    CongruenceClassQuotient K m (extensionRaySubgroup L m) →* ℂˣ :=
  QuotientGroup.lift (extensionRaySubgroup L m)
    (chi.comp (QuotientGroup.mk' (rayPrincipalSubgroup K m))) (by
      rw [extensionRaySubgroup]
      refine sup_le ?_ hNorm
      intro I hI
      change chi (QuotientGroup.mk' (rayPrincipalSubgroup K m) I) = 1
      calc
        chi (QuotientGroup.mk' (rayPrincipalSubgroup K m) I) = chi 1 :=
          congrArg chi ((QuotientGroup.eq_one_iff
            (N := rayPrincipalSubgroup K m) I).2 hI)
        _ = 1 := map_one chi)

@[simp]
theorem ray_character_mk
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ)
    (hNorm : RayNormsCharacter L m chi)
    (I : IdealsPrimeTo (𝓞 K) K m.finiteSupport) :
    rayClassCharacter L m chi hNorm
        (QuotientGroup.mk' (extensionRaySubgroup L m) I) =
      chi (QuotientGroup.mk' (rayPrincipalSubgroup K m) I) :=
  QuotientGroup.lift_mk' _ _ _

/-- Descent through the ray norm subgroup does not turn a nontrivial
ray-class character into the trivial character. -/
theorem ray_character_ne
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ)
    (hNorm : RayNormsCharacter L m chi)
    (hchi : chi ≠ 1) :
    rayClassCharacter L m chi hNorm ≠ 1 := by
  intro hdesc
  apply hchi
  ext I
  have hvalue := DFunLike.congr_fun hdesc
    (QuotientGroup.mk' (extensionRaySubgroup L m) I)
  simpa using hvalue

/-- The descended quotient character has exactly the same coefficient on
each prime-to-modulus integral ideal. -/
theorem congruence_l_shell
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ)
    (hNorm : RayNormsCharacter L m chi)
    (s : ℂ) (n : ℕ) :
    congruenceLShell K
        (rayClassCharacter L m chi hNorm) s n =
      congruenceLShell K chi s n := by
  unfold congruenceLShell
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hprime
  · rw [ray_character_mk]
  · rfl

/-- Descending a ray-class character through the ray norm subgroup leaves
the ordered ideal `L`-series value at `1` unchanged. -/
theorem congruence_l_ray
    {K : Type u} [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ)
    (hNorm : RayNormsCharacter L m chi) :
    congruenceLValue K
        (rayClassCharacter L m chi hNorm) =
      congruenceLValue K chi := by
  unfold congruenceLValue congruenceLPartial
  apply congrArg (limUnder atTop)
  funext N
  apply Finset.sum_congr rfl
  intro n hn
  exact congruence_l_shell
    L m chi hNorm 1 n

/-- Corollary 4.10, obtained from the nonvanishing conclusion inside the
density proof of Theorem 4.9 by descending the ray-class character through
the ray norm subgroup. -/
theorem norms_inequality_density
    (hSplitDensity : PolarDensityBridge.{u})
    (h41a : PolarImpliesDirichlet.{u})
    (h48 : CongruenceDensityFormula.{u})
    (hSplitNorm : SplittingRayBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ),
    IsGalois K L.carrier → chi ≠ 1 →
      RayNormsCharacter L m chi →
      congruenceLValue K chi ≠ 0
  := by
  intro K _ _ L m chi hGalois hchi hNorm
  have hnonzero :=
    congruence_l_values
      hSplitDensity h41a h48 hSplitNorm K L m hGalois
      (rayClassCharacter L m chi hNorm)
      (ray_character_ne L m chi hNorm hchi)
  rw [congruence_l_ray] at hnonzero
  exact hnonzero

end

end Towers.CField.DDensit
