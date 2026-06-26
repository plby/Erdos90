import Submission.ClassField.HilbertSymbols.FiniteCharacterUnit
import Submission.ClassField.KummerNormIndex.KummerKernel
import Submission.ClassField.KummerTheory.KummerRadicalExtension

/-!
# The Kummer pairing in Lemma VII.6.9

For chosen `p`th roots of the `S`-units, an automorphism acts on each root
by a `p`th root of unity.  This gives the usual Kummer pairing between
`Gal(M/L)` and the `S`-unit quotient.  Generation of `M` by those roots makes
the pairing faithful on the Galois side.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.KTheory

noncomputable section

universe u

private abbrev AUnits
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) :=
  ArithmeticSUnits K (finitePrimePart K S)

/-- A chosen nonzero root, bundled as a unit of `M`. -/
noncomputable def rootUnit
    (p : ℕ) (hp : 0 < p)
    (K M : Type u) [Field K] [Field M] [NumberField K] [Algebra K M]
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (a : AUnits K S) : Mˣ :=
  Units.mk0 (root a) <| by
    intro ha
    have hzero : algebraMap K M (((a : Kˣ) : K)) = 0 := by
      rw [← hroot a, ha, zero_pow hp.ne']
    exact (map_ne_zero (algebraMap K M)).2 (Units.ne_zero (a : Kˣ)) hzero

@[simp]
theorem rootUnit_val
    (p : ℕ) (hp : 0 < p)
    (K M : Type u) [Field K] [Field M] [NumberField K] [Algebra K M]
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (a : AUnits K S) :
    (rootUnit p hp K M S root hroot a : M) = root a := rfl

theorem rootUnit_pow
    (p : ℕ) (hp : 0 < p)
    (K M : Type u) [Field K] [Field M] [NumberField K] [Algebra K M]
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (a : AUnits K S) :
    rootUnit p hp K M S root hroot a ^ p =
      Units.map (algebraMap K M).toMonoidHom (a : Kˣ) := by
  apply Units.ext
  exact hroot a

/-- Every `p`th root of unity in `M` comes from `K`, hence is fixed by
`Gal(M/L)`. -/
theorem root_unity_fixed
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (x : Mˣ) (hx : x ^ p = 1) (sigma : Gal(M/L)) :
    Units.map sigma.toMonoidHom x = x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hroots
  have hprimitive : IsPrimitiveRoot zeta p :=
    (mem_primitiveRoots hp.pos).mp hzeta
  have hxField : (x : M) ^ p = algebraMap K M ((1 : K) ^ p) := by
    simpa using congrArg Units.val hx
  obtain ⟨c, hc⟩ := algebra_pow
    p zeta hprimitive (x : M) 1 one_ne_zero hxField
  apply Units.ext
  change sigma (x : M) = (x : M)
  rw [← hc, IsScalarTower.algebraMap_apply K L M, sigma.commutes]

/-- The raw Kummer ratio `σ(root(a))/root(a)`. -/
noncomputable def kummerRatio
    (p : ℕ) (hp : 0 < p)
    (K M : Type u) [Field K] [Field M] [NumberField K] [Algebra K M]
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : M ≃ₐ[K] M) (a : AUnits K S) : Mˣ :=
  Units.map sigma.toMonoidHom
      (rootUnit p hp K M S root hroot a) *
    (rootUnit p hp K M S root hroot a)⁻¹

/-- Each raw Kummer ratio is a `p`th root of unity. -/
theorem kummerRatio_pow
    (p : ℕ) (hp : p.Prime)
    (K M : Type u) [Field K] [Field M] [NumberField K] [Algebra K M]
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : M ≃ₐ[K] M) (a : AUnits K S) :
    kummerRatio p hp.pos K M S root hroot sigma a ^ p = 1 := by
  apply Units.ext
  change (sigma (root a) * (root a)⁻¹) ^ p = 1
  rw [mul_pow, inv_pow, ← map_pow, hroot a, sigma.commutes]
  exact mul_inv_cancel₀
    ((map_ne_zero (algebraMap K M)).2 (Units.ne_zero (a : Kˣ)))

/-- The Kummer ratio is multiplicative in the `S`-unit. -/
theorem kummerRatio_mul
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : Gal(M/L)) (a b : AUnits K S) :
    kummerRatio p hp.pos K M S root hroot
        (sigma.restrictScalars K) (a * b) =
      kummerRatio p hp.pos K M S root hroot
          (sigma.restrictScalars K) a *
        kummerRatio p hp.pos K M S root hroot
          (sigma.restrictScalars K) b := by
  let ra := rootUnit p hp.pos K M S root hroot a
  let rb := rootUnit p hp.pos K M S root hroot b
  let rab := rootUnit p hp.pos K M S root hroot (a * b)
  let delta : Mˣ := rab * (ra * rb)⁻¹
  have hdeltaPow : delta ^ p = 1 := by
    dsimp [delta]
    rw [mul_pow, inv_pow, mul_pow,
      rootUnit_pow, rootUnit_pow,
      rootUnit_pow]
    apply Units.ext
    simp
  have hdeltaFixed : Units.map sigma.toMonoidHom delta = delta :=
    root_unity_fixed p hp K L M hroots delta hdeltaPow sigma
  have hrab : rab = delta * (ra * rb) := by
    dsimp [delta]
    group
  change Units.map sigma.toMonoidHom rab * rab⁻¹ =
    (Units.map sigma.toMonoidHom ra * ra⁻¹) *
      (Units.map sigma.toMonoidHom rb * rb⁻¹)
  rw [hrab, map_mul, hdeltaFixed, map_mul]
  simp only [mul_inv_rev]
  calc
    delta * (Units.map sigma.toMonoidHom ra *
          Units.map sigma.toMonoidHom rb) *
        (rb⁻¹ * ra⁻¹ * delta⁻¹) =
      (delta * delta⁻¹) *
        ((Units.map sigma.toMonoidHom ra * ra⁻¹) *
          (Units.map sigma.toMonoidHom rb * rb⁻¹)) := by
            ac_rfl
    _ = (Units.map sigma.toMonoidHom ra * ra⁻¹) *
          (Units.map sigma.toMonoidHom rb * rb⁻¹) := by simp

/-- The Kummer ratio at the identity `S`-unit is one. -/
theorem kummerRatio_one
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : Gal(M/L)) :
    kummerRatio p hp.pos K M S root hroot
        (sigma.restrictScalars K) 1 = 1 := by
  let r := rootUnit p hp.pos K M S root hroot 1
  have hrPow : r ^ p = 1 := by
    rw [rootUnit_pow]
    simp
  have hrFixed : Units.map sigma.toMonoidHom r = r :=
    root_unity_fixed p hp K L M hroots r hrPow sigma
  change Units.map sigma.toMonoidHom r * r⁻¹ = 1
  rw [hrFixed, mul_inv_cancel]

/-- For fixed `σ`, the Kummer ratios form a character of the `S`-unit
group. -/
noncomputable def kummerRatioHom
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : Gal(M/L)) : AUnits K S →* Mˣ where
  toFun := kummerRatio p hp.pos K M S root hroot
    (sigma.restrictScalars K)
  map_one' := kummerRatio_one p hp K L M hroots S root hroot sigma
  map_mul' := kummerRatio_mul p hp K L M hroots S root hroot sigma

/-- A Kummer character is trivial on an `S`-unit which becomes a `p`th
power in `L`. -/
theorem kummer_ratio_extension
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : Gal(M/L)) (a : AUnits K S)
    (ha : a ∈ extensionPowerSubgroup K L p S) :
    kummerRatioHom p hp K L M hroots S root hroot sigma a = 1 := by
  rw [extension_power_subgroup K L p hp.pos S a] at ha
  obtain ⟨y, hy⟩ := ha
  have hy0 : y ≠ 0 := by
    intro h
    have ha0 : algebraMap K L (((a : Kˣ) : K)) = 0 := by
      rw [← hy, h, zero_pow hp.ne_zero]
    exact (map_ne_zero (algebraMap K L)).2 (Units.ne_zero (a : Kˣ)) ha0
  let yu : Lˣ := Units.mk0 y hy0
  let yM : Mˣ := Units.map (algebraMap L M).toMonoidHom yu
  let r := rootUnit p hp.pos K M S root hroot a
  let delta : Mˣ := r * yM⁻¹
  have hyM : yM ^ p =
      Units.map (algebraMap K M).toMonoidHom (a : Kˣ) := by
    apply Units.ext
    change (algebraMap L M y) ^ p = algebraMap K M (((a : Kˣ) : K))
    rw [← map_pow, hy, IsScalarTower.algebraMap_apply K L M]
  have hdeltaPow : delta ^ p = 1 := by
    dsimp [delta]
    rw [mul_pow, inv_pow, rootUnit_pow, hyM]
    exact mul_inv_cancel _
  have hdeltaFixed : Units.map sigma.toMonoidHom delta = delta :=
    root_unity_fixed p hp K L M hroots delta hdeltaPow sigma
  have hyMFixed : Units.map sigma.toMonoidHom yM = yM := by
    apply Units.ext
    exact sigma.commutes y
  have hr : r = delta * yM := by simp [delta]
  change Units.map sigma.toMonoidHom r * r⁻¹ = 1
  rw [hr, map_mul, hdeltaFixed, hyMFixed]
  exact mul_inv_cancel _

/-- The Kummer character factored through the quotient by the units which
become powers in `L`. -/
noncomputable def kummerQuotientCharacter
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma : Gal(M/L)) :
    (AUnits K S ⧸ extensionPowerSubgroup K L p S) →* Mˣ :=
  QuotientGroup.lift (extensionPowerSubgroup K L p S)
    (kummerRatioHom p hp K L M hroots S root hroot sigma) <| by
      intro a ha
      rw [MonoidHom.mem_ker]
      exact kummer_ratio_extension
        p hp K L M hroots S root hroot sigma a ha

/-- Kummer characters multiply with the automorphism. -/
theorem kummer_ratio_sigma
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (sigma tau : Gal(M/L)) (a : AUnits K S) :
    kummerRatioHom p hp K L M hroots S root hroot (sigma * tau) a =
      kummerRatioHom p hp K L M hroots S root hroot sigma a *
        kummerRatioHom p hp K L M hroots S root hroot tau a := by
  let r := rootUnit p hp.pos K M S root hroot a
  let qtau := kummerRatioHom p hp K L M hroots S root hroot tau a
  have hqtauPow : qtau ^ p = 1 :=
    kummerRatio_pow p hp K M S root hroot (tau.restrictScalars K) a
  have hqtauFixed : Units.map sigma.toMonoidHom qtau = qtau :=
    root_unity_fixed p hp K L M hroots qtau hqtauPow sigma
  have htau : Units.map tau.toMonoidHom r = qtau * r := by
    change Units.map tau.toMonoidHom r =
      (Units.map tau.toMonoidHom r * r⁻¹) * r
    group
  calc
    Units.map (sigma * tau).toMonoidHom r * r⁻¹ =
        Units.map sigma.toMonoidHom
            (Units.map tau.toMonoidHom r) * r⁻¹ := rfl
    _ = Units.map sigma.toMonoidHom (qtau * r) * r⁻¹ := by rw [htau]
    _ = (qtau * Units.map sigma.toMonoidHom r) * r⁻¹ := by
      rw [map_mul, hqtauFixed]
    _ = (Units.map sigma.toMonoidHom r * r⁻¹) *
          (Units.map tau.toMonoidHom r * r⁻¹) := by
      rw [htau]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      ac_rfl

/-- The perfect-pairing map from `Gal(M/L)` to characters of the radical
quotient. -/
noncomputable def kummerPairing
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K))) :
    Gal(M/L) →*
      ((AUnits K S ⧸ extensionPowerSubgroup K L p S) →* Mˣ) where
  toFun := kummerQuotientCharacter p hp K L M hroots S root hroot
  map_one' := by
    ext a
    have hunit :
        kummerRatioHom p hp K L M hroots S root hroot 1 a = 1 := by
      change rootUnit p hp.pos K M S root hroot a *
          (rootUnit p hp.pos K M S root hroot a)⁻¹ = 1
      exact mul_inv_cancel _
    simpa [kummerQuotientCharacter] using congrArg Units.val hunit
  map_mul' sigma tau := by
    ext a
    simpa [kummerQuotientCharacter] using
      congrArg Units.val (kummer_ratio_sigma
        p hp K L M hroots S root hroot sigma tau a)

set_option maxHeartbeats 2000000 in
-- Faithfulness expands the chosen-root pairing on every `S`-unit and compares
-- the resulting fixed field with the generated Kummer extension.
/-- If the chosen roots generate `M`, the Kummer pairing is faithful on
`Gal(M/L)`. -/
theorem kummerPairing_injective
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (hgen : IntermediateField.adjoin K (Set.range root) = ⊤) :
    Function.Injective
      (kummerPairing p hp K L M hroots S root hroot) := by
  letI : FiniteDimensional K M := FiniteDimensional.trans K L M
  intro sigma tau hpair
  have hquotient :
      kummerPairing p hp K L M hroots S root hroot (sigma * tau⁻¹) = 1 := by
    rw [map_mul, map_inv, hpair]
    simp
  have hfix (a : AUnits K S) : sigma (tau⁻¹ (root a)) = root a := by
    have hvalue := DFunLike.congr_fun hquotient
      (QuotientGroup.mk' (extensionPowerSubgroup K L p S) a)
    change kummerRatioHom p hp K L M hroots S root hroot
      (sigma * tau⁻¹) a = 1 at hvalue
    change Units.map (sigma * tau⁻¹).toMonoidHom
        (rootUnit p hp.pos K M S root hroot a) *
          (rootUnit p hp.pos K M S root hroot a)⁻¹ = 1 at hvalue
    have hu := mul_inv_eq_one.mp hvalue
    exact congrArg Units.val hu
  have hgenAlg : Algebra.adjoin K (Set.range root) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
    · have h := congrArg IntermediateField.toSubalgebra hgen
      simpa using h
    · intro x _
      exact IsAlgebraic.of_finite K x
  have heq :
      ((sigma * tau⁻¹).restrictScalars K).toAlgHom =
        (1 : Gal(M/K)).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgenAlg
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact hfix a
  have hmul : sigma * tau⁻¹ = 1 := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun heq x
  exact (mul_inv_eq_one.mp hmul)

/-- The transpose of the Kummer pairing. -/
noncomputable def kummerPairingTranspose
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K))) :
    (AUnits K S ⧸ extensionPowerSubgroup K L p S) →*
      (Gal(M/L) →* Mˣ) :=
  MonoidHom.flip
    (kummerPairing p hp K L M hroots S root hroot)

/-- The transposed pairing is injective: if every automorphism fixes the
chosen root, Galois fixed-field theory puts that root in `L`. -/
theorem kummer_pairing_transpose
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional L M] [IsGalois L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K))) :
    Function.Injective
      (kummerPairingTranspose p hp K L M hroots S root hroot) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    change q = 1
    refine Quotient.inductionOn' q (fun a ha ↦ ?_) hq
    apply (QuotientGroup.eq_one_iff a).2
    rw [extension_power_subgroup K L p hp.pos S a]
    have hfixed (sigma : Gal(M/L)) : sigma (root a) = root a := by
      have hvalue := DFunLike.congr_fun ha sigma
      change kummerRatioHom p hp K L M hroots S root hroot sigma a = 1
        at hvalue
      change Units.map sigma.toMonoidHom
          (rootUnit p hp.pos K M S root hroot a) *
            (rootUnit p hp.pos K M S root hroot a)⁻¹ = 1 at hvalue
      exact congrArg Units.val (mul_inv_eq_one.mp hvalue)
    obtain ⟨y, hy⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := L) (E := M) (root a)).2 hfixed
    refine ⟨y, ?_⟩
    apply (algebraMap L M).injective
    calc
      algebraMap L M (y ^ p) = root a ^ p := by rw [map_pow, hy]
      _ = algebraMap K M (((a : Kˣ) : K)) := hroot a
      _ = algebraMap L M (algebraMap K L (((a : Kˣ) : K))) :=
        IsScalarTower.algebraMap_apply K L M _
  · exact bot_le

/-- A finite commutative group killed by `p` has as many `M`-valued
characters as elements when `M` contains a primitive `p`th root. -/
theorem character_card_eq
    (p : ℕ) (hp : p.Prime)
    (K M G : Type u) [Field K] [Field M] [Algebra K M]
    [CommGroup G] [Finite G]
    (hroots : (primitiveRoots p K).Nonempty)
    (hpow : ∀ g : G, g ^ p = 1) :
    Nat.card (G →* Mˣ) = Nat.card G := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hroots
  have hprimitiveK : IsPrimitiveRoot zeta p :=
    (mem_primitiveRoots hp.pos).mp hzeta
  have hprimitiveM : IsPrimitiveRoot (algebraMap K M zeta) p :=
    hprimitiveK.map_of_injective (algebraMap K M).injective
  letI : HasEnoughRootsOfUnity M p :=
    HasEnoughRootsOfUnity.of_card_le (by rw [hprimitiveM.card_rootsOfUnity])
  letI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M
      ((Monoid.exponent_dvd_iff_forall_pow_eq_one).2 hpow)
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M

set_option maxHeartbeats 4000000 in
-- The index calculation combines the faithful Kummer pairing with finite
-- character-group cardinalities and exponent bounds.
/-- The quotient by units which become powers in `L` has the same order as
`Gal(M/L)`.  This is the perfect Kummer-pairing cardinality used in Lemma
VII.6.9. -/
theorem extension_galois_card
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M]
    (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (root : AUnits K S → M)
    (hroot : ∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K)))
    (hgen : IntermediateField.adjoin K (Set.range root) = ⊤) :
    (extensionPowerSubgroup K L p S).index = Nat.card Gal(M/L) := by
  let Q := AUnits K S ⧸ extensionPowerSubgroup K L p S
  let pairing := kummerPairing p hp K L M hroots S root hroot
  let transpose := kummerPairingTranspose p hp K L M hroots S root hroot
  let zeta := hroots.choose
  have hzeta : IsPrimitiveRoot zeta p :=
    (mem_primitiveRoots hp.pos).mp hroots.choose_spec
  have hradicalPow : ∀ x ∈ Set.range root,
      x ^ p ∈ Set.range (algebraMap K M) := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨(((a : Kˣ) : K)), (hroot a).symm⟩
  letI : IsMulCommutative Gal(M/L) := by
    refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
    ext x
    simpa using DFunLike.congr_fun
      (aut_commute_nth hp.pos hzeta
        (Set.range root) hgen hradicalPow
        (sigma.restrictScalars K) (tau.restrictScalars K)) x
  letI : CommGroup Gal(M/L) :=
    { (inferInstance : Group Gal(M/L)) with
      mul_comm := mul_comm' }
  have hgalPow : ∀ sigma : Gal(M/L), sigma ^ p = 1 := by
    intro sigma
    have hres := aut_nth_roots hp.pos
      hzeta (Set.range root) hgen hradicalPow (sigma.restrictScalars K)
    have hrestrictPow (n : ℕ) : ∀ x : M,
        ((sigma.restrictScalars K) ^ n) x = (sigma ^ n) x := by
      induction n with
      | zero => intro x; rfl
      | succ n ih =>
          intro x
          rw [pow_succ, pow_succ]
          exact ih (sigma x)
    apply AlgEquiv.ext
    intro x
    calc
      (sigma ^ p) x = ((sigma.restrictScalars K) ^ p) x :=
        (hrestrictPow p x).symm
      _ = (1 : Gal(M/K)) x := DFunLike.congr_fun hres x
      _ = (1 : Gal(M/L)) x := rfl
  have hdualGal : Nat.card (Gal(M/L) →* Mˣ) = Nat.card Gal(M/L) :=
    character_card_eq p hp K M Gal(M/L) hroots hgalPow
  letI : Finite (Gal(M/L) →* Mˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hdualGal]; exact Nat.card_pos.ne')
  have htransposeInj : Function.Injective transpose :=
    kummer_pairing_transpose
      p hp K L M hroots S root hroot
  letI : Finite Q := Finite.of_injective transpose htransposeInj
  have hqPow : ∀ q : Q, q ^ p = 1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro a
    apply (QuotientGroup.eq_one_iff (a ^ p)).2
    change sUnitsHom K L S (a ^ p) ∈
      pthPowerSubgroup p Lˣ
    exact ⟨sUnitsHom K L S a, (map_pow _ a p).symm⟩
  have hdualQ : Nat.card (Q →* Mˣ) = Nat.card Q :=
    character_card_eq p hp K M Q hroots hqPow
  letI : Finite (Q →* Mˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hdualQ]; exact Nat.card_pos.ne')
  have hleQ : Nat.card Q ≤ Nat.card Gal(M/L) := by
    rw [← hdualGal]
    exact Nat.card_le_card_of_injective transpose htransposeInj
  have hpairingInj : Function.Injective pairing :=
    kummerPairing_injective p hp K L M hroots S root hroot hgen
  have hleGal : Nat.card Gal(M/L) ≤ Nat.card Q := by
    rw [← hdualQ]
    exact Nat.card_le_card_of_injective pairing hpairingInj
  exact le_antisymm hleQ hleGal

/-- The Kummer kernel-index input in Lemma VII.6.9. -/
theorem kummerIndexBridge :
    KummerIndexBridge.{u} := by
  intro p K L M _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hp hroots hexponent S hunramified hcontains hgenerate T hDisjoint hT
  obtain ⟨root, hroot, hgen⟩ := hgenerate
  rw [obvious_ker_extension
    p hp K L M hroots hexponent S hunramified hcontains T hDisjoint hT]
  rw [extension_galois_card
    p hp K L M hroots S root hroot hgen]
  exact galois_card_eq p K L M hexponent S T hT

/-- **Lemma VII.6.9.** -/
theorem kummerPairingStatement : (∀ (p : ℕ) (K L M : Type u)
      [Field K] [Field L] [Field M]
      [NumberField K] [NumberField L] [NumberField M]
      [Algebra K L] [Algebra L M] [Algebra K M]
      [IsScalarTower K L M]
      [FiniteDimensional K L] [FiniteDimensional L M]
      [IsGalois L M] [IsAbelianGalois K M],
      p.Prime → (primitiveRoots p K).Nonempty →
      ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
        (S : Finset (NumberFieldPlace K)),
        (∀ v : NumberFieldPlace K,
          normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
        (∀ Q : FinitePrime M,
          (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∉ S →
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal) →
        ContainsPthRoots K M p S →
        SPthRoots K M p S →
        ∀ (T : Finset (FinitePrime K))
          (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
            (Sum.inl P : NumberFieldPlace K) ∉ S),
          FrobeniusBasis
              (K := K) (L := L) (M := M) p hexponent S T →
            Function.Surjective (obviousMap K p S T hDisjoint)) :=
  pth_roots_bridges
    kummerIndexBridge localTargetBridge

end

end Submission.CField.KNIndex
