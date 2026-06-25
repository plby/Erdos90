import Towers.ClassField.KummerTheory.KummerPairing
import Mathlib.GroupTheory.Abelianization.Finite

/-!
# The radical-class side of the Kummer pairing

This file constructs the complementary Kummer pairing for an arbitrary
finite Galois extension `L/K`.  A base-field power class which acquires an
`n`th root in `L` determines a character of `Gal(L/K)` by

`b ↦ (σ ↦ σ(√b) / √b)`.

The pairing is injective in the radical-class variable: if every
automorphism fixes the chosen radical, Galois fixed-field theory puts that
radical back in `K`, so the original power class is trivial.  Finite
abelian duality therefore gives the substantial inequality

`|Kˣ ∩ Lˣⁿ / Kˣⁿ| ≤ [L : K]`.
-/

namespace Towers.CField.KTheory

noncomputable section

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

section AbstractRatio

variable {L : Type u} [Field L] [Algebra K L]

/-- Automorphism ratio attached to a unit. -/
def automorphismRatio (σ : Gal(L/K)) (x : Lˣ) : Lˣ :=
  Units.map σ x * x⁻¹

/-- A ratio has `n`th power one when the `n`th power of the unit is in the
base field. -/
theorem automorphism_ratio_pow
    (n : ℕ) (a : Kˣ) (x : Lˣ)
    (hx : x ^ n = Units.map (algebraMap K L) a)
    (σ : Gal(L/K)) :
    automorphismRatio K σ x ^ n = 1 := by
  rw [automorphismRatio, mul_pow, ← map_pow, hx, inv_pow, hx]
  have hfix : Units.map σ (Units.map (algebraMap K L).toMonoidHom a) =
      Units.map (algebraMap K L).toMonoidHom a := by
    apply Units.ext
    exact σ.commutes (a : K)
  calc
    _ = Units.map (algebraMap K L).toMonoidHom a *
        (Units.map (algebraMap K L).toMonoidHom a)⁻¹ :=
      congrArg (fun z ↦ z * (Units.map (algebraMap K L).toMonoidHom a)⁻¹) hfix
    _ = 1 := mul_inv_cancel _

/-- For a radical unit, the automorphism ratio is multiplicative in the
automorphism variable.  The crossed-homomorphism defect disappears because
the intermediate ratio is an `n`th root of unity and hence comes from the
base field. -/
theorem automorphism_ratio_aut
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (a : Kˣ) (x : Lˣ)
    (hx : x ^ n = Units.map (algebraMap K L) a)
    (σ τ : Gal(L/K)) :
    automorphismRatio K (σ * τ) x =
      automorphismRatio K σ x * automorphismRatio K τ x := by
  let qσ := automorphismRatio K σ x
  let qτ := automorphismRatio K τ x
  have hτpow : qτ ^ n = 1 :=
    automorphism_ratio_pow K n a x hx τ
  have hτfix : Units.map σ qτ = qτ :=
    alg_fix_unit K n hn hζ σ qτ hτpow
  have hτdef : Units.map τ x = qτ * x := by
    dsimp [qτ]
    rw [automorphismRatio]
    group
  have hσdef : Units.map σ x = qσ * x := by
    dsimp [qσ]
    rw [automorphismRatio]
    group
  have hcomp : Units.map (σ * τ) x =
      Units.map (σ : L →* L) (Units.map (τ : L →* L) x) := by
    apply Units.ext
    exact AlgEquiv.mul_apply σ τ (x : L)
  change Units.map (σ * τ) x * x⁻¹ = qσ * qτ
  rw [hcomp, hτdef, map_mul, hτfix, hσdef]
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using (mul_comm qτ qσ)

/-- Multiplicativity of automorphism ratios for any section of power
classes by radicals.  This isolates the choice-defect argument from the
specific construction of `radicalPowerClasses`. -/
theorem automorphism_ratio_section
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (B : Subgroup (PowerClassGroup K n))
    (a : B → Kˣ) (r : B → Lˣ)
    (ha : ∀ b, powerClass n (a b) = b.1)
    (hr : ∀ b, r b ^ n = Units.map (algebraMap K L) (a b))
    (σ : Gal(L/K)) (b c : B) :
    automorphismRatio K σ (r (b * c)) =
      automorphismRatio K σ (r b) * automorphismRatio K σ (r c) := by
  have hclasses : powerClass n (a (b * c)) = powerClass n (a b * a c) := by
    rw [map_mul, ha, ha, ha]
    rfl
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclasses
  obtain ⟨d, rfl⟩ := hz
  have heq' : a (b * c) * d ^ n = a b * a c := by
    simpa only [powMonoidHom_apply] using heq
  let dL : Lˣ := Units.map (algebraMap K L) d
  let q : Lˣ := r (b * c) * dL * (r b * r c)⁻¹
  have hqpow : q ^ n = 1 := by
    change (r (b * c) * Units.map (algebraMap K L) d *
      (r b * r c)⁻¹) ^ n = 1
    rw [mul_pow, mul_pow, inv_pow, mul_pow, hr, hr, hr]
    rw [← map_pow]
    rw [← map_mul, heq', map_mul]
    group
  have hqfix : Units.map σ q = q :=
    alg_fix_unit K n hn hζ σ q hqpow
  have hdfix : Units.map σ dL = dL := by
    apply Units.ext
    exact σ.commutes (d : K)
  have hqdef : q = r (b * c) * dL * (r b * r c)⁻¹ := rfl
  have hrbc : r (b * c) = q * r b * r c * dL⁻¹ := by
    rw [hqdef]
    group
  have hsrbc := congrArg (Units.map (σ : L →* L)) hrbc
  simp only [map_mul, map_inv, hqfix, hdfix] at hsrbc
  have hrbc_inv : (r (b * c))⁻¹ = dL * (r c)⁻¹ * (r b)⁻¹ * q⁻¹ := by
    rw [hrbc]
    group
  rw [automorphismRatio, hsrbc, hrbc_inv, automorphismRatio,
    automorphismRatio]
  calc
    _ = (q * q⁻¹) * (dL⁻¹ * dL) *
        (Units.map σ (r b) * (r b)⁻¹) *
        (Units.map σ (r c) * (r c)⁻¹) := by ac_rfl
    _ = _ := by simp

end AbstractRatio

section RadicalClasses

variable (n : ℕ) (L : IntermediateField K Ω)

/-- A base-field unit representing a radical power class of `L`. -/
def radicalClassRepresentative
    (b : radicalPowerClasses K Ω n L) : Kˣ :=
  Classical.choose ((Subgroup.mem_map).mp b.prop)

omit [IsAlgClosure K Ω] in
private theorem radical_class_representative
    (b : radicalPowerClasses K Ω n L) :
    radicalClassRepresentative K Ω n L b ∈ radicalUnits K Ω n L :=
  (Classical.choose_spec ((Subgroup.mem_map).mp b.prop)).1

omit [IsAlgClosure K Ω] in
@[simp]
theorem power_radical_representative
    (b : radicalPowerClasses K Ω n L) :
    powerClass n (radicalClassRepresentative K Ω n L b) = b.1 :=
  (Classical.choose_spec ((Subgroup.mem_map).mp b.prop)).2

/-- A chosen `n`th root in `L` of the chosen representative of a radical
power class. -/
def radicalClassRoot
    (b : radicalPowerClasses K Ω n L) : Lˣ :=
  Classical.choose (radical_class_representative K Ω n L b)

omit [IsAlgClosure K Ω] in
@[simp]
theorem radical_root_pow
    (b : radicalPowerClasses K Ω n L) :
    radicalClassRoot K Ω n L b ^ n =
      Units.map (algebraMap K L) (radicalClassRepresentative K Ω n L b) :=
  Classical.choose_spec (radical_class_representative K Ω n L b)

/-- The raw radical-class ratio. -/
def radicalClassRatio
    (σ : Gal(L/K)) (b : radicalPowerClasses K Ω n L) : Lˣ :=
  automorphismRatio K σ (radicalClassRoot K Ω n L b)

omit [IsAlgClosure K Ω] in
theorem radical_class_ratio
    (σ : Gal(L/K)) (b : radicalPowerClasses K Ω n L) :
    radicalClassRatio K Ω n L σ b ^ n = 1 :=
  automorphism_ratio_pow K n
    (radicalClassRepresentative K Ω n L b)
    (radicalClassRoot K Ω n L b)
    (radical_root_pow K Ω n L b) σ

omit [IsAlgClosure K Ω] in
theorem class_ratio_mul
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (σ : Gal(L/K)) (b c : radicalPowerClasses K Ω n L) :
    radicalClassRatio K Ω n L σ (b * c) =
      radicalClassRatio K Ω n L σ b * radicalClassRatio K Ω n L σ c :=
  automorphism_ratio_section K n hn hζ
    (radicalPowerClasses K Ω n L)
    (radicalClassRepresentative K Ω n L)
    (radicalClassRoot K Ω n L)
    (power_radical_representative K Ω n L)
    (radical_root_pow K Ω n L) σ b c

omit [IsAlgClosure K Ω] in
theorem class_ratio_one
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (σ : Gal(L/K)) :
    radicalClassRatio K Ω n L σ 1 = 1 := by
  have hmul := class_ratio_mul K Ω n L hn hζ σ 1 1
  apply mul_left_cancel (a := radicalClassRatio K Ω n L σ 1)
  simpa using hmul.symm

/-- A radical power class gives a character of the Galois group. -/
def radicalGaloisCharacter
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (b : radicalPowerClasses K Ω n L) : Gal(L/K) →* Kˣ := by
  letI : NeZero n := ⟨hn.ne'⟩
  let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
  exact
    { toFun := fun σ ↦ (e.symm
        ⟨radicalClassRatio K Ω n L σ b,
          (mem_rootsOfUnity n _).2 (radical_class_ratio K Ω n L σ b)⟩ :
          rootsOfUnity n K)
      map_one' := by
        let η : rootsOfUnity n L :=
          ⟨radicalClassRatio K Ω n L 1 b,
            (mem_rootsOfUnity n _).2
              (radical_class_ratio K Ω n L 1 b)⟩
        have hη : η = 1 := by
          apply Subtype.ext
          change Units.map (1 : Gal(L/K)) (radicalClassRoot K Ω n L b) *
            (radicalClassRoot K Ω n L b)⁻¹ = 1
          have hone : Units.map (1 : Gal(L/K)) (radicalClassRoot K Ω n L b) =
              radicalClassRoot K Ω n L b := by
            apply Units.ext
            rfl
          rw [hone, mul_inv_cancel]
        simpa [η] using congrArg
          (fun z : rootsOfUnity n L ↦ ((e.symm z : rootsOfUnity n K) : Kˣ)) hη
      map_mul' := by
        intro σ τ
        let ηστ : rootsOfUnity n L :=
          ⟨radicalClassRatio K Ω n L (σ * τ) b,
            (mem_rootsOfUnity n _).2
              (radical_class_ratio K Ω n L (σ * τ) b)⟩
        let ησ : rootsOfUnity n L :=
          ⟨radicalClassRatio K Ω n L σ b,
            (mem_rootsOfUnity n _).2
              (radical_class_ratio K Ω n L σ b)⟩
        let ητ : rootsOfUnity n L :=
          ⟨radicalClassRatio K Ω n L τ b,
            (mem_rootsOfUnity n _).2
              (radical_class_ratio K Ω n L τ b)⟩
        have hη : ηστ = ησ * ητ := by
          apply Subtype.ext
          exact automorphism_ratio_aut K n hn hζ
            (radicalClassRepresentative K Ω n L b)
            (radicalClassRoot K Ω n L b)
            (radical_root_pow K Ω n L b) σ τ
        change ((e.symm ηστ : rootsOfUnity n K) : Kˣ) =
          ((e.symm ησ : rootsOfUnity n K) : Kˣ) *
            ((e.symm ητ : rootsOfUnity n K) : Kˣ)
        rw [hη, map_mul]
        rfl }

/-- The radical pairing as a homomorphism into the character group of the
Galois group. -/
def radicalPairingHom
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) :
    radicalPowerClasses K Ω n L →* (Gal(L/K) →* Kˣ) where
  toFun := radicalGaloisCharacter K Ω n L hn hζ
  map_one' := by
    apply MonoidHom.ext
    intro σ
    letI : NeZero n := ⟨hn.ne'⟩
    let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
    let η : rootsOfUnity n L :=
      ⟨radicalClassRatio K Ω n L σ 1,
        (mem_rootsOfUnity n _).2
          (radical_class_ratio K Ω n L σ 1)⟩
    have hη : η = 1 := by
      apply Subtype.ext
      exact class_ratio_one K Ω n L hn hζ σ
    simpa [radicalGaloisCharacter, η] using congrArg
      (fun z : rootsOfUnity n L ↦ ((e.symm z : rootsOfUnity n K) : Kˣ)) hη
  map_mul' := by
    intro b c
    apply MonoidHom.ext
    intro σ
    letI : NeZero n := ⟨hn.ne'⟩
    let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
    let ηbc : rootsOfUnity n L :=
      ⟨radicalClassRatio K Ω n L σ (b * c),
        (mem_rootsOfUnity n _).2
          (radical_class_ratio K Ω n L σ (b * c))⟩
    let ηb : rootsOfUnity n L :=
      ⟨radicalClassRatio K Ω n L σ b,
        (mem_rootsOfUnity n _).2
          (radical_class_ratio K Ω n L σ b)⟩
    let ηc : rootsOfUnity n L :=
      ⟨radicalClassRatio K Ω n L σ c,
        (mem_rootsOfUnity n _).2
          (radical_class_ratio K Ω n L σ c)⟩
    have hη : ηbc = ηb * ηc := by
      apply Subtype.ext
      exact class_ratio_mul K Ω n L hn hζ σ b c
    change ((e.symm ηbc : rootsOfUnity n K) : Kˣ) =
      ((e.symm ηb : rootsOfUnity n K) : Kˣ) *
        ((e.symm ηc : rootsOfUnity n K) : Kˣ)
    rw [hη, map_mul]
    rfl

omit [IsAlgClosure K Ω] in
/-- The radical-class Kummer pairing is injective for finite Galois
extensions. -/
theorem radical_pairing_injective
    [FiniteDimensional K L] [IsGalois K L]
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) :
    Function.Injective (radicalPairingHom K Ω n L hn hζ) := by
  intro b c hbc
  suffices b * c⁻¹ = 1 by
    exact (mul_inv_eq_one.mp this)
  let d := b * c⁻¹
  apply Subtype.ext
  change d.1 = 1
  rw [← power_radical_representative K Ω n L d]
  apply (QuotientGroup.eq_one_iff _).mpr
  let x := radicalClassRoot K Ω n L d
  have hchar : radicalGaloisCharacter K Ω n L hn hζ d = 1 := by
    change (radicalPairingHom K Ω n L hn hζ) (b * c⁻¹) = 1
    rw [map_mul, map_inv, hbc, mul_inv_cancel]
  have hfixed : ∀ σ : Gal(L/K), σ (x : L) = x := by
    intro σ
    have hz := DFunLike.congr_fun hchar σ
    have hratio : radicalClassRatio K Ω n L σ d = 1 := by
      letI : NeZero n := ⟨hn.ne'⟩
      let e := rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
      let η : rootsOfUnity n L :=
        ⟨radicalClassRatio K Ω n L σ d,
          (mem_rootsOfUnity n _).2
            (radical_class_ratio K Ω n L σ d)⟩
      have hηK : e.symm η = 1 := by
        apply Subtype.ext
        change (radicalGaloisCharacter K Ω n L hn hζ d) σ = 1 at hz
        exact hz
      have hη : η = 1 := by
        apply e.symm.injective
        simpa using hηK
      exact congrArg Subtype.val hη
    have hu : Units.map σ x = x := by
      have hm := congrArg (fun z : Lˣ ↦ z * x) hratio
      simpa [radicalClassRatio, automorphismRatio, x, mul_assoc] using hm
    exact congrArg (fun z : Lˣ ↦ (z : L)) hu
  have hxbot : (x : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed (x : L)).2 hfixed
  rw [IntermediateField.mem_bot] at hxbot
  obtain ⟨y, hy⟩ := hxbot
  refine ⟨Units.mk0 y (by
    intro hy0
    apply x.ne_zero
    change (x : L) = 0
    rw [← hy, hy0, map_zero]), ?_⟩
  have hxpow := radical_root_pow K Ω n L d
  apply Units.ext
  change y ^ n = (radicalClassRepresentative K Ω n L d : K)
  apply (algebraMap K L).injective
  rw [map_pow, hy]
  exact congrArg (fun z : Lˣ ↦ (z : L)) hxpow

omit [IsAlgClosure K Ω] in
/-- For a finite Galois extension of exponent dividing `n`, the radical
power-class subgroup is no larger than the extension degree.  This is the
cardinality half of Kummer theory opposite to
`kummer_field_card`: it follows from the injective radical pairing,
finite abelian duality, and `|Gal(L/K)| = [L:K]`. -/
theorem nat_radical_classes
    [FiniteDimensional K L] [IsGalois K L]
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexponent : ∀ σ : Gal(L/K), σ ^ n = 1) :
    Nat.card (radicalPowerClasses K Ω n L) ≤ Module.finrank K L := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hexp : Monoid.exponent Gal(L/K) ∣ n := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact hexponent
  letI : HasEnoughRootsOfUnity K n :=
    { prim := ⟨hζ.choose, (mem_primitiveRoots hn).mp hζ.choose_spec⟩
      cyc := rootsOfUnity.isCyclic K n }
  letI : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) :=
    HasEnoughRootsOfUnity.of_dvd K hexp
  letI : HasEnoughRootsOfUnity K (Monoid.exponent (Abelianization Gal(L/K))) :=
    HasEnoughRootsOfUnity.of_dvd K
      (Group.exponent_quotient_dvd (commutator Gal(L/K)))
  calc
    Nat.card (radicalPowerClasses K Ω n L) ≤
        Nat.card (Gal(L/K) →* Kˣ) :=
      Nat.card_le_card_of_injective
        (radicalPairingHom K Ω n L hn hζ)
        (radical_pairing_injective K Ω n L hn hζ)
    _ = Nat.card (Abelianization Gal(L/K) →* Kˣ) :=
      Nat.card_congr (Abelianization.lift (G := Gal(L/K)) (A := Kˣ))
    _ = Nat.card (Abelianization Gal(L/K)) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        (Abelianization Gal(L/K)) K
    _ ≤ Nat.card Gal(L/K) :=
      Nat.card_le_card_of_surjective Abelianization.of
        (QuotientGroup.mk'_surjective (commutator Gal(L/K)))
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

omit [IsAlgClosure K Ω] in
/-- Under the same hypotheses, the radical power-class subgroup is actually
finite.  This supplies the finiteness datum needed by the extension-to-class
map in Theorem A.3. -/
theorem finite_radical_classes
    [FiniteDimensional K L] [IsGalois K L]
    (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexponent : ∀ σ : Gal(L/K), σ ^ n = 1) :
    Finite (radicalPowerClasses K Ω n L) := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hexp : Monoid.exponent Gal(L/K) ∣ n := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact hexponent
  letI : HasEnoughRootsOfUnity K n :=
    { prim := ⟨hζ.choose, (mem_primitiveRoots hn).mp hζ.choose_spec⟩
      cyc := rootsOfUnity.isCyclic K n }
  letI : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) :=
    HasEnoughRootsOfUnity.of_dvd K hexp
  exact Finite.of_injective
    (radicalPairingHom K Ω n L hn hζ)
    (radical_pairing_injective K Ω n L hn hζ)

end RadicalClasses

end

end Towers.CField.KTheory
