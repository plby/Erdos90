import Submission.FieldTheory.CentralEmbeddingRadical


/-!
# Kummer actions attached to abelian-kernel group extensions

This file realizes a group extension whose factor set becomes a Kummer
coboundary as automorphisms of the corresponding radical field.  Unlike the
central cubic construction, the kernel action is allowed to be nontrivial.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Polynomial AdjoinRoot

universe u

/-- The kernel coordinate of an element relative to the normalized section. -/
noncomputable def groupExtensionCoordinate
    {C E Q : Type u} [Group C] [Group E] [Group Q]
    (S : GroupExtension C E Q) (e : E) : C :=
  Function.invFun S.inl
    (e * (normalizedExtensionSection S (S.rightHom e))⁻¹)

theorem extension_inl_coordinate
    {C E Q : Type u} [Group C] [Group E] [Group Q]
    (S : GroupExtension C E Q) (e : E) :
    S.inl (groupExtensionCoordinate S e) =
      e * (normalizedExtensionSection S (S.rightHom e))⁻¹ := by
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom,
    MonoidHom.mem_ker, map_mul, map_inv,
    GroupExtension.Section.rightHom_section, mul_inv_cancel]

theorem group_extension_section
    {C E Q : Type u} [Group C] [Group E] [Group Q]
    (S : GroupExtension C E Q) (e : E) :
    S.inl (groupExtensionCoordinate S e) *
        normalizedExtensionSection S (S.rightHom e) = e := by
  rw [extension_inl_coordinate]
  group

theorem group_extension_mul
    {C E Q : Type u} [CommGroup C] [Group E] [Group Q]
    [MulDistribMulAction Q C]
    (S : GroupExtension C E Q)
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (e f : E) :
    groupExtensionCoordinate S (e * f) =
      groupExtensionCoordinate S e *
        (S.rightHom e • groupExtensionCoordinate S f) *
          extensionNormalizedValue S
            (S.rightHom e) (S.rightHom f) := by
  let s := normalizedExtensionSection S
  let n := groupExtensionCoordinate S
  let c := extensionNormalizedValue S
  apply S.inl_injective
  apply mul_right_cancel (b := s (S.rightHom e * S.rightHom f))
  calc
    S.inl (n (e * f)) * s (S.rightHom e * S.rightHom f) =
        S.inl (n (e * f)) * s (S.rightHom (e * f)) := by
          rw [map_mul S.rightHom]
    _ = e * f := group_extension_section S (e * f)
    _ = (S.inl (n e) * s (S.rightHom e)) *
          (S.inl (n f) * s (S.rightHom f)) := by
            rw [group_extension_section,
              group_extension_section]
    _ = S.inl (n e) * (s (S.rightHom e) * S.inl (n f)) *
            s (S.rightHom f) := by group
    _ = S.inl (n e) *
          (S.inl (S.rightHom e • n f) * s (S.rightHom e)) *
            s (S.rightHom f) := by
              rw [normalized_section_inl S hS]
    _ = S.inl (n e * (S.rightHom e • n f)) *
          (s (S.rightHom e) * s (S.rightHom f)) := by
            simp only [map_mul]
            group
    _ = S.inl (n e * (S.rightHom e • n f)) *
          (S.inl (c (S.rightHom e) (S.rightHom f)) *
            s (S.rightHom e * S.rightHom f)) := by
              rw [extension_normalized_section]
    _ = S.inl (n e * (S.rightHom e • n f) *
          c (S.rightHom e) (S.rightHom f)) *
        s (S.rightHom e * S.rightHom f) := by
          simp only [map_mul]
          group

/-- Cardinality is multiplicative in a finite group extension. -/
theorem group_extension_card
    {C E Q : Type u} [Group C] [Group E] [Group Q]
    [Finite C] [Finite E] [Finite Q]
    (S : GroupExtension C E Q) :
    Nat.card E = Nat.card C * Nat.card Q := by
  let kerEquiv : C ≃ S.rightHom.ker := Equiv.ofBijective
    (fun c : C => ⟨S.inl c, by simp⟩) ⟨by
      intro c d h
      apply S.inl_injective
      exact congrArg Subtype.val h, by
      intro z
      have hz : z.1 ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom]
        exact z.2
      obtain ⟨c, hc⟩ := hz
      exact ⟨c, Subtype.ext hc⟩⟩
  have hkerCard : Nat.card S.rightHom.ker = Nat.card C :=
    (Nat.card_congr kerEquiv).symm
  have hindex : S.rightHom.ker.index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr S.rightHom_surjective]
    simp
  calc
    Nat.card E = Nat.card S.rightHom.ker * S.rightHom.ker.index :=
      S.rightHom.ker.card_mul_index.symm
    _ = Nat.card C * Nat.card Q := by rw [hkerCard, hindex]

section Action

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]
  {C E : Type u} [CommGroup C] [Group E]
  [MulDistribMulAction Gal(L/K) C]

/-- The scalar by which an extension element acts on the Kummer radical. -/
noncomputable def groupKummerScalar
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (b : Gal(L/K) → Lˣ) (e : E) : Lˣ :=
  phi (groupExtensionCoordinate S e) * b (S.rightHom e)

omit [FiniteDimensional K L] [MulDistribMulAction Gal(L/K) C] in
theorem kummer_scalar_pow
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (n : ℕ)
    (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (e : E) :
    Units.map (S.rightHom e).toRingEquiv.toMonoidHom a / a =
      groupKummerScalar S phi b e ^ n := by
  rw [ha]
  simp only [groupKummerScalar, mul_pow]
  rw [hpow, one_mul]

omit [FiniteDimensional K L] [MulDistribMulAction Gal(L/K) C] in
theorem group_kummer_cochain
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau)) :
    b 1 = 1 := by
  have h := hb 1 1
  rw [extension_normalized_left, map_one] at h
  simpa using h

omit [FiniteDimensional K L] in
theorem kummer_scalar_mul
    (S : GroupExtension C E Gal(L/K))
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (phi : C →* Lˣ)
    (hphi : ∀ sigma : Gal(L/K), ∀ c : C,
      phi (sigma • c) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi c))
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau))
    (e f : E) :
    groupKummerScalar S phi b (e * f) =
      Units.map (S.rightHom e).toRingEquiv.toMonoidHom
          (groupKummerScalar S phi b f) *
        groupKummerScalar S phi b e := by
  let sigma := S.rightHom e
  let tau := S.rightHom f
  let ne := groupExtensionCoordinate S e
  let nf := groupExtensionCoordinate S f
  let c := extensionNormalizedValue S sigma tau
  have hcoord : groupExtensionCoordinate S (e * f) =
      ne * (sigma • nf) * c :=
    group_extension_mul S hS e f
  have hfactor :
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) * b sigma =
        phi c * b (sigma * tau) := by
    have h := hb sigma tau
    calc
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) * b sigma =
          (Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
              b (sigma * tau) * b sigma) * b (sigma * tau) := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      _ = phi c * b (sigma * tau) := by rw [h]
  change phi (groupExtensionCoordinate S (e * f)) *
      b (S.rightHom (e * f)) =
    Units.map sigma.toRingEquiv.toMonoidHom (phi nf * b tau) *
      (phi ne * b sigma)
  rw [hcoord]
  simp only [map_mul]
  rw [hphi]
  calc
    phi ne * Units.map sigma.toRingEquiv.toMonoidHom (phi nf) * phi c *
          b (sigma * tau) =
        phi ne * Units.map sigma.toRingEquiv.toMonoidHom (phi nf) *
          (phi c * b (sigma * tau)) := by group
    _ = phi ne * Units.map sigma.toRingEquiv.toMonoidHom (phi nf) *
          (Units.map sigma.toRingEquiv.toMonoidHom (b tau) * b sigma) := by
            rw [hfactor]
    _ = Units.map sigma.toRingEquiv.toMonoidHom (phi nf) *
          Units.map sigma.toRingEquiv.toMonoidHom (b tau) *
            (phi ne * b sigma) := by ac_rfl

/-- The Kummer automorphism attached to one element of the extension. -/
noncomputable def groupKummerAction
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (n : ℕ) [NeZero n]
    (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a))
    (e : E) : Gal(TameKummerAdjoin n a/K) :=
  tameSemilinearLift n a hirr (S.rightHom e)
    (groupKummerScalar S phi b e)
    (kummer_scalar_pow S phi n hpow b a ha e)

theorem kummer_action_mul
    (S : GroupExtension C E Gal(L/K))
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (phi : C →* Lˣ)
    (hphi : ∀ sigma : Gal(L/K), ∀ c : C,
      phi (sigma • c) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi c))
    (n : ℕ) [NeZero n] (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau))
    (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a))
    (e f : E) :
    groupKummerAction S phi n hpow b a ha hirr (e * f) =
      groupKummerAction S phi n hpow b a ha hirr e *
        groupKummerAction S phi n hpow b a ha hirr f := by
  let sigma := S.rightHom e
  let tau := S.rightHom f
  let bSigma := groupKummerScalar S phi b e
  let bTau := groupKummerScalar S phi b f
  let bMul := groupKummerScalar S phi b (e * f)
  have hst : S.rightHom (e * f) = sigma * tau := map_mul S.rightHom e f
  have hc : bMul =
      Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma :=
    kummer_scalar_mul S hS phi hphi b hb e f
  have hSigma := kummer_scalar_pow S phi n hpow b a ha e
  have hTau := kummer_scalar_pow S phi n hpow b a ha f
  have hEF := kummer_scalar_pow S phi n hpow b a ha (e * f)
  have hMul : Units.map (sigma * tau).toRingEquiv.toMonoidHom a / a =
      bMul ^ n := by
    rw [← hst]
    exact hEF
  have h := tame_semilinear_cocycle n a hirr sigma tau
    bSigma bTau bMul hSigma hTau hMul hc
  change tameSemilinearLift n a hirr (S.rightHom (e * f)) bMul hEF = _
  exact (tame_semilinear_congr n a hirr hst bMul hEF hMul).trans h.symm

/-- The Kummer automorphisms form a homomorphism from the extension group. -/
noncomputable def extensionKummerAction
    (S : GroupExtension C E Gal(L/K))
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (phi : C →* Lˣ)
    (hphi : ∀ sigma : Gal(L/K), ∀ c : C,
      phi (sigma • c) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi c))
    (n : ℕ) [NeZero n] (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau))
    (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a)) :
    E →* Gal(TameKummerAdjoin n a/K) where
  toFun := groupKummerAction S phi n hpow b a ha hirr
  map_one' := by
    let z := groupKummerAction S phi n hpow b a ha hirr 1
    have hz : z = z * z := by
      simpa [z] using kummer_action_mul S hS phi hphi n hpow
        b hb a ha hirr 1 1
    apply mul_left_cancel (a := z)
    calc
      z * z = z := hz.symm
      _ = z * 1 := (mul_one z).symm
  map_mul' e f :=
    kummer_action_mul S hS phi hphi n hpow
      b hb a ha hirr e f

omit [MulDistribMulAction Gal(L/K) C] in
@[simp]
theorem extension_kummer_action
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (n : ℕ) [NeZero n]
    (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a))
    (e : E) (y : L) :
    groupKummerAction S phi n hpow b a ha hirr e
        (algebraMap L (TameKummerAdjoin n a) y) =
      algebraMap L (TameKummerAdjoin n a) (S.rightHom e y) := by
  simp [groupKummerAction]

omit [MulDistribMulAction Gal(L/K) C] in
@[simp]
theorem extension_kummer_root
    (S : GroupExtension C E Gal(L/K))
    (phi : C →* Lˣ) (n : ℕ) [NeZero n]
    (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a))
    (e : E) :
    groupKummerAction S phi n hpow b a ha hirr e
        (root (tameKummerPolynomial n a)) =
      algebraMap L (TameKummerAdjoin n a)
          (groupKummerScalar S phi b e : L) *
        root (tameKummerPolynomial n a) := by
  simp [groupKummerAction]

/-- A faithful coefficient embedding makes the Kummer action faithful. -/
theorem extension_kummer_injective
    (S : GroupExtension C E Gal(L/K))
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (phi : C →* Lˣ) (hphiInjective : Function.Injective phi)
    (hphi : ∀ sigma : Gal(L/K), ∀ c : C,
      phi (sigma • c) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi c))
    (n : ℕ) [NeZero n] (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau))
    (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a)) :
    Function.Injective
      (extensionKummerAction S hS phi hphi n hpow
        b hb a ha hirr) := by
  letI : Fact (Irreducible (tameKummerPolynomial n a)) := ⟨hirr⟩
  letI : Field (TameKummerAdjoin n a) := inferInstance
  let actionHom := extensionKummerAction S hS phi hphi n hpow
    b hb a ha hirr
  have hb1 : b 1 = 1 := group_kummer_cochain S phi b hb
  have hker : ∀ e : E, actionHom e = 1 → e = 1 := by
    intro e he
    have hbase : S.rightHom e = 1 := by
      apply AlgEquiv.ext
      intro y
      apply (algebraMap L (TameKummerAdjoin n a)).injective
      have happ := congrArg
        (fun g : Gal(TameKummerAdjoin n a/K) =>
          g (algebraMap L (TameKummerAdjoin n a) y)) he
      change groupKummerAction S phi n hpow b a ha hirr e
          (algebraMap L (TameKummerAdjoin n a) y) =
        algebraMap L (TameKummerAdjoin n a) y at happ
      rw [extension_kummer_action] at happ
      exact happ
    have hrootne : root (tameKummerPolynomial n a) ≠ 0 := by
      simpa [tameKummerPolynomial] using
        (root_X_pow_sub_C_ne_zero' (n := n) (Nat.pos_of_ne_zero (NeZero.ne n))
          (Units.ne_zero a))
    have hroot := congrArg
      (fun g : Gal(TameKummerAdjoin n a/K) =>
        g (root (tameKummerPolynomial n a))) he
    have hroot' :
        algebraMap L (TameKummerAdjoin n a)
            (groupKummerScalar S phi b e : L) *
              root (tameKummerPolynomial n a) =
          root (tameKummerPolynomial n a) := by
      change groupKummerAction S phi n hpow b a ha hirr e
          (root (tameKummerPolynomial n a)) =
        root (tameKummerPolynomial n a) at hroot
      rw [extension_kummer_root] at hroot
      exact hroot
    have hscalarMap :
        algebraMap L (TameKummerAdjoin n a)
            (groupKummerScalar S phi b e : L) = 1 := by
      apply mul_right_cancel₀ hrootne
      simpa using hroot'
    have hscalar : groupKummerScalar S phi b e = 1 := by
      apply Units.ext
      apply (algebraMap L (TameKummerAdjoin n a)).injective
      simpa using hscalarMap
    have hcoordMap : phi (groupExtensionCoordinate S e) = 1 := by
      simpa [groupKummerScalar, hbase, hb1] using hscalar
    have hcoord : groupExtensionCoordinate S e = 1 := by
      apply hphiInjective
      simpa using hcoordMap
    calc
      e = S.inl (groupExtensionCoordinate S e) *
          normalizedExtensionSection S (S.rightHom e) :=
            (group_extension_section S e).symm
      _ = 1 := by rw [hcoord, hbase, map_one,
        normalized_extension_section, one_mul]
  intro e f hef
  have hz : e * f⁻¹ = 1 := by
    apply hker
    rw [map_mul, map_inv, hef, mul_inv_cancel]
  exact mul_inv_eq_one.mp hz

/-- If the kernel has the radical degree, the faithful action has the full
degree.  Thus the radical extension is Galois and the action is bijective. -/
theorem extension_kummer_bijective
    [Finite C] [Finite E] [IsGalois K L]
    (S : GroupExtension C E Gal(L/K))
    (hS : ∀ e : E, ∀ c : C, S.conjAct e c = S.rightHom e • c)
    (phi : C →* Lˣ) (hphiInjective : Function.Injective phi)
    (hphi : ∀ sigma : Gal(L/K), ∀ c : C,
      phi (sigma • c) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi c))
    (n : ℕ) [NeZero n] (hcard : Nat.card C = n)
    (hpow : ∀ c : C, phi c ^ n = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma =
        phi (extensionNormalizedValue S sigma tau))
    (a : Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ n)
    (hirr : Irreducible (tameKummerPolynomial n a)) :
    letI : Fact (Irreducible (tameKummerPolynomial n a)) := ⟨hirr⟩
    ∃ _hGal : IsGalois K (TameKummerAdjoin n a),
      Function.Bijective
        (extensionKummerAction S hS phi hphi n hpow
          b hb a ha hirr) := by
  letI : Fact (Irreducible (tameKummerPolynomial n a)) := ⟨hirr⟩
  letI : Field (TameKummerAdjoin n a) := inferInstance
  let actionHom := extensionKummerAction S hS phi hphi n hpow
    b hb a ha hirr
  have hactionInjective : Function.Injective actionHom :=
    extension_kummer_injective S hS phi hphiInjective hphi
      n hpow b hb a ha hirr
  have hcardE : Nat.card E = n * Nat.card Gal(L/K) := by
    rw [group_extension_card S, hcard]
  have hfinrankLK : Module.finrank K L = Nat.card Gal(L/K) :=
    (IsGalois.card_aut_eq_finrank K L).symm
  have hfinrankNL : Module.finrank L (TameKummerAdjoin n a) = n := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    simp [tameKummerPolynomial]
  have hfinrankKN :
      Module.finrank K (TameKummerAdjoin n a) =
        n * Nat.card Gal(L/K) := by
    calc
      Module.finrank K (TameKummerAdjoin n a) =
          Module.finrank K L *
            Module.finrank L (TameKummerAdjoin n a) :=
        (Module.finrank_mul_finrank K L
          (TameKummerAdjoin n a)).symm
      _ = Nat.card Gal(L/K) * n := by rw [hfinrankLK, hfinrankNL]
      _ = n * Nat.card Gal(L/K) := Nat.mul_comm _ _
  have hcardEFinrank :
      Nat.card E = Module.finrank K (TameKummerAdjoin n a) :=
    hcardE.trans hfinrankKN.symm
  have hEleAut : Nat.card E ≤
      Nat.card Gal(TameKummerAdjoin n a/K) :=
    Nat.card_le_card_of_injective actionHom hactionInjective
  have hAutLeFinrank :
      Nat.card Gal(TameKummerAdjoin n a/K) ≤
        Module.finrank K (TameKummerAdjoin n a) := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hcardAut : Nat.card Gal(TameKummerAdjoin n a/K) =
      Module.finrank K (TameKummerAdjoin n a) := by
    apply Nat.le_antisymm hAutLeFinrank
    rw [← hcardEFinrank]
    exact hEleAut
  let hGal : IsGalois K (TameKummerAdjoin n a) :=
    IsGalois.of_card_aut_eq_finrank K (TameKummerAdjoin n a) hcardAut
  letI : IsGalois K (TameKummerAdjoin n a) := hGal
  letI := Fintype.ofFinite E
  letI := Fintype.ofFinite Gal(TameKummerAdjoin n a/K)
  have hactionSurjective : Function.Surjective actionHom :=
    (Fintype.bijective_iff_injective_and_card actionHom).2
      ⟨hactionInjective, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hcardEFinrank.trans hcardAut.symm⟩ |>.2
  exact ⟨hGal, hactionInjective, hactionSurjective⟩

end Action

end TBluepr
end Submission
