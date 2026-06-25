import Submission.FieldTheory.RationalFinitePlace
import Submission.FieldTheory.RestrictNormal
import Submission.NumberTheory.UnramifiedInertia

/-!
# Ramification in finite composita

An inertia element of a finite Galois compositum restricts to inertia in each
factor.  Consequently a compositum of number fields unramified at a rational
prime is again unramified there.
-/

open scoped Pointwise

noncomputable section

namespace Submission
namespace TBluepr

/-- Every rational prime is unramified in the base field `ℚ`. -/
theorem rational_unramified_rat {q : ℕ} (hq : Nat.Prime q) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers ℚ) q := by
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  let e0 : NumberField.RingOfIntegers ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) (by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe])
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  have halg :
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) = e0.symm.toRingHom :=
    Subsingleton.elim _ _
  have hmap : P.map e0.toRingHom = qI := by
    have hover : qI = P.comap (algebraMap ℤ
        (NumberField.RingOfIntegers ℚ)) := by
      exact P.over_def qI
    rw [halg] at hover
    calc
      P.map e0.toRingHom = P.comap e0.symm.toRingHom :=
        (Ideal.comap_symm (I := P) e0.toRingEquiv).symm
      _ = qI := hover.symm
  have hqtop : qI ≠ ⊤ := by
    exact Ideal.IsPrime.ne_top (rational_prime_ideal hq)
  have hqbot : qI ≠ ⊥ := rational_ne_bot hq
  have hmaptop : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊤ := by
    simpa using hqtop
  have hmapbot : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊥ := by
    simpa using hqbot
  calc
    Ideal.ramificationIdx qI P =
        Ideal.ramificationIdx qI (P.map e0.toRingHom) := by
      symm
      exact Ideal.ramificationIdx_map_eq (p := qI) (P := P) e0
    _ = Ideal.ramificationIdx qI qI := by rw [hmap]
    _ = 1 := by
      simpa using
        (Ideal.ramificationIdx_map_self_eq_one (R := ℤ) (S := ℤ)
          (p := qI) hmaptop hmapbot)

/-- Unramifiedness descends to a finite intermediate field, using the
intermediate field's canonical algebra structure. -/
theorem rational_intermediate_canonical
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    (E : IntermediateField ℚ K)
    (hEfin : letI : Algebra ℚ E := E.algebra'; FiniteDimensional ℚ E)
    {q : ℕ} (hq : Nat.Prime q)
    (hK : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers K) q) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers E) q := by
  letI : Algebra ℚ E := E.algebra'
  letI : FiniteDimensional ℚ E := hEfin
  letI : NumberField E := NumberField.of_module_finite ℚ E
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  obtain ⟨⟨Q, hQprime, hQoverP⟩⟩ :=
    P.nonempty_primesOver (S := NumberField.RingOfIntegers K)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver P := hQoverP
  letI : Q.LiesOver qI := Ideal.LiesOver.trans Q P qI
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) Q
  letI : Algebra.IsUnramifiedAt ℤ Q := by
    have hramQ : Ideal.ramificationIdx (Ideal.under ℤ Q) Q = 1 := by
      rw [← Ideal.LiesOver.over (P := Q) (p := qI)]
      exact hK Q ⟨hQprime, inferInstance⟩
    exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := NumberField.RingOfIntegers K) (p := Q) hQ0).2 hramQ
  letI : Algebra.IsUnramifiedAt ℤ P :=
    Algebra.IsUnramifiedAt.of_liesOver (R := ℤ) P Q
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) P
  have hramP : Ideal.ramificationIdx (Ideal.under ℤ P) P = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := NumberField.RingOfIntegers E) (p := P) hP0).1
        (show Algebra.IsUnramifiedAt ℤ P from inferInstance)
  rw [← Ideal.LiesOver.over (P := P) (p := qI)] at hramP
  exact hramP

/-- Restricting an inertia element to a normal intermediate field again gives
an inertia element at the prime below. -/
theorem number_restrict_intermediate
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : IntermediateField ℚ L)
    (hE : @Normal ℚ E _ _ E.algebra')
    {q : ℕ}
    {P : Ideal (NumberField.RingOfIntegers L)}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (sigma : Gal(L/ℚ))
    (hsigma : sigma ∈ P.inertia Gal(L/ℚ)) :
    ∀ x : NumberField.RingOfIntegers E,
      MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E)
          ((@AlgEquiv.restrictNormalHom ℚ _ L _ _ E _ E.algebra' _ _ hE)
            sigma) x - x ∈
        P.under (NumberField.RingOfIntegers E) := by
  let Q : Ideal (NumberField.RingOfIntegers E) :=
    P.under (NumberField.RingOfIntegers E)
  intro x
  change
    MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E)
        ((@AlgEquiv.restrictNormalHom ℚ _ L _ _ E _ E.algebra' _ _ hE) sigma) x -
      x ∈ Q
  rw [Ideal.mem_of_liesOver
    (A := NumberField.RingOfIntegers E)
    (B := NumberField.RingOfIntegers L)
    (p := Q)
    (P := P)]
  rw [map_sub]
  have hmap :
      algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L)
          (MulSemiringAction.toAlgHom ℤ
            (NumberField.RingOfIntegers E)
            ((@AlgEquiv.restrictNormalHom ℚ _ L _ _ E _ E.algebra' _ _ hE)
              sigma) x) =
        MulSemiringAction.toAlgHom ℤ
          (NumberField.RingOfIntegers L) sigma
            (algebraMap (NumberField.RingOfIntegers E)
              (NumberField.RingOfIntegers L) x) := by
    apply Subtype.ext
    change
      algebraMap E L
          (((@AlgEquiv.restrictNormalHom ℚ _ L _ _ E _ E.algebra' _ _ hE)
              sigma)
            (algebraMap (NumberField.RingOfIntegers E) E x)) =
        sigma
          (algebraMap E L
            (algebraMap (NumberField.RingOfIntegers E) E x))
    simpa using
      (@AlgEquiv.restrictNormalHom_apply
        ℚ _ L _ _ E hE sigma
        (algebraMap (NumberField.RingOfIntegers E) E x))
  rw [hmap]
  simpa using hsigma
    (algebraMap (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers L) x)

set_option maxHeartbeats 1000000 in
-- Completion of the two restriction maps creates a large dependent field tower.
set_option synthInstance.maxHeartbeats 500000 in
/-- The compositum of two finite Galois number fields unramified at `q` is
again unramified at `q`. -/
theorem rational_unramified_sup
    {Omega : Type*} [Field Omega] [Algebra ℚ Omega]
    (E F : IntermediateField ℚ Omega)
    (hEfin : letI : Algebra ℚ E := E.algebra'; FiniteDimensional ℚ E)
    (hFfin : letI : Algebra ℚ F := F.algebra'; FiniteDimensional ℚ F)
    (hEgal : letI : Algebra ℚ E := E.algebra'; IsGalois ℚ E)
    (hFgal : letI : Algebra ℚ F := F.algebra'; IsGalois ℚ F)
    {q : ℕ} (hq : Nat.Prime q)
    (hE : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers E) q)
    (hF : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers F) q) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers (E ⊔ F : IntermediateField ℚ Omega)) q := by
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra ℚ F := F.algebra'
  letI : FiniteDimensional ℚ E := hEfin
  letI : FiniteDimensional ℚ F := hFfin
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : IsGalois ℚ E := hEgal
  letI : IsGalois ℚ F := hFgal
  let K : IntermediateField ℚ Omega := E ⊔ F
  letI : Algebra ℚ K := K.algebra'
  letI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup E F
  letI : NumberField K := NumberField.of_module_finite ℚ K
  letI : Normal ℚ E := IsGalois.to_normal
  letI : Normal ℚ F := IsGalois.to_normal
  letI : Algebra.IsSeparable ℚ E := IsGalois.to_isSeparable
  letI : Algebra.IsSeparable ℚ F := IsGalois.to_isSeparable
  letI : IsGalois ℚ K :=
    { to_normal := inferInstance
      to_isSeparable := inferInstance }
  let EK : IntermediateField ℚ K := E.restrict le_sup_left
  let FK : IntermediateField ℚ K := F.restrict le_sup_right
  letI : Algebra ℚ EK := EK.algebra'
  letI : Algebra ℚ FK := FK.algebra'
  letI : Algebra EK K := EK.toAlgebra
  letI : Algebra FK K := FK.toAlgebra
  let eE : E ≃ₐ[ℚ] EK := IntermediateField.restrict_algEquiv le_sup_left
  let eF : F ≃ₐ[ℚ] FK := IntermediateField.restrict_algEquiv le_sup_right
  letI : FiniteDimensional ℚ EK := Module.Finite.equiv eE.toLinearEquiv
  letI : FiniteDimensional ℚ FK := Module.Finite.equiv eF.toLinearEquiv
  letI : NumberField EK := NumberField.of_module_finite ℚ EK
  letI : NumberField FK := NumberField.of_module_finite ℚ FK
  letI : IsGalois ℚ EK := IsGalois.of_algEquiv eE
  letI : IsGalois ℚ FK := IsGalois.of_algEquiv eF
  have hEK : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers EK) q :=
    rational_unramified_alg eE hE
  have hFK : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers FK) q :=
    rational_unramified_alg eF hF
  have hsup : EK ⊔ FK = ⊤ := by
    apply (IntermediateField.lift_inj (EK ⊔ FK) ⊤).mp
    rw [IntermediateField.lift_sup ℚ K EK FK,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top ℚ K]
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
  have hinertia : P.inertia Gal(K/ℚ) = ⊥ := by
    apply le_antisymm
    · intro sigma hsigma
      rw [Subgroup.mem_bot]
      let QE : Ideal (NumberField.RingOfIntegers EK) :=
        P.under (NumberField.RingOfIntegers EK)
      let QF : Ideal (NumberField.RingOfIntegers FK) :=
        P.under (NumberField.RingOfIntegers FK)
      letI : QE.IsPrime := inferInstance
      letI : QE.LiesOver (Ideal.rationalPrimeIdeal q) := inferInstance
      letI : QF.IsPrime := inferInstance
      letI : QF.LiesOver (Ideal.rationalPrimeIdeal q) := inferInstance
      have hsigmaE : sigma.restrictNormalHom EK ∈ QE.inertia Gal(EK/ℚ) :=
        number_restrict_intermediate
          (q := q) (P := P) EK IsGalois.to_normal sigma hsigma
      have hsigmaF : sigma.restrictNormalHom FK ∈ QF.inertia Gal(FK/ℚ) :=
        number_restrict_intermediate
          (q := q) (P := P) FK IsGalois.to_normal sigma hsigma
      have hIE : QE.inertia Gal(EK/ℚ) = ⊥ :=
        number_bot_unramified
          EK hq hEK QE
      have hIF : QF.inertia Gal(FK/ℚ) = ⊥ :=
        number_bot_unramified
          FK hq hFK QF
      have hresE : sigma.restrictNormalHom EK = 1 := by
        exact Subgroup.mem_bot.mp (hIE ▸ hsigmaE)
      have hresF : sigma.restrictNormalHom FK = 1 := by
        exact Subgroup.mem_bot.mp (hIF ▸ hsigmaF)
      have hfixE : sigma ∈ EK.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hx' := congrArg (fun tau : Gal(EK/ℚ) => tau ⟨x, hx⟩) hresE
        calc
          sigma x = ↑((sigma.restrictNormalHom EK) ⟨x, hx⟩) := by
            symm
            exact AlgEquiv.restrictNormal_commutes
              (χ := sigma) (E := EK) ⟨x, hx⟩
          _ = x := by simpa using congrArg Subtype.val hx'
      have hfixF : sigma ∈ FK.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hx' := congrArg (fun tau : Gal(FK/ℚ) => tau ⟨x, hx⟩) hresF
        calc
          sigma x = ↑((sigma.restrictNormalHom FK) ⟨x, hx⟩) := by
            symm
            exact AlgEquiv.restrictNormal_commutes
              (χ := sigma) (E := FK) ⟨x, hx⟩
          _ = x := by simpa using congrArg Subtype.val hx'
      have hfix : sigma ∈ (EK ⊔ FK).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hfixE, hfixF⟩
      rw [hsup, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hfix
      exact hfix
    · exact bot_le
  exact ramification_idx_bot K hq P hinertia

/-- A finite compositum of finite-dimensional intermediate fields remains
finite-dimensional.  The hypotheses use each field's canonical algebra. -/
theorem finset_i_dimensional
    {Omega ι : Type*} [Field Omega] [Algebra ℚ Omega]
    (t : ι → IntermediateField ℚ Omega) (s : Finset ι)
    (hfin : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      FiniteDimensional ℚ (t i)) :
    let U : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
    letI : Algebra ℚ U := U.algebra'
    FiniteDimensional ℚ U := by
  let U : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
  letI : Algebra ℚ U := U.algebra'
  change FiniteDimensional ℚ ↥(⨆ i ∈ s, t i)
  exact IntermediateField.finiteDimensional_iSup_of_finset'
    (t := t) (s := s) (fun i _ => hfin i)

/-- A finite compositum of finite Galois intermediate fields is Galois. -/
theorem finset_i_sup
    {Omega ι : Type*} [Field Omega] [Algebra ℚ Omega]
    (t : ι → IntermediateField ℚ Omega) (s : Finset ι)
    (hgal : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      IsGalois ℚ (t i)) :
    let U : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
    letI : Algebra ℚ U := U.algebra'
    IsGalois ℚ U := by
  classical
  dsimp only
  let index := {i // i ∈ s}
  let family : index → IntermediateField ℚ Omega := fun i => t i.1
  let U : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
  let V : IntermediateField ℚ Omega := ⨆ i : index, family i
  have hU : U = V := by
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    · refine iSup_le fun i => ?_
      exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  letI : Algebra ℚ V := V.algebra'
  have hnormal : Normal ℚ V := by
    simpa [V, family] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := Omega) (t := family)
        (h := fun i => by
          letI : Algebra ℚ (family i) := (family i).algebra'
          simpa [family] using (hgal i.1).to_normal))
  have hseparable : Algebra.IsSeparable ℚ V := by
    simpa [V, family] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := Omega) (t := family)
        (h := fun i => by
          letI : Algebra ℚ (family i) := (family i).algebra'
          simpa [family] using (hgal i.1).to_isSeparable))
  letI : IsGalois ℚ V :=
    { to_normal := hnormal, to_isSeparable := hseparable }
  letI : Algebra ℚ U := U.algebra'
  exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hU).symm

theorem finset_sup_bi
    {F Omega ι : Type*} [Field F] [Field Omega] [Algebra F Omega]
    (t : ι → IntermediateField F Omega) (s : Finset ι) :
    s.sup t = ⨆ i ∈ s, t i := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact Finset.le_sup (f := t) hi

theorem finset_sup_dimensional
    {Omega ι : Type*} [Field Omega] [Algebra ℚ Omega]
    (t : ι → IntermediateField ℚ Omega) (s : Finset ι)
    (hfin : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      FiniteDimensional ℚ (t i)) :
    let U : IntermediateField ℚ Omega := s.sup t
    letI : Algebra ℚ U := U.algebra'
    FiniteDimensional ℚ U := by
  let V : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
  letI : Algebra ℚ V := V.algebra'
  letI : FiniteDimensional ℚ V := finset_i_dimensional t s hfin
  let U : IntermediateField ℚ Omega := s.sup t
  letI : Algebra ℚ U := U.algebra'
  let e : V ≃ₐ[ℚ] U :=
    (IntermediateField.equivOfEq (finset_sup_bi t s)).symm
  exact Module.Finite.equiv e.toLinearEquiv

theorem finset_sup_galois
    {Omega ι : Type*} [Field Omega] [Algebra ℚ Omega]
    (t : ι → IntermediateField ℚ Omega) (s : Finset ι)
    (hgal : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      IsGalois ℚ (t i)) :
    let U : IntermediateField ℚ Omega := s.sup t
    letI : Algebra ℚ U := U.algebra'
    IsGalois ℚ U := by
  let V : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
  letI : Algebra ℚ V := V.algebra'
  letI : IsGalois ℚ V := finset_i_sup t s hgal
  let U : IntermediateField ℚ Omega := s.sup t
  letI : Algebra ℚ U := U.algebra'
  let e : V ≃ₐ[ℚ] U :=
    (IntermediateField.equivOfEq (finset_sup_bi t s)).symm
  exact IsGalois.of_algEquiv e

set_option maxHeartbeats 2000000 in
-- The induction repeatedly transports canonical algebra structures across finite suprema.
set_option synthInstance.maxHeartbeats 500000 in
/-- A finite compositum of finite Galois fields unramified at `q` is
unramified at `q`. -/
theorem rational_finset_sup
    {Omega ι : Type*} [Field Omega] [Algebra ℚ Omega]
    (t : ι → IntermediateField ℚ Omega)
    (hfin : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      FiniteDimensional ℚ (t i))
    (hgal : ∀ i,
      letI : Algebra ℚ (t i) := (t i).algebra'
      IsGalois ℚ (t i))
    {q : ℕ} (hq : Nat.Prime q)
    (s : Finset ι)
    (hunram : ∀ i ∈ s,
      RationalPrimeUnramified
        (S := NumberField.RingOfIntegers (t i)) q) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers
        (s.sup t : IntermediateField ℚ Omega)) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      let B : IntermediateField ℚ Omega := ⊥
      letI : Algebra ℚ B := B.algebra'
      letI : FiniteDimensional ℚ B := by
        exact (IntermediateField.botEquiv ℚ Omega).symm.toLinearEquiv.finiteDimensional
      letI : NumberField B := NumberField.of_module_finite ℚ B
      let e : ℚ ≃ₐ[ℚ] B := (IntermediateField.botEquiv ℚ Omega).symm
      simpa [B] using
        (rational_unramified_alg e
          (rational_unramified_rat hq))
  | @insert a s ha ih =>
      let V : IntermediateField ℚ Omega := ⨆ i ∈ s, t i
      letI : Algebra ℚ V := V.algebra'
      letI : FiniteDimensional ℚ V :=
        finset_i_dimensional t s hfin
      letI : IsGalois ℚ V := finset_i_sup t s hgal
      let U : IntermediateField ℚ Omega := s.sup t
      letI : Algebra ℚ U := U.algebra'
      let eVU : V ≃ₐ[ℚ] U :=
        (IntermediateField.equivOfEq (finset_sup_bi t s)).symm
      letI : FiniteDimensional ℚ U := Module.Finite.equiv eVU.toLinearEquiv
      letI : IsGalois ℚ U := IsGalois.of_algEquiv eVU
      have hU : RationalPrimeUnramified
          (S := NumberField.RingOfIntegers U) q := by
        simpa [U] using ih (fun i hi => hunram i (Finset.mem_insert_of_mem hi))
      have haUnram : RationalPrimeUnramified
          (S := NumberField.RingOfIntegers (t a)) q :=
        hunram a (Finset.mem_insert_self a s)
      have hsup := rational_unramified_sup
        (t a) U (hfin a) (by infer_instance) (hgal a) (by infer_instance)
        hq haUnram hU
      rw [Finset.sup_insert]
      exact hsup

end TBluepr
end Submission
