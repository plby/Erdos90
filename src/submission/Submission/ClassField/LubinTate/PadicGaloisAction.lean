import Submission.ClassField.LubinTate.PadicCyclotomic
import Submission.ClassField.LubinTate.RootGaloisAction
import Submission.ClassField.LubinTate.CyclotomicResidueDegree
import Submission.ClassField.FormalGroups.PowerSeriesUnary
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The finite cyclotomic Lubin--Tate Galois action

This file puts the generic finite Lubin--Tate quotient and the standard
cyclotomic Galois coordinate in the same types.  The direct quotient-unit
action sends `zeta` to `zeta ^ u`; the local Artin convention of Example
I.3.13 is its inverse on units.
-/

namespace Submission.CField.LTate

noncomputable section

open Submission.CField.FGroups
open scoped NormedField Topology

/-- A lift of a quotient unit acts on its orbit point by ordinary scalar
multiplication.  Kept as a separate cache boundary so finite local-field
instance telescopes do not normalize this quotient calculation repeatedly. -/
theorem torsion_smul_mk
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I)
    (a : A) (u : (A ⧸ I)ˣ)
    (ha : Ideal.Quotient.mk I a = (u : A ⧸ I)) :
    orbitEmbeddingTorsion y hy u = a • y := by
  change
    (spanSingletonTorsion y hy (u : A ⧸ I) : M) = a • y
  rw [← ha, singleton_torsion_mk]
  rfl

/-- For a natural scalar, the canonical endomorphism of the transported
cyclotomic Lubin--Tate datum is the literal polynomial `(1 + X)^k - 1`.
Using natural representatives is enough at every finite torsion level. -/
theorem lubin_scalar_intertwiner
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
    letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
    powerSeriesUnary (cyclotomicPowerSeries (R := A) k) =
      tateScalarIntertwiner D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit
        (padic_integer_residue p)
        (D.f : PowerSeries A) (D.f : PowerSeries A)
        D.lubin_tate_card D.lubin_tate_card
        (k : A) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
    padic_integer_residue p
  let hf := D.lubin_tate_card
  apply tate_intertwiner D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      (D.f : PowerSeries A) hf hf (fun _ : Fin 1 ↦ (k : A))
  apply unary_intertwiner_commutes
  · simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      D.lubinTateSeries.1
  · simp [cyclotomicPowerSeries]
  · simp [cyclotomicPowerSeries, PowerSeries.coeff_one_pow]
  · rw [lubin_datum_f]
    exact cyclotomic_subst_commute k p

/-- Evaluation form of the preceding natural-scalar identity on relative
adic Lubin--Tate points. -/
theorem padic_integer_smul
    (p : ℕ) [Fact p.Prime]
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I)
    (rho : Valuation.integer (NormedField.valuation (K := ℚ_[p])) →+* B) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
    letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
    let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
      padic_integer_residue p
    let hf := D.lubin_tate_card
    ∀ (k : ℕ)
      (x : RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) hf),
      (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
          ((k : A) • x) : B) =
        PowerSeries.eval₂ (RingHom.id B)
          (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
              D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
            x : B)
          (PowerSeries.map rho (cyclotomicPowerSeries (R := A) k)) := by
  dsimp only
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
    padic_integer_residue p
  let hf := D.lubin_tate_card
  intro k x
  rw [relative_lubin_points]
  change MvPowerSeries.eval₂ (RingHom.id B) _
      (MvPowerSeries.map rho
        (tateScalarIntertwiner D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          (D.f : PowerSeries A) hf hf (k : A))) = _
  rw [← lubin_scalar_intertwiner p k]
  have hmap : MvPowerSeries.map rho
      (powerSeriesUnary (cyclotomicPowerSeries (R := A) k)) =
        powerSeriesUnary
          (PowerSeries.map rho (cyclotomicPowerSeries (R := A) k)) := by
    rw [powerSeriesUnary, powerSeriesUnary, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by
        simp [FGLaw.unaryX]))]
    simp only [FGLaw.unaryX, MvPowerSeries.map_X]
  rw [hmap, powerSeriesUnary]
  change MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
          x : B))
      (PowerSeries.subst FGLaw.unaryX
        (PowerSeries.map rho (cyclotomicPowerSeries (R := A) k))) = _
  have heval := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (fun _ : Unit ↦ FGLaw.unaryX)
    (fun _ ↦ by simp [FGLaw.unaryX])
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
        x : B))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
      x).2)
    (PowerSeries.map rho (cyclotomicPowerSeries (R := A) k))
  simpa [PowerSeries.subst, FGLaw.unaryX] using heval

/-- Natural scalar multiplication in the cyclotomic Lubin--Tate module is
ordinary exponentiation in the multiplicative coordinate `1 + x`. -/
theorem padic_cyclotomic_smul
    (p : ℕ) [Fact p.Prime]
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I)
    (rho : Valuation.integer (NormedField.valuation (K := ℚ_[p])) →+* B) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
    letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
    let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
      padic_integer_residue p
    let hf := D.lubin_tate_card
    ∀ (k : ℕ)
      (x : RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) hf),
      (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
          ((k : A) • x) : B) =
        (1 + (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A) hf).map rho)
          x : B)) ^ k - 1 := by
  dsimp only
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
    padic_integer_residue p
  let hf := D.lubin_tate_card
  intro k x
  rw [padic_integer_smul p hI rho k x]
  have hmap : PowerSeries.map rho (cyclotomicPowerSeries (R := A) k) =
      cyclotomicPowerSeries (R := B) k := by
    simp [cyclotomicPowerSeries]
  rw [hmap]
  have hcoe : cyclotomicPowerSeries (R := B) k =
      (((1 + Polynomial.X : Polynomial B) ^ k - 1 : Polynomial B) :
        PowerSeries B) := by
    symm
    simp [cyclotomicPowerSeries]
  rw [hcoe, PowerSeries.eval₂_coe]
  simp

set_option maxHeartbeats 4000000 in
-- Specializing the spectral root-field action carries the full local-field instance telescope.
/-- The quotient-unit orbit supplied by the generic finite Lubin--Tate
theorem is the direct cyclotomic action on the distinguished root coordinate:
`1 + root` is raised to the residue-unit exponent. -/
theorem padic_integer_explicit
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
        (D.RootField ℚ_[p] n ≃ₐ[ℚ_[p]] D.RootField ℚ_[p] n),
      ∀ u,
        orbit u (D.root ℚ_[p] n) =
          (1 + D.root ℚ_[p] n) ^
            ((padicZMod p (n + 1) u :
              ZMod (p ^ (n + 1))).val) - 1 := by
  dsimp only
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let hfield : IsField (A ⧸ Ideal.span {D.pi}) :=
    padic_integer_residue p
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  letI : ValuativeRel ℚ_[p] :=
    ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
  letI : Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := ℚ_[p]))
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  letI : IsNonarchimedeanLocalField ℚ_[p] :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }
  let E := D.RootField ℚ_[p] n
  letI : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E :=
    LBrauer.FLExt.valuativeRel ℚ_[p] E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace ℚ_[p] E
  letI : ProperSpace E := FiniteDimensional.proper ℚ_[p] E
  letI : (NormedField.valuation (K := ℚ_[p])).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension ℚ_[p] E
  let B := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      LBrauer.discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (LBrauer.valuativeIntegerNorm E)
  letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
  let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
    Submission.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let M := RelativeLubinPoints hI rho D.pi
    D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
    (D.f : PowerSeries A) D.lubin_tate_card
  let point : M → B := fun z ↦
    FGLaw.APts.toIdeal hI (F.map rho) z
  obtain ⟨y, hy, hyroot, orbit, horbit⟩ :=
    D.root_unit_orbit ℚ_[p] hfield n
  refine ⟨orbit, ?_⟩
  intro u
  let k : ℕ :=
    (padicZMod p (n + 1) u :
      ZMod (p ^ (n + 1))).val
  have hlift : Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 1)}) (k : A) =
      (u : A ⧸ Ideal.span {D.pi ^ (n + 1)}) := by
    exact padic_integer_lift p (n + 1) u
  have hq : orbitEmbeddingTorsion y hy u = (k : A) • y := by
    exact torsion_smul_mk
      y hy (k : A) u hlift
  calc
    orbit u (D.root ℚ_[p] n) = B.subtype
        (point (orbitEmbeddingTorsion y hy u)) := horbit u
    _ = B.subtype (point ((k : A) • y)) := by rw [hq]
    _ = B.subtype ((1 + (point y : B)) ^ k - 1) := by
      congr 1
      exact padic_cyclotomic_smul p hI rho k y
    _ = (1 + B.subtype (point y)) ^ k - 1 := by simp
    _ = (1 + D.root ℚ_[p] n) ^ k - 1 := by rw [hyroot]

/-- A fixed choice of the explicit finite Lubin--Tate orbit. -/
noncomputable def padicIntegerCyclotomic
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
      (D.RootField ℚ_[p] n ≃ₐ[ℚ_[p]] D.RootField ℚ_[p] n) :=
  Classical.choose
    (padic_integer_explicit p n)

@[simp]
theorem padic_integer_cyclotomic
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
    padicIntegerCyclotomic p n u
        ((padicLubinDatum p).root ℚ_[p] n) =
      (1 + (padicLubinDatum p).root ℚ_[p] n) ^
          ((padicZMod p (n + 1) u :
            ZMod (p ^ (n + 1))).val) - 1 :=
  Classical.choose_spec
    (padic_integer_explicit p n) u

/-- The explicit full orbit has degree-many automorphisms, hence the
cyclotomic Lubin--Tate root field is Galois without replaying its spectral
local-field construction. -/
noncomputable instance padicCyclotomicGalois
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsGalois ℚ_[p]
      ((padicLubinDatum p).RootField ℚ_[p] n) := by
  let D := padicLubinDatum p
  let orbit := padicIntegerCyclotomic p n
  apply IsGalois.of_card_aut_eq_finrank
  calc
    Nat.card Gal(D.RootField ℚ_[p] n/ℚ_[p]) =
        Nat.card
          (Valuation.integer (NormedField.valuation (K := ℚ_[p])) ⧸
            Ideal.span {D.pi ^ (n + 1)})ˣ :=
      Nat.card_congr orbit.symm.toEquiv
    _ = Module.finrank ℚ_[p] (D.RootField ℚ_[p] n) :=
      D.card_units_finrank ℚ_[p] n

/-- The finite cyclotomic Lubin--Tate Galois group is commutative because it
is explicitly equivalent to a quotient-unit group. -/
noncomputable instance padicIntegerCommutative
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsMulCommutative
      Gal((padicLubinDatum p).RootField ℚ_[p] n/ℚ_[p]) := by
  let orbit := padicIntegerCyclotomic p n
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  obtain ⟨u, rfl⟩ := orbit.surjective σ
  obtain ⟨v, rfl⟩ := orbit.surjective τ
  simpa only [map_mul] using congrArg orbit (mul_comm u v)

/-- The direct cyclotomic action of the finite quotient units belonging to
the valuation-integer Lubin--Tate datum. -/
noncomputable def padicIntegerGalois
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃* Gal(E/ℚ_[p]) :=
  (padicZMod p (n + 1)).trans
    (IsCyclotomicExtension.autEquivPow E
      (padicCyclotomic_irreducible p n)).symm

/-- In the standard finite coordinate, quotient unit `u` acts on the chosen
primitive root by the exponent represented by `u`. -/
theorem padic_cyclotomic_zeta
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    (u : let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
    padicIntegerGalois p n E u
        (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E) =
      IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E ^
        ((padicZMod p (n + 1) u :
          ZMod (p ^ (n + 1))).val) := by
  exact cyclotomic_aut_zeta
    (padicCyclotomic_irreducible p n)
    (padicZMod p (n + 1) u)

/-- The same formula in the Lubin--Tate root coordinate `zeta - 1`. -/
theorem padic_integer_zeta
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    (u : let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
    padicIntegerGalois p n E u
        (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1) =
      IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E ^
          ((padicZMod p (n + 1) u :
            ZMod (p ^ (n + 1))).val) - 1 := by
  rw [map_sub, map_one,
    padic_cyclotomic_zeta]

/-- Taking the inverse unit in the direct Lubin--Tate action gives exactly
Milne's local-Artin convention from Example I.3.13(b). -/
theorem padic_inv_action
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    (u : ℤ_[p]ˣ) :
    padicIntegerGalois p n E
        (padicIntInteger p (n + 1) u⁻¹) =
      padicCyclotomicAction p (n + 1)
        (padicCyclotomic_irreducible p n) (L := E) u := by
  change (IsCyclotomicExtension.autEquivPow E
      (padicCyclotomic_irreducible p n)).symm
        (padicZMod p (n + 1)
          (padicIntInteger p (n + 1) u⁻¹)) =
    (IsCyclotomicExtension.autEquivPow E
      (padicCyclotomic_irreducible p n)).symm
        (padicUnitReduction p (n + 1) u⁻¹)
  congr 1

/-- Transporting the fixed explicit root-field orbit to any model of the
cyclotomic extension gives the standard direct cyclotomic action. -/
theorem padic_cyclotomic_direct
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    let e := padicCyclotomicAlg p n E
    (padicIntegerCyclotomic p n).trans
        e.autCongr =
      padicIntegerGalois p n E := by
  dsimp only
  let e := padicCyclotomicAlg p n E
  apply MulEquiv.ext
  intro u
  apply AlgEquiv.coe_algHom_injective
  apply ((IsCyclotomicExtension.zeta_spec
    (p ^ (n + 1)) ℚ_[p] E).subOnePowerBasis ℚ_[p]).algHom_ext
  change (e.autCongr
      (padicIntegerCyclotomic p n u))
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1) =
    padicIntegerGalois p n E u
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1)
  rw [← padic_cyclotomic_alg p n E]
  rw [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, e, AlgEquiv.symm_apply_apply]
  rw [padic_integer_cyclotomic]
  simp only [map_sub, map_pow, map_add, map_one]
  rw [padic_cyclotomic_alg]
  rw [padic_integer_zeta]
  simp

/-- After identifying the abstract root field with a cyclotomic extension,
the generic Lubin--Tate quotient-unit orbit is exactly the standard direct
cyclotomic Galois equivalence.  This closes the orientation-sensitive finite
action comparison in Example I.3.13 before the local Artin inverse is taken. -/
theorem padic_integer_direct
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    let e := padicCyclotomicAlg p n E
    ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
        (D.RootField ℚ_[p] n ≃ₐ[ℚ_[p]] D.RootField ℚ_[p] n),
      orbit.trans e.autCongr =
        padicIntegerGalois p n E := by
  dsimp only
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  let e := padicCyclotomicAlg p n E
  obtain ⟨orbit, horbit⟩ :=
    padic_integer_explicit p n
  refine ⟨orbit, ?_⟩
  apply MulEquiv.ext
  intro u
  apply AlgEquiv.coe_algHom_injective
  apply ((IsCyclotomicExtension.zeta_spec
    (p ^ (n + 1)) ℚ_[p] E).subOnePowerBasis ℚ_[p]).algHom_ext
  change (e.autCongr (orbit u))
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1) =
    padicIntegerGalois p n E u
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1)
  rw [← padic_cyclotomic_alg p n E]
  rw [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, e, AlgEquiv.symm_apply_apply]
  rw [horbit u]
  simp only [map_sub, map_pow, map_add, map_one]
  rw [padic_cyclotomic_alg]
  rw [padic_integer_zeta]
  simp

end

end Submission.CField.LTate
