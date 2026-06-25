import Submission.ClassField.CohomologyOps.AllDegrees
import Submission.ClassField.CohomologyOps.DimensionShiftingIso
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Class Field Theory, Chapter II, Lemma 3.3(a,c)

For a finite group, positive-degree cohomology with trivial rational
coefficients vanishes.  We prove this by averaging the trace retraction of
the canonical embedding into a coinduced module.  We then apply the long
exact sequence of `0 -> Z -> Q -> Q/Z -> 0` to obtain Milne's canonical
isomorphism `Hom(G,Q/Z) ≃ H^2(G,Z)`.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep
open Submission.CField.COps

noncomputable section

variable (G : Type) [Group G] [Fintype G]

/-- The trivial rational representation. -/
private abbrev rationalRepresentation : Rep ℤ G := Rep.trivial ℤ G ℚ

/-- Multiplication by a rational number, as an endomorphism of the trivial
rational representation. -/
private noncomputable def rationalScale (c : ℚ) :
    rationalRepresentation G ⟶ rationalRepresentation G :=
  Rep.ofHom ⟨LinearMap.mulLeft ℤ c, by simp⟩

/-- The trace from the coinduced rational module, divided by `|G|`. -/
private noncomputable def rationalAverageRetraction :
    Rep.coind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype (rationalRepresentation G)) ⟶
      rationalRepresentation G :=
  corestrictionTrace (rationalRepresentation G) (⊥ : Subgroup G) ≫
    rationalScale G ((Fintype.card G : ℚ)⁻¹)

/-- Averaging retracts the canonical embedding of `Q` into its coinduced
module. -/
private theorem rational_average_retraction :
    canonicalShiftEmbedding (rationalRepresentation G) ≫
      rationalAverageRetraction G = 𝟙 (rationalRepresentation G) := by
  rw [rationalAverageRetraction, ← Category.assoc,
    canonicalShiftEmbedding]
  have htrace := res_coind_corestriction
    (rationalRepresentation G) (⊥ : Subgroup G)
  calc
    _ = ((⊥ : Subgroup G).index • 𝟙 (rationalRepresentation G)) ≫
        rationalScale G ((Fintype.card G : ℚ)⁻¹) :=
      congrArg (fun f => f ≫ rationalScale G ((Fintype.card G : ℚ)⁻¹)) htrace
    _ = 𝟙 (rationalRepresentation G) := by
      ext x
      change (Fintype.card G : ℚ)⁻¹ * ((⊥ : Subgroup G).index • x) = x
      rw [Subgroup.index_bot, Nat.card_eq_fintype_card]
      simp [nsmul_eq_mul, Fintype.card_ne_zero]

/-- The trivial rational representation is a retract of the coinduced
representation used in dimension shifting. -/
private noncomputable def rationalCoinducedRetract :
    Retract (rationalRepresentation G)
      (Rep.coind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype (rationalRepresentation G))) where
  i := canonicalShiftEmbedding (rationalRepresentation G)
  r := rationalAverageRetraction G
  retract := rational_average_retraction G

/-- A retract of a zero object is zero. -/
private theorem zero_retract {C : Type*} [Category C]
    {X Y : C} (h : Retract X Y) (hY : IsZero Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩⟩⟩
  · intro f
    calc
      f = 𝟙 X ≫ f := by simp
      _ = (h.i ≫ h.r) ≫ f := by rw [h.retract]
      _ = h.i ≫ (h.r ≫ f) := Category.assoc _ _ _
      _ = h.i ≫ hY.to_ Z := by rw [hY.eq_of_src (h.r ≫ f) (hY.to_ Z)]
  · intro f
    calc
      f = f ≫ 𝟙 X := by simp
      _ = f ≫ (h.i ≫ h.r) := by rw [h.retract]
      _ = (f ≫ h.i) ≫ h.r := (Category.assoc _ _ _).symm
      _ = hY.from_ Z ≫ h.r := by rw [hY.eq_of_tgt (f ≫ h.i) (hY.from_ Z)]

omit [Fintype G] in
/-- **Lemma II.3.3(a), positive degrees.** Rational group cohomology of a
finite group vanishes in every positive degree. -/
theorem cohomology_trivial_rat
    [Finite G]
    (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology (rationalRepresentation G) n) := by
  letI := Fintype.ofFinite G
  let h := (rationalCoinducedRetract G).map
    (groupCohomology.functor ℤ G n)
  exact zero_retract h <|
    zero_cohomology_coinduced
      (Rep.res (⊥ : Subgroup G).subtype (rationalRepresentation G)) n hn

/-- The integer-to-rational linear map. -/
private noncomputable def integerRationalLinear : ℤ →ₗ[ℤ] ℚ :=
  (Int.castAddHom ℚ).toIntLinearMap

/-- The copy of `Z` inside `Q`. -/
abbrev rationalIntegerLattice : Submodule ℤ ℚ :=
  LinearMap.range integerRationalLinear

/-- A concrete model for `Q/Z`. -/
abbrev rationalModIntegers := ℚ ⧸ rationalIntegerLattice

/-- A linear map between trivial modules is automa equivariant. -/
private def trivialRepHom
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →ₗ[ℤ] B) : Rep.trivial ℤ G A ⟶ Rep.trivial ℤ G B :=
  Rep.ofHom ⟨f, by simp⟩

/-- The inclusion `Z -> Q` as a morphism of trivial representations. -/
noncomputable def integerToRational :
    Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  trivialRepHom G integerRationalLinear

/-- The quotient `Q -> Q/Z` as a morphism of trivial representations. -/
noncomputable def rationalIntegers :
    Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (rationalModIntegers) :=
  trivialRepHom G (Submodule.mkQ rationalIntegerLattice)

instance rational_integers_epi : Epi (rationalIntegers G) := by
  rw [Rep.epi_iff_surjective]
  change Function.Surjective (Submodule.mkQ rationalIntegerLattice)
  exact Submodule.mkQ_surjective _

/-- The short complex `Z -> Q -> Q/Z`. -/
noncomputable def integerRationalSequence :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (integerToRational G) (rationalIntegers G) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change Submodule.mkQ rationalIntegerLattice (z : ℚ) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨z, rfl⟩)

/-- A morphism out of `Q` which kills `Z` descends to `Q/Z`. -/
private noncomputable def rationalQuotientDesc
    {A : Rep ℤ G} (k : Rep.trivial ℤ G ℚ ⟶ A)
    (hk : integerToRational G ≫ k = 0) :
    Rep.trivial ℤ G rationalModIntegers ⟶ A := by
  letI : Module ℤ A := A.hV2
  have hker : rationalIntegerLattice ≤ LinearMap.ker k.hom.toLinearMap := by
    rintro x ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    have hz := congrArg
      (fun f : Rep.trivial ℤ G ℤ ⟶ A => f.hom z) hk
    change k.hom (z : ℚ) = 0 at hz
    exact hz
  exact Rep.ofHom ⟨rationalIntegerLattice.liftQ k.hom.toLinearMap hker, by
    intro g
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
        change k.hom x = A.ρ g (k.hom x)
        simpa using Rep.hom_comm_apply k g x⟩

omit [Fintype G] in
@[simp]
private theorem rational_integers_desc
    {A : Rep ℤ G} (k : Rep.trivial ℤ G ℚ ⟶ A)
    (hk : integerToRational G ≫ k = 0) :
    rationalIntegers G ≫ rationalQuotientDesc G k hk = k := by
  letI : Module ℤ A := A.hV2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The concrete quotient map `Q -> Q/Z` is a categorical cokernel in the
category of `G`-representations. -/
private noncomputable def rationalIntegersCokernel :
    IsColimit (CokernelCofork.ofπ (rationalIntegers G)
      (integerRationalSequence G).zero) :=
  CokernelCofork.IsColimit.ofπ' (rationalIntegers G)
    (integerRationalSequence G).zero
    (fun k hk => ⟨rationalQuotientDesc G k hk,
      rational_integers_desc G k hk⟩)

omit [Fintype G] in
/-- The coefficient sequence `0 -> Z -> Q -> Q/Z -> 0` is short exact. -/
theorem sequence_short_exact :
    (integerRationalSequence G).ShortExact where
  exact := (integerRationalSequence G).exact_of_g_is_cokernel
    (rationalIntegersCokernel G)
  mono_f := (Rep.mono_iff_injective _).2 <| by
    change Function.Injective integerRationalLinear
    exact Int.cast_injective
  epi_g := rational_integers_epi G

/-- The connecting morphism `H^1(G,Q/Z) -> H^2(G,Z)` is an isomorphism. -/
noncomputable def rationalIntegersIso :
    groupCohomology (Rep.trivial ℤ G (rationalModIntegers)) 1 ≅
      groupCohomology (Rep.trivial ℤ G ℤ) 2 :=
  dimensionShiftingIso (sequence_short_exact G)
    (fun n hn => cohomology_trivial_rat G n hn) 1 Nat.zero_lt_one

/-- **Lemma II.3.3(c).** Canonically,
`Hom(G,Q/Z) ≃ H^2(G,Z)`.  A homomorphism from the multiplicative group `G`
to an additive group is represented in Lean as a homomorphism from
`Additive G`. -/
noncomputable def integersIso2 :
    ModuleCat.of ℤ (Additive G →+ rationalModIntegers) ≅
      groupCohomology (Rep.trivial ℤ G ℤ) 2 :=
  (groupCohomology.H1IsoOfIsTrivial
    (Rep.trivial ℤ G (rationalModIntegers))).symm ≪≫
      rationalIntegersIso G

end

end Submission.CField.Shifting
