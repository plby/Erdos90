import Towers.ClassField.LubinTate.RootField
import Towers.ClassField.LubinTate.RelativeAdicModule
import Towers.ClassField.LocalBrauer.SpectralIntegerClosure
import Towers.ClassField.LocalBrauer.LocalField
import Towers.NumberTheory.Locals.CompleteDVRHenselian
import Mathlib.FieldTheory.Galois.Basic

/-!
# A distinguished Lubin--Tate root as an adic torsion point

The root field and the valuation ring containing its distinguished root have
different universal properties.  In particular, the root field should not be
mapped into a valuation ring in which the root is a nonunit.  This file uses a
common ambient ring instead: the valuation ring and the root field both embed
there, and the two coefficient maps and distinguished points are required to
agree.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups
open scoped NormedField

universe u v w z

namespace LTDatum

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-- A relative Lubin--Tate point with exact annihilator
`(pi^(n+1))` is a root of the reduced level polynomial.  The proof is the
factorization of the full iterate into the preceding iterate and the reduced
iterate, together with the fact that exact level excludes the first factor. -/
theorem eval₂_reducedLubinTateIterate_eq_zero_of_torsionOf_eq
    (D : LTDatum A)
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (z : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hz : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) z =
      Ideal.span {D.pi ^ (n + 1)}) :
    Polynomial.eval₂ rho
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho) z : B)
        (reducedLubinIterate D.f n) = 0 := by
  let M := RelativeLubinPoints hI rho D.pi
    D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
    (D.f : PowerSeries A) D.lubin_tate_card
  let zB : B :=
    FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
        D.lubin_tate_card).map rho) z
  have hlevelSmul : D.pi ^ (n + 1) • z = 0 := by
    apply (Ideal.mem_torsionOf_iff z (D.pi ^ (n + 1))).mp
    rw [hz]
    exact Ideal.mem_span_singleton_self _
  have hlevel :
      PowerSeries.eval₂ (RingHom.id B) zB
        (substitutionIterate
          (PowerSeries.map rho (D.f : PowerSeries A)) (n + 1)) = 0 := by
    apply (relative_substitution_iterate
      hI rho D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
      hfield (D.f : PowerSeries A) D.lubin_tate_card
      (n + 1) z).1
    exact mem_torsionKernel.mpr hlevelSmul
  have hprimitive :
      PowerSeries.eval₂ (RingHom.id B) zB
        (substitutionIterate
          (PowerSeries.map rho (D.f : PowerSeries A)) n) ≠ 0 := by
    intro heval
    have hsmul : D.pi ^ n • z = 0 :=
      mem_torsionKernel.mp
        ((relative_substitution_iterate
          hI rho D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card n z).2 heval)
    have hmem : D.pi ^ n ∈ Ideal.span {D.pi ^ (n + 1)} := by
      rw [← hz]
      exact (Ideal.mem_torsionOf_iff z (D.pi ^ n)).mpr hsmul
    have hdiv : D.pi ^ (n + 1) ∣ D.pi ^ n :=
      Ideal.mem_span_singleton.mp hmem
    have : n + 1 ≤ n :=
      (pow_dvd_pow_iff D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit).mp hdiv
    omega
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  rw [eval₂_substitutionIterate_map_polynomial rho D.f hf0
    (n + 1) zB] at hlevel
  rw [eval₂_substitutionIterate_map_polynomial rho D.f hf0 n zB]
    at hprimitive
  have hmul : Polynomial.X * D.f.divX = D.f := by
    simpa only [hf0, Polynomial.C_0, add_zero] using
      Polynomial.X_mul_divX_add D.f
  have hfactor :
      D.f.comp (D.f.comp^[n] Polynomial.X) =
        (D.f.comp^[n] Polynomial.X) *
          reducedLubinIterate D.f n := by
    rw [reducedLubinIterate]
    calc
      D.f.comp (D.f.comp^[n] Polynomial.X) =
          (Polynomial.X * D.f.divX).comp
            (D.f.comp^[n] Polynomial.X) := by rw [hmul]
      _ = (D.f.comp^[n] Polynomial.X) *
          D.f.divX.comp (D.f.comp^[n] Polynomial.X) := by
        rw [Polynomial.mul_comp, Polynomial.X_comp]
  rw [Function.iterate_succ_apply', hfactor, Polynomial.eval₂_mul] at hlevel
  exact (mul_eq_zero.mp hlevel).resolve_left hprimitive

/-- If a relative adic Lubin--Tate point becomes the distinguished root in a
common ambient ring, then it has exact annihilator `(pi^(n+1))`.  This is the
algebraic bridge from the concrete `AdjoinRoot` construction to the quotient
unit action in Theorem I.3.6(b). -/
theorem torsion_relative_point
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    {L : Type z} [CommRing L] [Nontrivial L]
    (j : B →+* L) (hj : Function.Injective j)
    (ι : D.RootField K n →+* L)
    (hcoeff : j.comp rho =
      ι.comp ((algebraMap K (D.RootField K n)).comp (algebraMap A K)))
    (hy : j
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho) y : B) =
      ι (D.root K n)) :
    Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)} := by
  let yB : B :=
    FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
        D.lubin_tate_card).map rho) y
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  have htransport (m : ℕ) :
      j (PowerSeries.eval₂ (RingHom.id B) yB
          (substitutionIterate
            (PowerSeries.map rho (D.f : PowerSeries A)) m)) =
        ι (Polynomial.aeval (D.root K n)
          ((D.f.comp^[m] Polynomial.X).map (algebraMap A K))) := by
    calc
      j (PowerSeries.eval₂ (RingHom.id B) yB
          (substitutionIterate
            (PowerSeries.map rho (D.f : PowerSeries A)) m)) =
          j (Polynomial.eval₂ rho yB
            (D.f.comp^[m] Polynomial.X)) := by
        rw [eval₂_substitutionIterate_map_polynomial rho D.f hf0 m yB]
      _ = Polynomial.eval₂ (j.comp rho) (j yB)
          (D.f.comp^[m] Polynomial.X) :=
        Polynomial.hom_eval₂ (D.f.comp^[m] Polynomial.X) rho j yB
      _ = Polynomial.eval₂
          (ι.comp ((algebraMap K (D.RootField K n)).comp
            (algebraMap A K))) (ι (D.root K n))
          (D.f.comp^[m] Polynomial.X) := by
        rw [hcoeff, show j yB = ι (D.root K n) from hy]
      _ = ι (Polynomial.eval₂
          ((algebraMap K (D.RootField K n)).comp (algebraMap A K))
          (D.root K n) (D.f.comp^[m] Polynomial.X)) := by
        exact (Polynomial.hom_eval₂ (D.f.comp^[m] Polynomial.X)
          ((algebraMap K (D.RootField K n)).comp (algebraMap A K))
          ι (D.root K n)).symm
      _ = ι (Polynomial.aeval (D.root K n)
          ((D.f.comp^[m] Polynomial.X).map (algebraMap A K))) := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hlevel :
      PowerSeries.eval₂ (RingHom.id B) yB
        (substitutionIterate
          (PowerSeries.map rho (D.f : PowerSeries A)) (n + 1)) = 0 := by
    apply hj
    rw [map_zero, htransport]
    simpa [torsionPolynomial] using
      congrArg ι (D.aeval_torsion_root K n)
  have hprimitive :
      PowerSeries.eval₂ (RingHom.id B) yB
        (substitutionIterate
          (PowerSeries.map rho (D.f : PowerSeries A)) n) ≠ 0 := by
    intro hzero
    have hjzero := congrArg j hzero
    rw [htransport, map_zero] at hjzero
    have hrootzero : Polynomial.aeval (D.root K n)
        ((D.f.comp^[n] Polynomial.X).map (algebraMap A K)) = 0 := by
      exact ι.injective (hjzero.trans (map_zero ι).symm)
    exact D.aeval_previous_iterate K n hrootzero
  exact torsion_exact_level hI rho D.pi
    D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
    D.pi_irreducible hfield (D.f : PowerSeries A)
    D.lubin_tate_card n y hlevel hprimitive

/-- The units of `A / (pi^(n+1))` act faithfully on any relative adic point
identified with the distinguished root in a common ambient ring. -/
noncomputable def relativeOrbitEmbedding
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    {L : Type z} [CommRing L] [Nontrivial L]
    (j : B →+* L) (hj : Function.Injective j)
    (ι : D.RootField K n →+* L)
    (hcoeff : j.comp rho =
      ι.comp ((algebraMap K (D.RootField K n)).comp (algebraMap A K)))
    (hy : j
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho) y : B) =
      ι (D.root K n)) :
    (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ↪
      RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card :=
  orbitEmbeddingTorsion y
    (D.torsion_relative_point K hI rho hfield
      n y j hj ι hcoeff hy)

/-- An exact relative root gives a degree-sized family of distinct roots of
the reduced level polynomial after embedding the evaluation ring in a field.
This is the root-orbit half of Theorem I.3.6(a)--(b). -/
theorem relative_set_embedding
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hy : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)})
    {L : Type z} [Field L] [Algebra K L]
    (j : B →+* L) (hj : Function.Injective j)
    (hcoeff : j.comp rho =
      (algebraMap K L).comp (algebraMap A K)) :
    ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ↪
        (D.reducedPolynomial K n).rootSet L,
      ∀ u, (orbit u : L) =
        j (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho)
          (orbitEmbeddingTorsion y hy u) : B) := by
  classical
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let pointEmbedding :
      RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card ↪ L :=
    { toFun := fun z ↦ j (FGLaw.APts.toIdeal hI
          (FGLaw.map rho F) z : B)
      inj' := by
        intro z z' hzz'
        apply FGLaw.APts.ext hI (FGLaw.map rho F)
        apply Subtype.ext
        exact hj hzz' }
  let moduleOrbit := orbitEmbeddingTorsion y hy
  let fieldOrbit := moduleOrbit.trans pointEmbedding
  have hroot (u : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
      Polynomial.aeval (fieldOrbit u) (D.reducedPolynomial K n) = 0 := by
    let z := moduleOrbit u
    have hz : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) z =
        Ideal.span {D.pi ^ (n + 1)} :=
      torsion_orbit_embedding y hy u
    have hzroot :=
      D.eval₂_reducedLubinTateIterate_eq_zero_of_torsionOf_eq
        hI rho hfield n z hz
    change Polynomial.aeval
      (j (FGLaw.APts.toIdeal hI
        (FGLaw.map rho F) z : B))
        (D.reducedPolynomial K n) = 0
    calc
      Polynomial.aeval
          (j (FGLaw.APts.toIdeal hI
            (FGLaw.map rho F) z : B))
          (D.reducedPolynomial K n) =
        Polynomial.eval₂ ((algebraMap K L).comp (algebraMap A K))
          (j (FGLaw.APts.toIdeal hI
            (FGLaw.map rho F) z : B))
          (reducedLubinIterate D.f n) := by
            rw [Polynomial.aeval_def, reducedPolynomial,
              Polynomial.eval₂_map]
      _ = Polynomial.eval₂ (j.comp rho)
          (j (FGLaw.APts.toIdeal hI
            (FGLaw.map rho F) z : B))
          (reducedLubinIterate D.f n) := by rw [hcoeff]
      _ = j (Polynomial.eval₂ rho
          (FGLaw.APts.toIdeal hI
            (FGLaw.map rho F) z : B)
          (reducedLubinIterate D.f n)) :=
        (Polynomial.hom_eval₂ (reducedLubinIterate D.f n) rho j
          (FGLaw.APts.toIdeal hI
            (FGLaw.map rho F) z : B)).symm
      _ = 0 := by rw [hzroot, map_zero]
  let rootOrbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ↪
      (D.reducedPolynomial K n).rootSet L :=
    { toFun := fun u ↦ ⟨fieldOrbit u,
        (D.reducedPolynomial_monic K n).mem_rootSet.mpr (hroot u)⟩
      inj' := fun u v huv ↦ fieldOrbit.injective (Subtype.ext_iff.mp huv) }
  exact ⟨rootOrbit, fun _ ↦ rfl⟩

/-- A relative exact-level orbit with the expected coefficient embedding
forces the reduced Lubin--Tate polynomial to split. -/
theorem reduced_splits_point
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hy : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)})
    {L : Type z} [Field L] [Algebra K L]
    (j : B →+* L) (hj : Function.Injective j)
    (hcoeff : j.comp rho =
      (algebraMap K L).comp (algebraMap A K)) :
    (D.reducedPolynomial K n).map (algebraMap K L) |>.Splits := by
  classical
  obtain ⟨orbit, -⟩ :=
    D.relative_set_embedding K hI rho hfield
      n y hy j hj hcoeff
  have horbitCard :
      Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≤
        Nat.card ((D.reducedPolynomial K n).rootSet L) :=
    Nat.card_le_card_of_injective orbit orbit.injective
  have hunitDegree :
      Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
        (D.reducedPolynomial K n).natDegree := by
    rw [D.card_quotientUnits n, D.reduced_nat_degree K n]
  have hrootLower :
      (D.reducedPolynomial K n).natDegree ≤
        Set.ncard ((D.reducedPolynomial K n).rootSet L) := by
    simpa only [hunitDegree, Nat.card_coe_set_eq] using horbitCard
  have hrootUpper :
      Set.ncard ((D.reducedPolynomial K n).rootSet L) ≤
        (D.reducedPolynomial K n).natDegree :=
    (D.reducedPolynomial K n).ncard_rootSet_le L
  have hrootCard :
      Set.ncard ((D.reducedPolynomial K n).rootSet L) =
        (D.reducedPolynomial K n).natDegree :=
    Nat.le_antisymm hrootUpper hrootLower
  have hrootsLower :
      (D.reducedPolynomial K n).natDegree ≤
        ((D.reducedPolynomial K n).map (algebraMap K L)).roots.card := by
    calc
      (D.reducedPolynomial K n).natDegree =
          Set.ncard ((D.reducedPolynomial K n).rootSet L) := hrootCard.symm
      _ = ((D.reducedPolynomial K n).map
          (algebraMap K L)).roots.toFinset.card := by
        simp only [Polynomial.rootSet, Polynomial.aroots_def,
          Set.ncard_coe_finset]
      _ ≤ ((D.reducedPolynomial K n).map
          (algebraMap K L)).roots.card :=
        Multiset.toFinset_card_le _
  rw [Polynomial.splits_iff_card_roots]
  have hdegreeMap :
      ((D.reducedPolynomial K n).map (algebraMap K L)).natDegree =
        (D.reducedPolynomial K n).natDegree :=
    (D.reducedPolynomial_monic K n).natDegree_map _
  rw [hdegreeMap]
  exact Nat.le_antisymm
    (Polynomial.card_roots_map_le_natDegree (D.reducedPolynomial K n))
    hrootsLower

/-- The same degree-sized unit orbit shows that the reduced polynomial has no
repeated roots.  This avoids imposing a characteristic-zero hypothesis on the
local field. -/
theorem reduced_separable_point
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hy : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)})
    {L : Type z} [Field L] [Algebra K L]
    (j : B →+* L) (hj : Function.Injective j)
    (hcoeff : j.comp rho =
      (algebraMap K L).comp (algebraMap A K)) :
    (D.reducedPolynomial K n).Separable := by
  classical
  have hsplits := D.reduced_splits_point K
    hI rho hfield n y hy j hj hcoeff
  obtain ⟨orbit, -⟩ :=
    D.relative_set_embedding K hI rho hfield
      n y hy j hj hcoeff
  have horbitCard :
      Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≤
        Nat.card ((D.reducedPolynomial K n).rootSet L) :=
    Nat.card_le_card_of_injective orbit orbit.injective
  have hunitDegree :
      Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
        (D.reducedPolynomial K n).natDegree := by
    rw [D.card_quotientUnits n, D.reduced_nat_degree K n]
  have hrootLower :
      (D.reducedPolynomial K n).natDegree ≤
        Set.ncard ((D.reducedPolynomial K n).rootSet L) := by
    simpa only [hunitDegree, Nat.card_coe_set_eq] using horbitCard
  have hrootUpper :
      Set.ncard ((D.reducedPolynomial K n).rootSet L) ≤
        (D.reducedPolynomial K n).natDegree :=
    (D.reducedPolynomial K n).ncard_rootSet_le L
  have hrootCard :
      Set.ncard ((D.reducedPolynomial K n).rootSet L) =
        (D.reducedPolynomial K n).natDegree :=
    Nat.le_antisymm hrootUpper hrootLower
  have hrootFintypeCard :
      Fintype.card ((D.reducedPolynomial K n).rootSet L) =
        (D.reducedPolynomial K n).natDegree := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using hrootCard
  exact (Polynomial.card_rootSet_eq_natDegree_iff_of_splits
    (D.reducedPolynomial_monic K n).ne_zero hsplits).mp hrootFintypeCard

/-- The quotient-unit orbit of an exact relative point exhausts the roots of
the reduced level polynomial.  This is an equivalence of finite types; the
later multiplicative Galois-action statement requires proving separately that
the corresponding field automorphisms respect the unit product. -/
theorem relative_orbit_set
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hy : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)})
    {L : Type z} [Field L] [Algebra K L]
    (j : B →+* L) (hj : Function.Injective j)
    (hcoeff : j.comp rho =
      (algebraMap K L).comp (algebraMap A K)) :
    ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃
        (D.reducedPolynomial K n).rootSet L,
      ∀ u, (orbit u : L) =
        j (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho)
          (orbitEmbeddingTorsion y hy u) : B) := by
  classical
  letI : Finite (A ⧸ Ideal.span {D.pi ^ (n + 1)}) := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.finite_quotient_pow
      (IsNoetherian.noetherian (Ideal.span {D.pi})) (n + 1)
  letI : Fintype (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ :=
    Fintype.ofFinite _
  obtain ⟨orbit, horbit⟩ :=
    D.relative_set_embedding K hI rho hfield
      n y hy j hj hcoeff
  have hsplits := D.reduced_splits_point K
    hI rho hfield n y hy j hj hcoeff
  have hseparable := D.reduced_separable_point K
    hI rho hfield n y hy j hj hcoeff
  have hrootCard :
      Fintype.card ((D.reducedPolynomial K n).rootSet L) =
        (D.reducedPolynomial K n).natDegree :=
    (Polynomial.card_rootSet_eq_natDegree_iff_of_splits
      (D.reducedPolynomial_monic K n).ne_zero hsplits).mpr hseparable
  have hcard :
      Fintype.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
        Fintype.card ((D.reducedPolynomial K n).rootSet L) := by
    calc
      Fintype.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
          Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ :=
        Nat.card_eq_fintype_card.symm
      _ = (D.q - 1) * D.q ^ n := D.card_quotientUnits n
      _ = (D.reducedPolynomial K n).natDegree :=
        (D.reduced_nat_degree K n).symm
      _ = Fintype.card ((D.reducedPolynomial K n).rootSet L) :=
        hrootCard.symm
  have hbijective : Function.Bijective orbit :=
    (Fintype.bijective_iff_injective_and_card orbit).mpr
      ⟨orbit.injective, hcard⟩
  exact ⟨Equiv.ofBijective orbit hbijective, horbit⟩

/-- An exact relative Lubin--Tate point gives an explicit bijection from
quotient units to automorphisms of the distinguished root field: the
automorphism corresponding to `u` sends the distinguished root to the
formal-module point `u • y`.  This intermediate result is intentionally an
`Equiv`; `LubinTateRootFieldGaloisAction` upgrades it to the `MulEquiv` of
Theorem I.3.6(b). -/
theorem relative_orbit_aut
    (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type w} [CommRing B] [IsDomain B]
    [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hy : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) y =
      Ideal.span {D.pi ^ (n + 1)})
    (j : B →+* D.RootField K n) (hj : Function.Injective j)
    (hcoeff : j.comp rho =
      (algebraMap K (D.RootField K n)).comp (algebraMap A K)) :
    ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃
        (D.RootField K n ≃ₐ[K] D.RootField K n),
      ∀ u, orbit u (D.root K n) =
        j (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho)
          (orbitEmbeddingTorsion y hy u) : B) := by
  obtain ⟨rootOrbit, hrootOrbit⟩ :=
    D.relative_orbit_set K hI rho hfield
      n y hy j hj hcoeff
  let autOrbit := rootOrbit.trans (D.rootSetAut K n)
  refine ⟨autOrbit, fun u ↦ ?_⟩
  calc
    autOrbit u (D.root K n) = (rootOrbit u : D.RootField K n) := by
      exact D.root_set_aut K n (rootOrbit u)
    _ = j (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
            D.lubin_tate_card).map rho)
          (orbitEmbeddingTorsion y hy u) : B) :=
      hrootOrbit u

set_option maxHeartbeats 2000000 in
-- The spectral local-field and relative formal-group instance telescope is deep.
-- The spectral local-field and relative formal-group instance telescope is deep.
/-- For the spectral norm on the concrete distinguished root field, the root
lies in the maximal ideal of the spectral integer ring and therefore defines
a relative adic Lubin--Tate point with exact annihilator `(pi^(n+1))`. -/
theorem spectral_point_maps
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    [Fintype
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi})]
    (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := K))
    let E := D.RootField K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := LBrauer.FLExt.valuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      LBrauer.FLExt.nonarchimedeanLocalField K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : CompleteSpace E := spectralNorm.completeSpace K E
    letI : ProperSpace E := FiniteDimensional.proper K E
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := E)) :=
      LBrauer.spectralValuationExtension K E
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
      Towers.NumberTheory.Milne.valued_integer_adic E
    let rho : A →+* B := algebraMap A B
    ∃ y : RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card,
      Ideal.torsionOf A
          (RelativeLubinPoints hI rho D.pi
            D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
            (D.f : PowerSeries A) D.lubin_tate_card) y =
        Ideal.span {D.pi ^ (n + 1)} ∧
      B.subtype (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map rho) y) =
        D.root K n := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  let E := D.RootField K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := LBrauer.FLExt.valuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
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
    Towers.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  have hpi : (NormedField.valuation (K := K)) (D.pi : K) < 1 := by
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      D.pi_irreducible.not_isUnit
  have hx : Polynomial.aeval (D.root K n)
      (D.f.comp^[n + 1] Polynomial.X) = 0 := by
    simpa [torsionPolynomial, Polynomial.aeval_def,
      Polynomial.eval₂_map, IsScalarTower.algebraMap_apply] using
      D.aeval_torsion_root K n
  have hroot : (NormedField.valuation (K := E)) (D.root K n) < 1 := by
    exact valuation_lubin_iterate
      (NormedField.valuation (K := K)) (NormedField.valuation (K := E))
      D.pi D.lubinTateSeries D.f_monic D.f_natDegree
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one D.one_lt_q)) hpi
      (n + 1) hx
  let alpha : B := ⟨D.root K n, hroot.le⟩
  have halpha : alpha ∈ IsLocalRing.maximalIdeal B := by
    exact (NormedField.valuation (K := E)).mem_maximalIdeal_iff.mpr hroot
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let y : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card :=
    FGLaw.APts.ofIdeal hI (F.map rho) ⟨alpha, halpha⟩
  refine ⟨y, ?_, rfl⟩
  apply D.torsion_relative_point K hI rho
    hfield n y B.subtype B.subtype_injective
    (RingHom.id E)
  · ext a
    rfl
  · rfl

set_option maxHeartbeats 2000000 in
-- The spectral local-field and relative formal-group instance telescope is deep.
/-- The reduced Lubin--Tate polynomial splits in its distinguished root field
and is separable.  Thus the `AdjoinRoot` construction is already the full
splitting field, as asserted in Theorem I.3.6(a). -/
theorem field_splits_separable
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    ((D.reducedPolynomial K n).map
        (algebraMap K (D.RootField K n))).Splits ∧
      (D.reducedPolynomial K n).Separable := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let E := D.RootField K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := LBrauer.FLExt.valuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
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
    Towers.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  obtain ⟨y, hy, -⟩ :=
    D.spectral_point_maps K hfield n
  have hcoeff : B.subtype.comp rho =
      (algebraMap K E).comp (algebraMap A K) := by
    ext a
    rfl
  exact ⟨D.reduced_splits_point K
      hI rho hfield n y hy B.subtype B.subtype_injective hcoeff,
    D.reduced_separable_point K
      hI rho hfield n y hy B.subtype B.subtype_injective hcoeff⟩

/-- The distinguished Lubin--Tate root field is Galois over the base local
field.  The proof identifies it as the splitting field of its separable
reduced level polynomial. -/
theorem root_field_galois
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) : IsGalois K (D.RootField K n) := by
  let p := D.reducedPolynomial K n
  let E := D.RootField K n
  have hsplits : (p.map (algebraMap K E)).Splits :=
    (D.field_splits_separable K hfield n).1
  have hseparable : p.Separable :=
    (D.field_splits_separable K hfield n).2
  have hroot : D.root K n ∈ p.rootSet E := by
    exact (D.reducedPolynomial_monic K n).mem_rootSet.mpr
      (D.aeval_root K n)
  have hadjoin : IntermediateField.adjoin K (p.rootSet E) = ⊤ := by
    apply top_unique
    rw [← D.adjoin_root_top K n]
    exact IntermediateField.adjoin.mono K {D.root K n} (p.rootSet E)
      (Set.singleton_subset_iff.mpr hroot)
  letI : p.IsSplittingField K E :=
    isSplittingField_iff_intermediateField.mpr
      ⟨hsplits, hadjoin⟩
  exact IsGalois.of_separable_splitting_field hseparable

end LTDatum

end

end Towers.CField.LTate
