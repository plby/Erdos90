import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Chapter V, Section 4: ideles

The finite ideles are the restricted product of the multiplicative groups of
the nonarchimedean completions with respect to their unit subgroups.  The full
idele group is the product of this restricted product with the units of the
infinite adele ring.

Algebraically, this is the group of units of the adele ring.  Topologically it
must *not* be given the subspace topology inherited from the adele ring: the
idele topology is the restricted-product topology.  Accordingly,
`adeleUnitsEquiv` below is deliberately only a multiplicative equivalence, not
a homeomorphism.

The ideal map of Statement 4.1 and the discreteness, content, and ray-class
results in Statements 4.2--4.4 and Propositions 4.6--4.7 require additional
compatibility results for completed valuations and global weak approximation
which are not currently packaged for Mathlib's finite adeles.  The idele norm
is constructed separately in `IdeleNorm`.
-/

noncomputable section

namespace Towers.CField.Ideles

open Filter IsDedekindDomain NumberField
open scoped RestrictedProduct

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The subgroup of units in a nonarchimedean completion which are integral
together with their inverses. -/
abbrev IdeleUnitSubgroup (v : HeightOneSpectrum R) :
    Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

/-- The finite idele group, with its restricted-product topology. -/
def FiniteIdeles : Type _ :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v]

instance : CommGroup (FiniteIdeles R K) := inferInstanceAs <|
  CommGroup <|
    Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v]

instance : TopologicalSpace (FiniteIdeles R K) := inferInstanceAs <|
  TopologicalSpace <|
    Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v]

private theorem idele_unit_open (v : HeightOneSpectrum R) :
    IsOpen (IdeleUnitSubgroup R K v : Set (v.adicCompletion K)ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  exact Valued.isOpen_valuationSubring _

instance : IsTopologicalGroup (FiniteIdeles R K) := by
  letI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (IdeleUnitSubgroup R K v : Set (v.adicCompletion K)ˣ)) :=
    ⟨idele_unit_open R K⟩
  change IsTopologicalGroup <|
    Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v]
  exact RestrictedProduct.isTopologicalGroup
    (fun v : HeightOneSpectrum R ↦ (v.adicCompletion K)ˣ)

/-- The idele group, with the product of the infinite-place unit topology and
the finite restricted-product topology. -/
def IdeleGroup : Type _ := (InfiniteAdeleRing K)ˣ × FiniteIdeles R K

instance : CommGroup (IdeleGroup R K) := inferInstanceAs <|
  CommGroup ((InfiniteAdeleRing K)ˣ × FiniteIdeles R K)

instance : TopologicalSpace (IdeleGroup R K) := inferInstanceAs <|
  TopologicalSpace ((InfiniteAdeleRing K)ˣ × FiniteIdeles R K)

instance : IsTopologicalGroup (IdeleGroup R K) := inferInstanceAs <|
  IsTopologicalGroup ((InfiniteAdeleRing K)ˣ × FiniteIdeles R K)

/-- The units of the finite adele ring are algebraically the finite ideles.
The codomain carries the restricted-product topology. -/
def finiteAdeleUnits : (FiniteAdeleRing R K)ˣ ≃* FiniteIdeles R K :=
  RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)

/-- Algebraically, ideles are the units of the adele ring.  This is not a
homeomorphism for the topology induced on the source from the adele ring. -/
def adeleUnitsEquiv : (AdeleRing R K)ˣ ≃* IdeleGroup R K :=
  (MulEquiv.prodUnits :
      (InfiniteAdeleRing K × FiniteAdeleRing R K)ˣ ≃*
        (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing R K)ˣ).trans
    ((MulEquiv.refl (InfiniteAdeleRing K)ˣ).prodCongr
      (finiteAdeleUnits R K))

/-- **Statement V.4.2, algebraic part.** The diagonal homomorphism from
`K×` to the idele group. -/
def principalIdele : Kˣ →* IdeleGroup R K :=
  (adeleUnitsEquiv R K).toMonoidHom.comp <|
    Units.map (algebraMap K (AdeleRing R K))

/-- The diagonal map into the ideles is injective for a number field.  The
book's further assertion that its image is discrete is not yet available. -/
theorem principalIdele_injective [NumberField K] :
    Function.Injective (principalIdele R K) := by
  have hmap : Function.Injective
      (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom) := by
    intro x y hxy
    apply Units.ext
    exact AdeleRing.algebraMap_injective R K (congrArg Units.val hxy)
  exact (adeleUnitsEquiv R K).injective.comp hmap

/-- The subgroup of principal ideles. -/
def principalIdeles : Subgroup (IdeleGroup R K) := (principalIdele R K).range

/-- The idele class group `C_K = ℐ_K / K×`. -/
abbrev IdeleClassGroup :=
  HasQuotient.Quotient (IdeleGroup R K) (principalIdeles R K)

set_option maxHeartbeats 800000 in
-- The dependent restricted-product expression needs extra elaboration time.
/-- **Statement V.4.3, finite-place part.** Put a local unit in one finite
coordinate and `1` in every other finite coordinate. -/
noncomputable def finiteLocalEmbedding (v : HeightOneSpectrum R) :
    (v.adicCompletion K)ˣ →* FiniteIdeles R K := by
  classical
  exact
    { toFun := RestrictedProduct.mulSingle
        (IdeleUnitSubgroup R K) v
      map_one' := RestrictedProduct.mulSingle_one (IdeleUnitSubgroup R K) v
      map_mul' := fun x y ↦ RestrictedProduct.mulSingle_mul
        (IdeleUnitSubgroup R K) v x y }

set_option maxHeartbeats 800000 in
-- Unfolding the dependent restricted product needs extra elaboration time.
/-- The one-coordinate finite local embedding is injective. -/
theorem local_embedding_injective (v : HeightOneSpectrum R) :
    Function.Injective (finiteLocalEmbedding R K v) := by
  classical
  change Function.Injective <|
    RestrictedProduct.mulSingle
      (IdeleUnitSubgroup R K) v
  exact RestrictedProduct.mulSingle_injective
    (IdeleUnitSubgroup R K) v

/-- The finite-place embedding into the full idele group. -/
def finitePlaceEmbedding (v : HeightOneSpectrum R) :
    (v.adicCompletion K)ˣ →* IdeleGroup R K where
  toFun x := (1, finiteLocalEmbedding R K v x)
  map_one' := by
    apply Prod.ext
    · rfl
    · exact map_one (finiteLocalEmbedding R K v)
  map_mul' x y := by
    apply Prod.ext
    · change (1 : (InfiniteAdeleRing K)ˣ) = 1 * 1
      simp
    · exact map_mul (finiteLocalEmbedding R K v) x y

/-- The finite-place embedding into the full idele group is injective. -/
theorem place_embedding_injective (v : HeightOneSpectrum R) :
    Function.Injective (finitePlaceEmbedding R K v) := by
  intro x y hxy
  apply local_embedding_injective R K v
  exact congrArg Prod.snd hxy

/-- Put an infinite local unit in one coordinate of the infinite adele ring
and `1` in every other infinite coordinate. -/
noncomputable def infiniteLocalEmbedding (v : InfinitePlace K) :
    v.Completionˣ →* (InfiniteAdeleRing K)ˣ := by
  classical
  let single : v.Completionˣ →* ((w : InfinitePlace K) → w.Completionˣ) :=
    MonoidHom.mulSingle (fun w : InfinitePlace K ↦ w.Completionˣ) v
  exact MulEquiv.piUnits.symm.toMonoidHom.comp single

/-- **Statement V.4.3, infinite-place part.** The one-coordinate embedding
of an infinite completion into the full idele group. -/
def infinitePlaceEmbedding (v : InfinitePlace K) :
    v.Completionˣ →* IdeleGroup R K where
  toFun x := (infiniteLocalEmbedding K v x, 1)
  map_one' := by
    apply Prod.ext
    · exact map_one (infiniteLocalEmbedding K v)
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · exact map_mul (infiniteLocalEmbedding K v) x y
    · change (1 : FiniteIdeles R K) = 1 * 1
      simp

/-- The infinite-place embedding into the idele group is injective. -/
theorem infinite_embedding_injective (v : InfinitePlace K) :
    Function.Injective (infinitePlaceEmbedding R K v) := by
  classical
  intro x y hxy
  have hfirst : infiniteLocalEmbedding K v x = infiniteLocalEmbedding K v y :=
    congrArg Prod.fst hxy
  change MulEquiv.piUnits.symm
      (Pi.mulSingle v x : (w : InfinitePlace K) → w.Completionˣ) =
    MulEquiv.piUnits.symm
      (Pi.mulSingle v y : (w : InfinitePlace K) → w.Completionˣ) at hfirst
  exact Pi.mulSingle_injective v (MulEquiv.piUnits.symm.injective hfirst)

end Towers.CField.Ideles
