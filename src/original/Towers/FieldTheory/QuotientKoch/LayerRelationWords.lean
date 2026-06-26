import Mathlib.Data.Set.Finite.List
import Towers.FieldTheory.QuotientKoch.LayerWordImages


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace IRScaffo

universe u w

variable
    {F G H : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [Group H]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {N : OpenNormalSubgroup F}

namespace SConjug

/--
Map a signed conjugate through a group homomorphism by mapping only its stored
conjugator and keeping its relator index and sign.
-/
def map
    (φ : F →* H)
    (letter : SConjug ι F) :
    SConjug ι H where
  conjugator := φ letter.conjugator
  relatorIndex := letter.relatorIndex
  isInverse := letter.isInverse

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Evaluation of a signed conjugate commutes with mapping its conjugator through a
group homomorphism.
-/
lemma value_map
    (φ : F →* H)
    (relator : ι → F)
    (letter : SConjug ι F) :
    (letter.map φ).value (fun i => φ (relator i)) =
      φ (letter.value relator) := by
  cases letter with
  | mk conjugator relatorIndex isInverse =>
      cases isInverse <;>
        simp [map, value, mul_assoc]

/--
Choose one lift of a signed conjugate along a surjective group homomorphism by
choosing a lift of its stored conjugator.
-/
def liftAlongSurjective
    (φ : F →* H)
    (hφ : Function.Surjective φ)
    (letter : SConjug ι H) :
    SConjug ι F where
  conjugator := Classical.choose (hφ letter.conjugator)
  relatorIndex := letter.relatorIndex
  isInverse := letter.isInverse

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Mapping the chosen lift of one signed conjugate recovers the original signed
conjugate.
-/
lemma lift_along_surjective
    (φ : F →* H)
    (hφ : Function.Surjective φ)
    (letter : SConjug ι H) :
    (letter.liftAlongSurjective φ hφ).map φ = letter := by
  cases letter with
  | mk conjugator relatorIndex isInverse =>
      simp [liftAlongSurjective, map, Classical.choose_spec (hφ conjugator)]

/--
Signed conjugates are equivalent to their three pieces of stored data.  This
makes finite signed-conjugate alphabets available in finite quotient layers.
-/
def equivProd
    (ι : Type w)
    (F : Type u)
    [Group F] :
    SConjug ι F ≃ F × ι × Bool where
  toFun := fun letter => (letter.conjugator, letter.relatorIndex, letter.isInverse)
  invFun := fun data =>
    { conjugator := data.1
      relatorIndex := data.2.1
      isInverse := data.2.2 }
  left_inv := by
    rintro ⟨conjugator, relatorIndex, isInverse⟩
    rfl
  right_inv := by
    rintro ⟨conjugator, relatorIndex, isInverse⟩
    rfl

instance finiteSignedConjugate
    [Finite ι]
    [Finite F] :
    Finite (SConjug ι F) :=
  Finite.of_equiv (F × ι × Bool) (equivProd ι F).symm

end SConjug

namespace RWord

/--
Map every signed conjugate in an explicit relation word through one group
homomorphism.
-/
def map
    (φ : F →* H)
    (word : RWord ι F) :
    RWord ι H :=
  List.map (fun letter => SConjug.map φ letter) word

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Evaluation of an explicit relation word commutes with mapping all of its
signed conjugates through one group homomorphism.
-/
lemma value_map
    (φ : F →* H)
    (relator : ι → F)
    (word : RWord ι F) :
    (word.map φ).value (fun i => φ (relator i)) =
      φ (word.value relator) := by
  induction word with
  | nil =>
      simp [map]
  | cons letter word ih =>
      rw [map, List.map_cons, value_cons, SConjug.value_map]
      rw [show
        value (fun i => φ (relator i))
            (List.map (fun tailLetter => SConjug.map φ tailLetter) word) =
          φ (value relator word) by
        simpa only [map] using ih]
      rw [value_cons, map_mul]

/--
Choose one lift of every signed conjugate in an explicit relation word along a
surjective group homomorphism.
-/
def liftAlongSurjective
    (φ : F →* H)
    (hφ : Function.Surjective φ)
    (word : RWord ι H) :
    RWord ι F :=
  List.map (fun letter => SConjug.liftAlongSurjective φ hφ letter) word

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Mapping the chosen lift of an explicit relation word recovers the original
relation word.
-/
lemma lift_along_surjective
    (φ : F →* H)
    (hφ : Function.Surjective φ)
    (word : RWord ι H) :
    (word.liftAlongSurjective φ hφ).map φ = word := by
  induction word with
  | nil =>
      simp [liftAlongSurjective, map]
  | cons letter word ih =>
      change SConjug.map φ (SConjug.liftAlongSurjective φ hφ letter) ::
          RWord.map φ (RWord.liftAlongSurjective φ hφ word) =
        letter :: word
      rw [SConjug.lift_along_surjective, ih]

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
The chosen lift of a quotient-level relation word evaluates to an ambient word
whose image is the original quotient-level relation-word value.
-/
lemma value_along_surjective
    (φ : F →* H)
    (hφ : Function.Surjective φ)
    (relator : ι → F)
    (word : RWord ι H) :
    φ ((word.liftAlongSurjective φ hφ).value relator) =
      word.value (fun i => φ (relator i)) := by
  rw [← value_map]
  rw [lift_along_surjective]

/--
Relation words of bounded length over a finite signed-conjugate alphabet form
a finite search space.
-/
abbrev Bounded
    (ι : Type w)
    (F : Type u)
    [Group F]
    (bound : ℕ) :=
  { word : RWord ι F // word.length ≤ bound }

instance boundedFinite
    [Finite ι]
    [Finite F]
    (bound : ℕ) :
    Finite (Bounded ι F bound) := by
  letI : Fintype (Bounded ι F bound) :=
    (List.finite_length_le (SConjug ι F) bound).fintype
  infer_instance

end RWord

/--
The displayed relator family after passing to one open-normal finite layer.
-/
abbrev openLayerRelator
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    ι → ONCompar.OpenNormalLayer N :=
  fun i => ONCompar.openNormalLayer N (relator i)

/--
An explicit relation-word certificate for one candidate-kernel-image element
using a relation word entirely inside the finite quotient layer.
-/
structure IECert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (z : ONCompar.kernelImage q N) where
  word :
    RWord ι (ONCompar.OpenNormalLayer N)
  value_eq :
    word.value (openLayerRelator relator N) =
      z

namespace IECert

/--
Pushing an ambient candidate-kernel-image relation-word certificate into the
finite quotient layer gives a quotient-level relation-word certificate.
-/
def ofAmbient
    {z : ONCompar.kernelImage q N}
    (C : ERCert q relator N z) :
    IECert q relator N z where
  word := C.word.map (ONCompar.openNormalLayer N)
  value_eq := by
    rw [RWord.value_map]
    exact C.quotient_value_eq

/--
Lifting a quotient-level relation-word certificate along the finite-layer
quotient map gives an ambient candidate-kernel-image relation-word certificate.
-/
def toAmbient
    {z : ONCompar.kernelImage q N}
    (C : IECert q relator N z) :
    ERCert q relator N z where
  word := C.word.liftAlongSurjective
    (ONCompar.openNormalLayer N)
    (QuotientGroup.mk'_surjective (N : Subgroup F))
  quotient_value_eq := by
    exact (RWord.value_along_surjective
      (ONCompar.openNormalLayer N)
      (QuotientGroup.mk'_surjective (N : Subgroup F))
      relator
      C.word).trans C.value_eq

omit [IsTopologicalGroup F] in
/--
Pushing an ambient relation word into one finite layer preserves its word
length.
-/
lemma ambient_word_length
    {z : ONCompar.kernelImage q N}
    (C : ERCert q relator N z) :
    (ofAmbient C).word.length = C.word.length := by
  simp [ofAmbient, RWord.map]

omit [IsTopologicalGroup F] in
/--
Lifting a quotient-level relation word from one finite layer preserves its word
length.
-/
lemma ambient_length
    {z : ONCompar.kernelImage q N}
    (C : IECert q relator N z) :
    (toAmbient C).word.length = C.word.length := by
  simp [toAmbient, RWord.liftAlongSurjective]

end IECert

/--
A quotient-level finite-layer relation-word table assigns one finite-layer
relation word to each element of the finite-layer candidate-kernel image.
-/
structure LICert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) where
  wordFor :
    ∀ z : ONCompar.kernelImage q N,
      IECert q relator N z

namespace LICert

/--
Push an ambient candidate-kernel-image relation-word table into one finite
quotient layer.
-/
def ofAmbient
    (C : KICert q relator N) :
    LICert q relator N where
  wordFor := fun z => IECert.ofAmbient (C.wordFor z)

/--
Lift a quotient-level candidate-kernel-image relation-word table back to the
ambient group.
-/
def toAmbient
    (C : LICert q relator N) :
    KICert q relator N where
  wordFor := fun z => (C.wordFor z).toAmbient

omit [IsTopologicalGroup F] in
/--
Ambient and quotient-level candidate-kernel-image relation-word tables are
equivalent formulations of the same finite-layer certificate problem.
-/
lemma nonempty_ambient
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Nonempty (LICert q relator N) ↔
      Nonempty (KICert q relator N) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toAmbient⟩
  · rintro ⟨C⟩
    exact ⟨ofAmbient C⟩

end LICert

/--
A bounded quotient-level finite-layer relation-word table records one complete
quotient-level table with a uniform relation-word length bound.
-/
structure BLCert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) where
  layerRelationCertificate :
    LICert q relator N
  wordLength_le :
    ∀ z : ONCompar.kernelImage q N,
      (layerRelationCertificate.wordFor z).word.length ≤ bound

namespace BLCert

/--
Push a bounded ambient finite-layer relation-word table into the finite quotient
layer without changing the word-length bound.
-/
def ofAmbient
    {bound : ℕ}
    (C : BKCert q relator N bound) :
    BLCert q relator N bound where
  layerRelationCertificate :=
    LICert.ofAmbient
      C.kernelRelationCertificate
  wordLength_le := by
    intro z
    change (IECert.ofAmbient
      (C.kernelRelationCertificate.wordFor z)).word.length ≤ bound
    rw [IECert.ambient_word_length]
    exact C.wordLength_le z

/--
Lift a bounded quotient-level finite-layer relation-word table to the ambient
group without changing the word-length bound.
-/
def toAmbient
    {bound : ℕ}
    (C : BLCert q relator N bound) :
    BKCert q relator N bound where
  kernelRelationCertificate :=
    C.layerRelationCertificate.toAmbient
  wordLength_le := by
    intro z
    change (IECert.toAmbient
      (C.layerRelationCertificate.wordFor z)).word.length ≤ bound
    rw [IECert.ambient_length]
    exact C.wordLength_le z

omit [IsTopologicalGroup F] in
/--
Bounded ambient and quotient-level candidate-kernel-image relation-word tables
are equivalent formulations of the same bounded finite-layer certificate
problem.
-/
lemma nonempty_ambient
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    Nonempty (BLCert q relator N bound) ↔
      Nonempty (BKCert q relator N bound) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toAmbient⟩
  · rintro ⟨C⟩
    exact ⟨ofAmbient C⟩

end BLCert

/--
A bounded quotient-level relation-word table with its correctness equations
forgotten.  For finite layers and finite relator index sets this is a finite
search space.
-/
abbrev BoundedLayerTable
    (q : F →* G)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :=
  ONCompar.kernelImage q N →
    RWord.Bounded ι (ONCompar.OpenNormalLayer N) bound

/--
A bounded quotient-level word table certifies the candidate-kernel image when
each stored quotient-layer relation word evaluates to its indexing
candidate-kernel-image element.
-/
def RelationTableCertifies
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    (table : BoundedLayerTable (ι := ι) q N bound) :
    Prop :=
  ∀ z : ONCompar.kernelImage q N,
    (table z).1.value (openLayerRelator relator N) = z

/--
Correctness of one bounded quotient-level word table is decidable once equality
in the finite quotient layer is decidable.
-/
def tableCertifiesDecidable
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    [Fintype (ONCompar.kernelImage q N)]
    [DecidableEq (ONCompar.kernelImage q N)]
    [DecidableEq (ONCompar.OpenNormalLayer N)]
    (table : BoundedLayerTable (ι := ι) q N bound) :
    Decidable (RelationTableCertifies q relator N bound table) := by
  unfold RelationTableCertifies
  letI : DecidablePred
      (fun z : ONCompar.kernelImage q N =>
        (table z).1.value (openLayerRelator relator N) = z) :=
    fun z => inferInstance
  exact Fintype.decidableForallFintype

omit [IsTopologicalGroup F] in
/--
Bounded quotient-level relation-word certificates are exactly certifying
bounded quotient-level relation-word tables.
-/
lemma nonempty_bounded_table
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    Nonempty (BLCert q relator N bound) ↔
      ∃ table : BoundedLayerTable (ι := ι) q N bound,
        RelationTableCertifies q relator N bound table := by
  constructor
  · rintro ⟨C⟩
    let table : BoundedLayerTable (ι := ι) q N bound :=
      fun z => ⟨(C.layerRelationCertificate.wordFor z).word,
        C.wordLength_le z⟩
    exact ⟨table, fun z =>
      (C.layerRelationCertificate.wordFor z).value_eq⟩
  · rintro ⟨table, htable⟩
    exact
      ⟨{ layerRelationCertificate :=
          { wordFor := fun z =>
              { word := (table z).1
                value_eq := htable z } }
         wordLength_le := fun z => (table z).2 }⟩

omit [IsTopologicalGroup F] in
/--
Bounded quotient-level relation-word tables form a finite search space once
the relator index set, the finite quotient layer, and the candidate-kernel
image are finite.
-/
lemma bounded_layer_table
    (q : F →* G)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    [Finite ι]
    [Finite (ONCompar.OpenNormalLayer N)]
    [Finite (ONCompar.kernelImage q N)] :
    Finite (BoundedLayerTable (ι := ι) q N bound) := by
  letI : Fintype (ONCompar.kernelImage q N) :=
    Fintype.ofFinite _
  infer_instance

/--
For fixed finite quotient layer and fixed word-length bound, existence of a
certifying bounded quotient-level word table is a decidable finite search
problem.
-/
def certifyingBoundedDecidable
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    [Finite ι]
    [Finite (ONCompar.OpenNormalLayer N)]
    [Finite (ONCompar.kernelImage q N)] :
    Decidable
      (∃ table : BoundedLayerTable (ι := ι) q N bound,
        RelationTableCertifies q relator N bound table) := by
  letI : Fintype (ONCompar.kernelImage q N) :=
    Fintype.ofFinite _
  letI : DecidableEq (ONCompar.kernelImage q N) :=
    Classical.decEq _
  letI : Fintype (BoundedLayerTable (ι := ι) q N bound) :=
    Fintype.ofFinite _
  letI : DecidableEq (BoundedLayerTable (ι := ι) q N bound) :=
    Classical.decEq _
  letI : DecidableEq (ONCompar.OpenNormalLayer N) :=
    Classical.decEq _
  letI : DecidablePred
      (fun table : BoundedLayerTable (ι := ι) q N bound =>
        RelationTableCertifies q relator N bound table) :=
    fun table => tableCertifiesDecidable
      (ι := ι) q relator N bound table
  exact Fintype.decidableExistsFintype

end IRScaffo

namespace KRData

/--
A bounded quotient-level relation-word table on the actual initial Koch
candidate-kernel image at one canonical Zassenhaus depth.
-/
abbrev BoundedRelationCertificate
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :=
  BLCert
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

/--
Existence of a bounded quotient-level relation-word table at one canonical
Zassenhaus depth.
-/
def RelationCertificateDepth
    (D : KRData)
    (n : ℕ) :
    Prop :=
  ∃ bound : ℕ,
    Nonempty (D.BoundedRelationCertificate n bound)

/--
Existence of bounded quotient-level relation-word tables at all canonical
Zassenhaus depths.
-/
def BoundedRelationCertificates
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, D.RelationCertificateDepth n

/--
At one Zassenhaus depth, bounded ambient and bounded quotient-level
candidate-kernel-image relation-word tables are equivalent.
-/
lemma bounded_certificate_ambient
    (D : KRData)
    (n : ℕ) :
    D.RelationCertificateDepth n ↔
      D.BoundedCertificateDepth n := by
  constructor
  · rintro ⟨bound, C⟩
    exact ⟨bound,
      (BLCert.nonempty_ambient
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)
        bound).mp C⟩
  · rintro ⟨bound, C⟩
    exact ⟨bound,
      (BLCert.nonempty_ambient
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)
        bound).mpr C⟩

/--
The concrete finite quotient Koch theorem is exactly existence of bounded
quotient-level relation-word tables in every canonical Zassenhaus finite
layer.
-/
lemma fin_koch_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.BoundedRelationCertificates := by
  rw [D.fin_factorization_certificates]
  exact forall_congr' fun n =>
    (D.bounded_certificate_ambient n).symm

/--
A bounded quotient-level relation-word table on the actual initial Koch
candidate-kernel image at one canonical Zassenhaus depth, with certificate
equations forgotten.
-/
abbrev BoundedRelationTable
    (n : ℕ)
    (bound : ℕ) :=
  BoundedLayerTable
    (ι := Fin 5)
    initialKochQuotient
    (zassenhausOpenSubgroup n)
    bound

/--
The correctness predicate for one bounded actual initial Koch Zassenhaus-layer
quotient relation-word table.
-/
abbrev BoundedTableCertifies
    (D : KRData)
    (n : ℕ)
    (bound : ℕ)
    (table : BoundedRelationTable n bound) :=
  RelationTableCertifies
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound
    table

/--
For fixed depth and word-length bound, the actual initial Koch bounded
Zassenhaus-layer quotient relation-word tables form a finite search space.
-/
lemma bounded_relation_table
    (n : ℕ)
    (bound : ℕ) :
    Finite (BoundedRelationTable n bound) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ZassenhausLayerImage n) := inferInstance
  exact bounded_layer_table
    (ι := Fin 5)
    initialKochQuotient
    (zassenhausOpenSubgroup n)
    bound

/--
For fixed Zassenhaus depth and fixed word-length bound, existence of a
certifying actual initial Koch quotient relation-word table is decidable.
-/
def certifyingTableDecidable
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :
    Decidable
      (∃ table : BoundedRelationTable n bound,
        D.BoundedTableCertifies n bound table) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ZassenhausLayerImage n) := inferInstance
  exact certifyingBoundedDecidable
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

/--
The concrete finite quotient Koch theorem is exactly the existence, at every
canonical Zassenhaus depth, of a bound and a certifying table in a finite
quotient-level word-table search space.
-/
lemma fin_forall_table
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, ∃ bound : ℕ,
        ∃ table : BoundedRelationTable n bound,
          D.BoundedTableCertifies n bound table := by
  rw [D.fin_koch_certificates]
  exact forall_congr' fun n => exists_congr fun bound =>
    nonempty_bounded_table
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)
      bound

end KRData

end TBluepr
end Towers
