import Submission.FieldTheory.QuotientKoch.LayerWordCofinality
import Submission.Group.OpenRelators.Comparison


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
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
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {N : OpenNormalSubgroup F}

/--
The element of the finite-layer candidate-kernel image represented by one
global candidate-kernel element.
-/
abbrev kernelImageElement
    (q : F →* G)
    (N : OpenNormalSubgroup F)
    (x : F)
    (hx : x ∈ q.ker) :
    ONCompar.kernelImage q N :=
  ⟨ONCompar.openNormalLayer N x, ⟨x, hx, rfl⟩⟩

/--
An explicit relation-word certificate for one element of the candidate-kernel
image in one open-normal finite layer.
-/
structure ERCert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (z : ONCompar.kernelImage q N) where
  word :
    RWord ι F
  quotient_value_eq :
    IGScaffoa.quotientMap N
        (word.value relator) =
      z

namespace ERCert

/--
A pointwise certificate for one ambient kernel element gives a certificate for
its class in the finite-layer candidate-kernel image.
-/
def ofKernelElement
    {x : F}
    {hx : x ∈ q.ker}
    (C : KECert q relator N x) :
    ERCert q relator N
      (kernelImageElement q N x hx) where
  word := C.word
  quotient_value_eq := C.quotient_value_eq

/--
A certificate for the finite-layer class of one ambient kernel element gives
the original pointwise certificate for that kernel element.
-/
def toKernelElement
    {x : F}
    {hx : x ∈ q.ker}
    (C :
      ERCert q relator N
        (kernelImageElement q N x hx)) :
    KECert q relator N x where
  word := C.word
  quotient_value_eq := C.quotient_value_eq

omit [IsTopologicalGroup F] in
/--
An image-element relation-word certificate proves that the certified finite
layer element lies in the relator image.
-/
lemma mem_relatorImage
    {z : ONCompar.kernelImage q N}
    (C : ERCert q relator N z) :
    (z : ONCompar.OpenNormalLayer N) ∈
      ONCompar.relatorImage relator N := by
  refine ⟨C.word.value relator, ?_, C.quotient_value_eq⟩
  simpa [IGScaffo.relationSubgroup,
    PRFact.relationSubgroup] using
      C.word.value_relation relator

/--
The length of the explicit relation word carried by one finite-layer
candidate-kernel-image certificate.
-/
def wordLength
    {z : ONCompar.kernelImage q N}
    (C : ERCert q relator N z) :
    ℕ :=
  C.word.length

end ERCert

/--
A finite-layer relation-word table assigns one explicit relation word to every
element of the finite-layer candidate-kernel image.
-/
structure KICert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) where
  wordFor :
    ∀ z : ONCompar.kernelImage q N,
      ERCert q relator N z

namespace KICert

omit [IsTopologicalGroup F] in
/--
A relation-word table on the candidate-kernel image proves inclusion of that
image in the relator image.
-/
lemma kernel_image_relator
    (C : KICert q relator N) :
    ONCompar.kernelImage q N ≤
      ONCompar.relatorImage relator N := by
  intro z hz
  exact (C.wordFor ⟨z, hz⟩).mem_relatorImage

omit [IsTopologicalGroup F] in
/--
A relation-word table on the candidate-kernel image proves the original
algebraic finite-layer kernel-generation predicate.
-/
lemma kernelGeneratedAlgebraically
    (C : KICert q relator N) :
    GeneratedAlgebraicallyOpen q relator N := by
  simpa [IGScaffo.GeneratedAlgebraicallyOpen,
    IGScaffoa.quotientMap,
    IGScaffo.relationSubgroup,
    ONFact.GeneratedAlgebraicallyOpen,
    PRFact.relationSubgroup] using
      (ONCompar.algebraically_open_relator
        q relator N).mpr C.kernel_image_relator

/--
An existing ambient-kernel finite-layer certificate descends to a table indexed
only by distinct candidate-kernel image elements in that finite layer.
-/
def openNormalCertificate
    (C : ORCert q relator N) :
    KICert q relator N where
  wordFor := by
    intro z
    let x : F := Classical.choose z.property
    have hx : x ∈ q.ker := (Classical.choose_spec z.property).1
    have hxz :
        IGScaffoa.quotientMap N x = z :=
      (Classical.choose_spec z.property).2
    exact
      { word := (C.wordFor x hx).word
        quotient_value_eq := (C.wordFor x hx).quotient_value_eq.trans hxz }

/--
A relation-word table indexed by finite-layer candidate-kernel image elements
recovers the older ambient-kernel finite-layer certificate.
-/
def openQuotientCertificate
    (C : KICert q relator N) :
    ORCert q relator N where
  wordFor := by
    intro x hx
    exact (C.wordFor (kernelImageElement q N x hx)).toKernelElement

omit [IsTopologicalGroup F] in
/--
The finite-layer relation-word table formulation is equivalent to the older
ambient-kernel certificate formulation.
-/
lemma nonempty_open_certificate
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Nonempty (KICert q relator N) ↔
      Nonempty (ORCert q relator N) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.openQuotientCertificate⟩
  · rintro ⟨C⟩
    exact ⟨openNormalCertificate C⟩

omit [IsTopologicalGroup F] in
/--
Existence of a finite-layer relation-word table is equivalent to pointwise
existence of the older ambient-kernel relation-word witnesses.
-/
lemma nonemp_point_certi
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Nonempty (KICert q relator N) ↔
      ∀ x : F, x ∈ q.ker →
        Nonempty (KECert q relator N x) := by
  rw [nonempty_open_certificate]
  constructor
  · rintro ⟨C⟩ x hx
    exact ⟨C.wordFor x hx⟩
  · intro h
    exact ⟨ORCert.ofPointwise h⟩

omit [IsTopologicalGroup F] in
/--
Existence of a finite-layer relation-word table is exactly algebraic
finite-layer kernel generation.
-/
lemma nonemp_gener_algeb
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Nonempty (KICert q relator N) ↔
      GeneratedAlgebraicallyOpen q relator N := by
  constructor
  · rintro ⟨C⟩
    exact C.kernelGeneratedAlgebraically
  · intro hgen
    apply (nonemp_point_certi q relator N).2
    intro x hx
    exact ⟨KECert.quotient_relation_subgroup
      q relator N x (hgen x hx)⟩

/--
If the candidate-kernel image in one layer is finite, any complete relation
word table has a uniform maximum word length over that finite layer.
-/
def maxWordLength
    [Fintype (ONCompar.kernelImage q N)]
    (C : KICert q relator N) :
    ℕ :=
  Finset.univ.sup (fun z => (C.wordFor z).wordLength)

omit [IsTopologicalGroup F] in
/--
Every relation word in a finite candidate-kernel-image table is bounded by the
table's maximum relation-word length.
-/
lemma word_length_max
    [Fintype (ONCompar.kernelImage q N)]
    (C : KICert q relator N)
    (z : ONCompar.kernelImage q N) :
    (C.wordFor z).wordLength ≤ C.maxWordLength := by
  exact Finset.le_sup (f := fun y => (C.wordFor y).wordLength) (Finset.mem_univ z)

end KICert

/--
A bounded finite-layer relation-word table records one complete candidate-
kernel-image table together with one uniform relation-word length bound.
-/
structure BKCert
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) where
  kernelRelationCertificate :
    KICert q relator N
  wordLength_le :
    ∀ z : ONCompar.kernelImage q N,
      (kernelRelationCertificate.wordFor z).wordLength ≤ bound

namespace BKCert

/--
Package a complete candidate-kernel-image relation-word table with any proven
uniform relation-word length bound.
-/
def certificateWordLength
    (C : KICert q relator N)
    (bound : ℕ)
    (hbound :
      ∀ z : ONCompar.kernelImage q N,
        (C.wordFor z).wordLength ≤ bound) :
    BKCert q relator N bound where
  kernelRelationCertificate := C
  wordLength_le := hbound

omit [IsTopologicalGroup F] in
/--
For a finite candidate-kernel image, every complete relation-word table admits
some uniform relation-word length bound.
-/
lemma exists_of_nonempty
    [Finite (ONCompar.kernelImage q N)]
    (h : Nonempty (KICert q relator N)) :
    ∃ bound : ℕ,
      Nonempty (BKCert q relator N bound) := by
  letI : Fintype (ONCompar.kernelImage q N) :=
    Fintype.ofFinite _
  rcases h with ⟨C⟩
  exact ⟨C.maxWordLength,
    ⟨certificateWordLength C C.maxWordLength C.word_length_max⟩⟩

omit [IsTopologicalGroup F] in
/--
For a finite candidate-kernel image, complete relation-word tables are
equivalent to bounded complete relation-word tables for some bound.
-/
lemma nonemp_relat_certi
    [Finite (ONCompar.kernelImage q N)] :
    Nonempty (KICert q relator N) ↔
      ∃ bound : ℕ,
        Nonempty (BKCert q relator N bound) := by
  constructor
  · exact exists_of_nonempty
  · rintro ⟨bound, C⟩
    exact C.map fun bounded => bounded.kernelRelationCertificate

end BKCert

end IRScaffo

namespace KRData

/-- The actual five tame Koch relators are killed by the actual initial Koch quotient map. -/
lemma tameRelatorsKilled
    (D : KRData) :
    PRFact.KillsRelators
      (initialTameRelator D.frobeniusLift)
      initialKochQuotient := by
  exact D.tame_maps_one

/--
The finite-layer candidate-kernel image for the actual initial Koch quotient
at one canonical Zassenhaus depth.
-/
abbrev ZassenhausLayerImage
    (n : ℕ) :=
  ONCompar.kernelImage
    initialKochQuotient
    (zassenhausOpenSubgroup n)

/--
A complete relation-word table on the actual initial Koch candidate-kernel
image at one canonical Zassenhaus depth.
-/
abbrev ImageRelationCertificate
    (D : KRData)
    (n : ℕ) :=
  KICert
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

/--
Existence of complete relation-word tables on the actual initial Koch
candidate-kernel images in every canonical Zassenhaus finite layer.
-/
def ImageRelationCertificates
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, Nonempty (D.ImageRelationCertificate n)

/--
A complete bounded relation-word table on the actual initial Koch candidate-
kernel image at one canonical Zassenhaus depth.
-/
abbrev BoundedImageCertificate
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :=
  BKCert
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

/--
The actual candidate-kernel image in one canonical Zassenhaus finite layer is
finite, so relation-word tables there can be equipped with finite maximum word
lengths.
-/
noncomputable abbrev zassenhausImageFintype
    (n : ℕ) :
    Fintype (ZassenhausLayerImage n) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  exact Fintype.ofFinite _

/--
Existence of a complete bounded candidate-kernel-image relation-word table at
one canonical Zassenhaus depth.
-/
def BoundedCertificateDepth
    (D : KRData)
    (n : ℕ) :
    Prop :=
  ∃ bound : ℕ,
    Nonempty (D.BoundedImageCertificate n bound)

/--
Existence of complete bounded candidate-kernel-image relation-word tables in
all canonical Zassenhaus finite layers.
-/
def BoundedImageCertificates
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, D.BoundedCertificateDepth n

/--
At one Zassenhaus depth, the candidate-kernel-image table formulation is
equivalent to the older pointwise ambient-kernel certificate formulation.
-/
lemma nonempty_certificate_pointwise
    (D : KRData)
    (n : ℕ) :
    Nonempty (D.ImageRelationCertificate n) ↔
      D.PointwiseCertificatesDepth n := by
  exact KICert.nonemp_point_certi
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

/--
At one Zassenhaus depth, complete candidate-kernel-image relation-word tables
are equivalent to bounded complete tables for some finite relation-word length
bound.
-/
lemma nonempty_certificate_depth
    (D : KRData)
    (n : ℕ) :
    Nonempty (D.ImageRelationCertificate n) ↔
      D.BoundedCertificateDepth n := by
  letI : Fintype (ZassenhausLayerImage n) :=
    zassenhausImageFintype n
  exact BKCert.nonemp_relat_certi

/--
The concrete finite quotient Koch theorem is exactly existence of finite
relation-word tables indexed by the actual candidate-kernel images in all
canonical Zassenhaus finite layers.
-/
lemma fin_image_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.ImageRelationCertificates := by
  rw [D.theorem_forall_certificates]
  exact forall_congr' fun n =>
    (D.nonempty_certificate_pointwise n).symm

/--
The concrete finite quotient Koch theorem is exactly existence, at every
canonical Zassenhaus depth, of a bounded finite relation-word table on the
actual candidate-kernel image.
-/
lemma fin_factorization_certificates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.BoundedImageCertificates := by
  rw [D.fin_image_certificates]
  exact forall_congr' fun n =>
    D.nonempty_certificate_depth n

/--
The canonical finite-layer quotient comparison for the actual initial Koch
quotient at one canonical Zassenhaus depth.
-/
abbrev relatorImageComparison
    (D : KRData)
    (n : ℕ) :=
  ONCompar.relatorKernelComparison
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    D.tameRelatorsKilled

/--
The canonical finite-layer comparison for the actual initial Koch quotient is
an isomorphism at one canonical Zassenhaus depth.
-/
def CanonicalComparisonIsomorphism
    (D : KRData)
    (n : ℕ) :
    Prop :=
  ONCompar.ImageComparisonIsomorphism
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    D.tameRelatorsKilled

/--
The canonical finite-layer comparison for the actual initial Koch quotient is
an isomorphism in every canonical Zassenhaus finite layer.
-/
def CanonicalComparisonIsomorphisms
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, D.CanonicalComparisonIsomorphism n

/--
At one Zassenhaus depth, a complete candidate-kernel-image relation-word table
is exactly bijectivity of the canonical finite-layer quotient comparison.
-/
lemma nonempty_certificate_iso
    (D : KRData)
    (n : ℕ) :
    Nonempty (D.ImageRelationCertificate n) ↔
      D.CanonicalComparisonIsomorphism n := by
  rw [KICert.nonemp_gener_algeb]
  simpa [IGScaffo.GeneratedAlgebraicallyOpen,
    IGScaffoa.quotientMap,
    IGScaffo.relationSubgroup,
    ONFact.GeneratedAlgebraicallyOpen,
    PRFact.relationSubgroup] using
      (ONCompar.algebraically_iso_kills
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)
        D.tameRelatorsKilled)

/--
The concrete finite quotient Koch theorem is exactly the statement that the
canonical relator-vs-kernel finite quotient comparison is an isomorphism in
every canonical Zassenhaus finite layer.
-/
lemma theorem_comparison_isomorphisms
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.CanonicalComparisonIsomorphisms := by
  rw [D.fin_image_certificates]
  exact forall_congr' fun n =>
    D.nonempty_certificate_iso n

end KRData

end TBluepr
end Submission
