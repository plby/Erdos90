import Submission.Group.FinitePGS


noncomputable section

namespace Submission
namespace TBluepr

structure GPSep
    (α : Type*) (p : ℕ) (w : FreeGroup α) : Type _ where
  quotient : Type
  [instGroup : Group quotient]
  [instFinite : Finite quotient]
  isPGroup : IsPGroup p quotient
  quotientMap : FreeGroup α →* quotient
  separates : quotientMap w ≠ 1

attribute [instance] GPSep.instGroup
attribute [instance] GPSep.instFinite

/- A coefficient-level witness for the Magnus residual-`p` argument.  This is deliberately not
yet a finite quotient of the free group.  It records the smaller fact that the Magnus expansion
of a nontrivial word has some nonzero coefficient in a finite truncation over `𝔽_p`. -/

structure MCWitnes
    (β : Type*) (p : ℕ) (w : FreeGroup β) : Type _ where
  truncationDepth : ℕ
  coefficientSpace : Type
  [instZero : Zero coefficientSpace]
  coefficientMap : FreeGroup β → coefficientSpace
  coefficient_one : coefficientMap 1 = 0
  coefficient_ne_zero : coefficientMap w ≠ 0

attribute [instance] MCWitnes.instZero

/- The nonzero coefficient can be read without exposing the internal field names of the witness.
This keeps the final residual-`p` assembly independent of the eventual concrete coefficient
space used by a Magnus formalization. -/

theorem MCWitnes.word_coeff_nezero
    {β : Type*} {p : ℕ} {w : FreeGroup β}
    (C : MCWitnes β p w) :
    C.coefficientMap w ≠ 0 := by
  have hcoeff :
      C.coefficientMap w ≠ 0 :=
    C.coefficient_ne_zero
  have hsame :
      C.coefficientMap w ≠ 0 :=
    hcoeff
  exact hsame

/- If a quotient kills the word, then it kills any coefficient that factors through that
quotient.  This is the exact compatibility statement needed from a finite Magnus truncation:
the coefficient witness must be visible in the finite quotient rather than only in a formal
power-series ring. -/

structure MTRealiz
    {β : Type*} {p : ℕ} {w : FreeGroup β}
    (C : MCWitnes β p w) : Type _ where
  quotient : Type
  [instGroup : Group quotient]
  [instFinite : Finite quotient]
  isPGroup : IsPGroup p quotient
  quotientMap : FreeGroup β →* quotient
  coeff_word_one :
    quotientMap w = 1 → C.coefficientMap w = 0

attribute [instance] MTRealiz.instGroup
attribute [instance] MTRealiz.instFinite

/- A finite Magnus truncation realization separates the word, because equality to `1` in the
quotient would force the chosen nonzero coefficient to vanish. -/

theorem MTRealiz.quotientMap_separates
    {β : Type*} {p : ℕ} {w : FreeGroup β}
    {C : MCWitnes β p w}
    (R : MTRealiz C) :
    R.quotientMap w ≠ 1 := by
  intro hword
  have hzero :
      C.coefficientMap w = 0 :=
    R.coeff_word_one hword
  have hnonzero :
      C.coefficientMap w ≠ 0 :=
    C.word_coeff_nezero
  exact hnonzero hzero

/- The quotient carried by a finite Magnus truncation realization is already a finite
`p`-separation in the sense used by the rest of the file. -/

def MTRealiz.fin_p_sep
    {β : Type*} {p : ℕ} {w : FreeGroup β}
    {C : MCWitnes β p w}
    (R : MTRealiz C) :
    GPSep β p w := by
  refine
    {
      quotient := R.quotient
      instGroup := R.instGroup
      instFinite := R.instFinite
      isPGroup := R.isPGroup
      quotientMap := R.quotientMap
      separates := ?_
    }
  exact R.quotientMap_separates

/- The first Magnus input: a nontrivial word in a finitely generated free group has a first
nonzero Magnus coefficient modulo `p`.  This is smaller than constructing the finite quotient;
it is a statement about the faithful Magnus expansion and the existence of a lowest nonzero
homogeneous term. -/

structure FPSep
    (α : Type*) (p : ℕ) (w : FreeGroup α) : Type _ where
  depth : ℕ
  quotient : Type
  [instGroup : Group quotient]
  [instFinite : Finite quotient]
  isPGroup : IsPGroup p quotient
  quotientMap : FreeGroup α →* quotient
  zassenhaus_le_kernel :
    zassenhausFiltration p (FreeGroup α) (depth + 1) ≤ quotientMap.ker
  separates : quotientMap w ≠ 1

attribute [instance] FPSep.instGroup
attribute [instance] FPSep.instFinite

/- If a shifted Zassenhaus separating quotient exists, then the word cannot lie in every
shifted Zassenhaus term.  This is the formal contradiction used in the intersection theorem. -/

theorem FPSep.not_memall_shiftedzass
    {α : Type*} {p : ℕ} {w : FreeGroup α}
    (S : FPSep α p w) :
    ¬ ∀ depth : ℕ,
        w ∈ zassenhausFiltration p (FreeGroup α) (depth + 1) := by
  intro hmem
  have hwker :
      w ∈ S.quotientMap.ker :=
    S.zassenhaus_le_kernel (hmem S.depth)
  have hwone : S.quotientMap w = 1 := by
    exact MonoidHom.mem_ker.mp hwker
  exact S.separates hwone

universe uFreeGroupSupport

/- A finite-support reduction for a single word in an arbitrary free group.  The `support`
type is finite, `modelWord` is the same reduced word written in that finite alphabet, and
`projection` kills every generator outside the finite support while sending the original word
to `modelWord`. -/

structure FSRed
    (α : Type uFreeGroupSupport) (w : FreeGroup α) : Type (uFreeGroupSupport + 1) where
  support : Type uFreeGroupSupport
  [instFintype : Fintype support]
  modelWord : FreeGroup support
  projection : FreeGroup α →* FreeGroup support
  projection_word : projection w = modelWord
  model_ne_one : modelWord ≠ 1

attribute [instance] FSRed.instFintype

/- A finite alphabet model for a word in a possibly infinitely generated free group.  This is
the first genuinely combinatorial ingredient in finite-support reduction: the word is already
the image of a word in a finite free group under the inclusion of the finitely many letters that
occur in a reduced representative. -/

structure FGAlphab
    (α : Type uFreeGroupSupport) (w : FreeGroup α) : Type (uFreeGroupSupport + 1) where
  support : Type uFreeGroupSupport
  [instFintype : Fintype support]
  letterEmbedding : support ↪ α
  inclusionMap : FreeGroup support →* FreeGroup α
  inclusion_on_generators :
    ∀ a : support, inclusionMap (FreeGroup.of a) =
      FreeGroup.of (letterEmbedding a)
  modelWord : FreeGroup support
  inclusion_model_word : inclusionMap modelWord = w

attribute [instance] FGAlphab.instFintype

/- A retraction for a finite alphabet model.  Once the finite letters have been identified as a
subtype of the ambient alphabet, the projection sends those letters back to their generators
and sends every other ambient letter to `1`.  This is kept separate from extracting the finite
alphabet itself. -/

structure FARetrac
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w) : Type _ where
  projection : FreeGroup α →* FreeGroup A.support
  projection_modelWord : projection w = A.modelWord

/- The model word really maps back to the original word.  This small accessor is useful because
later proofs should not unfold the finite alphabet record just to read off its core equality. -/

theorem FGAlphab.word_eq_inclusion
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w) :
    w = A.inclusionMap A.modelWord := by
  have hforward :
      A.inclusionMap A.modelWord = w :=
    A.inclusion_model_word
  have hback :
      w = A.inclusionMap A.modelWord :=
    hforward.symm
  exact hback

/- Nontriviality descends to the finite model word.  If the model word were trivial, applying
the inclusion map would make the original word trivial too. -/

theorem FGAlphab.model_ne_one
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w)
    (hw : w ≠ 1) :
    A.modelWord ≠ 1 := by
  intro hmodel
  apply hw
  calc
    w = A.inclusionMap A.modelWord := A.word_eq_inclusion
    _ = A.inclusionMap 1 := by rw [hmodel]
    _ = 1 := A.inclusionMap.map_one

/- The inclusion map in a finite alphabet model is the canonical free-group map induced by its
letter embedding.  The record stores the generator-level rule, and free-group extensionality
upgrades it to equality of homomorphisms. -/

theorem FGAlphab.inclusion_map_eqmap
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w) :
    A.inclusionMap = FreeGroup.map A.letterEmbedding := by
  ext a
  rw [A.inclusion_on_generators a]
  simp

/- The trivial word is supported on the empty finite alphabet. -/

def FGAlphab.one
    (α : Type uFreeGroupSupport) :
    FGAlphab α (1 : FreeGroup α) := by
  let support : Type _ := ULift.{uFreeGroupSupport} (Fin 0)
  refine
    {
      support := support
      instFintype := inferInstance
      letterEmbedding := ?_
      inclusionMap := FreeGroup.map (fun a : support => Fin.elim0 a.down)
      inclusion_on_generators := ?_
      modelWord := 1
      inclusion_model_word := ?_
    }
  · refine
      {
        toFun := fun a : support => Fin.elim0 a.down
        inj' := ?_
      }
    intro a
    exact Fin.elim0 a.down
  · intro a
    exact Fin.elim0 a.down
  · simp

/- A single generator is supported on a one-letter finite alphabet. -/

def FGAlphab.of
    {α : Type uFreeGroupSupport} (a : α) :
    FGAlphab α (FreeGroup.of a) := by
  let support : Type _ := ULift.{uFreeGroupSupport} (Fin 1)
  let letterEmbedding : support ↪ α :=
    {
      toFun := fun _ => a
      inj' := by
        intro i j _h
        exact Subsingleton.elim i j
    }
  refine
    {
      support := support
      instFintype := inferInstance
      letterEmbedding := letterEmbedding
      inclusionMap := FreeGroup.map letterEmbedding
      inclusion_on_generators := ?_
      modelWord := FreeGroup.of (ULift.up 0)
      inclusion_model_word := ?_
    }
  · intro i
    simp
  · simp [letterEmbedding]

/- The inverse of a single generator is supported on the same one-letter finite alphabet. -/

def FGAlphab.invOf
    {α : Type uFreeGroupSupport} (a : α) :
    FGAlphab α (FreeGroup.of a)⁻¹ := by
  let support : Type _ := ULift.{uFreeGroupSupport} (Fin 1)
  let letterEmbedding : support ↪ α :=
    {
      toFun := fun _ => a
      inj' := by
        intro i j _h
        exact Subsingleton.elim i j
    }
  refine
    {
      support := support
      instFintype := inferInstance
      letterEmbedding := letterEmbedding
      inclusionMap := FreeGroup.map letterEmbedding
      inclusion_on_generators := ?_
      modelWord := (FreeGroup.of (ULift.up 0))⁻¹
      inclusion_model_word := ?_
    }
  · intro i
    simp
  · simp [letterEmbedding]

/- Finite alphabet models are closed under multiplication by taking the union of the two finite
sets of ambient letters and transporting both model words into that union alphabet. -/

def FGAlphab.mul
    {α : Type uFreeGroupSupport} {x y : FreeGroup α}
    (A : FGAlphab α x)
    (B : FGAlphab α y) :
    FGAlphab α (x * y) := by
  classical
  let sA : Finset α := Finset.univ.image A.letterEmbedding
  let sB : Finset α := Finset.univ.image B.letterEmbedding
  let s : Finset α := sA ∪ sB
  let support : Type _ := {a : α // a ∈ s}
  let letterEmbedding : support ↪ α :=
    {
      toFun := fun a => a.1
      inj' := by
        intro a b h
        exact Subtype.ext h
    }
  let leftToUnion : A.support → support :=
    fun a =>
      ⟨A.letterEmbedding a, by
        dsimp [s, sA]
        exact Finset.mem_union_left sB (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)⟩
  let rightToUnion : B.support → support :=
    fun b =>
      ⟨B.letterEmbedding b, by
        dsimp [s, sB]
        exact Finset.mem_union_right sA (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)⟩
  let inclusionMap : FreeGroup support →* FreeGroup α :=
    FreeGroup.map letterEmbedding
  let modelWord : FreeGroup support :=
    FreeGroup.map leftToUnion A.modelWord *
      FreeGroup.map rightToUnion B.modelWord
  have hleft :
      inclusionMap.comp (FreeGroup.map leftToUnion) = A.inclusionMap := by
    ext a
    change inclusionMap (FreeGroup.map leftToUnion (FreeGroup.of a)) =
      A.inclusionMap (FreeGroup.of a)
    rw [A.inclusion_on_generators a]
    simp [inclusionMap, leftToUnion, letterEmbedding]
  have hright :
      inclusionMap.comp (FreeGroup.map rightToUnion) = B.inclusionMap := by
    ext b
    change inclusionMap (FreeGroup.map rightToUnion (FreeGroup.of b)) =
      B.inclusionMap (FreeGroup.of b)
    rw [B.inclusion_on_generators b]
    simp [inclusionMap, rightToUnion, letterEmbedding]
  refine
    {
      support := support
      instFintype := inferInstance
      letterEmbedding := letterEmbedding
      inclusionMap := inclusionMap
      inclusion_on_generators := ?_
      modelWord := modelWord
      inclusion_model_word := ?_
    }
  · intro a
    simp [inclusionMap, letterEmbedding]
  · calc
      inclusionMap modelWord =
          inclusionMap (FreeGroup.map leftToUnion A.modelWord) *
            inclusionMap (FreeGroup.map rightToUnion B.modelWord) := by
              simp [modelWord]
      _ =
          (inclusionMap.comp (FreeGroup.map leftToUnion)) A.modelWord *
            (inclusionMap.comp (FreeGroup.map rightToUnion)) B.modelWord := rfl
      _ = A.inclusionMap A.modelWord * B.inclusionMap B.modelWord := by
            rw [hleft, hright]
      _ = x * y := by
            rw [A.inclusion_model_word, B.inclusion_model_word]

/- A retraction sends the original word to the finite model word by definition.  This accessor
keeps the conversion to `FSRed` independent of the chosen field name
inside the retraction record. -/

theorem FARetrac.projection_word_eq
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    {A : FGAlphab α w}
    (R : FARetrac A) :
    R.projection w = A.modelWord := by
  have hprojection :
      R.projection w = A.modelWord :=
    R.projection_modelWord
  have hsame :
      R.projection w = A.modelWord :=
    hprojection
  exact hsame

/- The same retraction identity can be read after replacing the ambient word by the included
finite model.  This records the intended retraction behavior on the one word that matters,
without requiring the final reduction proof to reason about all generators. -/

theorem FARetrac.projection_inclusion_modelword
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    {A : FGAlphab α w}
    (R : FARetrac A) :
    R.projection (A.inclusionMap A.modelWord) = A.modelWord := by
  have hword :
      A.inclusionMap A.modelWord = w :=
    A.inclusion_model_word
  have hprojection :
      R.projection w = A.modelWord :=
    R.projection_word_eq
  calc
    R.projection (A.inclusionMap A.modelWord) = R.projection w := by rw [hword]
    _ = A.modelWord := hprojection

/- A finite alphabet model plus its retraction is exactly the finite-support reduction needed
by the residual finite-`p` argument. -/

def FGAlphab.fin_support_reduce
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w)
    (R : FARetrac A)
    (hw : w ≠ 1) :
    FSRed α w := by
  refine
    {
      support := A.support
      instFintype := A.instFintype
      modelWord := A.modelWord
      projection := R.projection
      projection_word := ?_
      model_ne_one := ?_
    }
  · exact R.projection_word_eq
  · exact A.model_ne_one hw

/- Every free-group word has a finite alphabet model.  This is proved by induction from the
free-group constructors: the identity uses the empty alphabet, a generator and its inverse use a
one-letter alphabet, and multiplication uses the union of the two finite alphabets. -/

theorem free_alphabet_any
    {α : Type uFreeGroupSupport}
    (w : FreeGroup α) :
    Nonempty (FGAlphab α w) := by
  classical
  induction w using FreeGroup.induction_on with
  | C1 =>
      exact ⟨FGAlphab.one α⟩
  | of a =>
      exact ⟨FGAlphab.of a⟩
  | inv_of a _ha =>
      exact ⟨FGAlphab.invOf a⟩
  | mul x y hx hy =>
      rcases hx with ⟨A⟩
      rcases hy with ⟨B⟩
      exact ⟨A.mul B⟩

/- Extracting the finite alphabet used by a nontrivial word is the first smaller combinatorial
input needed by finite-support reduction.  The construction actually works for every word; the
nontriviality hypothesis is kept in this wrapper because the later finite-support reduction uses
it to prove that the finite model word is nontrivial. -/

theorem free_group_alphabet
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (_hw : w ≠ 1) :
    Nonempty (FGAlphab α w) := by
  exact free_alphabet_any w

/- Once the finite alphabet has been extracted, the second smaller combinatorial input is the
ambient retraction.  It sends a generator in the finite support to the corresponding finite
generator and sends every generator outside the support to `1`, so the extracted model word is
fixed by projecting the original word. -/

theorem FGAlphab.retraction_exists
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (A : FGAlphab α w) :
    Nonempty (FARetrac A) := by
  classical
  let toSupport : α → FreeGroup A.support :=
    fun a =>
      if h : ∃ s : A.support, A.letterEmbedding s = a then
        FreeGroup.of (Classical.choose h)
      else
        1
  let projection : FreeGroup α →* FreeGroup A.support :=
    FreeGroup.lift toSupport
  have hprojection_generator :
      ∀ a : A.support,
        projection (FreeGroup.of (A.letterEmbedding a)) = FreeGroup.of a := by
    intro a
    have hmem : ∃ s : A.support, A.letterEmbedding s = A.letterEmbedding a :=
      ⟨a, rfl⟩
    have hchoose : Classical.choose hmem = a := by
      exact A.letterEmbedding.injective (Classical.choose_spec hmem)
    simp [projection, toSupport]
  have hleft :
      projection.comp A.inclusionMap = MonoidHom.id (FreeGroup A.support) := by
    ext a
    change projection (A.inclusionMap (FreeGroup.of a)) = FreeGroup.of a
    rw [A.inclusion_on_generators a]
    exact hprojection_generator a
  refine ⟨?_⟩
  exact
    {
      projection := projection
      projection_modelWord := by
        have hmodel :
            projection (A.inclusionMap A.modelWord) = A.modelWord := by
          change (projection.comp A.inclusionMap) A.modelWord = A.modelWord
          rw [hleft]
          rfl
        simpa [A.inclusion_model_word] using hmodel
    }

/- The finite-support reduction is the purely combinatorial part of residual finiteness for
free groups.  It is independent of `p`: a reduced nontrivial word uses only finitely many
letters, so it can be read in a finitely generated free subgroup and recovered by a retraction
from the original free group. -/

theorem free_support_reduction
    {α : Type uFreeGroupSupport} {w : FreeGroup α}
    (hw : w ≠ 1) :
    Nonempty (FSRed α w) := by
  classical
  rcases free_group_alphabet hw with ⟨A⟩
  rcases A.retraction_exists with ⟨R⟩
  have reduction :
      FSRed α w :=
    A.fin_support_reduce R hw
  exact ⟨reduction⟩

/- The finitely generated residual finite-`p` theorem.  This is the genuinely classical
residual-`p` input after finite-support reduction has removed all universe-size issues: every
nontrivial word in a finitely generated free group survives in a finite `p`-group quotient.

One standard proof uses the Magnus embedding into units of truncated noncommutative power
series over `𝔽_p`: a nontrivial word has a first nonzero homogeneous term, and truncating
above that degree gives a finite `p`-group of units that still detects the word. -/

def FSRed.compose_fin_psep
    {α : Type uFreeGroupSupport} {p : ℕ} {w : FreeGroup α}
    (R : FSRed α w)
    (S : GPSep R.support p R.modelWord) :
    GPSep α p w := by
  classical
  exact
    {
      quotient := S.quotient
      instGroup := S.instGroup
      instFinite := S.instFinite
      isPGroup := S.isPGroup
      quotientMap := S.quotientMap.comp R.projection
      separates := by
        intro hsep
        have hmodel :
            S.quotientMap R.modelWord =
              (S.quotientMap.comp R.projection) w := by
          calc
            S.quotientMap R.modelWord =
                S.quotientMap (R.projection w) := by
                  exact congrArg S.quotientMap R.projection_word.symm
            _ = (S.quotientMap.comp R.projection) w := rfl
        exact S.separates (hmodel.trans hsep)
    }

/- The arbitrary-alphabet residual finite-`p` statement follows from finite-support reduction
and the finitely generated residual finite-`p` theorem. -/

theorem augmentation_bot_pow
    {p : ℕ} (hp : Nat.Prime p)
    {G : Type*} [Group G]
    {n : ℕ}
    (hpow :
      (GShafar.augmentationIdeal (R := ZMod p) (G := G)) ^ n = ⊥) :
    GShafar.augmentationPowerSubgroup (R := ZMod p) (G := G) n = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  ext g
  constructor
  · intro hg
    have hdiff_zero :
        (MonoidAlgebra.of (ZMod p) G g - 1 :
          MonoidAlgebra (ZMod p) G) = 0 := by
      have hg_bot :
          (MonoidAlgebra.of (ZMod p) G g - 1 :
            MonoidAlgebra (ZMod p) G) ∈
            (⊥ : Ideal (MonoidAlgebra (ZMod p) G)) := by
        simpa [GShafar.augmentationPowerSubgroup, hpow] using hg
      simpa using hg_bot
    have hof_eq_one :
        (MonoidAlgebra.of (ZMod p) G g :
          MonoidAlgebra (ZMod p) G) = 1 := by
      exact sub_eq_zero.mp hdiff_zero
    by_cases hg_one : g = 1
    · simp [hg_one]
    · have hcoeff :=
        congrArg (fun x : MonoidAlgebra (ZMod p) G => x g) hof_eq_one
      have hcoeff_one :
          (MonoidAlgebra.of (ZMod p) G g :
            MonoidAlgebra (ZMod p) G) g = 1 := by
        simp
      have hcoeff_zero :
          (1 : MonoidAlgebra (ZMod p) G) g = 0 := by
        simp [MonoidAlgebra.one_def, Finsupp.single_eq_of_ne hg_one]
      have hone_zero : (1 : ZMod p) = 0 := by
        simp [hcoeff_zero] at hcoeff
      exact False.elim ((zero_ne_one : (0 : ZMod p) ≠ 1) hone_zero.symm)
  · intro hg
    have hg_one : g = 1 := by
      simpa using hg
    rw [hg_one]
    exact
      (GShafar.augmentationPowerSubgroup
        (R := ZMod p) (G := G) n).one_mem

/- A finite `p`-group has a trivial sufficiently deep augmentation-power subgroup.  This is
the group-theoretic form of nilpotence of the augmentation ideal in `𝔽_p[Q]`. -/

theorem p_eventually_bot
    {p : ℕ} (hp : Nat.Prime p)
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) :
    ∃ depth : ℕ,
      GShafar.augmentationPowerSubgroup
        (R := ZMod p) (G := Q) (depth + 1) = ⊥ := by
  classical
  rcases augmentation_nilpotent_group p hp Q hQ with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  exact
    augmentation_bot_pow
      (p := p) hp (n := N + 1)
      (by
        exact
          le_bot_iff.mp
            (by
              calc
                (GShafar.augmentationIdeal (R := ZMod p) (G := Q)) ^ (N + 1)
                    ≤ (GShafar.augmentationIdeal (R := ZMod p) (G := Q)) ^ N := by
                      exact Ideal.pow_le_pow_right (Nat.le_succ N)
                _ = ⊥ := hN))

/- Consequently, the Zassenhaus filtration of a finite `p`-group is eventually trivial:
Zassenhaus terms lie inside the corresponding augmentation-power subgroups. -/

theorem filtration_eventually_bot
    {p : ℕ} (hp : Nat.Prime p)
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) :
    ∃ depth : ℕ,
      zassenhausFiltration p Q (depth + 1) = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases p_eventually_bot
      (p := p) hp Q hQ with
    ⟨depth, hAug⟩
  refine ⟨depth, ?_⟩
  apply le_antisymm
  · calc
      zassenhausFiltration p Q (depth + 1)
          ≤ GShafar.augmentationPowerSubgroup
              (R := ZMod p) (G := Q) (depth + 1) := by
            exact
              GShafar.zassenhaus_filtration_subgroup
                (p := p) (G := Q) (depth + 1)
      _ = ⊥ := hAug
  · exact bot_le

/- Zassenhaus generators are functorial under group homomorphisms: lower central series terms
map into lower central series terms, and powers commute with homomorphisms. -/

theorem zassenhaus_generator_set
    {p : ℕ}
    {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {n : ℕ}
    {g : G}
    (hg : g ∈ zassenhausGeneratorSet p G n) :
    φ g ∈ zassenhausGeneratorSet p Q n := by
  rcases hg with ⟨i, j, x, hx_lower, hbound, hpow⟩
  refine ⟨i, j, φ x, ?_, hbound, ?_⟩
  · exact
      (Subgroup.lowerCentralSeries.map φ i)
        (Subgroup.mem_map_of_mem φ hx_lower)
  · rw [← hpow]
    simp [MonoidHom.map_pow]

/- Functoriality extends from the generating set to its subgroup closure, hence to the full
Zassenhaus filtration. -/

theorem filtration_map_le
    {p : ℕ}
    {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (n : ℕ) :
    (zassenhausFiltration p G n).map φ ≤ zassenhausFiltration p Q n := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine Subgroup.closure_induction
    (k := zassenhausGeneratorSet p G n)
    (p := fun x _hx => φ x ∈ zassenhausFiltration p Q n)
    ?mem ?one ?mul ?inv hx
  · intro x hxgen
    exact
      Subgroup.subset_closure
        (zassenhaus_generator_set (p := p) φ hxgen)
  · simp
  · intro x y _hx _hy hxmem hymem
    simpa using
      (zassenhausFiltration p Q n).mul_mem hxmem hymem
  · intro x _hx hxmem
    simpa using
      (zassenhausFiltration p Q n).inv_mem hxmem

/- If a target Zassenhaus term is trivial, then the corresponding source Zassenhaus term lies
in the kernel of any homomorphism to that target. -/

theorem filtration_target_bot
    {p : ℕ}
    {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {n : ℕ}
    (hbot : zassenhausFiltration p Q n = ⊥) :
    zassenhausFiltration p G n ≤ φ.ker := by
  intro g hg
  have hmap :
      φ g ∈ zassenhausFiltration p Q n := by
    exact
      filtration_map_le (p := p) φ n
        (Subgroup.mem_map_of_mem φ hg)
  have hmap_bot : φ g ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hmap
  have hφ_one : φ g = 1 := by
    exact Subgroup.mem_bot.mp hmap_bot
  exact MonoidHom.mem_ker.mpr hφ_one

/- Any homomorphism from a free group to a finite `p`-group kills a sufficiently deep
Zassenhaus term.  Mathematically, the Zassenhaus filtration of a finite `p`-group is finite
and eventually trivial, and functoriality sends `D_n(F)` into `D_n(Q)`. -/

theorem free_kills_deep
    {α : Type*} {p : ℕ} (hp : Nat.Prime p)
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (φ : FreeGroup α →* Q) :
    ∃ depth : ℕ,
      zassenhausFiltration p (FreeGroup α) (depth + 1) ≤ φ.ker := by
  classical
  rcases filtration_eventually_bot
      (p := p) hp Q hQ with
    ⟨depth, hbot⟩
  refine ⟨depth, ?_⟩
  exact
    filtration_target_bot
      (p := p) φ hbot

/- A residual finite-`p` quotient can be upgraded to one that contains a shifted Zassenhaus
term in its kernel, by passing to a sufficiently deep term for that finite quotient.  The
result is stated as `Nonempty` so that the existential depth supplied by the finite-quotient
input is eliminated only into a proposition. -/

theorem GPSep.zass_finp_sepexists
    {α : Type*} {p : ℕ} {w : FreeGroup α}
    (hp : Nat.Prime p)
    (S : GPSep α p w) :
    Nonempty (FPSep α p w) := by
  classical
  rcases free_kills_deep
      (α := α) (p := p) hp S.isPGroup S.quotientMap with
    ⟨depth, hker⟩
  exact ⟨
    {
      depth := depth
      quotient := S.quotient
      instGroup := S.instGroup
      instFinite := S.instFinite
      isPGroup := S.isPGroup
      quotientMap := S.quotientMap
      zassenhaus_le_kernel := hker
      separates := S.separates
    }⟩

end TBluepr
end Submission
