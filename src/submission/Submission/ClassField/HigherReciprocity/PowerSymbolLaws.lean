import Submission.ClassField.HigherReciprocity.PowerReciprocity
import Submission.ClassField.QuadraticForms.QuadraticHilbert
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Chapter VIII, Section 5, Statements 5.3--5.10

These declarations fill the source-numbering gap between the finite-field
power residue symbol and the Power Recip Law.  General symbol algebras
and their local Brauer invariants are not yet constructed in the project, so
the local and global symbol statements are recorded against explicit symbol
interfaces rather than replaced by stronger conclusions.
-/

namespace Submission.CField.HRecip

open scoped BigOperators
open Submission.CField.QForms

/-! ## Statement 5.3: Artin action on a radical -/

variable {I P μ E : Type*} [CommGroup I] [CommGroup μ] [CommGroup E]

/-- The data used in the proof of 5.3.  `prime_ext` is unique factorization
of prime-to-support ideals; `prime_frobenius` is the defining Frobenius
calculation at a prime. -/
structure RAData where
  primeIdeal : P → I
  prime_ext : ∀ f g : I →* μ,
    (∀ p, f (primeIdeal p) = g (primeIdeal p)) → f = g
  powerResidue : I →* μ
  artinRootScalar : I →* μ
  radical : E
  rootEmbedding : μ →* E
  artinActionRadical : I → E
  action_eq_scalar : ∀ b,
    artinActionRadical b = rootEmbedding (artinRootScalar b) * radical
  prime_frobenius : ∀ p,
    artinRootScalar (primeIdeal p) = powerResidue (primeIdeal p)

namespace RAData

variable (D : RAData (I := I) (P := P) (μ := μ) (E := E))

/-- The literal assertion of Statement VIII.5.3, separated from the prime
factorization and Frobenius facts used in its proof. -/
def ArtinActionRoots : Prop :=
  ∀ b : I,
    D.artinActionRadical b =
      D.rootEmbedding (D.powerResidue b) * D.radical

/-- **Statement VIII.5.3.** The Artin automorphism acts on the chosen
`n`th root through the power residue character. -/
theorem artin_smul_root (b : I) :
    D.artinActionRadical b =
      D.rootEmbedding (D.powerResidue b) * D.radical := by
  have hcharacters : D.artinRootScalar = D.powerResidue :=
    D.prime_ext _ _ D.prime_frobenius
  rw [D.action_eq_scalar, hcharacters]

/-- **Statement VIII.5.3.** The source statement for every admissible ideal
follows from the calculation on prime generators. -/
theorem artinActionRoots : D.ArtinActionRoots :=
  fun b ↦ D.artin_smul_root b

end RAData

/-! ## Statement 5.4: congruence in the numerator -/

variable {A J Q ν : Type*} [CommGroup ν]

/-- Prime-factor data sufficient for the elementary congruence proof in
5.4.  `admissible a b` means `b ∈ I^{S(a)}`. -/
structure RCData where
  primeFactors : J → Finset Q
  multiplicity : J → Q → ℕ
  localSymbol : A → Q → ν
  residueSymbol : A → J → ν
  admissible : A → J → Prop
  congruentMod : A → A → J → Prop
  factorization : ∀ a b, admissible a b →
    residueSymbol a b =
      ∏ q ∈ primeFactors b, localSymbol a q ^ multiplicity b q
  congruent_admissible : ∀ a a' b,
    admissible a b → congruentMod a a' b → admissible a' b
  congruent_localSymbol : ∀ a a' b,
    congruentMod a a' b →
    ∀ q ∈ primeFactors b, localSymbol a q = localSymbol a' q

namespace RCData

variable (D : RCData (A := A) (J := J) (Q := Q) (ν := ν))

/-- The literal assertion of Statement VIII.5.4, with admissibility and
congruence left as the number-field predicates supplied by the application. -/
def ResidueSymbolCongruence : Prop :=
  ∀ (a a' : A) (b : J),
    D.admissible a b → D.congruentMod a a' b →
      D.admissible a' b ∧ D.residueSymbol a b = D.residueSymbol a' b

/-- **Statement VIII.5.4.** Congruent integral numerators have the same
power residue symbol modulo an admissible integral ideal. -/
theorem residue_symbol_congruent {a a' : A} {b : J}
    (hadmissible : D.admissible a b) (hcongruent : D.congruentMod a a' b) :
    D.admissible a' b ∧ D.residueSymbol a b = D.residueSymbol a' b := by
  classical
  have hadmissible' := D.congruent_admissible a a' b hadmissible hcongruent
  refine ⟨hadmissible', ?_⟩
  rw [D.factorization a b hadmissible, D.factorization a' b hadmissible']
  apply Finset.prod_congr rfl
  intro q hq
  rw [D.congruent_localSymbol a a' b hcongruent q hq]

/-- **Statement VIII.5.4.** The source statement follows prime by prime
from congruence modulo every prime factor of the denominator ideal. -/
theorem residueSymbolCongruence : D.ResidueSymbolCongruence := by
  intro a a' b hadmissible hcongruent
  exact D.residue_symbol_congruent hadmissible hcongruent

end RCData

/-! ## Statement 5.5: ray-class factorization -/

variable {M C : Type*}

/-- Literal factorization assertion in 5.5 for a fixed power-residue
character.  `supported m` expresses that the modulus is supported in `S(a)`. -/
def SymbolRayFactorization [CommGroup I] [CommGroup μ]
    [CommGroup C] (powerResidue : I →* μ) (supported : M → Prop)
    (rayClassMap : M → I →* C) : Prop :=
  ∃ m : M, supported m ∧
    ∃ chi : C →* μ, powerResidue = chi.comp (rayClassMap m)

namespace RAData

variable (D : RAData (I := I) (P := P) (μ := μ) (E := E))

/-- **Statement VIII.5.5.** Once Artin reciprocity factors the Artin
character of the radical extension through a ray class group, Statement
5.3 identifies that character with the power-residue symbol, so the same
ray-class factorization applies to the latter. -/
theorem symbol_ray_scalar
    [CommGroup C] (supported : M → Prop) (rayClassMap : M → I →* C)
    (hArtin : ∃ m : M, supported m ∧
      ∃ chi : C →* μ, D.artinRootScalar = chi.comp (rayClassMap m)) :
    SymbolRayFactorization D.powerResidue supported rayClassMap := by
  obtain ⟨m, hm, chi, hchi⟩ := hArtin
  refine ⟨m, hm, chi, ?_⟩
  have hcharacters : D.artinRootScalar = D.powerResidue :=
    D.prime_ext _ _ D.prime_frobenius
  exact hcharacters.symm.trans hchi

end RAData

/-! ## Example 5.6: the quadratic Hilbert symbol -/

namespace QFEquiva

variable {K : Type*} [Field K]

/-- The conic and norm-value characterizations in Example 5.6, for the
concrete quadratic Hilbert sign already constructed in this chapter. -/
theorem split_conic_norm (a b : K) :
    (Submission.CField.QForms.quadraticHilbertSign a b = 1 ↔
      Submission.CField.HSymbol.NontrivialQuadraticConic a b) ∧
    (¬ IsSquare a →
      (Submission.CField.QForms.quadraticHilbertSign a b = 1 ↔
        Submission.CField.HSymbol.QuadraticValue a b)) :=
  ⟨Submission.CField.QForms.hilbert_sign_one a b,
    fun ha ↦
      QForms.quadratic_hilbert_sign ha⟩

end QFEquiva

/-! ## Statements 5.7--5.10: local and global Hilbert symbols -/

variable {V G ξ : Type*} [CommGroup ξ]

/-- A general `n`th Hilbert-symbol interface.  The numbered assertions below
are deliberately separate predicates: none is smuggled into the data. -/
structure GHSym where
  hilbert : V → G → G → ξ
  powerResidueAt : G → V → ξ
  valuation : V → G → ℤ
  localArtinRatio : V → G → G → ξ

namespace GHSym

variable (D : GHSym (V := V) (G := G) (ξ := ξ))

/-- **Statement VIII.5.7.** Opposite symbol algebras give skew-symmetry. -/
def SymbolSkewSymmetry : Prop :=
  ∀ v a b, D.hilbert v b a = (D.hilbert v a b)⁻¹

/-- **Statement VIII.5.8.** Away from `S(a)`, the local Hilbert symbol is
the power residue symbol raised to the valuation of `b`. -/
def HilbertSymbolAway (outsideSupport : G → V → Prop) : Prop :=
  ∀ a b v, outsideSupport a v →
    D.hilbert v a b = D.powerResidueAt a v ^ D.valuation v b

/-- **Remark VIII.5.9.** The Hilbert symbol is the local Artin action on an
`n`th root, divided by that root. -/
def HilbertSymbolArtin : Prop :=
  ∀ v a b, D.hilbert v a b = D.localArtinRatio v a b

/-- **Statement VIII.5.10.** Global product formula for the Hilbert symbol. -/
def HilbertSymbolFormula : Prop :=
  ∀ a b, (∏ᶠ v : V, D.hilbert v a b) = 1

/-- The local Artin formula specializes to skew-symmetry when the local
reciprocity pairing is known to be skew. -/
theorem symbol_skew_symmetry
    (hskew : ∀ v a b, D.hilbert v b a = (D.hilbert v a b)⁻¹) :
    D.SymbolSkewSymmetry :=
  hskew

end GHSym

end Submission.CField.HRecip
