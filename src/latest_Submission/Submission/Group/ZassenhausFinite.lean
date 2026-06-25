import Submission.Group.DegreeOneFunctor
import Submission.Group.Zassenhaus
import Submission.Group.FrattiniFunctor
import Submission.Algebra.Linear
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# Finite-rank monotonicity for degree-one quotients

Surjective group homomorphisms induce surjective linear maps on the first
Zassenhaus and mod-`p` Frattini quotients.  This file packages the immediate
finite-rank inequalities, useful when comparing generator ranks of finite
presentations and quotients.
-/

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The first Zassenhaus quotient cannot have larger `ZMod p`-rank after a
surjective group homomorphism. -/
theorem finrank_two_surjective
    {G H : Type*} [Group G] [Group H]
    [Module.Finite (ZMod p) (GroupAlgebra.zTAdditi p G)]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Module.finrank (ZMod p) (GroupAlgebra.zTAdditi p H) ≤
      Module.finrank (ZMod p) (GroupAlgebra.zTAdditi p G) := by
  let f := GroupAlgebra.zTAdditi.mapLinear p G φ
  have hf : Function.Surjective f :=
    GroupAlgebra.zTAdditi.mapLinear_surjective (p := p) (G := G) φ hs
  exact Submission.finrank_surjective f hf

/-- The mod-`p` Frattini quotient cannot have larger `ZMod p`-rank after a
surjective group homomorphism. -/
theorem finrank_frattini_surjective
    {G H : Type*} [Group G] [Group H]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Module.finrank (ZMod p) (mFAdditi p H) ≤
      Module.finrank (ZMod p) (mFAdditi p G) := by
  let f := mFAdditi.mapLinear (p := p) φ
  have hf : Function.Surjective f :=
    mFAdditi.mapLinear_surjective (p := p) φ hs
  exact Submission.finrank_surjective f hf

end Submission

namespace Submission

variable (p : ℕ) [Fact p.Prime]

/-- A surjection with kernel in the source mod-`p` Frattini subgroup preserves the
rank of the mod-`p` Frattini quotient. -/
theorem finrank_frattini_ker
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hs : Function.Surjective φ)
    (hker : φ.ker ≤ modPFrattini p G) :
    Module.finrank (ZMod p) (mFAdditi p G) =
      Module.finrank (ZMod p) (mFAdditi p H) := by
  exact Submission.eq_of_bijective
    (mFAdditi.mapLinear (p := p) φ)
    (mFAdditi.maplin_bijsurj_kerle
      (p := p) φ hs hker)

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- Under the degree-one reverse inclusion in the target, a surjection with kernel
in the source `D₂` preserves the rank of the first Zassenhaus quotient. -/
theorem finrank_surjective_ker
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hs : Function.Surjective φ)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : φ.ker ≤ zSubgro p G 2) :
    Module.finrank (ZMod p) (zTAdditi p G) =
      Module.finrank (ZMod p) (zTAdditi p H) := by
  exact Submission.eq_of_bijective
    (zTAdditi.mapLinear p G φ)
    (zTAdditi.maplin_bijsurj_kerle
      (p := p) φ hs hHrev hker)

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- Rank-nullity for the linear map on mod-`p` Frattini quotients induced by a surjection. -/
theorem rank_nullity_surjective
    {G H : Type*} [Group G] [Group H]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Module.finrank (ZMod p) (mFAdditi p G) =
      Module.finrank (ZMod p) (mFAdditi p H) +
        Module.finrank (ZMod p)
          (LinearMap.ker (mFAdditi.mapLinear (p := p) φ)) := by
  exact Submission.finrank_ker_surjective
    (mFAdditi.mapLinear (p := p) φ)
    (mFAdditi.mapLinear_surjective (p := p) φ hs)

/-- Rank-nullity for the linear map on first Zassenhaus quotients induced by a surjection. -/
theorem finrank_nullity_surjective
    {G H : Type*} [Group G] [Group H]
    [Module.Finite (ZMod p) (GroupAlgebra.zTAdditi p G)]
    (φ : G →* H) (hs : Function.Surjective φ) :
    Module.finrank (ZMod p) (GroupAlgebra.zTAdditi p G) =
      Module.finrank (ZMod p) (GroupAlgebra.zTAdditi p H) +
        Module.finrank (ZMod p)
          (LinearMap.ker (GroupAlgebra.zTAdditi.mapLinear p G φ)) := by
  exact Submission.finrank_ker_surjective
    (GroupAlgebra.zTAdditi.mapLinear p G φ)
    (GroupAlgebra.zTAdditi.mapLinear_surjective (p := p) (G := G) φ hs)

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- A split epimorphism satisfying the layer kernel-intersection criterion preserves
finite rank of the corresponding prime Zassenhaus layer. -/
theorem finrank_right_inverse
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ : H →* G)
    (hσ : Function.RightInverse σ φ) (n : ℕ)
    (hker : φ.ker ⊓ zSubgro p G n ≤ zSubgro p G (n + 1)) :
    Module.finrank (ZMod p) (Additive (zLKern p G n)) =
      Module.finrank (ZMod p) (Additive (zLKern p H n)) :=
  LinearEquiv.finrank_eq
    (zLKern.rinvLinearEquiv p G φ σ hσ hker)

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- Finite-dimensionality of consecutive Zassenhaus quotients is preserved by products. -/
theorem module_finite_next
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Module.Finite (ZMod p)
      (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) := by
  exact Module.Finite.equiv (zNQuot.prodLinearEquiv p G H n).symm

/-- Finite rank is additive for consecutive Zassenhaus quotients of products. -/
theorem finrank_zassenhaus_next
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Module.finrank (ZMod p)
      (Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)) =
      Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  let e := zNQuot.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p)
      (Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)) :=
    Module.Finite.equiv e.symm
  calc
    Module.finrank (ZMod p)
        (Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)) =
        Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
            Additive (zSubgro p H n ⧸ zNTerm p H n)) := e.finrank_eq
    _ = _ := by rw [Module.finrank_prod]

/-- Finite-dimensionality of Zassenhaus layer kernels is preserved by products. -/
theorem module_layer_kernel
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))] :
    Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) := by
  exact Module.Finite.equiv (zLKern.prodLinearEquiv p G H n).symm

/-- Finite rank is additive for Zassenhaus layer kernels of products. -/
theorem finrank_zassenhaus_prod
    (G H : Type*) [Group G] [Group H] (n : ℕ)
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))] :
    Module.finrank (ZMod p) (Additive (zLKern p (G × H) n)) =
      Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n)) := by
  let e := zLKern.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) :=
    Module.Finite.equiv e.symm
  calc
    Module.finrank (ZMod p) (Additive (zLKern p (G × H) n)) =
        Module.finrank (ZMod p)
          (Additive (zLKern p G n) × Additive (zLKern p H n)) :=
      e.finrank_eq
    _ = _ := by rw [Module.finrank_prod]

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- `Nat.card = p^finrank` for a finite-dimensional Zassenhaus layer kernel (additive form). -/
theorem card_additive_finrank
    (G : Type*) [Group G] (n : ℕ)
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Nat.card (Additive (zLKern p G n)) =
      p ^ Module.finrank (ZMod p) (Additive (zLKern p G n)) := by
  simpa [ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Additive (zLKern p G n)))

/-- `Nat.card = p^finrank` for a finite-dimensional Zassenhaus layer kernel. -/
theorem nat_pow_finrank
    (G : Type*) [Group G] (n : ℕ)
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Nat.card (zLKern p G n) =
      p ^ Module.finrank (ZMod p) (Additive (zLKern p G n)) := by
  simpa using card_additive_finrank (p := p) G n

/-- `Nat.card = p^finrank` for a finite-dimensional consecutive Zassenhaus quotient
(additive form). -/
theorem nat_next_additive
    (G : Type*) [Group G] (n : ℕ)
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Nat.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) =
      p ^ Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  simpa [ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Additive (zSubgro p G n ⧸ zNTerm p G n)))

/-- `Nat.card = p^finrank` for a finite-dimensional consecutive Zassenhaus quotient. -/
theorem next_pow_finrank
    (G : Type*) [Group G] (n : ℕ)
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Nat.card (zSubgro p G n ⧸ zNTerm p G n) =
      p ^ Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  simpa using nat_next_additive (p := p) G n

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- `Nat.card` multiplicativity for product Zassenhaus layer kernels. -/
theorem nat_kernel_prod :
    Nat.card (zLKern p (G × H) n) =
      Nat.card (zLKern p G n) * Nat.card (zLKern p H n) := by
  calc
    Nat.card (zLKern p (G × H) n) =
        Nat.card (zLKern p G n × zLKern p H n) :=
      Nat.card_congr (zLKern.prodEquiv p G H n).toEquiv
    _ = _ := Nat.card_prod _ _

/-- Additive `Nat.card` multiplicativity for product Zassenhaus layer kernels. -/
theorem nat_card_prod [Fact p.Prime] :
    Nat.card (Additive (zLKern p (G × H) n)) =
      Nat.card (Additive (zLKern p G n)) *
        Nat.card (Additive (zLKern p H n)) := by
  calc
    Nat.card (Additive (zLKern p (G × H) n)) =
        Nat.card (Additive (zLKern p G n) ×
          Additive (zLKern p H n)) :=
      Nat.card_congr (zLKern.prodAddEquiv p G H n).toEquiv
    _ = _ := Nat.card_prod _ _

/-- `Nat.card` multiplicativity for product consecutive Zassenhaus quotients. -/
theorem nat_zassenhaus_prod :
    Nat.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) =
      Nat.card (zSubgro p G n ⧸ zNTerm p G n) *
        Nat.card (zSubgro p H n ⧸ zNTerm p H n) := by
  calc
    Nat.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) =
        Nat.card ((zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n)) :=
      Nat.card_congr (zNQuot.prodEquiv p G H n).toEquiv
    _ = _ := Nat.card_prod _ _

/-- Additive `Nat.card` multiplicativity for product consecutive Zassenhaus quotients. -/
theorem nat_card_next [Fact p.Prime] :
    Nat.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) =
      Nat.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) *
        Nat.card (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  calc
    Nat.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) =
        Nat.card (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
          Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
      Nat.card_congr (zNQuot.prodAddEquiv p G H n).toEquiv
    _ = _ := Nat.card_prod _ _

end Submission

namespace Submission

open GroupAlgebra

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Product layer-kernel cardinality in summed-finrank form (additive type). -/
theorem nat_card_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))] :
    Nat.card (Additive (zLKern p (G × H) n)) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n))) := by
  letI : Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) :=
    module_layer_kernel (p := p) G H n
  rw [card_additive_finrank (p := p) (G × H) n,
    finrank_zassenhaus_prod (p := p) G H n]

/-- Product layer-kernel cardinality in summed-finrank form. -/
theorem nat_add_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))] :
    Nat.card (zLKern p (G × H) n) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n))) := by
  simpa using
    nat_card_finrank (p := p) G H n

/-- Product consecutive-quotient cardinality in summed-finrank form (additive type). -/
theorem next_additive_finrank
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Nat.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n))) := by
  letI : Module.Finite (ZMod p)
      (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) :=
    module_finite_next (p := p) G H n
  rw [nat_next_additive (p := p) (G × H) n,
    finrank_zassenhaus_next (p := p) G H n]

/-- Product consecutive-quotient cardinality in summed-finrank form. -/
theorem next_prod_finrank
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Nat.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n))) := by
  simpa using
    next_additive_finrank (p := p) G H n

end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Canonical fintype on a product Zassenhaus layer kernel from factor fintypes. -/
@[reducible] noncomputable def fintype_zassenhaus_kernel
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)] :
    Fintype (zLKern p (G × H) n) := by
  exact Fintype.ofEquiv (zLKern p G n × zLKern p H n)
    (zLKern.prodEquiv p G H n).symm.toEquiv

/-- Cardinality of the canonical product fintype on Zassenhaus layer kernels. -/
theorem fintype_card_layer
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)] :
    @Fintype.card (zLKern p (G × H) n)
        (fintype_zassenhaus_kernel p G H n) =
      Fintype.card (zLKern p G n) *
        Fintype.card (zLKern p H n) := by
  letI : Fintype (zLKern p (G × H) n) :=
    fintype_zassenhaus_kernel p G H n
  rw [Fintype.card_congr (zLKern.prodEquiv p G H n).toEquiv]
  exact Fintype.card_prod _ _

/-- Canonical fintype on a product consecutive Zassenhaus quotient from factor fintypes. -/
@[reducible] noncomputable def zassenhaus_next_quotient
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)] :
    Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) := by
  exact Fintype.ofEquiv
    ((zSubgro p G n ⧸ zNTerm p G n) ×
      (zSubgro p H n ⧸ zNTerm p H n))
    (zNQuot.prodEquiv p G H n).symm.toEquiv

/-- Cardinality of the canonical product fintype on consecutive Zassenhaus quotients. -/
theorem fintype_card_zassenhaus
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)] :
    @Fintype.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)
        (zassenhaus_next_quotient p G H n) =
      Fintype.card (zSubgro p G n ⧸ zNTerm p G n) *
        Fintype.card (zSubgro p H n ⧸ zNTerm p H n) := by
  letI : Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :=
    zassenhaus_next_quotient p G H n
  rw [Fintype.card_congr (zNQuot.prodEquiv p G H n).toEquiv]
  exact Fintype.card_prod _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Canonical fintype on an additive product Zassenhaus layer kernel from factor fintypes. -/
@[reducible] noncomputable def zassenhaus_additive_prod
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))] :
    Fintype (Additive (zLKern p (G × H) n)) := by
  exact Fintype.ofEquiv
    (Additive (zLKern p G n) × Additive (zLKern p H n))
    (zLKern.prodAddEquiv p G H n).symm.toEquiv

/-- Cardinality of the canonical additive product fintype on Zassenhaus layer kernels. -/
theorem fintype_kernel_additive
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))] :
    @Fintype.card (Additive (zLKern p (G × H) n))
        (zassenhaus_additive_prod p G H n) =
      Fintype.card (Additive (zLKern p G n)) *
        Fintype.card (Additive (zLKern p H n)) := by
  letI : Fintype (Additive (zLKern p (G × H) n)) :=
    zassenhaus_additive_prod p G H n
  rw [Fintype.card_congr (zLKern.prodAddEquiv p G H n).toEquiv]
  exact Fintype.card_prod _ _

/-- Canonical fintype on an additive product consecutive Zassenhaus quotient. -/
@[reducible] noncomputable def fintype_zassenhaus_additive
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) := by
  exact Fintype.ofEquiv
    (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
      Additive (zSubgro p H n ⧸ zNTerm p H n))
    (zNQuot.prodAddEquiv p G H n).symm.toEquiv

/-- Cardinality of the canonical additive product fintype on consecutive quotients. -/
theorem fintype_card_additive
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    @Fintype.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n))
        (fintype_zassenhaus_additive p G H n) =
      Fintype.card (Additive (zSubgro p G n ⧸
        zNTerm p G n)) *
        Fintype.card (Additive (zSubgro p H n ⧸
          zNTerm p H n)) := by
  letI : Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
    fintype_zassenhaus_additive p G H n
  rw [Fintype.card_congr (zNQuot.prodAddEquiv p G H n).toEquiv]
  exact Fintype.card_prod _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable {p : ℕ} (G : Type*) [Group G] (n : ℕ)

/-- A finite-dimensional additive Zassenhaus layer kernel is finite as a type. -/
theorem layer_additive_module [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Finite (Additive (zLKern p G n)) := by
  have hcard := card_additive_finrank (p := p) G n
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpos : 0 < Nat.card (Additive (zLKern p G n)) := by
    rw [hcard]
    exact pow_pos hp _
  exact (Nat.card_pos_iff.mp hpos).2

/-- A finite-dimensional Zassenhaus layer kernel is finite in multiplicative form. -/
theorem layer_kernel_module [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Finite (zLKern p G n) := by
  haveI : Finite (Additive (zLKern p G n)) :=
    layer_additive_module (p := p) G n
  exact Finite.of_equiv (Additive (zLKern p G n)) Additive.ofMul.symm

/-- Canonical fintype on an additive layer kernel from finite-dimensionality. -/
@[reducible] noncomputable def fintype_layer_module
    [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Fintype (Additive (zLKern p G n)) := by
  classical
  haveI : Finite (Additive (zLKern p G n)) :=
    layer_additive_module (p := p) G n
  exact Fintype.ofFinite _

/-- Canonical fintype on a layer kernel from finite-dimensionality. -/
@[reducible] noncomputable def fintype_zassenhaus_module
    [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    Fintype (zLKern p G n) := by
  classical
  haveI : Finite (zLKern p G n) :=
    layer_kernel_module (p := p) G n
  exact Fintype.ofFinite _

/-- `Fintype.card` form for the canonical additive layer-kernel fintype. -/
theorem fintype_additive_module [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    @Fintype.card (Additive (zLKern p G n))
        (fintype_layer_module (p := p) G n) =
      p ^ Module.finrank (ZMod p) (Additive (zLKern p G n)) := by
  have h := card_additive_finrank (p := p) G n
  rw [@Nat.card_eq_fintype_card (Additive (zLKern p G n))
    (fintype_layer_module (p := p) G n)] at h
  exact h

/-- `Fintype.card` form for the canonical layer-kernel fintype. -/
theorem fintype_card_module [Fact p.Prime]
    [Module.Finite (ZMod p) (Additive (zLKern p G n))] :
    @Fintype.card (zLKern p G n)
        (fintype_zassenhaus_module (p := p) G n) =
      p ^ Module.finrank (ZMod p) (Additive (zLKern p G n)) := by
  have h := nat_pow_finrank (p := p) G n
  rw [@Nat.card_eq_fintype_card (zLKern p G n)
    (fintype_zassenhaus_module (p := p) G n)] at h
  exact h

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable {p : ℕ} (G : Type*) [Group G] (n : ℕ)

/-- A finite-dimensional additive consecutive Zassenhaus quotient is finite as a type. -/
theorem zassenhaus_next_module [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Finite (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  have hcard := nat_next_additive (p := p) G n
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpos : 0 < Nat.card
      (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
    rw [hcard]
    exact pow_pos hp _
  exact (Nat.card_pos_iff.mp hpos).2

/-- A finite-dimensional consecutive Zassenhaus quotient is finite in multiplicative form. -/
theorem finite_next_module [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Finite (zSubgro p G n ⧸ zNTerm p G n) := by
  haveI : Finite
      (Additive (zSubgro p G n ⧸ zNTerm p G n)) :=
    zassenhaus_next_module (p := p) G n
  exact Finite.of_equiv
    (Additive (zSubgro p G n ⧸ zNTerm p G n))
    Additive.ofMul.symm

/-- Canonical fintype on an additive consecutive quotient from finite-dimensionality. -/
@[reducible] noncomputable def next_additive_module
    [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  classical
  haveI : Finite
      (Additive (zSubgro p G n ⧸ zNTerm p G n)) :=
    zassenhaus_next_module (p := p) G n
  exact Fintype.ofFinite _

/-- Canonical fintype on a consecutive quotient from finite-dimensionality. -/
@[reducible] noncomputable def fintype_next_finite
    [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    Fintype (zSubgro p G n ⧸ zNTerm p G n) := by
  classical
  haveI : Finite (zSubgro p G n ⧸ zNTerm p G n) :=
    finite_next_module (p := p) G n
  exact Fintype.ofFinite _

/-- `Fintype.card` form for the canonical additive consecutive-quotient fintype. -/
theorem fintype_next_module [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    @Fintype.card
        (Additive (zSubgro p G n ⧸ zNTerm p G n))
        (next_additive_module (p := p) G n) =
      p ^ Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  have h := nat_next_additive (p := p) G n
  rw [@Nat.card_eq_fintype_card
    (Additive (zSubgro p G n ⧸ zNTerm p G n))
    (next_additive_module (p := p) G n)] at h
  exact h

/-- `Fintype.card` form for the canonical consecutive-quotient fintype. -/
theorem fintype_card_next [Fact p.Prime]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))] :
    @Fintype.card (zSubgro p G n ⧸ zNTerm p G n)
        (fintype_next_finite (p := p) G n) =
      p ^ Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  have h := next_pow_finrank (p := p) G n
  rw [@Nat.card_eq_fintype_card
    (zSubgro p G n ⧸ zNTerm p G n)
    (fintype_next_finite (p := p) G n)] at h
  exact h

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of Zassenhaus layer kernels is preserved by products. -/
theorem finite_layer_prod
    [Finite (zLKern p G n)] [Finite (zLKern p H n)] :
    Finite (zLKern p (G × H) n) := by
  exact Finite.of_equiv (zLKern p G n × zLKern p H n)
    (zLKern.prodEquiv p G H n).symm.toEquiv

/-- Finiteness of a product layer kernel implies finiteness of the left factor. -/
theorem layer_left_prod
    [Finite (zLKern p (G × H) n)] :
    Finite (zLKern p G n) := by
  haveI : Finite (zLKern p G n × zLKern p H n) :=
    Finite.of_equiv _ (zLKern.prodEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : zLKern p G n × zLKern p H n => z.1)
    (by intro x; exact ⟨(x, 1), rfl⟩)

/-- Finiteness of a product layer kernel implies finiteness of the right factor. -/
theorem layer_right_prod
    [Finite (zLKern p (G × H) n)] :
    Finite (zLKern p H n) := by
  haveI : Finite (zLKern p G n × zLKern p H n) :=
    Finite.of_equiv _ (zLKern.prodEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : zLKern p G n × zLKern p H n => z.2)
    (by intro y; exact ⟨(1, y), rfl⟩)

/-- A product layer kernel is finite iff both factor layer kernels are finite. -/
theorem zassenhaus_layer_prod :
    Finite (zLKern p (G × H) n) ↔
      Finite (zLKern p G n) ∧ Finite (zLKern p H n) := by
  constructor
  · intro h
    letI := h
    exact ⟨layer_left_prod p G H n,
      layer_right_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact finite_layer_prod p G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of consecutive Zassenhaus quotients is preserved by products. -/
theorem finite_zassenhaus_prod
    [Finite (zSubgro p G n ⧸ zNTerm p G n)]
    [Finite (zSubgro p H n ⧸ zNTerm p H n)] :
    Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) := by
  exact Finite.of_equiv
    ((zSubgro p G n ⧸ zNTerm p G n) ×
      (zSubgro p H n ⧸ zNTerm p H n))
    (zNQuot.prodEquiv p G H n).symm.toEquiv

/-- Finiteness of a product consecutive quotient implies finiteness of the left factor. -/
theorem zassenhaus_next_left
    [Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)] :
    Finite (zSubgro p G n ⧸ zNTerm p G n) := by
  haveI : Finite ((zSubgro p G n ⧸ zNTerm p G n) ×
      (zSubgro p H n ⧸ zNTerm p H n)) :=
    Finite.of_equiv _ (zNQuot.prodEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : (zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n) => z.1)
    (by intro x; exact ⟨(x, 1), rfl⟩)

/-- Finiteness of a product consecutive quotient implies finiteness of the right factor. -/
theorem next_quotient_prod
    [Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)] :
    Finite (zSubgro p H n ⧸ zNTerm p H n) := by
  haveI : Finite ((zSubgro p G n ⧸ zNTerm p G n) ×
      (zSubgro p H n ⧸ zNTerm p H n)) :=
    Finite.of_equiv _ (zNQuot.prodEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : (zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n) => z.2)
    (by intro y; exact ⟨(1, y), rfl⟩)

/-- A product consecutive quotient is finite iff both factor quotients are finite. -/
theorem finite_zassenhaus_next :
    Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) ↔
      Finite (zSubgro p G n ⧸ zNTerm p G n) ∧
        Finite (zSubgro p H n ⧸ zNTerm p H n) := by
  constructor
  · intro h
    letI := h
    exact ⟨zassenhaus_next_left p G H n,
      next_quotient_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact finite_zassenhaus_prod p G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of additive Zassenhaus layer kernels is preserved by products. -/
theorem finite_additive_prod
    [Finite (Additive (zLKern p G n))]
    [Finite (Additive (zLKern p H n))] :
    Finite (Additive (zLKern p (G × H) n)) := by
  exact Finite.of_equiv
    (Additive (zLKern p G n) × Additive (zLKern p H n))
    (zLKern.prodAddEquiv p G H n).symm.toEquiv

/-- Finiteness of an additive product layer kernel implies finiteness of the left factor. -/
theorem additive_left_prod
    [Finite (Additive (zLKern p (G × H) n))] :
    Finite (Additive (zLKern p G n)) := by
  haveI : Finite (Additive (zLKern p G n) ×
      Additive (zLKern p H n)) :=
    Finite.of_equiv _ (zLKern.prodAddEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : Additive (zLKern p G n) ×
        Additive (zLKern p H n) => z.1)
    (by intro x; exact ⟨(x, 0), rfl⟩)

/-- Finiteness of an additive product layer kernel implies finiteness of the right factor. -/
theorem additive_right_prod
    [Finite (Additive (zLKern p (G × H) n))] :
    Finite (Additive (zLKern p H n)) := by
  haveI : Finite (Additive (zLKern p G n) ×
      Additive (zLKern p H n)) :=
    Finite.of_equiv _ (zLKern.prodAddEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : Additive (zLKern p G n) ×
        Additive (zLKern p H n) => z.2)
    (by intro y; exact ⟨(0, y), rfl⟩)

/-- An additive product layer kernel is finite iff both factor layer kernels are finite. -/
theorem kernel_additive_prod :
    Finite (Additive (zLKern p (G × H) n)) ↔
      Finite (Additive (zLKern p G n)) ∧
        Finite (Additive (zLKern p H n)) := by
  constructor
  · intro h
    letI := h
    exact ⟨additive_left_prod p G H n,
      additive_right_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact finite_additive_prod p G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of additive consecutive Zassenhaus quotients is preserved by products. -/
theorem zassenhaus_next_additive
    [Finite (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Finite (Additive (zSubgro p H n ⧸ zNTerm p H n))] :
    Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) := by
  exact Finite.of_equiv
    (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
      Additive (zSubgro p H n ⧸ zNTerm p H n))
    (zNQuot.prodAddEquiv p G H n).symm.toEquiv

/-- Finiteness of an additive product consecutive quotient implies finiteness of the left factor. -/
theorem next_left_prod
    [Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Finite (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  haveI : Finite (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
      Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
    Finite.of_equiv _ (zNQuot.prodAddEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n) => z.1)
    (by intro x; exact ⟨(x, 0), rfl⟩)

/-- Finiteness of an additive product consecutive quotient implies finiteness of the
right factor. -/
theorem next_right_prod
    [Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Finite (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  haveI : Finite (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
      Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
    Finite.of_equiv _ (zNQuot.prodAddEquiv p G H n).toEquiv
  exact Finite.of_surjective
    (fun z : Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n) => z.2)
    (by intro y; exact ⟨(0, y), rfl⟩)

/-- An additive product consecutive quotient is finite iff both factor quotients are finite. -/
theorem zassenhaus_next_prod :
    Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) ↔
      Finite (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Finite (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  constructor
  · intro h
    letI := h
    exact ⟨next_left_prod p G H n,
      next_right_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact zassenhaus_next_additive p G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- A fintype on a product layer kernel induces a canonical fintype on the left factor. -/
@[reducible] noncomputable def fintype_kernel_left
    [Fintype (zLKern p (G × H) n)] :
    Fintype (zLKern p G n) := by
  haveI : Finite (zLKern p (G × H) n) := Fintype.finite (inferInstance)
  haveI : Finite (zLKern p G n) :=
    layer_left_prod p G H n
  exact Fintype.ofFinite _

/-- A fintype on a product layer kernel induces a canonical fintype on the right factor. -/
@[reducible] noncomputable def fintype_zassenhaus_layer
    [Fintype (zLKern p (G × H) n)] :
    Fintype (zLKern p H n) := by
  haveI : Finite (zLKern p (G × H) n) := Fintype.finite (inferInstance)
  haveI : Finite (zLKern p H n) :=
    layer_right_prod p G H n
  exact Fintype.ofFinite _

/-- A fintype on a product consecutive quotient induces a canonical fintype on the left factor. -/
@[reducible] noncomputable def fintype_quotient_prod
    [Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)] :
    Fintype (zSubgro p G n ⧸ zNTerm p G n) := by
  haveI : Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) := Fintype.finite (inferInstance)
  haveI : Finite (zSubgro p G n ⧸ zNTerm p G n) :=
    zassenhaus_next_left p G H n
  exact Fintype.ofFinite _

/-- A fintype on a product consecutive quotient induces a canonical fintype on the right factor. -/
@[reducible] noncomputable def fintype_next_quotient
    [Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)] :
    Fintype (zSubgro p H n ⧸ zNTerm p H n) := by
  haveI : Finite (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) := Fintype.finite (inferInstance)
  haveI : Finite (zSubgro p H n ⧸ zNTerm p H n) :=
    next_quotient_prod p G H n
  exact Fintype.ofFinite _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- A fintype on an additive product layer kernel induces a canonical fintype on the left factor. -/
@[reducible] noncomputable def fintype_layer_prod
    [Fintype (Additive (zLKern p (G × H) n))] :
    Fintype (Additive (zLKern p G n)) := by
  haveI : Finite (Additive (zLKern p (G × H) n)) :=
    Fintype.finite (inferInstance)
  haveI : Finite (Additive (zLKern p G n)) :=
    additive_left_prod p G H n
  exact Fintype.ofFinite _

/-- A fintype on an additive product layer kernel induces a canonical fintype on the
right factor. -/
@[reducible] noncomputable def fintype_right_prod
    [Fintype (Additive (zLKern p (G × H) n))] :
    Fintype (Additive (zLKern p H n)) := by
  haveI : Finite (Additive (zLKern p (G × H) n)) :=
    Fintype.finite (inferInstance)
  haveI : Finite (Additive (zLKern p H n)) :=
    additive_right_prod p G H n
  exact Fintype.ofFinite _

/-- A fintype on an additive product consecutive quotient induces a canonical fintype on the
left factor. -/
@[reducible] noncomputable def fintype_left_prod
    [Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  haveI : Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) := Fintype.finite (inferInstance)
  haveI : Finite (Additive (zSubgro p G n ⧸
      zNTerm p G n)) :=
    next_left_prod p G H n
  exact Fintype.ofFinite _

/-- A fintype on an additive product consecutive quotient induces a canonical fintype on the
right factor. -/
@[reducible] noncomputable def fintype_additive_prod
    [Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  haveI : Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) := Fintype.finite (inferInstance)
  haveI : Finite (Additive (zSubgro p H n ⧸
      zNTerm p H n)) :=
    next_right_prod p G H n
  exact Fintype.ofFinite _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finite-dimensionality of a product layer kernel implies finite-dimensionality of the
left factor. -/
theorem module_kernel_prod
    [Module.Finite (ZMod p) (Additive (zLKern p (G × H) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p G n)) := by
  let e := zLKern.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p)
      (Additive (zLKern p G n) × Additive (zLKern p H n)) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.fst (ZMod p) (Additive (zLKern p G n))
      (Additive (zLKern p H n)))
    (by intro x; exact ⟨(x, 0), rfl⟩)

/-- Finite-dimensionality of a product layer kernel implies finite-dimensionality of the
right factor. -/
theorem module_zassenhaus_prod
    [Module.Finite (ZMod p) (Additive (zLKern p (G × H) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p H n)) := by
  let e := zLKern.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p)
      (Additive (zLKern p G n) × Additive (zLKern p H n)) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.snd (ZMod p) (Additive (zLKern p G n))
      (Additive (zLKern p H n)))
    (by intro y; exact ⟨(0, y), rfl⟩)

/-- Product layer kernels are finite-dimensional iff both factor layer kernels are. -/
theorem module_zassenhaus_layer :
    Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) ↔
      Module.Finite (ZMod p) (Additive (zLKern p G n)) ∧
        Module.Finite (ZMod p) (Additive (zLKern p H n)) := by
  constructor
  · intro h
    letI := h
    exact ⟨module_kernel_prod p G H n,
      module_zassenhaus_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact module_layer_kernel (p := p) G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finite-dimensionality of a product consecutive quotient implies finite-dimensionality of the
left factor. -/
theorem module_left_prod
    [Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  let e := zNQuot.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.fst (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))
      (Additive (zSubgro p H n ⧸ zNTerm p H n)))
    (by intro x; exact ⟨(x, 0), rfl⟩)

/-- Finite-dimensionality of a product consecutive quotient implies finite-dimensionality of the
right factor. -/
theorem module_right_prod
    [Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  let e := zNQuot.prodLinearEquiv p G H n
  haveI : Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.snd (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))
      (Additive (zSubgro p H n ⧸ zNTerm p H n)))
    (by intro y; exact ⟨(0, y), rfl⟩)

/-- Product consecutive quotients are finite-dimensional iff both factor quotients are. -/
theorem module_quotient_prod :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) ↔
      Module.Finite (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Module.Finite (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) := by
  constructor
  · intro h
    letI := h
    exact ⟨module_left_prod p G H n,
      module_right_prod p G H n⟩
  · intro h
    letI := h.1
    letI := h.2
    exact module_finite_next (p := p) G H n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Left-nested product layer kernels are finite-dimensional iff all three factors are. -/
theorem module_layer_prod :
    Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n)) ↔
      Module.Finite (ZMod p) (Additive (zLKern p G n)) ∧
        Module.Finite (ZMod p) (Additive (zLKern p H n)) ∧
          Module.Finite (ZMod p) (Additive (zLKern p K n)) := by
  rw [module_zassenhaus_layer (p := p) (G × H) K n,
    module_zassenhaus_layer (p := p) G H n]
  exact and_assoc

/-- Right-nested product layer kernels are finite-dimensional iff all three factors are. -/
theorem module_prod_nested :
    Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n)) ↔
      Module.Finite (ZMod p) (Additive (zLKern p G n)) ∧
        Module.Finite (ZMod p) (Additive (zLKern p H n)) ∧
          Module.Finite (ZMod p) (Additive (zLKern p K n)) := by
  rw [module_zassenhaus_layer (p := p) G (H × K) n,
    module_zassenhaus_layer (p := p) H K n]

/-- Left-nested consecutive quotients are finite-dimensional iff all three factors are. -/
theorem module_next_prod :
    Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) ↔
      Module.Finite (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Module.Finite (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) ∧
          Module.Finite (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [module_quotient_prod (p := p) (G × H) K n,
    module_quotient_prod (p := p) G H n]
  exact and_assoc

/-- Right-nested consecutive quotients are finite-dimensional iff all three factors are. -/
theorem module_next_nested :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) ↔
      Module.Finite (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Module.Finite (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) ∧
          Module.Finite (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [module_quotient_prod (p := p) G (H × K) n,
    module_quotient_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Finrank of a left-nested product layer kernel is the sum of the three factor finranks. -/
theorem finrank_layer_prod
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Module.finrank (ZMod p) (Additive (zLKern p ((G × H) × K) n)) =
      Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n)) := by
  haveI : Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) :=
    module_layer_kernel (p := p) G H n
  rw [finrank_zassenhaus_prod (p := p) (G × H) K n,
    finrank_zassenhaus_prod (p := p) G H n]

/-- Finrank of a right-nested product layer kernel is the sum of the three factor finranks. -/
theorem finrank_prod_nested
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Module.finrank (ZMod p) (Additive (zLKern p (G × (H × K)) n)) =
      Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        (Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n))) := by
  haveI : Module.Finite (ZMod p) (Additive (zLKern p (H × K) n)) :=
    module_layer_kernel (p := p) H K n
  rw [finrank_zassenhaus_prod (p := p) G (H × K) n,
    finrank_zassenhaus_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Finrank of a left-nested product consecutive quotient is the sum of factor finranks. -/
theorem finrank_next_prod
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Module.finrank (ZMod p)
        (Additive (zSubgro p ((G × H) × K) n ⧸
          zNTerm p ((G × H) × K) n)) =
      Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  haveI : Module.Finite (ZMod p)
      (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) :=
    module_finite_next (p := p) G H n
  rw [finrank_zassenhaus_next (p := p) (G × H) K n,
    finrank_zassenhaus_next (p := p) G H n]

/-- Finrank of a right-nested product consecutive quotient is the sum of factor finranks. -/
theorem finrank_next_nested
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Module.finrank (ZMod p)
        (Additive (zSubgro p (G × (H × K)) n ⧸
          zNTerm p (G × (H × K)) n)) =
      Module.finrank (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        (Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n))) := by
  haveI : Module.Finite (ZMod p)
      (Additive (zSubgro p (H × K) n ⧸
        zNTerm p (H × K) n)) :=
    module_finite_next (p := p) H K n
  rw [finrank_zassenhaus_next (p := p) G (H × K) n,
    finrank_zassenhaus_next (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- `Nat.card` multiplicativity for left-nested triple layer kernels. -/
theorem nat_layer_prod :
    Nat.card (zLKern p ((G × H) × K) n) =
      Nat.card (zLKern p G n) *
        Nat.card (zLKern p H n) *
          Nat.card (zLKern p K n) := by
  rw [nat_kernel_prod (p := p) (G × H) K n,
    nat_kernel_prod (p := p) G H n]

/-- `Nat.card` multiplicativity for right-nested triple layer kernels. -/
theorem nat_prod_nested :
    Nat.card (zLKern p (G × (H × K)) n) =
      Nat.card (zLKern p G n) *
        (Nat.card (zLKern p H n) *
          Nat.card (zLKern p K n)) := by
  rw [nat_kernel_prod (p := p) G (H × K) n,
    nat_kernel_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Additive `Nat.card` multiplicativity for left-nested triple layer kernels. -/
theorem nat_additive_prod :
    Nat.card (Additive (zLKern p ((G × H) × K) n)) =
      Nat.card (Additive (zLKern p G n)) *
        Nat.card (Additive (zLKern p H n)) *
          Nat.card (Additive (zLKern p K n)) := by
  rw [nat_card_prod (p := p) (G × H) K n,
    nat_card_prod (p := p) G H n]

/-- Additive `Nat.card` multiplicativity for right-nested triple layer kernels. -/
theorem nat_card_nested :
    Nat.card (Additive (zLKern p (G × (H × K)) n)) =
      Nat.card (Additive (zLKern p G n)) *
        (Nat.card (Additive (zLKern p H n)) *
          Nat.card (Additive (zLKern p K n))) := by
  rw [nat_card_prod (p := p) G (H × K) n,
    nat_card_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- `Nat.card` multiplicativity for left-nested triple consecutive quotients. -/
theorem nat_zassenhaus_next :
    Nat.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n) =
      Nat.card (zSubgro p G n ⧸ zNTerm p G n) *
        Nat.card (zSubgro p H n ⧸ zNTerm p H n) *
          Nat.card (zSubgro p K n ⧸ zNTerm p K n) := by
  rw [nat_zassenhaus_prod (p := p) (G × H) K n,
    nat_zassenhaus_prod (p := p) G H n]

/-- `Nat.card` multiplicativity for right-nested triple consecutive quotients. -/
theorem card_next_nested :
    Nat.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) =
      Nat.card (zSubgro p G n ⧸ zNTerm p G n) *
        (Nat.card (zSubgro p H n ⧸ zNTerm p H n) *
          Nat.card (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [nat_zassenhaus_prod (p := p) G (H × K) n,
    nat_zassenhaus_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Additive `Nat.card` multiplicativity for left-nested triple consecutive quotients. -/
theorem nat_next_prod :
    Nat.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)) =
      Nat.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) *
        Nat.card (Additive (zSubgro p H n ⧸ zNTerm p H n)) *
          Nat.card (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [nat_card_next (p := p) (G × H) K n,
    nat_card_next (p := p) G H n]

/-- Additive `Nat.card` multiplicativity for right-nested triple consecutive quotients. -/
theorem nat_additive_nested :
    Nat.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)) =
      Nat.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) *
        (Nat.card (Additive (zSubgro p H n ⧸ zNTerm p H n)) *
          Nat.card (Additive (zSubgro p K n ⧸ zNTerm p K n))) := by
  rw [nat_card_next (p := p) G (H × K) n,
    nat_card_next (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Left-nested product layer kernels are finite iff all three factor kernels are finite. -/
theorem layer_kernel_prod :
    Finite (zLKern p ((G × H) × K) n) ↔
      Finite (zLKern p G n) ∧ Finite (zLKern p H n) ∧
        Finite (zLKern p K n) := by
  rw [zassenhaus_layer_prod (p := p) (G × H) K n,
    zassenhaus_layer_prod (p := p) G H n]
  exact and_assoc

/-- Right-nested product layer kernels are finite iff all three factor kernels are finite. -/
theorem layer_prod_nested :
    Finite (zLKern p (G × (H × K)) n) ↔
      Finite (zLKern p G n) ∧ Finite (zLKern p H n) ∧
        Finite (zLKern p K n) := by
  rw [zassenhaus_layer_prod (p := p) G (H × K) n,
    zassenhaus_layer_prod (p := p) H K n]

/-- Left-nested consecutive quotients are finite iff all three factor quotients are finite. -/
theorem finite_next_prod :
    Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) ↔
      Finite (zSubgro p G n ⧸ zNTerm p G n) ∧
        Finite (zSubgro p H n ⧸ zNTerm p H n) ∧
          Finite (zSubgro p K n ⧸ zNTerm p K n) := by
  rw [finite_zassenhaus_next (p := p) (G × H) K n,
    finite_zassenhaus_next (p := p) G H n]
  exact and_assoc

/-- Right-nested consecutive quotients are finite iff all three factor quotients are finite. -/
theorem zassenhaus_next_nested :
    Finite (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) ↔
      Finite (zSubgro p G n ⧸ zNTerm p G n) ∧
        Finite (zSubgro p H n ⧸ zNTerm p H n) ∧
          Finite (zSubgro p K n ⧸ zNTerm p K n) := by
  rw [finite_zassenhaus_next (p := p) G (H × K) n,
    finite_zassenhaus_next (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Left-nested additive layer kernels are finite iff all three factor kernels are finite. -/
theorem layer_additive_prod :
    Finite (Additive (zLKern p ((G × H) × K) n)) ↔
      Finite (Additive (zLKern p G n)) ∧
        Finite (Additive (zLKern p H n)) ∧
          Finite (Additive (zLKern p K n)) := by
  rw [kernel_additive_prod (p := p) (G × H) K n,
    kernel_additive_prod (p := p) G H n]
  exact and_assoc

/-- Right-nested additive layer kernels are finite iff all three factor kernels are finite. -/
theorem additive_prod_nested :
    Finite (Additive (zLKern p (G × (H × K)) n)) ↔
      Finite (Additive (zLKern p G n)) ∧
        Finite (Additive (zLKern p H n)) ∧
          Finite (Additive (zLKern p K n)) := by
  rw [kernel_additive_prod (p := p) G (H × K) n,
    kernel_additive_prod (p := p) H K n]

/-- Left-nested additive consecutive quotients are finite iff all three factors are finite. -/
theorem next_additive_prod :
    Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) ↔
      Finite (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Finite (Additive (zSubgro p H n ⧸ zNTerm p H n)) ∧
          Finite (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [zassenhaus_next_prod (p := p) (G × H) K n,
    zassenhaus_next_prod (p := p) G H n]
  exact and_assoc

/-- Right-nested additive consecutive quotients are finite iff all three factors are finite. -/
theorem next_additive_nested :
    Finite (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) ↔
      Finite (Additive (zSubgro p G n ⧸ zNTerm p G n)) ∧
        Finite (Additive (zSubgro p H n ⧸ zNTerm p H n)) ∧
          Finite (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  rw [zassenhaus_next_prod (p := p) G (H × K) n,
    zassenhaus_next_prod (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Canonical fintype on a left-nested triple product layer kernel. -/
@[reducible] noncomputable def fintype_layer_kernel
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)]
    [Fintype (zLKern p K n)] :
    Fintype (zLKern p ((G × H) × K) n) := by
  letI : Fintype (zLKern p (G × H) n) :=
    fintype_zassenhaus_kernel p G H n
  exact fintype_zassenhaus_kernel p (G × H) K n

/-- Cardinality of the canonical left-nested triple layer-kernel fintype. -/
theorem fintype_kernel_prod
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)]
    [Fintype (zLKern p K n)] :
    @Fintype.card (zLKern p ((G × H) × K) n)
        (fintype_layer_kernel p G H K n) =
      Fintype.card (zLKern p G n) *
        Fintype.card (zLKern p H n) *
          Fintype.card (zLKern p K n) := by
  letI : Fintype (zLKern p (G × H) n) :=
    fintype_zassenhaus_kernel p G H n
  rw [fintype_card_layer (p := p) (G × H) K n]
  rw [fintype_card_layer (p := p) G H n]

/-- Canonical fintype on a right-nested triple product layer kernel. -/
@[reducible] noncomputable def kernel_prod_nested
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)]
    [Fintype (zLKern p K n)] :
    Fintype (zLKern p (G × (H × K)) n) := by
  letI : Fintype (zLKern p (H × K) n) :=
    fintype_zassenhaus_kernel p H K n
  exact fintype_zassenhaus_kernel p G (H × K) n

/-- Cardinality of the canonical right-nested triple layer-kernel fintype. -/
theorem fintype_kernel_nested
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)]
    [Fintype (zLKern p K n)] :
    @Fintype.card (zLKern p (G × (H × K)) n)
        (kernel_prod_nested p G H K n) =
      Fintype.card (zLKern p G n) *
        (Fintype.card (zLKern p H n) *
          Fintype.card (zLKern p K n)) := by
  letI : Fintype (zLKern p (H × K) n) :=
    fintype_zassenhaus_kernel p H K n
  rw [fintype_card_layer (p := p) G (H × K) n]
  rw [fintype_card_layer (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Canonical fintype on a left-nested triple product consecutive quotient. -/
@[reducible] noncomputable def fintype_zassenhaus_quotient
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)]
    [Fintype (zSubgro p K n ⧸ zNTerm p K n)] :
    Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) := by
  letI : Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :=
    zassenhaus_next_quotient p G H n
  exact zassenhaus_next_quotient p (G × H) K n

/-- Cardinality of the canonical left-nested triple consecutive-quotient fintype. -/
theorem card_next_prod
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)]
    [Fintype (zSubgro p K n ⧸ zNTerm p K n)] :
    @Fintype.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)
        (fintype_zassenhaus_quotient p G H K n) =
      Fintype.card (zSubgro p G n ⧸ zNTerm p G n) *
        Fintype.card (zSubgro p H n ⧸ zNTerm p H n) *
          Fintype.card (zSubgro p K n ⧸ zNTerm p K n) := by
  letI : Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :=
    zassenhaus_next_quotient p G H n
  rw [fintype_card_zassenhaus (p := p) (G × H) K n]
  rw [fintype_card_zassenhaus (p := p) G H n]

/-- Canonical fintype on a right-nested triple product consecutive quotient. -/
@[reducible] noncomputable def fintype_quotient_nested
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)]
    [Fintype (zSubgro p K n ⧸ zNTerm p K n)] :
    Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) := by
  letI : Fintype (zSubgro p (H × K) n ⧸
      zNTerm p (H × K) n) :=
    zassenhaus_next_quotient p H K n
  exact zassenhaus_next_quotient p G (H × K) n

/-- Cardinality of the canonical right-nested triple consecutive-quotient fintype. -/
theorem fintype_zassenhaus_nested
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)]
    [Fintype (zSubgro p K n ⧸ zNTerm p K n)] :
    @Fintype.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)
        (fintype_quotient_nested p G H K n) =
      Fintype.card (zSubgro p G n ⧸ zNTerm p G n) *
        (Fintype.card (zSubgro p H n ⧸ zNTerm p H n) *
          Fintype.card (zSubgro p K n ⧸ zNTerm p K n)) := by
  letI : Fintype (zSubgro p (H × K) n ⧸
      zNTerm p (H × K) n) :=
    zassenhaus_next_quotient p H K n
  rw [fintype_card_zassenhaus (p := p) G (H × K) n]
  rw [fintype_card_zassenhaus (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Canonical additive fintype on a left-nested triple product layer kernel. -/
@[reducible] noncomputable def fintype_layer_additive
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))]
    [Fintype (Additive (zLKern p K n))] :
    Fintype (Additive (zLKern p ((G × H) × K) n)) := by
  letI : Fintype (Additive (zLKern p (G × H) n)) :=
    zassenhaus_additive_prod p G H n
  exact zassenhaus_additive_prod p (G × H) K n

/-- Cardinality of the canonical additive left-nested triple layer-kernel fintype. -/
theorem fintype_card_prod
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))]
    [Fintype (Additive (zLKern p K n))] :
    @Fintype.card (Additive (zLKern p ((G × H) × K) n))
        (fintype_layer_additive p G H K n) =
      Fintype.card (Additive (zLKern p G n)) *
        Fintype.card (Additive (zLKern p H n)) *
          Fintype.card (Additive (zLKern p K n)) := by
  letI : Fintype (Additive (zLKern p (G × H) n)) :=
    zassenhaus_additive_prod p G H n
  rw [fintype_kernel_additive (p := p) (G × H) K n]
  rw [fintype_kernel_additive (p := p) G H n]

/-- Canonical additive fintype on a right-nested triple product layer kernel. -/
@[reducible] noncomputable def fintype_layer_nested
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))]
    [Fintype (Additive (zLKern p K n))] :
    Fintype (Additive (zLKern p (G × (H × K)) n)) := by
  letI : Fintype (Additive (zLKern p (H × K) n)) :=
    zassenhaus_additive_prod p H K n
  exact zassenhaus_additive_prod p G (H × K) n

/-- Cardinality of the canonical additive right-nested triple layer-kernel fintype. -/
theorem fintype_card_nested
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))]
    [Fintype (Additive (zLKern p K n))] :
    @Fintype.card (Additive (zLKern p (G × (H × K)) n))
        (fintype_layer_nested p G H K n) =
      Fintype.card (Additive (zLKern p G n)) *
        (Fintype.card (Additive (zLKern p H n)) *
          Fintype.card (Additive (zLKern p K n))) := by
  letI : Fintype (Additive (zLKern p (H × K) n)) :=
    zassenhaus_additive_prod p H K n
  rw [fintype_kernel_additive (p := p) G (H × K) n]
  rw [fintype_kernel_additive (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Canonical additive fintype on a left-nested triple product consecutive quotient. -/
@[reducible] noncomputable def fintype_zassenhaus_prod
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Fintype (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) := by
  letI : Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
    fintype_zassenhaus_additive p G H n
  exact fintype_zassenhaus_additive p (G × H) K n

/-- Cardinality of the canonical additive left-nested triple consecutive-quotient fintype. -/
theorem fintype_next_prod
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Fintype (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    @Fintype.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n))
        (fintype_zassenhaus_prod p G H K n) =
      Fintype.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) *
        Fintype.card (Additive (zSubgro p H n ⧸ zNTerm p H n)) *
          Fintype.card (Additive (zSubgro p K n ⧸ zNTerm p K n)) := by
  letI : Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
    fintype_zassenhaus_additive p G H n
  rw [fintype_card_additive (p := p) (G × H) K n]
  rw [fintype_card_additive (p := p) G H n]

/-- Canonical additive fintype on a right-nested triple product consecutive quotient. -/
@[reducible] noncomputable def fintype_prod_nested
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Fintype (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) := by
  letI : Fintype (Additive (zSubgro p (H × K) n ⧸
      zNTerm p (H × K) n)) :=
    fintype_zassenhaus_additive p H K n
  exact fintype_zassenhaus_additive p G (H × K) n

/-- Cardinality of the canonical additive right-nested triple consecutive-quotient fintype. -/
theorem fintype_next_nested
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Fintype (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    @Fintype.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n))
        (fintype_prod_nested p G H K n) =
      Fintype.card (Additive (zSubgro p G n ⧸ zNTerm p G n)) *
        (Fintype.card (Additive (zSubgro p H n ⧸ zNTerm p H n)) *
          Fintype.card (Additive (zSubgro p K n ⧸ zNTerm p K n))) := by
  letI : Fintype (Additive (zSubgro p (H × K) n ⧸
      zNTerm p (H × K) n)) :=
    fintype_zassenhaus_additive p H K n
  rw [fintype_card_additive (p := p) G (H × K) n]
  rw [fintype_card_additive (p := p) H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Finite-dimensionality of left-nested triple layer kernels from finite-dimensional factors. -/
theorem module_finite_prod
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n)) := by
  haveI : Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) :=
    module_layer_kernel (p := p) G H n
  exact module_layer_kernel (p := p) (G × H) K n

/-- Finite-dimensionality of right-nested triple layer kernels from finite-dimensional factors. -/
theorem module_layer_nested
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n)) := by
  haveI : Module.Finite (ZMod p) (Additive (zLKern p (H × K) n)) :=
    module_layer_kernel (p := p) H K n
  exact module_layer_kernel (p := p) G (H × K) n

/-- Finite-dimensionality of left-nested triple consecutive quotients from factors. -/
theorem module_zassenhaus_next
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) := by
  haveI : Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
    module_finite_next (p := p) G H n
  exact module_finite_next (p := p) (G × H) K n

/-- Finite-dimensionality of right-nested triple consecutive quotients from factors. -/
theorem next_prod_nested
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) := by
  haveI : Module.Finite (ZMod p) (Additive (zSubgro p (H × K) n ⧸
      zNTerm p (H × K) n)) :=
    module_finite_next (p := p) H K n
  exact module_finite_next (p := p) G (H × K) n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Left-nested triple layer-kernel cardinality in summed-finrank form (additive). -/
theorem nat_additive_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Nat.card (Additive (zLKern p ((G × H) × K) n)) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n))) := by
  letI : Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n)) :=
    module_finite_prod (p := p) G H K n
  rw [card_additive_finrank (p := p) ((G × H) × K) n,
    finrank_layer_prod (p := p) G H K n]

/-- Right-nested triple layer-kernel cardinality in summed-finrank form (additive). -/
theorem nat_nested_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Nat.card (Additive (zLKern p (G × (H × K)) n)) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        (Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n)))) := by
  letI : Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n)) :=
    module_layer_nested (p := p) G H K n
  rw [card_additive_finrank (p := p) (G × (H × K)) n,
    finrank_prod_nested (p := p) G H K n]

/-- Left-nested triple layer-kernel cardinality in summed-finrank form. -/
theorem nat_prod_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Nat.card (zLKern p ((G × H) × K) n) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n))) := by
  simpa using
    nat_additive_finrank (p := p) G H K n

/-- Right-nested triple layer-kernel cardinality in summed-finrank form. -/
theorem prod_nested_finrank
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Nat.card (zLKern p (G × (H × K)) n) =
      p ^ (Module.finrank (ZMod p) (Additive (zLKern p G n)) +
        (Module.finrank (ZMod p) (Additive (zLKern p H n)) +
          Module.finrank (ZMod p) (Additive (zLKern p K n)))) := by
  simpa using
    nat_nested_finrank (p := p) G H K n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Left-nested triple consecutive-quotient cardinality in summed-finrank form (additive). -/
theorem nat_next_finrank
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Nat.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n))) := by
  letI : Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :=
    module_zassenhaus_next (p := p) G H K n
  rw [nat_next_additive (p := p) ((G × H) × K) n,
    finrank_next_prod (p := p) G H K n]

/-- Right-nested triple consecutive-quotient cardinality in summed-finrank form (additive). -/
theorem next_nested_finrank
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Nat.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        (Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n)))) := by
  letI : Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :=
    next_prod_nested (p := p) G H K n
  rw [nat_next_additive (p := p) (G × (H × K)) n,
    finrank_next_nested (p := p) G H K n]

/-- Left-nested triple consecutive-quotient cardinality in summed-finrank form. -/
theorem card_next_finrank
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Nat.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n))) := by
  simpa using
    nat_next_finrank (p := p) G H K n

/-- Right-nested triple consecutive-quotient cardinality in summed-finrank form. -/
theorem nat_next_nested
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Nat.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) =
      p ^ (Module.finrank (ZMod p)
          (Additive (zSubgro p G n ⧸ zNTerm p G n)) +
        (Module.finrank (ZMod p)
          (Additive (zSubgro p H n ⧸ zNTerm p H n)) +
          Module.finrank (ZMod p)
            (Additive (zSubgro p K n ⧸ zNTerm p K n)))) := by
  simpa using
    next_nested_finrank (p := p) G H K n

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Finite-dimensionality is invariant under reassociating triple product layer kernels. -/
theorem module_layer_assoc :
    Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n)) ↔
      Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n)) := by
  rw [module_layer_prod (p := p) G H K n,
    module_prod_nested (p := p) G H K n]

/-- Finite-dimensionality is invariant under reassociating triple consecutive quotients. -/
theorem module_zassenhaus_assoc :
    Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) ↔
      Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)) := by
  rw [module_next_prod (p := p) G H K n,
    module_next_nested (p := p) G H K n]

omit [Fact p.Prime] in
/-- Finiteness is invariant under reassociating triple product layer kernels. -/
theorem layer_prod_assoc :
    Finite (zLKern p ((G × H) × K) n) ↔
      Finite (zLKern p (G × (H × K)) n) := by
  rw [layer_kernel_prod (p := p) G H K n,
    layer_prod_nested (p := p) G H K n]

omit [Fact p.Prime] in
/-- Finiteness is invariant under reassociating triple consecutive quotients. -/
theorem next_quotient_assoc :
    Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) ↔
      Finite (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) := by
  rw [finite_next_prod (p := p) G H K n,
    zassenhaus_next_nested (p := p) G H K n]

/-- Additive finiteness is invariant under reassociating triple product layer kernels. -/
theorem layer_additive_assoc :
    Finite (Additive (zLKern p ((G × H) × K) n)) ↔
      Finite (Additive (zLKern p (G × (H × K)) n)) := by
  rw [layer_additive_prod (p := p) G H K n,
    additive_prod_nested (p := p) G H K n]

/-- Additive finiteness is invariant under reassociating triple consecutive quotients. -/
theorem next_prod_assoc :
    Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) ↔
      Finite (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)) := by
  rw [next_additive_prod (p := p) G H K n,
    next_additive_nested (p := p) G H K n]

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- `Nat.card` is unchanged by reassociating a triple product layer kernel. -/
theorem nat_prod_assoc :
    Nat.card (zLKern p ((G × H) × K) n) =
      Nat.card (zLKern p (G × (H × K)) n) := by
  rw [nat_layer_prod (p := p) G H K n,
    nat_prod_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

/-- `Nat.card` is unchanged by reassociating a triple product consecutive quotient. -/
theorem nat_card_assoc :
    Nat.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n) =
      Nat.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) := by
  rw [nat_zassenhaus_next (p := p) G H K n,
    card_next_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Additive `Nat.card` is unchanged by reassociating a triple product layer kernel. -/
theorem nat_additive_assoc :
    Nat.card (Additive (zLKern p ((G × H) × K) n)) =
      Nat.card (Additive (zLKern p (G × (H × K)) n)) := by
  rw [nat_additive_prod (p := p) G H K n,
    nat_card_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

/-- Additive `Nat.card` is unchanged by reassociating a triple consecutive quotient. -/
theorem nat_next_assoc :
    Nat.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)) =
      Nat.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)) := by
  rw [nat_next_prod (p := p) G H K n,
    nat_additive_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

/-- Finrank is unchanged by reassociating a triple product layer kernel. -/
theorem finrank_prod_assoc
    [Module.Finite (ZMod p) (Additive (zLKern p G n))]
    [Module.Finite (ZMod p) (Additive (zLKern p H n))]
    [Module.Finite (ZMod p) (Additive (zLKern p K n))] :
    Module.finrank (ZMod p) (Additive (zLKern p ((G × H) × K) n)) =
      Module.finrank (ZMod p) (Additive (zLKern p (G × (H × K)) n)) := by
  rw [finrank_layer_prod (p := p) G H K n,
    finrank_prod_nested (p := p) G H K n]
  exact Nat.add_assoc _ _ _

/-- Finrank is unchanged by reassociating a triple consecutive quotient. -/
theorem finrank_next_assoc
    [Module.Finite (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Module.Finite (ZMod p)
      (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    Module.finrank (ZMod p)
        (Additive (zSubgro p ((G × H) × K) n ⧸
          zNTerm p ((G × H) × K) n)) =
      Module.finrank (ZMod p)
        (Additive (zSubgro p (G × (H × K)) n ⧸
          zNTerm p (G × (H × K)) n)) := by
  rw [finrank_next_prod (p := p) G H K n,
    finrank_next_nested (p := p) G H K n]
  exact Nat.add_assoc _ _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- The canonical left- and right-nested triple layer-kernel fintypes have the same card. -/
theorem card_prod_assoc
    [Fintype (zLKern p G n)] [Fintype (zLKern p H n)]
    [Fintype (zLKern p K n)] :
    @Fintype.card (zLKern p ((G × H) × K) n)
        (fintype_layer_kernel p G H K n) =
      @Fintype.card (zLKern p (G × (H × K)) n)
        (kernel_prod_nested p G H K n) := by
  rw [fintype_kernel_prod (p := p) G H K n,
    fintype_kernel_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

/-- The canonical left- and right-nested triple quotient fintypes have the same card. -/
theorem card_next_assoc
    [Fintype (zSubgro p G n ⧸ zNTerm p G n)]
    [Fintype (zSubgro p H n ⧸ zNTerm p H n)]
    [Fintype (zSubgro p K n ⧸ zNTerm p K n)] :
    @Fintype.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)
        (fintype_zassenhaus_quotient p G H K n) =
      @Fintype.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)
        (fintype_quotient_nested p G H K n) := by
  rw [card_next_prod (p := p) G H K n,
    fintype_zassenhaus_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- The canonical additive triple layer-kernel fintypes have the same card after reassociation. -/
theorem card_additive_assoc
    [Fintype (Additive (zLKern p G n))]
    [Fintype (Additive (zLKern p H n))]
    [Fintype (Additive (zLKern p K n))] :
    @Fintype.card (Additive (zLKern p ((G × H) × K) n))
        (fintype_layer_additive p G H K n) =
      @Fintype.card (Additive (zLKern p (G × (H × K)) n))
        (fintype_layer_nested p G H K n) := by
  rw [fintype_card_prod (p := p) G H K n,
    fintype_card_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

/-- The canonical additive triple quotient fintypes have the same card after reassociation. -/
theorem fintype_zassenhaus_assoc
    [Fintype (Additive (zSubgro p G n ⧸ zNTerm p G n))]
    [Fintype (Additive (zSubgro p H n ⧸ zNTerm p H n))]
    [Fintype (Additive (zSubgro p K n ⧸ zNTerm p K n))] :
    @Fintype.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n))
        (fintype_zassenhaus_prod p G H K n) =
      @Fintype.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n))
        (fintype_prod_nested p G H K n) := by
  rw [fintype_next_prod (p := p) G H K n,
    fintype_next_nested (p := p) G H K n]
  exact Nat.mul_assoc _ _ _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport a fintype on a left-nested triple layer kernel across reassociation. -/
@[reducible] noncomputable def layer_assoc_right
    [Fintype (zLKern p ((G × H) × K) n)] :
    Fintype (zLKern p (G × (H × K)) n) := by
  haveI : Finite (zLKern p ((G × H) × K) n) :=
    Fintype.finite (inferInstance)
  haveI : Finite (zLKern p (G × (H × K)) n) :=
    (layer_prod_assoc (p := p) G H K n).1 inferInstance
  exact Fintype.ofFinite _

/-- Transport a fintype on a right-nested triple layer kernel across reassociation. -/
@[reducible] noncomputable def layer_assoc_left
    [Fintype (zLKern p (G × (H × K)) n)] :
    Fintype (zLKern p ((G × H) × K) n) := by
  haveI : Finite (zLKern p (G × (H × K)) n) :=
    Fintype.finite (inferInstance)
  haveI : Finite (zLKern p ((G × H) × K) n) :=
    (layer_prod_assoc (p := p) G H K n).2 inferInstance
  exact Fintype.ofFinite _

/-- Transport a fintype on a left-nested triple consecutive quotient across reassociation. -/
@[reducible] noncomputable def fintype_quotient_assoc
    [Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)] :
    Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) := by
  haveI : Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) := Fintype.finite (inferInstance)
  haveI : Finite (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :=
    (next_quotient_assoc (p := p) G H K n).1 inferInstance
  exact Fintype.ofFinite _

/-- Transport a fintype on a right-nested triple consecutive quotient across reassociation. -/
@[reducible] noncomputable def fintype_zassenhaus_left
    [Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)] :
    Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) := by
  haveI : Finite (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) := Fintype.finite (inferInstance)
  haveI : Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :=
    (next_quotient_assoc (p := p) G H K n).2 inferInstance
  exact Fintype.ofFinite _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport an additive fintype on a left-nested triple layer kernel across reassociation. -/
@[reducible] noncomputable def additive_assoc_right
    [Fintype (Additive (zLKern p ((G × H) × K) n))] :
    Fintype (Additive (zLKern p (G × (H × K)) n)) := by
  haveI : Finite (Additive (zLKern p ((G × H) × K) n)) :=
    Fintype.finite (inferInstance)
  haveI : Finite (Additive (zLKern p (G × (H × K)) n)) :=
    (layer_additive_assoc (p := p) G H K n).1 inferInstance
  exact Fintype.ofFinite _

/-- Transport an additive fintype on a right-nested triple layer kernel across reassociation. -/
@[reducible] noncomputable def fintype_kernel_assoc
    [Fintype (Additive (zLKern p (G × (H × K)) n))] :
    Fintype (Additive (zLKern p ((G × H) × K) n)) := by
  haveI : Finite (Additive (zLKern p (G × (H × K)) n)) :=
    Fintype.finite (inferInstance)
  haveI : Finite (Additive (zLKern p ((G × H) × K) n)) :=
    (layer_additive_assoc (p := p) G H K n).2 inferInstance
  exact Fintype.ofFinite _

/-- Transport an additive fintype on a left-nested triple quotient across reassociation. -/
@[reducible] noncomputable def next_additive_assoc
    [Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))] :
    Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) := by
  haveI : Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) := Fintype.finite (inferInstance)
  haveI : Finite (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :=
    (next_prod_assoc (p := p) G H K n).1 inferInstance
  exact Fintype.ofFinite _

/-- Transport an additive fintype on a right-nested triple quotient across reassociation. -/
@[reducible] noncomputable def next_assoc_left
    [Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n))] :
    Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) := by
  haveI : Finite (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) := Fintype.finite (inferInstance)
  haveI : Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :=
    (next_prod_assoc (p := p) G H K n).2 inferInstance
  exact Fintype.ofFinite _

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport finite-dimensionality from left- to right-nested triple layer kernels. -/
theorem module_assoc_right
    [Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n)) :=
  (module_layer_assoc (p := p) G H K n).1 inferInstance

/-- Transport finite-dimensionality from right- to left-nested triple layer kernels. -/
theorem module_prod_assoc
    [Module.Finite (ZMod p) (Additive (zLKern p (G × (H × K)) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p ((G × H) × K) n)) :=
  (module_layer_assoc (p := p) G H K n).2 inferInstance

/-- Transport finite-dimensionality from left- to right-nested triple consecutive quotients. -/
theorem module_next_assoc
    [Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :=
  (module_zassenhaus_assoc (p := p) G H K n).1 inferInstance

/-- Transport finite-dimensionality from right- to left-nested triple consecutive quotients. -/
theorem module_assoc_left
    [Module.Finite (ZMod p) (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :=
  (module_zassenhaus_assoc (p := p) G H K n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport finiteness from left- to right-nested triple layer kernels. -/
theorem zassenhaus_assoc_right
    [Finite (zLKern p ((G × H) × K) n)] :
    Finite (zLKern p (G × (H × K)) n) :=
  (layer_prod_assoc (p := p) G H K n).1 inferInstance

/-- Transport finiteness from right- to left-nested triple layer kernels. -/
theorem kernel_assoc_left
    [Finite (zLKern p (G × (H × K)) n)] :
    Finite (zLKern p ((G × H) × K) n) :=
  (layer_prod_assoc (p := p) G H K n).2 inferInstance

/-- Transport finiteness from left- to right-nested triple consecutive quotients. -/
theorem zassenhaus_next_assoc
    [Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)] :
    Finite (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :=
  (next_quotient_assoc (p := p) G H K n).1 inferInstance

/-- Transport finiteness from right- to left-nested triple consecutive quotients. -/
theorem finite_next_assoc
    [Finite (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)] :
    Finite (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :=
  (next_quotient_assoc (p := p) G H K n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport additive finiteness from left- to right-nested triple layer kernels. -/
theorem additive_prod_assoc
    [Finite (Additive (zLKern p ((G × H) × K) n))] :
    Finite (Additive (zLKern p (G × (H × K)) n)) :=
  (layer_additive_assoc (p := p) G H K n).1 inferInstance

/-- Transport additive finiteness from right- to left-nested triple layer kernels. -/
theorem prod_assoc_left
    [Finite (Additive (zLKern p (G × (H × K)) n))] :
    Finite (Additive (zLKern p ((G × H) × K) n)) :=
  (layer_additive_assoc (p := p) G H K n).2 inferInstance

/-- Transport additive finiteness from left- to right-nested triple consecutive quotients. -/
theorem next_assoc_right
    [Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))] :
    Finite (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :=
  (next_prod_assoc (p := p) G H K n).1 inferInstance

/-- Transport additive finiteness from right- to left-nested triple consecutive quotients. -/
theorem additive_assoc_left
    [Finite (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n))] :
    Finite (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :=
  (next_prod_assoc (p := p) G H K n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport a layer-kernel fintype across the explicit Zassenhaus reassociation equivalence. -/
@[reducible] noncomputable def prod_assoc_right
    [Fintype (zLKern p ((G × H) × K) n)] :
    Fintype (zLKern p (G × (H × K)) n) := by
  exact Fintype.ofEquiv (zLKern p ((G × H) × K) n)
    (zLKern.prodAssocEquiv p G H K n).toEquiv

/-- Transport a layer-kernel fintype across the inverse explicit reassociation equivalence. -/
@[reducible] noncomputable def fintype_layer_left
    [Fintype (zLKern p (G × (H × K)) n)] :
    Fintype (zLKern p ((G × H) × K) n) := by
  exact Fintype.ofEquiv (zLKern p (G × (H × K)) n)
    (zLKern.prodAssocEquiv p G H K n).symm.toEquiv

/-- Transport a consecutive-quotient fintype across the explicit reassociation equivalence. -/
@[reducible] noncomputable def fintype_next_right
    [Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)] :
    Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) := by
  exact Fintype.ofEquiv (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)
    (zNQuot.prodAssocEquiv p G H K n).toEquiv

/-- Transport a consecutive-quotient fintype across the inverse explicit
reassociation equivalence. -/
@[reducible] noncomputable def fintype_zassenhaus_next
    [Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)] :
    Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) := by
  exact Fintype.ofEquiv (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)
    (zNQuot.prodAssocEquiv p G H K n).symm.toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Transport an additive layer-kernel fintype across the linear reassociation equivalence. -/
@[reducible] noncomputable def fintype_assoc_linear
    [Fintype (Additive (zLKern p ((G × H) × K) n))] :
    Fintype (Additive (zLKern p (G × (H × K)) n)) := by
  exact Fintype.ofEquiv (Additive (zLKern p ((G × H) × K) n))
    (zLKern.prod_assoc_linequiv p G H K n).toEquiv

/-- Transport an additive layer-kernel fintype across the inverse linear
reassociation equivalence. -/
@[reducible] noncomputable def fintype_prod_assoc
    [Fintype (Additive (zLKern p (G × (H × K)) n))] :
    Fintype (Additive (zLKern p ((G × H) × K) n)) := by
  exact Fintype.ofEquiv (Additive (zLKern p (G × (H × K)) n))
    (zLKern.prod_assoc_linequiv p G H K n).symm.toEquiv

/-- Transport an additive consecutive-quotient fintype across the linear
reassociation equivalence. -/
@[reducible] noncomputable def fintype_assoc_right
    [Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))] :
    Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) := by
  exact Fintype.ofEquiv (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))
    (zNQuot.prod_assoc_linequiv p G H K n).toEquiv

/-- Transport an additive consecutive-quotient fintype across the inverse linear equivalence. -/
@[reducible] noncomputable def fintype_assoc_left
    [Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n))] :
    Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) := by
  exact Fintype.ofEquiv (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n))
    (zNQuot.prod_assoc_linequiv p G H K n).symm.toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Card preservation for the equivalence-transported reassociated layer-kernel fintype. -/
theorem fintype_layer_assoc
    [Fintype (zLKern p ((G × H) × K) n)] :
    @Fintype.card (zLKern p (G × (H × K)) n)
        (prod_assoc_right p G H K n) =
      Fintype.card (zLKern p ((G × H) × K) n) := by
  letI : Fintype (zLKern p (G × (H × K)) n) :=
    prod_assoc_right p G H K n
  exact (Fintype.card_congr
    (zLKern.prodAssocEquiv p G H K n).toEquiv).symm

/-- Card preservation for the equivalence-transported reassociated consecutive quotient. -/
theorem fintype_card_assoc
    [Fintype (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)] :
    @Fintype.card (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n)
        (fintype_next_right p G H K n) =
      Fintype.card (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n) := by
  letI : Fintype (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :=
    fintype_next_right p G H K n
  exact (Fintype.card_congr
    (zNQuot.prodAssocEquiv p G H K n).toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Card preservation for the linear-equivalence-transported additive layer-kernel fintype. -/
theorem fintype_additive_assoc
    [Fintype (Additive (zLKern p ((G × H) × K) n))] :
    @Fintype.card (Additive (zLKern p (G × (H × K)) n))
        (fintype_assoc_linear p G H K n) =
      Fintype.card (Additive (zLKern p ((G × H) × K) n)) := by
  letI : Fintype (Additive (zLKern p (G × (H × K)) n)) :=
    fintype_assoc_linear p G H K n
  exact (Fintype.card_congr
    (zLKern.prod_assoc_linequiv p G H K n).toEquiv).symm

/-- Card preservation for the linear-equivalence-transported additive consecutive quotient. -/
theorem fintype_next_assoc
    [Fintype (Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n))] :
    @Fintype.card (Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n))
        (fintype_assoc_right p G H K n) =
      Fintype.card (Additive (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n)) := by
  letI : Fintype (Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :=
    fintype_assoc_right p G H K n
  exact (Fintype.card_congr
    (zNQuot.prod_assoc_linequiv p G H K n).toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finite-dimensionality of additive layer kernels is invariant under swapping product factors. -/
theorem module_layer_comm :
    Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) ↔
      Module.Finite (ZMod p) (Additive (zLKern p (H × G) n)) := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv (zLKern.prod_comm_linequiv p G H n)
  · intro h
    letI := h
    exact Module.Finite.equiv (zLKern.prod_comm_linequiv p G H n).symm

/-- Finite-dimensionality of additive consecutive quotients is invariant under swapping factors. -/
theorem module_zassenhaus_comm :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) ↔
      Module.Finite (ZMod p) (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)) := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv (zNQuot.prod_comm_linequiv p G H n)
  · intro h
    letI := h
    exact Module.Finite.equiv (zNQuot.prod_comm_linequiv p G H n).symm

/-- Swapping product factors preserves the finite rank of additive layer kernels. -/
theorem finrank_prod_comm :
    Module.finrank (ZMod p) (Additive (zLKern p (G × H) n)) =
      Module.finrank (ZMod p) (Additive (zLKern p (H × G) n)) :=
  (zLKern.prod_comm_linequiv p G H n).finrank_eq

/-- Swapping product factors preserves the finite rank of additive consecutive quotients. -/
theorem finrank_next_comm :
    Module.finrank (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) =
      Module.finrank (ZMod p) (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)) :=
  (zNQuot.prod_comm_linequiv p G H n).finrank_eq

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of layer kernels is invariant under swapping product factors. -/
theorem layer_prod_comm :
    Finite (zLKern p (G × H) n) ↔
      Finite (zLKern p (H × G) n) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zLKern.prodCommEquiv p G H n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zLKern.prodCommEquiv p G H n).symm.toEquiv

/-- Finiteness of consecutive quotients is invariant under swapping product factors. -/
theorem finite_next_comm :
    Finite (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) ↔
      Finite (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zNQuot.prodCommEquiv p G H n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zNQuot.prodCommEquiv p G H n).symm.toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Additive finiteness of layer kernels is invariant under swapping product factors. -/
theorem additive_prod_comm :
    Finite (Additive (zLKern p (G × H) n)) ↔
      Finite (Additive (zLKern p (H × G) n)) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zLKern.prod_comm_linequiv p G H n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zLKern.prod_comm_linequiv p G H n).symm.toEquiv

/-- Additive finiteness of consecutive quotients is invariant under swapping product factors. -/
theorem next_prod_comm :
    Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) ↔
      Finite (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zNQuot.prod_comm_linequiv p G H n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zNQuot.prod_comm_linequiv p G H n).symm.toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Transport a layer-kernel fintype across the product-swap equivalence. -/
@[reducible] noncomputable def fintype_kernel_comm
    [Fintype (zLKern p (G × H) n)] :
    Fintype (zLKern p (H × G) n) := by
  exact Fintype.ofEquiv (zLKern p (G × H) n)
    (zLKern.prodCommEquiv p G H n).toEquiv

/-- Transport a layer-kernel fintype across the inverse product-swap equivalence. -/
@[reducible] noncomputable def prod_comm_left
    [Fintype (zLKern p (H × G) n)] :
    Fintype (zLKern p (G × H) n) := by
  exact Fintype.ofEquiv (zLKern p (H × G) n)
    (zLKern.prodCommEquiv p G H n).symm.toEquiv

/-- Transport a consecutive-quotient fintype across the product-swap equivalence. -/
@[reducible] noncomputable def next_comm_right
    [Fintype (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)] :
    Fintype (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) := by
  exact Fintype.ofEquiv (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)
    (zNQuot.prodCommEquiv p G H n).toEquiv

/-- Transport a consecutive-quotient fintype across the inverse product-swap equivalence. -/
@[reducible] noncomputable def fintype_comm_equiv
    [Fintype (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n)] :
    Fintype (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) := by
  exact Fintype.ofEquiv (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)
    (zNQuot.prodCommEquiv p G H n).symm.toEquiv

/-- Card preservation for the product-swap transported layer-kernel fintype. -/
theorem fintype_layer_comm
    [Fintype (zLKern p (G × H) n)] :
    @Fintype.card (zLKern p (H × G) n)
        (fintype_kernel_comm p G H n) =
      Fintype.card (zLKern p (G × H) n) := by
  letI : Fintype (zLKern p (H × G) n) :=
    fintype_kernel_comm p G H n
  exact (Fintype.card_congr
    (zLKern.prodCommEquiv p G H n).toEquiv).symm

/-- Card preservation for the product-swap transported consecutive-quotient fintype. -/
theorem fintype_card_comm
    [Fintype (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)] :
    @Fintype.card (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)
        (next_comm_right p G H n) =
      Fintype.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) := by
  letI : Fintype (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n) :=
    next_comm_right p G H n
  exact (Fintype.card_congr
    (zNQuot.prodCommEquiv p G H n).toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Transport an additive layer-kernel fintype across the linear product-swap equivalence. -/
@[reducible] noncomputable def fintype_prod_comm
    [Fintype (Additive (zLKern p (G × H) n))] :
    Fintype (Additive (zLKern p (H × G) n)) := by
  exact Fintype.ofEquiv (Additive (zLKern p (G × H) n))
    (zLKern.prod_comm_linequiv p G H n).toEquiv

/-- Transport an additive layer-kernel fintype across the inverse linear
product-swap equivalence. -/
@[reducible] noncomputable def fintype_additive_left
    [Fintype (Additive (zLKern p (H × G) n))] :
    Fintype (Additive (zLKern p (G × H) n)) := by
  exact Fintype.ofEquiv (Additive (zLKern p (H × G) n))
    (zLKern.prod_comm_linequiv p G H n).symm.toEquiv

/-- Transport an additive consecutive-quotient fintype across the linear
product-swap equivalence. -/
@[reducible] noncomputable def fintype_comm_right
    [Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Fintype (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)) := by
  exact Fintype.ofEquiv (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))
    (zNQuot.prod_comm_linequiv p G H n).toEquiv

/-- Transport an additive consecutive-quotient fintype across the inverse
linear swap equivalence. -/
@[reducible] noncomputable def fintype_next_additive
    [Fintype (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n))] :
    Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) := by
  exact Fintype.ofEquiv (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n))
    (zNQuot.prod_comm_linequiv p G H n).symm.toEquiv

/-- Card preservation for the linear-swap transported additive layer-kernel fintype. -/
theorem fintype_additive_comm
    [Fintype (Additive (zLKern p (G × H) n))] :
    @Fintype.card (Additive (zLKern p (H × G) n))
        (fintype_prod_comm p G H n) =
      Fintype.card (Additive (zLKern p (G × H) n)) := by
  letI : Fintype (Additive (zLKern p (H × G) n)) :=
    fintype_prod_comm p G H n
  exact (Fintype.card_congr
    (zLKern.prod_comm_linequiv p G H n).toEquiv).symm

/-- Card preservation for the linear-swap transported additive consecutive-quotient fintype. -/
theorem fintype_next_comm
    [Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    @Fintype.card (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n))
        (fintype_comm_right p G H n) =
      Fintype.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)) := by
  letI : Fintype (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)) :=
    fintype_comm_right p G H n
  exact (Fintype.card_congr
    (zNQuot.prod_comm_linequiv p G H n).toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- `Nat.card` of a layer kernel is invariant under swapping product factors. -/
theorem nat_card_comm :
    Nat.card (zLKern p (G × H) n) =
      Nat.card (zLKern p (H × G) n) :=
  Nat.card_congr (zLKern.prodCommEquiv p G H n).toEquiv

/-- `Nat.card` of a consecutive quotient is invariant under swapping product factors. -/
theorem card_next_comm :
    Nat.card (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) =
      Nat.card (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) :=
  Nat.card_congr (zNQuot.prodCommEquiv p G H n).toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Additive `Nat.card` of a layer kernel is invariant under swapping product factors. -/
theorem nat_additive_comm :
    Nat.card (Additive (zLKern p (G × H) n)) =
      Nat.card (Additive (zLKern p (H × G) n)) :=
  Nat.card_congr (zLKern.prod_comm_linequiv p G H n).toEquiv

/-- Additive `Nat.card` of a consecutive quotient is invariant under swapping product factors. -/
theorem nat_next_comm :
    Nat.card (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) =
      Nat.card (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)) :=
  Nat.card_congr (zNQuot.prod_comm_linequiv p G H n).toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Transport finite-dimensionality of layer kernels across product swap (forward). -/
theorem module_comm_right
    [Module.Finite (ZMod p) (Additive (zLKern p (G × H) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p (H × G) n)) :=
  (module_layer_comm (p := p) G H n).1 inferInstance

/-- Transport finite-dimensionality of layer kernels across product swap (backward). -/
theorem module_prod_comm
    [Module.Finite (ZMod p) (Additive (zLKern p (H × G) n))] :
    Module.Finite (ZMod p) (Additive (zLKern p (G × H) n)) :=
  (module_layer_comm (p := p) G H n).2 inferInstance

/-- Transport finite-dimensionality of consecutive quotients across product swap (forward). -/
theorem module_next_comm
    [Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)) :=
  (module_zassenhaus_comm (p := p) G H n).1 inferInstance

/-- Transport finite-dimensionality of consecutive quotients across product swap (backward). -/
theorem module_comm_left
    [Module.Finite (ZMod p) (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n))] :
    Module.Finite (ZMod p) (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
  (module_zassenhaus_comm (p := p) G H n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Transport finiteness of layer kernels across product swap (forward). -/
theorem layer_comm_right
    [Finite (zLKern p (G × H) n)] :
    Finite (zLKern p (H × G) n) :=
  (layer_prod_comm (p := p) G H n).1 inferInstance

/-- Transport finiteness of layer kernels across product swap (backward). -/
theorem layer_comm_left
    [Finite (zLKern p (H × G) n)] :
    Finite (zLKern p (G × H) n) :=
  (layer_prod_comm (p := p) G H n).2 inferInstance

/-- Transport finiteness of consecutive quotients across product swap (forward). -/
theorem prod_comm_right
    [Finite (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)] :
    Finite (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) :=
  (finite_next_comm (p := p) G H n).1 inferInstance

/-- Transport finiteness of consecutive quotients across product swap (backward). -/
theorem zassenhaus_next_comm
    [Finite (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n)] :
    Finite (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) :=
  (finite_next_comm (p := p) G H n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Transport additive finiteness of layer kernels across product swap (forward). -/
theorem additive_comm_right
    [Finite (Additive (zLKern p (G × H) n))] :
    Finite (Additive (zLKern p (H × G) n)) :=
  (additive_prod_comm (p := p) G H n).1 inferInstance

/-- Transport additive finiteness of layer kernels across product swap (backward). -/
theorem additive_comm_left
    [Finite (Additive (zLKern p (H × G) n))] :
    Finite (Additive (zLKern p (G × H) n)) :=
  (additive_prod_comm (p := p) G H n).2 inferInstance

/-- Transport additive finiteness of consecutive quotients across product swap (forward). -/
theorem next_additive_comm
    [Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n))] :
    Finite (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)) :=
  (next_prod_comm (p := p) G H n).1 inferInstance

/-- Transport additive finiteness of consecutive quotients across product swap (backward). -/
theorem next_comm_left
    [Finite (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n))] :
    Finite (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
  (next_prod_comm (p := p) G H n).2 inferInstance

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Card preservation for the inverse product-swap transported layer-kernel fintype. -/
theorem fintype_card_left
    [Fintype (zLKern p (H × G) n)] :
    @Fintype.card (zLKern p (G × H) n)
        (prod_comm_left p G H n) =
      Fintype.card (zLKern p (H × G) n) := by
  letI : Fintype (zLKern p (G × H) n) :=
    prod_comm_left p G H n
  exact (Fintype.card_congr
    (zLKern.prodCommEquiv p G H n).symm.toEquiv).symm

/-- Card preservation for the inverse product-swap transported quotient fintype. -/
theorem fintype_next_left
    [Fintype (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)] :
    @Fintype.card (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n)
        (fintype_comm_equiv p G H n) =
      Fintype.card (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n) := by
  letI : Fintype (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :=
    fintype_comm_equiv p G H n
  exact (Fintype.card_congr
    (zNQuot.prodCommEquiv p G H n).symm.toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Card preservation for the inverse linear-swap transported additive layer fintype. -/
theorem fintype_comm_linear
    [Fintype (Additive (zLKern p (H × G) n))] :
    @Fintype.card (Additive (zLKern p (G × H) n))
        (fintype_additive_left p G H n) =
      Fintype.card (Additive (zLKern p (H × G) n)) := by
  letI : Fintype (Additive (zLKern p (G × H) n)) :=
    fintype_additive_left p G H n
  exact (Fintype.card_congr
    (zLKern.prod_comm_linequiv p G H n).symm.toEquiv).symm

/-- Card preservation for the inverse linear-swap transported additive quotient fintype. -/
theorem fintype_comm_left
    [Fintype (Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n))] :
    @Fintype.card (Additive (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n))
        (fintype_next_additive p G H n) =
      Fintype.card (Additive (zSubgro p (H × G) n ⧸
        zNTerm p (H × G) n)) := by
  letI : Fintype (Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :=
    fintype_next_additive p G H n
  exact (Fintype.card_congr
    (zNQuot.prod_comm_linequiv p G H n).symm.toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Finiteness of ordinary Zassenhaus quotients is invariant under swapping product factors. -/
theorem zassenhaus_prod_comm :
    Finite (zQuot p (G × H) n) ↔
      Finite (zQuot p (H × G) n) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zQuot.prodCommEquiv p G H n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zQuot.prodCommEquiv p G H n).symm.toEquiv

/-- Transport an ordinary quotient fintype across the product-swap equivalence. -/
@[reducible] noncomputable def fintype_quotient_comm
    [Fintype (zQuot p (G × H) n)] :
    Fintype (zQuot p (H × G) n) := by
  exact Fintype.ofEquiv (zQuot p (G × H) n)
    (zQuot.prodCommEquiv p G H n).toEquiv

/-- Transport an ordinary quotient fintype across the inverse product-swap equivalence. -/
@[reducible] noncomputable def fintype_equiv_left
    [Fintype (zQuot p (H × G) n)] :
    Fintype (zQuot p (G × H) n) := by
  exact Fintype.ofEquiv (zQuot p (H × G) n)
    (zQuot.prodCommEquiv p G H n).symm.toEquiv

/-- Card preservation for the product-swap transported ordinary quotient fintype. -/
theorem fintype_zassenhaus_comm
    [Fintype (zQuot p (G × H) n)] :
    @Fintype.card (zQuot p (H × G) n)
        (fintype_quotient_comm p G H n) =
      Fintype.card (zQuot p (G × H) n) := by
  letI : Fintype (zQuot p (H × G) n) :=
    fintype_quotient_comm p G H n
  exact (Fintype.card_congr
    (zQuot.prodCommEquiv p G H n).toEquiv).symm

/-- Card preservation for the inverse-swap transported ordinary quotient fintype. -/
theorem fintype_prod_left
    [Fintype (zQuot p (H × G) n)] :
    @Fintype.card (zQuot p (G × H) n)
        (fintype_equiv_left p G H n) =
      Fintype.card (zQuot p (H × G) n) := by
  letI : Fintype (zQuot p (G × H) n) :=
    fintype_equiv_left p G H n
  exact (Fintype.card_congr
    (zQuot.prodCommEquiv p G H n).symm.toEquiv).symm

/-- `Nat.card` of an ordinary quotient is invariant under swapping product factors. -/
theorem nat_prod_comm :
    Nat.card (zQuot p (G × H) n) =
      Nat.card (zQuot p (H × G) n) :=
  Nat.card_congr (zQuot.prodCommEquiv p G H n).toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Finiteness of ordinary Zassenhaus quotients is invariant under reassociating products. -/
theorem zassenhaus_prod_assoc :
    Finite (zQuot p ((G × H) × K) n) ↔
      Finite (zQuot p (G × (H × K)) n) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (zQuot.prodAssocEquiv p G H K n).toEquiv
  · intro h
    letI := h
    exact Finite.of_equiv _ (zQuot.prodAssocEquiv p G H K n).symm.toEquiv

/-- `Nat.card` of an ordinary quotient is invariant under reassociating products. -/
theorem nat_zassenhaus_assoc :
    Nat.card (zQuot p ((G × H) × K) n) =
      Nat.card (zQuot p (G × (H × K)) n) :=
  Nat.card_congr (zQuot.prodAssocEquiv p G H K n).toEquiv

/-- Transport an ordinary quotient fintype across the reassociation equivalence. -/
@[reducible] noncomputable def fintype_prod_right
    [Fintype (zQuot p ((G × H) × K) n)] :
    Fintype (zQuot p (G × (H × K)) n) := by
  exact Fintype.ofEquiv (zQuot p ((G × H) × K) n)
    (zQuot.prodAssocEquiv p G H K n).toEquiv

/-- Transport an ordinary quotient fintype across the inverse reassociation equivalence. -/
@[reducible] noncomputable def zassenhaus_assoc_left
    [Fintype (zQuot p (G × (H × K)) n)] :
    Fintype (zQuot p ((G × H) × K) n) := by
  exact Fintype.ofEquiv (zQuot p (G × (H × K)) n)
    (zQuot.prodAssocEquiv p G H K n).symm.toEquiv

/-- Card preservation for the reassociation-transported ordinary quotient fintype. -/
theorem fintype_card_right
    [Fintype (zQuot p ((G × H) × K) n)] :
    @Fintype.card (zQuot p (G × (H × K)) n)
        (fintype_prod_right p G H K n) =
      Fintype.card (zQuot p ((G × H) × K) n) := by
  letI : Fintype (zQuot p (G × (H × K)) n) :=
    fintype_prod_right p G H K n
  exact (Fintype.card_congr
    (zQuot.prodAssocEquiv p G H K n).toEquiv).symm

/-- Card preservation for the inverse reassociation-transported ordinary quotient fintype. -/
theorem fintype_assoc_equiv
    [Fintype (zQuot p (G × (H × K)) n)] :
    @Fintype.card (zQuot p ((G × H) × K) n)
        (zassenhaus_assoc_left p G H K n) =
      Fintype.card (zQuot p (G × (H × K)) n) := by
  letI : Fintype (zQuot p ((G × H) × K) n) :=
    zassenhaus_assoc_left p G H K n
  exact (Fintype.card_congr
    (zQuot.prodAssocEquiv p G H K n).symm.toEquiv).symm

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H] (n : ℕ)

/-- Fintype cardinality of ordinary quotients is invariant under swapping factors. -/
theorem card_prod_comm
    [Fintype (zQuot p (G × H) n)]
    [Fintype (zQuot p (H × G) n)] :
    Fintype.card (zQuot p (G × H) n) =
      Fintype.card (zQuot p (H × G) n) :=
  Fintype.card_congr (zQuot.prodCommEquiv p G H n).toEquiv

end
end Submission

namespace Submission

open GroupAlgebra

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)

/-- Fintype cardinality of ordinary quotients is invariant under reassociating factors. -/
theorem card_zassenhaus_assoc
    [Fintype (zQuot p ((G × H) × K) n)]
    [Fintype (zQuot p (G × (H × K)) n)] :
    Fintype.card (zQuot p ((G × H) × K) n) =
      Fintype.card (zQuot p (G × (H × K)) n) :=
  Fintype.card_congr (zQuot.prodAssocEquiv p G H K n).toEquiv

end
end Submission
