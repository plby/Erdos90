import Towers.Group.LowerMagnusMap

noncomputable section

namespace Towers
namespace TBluepr

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The multiplicative class map from `γ_(n+1)` to its zero-based associated-graded layer. -/
def lowerClassHom
    (n : ℕ) :
    Subgroup.lowerCentralSeries G n →*
      LowerGradedLayer G n :=
  QuotientGroup.mk'
    ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
      (Subgroup.lowerCentralSeries G n))

/-- The additive associated-graded class represented by an element of `γ_(n+1)`. -/
def lowerCentralClass
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    Additive (LowerGradedLayer G n) :=
  Additive.ofMul (lowerClassHom n x)

@[simp]
theorem lower_central_one
    (n : ℕ) :
    lowerCentralClass (G := G) n 1 = 0 := by
  change
    Additive.ofMul (lowerClassHom (G := G) n 1) =
      (0 : Additive (LowerGradedLayer G n))
  rw [map_one]
  rfl

@[simp]
theorem lower_class_mul
    (n : ℕ)
    (x y : Subgroup.lowerCentralSeries G n) :
    lowerCentralClass n (x * y) =
      lowerCentralClass n x + lowerCentralClass n y := by
  change
    Additive.ofMul (lowerClassHom n (x * y)) =
      Additive.ofMul (lowerClassHom n x) +
        Additive.ofMul (lowerClassHom n y)
  rw [map_mul]
  rfl

@[simp]
theorem lower_class_inv
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    lowerCentralClass n x⁻¹ =
      -lowerCentralClass n x := by
  change
    Additive.ofMul (lowerClassHom n x⁻¹) =
      -Additive.ofMul (lowerClassHom n x)
  rw [map_inv]
  rfl

/-- Conjugation does not change a lower-central associated-graded class. -/
theorem lower_class_conj
    (n : ℕ)
    (g : G)
    (x : Subgroup.lowerCentralSeries G n) :
    lowerCentralClass n
        ⟨g * (x : G) * g⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G n).Normal).conj_mem
              (x : G) x.property g⟩ =
      lowerCentralClass n x := by
  change
    lowerClassHom n
        ⟨g * (x : G) * g⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G n).Normal).conj_mem
              (x : G) x.property g⟩ =
      lowerClassHom n x
  apply (QuotientGroup.eq_iff_div_mem).2
  change g * (x : G) * g⁻¹ / (x : G) ∈
    Subgroup.lowerCentralSeries G (n + 1)
  rw [div_eq_mul_inv]
  simpa only [commutatorElement_def, Nat.zero_add] using
    lower_commutator_succ 0 n
      (Subgroup.commutator_mem_commutator
        (show g ∈ Subgroup.lowerCentralSeries G 0 by simp) x.property)

/-- A commutator of lower-central representatives, represented in its expected term. -/
def centralBracketRep
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    Subgroup.lowerCentralSeries G (i + j + 1) :=
  ⟨⁅(x : G), (y : G)⁆,
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator x.property y.property)⟩

/-- The associated-graded commutator class of two lower-central representatives. -/
def centralBracketClass
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    Additive
      (LowerGradedLayer G (i + j + 1)) :=
  lowerCentralClass (i + j + 1) (centralBracketRep i j x y)

@[simp]
theorem central_bracket_class
    (i j : ℕ)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j
        (1 : Subgroup.lowerCentralSeries G i) y =
      0 := by
  change lowerCentralClass (i + j + 1) (centralBracketRep i j 1 y) = 0
  rw [show
    centralBracketRep i j (1 : Subgroup.lowerCentralSeries G i) y = 1 by
      apply Subtype.ext
      exact commutatorElement_one_left (y : G)]
  exact lower_central_one (i + j + 1)

@[simp]
theorem bracket_class_right
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i) :
    centralBracketClass i j x
        (1 : Subgroup.lowerCentralSeries G j) =
      0 := by
  change lowerCentralClass (i + j + 1) (centralBracketRep i j x 1) = 0
  rw [show
    centralBracketRep i j x (1 : Subgroup.lowerCentralSeries G j) = 1 by
      apply Subtype.ext
      exact commutatorElement_one_right (x : G)]
  exact lower_central_one (i + j + 1)

/-- The associated-graded commutator class is additive in its left representative. -/
theorem bracket_class_left
    (i j : ℕ)
    (x y : Subgroup.lowerCentralSeries G i)
    (z : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j (x * y) z =
      centralBracketClass i j x z +
        centralBracketClass i j y z := by
  change
    lowerCentralClass (i + j + 1) (centralBracketRep i j (x * y) z) =
      lowerCentralClass (i + j + 1) (centralBracketRep i j x z) +
        lowerCentralClass (i + j + 1) (centralBracketRep i j y z)
  rw [show
    centralBracketRep i j (x * y) z =
        ⟨(x : G) * (centralBracketRep i j y z : G) * (x : G)⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G (i + j + 1)).Normal).conj_mem
              (centralBracketRep i j y z : G)
              (centralBracketRep i j y z).property x⟩ *
          centralBracketRep i j x z by
      apply Subtype.ext
      exact element_mul_left (x : G) (y : G) (z : G)]
  rw [lower_class_mul, lower_class_conj]
  exact add_comm _ _

/-- The associated-graded commutator class is additive in its right representative. -/
theorem central_bracket_right
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y z : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j x (y * z) =
      centralBracketClass i j x y +
        centralBracketClass i j x z := by
  change
    lowerCentralClass (i + j + 1) (centralBracketRep i j x (y * z)) =
      lowerCentralClass (i + j + 1) (centralBracketRep i j x y) +
        lowerCentralClass (i + j + 1) (centralBracketRep i j x z)
  rw [show
    centralBracketRep i j x (y * z) =
        centralBracketRep i j x y *
          ⟨(y : G) * (centralBracketRep i j x z : G) * (y : G)⁻¹,
            (inferInstance :
              (Subgroup.lowerCentralSeries G (i + j + 1)).Normal).conj_mem
                (centralBracketRep i j x z : G)
                (centralBracketRep i j x z).property y⟩ by
      apply Subtype.ext
      simpa only [mul_assoc] using
        element_mul_right (x : G) (y : G) (z : G)]
  rw [lower_class_mul, lower_class_conj]

@[simp]
theorem bracket_inv_left
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j x⁻¹ y =
      -centralBracketClass i j x y := by
  have h := bracket_class_left i j x⁻¹ x y
  rw [inv_mul_cancel, central_bracket_class] at h
  calc
    centralBracketClass i j x⁻¹ y =
        (centralBracketClass i j x⁻¹ y +
          centralBracketClass i j x y) +
            (-centralBracketClass i j x y) := by simp
    _ = -centralBracketClass i j x y := by rw [← h, zero_add]

@[simp]
theorem bracket_inv_right
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j x y⁻¹ =
      -centralBracketClass i j x y := by
  have h := central_bracket_right i j x y⁻¹ y
  rw [inv_mul_cancel, bracket_class_right] at h
  calc
    centralBracketClass i j x y⁻¹ =
        (centralBracketClass i j x y⁻¹ +
          centralBracketClass i j x y) +
            (-centralBracketClass i j x y) := by simp
    _ = -centralBracketClass i j x y := by rw [← h, zero_add]

/-- Raising the left representative by one lower-central degree kills its bracket class. -/
theorem central_bracket_succ
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (hx : (x : G) ∈ Subgroup.lowerCentralSeries G (i + 1))
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j x y = 0 := by
  change
    Additive.ofMul
        (lowerClassHom (i + j + 1)
          (centralBracketRep i j x y)) =
      0
  change
    lowerClassHom (i + j + 1)
        (centralBracketRep i j x y) =
      1
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅(x : G), (y : G)⁆ ∈ Subgroup.lowerCentralSeries G ((i + j + 1) + 1)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    lower_commutator_succ (i + 1) j
      (Subgroup.commutator_mem_commutator hx y.property)

/-- Raising the right representative by one lower-central degree kills its bracket class. -/
theorem lower_bracket_succ
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (hy : (y : G) ∈ Subgroup.lowerCentralSeries G (j + 1)) :
    centralBracketClass i j x y = 0 := by
  change
    Additive.ofMul
        (lowerClassHom (i + j + 1)
          (centralBracketRep i j x y)) =
      0
  change
    lowerClassHom (i + j + 1)
        (centralBracketRep i j x y) =
      1
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅(x : G), (y : G)⁆ ∈ Subgroup.lowerCentralSeries G ((i + j + 1) + 1)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    lower_commutator_succ i (j + 1)
      (Subgroup.commutator_mem_commutator x.property hy)

/-- The graded bracket depends only on the associated-graded class of its left input. -/
theorem bracket_congr_left
    (i j : ℕ)
    (x y : Subgroup.lowerCentralSeries G i)
    (z : Subgroup.lowerCentralSeries G j)
    (hxy : (x : G) * (y : G)⁻¹ ∈ Subgroup.lowerCentralSeries G (i + 1)) :
    centralBracketClass i j x z =
      centralBracketClass i j y z := by
  let e : Subgroup.lowerCentralSeries G i :=
    ⟨(x : G) * (y : G)⁻¹,
      Subgroup.lowerCentralSeries_antitone (Nat.le_succ i) hxy⟩
  have hx : x = e * y := by
    apply Subtype.ext
    change (x : G) = ((x : G) * (y : G)⁻¹) * (y : G)
    group
  rw [hx, bracket_class_left,
    central_bracket_succ i j e hxy,
    zero_add]

/-- The graded bracket depends only on the associated-graded class of its right input. -/
theorem bracket_congr_right
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y z : Subgroup.lowerCentralSeries G j)
    (hyz : (y : G) * (z : G)⁻¹ ∈ Subgroup.lowerCentralSeries G (j + 1)) :
    centralBracketClass i j x y =
      centralBracketClass i j x z := by
  let e : Subgroup.lowerCentralSeries G j :=
    ⟨(y : G) * (z : G)⁻¹,
      Subgroup.lowerCentralSeries_antitone (Nat.le_succ j) hyz⟩
  have hy : y = e * z := by
    apply Subtype.ext
    change (y : G) = ((y : G) * (z : G)⁻¹) * (z : G)
    group
  rw [hy, central_bracket_right,
    lower_bracket_succ i j x e hyz,
    zero_add]

end TBluepr
end Towers

noncomputable section

namespace Towers
namespace TBluepr

universe u

variable {G : Type u} [Group G]

/-- Before quotienting the left input, graded bracketing with a fixed right representative. -/
def bracketRepHom
    (i j : ℕ)
    (y : Subgroup.lowerCentralSeries G j) :
    Subgroup.lowerCentralSeries G i →*
      LowerGradedLayer G (i + j + 1) where
  toFun x :=
    lowerClassHom (i + j + 1)
      (centralBracketRep i j x y)
  map_one' := by
    apply Additive.ofMul.injective
    change centralBracketClass i j 1 y = 0
    exact central_bracket_class i j y
  map_mul' x z := by
    apply Additive.ofMul.injective
    change
      centralBracketClass i j (x * z) y =
        centralBracketClass i j x y +
          centralBracketClass i j z y
    exact bracket_class_left i j x z y

/-- Graded bracketing with a fixed right representative, lifted through the left layer. -/
def lowerBracketHom
    (i j : ℕ)
    (y : Subgroup.lowerCentralSeries G j) :
    LowerGradedLayer G i →*
      LowerGradedLayer G (i + j + 1) :=
  QuotientGroup.lift
    ((Subgroup.lowerCentralSeries G (i + 1)).subgroupOf
      (Subgroup.lowerCentralSeries G i))
    (bracketRepHom i j y)
    (by
      intro x hx
      apply Additive.ofMul.injective
      change centralBracketClass i j x y = 0
      exact central_bracket_succ i j x hx y)

@[simp]
theorem bracket_left_mk
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    lowerBracketHom i j y
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G (i + 1)).subgroupOf
            (Subgroup.lowerCentralSeries G i)) x) =
      lowerClassHom (i + j + 1)
        (centralBracketRep i j x y) :=
  rfl

/-- Before quotienting the right input, graded bracketing as a homomorphism on the left layer. -/
def lowerBracketRep
    (i j : ℕ) :
    Subgroup.lowerCentralSeries G j →*
      (LowerGradedLayer G i →*
        LowerGradedLayer G (i + j + 1)) where
  toFun y := lowerBracketHom i j y
  map_one' := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply Additive.ofMul.injective
    change centralBracketClass i j x 1 = 0
    exact bracket_class_right i j x
  map_mul' y z := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply Additive.ofMul.injective
    change
      centralBracketClass i j x (y * z) =
        centralBracketClass i j x y +
          centralBracketClass i j x z
    exact central_bracket_right i j x y z

/--
The lower-central associated-graded bracket, multiplicatively packaged as a
homomorphism in each input.
-/
def centralBracketHom
    (i j : ℕ) :
    LowerGradedLayer G j →*
      (LowerGradedLayer G i →*
        LowerGradedLayer G (i + j + 1)) :=
  QuotientGroup.lift
    ((Subgroup.lowerCentralSeries G (j + 1)).subgroupOf
      (Subgroup.lowerCentralSeries G j))
    (lowerBracketRep i j)
    (by
      intro y hy
      apply MonoidHom.ext
      intro q
      refine QuotientGroup.induction_on q ?_
      intro x
      apply Additive.ofMul.injective
      change centralBracketClass i j x y = 0
      exact lower_bracket_succ i j x y hy)

@[simp]
theorem central_bracket_mk
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketHom i j
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G (j + 1)).subgroupOf
            (Subgroup.lowerCentralSeries G j)) y)
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G (i + 1)).subgroupOf
            (Subgroup.lowerCentralSeries G i)) x) =
      lowerClassHom (i + j + 1)
        (centralBracketRep i j x y) :=
  rfl

/-- Additive form of the lower-central associated-graded bracket. -/
def lowerCentralBracket
    (i j : ℕ) :
    Additive (LowerGradedLayer G j) →+
      (Additive (LowerGradedLayer G i) →+
        Additive (LowerGradedLayer G (i + j + 1))) where
  toFun y :=
    { toFun := fun x =>
        Additive.ofMul (centralBracketHom i j y.toMul x.toMul)
      map_zero' := by simp
      map_add' := by simp }
  map_zero' := by
    ext x
    simp
  map_add' y z := by
    ext x
    simp

@[simp]
theorem lower_bracket_mk
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    lowerCentralBracket i j
        (Additive.ofMul
          (QuotientGroup.mk'
            ((Subgroup.lowerCentralSeries G (j + 1)).subgroupOf
              (Subgroup.lowerCentralSeries G j)) y))
        (Additive.ofMul
          (QuotientGroup.mk'
            ((Subgroup.lowerCentralSeries G (i + 1)).subgroupOf
              (Subgroup.lowerCentralSeries G i)) x)) =
      centralBracketClass i j x y :=
  rfl

end TBluepr
end Towers

noncomputable section

namespace Towers
namespace TBluepr

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The reversed commutator represented in the canonical degree of `[x,y]`. -/
def bracketSwapRep
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    Subgroup.lowerCentralSeries G (i + j + 1) :=
  ⟨⁅(y : G), (x : G)⁆, by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      lower_commutator_succ j i
        (Subgroup.commutator_mem_commutator y.property x.property)⟩

/-- The reversed representative is the inverse of the original bracket. -/
@[simp]
theorem bracket_rep_inv
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    bracketSwapRep i j x y =
      (centralBracketRep i j x y)⁻¹ := by
  apply Subtype.ext
  exact (commutatorElement_inv (x : G) (y : G)).symm

/-- Reversing a graded commutator negates its class in the canonical target degree. -/
theorem bracket_swap_rep
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    lowerCentralClass (i + j + 1) (bracketSwapRep i j x y) =
      -centralBracketClass i j x y := by
  rw [bracket_rep_inv, centralBracketClass,
    lower_class_inv]

/-- Conjugating the left representative does not change its graded bracket class. -/
theorem bracket_conj_left
    (i j : ℕ)
    (g : G)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j
        ⟨g * (x : G) * g⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G i).Normal).conj_mem
              (x : G) x.property g⟩ y =
      centralBracketClass i j x y := by
  apply bracket_congr_left
  change g * (x : G) * g⁻¹ * (x : G)⁻¹ ∈ Subgroup.lowerCentralSeries G (i + 1)
  simpa only [commutatorElement_def, Nat.zero_add] using
    lower_commutator_succ 0 i
      (Subgroup.commutator_mem_commutator
        (show g ∈ Subgroup.lowerCentralSeries G 0 by simp) x.property)

/-- Conjugating the right representative does not change its graded bracket class. -/
theorem bracket_conj_right
    (i j : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (g : G)
    (y : Subgroup.lowerCentralSeries G j) :
    centralBracketClass i j x
        ⟨g * (y : G) * g⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G j).Normal).conj_mem
              (y : G) y.property g⟩ =
      centralBracketClass i j x y := by
  apply bracket_congr_right
  change g * (y : G) * g⁻¹ * (y : G)⁻¹ ∈ Subgroup.lowerCentralSeries G (j + 1)
  simpa only [commutatorElement_def, Nat.zero_add] using
    lower_commutator_succ 0 j
      (Subgroup.commutator_mem_commutator
        (show g ∈ Subgroup.lowerCentralSeries G 0 by simp) y.property)

/-- A self-bracket vanishes in the associated-graded layer. -/
@[simp]
theorem lower_bracket_self
    (i : ℕ)
    (x : Subgroup.lowerCentralSeries G i) :
    centralBracketClass i i x x = 0 := by
  change lowerCentralClass (i + i + 1) (centralBracketRep i i x x) = 0
  rw [show centralBracketRep i i x x = 1 by
    apply Subtype.ext
    exact commutatorElement_self (x : G)]
  exact lower_central_one (i + i + 1)

end TBluepr
end Towers

noncomputable section

namespace Towers
namespace TBluepr

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The left-normed three-input commutator representative `[[x,y],z]`. -/
def centralTripleRep
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Subgroup.lowerCentralSeries G ((i + j + 1) + k + 1) :=
  centralBracketRep (i + j + 1) k
    (centralBracketRep i j x y) z

/-- The associated-graded class of the left-normed commutator `[[x,y],z]`. -/
def lowerCentralTriple
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Additive
      (LowerGradedLayer G ((i + j + 1) + k + 1)) :=
  centralBracketClass (i + j + 1) k
    (centralBracketRep i j x y) z

@[simp]
theorem lower_central_triple
    (i j k : ℕ)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k 1 y z = 0 := by
  change
    centralBracketClass (i + j + 1) k
      (centralBracketRep i j 1 y) z = 0
  rw [show centralBracketRep i j (1 : Subgroup.lowerCentralSeries G i) y = 1 by
    apply Subtype.ext
    exact commutatorElement_one_left (y : G)]
  exact central_bracket_class (i + j + 1) k z

@[simp]
theorem lower_central_second
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x 1 z = 0 := by
  change
    centralBracketClass (i + j + 1) k
      (centralBracketRep i j x 1) z = 0
  rw [show centralBracketRep i j x (1 : Subgroup.lowerCentralSeries G j) = 1 by
    apply Subtype.ext
    exact commutatorElement_one_right (x : G)]
  exact central_bracket_class (i + j + 1) k z

@[simp]
theorem lower_central_third
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j) :
    lowerCentralTriple i j k x y 1 = 0 :=
  bracket_class_right (i + j + 1) k
    (centralBracketRep i j x y)

/-- The graded triple class is additive in its first representative. -/
theorem triple_class_first
    (i j k : ℕ)
    (x y : Subgroup.lowerCentralSeries G i)
    (z : Subgroup.lowerCentralSeries G j)
    (w : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k (x * y) z w =
      lowerCentralTriple i j k x z w +
        lowerCentralTriple i j k y z w := by
  change
    centralBracketClass (i + j + 1) k
        (centralBracketRep i j (x * y) z) w =
      centralBracketClass (i + j + 1) k
          (centralBracketRep i j x z) w +
        centralBracketClass (i + j + 1) k
          (centralBracketRep i j y z) w
  rw [show
    centralBracketRep i j (x * y) z =
        ⟨(x : G) * (centralBracketRep i j y z : G) * (x : G)⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries G (i + j + 1)).Normal).conj_mem
              (centralBracketRep i j y z : G)
              (centralBracketRep i j y z).property x⟩ *
          centralBracketRep i j x z by
      apply Subtype.ext
      exact element_mul_left (x : G) (y : G) (z : G)]
  rw [bracket_class_left,
    bracket_conj_left]
  exact add_comm _ _

/-- The graded triple class is additive in its second representative. -/
theorem triple_class_second
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y z : Subgroup.lowerCentralSeries G j)
    (w : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x (y * z) w =
      lowerCentralTriple i j k x y w +
        lowerCentralTriple i j k x z w := by
  change
    centralBracketClass (i + j + 1) k
        (centralBracketRep i j x (y * z)) w =
      centralBracketClass (i + j + 1) k
          (centralBracketRep i j x y) w +
        centralBracketClass (i + j + 1) k
          (centralBracketRep i j x z) w
  rw [show
    centralBracketRep i j x (y * z) =
        centralBracketRep i j x y *
          ⟨(y : G) * (centralBracketRep i j x z : G) * (y : G)⁻¹,
            (inferInstance :
              (Subgroup.lowerCentralSeries G (i + j + 1)).Normal).conj_mem
                (centralBracketRep i j x z : G)
                (centralBracketRep i j x z).property y⟩ by
      apply Subtype.ext
      simpa only [mul_assoc] using
        element_mul_right (x : G) (y : G) (z : G)]
  rw [bracket_class_left,
    bracket_conj_left]

/-- The graded triple class is additive in its third representative. -/
theorem triple_class_third
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z w : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x y (z * w) =
      lowerCentralTriple i j k x y z +
        lowerCentralTriple i j k x y w :=
  central_bracket_right (i + j + 1) k
    (centralBracketRep i j x y) z w

@[simp]
theorem triple_inv_first
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x⁻¹ y z =
      -lowerCentralTriple i j k x y z := by
  have h := triple_class_first i j k x⁻¹ x y z
  rw [inv_mul_cancel, lower_central_triple] at h
  calc
    lowerCentralTriple i j k x⁻¹ y z =
        (lowerCentralTriple i j k x⁻¹ y z +
          lowerCentralTriple i j k x y z) +
            (-lowerCentralTriple i j k x y z) := by simp
    _ = -lowerCentralTriple i j k x y z := by rw [← h, zero_add]

@[simp]
theorem triple_inv_second
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x y⁻¹ z =
      -lowerCentralTriple i j k x y z := by
  have h := triple_class_second i j k x y⁻¹ y z
  rw [inv_mul_cancel, lower_central_second] at h
  calc
    lowerCentralTriple i j k x y⁻¹ z =
        (lowerCentralTriple i j k x y⁻¹ z +
          lowerCentralTriple i j k x y z) +
            (-lowerCentralTriple i j k x y z) := by simp
    _ = -lowerCentralTriple i j k x y z := by rw [← h, zero_add]

@[simp]
theorem triple_inv_third
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerCentralTriple i j k x y z⁻¹ =
      -lowerCentralTriple i j k x y z :=
  bracket_inv_right (i + j + 1) k
    (centralBracketRep i j x y) z

/--
Swapping the first two entries negates a left-normed triple class.  The
reversed inner bracket is represented directly in the original target degree.
-/
theorem triple_swap_second
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    centralBracketClass (i + j + 1) k
        (bracketSwapRep i j x y) z =
      -lowerCentralTriple i j k x y z := by
  rw [bracket_rep_inv,
    bracket_inv_left]
  rfl

end TBluepr
end Towers

noncomputable section

namespace Towers
namespace TBluepr

universe u

variable {G : Type u} [Group G]

/-- Transport lower-central representatives along an equality of zero-based degrees. -/
def lowerSeriesEquiv
    {m n : ℕ}
    (h : m = n) :
    Subgroup.lowerCentralSeries G m ≃* Subgroup.lowerCentralSeries G n := by
  subst n
  exact MulEquiv.refl _

@[simp]
theorem coe_lower_series
    {m n : ℕ}
    (h : m = n)
    (x : Subgroup.lowerCentralSeries G m) :
    ((lowerSeriesEquiv (G := G) h x :
      Subgroup.lowerCentralSeries G n) : G) = (x : G) := by
  subst n
  rfl

/-- Transport associated-graded additive layers along an equality of degrees. -/
def lowerCentralLayer
    {m n : ℕ}
    (h : m = n) :
    Additive (LowerGradedLayer G m) ≃+
      Additive (LowerGradedLayer G n) := by
  subst n
  exact AddEquiv.refl _

@[simp]
theorem lower_central_class
    {m n : ℕ}
    (h : m = n)
    (x : Subgroup.lowerCentralSeries G m) :
    lowerCentralLayer (G := G) h (lowerCentralClass m x) =
      lowerCentralClass n (lowerSeriesEquiv h x) := by
  subst n
  rfl

/-- Reverse-facing form of class-map transport for normalized representatives. -/
theorem lower_series_equiv
    {m n : ℕ}
    (h : m = n)
    (x : Subgroup.lowerCentralSeries G m) :
    lowerCentralClass n (lowerSeriesEquiv h x) =
      lowerCentralLayer (G := G) h (lowerCentralClass m x) :=
  (lower_central_class h x).symm

@[simp]
theorem lower_central_neg
    {m n : ℕ}
    (h : m = n)
    (x : Additive (LowerGradedLayer G m)) :
    lowerCentralLayer (G := G) h (-x) =
      -lowerCentralLayer h x :=
  map_neg (lowerCentralLayer (G := G) h) x

end TBluepr
end Towers

noncomputable section

namespace Towers
namespace TBluepr

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The normalized class representative `[[x,y],z]`. -/
def tripleRepXYZ
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Subgroup.lowerCentralSeries G (i + j + k + 2) :=
  lowerSeriesEquiv (G := G)
    (by omega : (i + j + 1) + k + 1 = i + j + k + 2)
    (centralTripleRep i j k x y z)

/-- The normalized cyclic class representative `[[y,z],x]`. -/
def tripleRepYZX
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Subgroup.lowerCentralSeries G (i + j + k + 2) :=
  lowerSeriesEquiv (G := G)
    (by omega : (j + k + 1) + i + 1 = i + j + k + 2)
    (centralTripleRep j k i y z x)

/-- The normalized cyclic class representative `[[z,x],y]`. -/
def tripleRepZXY
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Subgroup.lowerCentralSeries G (i + j + k + 2) :=
  lowerSeriesEquiv (G := G)
    (by omega : (k + i + 1) + j + 1 = i + j + k + 2)
    (centralTripleRep k i j z x y)

/-- The normalized associated-graded class of `[[x,y],z]`. -/
def lowerTripleXYZ
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Additive (LowerGradedLayer G (i + j + k + 2)) :=
  lowerCentralLayer (G := G)
    (by omega : (i + j + 1) + k + 1 = i + j + k + 2)
    (lowerCentralTriple i j k x y z)

/-- The normalized associated-graded class of `[[y,z],x]`. -/
def lowerTripleYZX
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Additive (LowerGradedLayer G (i + j + k + 2)) :=
  lowerCentralLayer (G := G)
    (by omega : (j + k + 1) + i + 1 = i + j + k + 2)
    (lowerCentralTriple j k i y z x)

/-- The normalized associated-graded class of `[[z,x],y]`. -/
def lowerTripleZXY
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Additive (LowerGradedLayer G (i + j + k + 2)) :=
  lowerCentralLayer (G := G)
    (by omega : (k + i + 1) + j + 1 = i + j + k + 2)
    (lowerCentralTriple k i j z x y)

@[simp]
theorem lower_triple_xyz
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleXYZ i j k x y z =
      lowerCentralClass (i + j + k + 2)
        (tripleRepXYZ i j k x y z) := by
  rw [lowerTripleXYZ, tripleRepXYZ,
    lower_series_equiv]
  rfl

@[simp]
theorem lower_triple_yzx
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleYZX i j k x y z =
      lowerCentralClass (i + j + k + 2)
        (tripleRepYZX i j k x y z) := by
  rw [lowerTripleYZX, tripleRepYZX,
    lower_series_equiv]
  rfl

@[simp]
theorem lower_triple_zxy
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleZXY i j k x y z =
      lowerCentralClass (i + j + k + 2)
        (tripleRepZXY i j k x y z) := by
  rw [lowerTripleZXY, tripleRepZXY,
    lower_series_equiv]
  rfl

/-- The rearranged Hall-Witt identity used by the graded Jacobi proof. -/
theorem commutator_witt_rearranged
    (x y z : G) :
    ⁅z, ⁅x, y⁆⁆ =
      x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ *
        y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
  simp [commutatorElement_def, mul_assoc]

/-- The lower-central associated-graded triple classes satisfy Jacobi in every degree. -/
theorem triple_class_jacobi
    (i j k : ℕ)
    (x : Subgroup.lowerCentralSeries G i)
    (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleXYZ i j k x y z +
          lowerTripleYZX i j k x y z +
        lowerTripleZXY i j k x y z =
      0 := by
  let n := i + j + k + 2
  let A : Subgroup.lowerCentralSeries G n :=
    lowerSeriesEquiv (G := G)
      (by omega : (k + i + 1) + j + 1 = n)
      (centralTripleRep k i j z⁻¹ x⁻¹ y)
  let B : Subgroup.lowerCentralSeries G n :=
    lowerSeriesEquiv (G := G)
      (by omega : (j + k + 1) + i + 1 = n)
      (centralTripleRep j k i y⁻¹ z x⁻¹)
  let Az : Subgroup.lowerCentralSeries G n :=
    ⟨(z : G) * (A : G) * (z : G)⁻¹,
      (inferInstance : (Subgroup.lowerCentralSeries G n).Normal).conj_mem
        (A : G) A.property z⟩
  let By : Subgroup.lowerCentralSeries G n :=
    ⟨(y : G) * (B : G) * (y : G)⁻¹,
      (inferInstance : (Subgroup.lowerCentralSeries G n).Normal).conj_mem
        (B : G) B.property y⟩
  let Cx : Subgroup.lowerCentralSeries G n :=
    ⟨(x : G) * ((Az * By : Subgroup.lowerCentralSeries G n) : G) * (x : G)⁻¹,
      (inferInstance : (Subgroup.lowerCentralSeries G n).Normal).conj_mem
        ((Az * By : Subgroup.lowerCentralSeries G n) : G) (Az * By).property x⟩
  have hrep : (tripleRepXYZ i j k x y z)⁻¹ = Cx := by
    apply Subtype.ext
    simp only [tripleRepXYZ, A, B, Az, By, Cx,
      coe_lower_series, Subgroup.coe_inv, Subgroup.coe_mul]
    change
      ⁅⁅(x : G), (y : G)⁆, (z : G)⁆⁻¹ =
        (x : G) *
          ((z : G) * ⁅⁅(z : G)⁻¹, (x : G)⁻¹⁆, (y : G)⁆ * (z : G)⁻¹ *
            ((y : G) * ⁅⁅(y : G)⁻¹, (z : G)⁆, (x : G)⁻¹⁆ * (y : G)⁻¹)) *
          (x : G)⁻¹
    calc
      ⁅⁅(x : G), (y : G)⁆, (z : G)⁆⁻¹ =
          ⁅(z : G), ⁅(x : G), (y : G)⁆⁆ :=
        commutatorElement_inv _ _
      _ =
          (x : G) * (z : G) *
              ⁅(y : G), ⁅(z : G)⁻¹, (x : G)⁻¹⁆⁆⁻¹ * (z : G)⁻¹ *
            (y : G) * ⁅(x : G)⁻¹, ⁅(y : G)⁻¹, (z : G)⁆⁆⁻¹ *
              (y : G)⁻¹ * (x : G)⁻¹ :=
        commutator_witt_rearranged (x : G) (y : G) (z : G)
      _ =
          (x : G) *
            ((z : G) * ⁅⁅(z : G)⁻¹, (x : G)⁻¹⁆, (y : G)⁆ * (z : G)⁻¹ *
              ((y : G) * ⁅⁅(y : G)⁻¹, (z : G)⁆, (x : G)⁻¹⁆ * (y : G)⁻¹)) *
            (x : G)⁻¹ := by
        rw [commutatorElement_inv (y : G) ⁅(z : G)⁻¹, (x : G)⁻¹⁆,
          commutatorElement_inv (x : G)⁻¹ ⁅(y : G)⁻¹, (z : G)⁆]
        group
  have hA :
      lowerCentralClass n A =
        lowerTripleZXY i j k x y z := by
    simp only [A, lower_series_equiv,
      lowerTripleZXY]
    congr 1
    change lowerCentralTriple k i j z⁻¹ x⁻¹ y =
      lowerCentralTriple k i j z x y
    simp
  have hB :
      lowerCentralClass n B =
        lowerTripleYZX i j k x y z := by
    simp only [B, lower_series_equiv,
      lowerTripleYZX]
    congr 1
    change lowerCentralTriple j k i y⁻¹ z x⁻¹ =
      lowerCentralTriple j k i y z x
    simp
  have hneg :
      -lowerTripleXYZ i j k x y z =
        lowerTripleZXY i j k x y z +
          lowerTripleYZX i j k x y z := by
    calc
      -lowerTripleXYZ i j k x y z =
          lowerCentralClass n (tripleRepXYZ i j k x y z)⁻¹ := by
        rw [lower_triple_xyz, lower_class_inv]
      _ = lowerCentralClass n Cx := by rw [hrep]
      _ = lowerCentralClass n (Az * By) :=
        lower_class_conj n (x : G) (Az * By)
      _ = lowerCentralClass n Az + lowerCentralClass n By :=
        lower_class_mul n Az By
      _ = lowerCentralClass n A + lowerCentralClass n B := by
        rw [lower_class_conj, lower_class_conj]
      _ =
          lowerTripleZXY i j k x y z +
            lowerTripleYZX i j k x y z := by rw [hA, hB]
  calc
    lowerTripleXYZ i j k x y z +
          lowerTripleYZX i j k x y z +
        lowerTripleZXY i j k x y z =
        lowerTripleXYZ i j k x y z +
          (lowerTripleZXY i j k x y z +
            lowerTripleYZX i j k x y z) := by
      abel
    _ = lowerTripleXYZ i j k x y z +
          (-lowerTripleXYZ i j k x y z) := by rw [← hneg]
    _ = 0 := by simp

end TBluepr
end Towers

/-!
# Lie identities in the lower-central associated graded

This file packages the degree casts needed to state the skew-symmetry and Jacobi
identities for the lower-central associated graded as ordinary equalities.
-/

namespace Towers
namespace TBluepr

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Reindex a lower-central associated-graded layer along an equality of degrees. -/
def lowerCentralReindex {m n : ℕ} (h : m = n) :
    Additive (LowerGradedLayer G m) ≃+
      Additive (LowerGradedLayer G n) := by
  subst n
  exact AddEquiv.refl _

@[simp]
theorem layer_reindex_rfl {n : ℕ} :
    lowerCentralReindex (G := G) (rfl : n = n) = AddEquiv.refl _ :=
  rfl

@[simp]
theorem lower_reindex_rfl {n : ℕ}
    (x : Additive (LowerGradedLayer G n)) :
    lowerCentralReindex (G := G) (rfl : n = n) x = x :=
  rfl

@[simp]
theorem lower_reindex_class {m n : ℕ} (h : m = n)
    (x : Subgroup.lowerCentralSeries G m) :
    lowerCentralReindex (G := G) h (lowerCentralClass m x) =
      lowerCentralClass n ⟨(x : G), by simpa [h] using x.property⟩ := by
  subst n
  rfl

/-- The lower-central bracket, reindexed into a specified target degree. -/
def lowerBracketClass (i j n : ℕ) (h : i + j + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    Additive (LowerGradedLayer G n) :=
  lowerCentralReindex h (lowerCentralBracket i j y x)

@[simp]
theorem lower_bracket_left
    (i j n : ℕ) (h : i + j + 1 = n)
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h 0 y = 0 := by
  simp [lowerBracketClass]

@[simp]
theorem lower_bracket_right
    (i j n : ℕ) (h : i + j + 1 = n)
    (x : Additive (LowerGradedLayer G i)) :
    lowerBracketClass i j n h x 0 = 0 := by
  simp [lowerBracketClass]

theorem central_bracket_left
    (i j n : ℕ) (h : i + j + 1 = n)
    (x x' : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h (x + x') y =
      lowerBracketClass i j n h x y +
        lowerBracketClass i j n h x' y := by
  simp [lowerBracketClass]

theorem lower_central_bracket
    (i j n : ℕ) (h : i + j + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y y' : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h x (y + y') =
      lowerBracketClass i j n h x y +
        lowerBracketClass i j n h x y' := by
  simp [lowerBracketClass]

theorem bracket_zsmul_left
    (i j n : ℕ) (h : i + j + 1 = n)
    (c : ℤ)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h (c • x) y =
      c • lowerBracketClass i j n h x y := by
  simp [lowerBracketClass]

theorem bracket_zsmul_right
    (i j n : ℕ) (h : i + j + 1 = n)
    (c : ℤ)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h x (c • y) =
      c • lowerBracketClass i j n h x y := by
  simp [lowerBracketClass]

@[simp]
theorem bracket_neg_left
    (i j n : ℕ) (h : i + j + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h (-x) y =
      -lowerBracketClass i j n h x y := by
  simp [lowerBracketClass]

@[simp]
theorem bracket_neg_right
    (i j n : ℕ) (h : i + j + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n h x (-y) =
      -lowerBracketClass i j n h x y := by
  simp [lowerBracketClass]

@[simp]
theorem lower_bracket_class
    (i j n : ℕ) (h : i + j + 1 = n)
    (x : Subgroup.lowerCentralSeries G i) (y : Subgroup.lowerCentralSeries G j) :
    lowerBracketClass i j n h
        (lowerCentralClass i x) (lowerCentralClass j y) =
      lowerCentralClass n
        ⟨⁅(x : G), (y : G)⁆, by
          rw [← h]
          exact (centralBracketRep i j x y).property⟩ := by
  subst n
  rfl

theorem lower_bracket_skew
    (i j n : ℕ)
    (hij : i + j + 1 = n) (hji : j + i + 1 = n)
    (x : Subgroup.lowerCentralSeries G i) (y : Subgroup.lowerCentralSeries G j) :
    lowerBracketClass i j n hij
        (lowerCentralClass i x) (lowerCentralClass j y) =
      -lowerBracketClass j i n hji
        (lowerCentralClass j y) (lowerCentralClass i x) := by
  rw [lower_bracket_class,
    lower_bracket_class, ← lower_class_inv]
  congr 1
  apply Subtype.ext
  exact (commutatorElement_inv (y : G) (x : G)).symm

/-- Skew-symmetry of the lower-central associated-graded bracket. -/
theorem central_bracket_skew
    (i j n : ℕ)
    (hij : i + j + 1 = n) (hji : j + i + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerBracketClass i j n hij x y =
      -lowerBracketClass j i n hji y x := by
  induction x using Additive.rec with
  | ofMul qx =>
      refine QuotientGroup.induction_on qx ?_
      intro x
      induction y using Additive.rec with
      | ofMul qy =>
          refine QuotientGroup.induction_on qy ?_
          intro y
          exact lower_bracket_skew
            i j n hij hji x y

/-- A representative for a nested lower-central bracket in a specified degree. -/
def lowerTripleRep (i j k n : ℕ)
    (h : (i + j + 1) + k + 1 = n)
    (x : Subgroup.lowerCentralSeries G i) (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    Subgroup.lowerCentralSeries G n :=
  ⟨⁅⁅(x : G), (y : G)⁆, (z : G)⁆, by
    rw [← h]
    exact lower_commutator_succ (i + j + 1) k
      (Subgroup.commutator_mem_commutator
        (centralBracketRep i j x y).property z.property)⟩

/-- A nested lower-central bracket, reindexed into a specified target degree. -/
def lowerTripleClass (i j k n : ℕ)
    (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    Additive (LowerGradedLayer G n) :=
  lowerCentralReindex h
    (lowerCentralBracket (i + j + 1) k z
      (lowerCentralBracket i j y x))

@[simp]
theorem lower_triple_first
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h 0 y z = 0 := by
  simp [lowerTripleClass]

@[simp]
theorem lower_triple_second
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h x 0 z = 0 := by
  simp [lowerTripleClass]

@[simp]
theorem lower_triple_third
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j)) :
    lowerTripleClass i j k n h x y 0 = 0 := by
  simp [lowerTripleClass]

theorem central_triple_first
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x x' : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h (x + x') y z =
      lowerTripleClass i j k n h x y z +
        lowerTripleClass i j k n h x' y z := by
  simp [lowerTripleClass]

theorem central_triple_second
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y y' : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h x (y + y') z =
      lowerTripleClass i j k n h x y z +
        lowerTripleClass i j k n h x y' z := by
  simp [lowerTripleClass]

theorem central_triple_third
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z z' : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h x y (z + z') =
      lowerTripleClass i j k n h x y z +
        lowerTripleClass i j k n h x y z' := by
  simp [lowerTripleClass]

@[simp]
theorem triple_neg_first
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h (-x) y z =
      -lowerTripleClass i j k n h x y z := by
  simp [lowerTripleClass]

@[simp]
theorem triple_neg_second
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h x (-y) z =
      -lowerTripleClass i j k n h x y z := by
  simp [lowerTripleClass]

@[simp]
theorem triple_neg_third
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n h x y (-z) =
      -lowerTripleClass i j k n h x y z := by
  simp [lowerTripleClass]

@[simp]
theorem lower_triple_class
    (i j k n : ℕ) (h : (i + j + 1) + k + 1 = n)
    (x : Subgroup.lowerCentralSeries G i) (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleClass i j k n h
        (lowerCentralClass i x) (lowerCentralClass j y)
        (lowerCentralClass k z) =
      lowerCentralClass n (lowerTripleRep i j k n h x y z) := by
  subst n
  rfl

/--
The rearranged Hall-Witt identity used to prove Jacobi in the lower-central
associated graded.
-/
theorem element_witt_rearranged
    (x y z : G) :
    ⁅z, ⁅x, y⁆⁆ =
      x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ *
        y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
  simp [commutatorElement_def, mul_assoc]

theorem lower_triple_jacobi
    (i j k n : ℕ)
    (hxyz : (i + j + 1) + k + 1 = n)
    (hyzx : (j + k + 1) + i + 1 = n)
    (hzxy : (k + i + 1) + j + 1 = n)
    (x : Subgroup.lowerCentralSeries G i) (y : Subgroup.lowerCentralSeries G j)
    (z : Subgroup.lowerCentralSeries G k) :
    lowerTripleClass i j k n hxyz
          (lowerCentralClass i x) (lowerCentralClass j y)
          (lowerCentralClass k z) +
        lowerTripleClass j k i n hyzx
          (lowerCentralClass j y) (lowerCentralClass k z)
          (lowerCentralClass i x) +
      lowerTripleClass k i j n hzxy
        (lowerCentralClass k z) (lowerCentralClass i x)
        (lowerCentralClass j y) =
      0 := by
  let A : Subgroup.lowerCentralSeries G n :=
    lowerTripleRep k i j n hzxy z⁻¹ x⁻¹ y
  let B : Subgroup.lowerCentralSeries G n :=
    lowerTripleRep j k i n hyzx y⁻¹ z x⁻¹
  let Az : Subgroup.lowerCentralSeries G n :=
    ⟨(z : G) * (A : G) * (z : G)⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries G n).Normal).conj_mem
          (A : G) A.property (z : G)⟩
  let By : Subgroup.lowerCentralSeries G n :=
    ⟨(y : G) * (B : G) * (y : G)⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries G n).Normal).conj_mem
          (B : G) B.property (y : G)⟩
  let Cx : Subgroup.lowerCentralSeries G n :=
    ⟨(x : G) * ((Az * By : Subgroup.lowerCentralSeries G n) : G) * (x : G)⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries G n).Normal).conj_mem
          ((Az * By : Subgroup.lowerCentralSeries G n) : G)
          (Az * By).property (x : G)⟩
  have hrep :
      (lowerTripleRep i j k n hxyz x y z)⁻¹ = Cx := by
    apply Subtype.ext
    change
      ⁅⁅(x : G), (y : G)⁆, (z : G)⁆⁻¹ =
        (x : G) * ((z : G) * ⁅⁅(z : G)⁻¹, (x : G)⁻¹⁆, (y : G)⁆ *
          (z : G)⁻¹ *
          ((y : G) * ⁅⁅(y : G)⁻¹, (z : G)⁆, (x : G)⁻¹⁆ *
            (y : G)⁻¹)) * (x : G)⁻¹
    calc
      ⁅⁅(x : G), (y : G)⁆, (z : G)⁆⁻¹ =
          ⁅(z : G), ⁅(x : G), (y : G)⁆⁆ :=
        commutatorElement_inv _ _
      _ =
          (x : G) * (z : G) * ⁅(y : G), ⁅(z : G)⁻¹, (x : G)⁻¹⁆⁆⁻¹ *
              (z : G)⁻¹ *
            (y : G) * ⁅(x : G)⁻¹, ⁅(y : G)⁻¹, (z : G)⁆⁆⁻¹ *
              (y : G)⁻¹ * (x : G)⁻¹ :=
        element_witt_rearranged
          (x : G) (y : G) (z : G)
      _ =
          (x : G) * ((z : G) * ⁅⁅(z : G)⁻¹, (x : G)⁻¹⁆, (y : G)⁆ *
            (z : G)⁻¹ *
            ((y : G) * ⁅⁅(y : G)⁻¹, (z : G)⁆, (x : G)⁻¹⁆ *
              (y : G)⁻¹)) * (x : G)⁻¹ := by
        rw [commutatorElement_inv (y : G) ⁅(z : G)⁻¹, (x : G)⁻¹⁆,
          commutatorElement_inv (x : G)⁻¹ ⁅(y : G)⁻¹, (z : G)⁆]
        group
  have hneg :
      -lowerTripleClass i j k n hxyz
          (lowerCentralClass i x) (lowerCentralClass j y)
          (lowerCentralClass k z) =
        lowerTripleClass k i j n hzxy
            (lowerCentralClass k z) (lowerCentralClass i x)
            (lowerCentralClass j y) +
          lowerTripleClass j k i n hyzx
            (lowerCentralClass j y) (lowerCentralClass k z)
            (lowerCentralClass i x) := by
    calc
      -lowerTripleClass i j k n hxyz
          (lowerCentralClass i x) (lowerCentralClass j y)
          (lowerCentralClass k z) =
          lowerCentralClass n
            (lowerTripleRep i j k n hxyz x y z)⁻¹ := by
        rw [lower_triple_class,
          lower_class_inv]
      _ = lowerCentralClass n Cx := by rw [hrep]
      _ = lowerCentralClass n (Az * By) :=
        lower_class_conj n (x : G) (Az * By)
      _ = lowerCentralClass n Az + lowerCentralClass n By :=
        lower_class_mul n Az By
      _ = lowerCentralClass n A + lowerCentralClass n B := by
        rw [lower_class_conj, lower_class_conj]
      _ =
          lowerTripleClass k i j n hzxy
              (lowerCentralClass k z⁻¹) (lowerCentralClass i x⁻¹)
              (lowerCentralClass j y) +
            lowerTripleClass j k i n hyzx
              (lowerCentralClass j y⁻¹) (lowerCentralClass k z)
              (lowerCentralClass i x⁻¹) := by
        rw [lower_triple_class,
          lower_triple_class]
      _ =
          lowerTripleClass k i j n hzxy
              (lowerCentralClass k z) (lowerCentralClass i x)
              (lowerCentralClass j y) +
            lowerTripleClass j k i n hyzx
              (lowerCentralClass j y) (lowerCentralClass k z)
              (lowerCentralClass i x) := by
        simp [lowerTripleClass]
  calc
    lowerTripleClass i j k n hxyz
          (lowerCentralClass i x) (lowerCentralClass j y)
          (lowerCentralClass k z) +
        lowerTripleClass j k i n hyzx
          (lowerCentralClass j y) (lowerCentralClass k z)
          (lowerCentralClass i x) +
      lowerTripleClass k i j n hzxy
        (lowerCentralClass k z) (lowerCentralClass i x)
        (lowerCentralClass j y) =
        lowerTripleClass i j k n hxyz
            (lowerCentralClass i x) (lowerCentralClass j y)
            (lowerCentralClass k z) +
          (lowerTripleClass k i j n hzxy
              (lowerCentralClass k z) (lowerCentralClass i x)
              (lowerCentralClass j y) +
            lowerTripleClass j k i n hyzx
              (lowerCentralClass j y) (lowerCentralClass k z)
              (lowerCentralClass i x)) := by
      abel
    _ =
        lowerTripleClass i j k n hxyz
            (lowerCentralClass i x) (lowerCentralClass j y)
            (lowerCentralClass k z) +
          (-lowerTripleClass i j k n hxyz
            (lowerCentralClass i x) (lowerCentralClass j y)
            (lowerCentralClass k z)) := by
      rw [← hneg]
    _ = 0 := by simp

/-- Jacobi identity for the lower-central associated-graded bracket. -/
theorem central_triple_jacobi
    (i j k n : ℕ)
    (hxyz : (i + j + 1) + k + 1 = n)
    (hyzx : (j + k + 1) + i + 1 = n)
    (hzxy : (k + i + 1) + j + 1 = n)
    (x : Additive (LowerGradedLayer G i))
    (y : Additive (LowerGradedLayer G j))
    (z : Additive (LowerGradedLayer G k)) :
    lowerTripleClass i j k n hxyz x y z +
        lowerTripleClass j k i n hyzx y z x +
      lowerTripleClass k i j n hzxy z x y =
      0 := by
  induction x using Additive.rec with
  | ofMul qx =>
      refine QuotientGroup.induction_on qx ?_
      intro x
      induction y using Additive.rec with
      | ofMul qy =>
          refine QuotientGroup.induction_on qy ?_
          intro y
          induction z using Additive.rec with
          | ofMul qz =>
              refine QuotientGroup.induction_on qz ?_
              intro z
              exact lower_triple_jacobi
                i j k n hxyz hyzx hzxy x y z

end TBluepr
end Towers
