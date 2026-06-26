import Submission.CantEick.HallPolynomials
import Submission.CantEick.Operations

/-!
# Abelian Hall polynomials

For an abelian consistent presentation, the Hall polynomials are the obvious
ones: multiplication is coordinatewise addition and powering is scalar
multiplication.  This supplies the formal base used by Cant--Eick's induction
approach in Section 3.
-/

namespace Submission
namespace CantEick

open scoped BigOperators

noncomputable section

variable {n : ℕ}

lemma add_list_prod {A : Type*} [AddMonoid A] (l : List (Multiplicative A)) :
    Multiplicative.toAdd l.prod = (l.map Multiplicative.toAdd).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, toAdd_mul]

lemma list_sum_apply {ι A : Type*} [AddMonoid A] (l : List (ι → A)) (i : ι) :
    l.sum i = (l.map fun f => f i).sum := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih]

/-- The standard generator of the free abelian group with coordinates `Fin n → ℤ`. -/
def freeAbelianGen {n : ℕ} (i : Fin n) : Multiplicative (Fin n → ℤ) :=
  Multiplicative.ofAdd (singleCoord i 1)

lemma z_abelian_gen {n : ℕ} (x : Fin n → ℤ) :
    orderedZPow (freeAbelianGen (n := n)) x =
      (Multiplicative.ofAdd x : Multiplicative (Fin n → ℤ)) := by
  unfold orderedZPow
  apply Multiplicative.toAdd.injective
  funext j
  rw [add_list_prod]
  rw [list_sum_apply]
  simp only [List.map_map, toAdd_ofAdd]
  rw [List.sum_map_eq_nsmul_single j]
  · simp [freeAbelianGen, singleCoord]
  · intro i hij _hi
    simp [freeAbelianGen, singleCoord, hij.symm]

/-- The coordinate system on the free abelian group `ℤ^n`, written multiplicatively. -/
noncomputable def freeAbelianSystem (n : ℕ) :
    NCSystem (Multiplicative (Fin n → ℤ)) n where
  gen := freeAbelianGen
  normalForm_bijective := by
    constructor
    · intro x y hxy
      have h := congrArg Multiplicative.toAdd hxy
      simpa [z_abelian_gen] using h
    · intro g
      refine ⟨Multiplicative.toAdd g, ?_⟩
      simp [z_abelian_gen, ofAdd_toAdd]

noncomputable def abelianConsistentPresentation
    (T : ParameterIndex 0 → ℤ) : CPres 0 T where
  G := Multiplicative (Fin 0 → ℤ)
  coords := freeAbelianSystem 0
  relation := by
    intro i
    exact Fin.elim0 i

noncomputable def freeConsistentPresentation
    (T : ParameterIndex 1 → ℤ) : CPres 1 T where
  G := Multiplicative (Fin 1 → ℤ)
  coords := freeAbelianSystem 1
  relation := by
    intro i j hij
    fin_cases i
    fin_cases j
    omega

noncomputable def freeAbelianConsistent
    (T : ParameterIndex 2 → ℤ) : CPres 2 T where
  G := Multiplicative (Fin 2 → ℤ)
  coords := freeAbelianSystem 2
  relation := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · norm_num at hij
      · simp [freeAbelianSystem, freeAbelianGen, relationTail,
          upperIndices, List.finRange, mul_comm]
    · fin_cases j
      · norm_num at hij
      · norm_num at hij

/-- The unique parameter index in rank three. -/
def rankParameterIndex : ParameterIndex 3 :=
  ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩

/--
The class-two integer model realizing an arbitrary rank-three parameter.
The last coordinate records the single commutator correction.
-/
structure RankThreeGroup (t : ℤ) where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ

@[ext]
theorem rank_three_ext {t : ℤ} {a b : RankThreeGroup t}
    (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) : a = b := by
  cases a
  cases b
  simp_all

def rankThreeMul (t : ℤ) (a b : RankThreeGroup t) : RankThreeGroup t :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2 + t * a.c1 * b.c0⟩

def rankThreeInv (t : ℤ) (a : RankThreeGroup t) : RankThreeGroup t :=
  ⟨-a.c0, -a.c1, -a.c2 + t * a.c1 * a.c0⟩

instance rankThreeGroup (t : ℤ) : Group (RankThreeGroup t) where
  mul := rankThreeMul t
  one := ⟨0, 0, 0⟩
  inv := rankThreeInv t
  mul_assoc := by
    intro a b c
    change rankThreeMul t (rankThreeMul t a b) c = rankThreeMul t a (rankThreeMul t b c)
    ext <;> simp [rankThreeMul] <;> ring_nf
  one_mul := by
    intro a
    change rankThreeMul t ⟨0, 0, 0⟩ a = a
    ext <;> simp [rankThreeMul]
  mul_one := by
    intro a
    change rankThreeMul t a ⟨0, 0, 0⟩ = a
    ext <;> simp [rankThreeMul]
  inv_mul_cancel := by
    intro a
    change rankThreeMul t (rankThreeInv t a) a = ⟨0, 0, 0⟩
    ext <;> simp [rankThreeMul, rankThreeInv]

@[simp]
lemma one_c_0 {t : ℤ} : (1 : RankThreeGroup t).c0 = 0 :=
  rfl

@[simp]
lemma rank_three_c {t : ℤ} : (1 : RankThreeGroup t).c1 = 0 :=
  rfl

@[simp]
lemma three_c_2 {t : ℤ} : (1 : RankThreeGroup t).c2 = 0 :=
  rfl

@[simp]
lemma three_c_0 {t : ℤ} (a b : RankThreeGroup t) :
    (a * b).c0 = a.c0 + b.c0 :=
  rfl

@[simp]
lemma three_c_1 {t : ℤ} (a b : RankThreeGroup t) :
    (a * b).c1 = a.c1 + b.c1 :=
  rfl

@[simp]
lemma rank_c_2 {t : ℤ} (a b : RankThreeGroup t) :
    (a * b).c2 = a.c2 + b.c2 + t * a.c1 * b.c0 :=
  rfl

@[simp]
lemma rank_c_0 {t : ℤ} (a : RankThreeGroup t) : a⁻¹.c0 = -a.c0 :=
  rfl

@[simp]
lemma rank_c_1 {t : ℤ} (a : RankThreeGroup t) : a⁻¹.c1 = -a.c1 :=
  rfl

@[simp]
lemma rank_inv_c {t : ℤ} (a : RankThreeGroup t) :
    a⁻¹.c2 = -a.c2 + t * a.c1 * a.c0 :=
  rfl

def rankThreeGen (t : ℤ) : Fin 3 → RankThreeGroup t
  | 0 => ⟨1, 0, 0⟩
  | 1 => ⟨0, 1, 0⟩
  | 2 => ⟨0, 0, 1⟩

lemma rank_gen_zpow (t z : ℤ) :
    rankThreeGen t 0 ^ z = (⟨z, 0, 0⟩ : RankThreeGroup t) := by
  induction z using Int.induction_on with
  | zero => ext <;> simp [rankThreeGen]
  | succ n ih =>
      conv_lhs => rw [zpow_add_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
  | pred n ih =>
      conv_lhs => rw [zpow_sub_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
      ring

lemma three_gen_zpow (t z : ℤ) :
    rankThreeGen t 1 ^ z = (⟨0, z, 0⟩ : RankThreeGroup t) := by
  induction z using Int.induction_on with
  | zero => ext <;> simp [rankThreeGen]
  | succ n ih =>
      conv_lhs => rw [zpow_add_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
  | pred n ih =>
      conv_lhs => rw [zpow_sub_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
      ring

lemma rank_two_zpow (t z : ℤ) :
    rankThreeGen t 2 ^ z = (⟨0, 0, z⟩ : RankThreeGroup t) := by
  induction z using Int.induction_on with
  | zero => ext <;> simp [rankThreeGen]
  | succ n ih =>
      conv_lhs => rw [zpow_add_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
  | pred n ih =>
      conv_lhs => rw [zpow_sub_one]
      rw [ih]
      ext <;> simp [rankThreeGen]
      ring

lemma ordered_z_gen (t : ℤ) (x : Fin 3 → ℤ) :
    orderedZPow (rankThreeGen t) x =
      (⟨x 0, x 1, x 2⟩ : RankThreeGroup t) := by
  norm_num [orderedZPow, List.finRange]
  rw [rank_gen_zpow, three_gen_zpow, rank_two_zpow]
  ext <;> simp

lemma relation_tail_rank (T : ParameterIndex 3 → ℤ) :
    relationTail (rankThreeGen (T rankParameterIndex)) T 0 1 (by decide) =
      rankThreeGen (T rankParameterIndex) 2 ^ T rankParameterIndex := by
  norm_num [relationTail, upperIndices, List.finRange, rankParameterIndex]
  simp [rankThreeGen]

noncomputable def rankCoordinateSystem (T : ParameterIndex 3 → ℤ) :
    NCSystem (RankThreeGroup (T rankParameterIndex)) 3 where
  gen := rankThreeGen (T rankParameterIndex)
  normalForm_bijective := by
    constructor
    · intro x y hxy
      rw [ordered_z_gen, ordered_z_gen] at hxy
      funext i
      fin_cases i
      · exact congrArg RankThreeGroup.c0 hxy
      · exact congrArg RankThreeGroup.c1 hxy
      · exact congrArg RankThreeGroup.c2 hxy
    · intro g
      refine ⟨fun i => if i = 0 then g.c0 else if i = 1 then g.c1 else g.c2, ?_⟩
      rw [ordered_z_gen]
      ext <;> simp

lemma rank_three_relation
    (T : ParameterIndex 3 → ℤ) (hij : (0 : Fin 3) < 1) :
    rankThreeGen (T rankParameterIndex) 1 *
        rankThreeGen (T rankParameterIndex) 0 =
      rankThreeGen (T rankParameterIndex) 0 *
        rankThreeGen (T rankParameterIndex) 1 *
        relationTail (rankThreeGen (T rankParameterIndex)) T 0 1 hij := by
  have htail :
      relationTail (rankThreeGen (T rankParameterIndex)) T 0 1 hij =
        rankThreeGen (T rankParameterIndex) 2 ^ T rankParameterIndex := by
    simpa using relation_tail_rank T
  rw [htail]
  rw [rank_two_zpow]
  change
    rankThreeMul (T rankParameterIndex)
        (rankThreeGen (T rankParameterIndex) 1)
        (rankThreeGen (T rankParameterIndex) 0) =
      rankThreeMul (T rankParameterIndex)
        (rankThreeMul (T rankParameterIndex)
          (rankThreeGen (T rankParameterIndex) 0)
          (rankThreeGen (T rankParameterIndex) 1))
        ⟨0, 0, T rankParameterIndex⟩
  ext <;> simp [rankThreeMul, rankThreeGen, rankParameterIndex]

lemma rank_relation_two
    (T : ParameterIndex 3 → ℤ) (hij : (0 : Fin 3) < 2) :
    rankThreeGen (T rankParameterIndex) 2 *
        rankThreeGen (T rankParameterIndex) 0 =
      rankThreeGen (T rankParameterIndex) 0 *
        rankThreeGen (T rankParameterIndex) 2 *
        relationTail (rankThreeGen (T rankParameterIndex)) T 0 2 hij := by
  ext <;> simp [rankThreeGen, relationTail, upperIndices, List.finRange]

lemma rank_three_two
    (T : ParameterIndex 3 → ℤ) (hij : (1 : Fin 3) < 2) :
    rankThreeGen (T rankParameterIndex) 2 *
        rankThreeGen (T rankParameterIndex) 1 =
      rankThreeGen (T rankParameterIndex) 1 *
        rankThreeGen (T rankParameterIndex) 2 *
        relationTail (rankThreeGen (T rankParameterIndex)) T 1 2 hij := by
  ext <;> simp [rankThreeGen, relationTail, upperIndices, List.finRange]

noncomputable def rankConsistentPresentation
    (T : ParameterIndex 3 → ℤ) : CPres 3 T where
  G := RankThreeGroup (T rankParameterIndex)
  group := rankThreeGroup (T rankParameterIndex)
  coords := rankCoordinateSystem T
  relation := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · norm_num at hij
      · simpa [rankCoordinateSystem] using
          rank_three_relation T hij
      · simpa [rankCoordinateSystem] using
          rank_relation_two T hij
    · fin_cases j
      · norm_num at hij
      · norm_num at hij
      · simpa [rankCoordinateSystem] using
          rank_three_two T hij
    · fin_cases j <;> norm_num at hij

namespace CPres

/-- The paper's base consistency case: all tuples of length at most two are consistent. -/
theorem consistent_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    IsConsistent T := by
  interval_cases n
  · exact ⟨abelianConsistentPresentation T⟩
  · exact ⟨freeConsistentPresentation T⟩
  · exact ⟨freeAbelianConsistent T⟩

/-- Every rank-three parameter tuple has a concrete consistent presentation. -/
theorem isConsistent_three (T : ParameterIndex 3 → ℤ) :
    IsConsistent T :=
  ⟨rankConsistentPresentation T⟩

/-- All tuples of length at most three are consistent. -/
theorem consistent_three
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 3) :
    IsConsistent T := by
  interval_cases n
  · exact ⟨abelianConsistentPresentation T⟩
  · exact ⟨freeConsistentPresentation T⟩
  · exact ⟨freeAbelianConsistent T⟩
  · exact isConsistent_three T

theorem locus_univ_two {n : ℕ} (hn : n ≤ 2) :
    consistencyLocus n = Set.univ := by
  ext T
  constructor
  · intro _hT
    trivial
  · intro _hT
    exact consistent_two T hn

theorem locus_univ_three {n : ℕ} (hn : n ≤ 3) :
    consistencyLocus n = Set.univ := by
  ext T
  constructor
  · intro _hT
    trivial
  · intro _hT
    exact consistent_three T hn

variable {T : ParameterIndex n → ℤ} (M : CPres n T)

lemma list_zpow_comm {ι G : Type*} [Group G] [IsMulCommutative G]
    (a : ι → G) (x y : ι → ℤ) :
    ∀ l : List ι,
      ((l.map fun i => a i ^ (x i + y i)).prod) =
        ((l.map fun i => a i ^ x i).prod) *
          ((l.map fun i => a i ^ y i).prod)
  | [] => by simp
  | i :: l => by
      simp only [List.map_cons, List.prod_cons]
      rw [zpow_add]
      rw [list_zpow_comm a x y l]
      ac_rfl

lemma prod_zpow_comm {ι G : Type*} [Group G] [IsMulCommutative G]
    (a : ι → G) (x : ι → ℤ) (z : ℤ) :
    ∀ l : List ι,
      ((l.map fun i => a i ^ x i).prod) ^ z =
        ((l.map fun i => a i ^ (x i * z)).prod)
  | [] => by simp
  | i :: l => by
      simp only [List.map_cons, List.prod_cons]
      rw [(show Commute (a i ^ x i)
        (List.map (fun i => a i ^ x i) l).prod from mul_comm' _ _).mul_zpow]
      rw [prod_zpow_comm a x z l, zpow_mul]

lemma normal_add_comm [IsMulCommutative M.G] (x y : Fin n → ℤ) :
    M.normalWord (fun i => x i + y i) =
      M.normalWord x * M.normalWord y := by
  simpa [normalWord, orderedZPow, gen] using
    list_zpow_comm M.gen x y (List.finRange n)

lemma normal_zpow_comm [IsMulCommutative M.G] (x : Fin n → ℤ) (z : ℤ) :
    M.normalWord x ^ z = M.normalWord (fun i => x i * z) := by
  simpa [normalWord, orderedZPow, gen] using
    prod_zpow_comm M.gen x z (List.finRange n)

lemma single_coord_comm [IsMulCommutative M.G]
    (i j : Fin n) (v u : ℤ) :
    M.normalWord (fun k => singleCoord i v k + singleCoord j u k) =
      M.gen i ^ v * M.gen j ^ u := by
  rw [normal_add_comm]
  rw [normal_single_coord, normal_single_coord]

lemma single_coord_ne
    (i j k : Fin n) (hij : i ≠ j) (v u : ℤ) :
    singleCoord i v k + singleCoord j u k =
      if k = i then v else if k = j then u else 0 := by
  by_cases hki : k = i
  · subst k
    simp [singleCoord, hij]
  · by_cases hkj : k = j
    · subst k
      simp [singleCoord, hij.symm]
    · simp [singleCoord, hki, hkj]

lemma normal_coord_comm [IsMulCommutative M.G]
    (i j : Fin n) (hij : i ≠ j) (v u : ℤ) :
    M.normalWord (fun k => if k = i then v else if k = j then u else 0) =
      M.gen i ^ v * M.gen j ^ u := by
  have hfun : (fun k => if k = i then v else if k = j then u else 0) =
      fun k => singleCoord i v k + singleCoord j u k := by
    funext k
    rw [single_coord_ne i j k hij v u]
  rw [hfun]
  exact M.single_coord_comm i j v u

/-- The abelian multiplication polynomial `F_i(x,y)=x_i+y_i`. -/
def abelianMultiplicationPolynomial (i : Fin n) :
    MvPolynomial (MulVar n) ℚ :=
  MvPolynomial.X (MulVar.left i) + MvPolynomial.X (MulVar.right i)

/-- The abelian powering polynomial `K_i(x,z)=x_i z`. -/
def abelianPoweringPolynomial (i : Fin n) :
    MvPolynomial (PowerVar n) ℚ :=
  MvPolynomial.X (PowerVar.coord i) * MvPolynomial.X PowerVar.exponent

/-- In an abelian presentation the tail conjugation polynomials are zero. -/
def abelianConjugationPolynomial (_I : ParameterIndex n) :
    MvPolynomial (ConjVar n) ℚ :=
  0

@[simp]
lemma abelian_multiplication_polynomial
    (T : ParameterIndex n → ℤ) (x y : Fin n → ℤ) (i : Fin n) :
    evalMulPolynomial T x y (abelianMultiplicationPolynomial i) =
      (x i + y i : ℚ) := by
  simp [abelianMultiplicationPolynomial, evalMulPolynomial, evalMulVar,
    mulVarQ]

/-- The left-associated abelian multiplication polynomial is `x_i + y_i + w_i`. -/
@[simp]
lemma assoc_left_multiplication (i : Fin n) :
    assocLeftPolynomial abelianMultiplicationPolynomial i =
      (MvPolynomial.X (AssocVar.x i) + MvPolynomial.X (AssocVar.y i)) +
        MvPolynomial.X (AssocVar.w i) := by
  simp [assocLeftPolynomial, assocLeftSubst, abelianMultiplicationPolynomial,
    MulVar.toAssocXY]

/-- The right-associated abelian multiplication polynomial is `x_i + y_i + w_i`. -/
@[simp]
lemma assoc_abelian_multiplication (i : Fin n) :
    assocRightPolynomial abelianMultiplicationPolynomial i =
      MvPolynomial.X (AssocVar.x i) +
        (MvPolynomial.X (AssocVar.y i) + MvPolynomial.X (AssocVar.w i)) := by
  simp [assocRightPolynomial, assocRightSubst, abelianMultiplicationPolynomial,
    MulVar.toAssocYW]

/--
The abelian multiplication Hall polynomials are associatively exact as
polynomials, before any parameter specialization.
-/
@[simp]
theorem associator_polynomial_multiplication (i : Fin n) :
    associatorPolynomial abelianMultiplicationPolynomial i = 0 := by
  simp [associatorPolynomial, add_assoc]

/-- Evaluation form of the abelian associator identity. -/
@[simp]
theorem eval_associator_multiplication
    (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ) (i : Fin n) :
    evalAssocPolynomial T x y w (associatorPolynomial abelianMultiplicationPolynomial i) =
      0 := by
  simp [evalAssocPolynomial]

/--
All parameter-coefficient polynomials of the abelian associator are zero.
-/
@[simp]
theorem associator_abelian_multiplication
    (i : Fin n) (m : TripleVar n →₀ ℕ) :
    associatorCoefficientPolynomial abelianMultiplicationPolynomial i m = 0 := by
  simp [associatorCoefficientPolynomial, assocTriplePolynomial]

/--
The Section 4 obstruction ideal of the abelian multiplication polynomials is
the zero ideal.
-/
@[simp]
theorem consistency_abelian_multiplication :
    consistencyObstructionIdeal
      (abelianMultiplicationPolynomial : Fin n → MvPolynomial (MulVar n) ℚ) =
      ⊥ := by
  apply le_antisymm
  · rw [consistency_obstruction_ideal]
    intro i m
    simp
  · exact bot_le

/--
The abelian obstruction ideal is contained in every vanishing ideal, in every
rank.
-/
theorem consistency_vanishing_multiplication
    (T : ParameterIndex n → ℤ) :
    consistencyObstructionIdeal abelianMultiplicationPolynomial ≤ vanishingIdealAt T := by
  rw [consistency_abelian_multiplication]
  exact bot_le

/--
All-rank abelian remainder corollary for parameter polynomials.
-/
theorem remainder_consistency_multiplication
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ consistencyObstructionIdeal abelianMultiplicationPolynomial) :
    parameterEvaluation T r = parameterEvaluation T p :=
  remainder_vanishing_ideal T
    (consistency_vanishing_multiplication T h)

/--
All-rank abelian specialized multiplication remainder corollary.
-/
theorem remainder_coeff_abelian
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r)) :
    specializeMul T r = specializeMul T p :=
  specialize_remainder_coefficientwise
    abelianMultiplicationPolynomial
    (fun i x y w => by simp [evalAssocPolynomial])
    h

/--
All-rank abelian multiplication remainder corollary on integer inputs.
-/
theorem coeff_consistency_abelian
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r))
    (x y : Fin n → ℤ) :
    evalMulPolynomial T x y r = evalMulPolynomial T x y p :=
  remainder_coefficientwise_ideal
    abelianMultiplicationPolynomial
    (fun i x y w => by simp [evalAssocPolynomial])
    h x y

/--
All-rank abelian specialized powering remainder corollary.
-/
theorem specialize_consistency_abelian
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r)) :
    specializePower T r = specializePower T p :=
  specialize_remainder_sub
    abelianMultiplicationPolynomial
    (fun i x y w => by simp [evalAssocPolynomial])
    h

/--
All-rank abelian powering remainder corollary on integer inputs.
-/
theorem remainder_sub_abelian
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r))
    (x : Fin n → ℤ) (z : ℤ) :
    evalPowerPolynomial T x z r = evalPowerPolynomial T x z p :=
  remainder_consistency_ideal
    abelianMultiplicationPolynomial
    (fun i x y w => by simp [evalAssocPolynomial])
    h x z

/--
The abelian multiplication polynomials satisfy the obstruction equations for
every parameter tuple, in every rank.
-/
theorem consistency_locus_abelian
    (T : ParameterIndex n → ℤ) :
    consistencyObstructionLocus abelianMultiplicationPolynomial T := by
  intro p hp
  rcases hp with ⟨⟨i, m⟩, rfl⟩
  simp

/--
The obstruction zero locus of the abelian multiplication polynomials is all of
parameter space.
-/
@[simp]
theorem locus_abelian_univ :
    {T : ParameterIndex n → ℤ |
      consistencyObstructionLocus abelianMultiplicationPolynomial T} =
      Set.univ := by
  ext T
  constructor
  · intro _hT
    trivial
  · intro _hT
    exact consistency_locus_abelian T

@[simp]
lemma abelian_powering_polynomial
    (T : ParameterIndex n → ℤ) (x : Fin n → ℤ) (z : ℤ) (i : Fin n) :
    evalPowerPolynomial T x z (abelianPoweringPolynomial i) =
      (x i * z : ℚ) := by
  simp [abelianPoweringPolynomial, evalPowerPolynomial, evalPowerVar,
    evalVarQ]

@[simp]
lemma abelian_conjugation_polynomial
    (T : ParameterIndex n → ℤ) (u v : ℤ) (I : ParameterIndex n) :
    evalConjPolynomial T u v (abelianConjugationPolynomial I) = 0 := by
  simp [abelianConjugationPolynomial, evalConjPolynomial]

/-- In an abelian consistent presentation, coordinatewise addition represents multiplication. -/
theorem representsMultiplication_abelian [IsMulCommutative M.G] :
    RepresentsMultiplication M abelianMultiplicationPolynomial := by
  intro x y i
  rw [abelian_multiplication_polynomial]
  have hword :
      M.normalWord (fun i => x i + y i) =
        M.normalWord x * M.normalWord y :=
    M.normal_add_comm x y
  have hcoord := congrFun (M.coord_normalWord (fun i => x i + y i)) i
  rw [hword] at hcoord
  simpa only [Int.cast_add] using
    congrArg (fun z : ℤ => (z : ℚ)) hcoord.symm

/-- In an abelian consistent presentation, scalar multiplication represents powering. -/
theorem representsPowering_abelian [IsMulCommutative M.G] :
    RepresentsPowering M abelianPoweringPolynomial := by
  intro x z i
  rw [abelian_powering_polynomial]
  have hword :
      M.normalWord x ^ z = M.normalWord (fun i => x i * z) :=
    M.normal_zpow_comm x z
  have hcoord := congrFun (M.coord_normalWord (fun i => x i * z)) i
  rw [← hword] at hcoord
  simpa only [Int.cast_mul] using
    congrArg (fun z : ℤ => (z : ℚ)) hcoord.symm

/-- In an abelian consistent presentation, zero tail polynomials represent conjugation. -/
theorem representsConjugation_abelian [IsMulCommutative M.G] :
    RepresentsConjugation M abelianConjugationPolynomial := by
  intro i j hij u v k
  let pair : Fin n → ℤ := fun k => if k = i then v else if k = j then u else 0
  have hword : M.normalWord pair = M.gen j ^ u * M.gen i ^ v := by
    rw [M.normal_coord_comm i j (ne_of_lt hij) v u]
    exact mul_comm' _ _
  have hcoord := congrFun (M.coord_normalWord pair) k
  rw [hword] at hcoord
  change (M.coord (M.gen j ^ u * M.gen i ^ v) k : ℚ) =
    conjugationCoordinateQ T abelianConjugationPolynomial i j hij u v k
  rw [hcoord]
  by_cases hki : k = i
  · subst k
    simp [pair, conjugationCoordinateQ]
  · by_cases hkj : k = j
    · subst k
      simp [pair, conjugationCoordinateQ, ne_of_gt hij]
    · by_cases hjk : j < k
      · simp [pair, conjugationCoordinateQ, hki, hkj, hjk]
      · simp [pair, conjugationCoordinateQ, hki, hkj, hjk]

/--
The abelian Hall-polynomial families represent multiplication, powering, and
conjugation simultaneously.
-/
theorem represents_polynomials_abelian [IsMulCommutative M.G] :
    RepresentsHallPolynomials M abelianMultiplicationPolynomial
      abelianPoweringPolynomial abelianConjugationPolynomial :=
  ⟨M.representsMultiplication_abelian, M.representsPowering_abelian,
    M.representsConjugation_abelian⟩

/--
In any commutative consistent presentation, the abelian multiplication
polynomials form a uniform evaluation method.
-/
theorem mul_method_abelian [IsMulCommutative M.G] :
    MulEvaluationMethod M abelianMultiplicationPolynomial :=
  mul_evaluation_method M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    M.represents_polynomials_abelian

/--
In any commutative consistent presentation, the parameter-specialized abelian
multiplication polynomials form a uniform evaluation method.
-/
theorem specialized_evaluation_abelian [IsMulCommutative M.G] :
    SpecializedMulMethod M abelianMultiplicationPolynomial :=
  specialized_method_hall M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    M.represents_polynomials_abelian

/--
In any commutative consistent presentation, the abelian powering polynomials
form a uniform evaluation method.
-/
theorem evaluation_method_abelian [IsMulCommutative M.G] :
    PowerEvaluationMethod M abelianPoweringPolynomial :=
  power_evaluation_method M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    M.represents_polynomials_abelian

/--
In any commutative consistent presentation, the parameter-specialized abelian
powering polynomials form a uniform evaluation method.
-/
theorem specialized_method_abelian [IsMulCommutative M.G] :
    SpecializedEvaluationMethod M abelianPoweringPolynomial :=
  specialized_method_represents M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    M.represents_polynomials_abelian

/--
All-rank commutative-presentation form of the Section 6 operation methods for
the abelian Hall polynomials.
-/
theorem operationMethods_abelian [IsMulCommutative M.G] :
    MulEvaluationMethod M abelianMultiplicationPolynomial ∧
      SpecializedMulMethod M abelianMultiplicationPolynomial ∧
      PowerEvaluationMethod M abelianPoweringPolynomial ∧
      SpecializedEvaluationMethod M abelianPoweringPolynomial :=
  ⟨M.mul_method_abelian,
    M.specialized_evaluation_abelian,
    M.evaluation_method_abelian,
    M.specialized_method_abelian⟩

/-- A length-zero consistent presentation is the trivial group. -/
theorem mul_commutative_zero
    {T : ParameterIndex 0 → ℤ} (M : CPres 0 T) :
    IsMulCommutative M.G := by
  refine ⟨Std.Commutative.mk ?_⟩
  intro g h
  have hgcoord : M.coord g = fun _ => 0 := by
    funext i
    exact Fin.elim0 i
  have hhcoord : M.coord h = fun _ => 0 := by
    funext i
    exact Fin.elim0 i
  have hg : g = 1 := by
    rw [← M.normalWord_coord g, hgcoord, M.normalWord_zero]
  have hh : h = 1 := by
    rw [← M.normalWord_coord h, hhcoord, M.normalWord_zero]
  simp [hg, hh]

lemma normal_word_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T)
    (x : Fin 1 → ℤ) :
    M.normalWord x = M.gen 0 ^ x 0 := by
  norm_num [normalWord, orderedZPow, gen, List.finRange]

/-- A length-one consistent presentation is cyclic, hence commutative. -/
theorem mul_commutative_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T) :
    IsMulCommutative M.G := by
  refine ⟨Std.Commutative.mk ?_⟩
  intro g h
  let x : ℤ := M.coord g 0
  let y : ℤ := M.coord h 0
  have hg : g = M.gen 0 ^ x := by
    rw [← M.normalWord_coord g]
    simp [normal_word_one, x]
  have hh : h = M.gen 0 ^ y := by
    rw [← M.normalWord_coord h]
    simp [normal_word_one, y]
  rw [hg, hh]
  exact zpow_mul_comm (M.gen 0) x y

theorem representsMultiplication_zero
    {T : ParameterIndex 0 → ℤ} (M : CPres 0 T) :
    RepresentsMultiplication M abelianMultiplicationPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_zero M
  exact M.representsMultiplication_abelian

theorem representsPowering_zero
    {T : ParameterIndex 0 → ℤ} (M : CPres 0 T) :
    RepresentsPowering M abelianPoweringPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_zero M
  exact M.representsPowering_abelian

theorem representsConjugation_zero
    {T : ParameterIndex 0 → ℤ} (M : CPres 0 T)
    (R : ParameterIndex 0 → MvPolynomial (ConjVar 0) ℚ) :
    RepresentsConjugation M R := by
  intro i
  exact Fin.elim0 i

theorem hall_polynomials_zero
    {T : ParameterIndex 0 → ℤ} (M : CPres 0 T) :
    RepresentsHallPolynomials M abelianMultiplicationPolynomial
      abelianPoweringPolynomial abelianConjugationPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_zero M
  exact M.represents_polynomials_abelian

theorem representsMultiplication_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T) :
    RepresentsMultiplication M abelianMultiplicationPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_one M
  exact M.representsMultiplication_abelian

theorem representsPowering_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T) :
    RepresentsPowering M abelianPoweringPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_one M
  exact M.representsPowering_abelian

theorem representsConjugation_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T)
    (R : ParameterIndex 1 → MvPolynomial (ConjVar 1) ℚ) :
    RepresentsConjugation M R := by
  intro i j hij
  fin_cases i
  fin_cases j
  omega

theorem represents_polynomials_one
    {T : ParameterIndex 1 → ℤ} (M : CPres 1 T) :
    RepresentsHallPolynomials M abelianMultiplicationPolynomial
      abelianPoweringPolynomial abelianConjugationPolynomial := by
  letI : IsMulCommutative M.G := mul_commutative_one M
  exact M.represents_polynomials_abelian

lemma relation_tail_zero
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    relationTail M.gen T 0 1 (by decide) = 1 := by
  norm_num [relationTail, upperIndices, gen, List.finRange]

lemma gen_commute_one
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    Commute (M.gen 0) (M.gen 1) := by
  have hrel := M.relation 0 1 (by decide)
  norm_num [relationTail, upperIndices, gen, List.finRange] at hrel
  change M.gen 0 * M.gen 1 = M.gen 1 * M.gen 0
  exact hrel.symm

lemma normal_word_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T)
    (x : Fin 2 → ℤ) :
    M.normalWord x = M.gen 0 ^ x 0 * M.gen 1 ^ x 1 := by
  norm_num [normalWord, orderedZPow, gen, List.finRange]

/-- A length-two consistent presentation is abelian; its single relation says
the two generators commute, and every element has a unique normal form in
those generators. -/
theorem commutative_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    IsMulCommutative M.G := by
  refine ⟨Std.Commutative.mk ?_⟩
  intro g h
  let x : Fin 2 → ℤ := M.coord g
  let y : Fin 2 → ℤ := M.coord h
  have hg : g = M.gen 0 ^ x 0 * M.gen 1 ^ x 1 := by
    rw [← M.normalWord_coord g]
    simp [normal_word_two, x]
  have hh : h = M.gen 0 ^ y 0 * M.gen 1 ^ y 1 := by
    rw [← M.normalWord_coord h]
    simp [normal_word_two, y]
  rw [hg, hh]
  let A := M.gen 0 ^ x 0
  let B := M.gen 1 ^ x 1
  let C := M.gen 0 ^ y 0
  let D := M.gen 1 ^ y 1
  change A * B * (C * D) = C * D * (A * B)
  have hab : Commute (M.gen 0) (M.gen 1) :=
    M.gen_commute_one
  have hAC : Commute A C := by
    exact (Commute.refl (M.gen 0)).zpow_zpow (x 0) (y 0)
  have hAD : Commute A D := by
    exact hab.zpow_zpow (x 0) (y 1)
  have hBC : Commute B C := by
    exact hab.symm.zpow_zpow (x 1) (y 0)
  have hBD : Commute B D := by
    exact (Commute.refl (M.gen 1)).zpow_zpow (x 1) (y 1)
  exact ((hAC.mul_right hAD).mul_left (hBC.mul_right hBD)).eq

theorem representsMultiplication_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    RepresentsMultiplication M abelianMultiplicationPolynomial := by
  letI : IsMulCommutative M.G := commutative_two M
  exact M.representsMultiplication_abelian

theorem representsPowering_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    RepresentsPowering M abelianPoweringPolynomial := by
  letI : IsMulCommutative M.G := commutative_two M
  exact M.representsPowering_abelian

theorem representsConjugation_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T)
    (R : ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ) :
    RepresentsConjugation M R := by
  intro i j hij u v k
  fin_cases i
  · fin_cases j
    · omega
    · fin_cases k
      · have hword :
            M.normalWord (fun k : Fin 2 => if k = 0 then v else if k = 1 then u else 0) =
              M.gen 1 ^ u * M.gen 0 ^ v := by
          rw [normal_word_two]
          simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
          exact (M.gen_commute_one.zpow_zpow v u).eq
        have hcoord := congrFun
          (M.coord_normalWord
            (fun k : Fin 2 => if k = 0 then v else if k = 1 then u else 0)) 0
        rw [hword] at hcoord
        change (M.coord (M.gen 1 ^ u * M.gen 0 ^ v) 0 : ℚ) =
          conjugationCoordinateQ T R 0 1 (by decide) u v 0
        norm_num at hcoord
        rw [hcoord]
        simp [conjugationCoordinateQ]
      · have hword :
            M.normalWord (fun k : Fin 2 => if k = 0 then v else if k = 1 then u else 0) =
              M.gen 1 ^ u * M.gen 0 ^ v := by
          rw [normal_word_two]
          simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
          exact (M.gen_commute_one.zpow_zpow v u).eq
        have hcoord := congrFun
          (M.coord_normalWord
            (fun k : Fin 2 => if k = 0 then v else if k = 1 then u else 0)) 1
        rw [hword] at hcoord
        change (M.coord (M.gen 1 ^ u * M.gen 0 ^ v) 1 : ℚ) =
          conjugationCoordinateQ T R 0 1 (by decide) u v 1
        norm_num at hcoord
        rw [hcoord]
        simp [conjugationCoordinateQ]
  · fin_cases j
    · norm_num at hij
    · norm_num at hij

/--
The rank-three conjugation family.  There is only one tail slot,
`R_{0,1,2}`, and it is represented by the monomial `T_{0,1,2} u v`.
-/
def rankThreeConjugation (I : ParameterIndex 3) :
    MvPolynomial (ConjVar 3) ℚ :=
  MvPolynomial.X (ConjVar.param I) *
    MvPolynomial.X ConjVar.u * MvPolynomial.X ConjVar.v

@[simp]
lemma rank_conjugation_polynomial
    (T : ParameterIndex 3 → ℤ) (u v : ℤ) (I : ParameterIndex 3) :
    evalConjPolynomial T u v (rankThreeConjugation I) =
      (T I : ℚ) * (u : ℚ) * (v : ℚ) := by
  simp [rankThreeConjugation, evalConjPolynomial, evalConjVar,
    varQ]

/--
Every rank-three consistent presentation has represented conjugation
polynomials, unconditionally.
-/
theorem representsConjugation_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    RepresentsConjugation M rankThreeConjugation := by
  intro i j hij u v k
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · fin_cases k
      · change (M.conjugationTuple 0 1 u v 0 : ℚ) =
          conjugationCoordinateQ T rankThreeConjugation 0 1
            (by decide) u v 0
        rw [M.conjugation_tuple_three]
        simp [conjugationCoordinateQ]
      · change (M.conjugationTuple 0 1 u v 1 : ℚ) =
          conjugationCoordinateQ T rankThreeConjugation 0 1
            (by decide) u v 1
        rw [M.conjugation_tuple_three]
        simp [conjugationCoordinateQ]
      · change (M.conjugationTuple 0 1 u v 2 : ℚ) =
          conjugationCoordinateQ T rankThreeConjugation 0 1
            (by decide) u v 2
        rw [M.conjugation_tuple_three]
        simp [conjugationCoordinateQ, rankThreeConjugation,
          evalConjPolynomial, evalConjVar, varQ]
        ring
    · exact represents_conjugation_last M
        rankThreeConjugation 0 k hij u v
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact represents_conjugation_last M
        rankThreeConjugation 1 k hij u v
  · fin_cases j <;> norm_num at hij

theorem represents_conjugation_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    ∃ R : ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ,
      RepresentsConjugation M R :=
  ⟨rankThreeConjugation, M.representsConjugation_three⟩

/--
The central-tail monomial family used by the rank-four penultimate-generator
conjugation slots.  It represents the `(0,2,3)` and `(1,2,3)` slots directly;
the harder `(0,1,3)` slot needs the full rank-four collection formula.
-/
def rankTailConjugation (I : ParameterIndex 4) :
    MvPolynomial (ConjVar 4) ℚ :=
  MvPolynomial.X (ConjVar.param I) *
    MvPolynomial.X ConjVar.u * MvPolynomial.X ConjVar.v

def conjChooseV {n : ℕ} : MvPolynomial (ConjVar n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) * MvPolynomial.X ConjVar.v *
    (MvPolynomial.X ConjVar.v - 1)

def conjChooseU {n : ℕ} : MvPolynomial (ConjVar n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) * MvPolynomial.X ConjVar.u *
    (MvPolynomial.X ConjVar.u - 1)

@[simp]
lemma rank_four_conjugation
    (T : ParameterIndex 4 → ℤ) (u v : ℤ) (I : ParameterIndex 4) :
    evalConjPolynomial T u v (rankTailConjugation I) =
      (T I : ℚ) * (u : ℚ) * (v : ℚ) := by
  simp [rankTailConjugation, evalConjPolynomial,
    evalConjVar, varQ]

@[simp]
lemma conj_choose_v
    {n : ℕ} (T : ParameterIndex n → ℤ) (u v : ℤ) :
    evalConjPolynomial T u v (conjChooseV (n := n)) =
      ((chooseTwoInt v : ℤ) : ℚ) := by
  rw [choose_cast_rat]
  simp [conjChooseV, evalConjPolynomial, evalConjVar,
    varQ]
  ring

@[simp]
lemma conj_choose_u
    {n : ℕ} (T : ParameterIndex n → ℤ) (u v : ℤ) :
    evalConjPolynomial T u v (conjChooseU (n := n)) =
      ((chooseTwoInt u : ℤ) : ℚ) := by
  rw [choose_cast_rat]
  simp [conjChooseU, evalConjPolynomial, evalConjVar,
    varQ]
  ring

/--
Rank-four first-generator conjugation at `u = 1`.  This is the polynomial
visible in the paper's step-2 recursion for the remaining `(0,1)` slot.
-/
def rankFourConjugation (I : ParameterIndex 4) :
    MvPolynomial (ConjVar 4) ℚ :=
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  if I = I012 then
    MvPolynomial.X (ConjVar.param I012) * MvPolynomial.X ConjVar.v
  else if I = I013 then
    MvPolynomial.X (ConjVar.param I013) * MvPolynomial.X ConjVar.v +
      MvPolynomial.X (ConjVar.param I012) *
        MvPolynomial.X (ConjVar.param I023) * conjChooseV
  else
    rankTailConjugation I

/--
The full rank-four conjugation family.  The `(0,1,2)` coordinate is the
linear tail parameter, `(0,1,3)` is the two-step central exponent, and the
two penultimate-generator coordinates are central-tail monomials.
-/
def fourConjugationPolynomial (I : ParameterIndex 4) :
    MvPolynomial (ConjVar 4) ℚ :=
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I123 : ParameterIndex 4 :=
    ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  if I = I012 then
    MvPolynomial.X (ConjVar.param I012) *
      MvPolynomial.X ConjVar.u * MvPolynomial.X ConjVar.v
  else if I = I013 then
    MvPolynomial.X (ConjVar.param I013) *
        MvPolynomial.X ConjVar.u * MvPolynomial.X ConjVar.v +
      MvPolynomial.X (ConjVar.param I012) *
          MvPolynomial.X (ConjVar.param I023) *
          MvPolynomial.X ConjVar.u * conjChooseV +
      MvPolynomial.X (ConjVar.param I012) *
          MvPolynomial.X (ConjVar.param I123) *
          MvPolynomial.X ConjVar.v * conjChooseU
  else
    rankTailConjugation I

/--
Rank-four penultimate-generator conjugation is represented unconditionally.
The only tail in `a₂^u aᵢ^v` for `i < 2` is the central last generator.
-/
theorem represents_conjugation_penultimate
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (i k : Fin 4) (hi : i < (2 : Fin 4)) (u v : ℤ) :
    (M.coord (M.gen 2 ^ u * M.gen i ^ v) k : ℚ) =
      conjugationCoordinateQ T rankTailConjugation
        i 2 hi u v k := by
  simpa [rankTailConjugation,
    centralTailConjugation] using
      conjugation_penultimate_coordinate M i k hi u v

set_option linter.flexible false in
/--
The `u = 1` slice of the remaining rank-four first-generator pair `(0,1)` is
already represented by an explicit quadratic polynomial in `v`.
-/
theorem represents_conjugation_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (v : ℤ) (k : Fin 4) :
    (M.conjugationTuple 0 1 1 v k : ℚ) =
      conjugationCoordinateQ T rankFourConjugation
        0 1 (by decide) 1 v k := by
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  fin_cases k
  · change (M.conjugationTuple 0 1 1 v 0 : ℚ) =
      conjugationCoordinateQ T rankFourConjugation
        0 1 (by decide) 1 v 0
    rw [M.conjugation_tuple_four]
    simp [conjugationCoordinateQ]
  · change (M.conjugationTuple 0 1 1 v 1 : ℚ) =
      conjugationCoordinateQ T rankFourConjugation
        0 1 (by decide) 1 v 1
    rw [M.conjugation_tuple_four]
    simp [conjugationCoordinateQ]
  · change (M.conjugationTuple 0 1 1 v 2 : ℚ) =
      conjugationCoordinateQ T rankFourConjugation
        0 1 (by decide) 1 v 2
    rw [M.conjugation_tuple_four]
    simp [conjugationCoordinateQ, rankFourConjugation,
      evalConjPolynomial, evalConjVar, varQ]
  · change (M.conjugationTuple 0 1 1 v 3 : ℚ) =
      conjugationCoordinateQ T rankFourConjugation
        0 1 (by decide) 1 v 3
    rw [M.conjugation_tuple_four]
    simp [conjugationCoordinateQ, rankFourConjugation,
      conjChooseV, evalConjPolynomial, evalConjVar, varQ]
    rw [choose_cast_rat]
    left
    ring

set_option linter.flexible false in
/--
The full rank-four first-generator pair `(0,1)` is represented by
`fourConjugationPolynomial`.
-/
theorem represents_conjugation_coordinate
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) (k : Fin 4) :
    (M.conjugationTuple 0 1 u v k : ℚ) =
      conjugationCoordinateQ T fourConjugationPolynomial
        0 1 (by decide) u v k := by
  fin_cases k
  · change (M.conjugationTuple 0 1 u v 0 : ℚ) =
      conjugationCoordinateQ T fourConjugationPolynomial
        0 1 (by decide) u v 0
    rw [M.conjugation_zero_four]
    simp [conjugationCoordinateQ]
  · change (M.conjugationTuple 0 1 u v 1 : ℚ) =
      conjugationCoordinateQ T fourConjugationPolynomial
        0 1 (by decide) u v 1
    rw [M.conjugation_zero_four]
    simp [conjugationCoordinateQ]
  · change (M.conjugationTuple 0 1 u v 2 : ℚ) =
      conjugationCoordinateQ T fourConjugationPolynomial
        0 1 (by decide) u v 2
    rw [M.conjugation_zero_four]
    simp [conjugationCoordinateQ, fourConjugationPolynomial,
      evalConjPolynomial, evalConjVar, varQ]
    ring
  · change (M.conjugationTuple 0 1 u v 3 : ℚ) =
      conjugationCoordinateQ T fourConjugationPolynomial
        0 1 (by decide) u v 3
    rw [M.conjugation_zero_four]
    simp [conjugationCoordinateQ, fourConjugationPolynomial,
      conjChooseV, conjChooseU,
      evalConjPolynomial, evalConjVar, varQ, twoStepExponent]
    rw [choose_cast_rat, choose_cast_rat]
    ring

/--
Every rank-four consistent presentation has represented conjugation
polynomials, unconditionally.
-/
theorem representsConjugation_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    RepresentsConjugation M fourConjugationPolynomial := by
  intro i j hij u v k
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · exact M.represents_conjugation_coordinate u v k
    · exact M.represents_conjugation_penultimate
        0 k (by decide) u v
    · exact represents_conjugation_last M
        fourConjugationPolynomial 0 k hij u v
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact M.represents_conjugation_penultimate
        1 k (by decide) u v
    · exact represents_conjugation_last M
        fourConjugationPolynomial 1 k hij u v
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact represents_conjugation_last M
        fourConjugationPolynomial 2 k hij u v
  · fin_cases j <;> norm_num at hij

theorem conjugation_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    ∃ R : ParameterIndex 4 → MvPolynomial (ConjVar 4) ℚ,
      RepresentsConjugation M R :=
  ⟨fourConjugationPolynomial, M.representsConjugation_four⟩

theorem represents_hall_two
    {T : ParameterIndex 2 → ℤ} (M : CPres 2 T) :
    RepresentsHallPolynomials M abelianMultiplicationPolynomial
      abelianPoweringPolynomial abelianConjugationPolynomial := by
  letI : IsMulCommutative M.G := commutative_two M
  exact M.represents_polynomials_abelian

/--
Paper-style base case for the Section 3 induction: every consistent
presentation of length at most two is abelian.
-/
theorem mul_commutative_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    IsMulCommutative M.G := by
  interval_cases n
  · exact mul_commutative_zero M
  · exact mul_commutative_one M
  · exact commutative_two M

/--
Paper-style base case for the Section 3 induction: for `n ≤ 2`, the
coordinatewise abelian Hall-polynomial families represent multiplication,
powering, and conjugation.
-/
theorem represents_hall_polynomials
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    RepresentsHallPolynomials M abelianMultiplicationPolynomial
      abelianPoweringPolynomial abelianConjugationPolynomial := by
  letI : IsMulCommutative M.G := M.mul_commutative_two hn
  exact M.represents_polynomials_abelian

/--
Base case in the shape needed by the global Hall-polynomial existence theorem:
for every already-consistent presentation of length at most two, some Hall
polynomial families represent multiplication, powering, and conjugation.
-/
theorem hall_polynomials_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R :=
  ⟨abelianMultiplicationPolynomial, abelianPoweringPolynomial,
    abelianConjugationPolynomial, M.represents_hall_polynomials hn⟩

/--
The explicit rank-three multiplication family obtained by feeding the
rank-two abelian Hall families and the rank-three conjugation family into the
seed-free U/W local assembly.
-/
noncomputable def rankMultiplicationPolynomial :
    Fin 3 → MvPolynomial (MulVar 3) ℚ :=
  displayMultiplicationFamily
    (n := 2)
    (abelianMultiplicationPolynomial : Fin 2 → MvPolynomial (MulVar 2) ℚ)
    (abelianPoweringPolynomial : Fin 2 → MvPolynomial (PowerVar 2) ℚ)
    rankThreeConjugation

/--
The explicit rank-three powering family from the seed-free U/W local
assembly, with the quotient input supplied by the rank-two abelian powering
family.
-/
noncomputable def rankPoweringPolynomial :
    Fin 3 → MvPolynomial (PowerVar 3) ℚ :=
  uwPoweringSolution
    (n := 2)
    (abelianMultiplicationPolynomial : Fin 2 → MvPolynomial (MulVar 2) ℚ)
    (abelianPoweringPolynomial : Fin 2 → MvPolynomial (PowerVar 2) ℚ)
    rankThreeConjugation
    (abelianPoweringPolynomial : Fin 2 → MvPolynomial (PowerVar 2) ℚ)

/--
The explicit rank-three conjugation family after the local assembly has
installed the delete-first tail coordinates.
-/
noncomputable def rankConjugationPolynomial :
    ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ :=
  conj1U
    (n := 2)
    (abelianMultiplicationPolynomial : Fin 2 → MvPolynomial (MulVar 2) ℚ)
    (abelianPoweringPolynomial : Fin 2 → MvPolynomial (PowerVar 2) ℚ)
    (abelianConjugationPolynomial :
      ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ)
    rankThreeConjugation

/--
The named rank-three Hall-polynomial families represent multiplication,
powering, and conjugation for every already-consistent rank-three
presentation.
-/
theorem represents_polynomials
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    RepresentsHallPolynomials M
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial := by
  have hHallU :
      RepresentsHallPolynomials M.deleteFirstConsistent
        (abelianMultiplicationPolynomial :
          Fin 2 → MvPolynomial (MulVar 2) ℚ)
        (abelianPoweringPolynomial :
          Fin 2 → MvPolynomial (PowerVar 2) ℚ)
        (abelianConjugationPolynomial :
          ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ) :=
    M.deleteFirstConsistent.represents_hall_polynomials
      (by decide)
  have hHallW :
      RepresentsHallPolynomials M.deleteConsistentPresentation
        (abelianMultiplicationPolynomial :
          Fin 2 → MvPolynomial (MulVar 2) ℚ)
        (abelianPoweringPolynomial :
          Fin 2 → MvPolynomial (PowerVar 2) ℚ)
        (abelianConjugationPolynomial :
          ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ) :=
    M.deleteConsistentPresentation.represents_hall_polynomials
      (by decide)
  simpa [rankMultiplicationPolynomial, rankPoweringPolynomial,
    rankConjugationPolynomial] using
    uw_solution_full
      M rankThreeConjugation
      (abelianMultiplicationPolynomial :
        Fin 2 → MvPolynomial (MulVar 2) ℚ)
      (abelianPoweringPolynomial :
        Fin 2 → MvPolynomial (PowerVar 2) ℚ)
      (abelianConjugationPolynomial :
        ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ)
      (abelianMultiplicationPolynomial :
        Fin 2 → MvPolynomial (MulVar 2) ℚ)
      (abelianPoweringPolynomial :
        Fin 2 → MvPolynomial (PowerVar 2) ℚ)
      (abelianConjugationPolynomial :
        ParameterIndex 2 → MvPolynomial (ConjVar 2) ℚ)
      M.representsConjugation_three hHallU hHallW

/--
Exact rank-three Hall-polynomial existence.  The ambient conjugation family is
the explicit monomial `T_{0,1,2} u v`; the two lower-rank presentations used by
the local U/W assembly are rank-two abelian base cases.
-/
theorem polynomials_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    ∃ (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
      (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ)
      (R : ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ),
        RepresentsHallPolynomials M F K R := by
  exact
    ⟨rankMultiplicationPolynomial, rankPoweringPolynomial,
      rankConjugationPolynomial, M.represents_polynomials⟩

/--
Base range for the global induction with rank three included: every already
consistent presentation of length at most three has represented Hall
polynomials without any represented ambient conjugation hypothesis.
-/
theorem hall_polynomials_three
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 3) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R := by
  interval_cases n
  · exact M.hall_polynomials_two (by decide)
  · exact M.hall_polynomials_two (by decide)
  · exact M.hall_polynomials_two (by decide)
  · exact M.polynomials_three

/--
The explicit rank-four multiplication family obtained by feeding the named
rank-three Hall families and the rank-four conjugation family into the
seed-free U/W local assembly.
-/
noncomputable def rankFourMultiplication :
    Fin 4 → MvPolynomial (MulVar 4) ℚ :=
  displayMultiplicationFamily
    (n := 3)
    rankMultiplicationPolynomial
    rankPoweringPolynomial
    fourConjugationPolynomial

/--
The explicit rank-four powering family from the seed-free U/W local assembly,
with both lower-rank subquotients supplied by the named rank-three families.
-/
noncomputable def rankFourPowering :
    Fin 4 → MvPolynomial (PowerVar 4) ℚ :=
  uwPoweringSolution
    (n := 3)
    rankMultiplicationPolynomial
    rankPoweringPolynomial
    fourConjugationPolynomial
    rankPoweringPolynomial

/--
The explicit rank-four conjugation family after the local assembly installs
delete-first tail coordinates from the named rank-three conjugation family.
-/
noncomputable def rankFourPolynomial :
    ParameterIndex 4 → MvPolynomial (ConjVar 4) ℚ :=
  conj1U
    (n := 3)
    rankMultiplicationPolynomial
    rankPoweringPolynomial
    rankConjugationPolynomial
    fourConjugationPolynomial

/--
The named rank-four Hall-polynomial families represent multiplication,
powering, and conjugation for every already-consistent rank-four
presentation.
-/
theorem represents_polynomials_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    RepresentsHallPolynomials M
      rankFourMultiplication
      rankFourPowering
      rankFourPolynomial := by
  have hHallU :
      RepresentsHallPolynomials M.deleteFirstConsistent
        rankMultiplicationPolynomial
        rankPoweringPolynomial
        rankConjugationPolynomial :=
    M.deleteFirstConsistent.represents_polynomials
  have hHallW :
      RepresentsHallPolynomials M.deleteConsistentPresentation
        rankMultiplicationPolynomial
        rankPoweringPolynomial
        rankConjugationPolynomial :=
    M.deleteConsistentPresentation.represents_polynomials
  simpa [rankFourMultiplication, rankFourPowering,
    rankFourPolynomial] using
    uw_solution_full
      M fourConjugationPolynomial
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      M.representsConjugation_four hHallU hHallW

/--
Exact rank-four Hall-polynomial existence.  The ambient conjugation family is
the explicit rank-four family, and both lower-rank presentations in the
seed-free U/W assembly are covered by the rank-three base range.
-/
theorem polynomials_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    ∃ (F : Fin 4 → MvPolynomial (MulVar 4) ℚ)
      (K : Fin 4 → MvPolynomial (PowerVar 4) ℚ)
      (R : ParameterIndex 4 → MvPolynomial (ConjVar 4) ℚ),
        RepresentsHallPolynomials M F K R := by
  exact
    ⟨rankFourMultiplication, rankFourPowering,
      rankFourPolynomial, M.represents_polynomials_four⟩

/--
Base range for the global induction with rank four included: every already
consistent presentation of length at most four has represented Hall
polynomials without any represented ambient conjugation hypothesis.
-/
theorem hall_polynomials_four
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 4) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R := by
  interval_cases n
  · exact M.hall_polynomials_two (by decide)
  · exact M.hall_polynomials_two (by decide)
  · exact M.hall_polynomials_two (by decide)
  · exact M.polynomials_three
  · exact M.polynomials_four

/--
Section 6 base-case consequence: for `n ≤ 2`, the abelian multiplication
polynomials form a uniform evaluation method.
-/
theorem mul_method_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    MulEvaluationMethod M abelianMultiplicationPolynomial :=
  mul_evaluation_method M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Section 6 base-case consequence after parameter specialization.
-/
theorem specialized_mul_method
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    SpecializedMulMethod M abelianMultiplicationPolynomial :=
  specialized_method_hall M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Powering-method base-case consequence for `n ≤ 2`.
-/
theorem evaluation_method_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    PowerEvaluationMethod M abelianPoweringPolynomial :=
  power_evaluation_method M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Specialized powering-method base-case consequence for `n ≤ 2`.
-/
theorem specialized_method_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    SpecializedEvaluationMethod M abelianPoweringPolynomial :=
  specialized_method_represents M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Combined Section 6 base-case consequence: the abelian Hall polynomials provide
the uniform multiplication and powering methods, before and after parameter
specialization.
-/
theorem operation_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    MulEvaluationMethod M abelianMultiplicationPolynomial ∧
      SpecializedMulMethod M abelianMultiplicationPolynomial ∧
      PowerEvaluationMethod M abelianPoweringPolynomial ∧
      SpecializedEvaluationMethod M abelianPoweringPolynomial :=
  ⟨M.mul_method_two hn,
    M.specialized_mul_method hn,
    M.evaluation_method_two hn,
    M.specialized_method_two hn⟩

/--
Section 6 operation-method consequence for the named rank-three Hall
families.
-/
theorem operationMethods_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    MulEvaluationMethod M rankMultiplicationPolynomial ∧
      SpecializedMulMethod M rankMultiplicationPolynomial ∧
      PowerEvaluationMethod M rankPoweringPolynomial ∧
      SpecializedEvaluationMethod M rankPoweringPolynomial :=
  ⟨mul_evaluation_method M
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      M.represents_polynomials,
    specialized_method_hall M
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      M.represents_polynomials,
    power_evaluation_method M
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      M.represents_polynomials,
    specialized_method_represents M
      rankMultiplicationPolynomial
      rankPoweringPolynomial
      rankConjugationPolynomial
      M.represents_polynomials⟩

/--
Section 6 operation-method consequence in exact rank three, obtained from the
explicit rank-three Hall-polynomial package.
-/
theorem operation_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    ∃ (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
      (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  ⟨rankMultiplicationPolynomial, rankPoweringPolynomial,
    M.operationMethods_three⟩

/--
Section 6 operation-method consequence for every already-consistent
presentation of length at most three.
-/
theorem operation_methods
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 3) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  operation_methods_polynomials M
    (M.hall_polynomials_three hn)

/--
Section 6 operation-method consequence for the named rank-four Hall
families.
-/
theorem operationMethods_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    MulEvaluationMethod M rankFourMultiplication ∧
      SpecializedMulMethod M rankFourMultiplication ∧
      PowerEvaluationMethod M rankFourPowering ∧
      SpecializedEvaluationMethod M rankFourPowering :=
  ⟨mul_evaluation_method M
      rankFourMultiplication
      rankFourPowering
      rankFourPolynomial
      M.represents_polynomials_four,
    specialized_method_hall M
      rankFourMultiplication
      rankFourPowering
      rankFourPolynomial
      M.represents_polynomials_four,
    power_evaluation_method M
      rankFourMultiplication
      rankFourPowering
      rankFourPolynomial
      M.represents_polynomials_four,
    specialized_method_represents M
      rankFourMultiplication
      rankFourPowering
      rankFourPolynomial
      M.represents_polynomials_four⟩

/--
Section 6 operation-method consequence in exact rank four, obtained from the
explicit rank-four Hall-polynomial package.
-/
theorem methods_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    ∃ (F : Fin 4 → MvPolynomial (MulVar 4) ℚ)
      (K : Fin 4 → MvPolynomial (PowerVar 4) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  ⟨rankFourMultiplication, rankFourPowering,
    M.operationMethods_four⟩

/--
Section 6 operation-method consequence for every already-consistent
presentation of length at most four.
-/
theorem operation_four
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 4) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  operation_methods_polynomials M
    (M.hall_polynomials_four hn)

/--
Section 4 obstruction package in exact rank three, obtained without a
represented ambient conjugation hypothesis.
-/
theorem obstruction_package
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    ∃ (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
      (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ)
      (R : ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex 3) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  obstruction_package_polynomials M
    M.polynomials_three

/--
Section 4 obstruction package for every already-consistent presentation of
length at most three.
-/
theorem obstruction_package_three
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 3) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  obstruction_package_polynomials M
    (M.hall_polynomials_three hn)

/--
Section 4 obstruction package in exact rank four, obtained without a
represented ambient conjugation hypothesis.
-/
theorem package_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    ∃ (F : Fin 4 → MvPolynomial (MulVar 4) ℚ)
      (K : Fin 4 → MvPolynomial (PowerVar 4) ℚ)
      (R : ParameterIndex 4 → MvPolynomial (ConjVar 4) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex 4) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar 4) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar 4) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar 4) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar 4) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  obstruction_package_polynomials M
    M.polynomials_four

/--
Section 4 obstruction package for every already-consistent presentation of
length at most four.
-/
theorem obstruction_package_four
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 4) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  obstruction_package_polynomials M
    (M.hall_polynomials_four hn)

/--
Section 4 base-case consequence: the specialized associator polynomial
vanishes for the abelian multiplication Hall polynomials.
-/
theorem specialized_associator_zero
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) (i : Fin n) :
    specializeAssoc T (associatorPolynomial abelianMultiplicationPolynomial i) = 0 :=
  specialized_associator_represents M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) i

/--
Section 4 base-case coefficient form of associator vanishing.
-/
theorem specialized_associator_coeff
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    (i : Fin n) (m : TripleVar n →₀ ℕ) :
    (specializeAssoc T (associatorPolynomial abelianMultiplicationPolynomial i)).coeff m =
      0 :=
  specialized_associator_polynomials M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) i m

/--
Section 4 base-case parameter-coefficient form.
-/
theorem associator_vanishes_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    (i : Fin n) (m : TripleVar n →₀ ℕ) :
    parameterEvaluation T
        (associatorCoefficientPolynomial abelianMultiplicationPolynomial i m) =
      0 :=
  associator_vanishes_polynomials M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) i m

/--
Section 4 base-case zero-locus theorem.
-/
theorem consistency_locus_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    consistencyObstructionLocus abelianMultiplicationPolynomial T :=
  consistency_locus_polynomials M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Section 4 base-case ideal form.
-/
theorem consistency_vanishing_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2) :
    consistencyObstructionIdeal abelianMultiplicationPolynomial ≤ vanishingIdealAt T :=
  consistency_vanishing_polynomials M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn)

/--
Section 4 base-case remainder corollary for parameter polynomials.
-/
theorem remainder_sub_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ consistencyObstructionIdeal abelianMultiplicationPolynomial) :
    parameterEvaluation T r = parameterEvaluation T p :=
  remainder_obstruction_polynomials
    M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) h

/--
Section 4 base-case specialized multiplication remainder corollary.
-/
theorem specialize_remainder_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r)) :
    specializeMul T r = specializeMul T p :=
  specialize_remainder_consistency
    M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) h

/--
Section 4 base-case multiplication remainder corollary on integer inputs.
-/
theorem eval_remainder_consistency
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r))
    (x y : Fin n → ℤ) :
    evalMulPolynomial T x y r = evalMulPolynomial T x y p :=
  remainder_coeff_polynomials
    M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) h x y

/--
Section 4 base-case specialized powering remainder corollary.
-/
theorem specialize_remainder_coeff
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r)) :
    specializePower T r = specializePower T p :=
  specialize_remainder_polynomials
    M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) h

/--
Section 4 base-case powering remainder corollary on integer inputs.
-/
theorem remainder_consistency_two
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (hn : n ≤ 2)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r))
    (x : Fin n → ℤ) (z : ℤ) :
    evalPowerPolynomial T x z r = evalPowerPolynomial T x z p :=
  remainder_consistency_polynomials
    M
    abelianMultiplicationPolynomial
    abelianPoweringPolynomial
    abelianConjugationPolynomial
    (M.represents_hall_polynomials hn) h x z

/--
Parameter-only base-case associator vanishing: for `n ≤ 2`, no explicit
consistent presentation hypothesis is needed.
-/
theorem specialized_associator_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) (i : Fin n) :
    specializeAssoc T (associatorPolynomial abelianMultiplicationPolynomial i) = 0 := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.specialized_associator_zero hn i

/--
Parameter-only base-case coefficient form of associator vanishing.
-/
theorem specialized_associator_abelian
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    (i : Fin n) (m : TripleVar n →₀ ℕ) :
    (specializeAssoc T (associatorPolynomial abelianMultiplicationPolynomial i)).coeff m =
      0 := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.specialized_associator_coeff hn i m

/--
Parameter-only base-case form for associator coefficient polynomials.
-/
theorem associator_vanishes_abelian
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    (i : Fin n) (m : TripleVar n →₀ ℕ) :
    parameterEvaluation T
        (associatorCoefficientPolynomial abelianMultiplicationPolynomial i m) =
      0 := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.associator_vanishes_two hn i m

/--
Parameter-only base-case zero-locus theorem.
-/
theorem consistency_obstruction_locus
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    consistencyObstructionLocus abelianMultiplicationPolynomial T := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.consistency_locus_two hn

/--
Parameter-only base-case obstruction-ideal containment.
-/
theorem consistency_obstruction_vanishing
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    consistencyObstructionIdeal abelianMultiplicationPolynomial ≤ vanishingIdealAt T := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.consistency_vanishing_two hn

/--
Parameter-only base-case remainder corollary for parameter polynomials.
-/
theorem remainder_abelian_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ consistencyObstructionIdeal abelianMultiplicationPolynomial) :
    parameterEvaluation T r = parameterEvaluation T p := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.remainder_sub_two hn h

/--
Parameter-only base-case specialized multiplication remainder corollary.
-/
theorem remainder_consistency_abelian
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r)) :
    specializeMul T r = specializeMul T p := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.specialize_remainder_two hn h

/--
Parameter-only base-case multiplication remainder corollary on integer inputs.
-/
theorem remainder_sub_consistency
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (mulInputPolynomial p) (mulInputPolynomial r))
    (x y : Fin n → ℤ) :
    evalMulPolynomial T x y r = evalMulPolynomial T x y p := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.eval_remainder_consistency hn h x y

/--
Parameter-only base-case specialized powering remainder corollary.
-/
theorem specialize_remainder_abelian
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r)) :
    specializePower T r = specializePower T p := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.specialize_remainder_coeff hn h

/--
Parameter-only base-case powering remainder corollary on integer inputs.
-/
theorem remainder_coeff_consistency
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2)
    {p r : MvPolynomial (PowerVar n) ℚ}
    (h : coefficientwiseSubMem
      (consistencyObstructionIdeal abelianMultiplicationPolynomial)
      (powerInputPolynomial p) (powerInputPolynomial r))
    (x : Fin n → ℤ) (z : ℤ) :
    evalPowerPolynomial T x z r = evalPowerPolynomial T x z p := by
  rcases consistent_two T hn with ⟨M⟩
  exact M.remainder_consistency_two hn h x z

/--
Section 4 base-case obstruction package: for `n ≤ 2`, the abelian
presentation and Hall-polynomial families exist for every parameter tuple, and
the full obstruction/remainder package holds without caller-supplied
representation data.
-/
theorem obstruction_package_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    ∃ (M : CPres n T)
      (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p := by
  rcases consistent_two T hn with ⟨M⟩
  refine
    ⟨M, abelianMultiplicationPolynomial, abelianPoweringPolynomial,
      abelianConjugationPolynomial, M.represents_hall_polynomials hn,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.consistency_locus_two hn
  · exact M.consistency_vanishing_two hn
  · intro p r h
    exact M.remainder_sub_two hn h
  · intro p r h
    exact
      M.specialize_remainder_two
        hn h
  · intro p r h x y
    exact
      M.eval_remainder_consistency
        hn h x y
  · intro p r h
    exact
      M.specialize_remainder_coeff
        hn h
  · intro p r h x z
    exact
      M.remainder_consistency_two
        hn h x z

/--
Section 4 package in exact rank three, with the concrete rank-three
presentation constructed from the parameter tuple.
-/
theorem package_parameter_three
    (T : ParameterIndex 3 → ℤ) :
    ∃ (M : CPres 3 T)
      (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
      (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ)
      (R : ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex 3) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar 3) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p := by
  let M := rankConsistentPresentation T
  rcases M.obstruction_package with
    ⟨F, K, R, hHall, hZero, hIdeal, hParam, hSpecMul, hEvalMul,
      hSpecPower, hEvalPower⟩
  exact
    ⟨M, F, K, R, hHall, hZero, hIdeal, hParam, hSpecMul, hEvalMul,
      hSpecPower, hEvalPower⟩

/--
Section 4 package for all parameter tuples of length at most three.  The
rank-three case uses the concrete class-two model above; lower ranks use the
free abelian base presentations.
-/
theorem obstruction_package_parameter
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 3) :
    ∃ (M : CPres n T)
      (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p := by
  rcases consistent_three T hn with ⟨M⟩
  rcases M.obstruction_package_three hn with
    ⟨F, K, R, hHall, hZero, hIdeal, hParam, hSpecMul, hEvalMul,
      hSpecPower, hEvalPower⟩
  exact
    ⟨M, F, K, R, hHall, hZero, hIdeal, hParam, hSpecMul, hEvalMul,
      hSpecPower, hEvalPower⟩

/--
Section 4 conjecture in the base cases: when `n ≤ 2`, every parameter tuple is
consistent, so every obstruction zero-locus is contained in the consistency
locus.
-/
theorem consistency_conjecture_two
    {n : ℕ} (hn : n ≤ 2)
    (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    consistencyObstructionConjecture F := by
  intro T _hT
  exact consistent_two T hn

/--
Section 4 conjecture in the strengthened base range: when `n ≤ 3`, every
parameter tuple is consistent.
-/
theorem consistency_conjecture_three
    {n : ℕ} (hn : n ≤ 3)
    (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    consistencyObstructionConjecture F := by
  intro T _hT
  exact consistent_three T hn

/--
Section 4 conjecture for the abelian base-case Hall multiplication family.
-/
theorem consistency_obstruction_conjecture
    {n : ℕ} (hn : n ≤ 2) :
    consistencyObstructionConjecture
      (abelianMultiplicationPolynomial : Fin n → MvPolynomial (MulVar n) ℚ) :=
  consistency_conjecture_two hn abelianMultiplicationPolynomial

/--
For `n ≤ 2`, the abelian Hall-polynomial obstruction equations vanish for all
parameter tuples.
-/
theorem consistency_locus_univ
    {n : ℕ} (hn : n ≤ 2) :
    {T : ParameterIndex n → ℤ |
      consistencyObstructionLocus abelianMultiplicationPolynomial T} =
      Set.univ := by
  ext T
  constructor
  · intro _hT
    trivial
  · intro _hT
    exact consistency_obstruction_locus T hn

/--
In the base cases, the abelian obstruction equations exactly describe the
consistency locus.
-/
theorem consistency_locus_obstruction
    {n : ℕ} (hn : n ≤ 2) :
    consistencyLocus n =
      {T : ParameterIndex n → ℤ |
        consistencyObstructionLocus abelianMultiplicationPolynomial T} := by
  rw [locus_univ_two hn,
    consistency_locus_univ hn]

/--
Section 3 base case as an existence statement: for `n ≤ 2`, the free abelian
presentation is consistent and the coordinatewise Hall-polynomial families
represent multiplication, powering, and conjugation.
-/
theorem represents_polynomials_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    ∃ M : CPres n T,
      RepresentsHallPolynomials M abelianMultiplicationPolynomial
        abelianPoweringPolynomial abelianConjugationPolynomial := by
  rcases consistent_two T hn with ⟨M⟩
  exact ⟨M, M.represents_hall_polynomials hn⟩

/--
Section 3 rank-three existence as a parameter-only statement.  The concrete
rank-three model supplies the presentation, and the rank-three local assembly
supplies represented Hall-polynomial families.
-/
theorem represents_hall_three
    (T : ParameterIndex 3 → ℤ) :
    ∃ M : CPres 3 T,
      ∃ (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
        (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ)
        (R : ParameterIndex 3 → MvPolynomial (ConjVar 3) ℚ),
          RepresentsHallPolynomials M F K R := by
  let M := rankConsistentPresentation T
  rcases M.polynomials_three with ⟨F, K, R, hHall⟩
  exact ⟨M, F, K, R, hHall⟩

/--
Section 3 base range with rank three included: every parameter tuple of length
at most three has a consistent presentation and represented Hall polynomials.
-/
theorem represents_polynomials_three
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 3) :
    ∃ M : CPres n T,
      ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
        (K : Fin n → MvPolynomial (PowerVar n) ℚ)
        (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
          RepresentsHallPolynomials M F K R := by
  rcases consistent_three T hn with ⟨M⟩
  rcases M.hall_polynomials_three hn with ⟨F, K, R, hHall⟩
  exact ⟨M, F, K, R, hHall⟩

/--
Section 6 base case as an existence statement: for `n ≤ 2`, the abelian
presentation exists and its coordinatewise Hall polynomials provide uniform
multiplication and powering methods, before and after parameter specialization.
-/
theorem operation_methods_two
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 2) :
    ∃ M : CPres n T,
      MulEvaluationMethod M abelianMultiplicationPolynomial ∧
      SpecializedMulMethod M abelianMultiplicationPolynomial ∧
      PowerEvaluationMethod M abelianPoweringPolynomial ∧
      SpecializedEvaluationMethod M abelianPoweringPolynomial := by
  rcases consistent_two T hn with ⟨M⟩
  exact ⟨M, M.operation_two hn⟩

/--
Section 6 operation methods in exact rank three, with the concrete rank-three
presentation constructed from the parameter tuple.
-/
theorem operation_parameter_three
    (T : ParameterIndex 3 → ℤ) :
    ∃ M : CPres 3 T,
      ∃ (F : Fin 3 → MvPolynomial (MulVar 3) ℚ)
        (K : Fin 3 → MvPolynomial (PowerVar 3) ℚ),
          MulEvaluationMethod M F ∧
          SpecializedMulMethod M F ∧
          PowerEvaluationMethod M K ∧
          SpecializedEvaluationMethod M K := by
  let M := rankConsistentPresentation T
  rcases M.operation_three with ⟨F, K, hMethods⟩
  exact ⟨M, F, K, hMethods⟩

/--
Section 6 operation methods for all parameter tuples of length at most three.
-/
theorem operation_methods_parameter
    {n : ℕ} (T : ParameterIndex n → ℤ) (hn : n ≤ 3) :
    ∃ M : CPres n T,
      ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
        (K : Fin n → MvPolynomial (PowerVar n) ℚ),
          MulEvaluationMethod M F ∧
          SpecializedMulMethod M F ∧
          PowerEvaluationMethod M K ∧
          SpecializedEvaluationMethod M K := by
  rcases consistent_three T hn with ⟨M⟩
  rcases M.operation_methods hn with ⟨F, K, hMethods⟩
  exact ⟨M, F, K, hMethods⟩

/--
Global Hall-polynomial induction with the abelian base cases built in.
Since every consistent presentation of length at most two is abelian, the
remaining represented ambient conjugation input is needed only from rank
three onward.
-/
theorem polynomials_three_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 3) → ℤ}
        (N : CPres (m + 3) U),
          ∃ R : ParameterIndex (m + 3) → MvPolynomial (ConjVar (m + 3)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R := by
  revert T
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro T M
      by_cases hsmall : n ≤ 2
      · exact hall_polynomials_two M hsmall
      · cases n with
        | zero => omega
        | succ n =>
            cases n with
            | zero => omega
            | succ n =>
                cases n with
                | zero => omega
                | succ n =>
                    rcases hConj (m := n) M with ⟨R, hR⟩
                    have hHallU :
                        ∃ (F_U : Fin (n + 2) → MvPolynomial (MulVar (n + 2)) ℚ)
                          (K_U : Fin (n + 2) → MvPolynomial (PowerVar (n + 2)) ℚ)
                          (R_U :
                            ParameterIndex (n + 2) →
                              MvPolynomial (ConjVar (n + 2)) ℚ),
                            RepresentsHallPolynomials
                              M.deleteFirstConsistent F_U K_U R_U :=
                      ih (n + 2) (by omega)
                        M.deleteFirstConsistent
                    have hHallW :
                        ∃ (F_W : Fin (n + 2) → MvPolynomial (MulVar (n + 2)) ℚ)
                          (K_W : Fin (n + 2) → MvPolynomial (PowerVar (n + 2)) ℚ)
                          (R_W :
                            ParameterIndex (n + 2) →
                              MvPolynomial (ConjVar (n + 2)) ℚ),
                            RepresentsHallPolynomials
                              M.deleteConsistentPresentation F_W K_W R_W :=
                      ih (n + 2) (by omega)
                        M.deleteConsistentPresentation
                    exact
                      uw_solution_delete
                        M R hHallU hHallW hR

/--
Section 6 operation-method consequence of the rank-three conjugation
reduction.
-/
theorem operation_methods_three
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 3) → ℤ}
        (N : CPres (m + 3) U),
          ∃ R : ParameterIndex (m + 3) → MvPolynomial (ConjVar (m + 3)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  operation_methods_polynomials M
    (polynomials_three_conjugation hConj M)

/--
Section 4 obstruction package with abelian base cases built into the global
Hall-polynomial induction.  The represented conjugation input is needed only
from rank three onward.
-/
theorem obstruction_package_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 3) → ℤ}
        (N : CPres (m + 3) U),
          ∃ R : ParameterIndex (m + 3) → MvPolynomial (ConjVar (m + 3)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p := by
  rcases polynomials_three_conjugation hConj M with
    ⟨F, K, R, hHall⟩
  refine
    ⟨F, K, R, hHall, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact consistency_locus_polynomials
      M F K R hHall
  · exact
      consistency_vanishing_polynomials
        M F K R hHall
  · intro p r h
    exact
      remainder_obstruction_polynomials
        M F K R hHall h
  · intro p r h
    exact
      specialize_remainder_consistency
        M F K R hHall h
  · intro p r h x y
    exact
      remainder_coeff_polynomials
        M F K R hHall h x y
  · intro p r h
    exact
      specialize_remainder_polynomials
        M F K R hHall h
  · intro p r h x z
    exact
      remainder_consistency_polynomials
        M F K R hHall h x z

/--
Global Hall-polynomial induction with all ranks up to three discharged.
The only remaining represented ambient conjugation input is needed from rank
four onward.
-/
theorem polynomials_four_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 4) → ℤ}
        (N : CPres (m + 4) U),
          ∃ R : ParameterIndex (m + 4) → MvPolynomial (ConjVar (m + 4)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R :=
  polynomials_three_conjugation
    (fun {m} {_U} N => by
      cases m with
      | zero =>
          exact represents_conjugation_three N
      | succ m =>
          exact hConj (m := m) N)
    M

/--
Section 6 operation-method consequence of the rank-four conjugation
reduction.
-/
theorem operation_methods_four
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 4) → ℤ}
        (N : CPres (m + 4) U),
          ∃ R : ParameterIndex (m + 4) → MvPolynomial (ConjVar (m + 4)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  operation_methods_polynomials M
    (polynomials_four_conjugation hConj M)

/--
Section 4 obstruction package with all ranks up to three discharged from the
global Hall-polynomial induction.  The represented conjugation input is
needed only from rank four onward.
-/
theorem package_four_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 4) → ℤ}
        (N : CPres (m + 4) U),
          ∃ R : ParameterIndex (m + 4) → MvPolynomial (ConjVar (m + 4)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  obstruction_package_conjugation
    (fun {m} {_U} N => by
      cases m with
      | zero =>
          exact represents_conjugation_three N
      | succ m =>
          exact hConj (m := m) N)
    M

/--
Global Hall-polynomial induction with all ranks up to four discharged.  The
only remaining represented ambient conjugation input is needed from rank five
onward.
-/
theorem polynomials_five_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 5) → ℤ}
        (N : CPres (m + 5) U),
          ∃ R : ParameterIndex (m + 5) → MvPolynomial (ConjVar (m + 5)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R :=
  polynomials_four_conjugation
    (fun {m} {_U} N => by
      cases m with
      | zero =>
          exact conjugation_four N
      | succ m =>
          exact hConj (m := m) N)
    M

/--
Section 6 operation-method consequence of the rank-five conjugation
reduction.
-/
theorem operation_methods_five
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 5) → ℤ}
        (N : CPres (m + 5) U),
          ∃ R : ParameterIndex (m + 5) → MvPolynomial (ConjVar (m + 5)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ),
        MulEvaluationMethod M F ∧
        SpecializedMulMethod M F ∧
        PowerEvaluationMethod M K ∧
        SpecializedEvaluationMethod M K :=
  operation_methods_polynomials M
    (polynomials_five_conjugation hConj M)

/--
Section 4 obstruction package with all ranks up to four discharged from the
global Hall-polynomial induction.  The represented conjugation input is
needed only from rank five onward.
-/
theorem package_five_conjugation
    (hConj :
      ∀ {m : ℕ} {U : ParameterIndex (m + 5) → ℤ}
        (N : CPres (m + 5) U),
          ∃ R : ParameterIndex (m + 5) → MvPolynomial (ConjVar (m + 5)) ℚ,
            RepresentsConjugation N R)
    {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) :
    ∃ (F : Fin n → MvPolynomial (MulVar n) ℚ)
      (K : Fin n → MvPolynomial (PowerVar n) ℚ)
      (R : ParameterIndex n → MvPolynomial (ConjVar n) ℚ),
        RepresentsHallPolynomials M F K R ∧
        consistencyObstructionLocus F T ∧
        consistencyObstructionIdeal F ≤ vanishingIdealAt T ∧
        (∀ {p r : MvPolynomial (ParameterIndex n) ℚ},
          p - r ∈ consistencyObstructionIdeal F →
            parameterEvaluation T r = parameterEvaluation T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            specializeMul T r = specializeMul T p) ∧
        (∀ {p r : MvPolynomial (MulVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (mulInputPolynomial p) (mulInputPolynomial r) →
            ∀ x y, evalMulPolynomial T x y r = evalMulPolynomial T x y p) ∧
        (∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
            specializePower T r = specializePower T p) ∧
        ∀ {p r : MvPolynomial (PowerVar n) ℚ},
          coefficientwiseSubMem (consistencyObstructionIdeal F)
            (powerInputPolynomial p) (powerInputPolynomial r) →
          ∀ x z, evalPowerPolynomial T x z r =
            evalPowerPolynomial T x z p :=
  package_four_conjugation
    (fun {m} {_U} N => by
      cases m with
      | zero =>
          exact conjugation_four N
      | succ m =>
          exact hConj (m := m) N)
    M

end CPres

end

end CantEick
end Submission
