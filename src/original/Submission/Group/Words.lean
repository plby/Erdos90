import Submission.Topology.LightweightTopology
import Mathlib.Tactic

namespace Submission
namespace Group

universe u v w
noncomputable local instance propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A free generating set is just the indexing type for a free group. -/
abbrev freeGeneratingSet (α : Type u) := α

/-- A signed generator: `true` means the generator, `false` its inverse. -/
abbrev sGen (α : Type u) := α × Bool

/-- Flip the sign of a signed generator. -/
def sGen.inv {α : Type u} (a : sGen α) : sGen α :=
  (a.1, !a.2)

@[simp] theorem sGen.inv_fst {α : Type u} (a : sGen α) :
    (sGen.inv a).1 = a.1 := rfl

@[simp] theorem sGen.inv_snd {α : Type u} (a : sGen α) :
    (sGen.inv a).2 = !a.2 := rfl

/-- Flipping the sign twice gives back the signed generator. -/
@[simp] theorem sGen.inv_inv {α : Type u} (a : sGen α) :
    sGen.inv (sGen.inv a) = a := by
  cases a with
  | mk x b => cases b <;> rfl

/-- Signed inversion is injective. -/
theorem sGen.inv_injective {α : Type u} :
    Function.Injective (@sGen.inv α) := by
  intro a b h
  calc
    a = sGen.inv (sGen.inv a) := by simp
    _ = sGen.inv (sGen.inv b) := by rw [h]
    _ = b := by simp

/-- A raw word in the free group, before quotienting by cancellation. -/
abbrev wFGroup (α : Type u) := List (sGen α)

/-- Evaluate a raw signed word in the actual free group. -/
def wFGroup.eval {α : Type u} : wFGroup α → FreeGroup α
  | [] => 1
  | (a, true) :: xs => FreeGroup.of a * wFGroup.eval xs
  | (a, false) :: xs => (FreeGroup.of a)⁻¹ * wFGroup.eval xs

/-- No adjacent inverse pair occurs in a raw word. -/
def reducedLetters {α : Type u} : wFGroup α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => y ≠ sGen.inv x ∧ reducedLetters (y :: xs)

@[simp] theorem reducedLetters_nil {α : Type u} :
    reducedLetters ([] : wFGroup α) := trivial

@[simp] theorem reducedLetters_singleton {α : Type u} (a : sGen α) :
    reducedLetters ([a] : wFGroup α) := trivial

@[simp] theorem reduced_letters_cons {α : Type u} (x y : sGen α)
    (xs : wFGroup α) :
    reducedLetters (x :: y :: xs) ↔ y ≠ sGen.inv x ∧ reducedLetters (y :: xs) :=
  Iff.rfl

/-- A reduced word is a raw word equipped with the no-adjacent-cancellation proof. -/
structure rWord (α : Type u) where
  letters : wFGroup α
  reduced : reducedLetters letters
  length : ℕ := letters.length
  length_eq : length = letters.length
  value : FreeGroup α := wFGroup.eval letters
  value_eq_eval : value = wFGroup.eval letters

/-- The stored length of a reduced word is the list length. -/
theorem rWord.length_spec {α : Type u} (w : rWord α) :
    w.length = w.letters.length :=
  w.length_eq

/-- The stored value of a reduced word is evaluation of its letters. -/
theorem rWord.value_spec {α : Type u} (w : rWord α) :
    w.value = wFGroup.eval w.letters :=
  w.value_eq_eval

/-- The letters of a reduced word satisfy the reduction predicate. -/
theorem rWord.reduced_letters {α : Type u} (w : rWord α) :
    reducedLetters w.letters :=
  w.reduced


/-- A normal form is a reduced word equipped with a uniqueness certificate among
reduced representatives of the same free-group element.  This separates mere
reduction from canonicity. -/
structure normalForm (α : Type u) where
  word : rWord α
  unique : ∀ w : rWord α, w.value = word.value → w.letters = word.letters

/-- The underlying reduced word of a normal form is reduced. -/
theorem normalForm.reduced {α : Type u} (n : normalForm α) :
    reducedLetters n.word.letters := n.word.reduced



@[simp] theorem wFGroup.eval_nil {α : Type u} :
    wFGroup.eval ([] : wFGroup α) = 1 := rfl

@[simp] theorem wFGroup.eval_cons_true {α : Type u} (a : α)
    (xs : wFGroup α) :
    wFGroup.eval ((a, true) :: xs) = FreeGroup.of a * wFGroup.eval xs := rfl

@[simp] theorem wFGroup.eval_cons_false {α : Type u} (a : α)
    (xs : wFGroup α) :
    wFGroup.eval ((a, false) :: xs) = (FreeGroup.of a)⁻¹ * wFGroup.eval xs := rfl

@[simp] theorem wFGroup.eval_singleton_true {α : Type u} (a : α) :
    wFGroup.eval ([(a, true)] : wFGroup α) = FreeGroup.of a := by
  simp [wFGroup.eval]

@[simp] theorem wFGroup.eval_singleton_false {α : Type u} (a : α) :
    wFGroup.eval ([(a, false)] : wFGroup α) = (FreeGroup.of a)⁻¹ := by
  simp [wFGroup.eval]

/-- Evaluation of concatenated raw words is multiplicative. -/
theorem wFGroup.eval_append {α : Type u} (xs ys : wFGroup α) :
    wFGroup.eval (xs ++ ys) = wFGroup.eval xs * wFGroup.eval ys := by
  induction xs with
  | nil => simp [wFGroup.eval]
  | cons x xs ih =>
      rcases x with ⟨a, b⟩
      cases b <;> simp [wFGroup.eval, ih, mul_assoc]

/-- The empty reduced word. -/
def rWord.nil (α : Type u) : rWord α where
  letters := []
  reduced := trivial
  length := 0
  length_eq := rfl
  value := 1
  value_eq_eval := rfl

@[simp] theorem rWord.nil_letters (α : Type u) :
    (rWord.nil α).letters = [] := rfl

@[simp] theorem rWord.nil_length (α : Type u) :
    (rWord.nil α).length = 0 := rfl

@[simp] theorem rWord.nil_value (α : Type u) :
    (rWord.nil α).value = (1 : FreeGroup α) := rfl

/-- A one-letter reduced word. -/
def rWord.singleton {α : Type u} (a : sGen α) : rWord α where
  letters := [a]
  reduced := trivial
  length := 1
  length_eq := rfl
  value := wFGroup.eval [a]
  value_eq_eval := rfl

@[simp] theorem rWord.singleton_letters {α : Type u} (a : sGen α) :
    (rWord.singleton a).letters = [a] := rfl

@[simp] theorem rWord.singleton_length {α : Type u} (a : sGen α) :
    (rWord.singleton a).length = 1 := rfl

@[simp] theorem rWord.singleton_value_true {α : Type u} (a : α) :
    (rWord.singleton (a, true)).value = FreeGroup.of a := by
  simp [rWord.singleton]

@[simp] theorem rWord.singleton_value_false {α : Type u} (a : α) :
    (rWord.singleton (a, false)).value = (FreeGroup.of a)⁻¹ := by
  simp [rWord.singleton]

/-- Kronecker delta coefficient used in the raw Fox derivative. -/
noncomputable def foxDelta (R : Type u) (α : Type v) [Ring R] [DecidableEq α]
    (a x : α) : MonoidAlgebra R (FreeGroup α) :=
  if x = a then MonoidAlgebra.single 1 1 else 0

@[simp] theorem foxDelta_same (R : Type u) (α : Type v) [Ring R] [DecidableEq α]
    (a : α) : foxDelta R α a a = MonoidAlgebra.single 1 1 := by
  simp [foxDelta]

@[simp] theorem fox_delta_ne (R : Type u) (α : Type v) [Ring R] [DecidableEq α]
    {a x : α} (h : x ≠ a) : foxDelta R α a x = 0 := by
  simp [foxDelta, h]


/-- Fox derivative of a raw signed word.  This is the recursive formula before
proving invariance under free reduction. -/
noncomputable def foxDerivativeRaw (R : Type u) {α : Type v} [Ring R] [DecidableEq α]
    (a : α) : wFGroup α → MonoidAlgebra R (FreeGroup α)
  | [] => 0
  | (x, true) :: xs =>
      foxDelta R α a x +
        MonoidAlgebra.single (FreeGroup.of x) (1 : R) * foxDerivativeRaw R a xs
  | (x, false) :: xs =>
      -MonoidAlgebra.single ((FreeGroup.of x)⁻¹) (1 : R) * foxDelta R α a x +
        MonoidAlgebra.single ((FreeGroup.of x)⁻¹) (1 : R) * foxDerivativeRaw R a xs


@[simp] theorem fox_derivative_nil (R : Type u) {α : Type v} [Ring R]
    [DecidableEq α] (a : α) :
    foxDerivativeRaw R a ([] : wFGroup α) = 0 := rfl

@[simp] theorem derivative_cons_pos (R : Type u) {α : Type v} [Ring R]
    [DecidableEq α] (a x : α) (xs : wFGroup α) :
    foxDerivativeRaw R a ((x, true) :: xs) =
      foxDelta R α a x + MonoidAlgebra.single (FreeGroup.of x) (1 : R) *
        foxDerivativeRaw R a xs := rfl

@[simp] theorem derivative_cons_neg (R : Type u) {α : Type v} [Ring R]
    [DecidableEq α] (a x : α) (xs : wFGroup α) :
    foxDerivativeRaw R a ((x, false) :: xs) =
      -MonoidAlgebra.single ((FreeGroup.of x)⁻¹) (1 : R) * foxDelta R α a x +
        MonoidAlgebra.single ((FreeGroup.of x)⁻¹) (1 : R) * foxDerivativeRaw R a xs := rfl

/-- A set of relators in a free group. -/
abbrev relatorSet (α : Type u) := Set (FreeGroup α)

/-- The normal closure of a relator set. -/
def normalClosureRelators {α : Type u} (R : relatorSet α) : Subgroup (FreeGroup α) :=
  Subgroup.normalClosure R

/-- The normal subgroup generated by relators, packaged with normality. -/
def normalGeneratedRelators {α : Type u} (R : relatorSet α) :
    nSubgro (FreeGroup α) where
  carrier := normalClosureRelators R
  normal' := Subgroup.normalClosure_normal

/-- Each listed relator lies in its normal closure. -/
theorem relator_normal_closure {α : Type u} {R : relatorSet α} {r : FreeGroup α}
    (hr : r ∈ R) : r ∈ normalClosureRelators R :=
  Subgroup.subset_normalClosure hr

/-- Normal closure is the least normal subgroup containing the relators. -/
theorem normal_closure_relators {α : Type u} {R : relatorSet α} (N : Subgroup (FreeGroup α))
    [N.Normal] (h : R ⊆ N) : normalClosureRelators R ≤ N := by
  apply Subgroup.normalClosure_le_normal
  exact h

/-- The packaged normal subgroup generated by relators contains the relators. -/
theorem relator_normal_generated {α : Type u} {R : relatorSet α}
    {r : FreeGroup α} (hr : r ∈ R) :
    r ∈ (normalGeneratedRelators R).carrier :=
  relator_normal_closure hr

/-- Presentations reuse the project-level presentation structure. -/
abbrev presentations := Submission.Presentation

/-- A lightweight relation module: a module with a distinguished set of relation vectors. -/
structure rModule (R : Type u) [Semiring R] where
  M : Type v
  [addCommMonoid : AddCommGroup M]
  [module' : Module R M]
  relations : Submodule R M
  relation_generators : Set M
  generators_span : Submodule.span R relation_generators = relations
  generators_mem : relation_generators ⊆ relations

attribute [instance] rModule.addCommMonoid rModule.module'


/-- Build a relation module from a submodule and a chosen spanning set. -/
def rModule.ofSpan (R : Type u) [Semiring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M) (N : Submodule R M)
    (hspan : Submodule.span R S = N) : rModule R where
  M := M
  relations := N
  relation_generators := S
  generators_span := hspan
  generators_mem := by
    intro x hx
    rw [← hspan]
    exact Submodule.subset_span hx

/-- Relation generators lie in the relation submodule. -/
theorem rModule.generator_mem {R : Type u} [Semiring R]
    (M : rModule R) {x : M.M} (hx : x ∈ M.relation_generators) :
    x ∈ M.relations := M.generators_mem hx

/-- The quotient map associated to a presentation. -/
abbrev presentationQuotientMap (P : presentations.{u}) : P.Free →* P.Group := P.quotientMap

/-- The kernel of the presentation quotient map. -/
abbrev presentationKernel (P : presentations.{u}) : Subgroup P.Free := MonoidHom.ker P.quotientMap

/-- A Fox derivative with respect to one generator, with the defining crossed-
derivation laws recorded as data.  This is deliberately a structure rather than
just a function: later proofs can instantiate it by recursion on `FreeGroup`,
while downstream definitions can already use the product and generator laws. -/
structure fDRespec (R : Type u) (α : Type v) [Ring R]
    [DecidableEq α] where
  generator : α
  deriv : FreeGroup α → MonoidAlgebra R (FreeGroup α)
  map_one : deriv 1 = 0
  map_mul : ∀ x y, deriv (x * y) = deriv x +
    MonoidAlgebra.single x (1 : R) * deriv y
  map_of : ∀ a, deriv (FreeGroup.of a) =
    (if a = generator then MonoidAlgebra.single 1 (1 : R) else 0)
  map_inv : ∀ x, deriv x⁻¹ =
    -MonoidAlgebra.single x⁻¹ (1 : R) * deriv x

@[simp] theorem fDRespec.map_one_apply {R : Type u} {α : Type v}
    [Ring R] [DecidableEq α] (D : fDRespec R α) : D.deriv 1 = 0 :=
  D.map_one

/-- Product rule for a packaged Fox derivative. -/
theorem fDRespec.map_mul_apply {R : Type u} {α : Type v}
    [Ring R] [DecidableEq α] (D : fDRespec R α) (x y : FreeGroup α) :
    D.deriv (x * y) = D.deriv x + MonoidAlgebra.single x (1 : R) * D.deriv y :=
  D.map_mul x y

/-- Value of a packaged Fox derivative on a free generator. -/
theorem fDRespec.map_of_apply {R : Type u} {α : Type v}
    [Ring R] [DecidableEq α] (D : fDRespec R α) (a : α) :
    D.deriv (FreeGroup.of a) =
      (if a = D.generator then MonoidAlgebra.single 1 (1 : R) else 0) :=
  D.map_of a


instance fDRespec.instFun (R : Type u) (α : Type v) [Ring R]
    [DecidableEq α] : CoeFun (fDRespec R α)
      (fun _ => FreeGroup α → MonoidAlgebra R (FreeGroup α)) :=
  ⟨fDRespec.deriv⟩

/-- A Fox Jacobian: a relator set together with one Fox derivative for each
generator and the resulting matrix entries.  The `entry_eq` field pins the
matrix to evaluation of the derivatives on relators. -/
structure fJacobi (R : Type u) (α : Type v) [Ring R] [DecidableEq α] where
  rels : relatorSet α
  derivative : α → fDRespec R α
  derivative_generator : ∀ a, (derivative a).generator = a
  entry : rels → α → MonoidAlgebra R (FreeGroup α)
  entry_eq : ∀ r a, entry r a = derivative a r.1

/-- A Fox Jacobian entry is evaluation of the corresponding derivative. -/
theorem fJacobi.entry_apply {R : Type u} {α : Type v} [Ring R] [DecidableEq α]
    (J : fJacobi R α) (r : J.rels) (a : α) :
    J.entry r a = J.derivative a r.1 :=
  J.entry_eq r a

/-- The derivative indexed by a generator records that generator. -/
theorem fJacobi.derivative_generator_apply {R : Type u} {α : Type v}
    [Ring R] [DecidableEq α] (J : fJacobi R α) (a : α) :
    (J.derivative a).generator = a :=
  J.derivative_generator a


/-- The `n`th term of a Zassenhaus/descending filtration. -/
abbrev zassenhausTermDn {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ) : Subgroup G :=
  F n

/-- Having depth at least `n` means lying in the `n`th filtration term. -/
def lowerBoundDepth {G : Type u} [Group G] (F : DFilt G) (x : G) (n : ℕ) : Prop :=
  x ∈ F n

/-- The set of filtration degrees containing an element. -/
def zassenhausDepthElement {G : Type u} [Group G] (F : DFilt G) (x : G) : Set ℕ :=
  {n | x ∈ F n}

/-- Relators equipped with Zassenhaus depth lower bounds after evaluation in a
filtered target group. -/
structure rADepths (α : Type u) (G : Type v) [Group G] where
  rels : relatorSet α
  eval : FreeGroup α →* G
  filtration : DFilt G
  depth : rels → ℕ
  depth_sound : ∀ r : rels, eval r.1 ∈ filtration (depth r)

/-- A relator has the recorded lower-bound depth after evaluation. -/
theorem rADepths.depth_mem {α : Type u} {G : Type v}
    [Group G] (D : rADepths α G) (r : D.rels) :
    D.eval r.1 ∈ D.filtration (D.depth r) :=
  D.depth_sound r


/-- A depth function on a relator set. -/
abbrev relatorDepths {α : Type u} (R : relatorSet α) := R → ℕ

/-- Exact depth `n`: in term `n`, but not in term `n+1`. -/
def exactDepth {G : Type u} [Group G] (F : DFilt G) (x : G) (n : ℕ) : Prop :=
  x ∈ F n ∧ x ∉ F (n+1)


end Group
end Submission

/-!
## Statements migrated from `Submission.Theorems`

These declarations keep their historical `Submission.Theorems` namespace while living
next to the API they describe.
-/

namespace Submission
namespace Theorems

open Submission.Group
open Submission.Algebra
open Submission.Topology

universe u v w x

/-- A chosen Fox-derivative family satisfies the fundamental formula for every word. -/
def DerivativeFundamentalFormula {R : Type u} {α : Type v}
    [Ring R] [Fintype α] [DecidableEq α]
    (D : α → fDRespec R α) : Prop :=
  ∀ w : FreeGroup α,
    MonoidAlgebra.single w (1 : R) - 1 =
      Finset.sum Finset.univ (fun a : α =>
        D a w * (MonoidAlgebra.single (FreeGroup.of a) (1 : R) - 1))
/-- Reordering is symmetric. -/
theorem swaps {α : Type u} {xs ys : List α} :
    reordering xs ys → reordering ys xs
  := by
  exact List.Perm.symm
/-- The free group has its usual universal mapping property. -/
theorem universalPropertyGroups {α : Type u} {G : Type v} [Group G] (f : α → G) :
    ∃! φ : FreeGroup α →* G, ∀ a, φ (FreeGroup.of a) = f a
  := by
  refine ⟨FreeGroup.lift f, ?_, ?_⟩
  · intro a
    exact FreeGroup.lift_apply_of
  · intro φ hφ
    ext a
    exact (hφ a).trans FreeGroup.lift_apply_of.symm
/-- Relators vanish in the quotient they present. -/
theorem presentationRealizesRelators (P : presentations.{u}) (r : P.rels) :
    P.quotientMap r.1 = 1
  := by
  exact P.quotient_rel_one r.2

/-- The semidirect product used to encode Fox derivatives. -/
structure FoxPair (R : Type u) (G : Type v) [Ring R] [Group G] where
  deriv : MonoidAlgebra R G
  elt : G

namespace FoxPair

variable {R : Type u} {G : Type v} [Ring R] [Group G]

private lemma single_mul_one (g h : G) :
    MonoidAlgebra.single g (1 : R) * MonoidAlgebra.single h (1 : R) =
      MonoidAlgebra.single (g * h) (1 : R) := by
  rw [MonoidAlgebra.single_mul_single]
  simp

private lemma single_action_assoc (g h : G) (m : MonoidAlgebra R G) :
    MonoidAlgebra.single g (1 : R) *
        (MonoidAlgebra.single h (1 : R) * m) =
      MonoidAlgebra.single (g * h) (1 : R) * m := by
  rw [← mul_assoc, single_mul_one]

private lemma single_one_mul (m : MonoidAlgebra R G) :
    MonoidAlgebra.single (1 : G) (1 : R) * m = m := by
  rw [← MonoidAlgebra.one_def, one_mul]

@[ext] theorem ext {p q : FoxPair R G} (hderiv : p.deriv = q.deriv)
    (helt : p.elt = q.elt) : p = q := by
  cases p
  cases q
  simp_all

noncomputable def one : FoxPair R G where
  deriv := 0
  elt := 1

noncomputable def mul (p q : FoxPair R G) : FoxPair R G where
  deriv := p.deriv + MonoidAlgebra.single p.elt (1 : R) * q.deriv
  elt := p.elt * q.elt

noncomputable def inv (p : FoxPair R G) : FoxPair R G where
  deriv := -(MonoidAlgebra.single (p.elt⁻¹) (1 : R) * p.deriv)
  elt := p.elt⁻¹

noncomputable instance instGroup : Group (FoxPair R G) where
  one := FoxPair.one
  mul := FoxPair.mul
  inv := FoxPair.inv
  mul_assoc := by
    intro p q r
    apply FoxPair.ext
    · change (FoxPair.mul (FoxPair.mul p q) r).deriv =
        (FoxPair.mul p (FoxPair.mul q r)).deriv
      dsimp [FoxPair.mul]
      rw [mul_add]
      rw [single_action_assoc]
      rw [add_assoc]
    · change (FoxPair.mul (FoxPair.mul p q) r).elt =
        (FoxPair.mul p (FoxPair.mul q r)).elt
      dsimp [FoxPair.mul]
      rw [mul_assoc]
  one_mul := by
    intro p
    apply FoxPair.ext
    · change (FoxPair.mul FoxPair.one p).deriv = p.deriv
      dsimp [FoxPair.one, FoxPair.mul]
      rw [zero_add, single_one_mul]
    · change (FoxPair.mul FoxPair.one p).elt = p.elt
      dsimp [FoxPair.one, FoxPair.mul]
      rw [one_mul]
  mul_one := by
    intro p
    apply FoxPair.ext
    · change (FoxPair.mul p FoxPair.one).deriv = p.deriv
      dsimp [FoxPair.one, FoxPair.mul]
      simp
    · change (FoxPair.mul p FoxPair.one).elt = p.elt
      dsimp [FoxPair.one, FoxPair.mul]
      simp
  inv_mul_cancel := by
    intro p
    apply FoxPair.ext
    · change (FoxPair.mul (FoxPair.inv p) p).deriv = FoxPair.one.deriv
      dsimp [FoxPair.inv, FoxPair.one, FoxPair.mul]
      simp
    · change (FoxPair.mul (FoxPair.inv p) p).elt = FoxPair.one.elt
      dsimp [FoxPair.inv, FoxPair.one, FoxPair.mul]
      simp

@[simp] theorem deriv_one :
    (1 : FoxPair R G).deriv = 0 :=
  rfl

@[simp] theorem elt_one :
    (1 : FoxPair R G).elt = 1 :=
  rfl

@[simp] theorem deriv_mul (p q : FoxPair R G) :
    (p * q).deriv =
      p.deriv + MonoidAlgebra.single p.elt (1 : R) * q.deriv :=
  rfl

@[simp] theorem elt_mul (p q : FoxPair R G) :
    (p * q).elt = p.elt * q.elt :=
  rfl

noncomputable def eltHom : FoxPair R G →* G where
  toFun := fun p => p.elt
  map_one' := by simp
  map_mul' := by intro p q; simp

@[simp] theorem eltHom_apply (p : FoxPair R G) :
    (eltHom (R := R) (G := G)) p = p.elt :=
  rfl

noncomputable def basis (g : G) : MonoidAlgebra R G :=
  MonoidAlgebra.of R G g

@[simp] theorem basis_one : basis (R := R) (1 : G) = 1 := by
  rfl

@[simp] theorem basis_mul (g h : G) :
    basis (R := R) (g * h) = basis (R := R) g * basis (R := R) h := by
  simp [basis]

end FoxPair

private lemma free_group_ne {α : Type v} {a b : α} (hba : b ≠ a) :
    FreeGroup.of b ≠ FreeGroup.of a := by
  classical
  intro h
  let f : α → Multiplicative ℤ := fun x =>
    if x = b then Multiplicative.ofAdd (1 : ℤ) else Multiplicative.ofAdd (0 : ℤ)
  have hab : a ≠ b := by
    intro h'
    exact hba h'.symm
  have h' := congrArg (fun y : FreeGroup α => (FreeGroup.lift f) y) h
  have hmap :
      Multiplicative.ofAdd (1 : ℤ) = Multiplicative.ofAdd (0 : ℤ) := by
    simp [f, hab] at h'
  have hint : (1 : ℤ) = 0 := by
    simpa using congrArg (fun z : Multiplicative ℤ => Multiplicative.toAdd z) hmap
  have h10 : (1 : ℤ) ≠ 0 := by norm_num
  exact h10 hint

private lemma free_ne_inv {α : Type v} (a b : α) :
    FreeGroup.of b ≠ (FreeGroup.of a)⁻¹ := by
  classical
  intro h
  let f : α → Multiplicative ℤ := fun _ => Multiplicative.ofAdd (1 : ℤ)
  have h' := congrArg (fun y : FreeGroup α => (FreeGroup.lift f) y) h
  have hmap :
      Multiplicative.ofAdd (1 : ℤ) =
        (Multiplicative.ofAdd (1 : ℤ))⁻¹ := by
    simpa [f] using h'
  have hint : (1 : ℤ) = -1 := by
    simpa using congrArg (fun z : Multiplicative ℤ => Multiplicative.toAdd z) hmap
  have h1m1 : (1 : ℤ) ≠ -1 := by norm_num
  exact h1m1 hint

private noncomputable def twoPointD (R : Type u) {G : Type v} [Ring R] [Group G]
    (g : G) : G → MonoidAlgebra R G := by
  classical
  exact fun u =>
    if u = g then (1 : MonoidAlgebra R G)
    else if u = g⁻¹ then -MonoidAlgebra.single (g⁻¹) (1 : R)
    else 0

private lemma neg_single_inv {R : Type u} {G : Type v}
    [Ring R] [Group G] (g : G) :
    (-MonoidAlgebra.single g (1 : R)) *
        (-MonoidAlgebra.single (g⁻¹) (1 : R)) =
      (1 : MonoidAlgebra R G) := by
  classical
  calc
    (-MonoidAlgebra.single g (1 : R)) *
        (-MonoidAlgebra.single (g⁻¹) (1 : R))
        = MonoidAlgebra.single g (1 : R) *
            MonoidAlgebra.single (g⁻¹) (1 : R) := by
          simp
    _ = MonoidAlgebra.single (g * g⁻¹) ((1 : R) * (1 : R)) := by
          rw [MonoidAlgebra.single_mul_single]
    _ = (1 : MonoidAlgebra R G) := by
          simp [MonoidAlgebra.one_def]

private lemma point_d_rule {R : Type u} {G : Type v} [Ring R] [Group G]
    (g : G) (hg : g ≠ g⁻¹) :
    ∀ u : G,
      twoPointD R g (u⁻¹) =
        -MonoidAlgebra.single (u⁻¹) (1 : R) * twoPointD R g u := by
  classical
  intro u
  by_cases hu : u = g
  · subst u
    have hginv : g⁻¹ ≠ g := by
      intro h
      exact hg h.symm
    simp [twoPointD, hginv, MonoidAlgebra.one_def]
  · by_cases hui : u = g⁻¹
    · subst u
      have hginv : g⁻¹ ≠ g := by
        intro h
        exact hg h.symm
      simp [twoPointD, hginv, MonoidAlgebra.one_def]
    · have h_inv_ne_g : u⁻¹ ≠ g := by
        intro h'
        exact hui (by simpa using congrArg (fun x : G => x⁻¹) h')
      have h_inv_ne_ginv : u⁻¹ ≠ g⁻¹ := by
        intro h'
        exact hu (by simpa using congrArg (fun x : G => x⁻¹) h')
      simp [twoPointD, hu, hui, h_inv_ne_g, h_inv_ne_ginv]

section FoxFundamental

variable {R : Type u} {α : Type v} [Ring R]
noncomputable local instance : DecidableEq α := Classical.decEq α

noncomputable def foxAux (a : α) : FreeGroup α →* FoxPair R (FreeGroup α) := by
  classical
  exact
    FreeGroup.lift fun b : α =>
      ({ deriv := if b = a then (1 : MonoidAlgebra R (FreeGroup α)) else 0
         elt := FreeGroup.of b } :
        FoxPair R (FreeGroup α))

@[simp] lemma foxAux_elt (a : α) (w : FreeGroup α) :
    (foxAux (R := R) a w).elt = w := by
  let f : FreeGroup α →* FreeGroup α :=
    (FoxPair.eltHom (R := R) (G := FreeGroup α)).comp (foxAux (R := R) a)
  have hf : f = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    intro b
    simp [f, foxAux, FoxPair.eltHom]
  simpa [f, FoxPair.eltHom] using
    (congrArg (fun φ : FreeGroup α →* FreeGroup α => φ w) hf)

noncomputable def foxD (a : α) (w : FreeGroup α) : MonoidAlgebra R (FreeGroup α) :=
  (foxAux (R := R) a w).deriv

@[simp] lemma foxD_one (a : α) :
    foxD (R := R) a (1 : FreeGroup α) = 0 := by
  simp [foxD]

@[simp] lemma foxD_of (a b : α) :
    foxD (R := R) a (FreeGroup.of b) =
      if b = a then (1 : MonoidAlgebra R (FreeGroup α)) else 0 := by
  simp [foxD, foxAux]

@[simp] lemma fox_d_self (a : α) :
    foxD (R := R) a (FreeGroup.of a) = 1 := by
  simp [foxD_of]

lemma fox_d_ne (a b : α) (h : b ≠ a) :
    foxD (R := R) a (FreeGroup.of b) = 0 := by
  simp [foxD_of, h]

lemma foxD_mul (a : α) (x y : FreeGroup α) :
    foxD (R := R) a (x * y) =
      foxD (R := R) a x +
        MonoidAlgebra.single x (1 : R) * foxD (R := R) a y := by
  simp [foxD]

end FoxFundamental

section Fundamental

variable {R : Type u} {α : Type v} [Ring R] [Fintype α]

noncomputable def foxEpsilonHom : FreeGroup α →* FoxPair R (FreeGroup α) where
  toFun w := ⟨FoxPair.basis (R := R) w - 1, w⟩
  map_one' := by
    change
      ({ deriv := FoxPair.basis (R := R) (1 : FreeGroup α) - 1,
         elt := (1 : FreeGroup α) } :
          FoxPair R (FreeGroup α)) = FoxPair.one
    apply FoxPair.ext
    · simp [FoxPair.one]
    · simp [FoxPair.one]
  map_mul' x y := by
    change
      ({ deriv := FoxPair.basis (R := R) (x * y) - 1, elt := x * y } :
          FoxPair R (FreeGroup α)) =
        FoxPair.mul
          ({ deriv := FoxPair.basis (R := R) x - 1, elt := x } : FoxPair R (FreeGroup α))
          ({ deriv := FoxPair.basis (R := R) y - 1, elt := y } : FoxPair R (FreeGroup α))
    apply FoxPair.ext
    · simp only [FoxPair.mul, FoxPair.basis, MonoidAlgebra.of_apply]
      rw [mul_sub, MonoidAlgebra.single_mul_single]
      simp
    · simp [FoxPair.mul]

noncomputable def foxFundamentalSum (w : FreeGroup α) : MonoidAlgebra R (FreeGroup α) :=
  ∑ a : α,
    foxD (R := R) a w *
      (FoxPair.basis (R := R) (FreeGroup.of a) - 1)

@[simp] lemma fox_fundamental_sum :
    foxFundamentalSum (R := R) (1 : FreeGroup α) = 0 := by
  simp [foxFundamentalSum]

lemma fox_fundamental_mul (x y : FreeGroup α) :
    foxFundamentalSum (R := R) (x * y) =
      foxFundamentalSum (R := R) x +
        FoxPair.basis (R := R) x * foxFundamentalSum (R := R) y := by
  classical
  let q : α → MonoidAlgebra R (FreeGroup α) :=
    fun a => FoxPair.basis (R := R) (FreeGroup.of a) - 1
  unfold foxFundamentalSum
  change
    (∑ a : α, foxD (R := R) a (x * y) * q a) =
      (∑ a : α, foxD (R := R) a x * q a) +
        FoxPair.basis (R := R) x *
          (∑ a : α, foxD (R := R) a y * q a)
  calc
    (∑ a : α, foxD (R := R) a (x * y) * q a)
        =
      (∑ a : α,
        (foxD (R := R) a x * q a +
          (FoxPair.basis (R := R) x * foxD (R := R) a y) * q a)) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        simp [foxD_mul, add_mul, FoxPair.basis]
    _ =
      (∑ a : α, foxD (R := R) a x * q a) +
        (∑ a : α,
          (FoxPair.basis (R := R) x * foxD (R := R) a y) * q a) := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ a : α, foxD (R := R) a x * q a) +
        (∑ a : α,
          FoxPair.basis (R := R) x * (foxD (R := R) a y * q a)) := by
        apply congrArg (fun t =>
          (∑ a : α, foxD (R := R) a x * q a) + t)
        refine Finset.sum_congr rfl ?_
        intro a _ha
        rw [mul_assoc]
    _ =
      (∑ a : α, foxD (R := R) a x * q a) +
        FoxPair.basis (R := R) x *
          (∑ a : α, foxD (R := R) a y * q a) := by
        rw [← Finset.mul_sum]

@[simp] lemma fox_fundamental (b : α) :
    foxFundamentalSum (R := R) (FreeGroup.of b) =
      FoxPair.basis (R := R) (FreeGroup.of b) - 1 := by
  classical
  unfold foxFundamentalSum
  calc
    (∑ a : α,
      foxD (R := R) a (FreeGroup.of b) *
        (FoxPair.basis (R := R) (FreeGroup.of a) - 1))
        =
      foxD (R := R) b (FreeGroup.of b) *
        (FoxPair.basis (R := R) (FreeGroup.of b) - 1) := by
        refine Finset.sum_eq_single b ?_ ?_
        · intro a _ha hne
          have hba : b ≠ a := by
            intro hb
            exact hne hb.symm
          simp [foxD_of, hba]
        · intro hb
          simp at hb
    _ = FoxPair.basis (R := R) (FreeGroup.of b) - 1 := by
      simp [foxD_of]

noncomputable def foxFundamentalHom : FreeGroup α →* FoxPair R (FreeGroup α) where
  toFun w := ⟨foxFundamentalSum (R := R) w, w⟩
  map_one' := by
    change
      ({ deriv := foxFundamentalSum (R := R) (1 : FreeGroup α),
         elt := (1 : FreeGroup α) } :
          FoxPair R (FreeGroup α)) = FoxPair.one
    apply FoxPair.ext
    · simp [FoxPair.one]
    · simp [FoxPair.one]
  map_mul' x y := by
    change
      ({ deriv := foxFundamentalSum (R := R) (x * y), elt := x * y } :
          FoxPair R (FreeGroup α)) =
        FoxPair.mul
          ({ deriv := foxFundamentalSum (R := R) x, elt := x } : FoxPair R (FreeGroup α))
          ({ deriv := foxFundamentalSum (R := R) y, elt := y } : FoxPair R (FreeGroup α))
    apply FoxPair.ext
    · simp [FoxPair.mul, fox_fundamental_mul, FoxPair.basis]
    · simp [FoxPair.mul]

lemma fox_fundamental_aux (w : FreeGroup α) :
    MonoidAlgebra.single w (1 : R) - 1 =
      foxFundamentalSum (R := R) w := by
  have hHom :
      foxEpsilonHom (R := R) (α := α) =
        foxFundamentalHom (R := R) (α := α) := by
    apply FreeGroup.ext_hom
    intro b
    ext
    · simp [foxEpsilonHom, foxFundamentalHom, fox_fundamental]
    · simp [foxEpsilonHom, foxFundamentalHom]
  have hApply :=
    congrArg (fun φ : FreeGroup α →* FoxPair R (FreeGroup α) => φ w) hHom
  have hDeriv :=
    congrArg (fun p : FoxPair R (FreeGroup α) => p.deriv) hApply
  simpa [foxEpsilonHom, foxFundamentalHom, FoxPair.basis] using hDeriv

end Fundamental

/-- Fox derivatives satisfy the product rule. -/
theorem derivativeProductRule {R : Type u} {α : Type v} [Ring R]
    (a : α) :
    ∃ D : FreeGroup α → MonoidAlgebra R (FreeGroup α),
      D (FreeGroup.of a) = 1 ∧
      (∀ b : α, b ≠ a → D (FreeGroup.of b) = 0) ∧
        ∀ x y : FreeGroup α,
          D (x * y) = D x + MonoidAlgebra.single x (1 : R) * D y
  := by
  classical
  let gen : α → FoxPair R (FreeGroup α) := fun b =>
    { deriv := if b = a then (1 : MonoidAlgebra R (FreeGroup α)) else 0
      elt := FreeGroup.of b }
  let φ : FreeGroup α →* FoxPair R (FreeGroup α) := FreeGroup.lift gen
  let D : FreeGroup α → MonoidAlgebra R (FreeGroup α) := fun x => (φ x).deriv
  have hsndHom :
      (FoxPair.eltHom (R := R) (G := FreeGroup α)).comp φ =
        MonoidHom.id (FreeGroup α) := by
    apply (FreeGroup.lift : (α → FreeGroup α) ≃
      (FreeGroup α →* FreeGroup α)).symm.injective
    funext b
    simp [φ, gen, FoxPair.eltHom]
  have hsnd : ∀ x : FreeGroup α, (φ x).elt = x := by
    intro x
    have h := congrArg (fun f : FreeGroup α →* FreeGroup α => f x) hsndHom
    simpa [FoxPair.eltHom] using h
  refine ⟨D, ?_, ?_, ?_⟩
  · simp [D, φ, gen]
  · intro b hb
    simp [D, φ, gen, hb]
  · intro x y
    change (φ (x * y)).deriv =
      (φ x).deriv + MonoidAlgebra.single x (1 : R) * (φ y).deriv
    rw [φ.map_mul]
    simp [FoxPair.deriv_mul, hsnd x]
/-- Fox derivatives satisfy the inverse rule. -/
theorem foxDerivativeRule {R : Type u} {α : Type v} [Ring R]
    (a : α) :
    ∃ D : FreeGroup α → MonoidAlgebra R (FreeGroup α),
      D (FreeGroup.of a) = 1 ∧
      (∀ b : α, b ≠ a → D (FreeGroup.of b) = 0) ∧
        ∀ u : FreeGroup α,
          D u⁻¹ = -MonoidAlgebra.single u⁻¹ (1 : R) * D u
  := by
  classical
  let g : FreeGroup α := FreeGroup.of a
  let D : FreeGroup α → MonoidAlgebra R (FreeGroup α) := twoPointD R g
  have hg : g ≠ g⁻¹ := by
    change FreeGroup.of a ≠ (FreeGroup.of a)⁻¹
    exact free_ne_inv (a := a) (b := a)
  refine ⟨D, ?_, ?_, ?_⟩
  · simp [D, g, twoPointD]
  · intro b hb
    have hne : FreeGroup.of b ≠ g := by
      change FreeGroup.of b ≠ FreeGroup.of a
      exact free_group_ne (a := a) (b := b) hb
    have hne_inv : FreeGroup.of b ≠ g⁻¹ := by
      change FreeGroup.of b ≠ (FreeGroup.of a)⁻¹
      exact free_ne_inv (a := a) (b := b)
    simp [D, twoPointD, hne, hne_inv]
  · intro u
    simpa [D] using (point_d_rule (R := R) (g := g) hg u)
/-- The Fox fundamental formula. -/
theorem foxFundamentalFormula {R : Type u} {α : Type v} [Ring R] [Fintype α]
    :
    ∃ D : α → FreeGroup α → MonoidAlgebra R (FreeGroup α),
      (∀ a : α, D a (FreeGroup.of a) = 1) ∧
      (∀ a b : α, b ≠ a → D a (FreeGroup.of b) = 0) ∧
      (∀ a (x y : FreeGroup α),
        D a (x * y) = D a x + MonoidAlgebra.single x (1 : R) * D a y) ∧
      ∀ w : FreeGroup α,
        MonoidAlgebra.single w (1 : R) - 1 =
          Finset.sum Finset.univ (fun a : α =>
            D a w * (MonoidAlgebra.single (FreeGroup.of a) (1 : R) - 1))
  := by
  classical
  refine ⟨fun a w => foxD (R := R) a w, ?_, ?_, ?_, ?_⟩
  · intro a
    simp
  · intro a b h
    simpa using (fox_d_ne (R := R) a b h)
  · intro a x y
    simpa using (foxD_mul (R := R) a x y)
  · intro w
    simpa [foxFundamentalSum, FoxPair.basis] using
      (fox_fundamental_aux (R := R) (α := α) w)
/-- Iterated swaps preserve the reordered list up to permutation. -/
theorem iteratedSwapLemma {α : Type u} {xs ys : List α} :
    reordering xs ys → xs.Perm ys
  := by
  exact fun h => h

end Theorems
end Submission
