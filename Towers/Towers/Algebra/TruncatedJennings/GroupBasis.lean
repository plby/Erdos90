import Towers.Algebra.TruncatedJennings.OrderedWords


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

universe u v

open NumberField

namespace Towers
namespace TJennin

/-- The normal-form group basis used at the start of Step 7 of `S.tex`.

The ordered normal form gives a bijection
`Fin R.r → Fin p ≃ Q`. Reindexing the standard group-algebra basis by this bijection gives
the basis whose `e`th vector is the canonical group-algebra element
`[R.wordEquiv e] = [x_1^(e_1) ... x_r^(e_r)]`. -/
structure OBData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m) : Type (u + 1) where
  basis :
    Module.Basis (ULift.{u, 0} (Fin R.r → Fin p))
      (ZMod p) (denseGroupAlgebra p Q)
  basis_apply :
    ∀ e : ULift.{u, 0} (Fin R.r → Fin p),
      basis e = denseGeneratorsElement p Q (R.wordEquiv e.down)

namespace OBData

/-- The `e = 0` vector in the normal-form group basis is the algebra unit. -/
lemma basis_zero_one
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R) :
    G.basis (ULift.up (fun _ : Fin R.r => (0 : Fin p)) : ULift.{u, 0} (Fin R.r → Fin p)) =
      (1 : denseGroupAlgebra p Q) := by
  have hword_zero :
      R.wordEquiv (fun _ : Fin R.r => (0 : Fin p)) = 1 := by
    rw [R.wordEquiv_apply]
    unfold orderedWordFin orderedWord
    simp [fin_prod_one]
  rw [G.basis_apply]
  simp [hword_zero, denseGeneratorsElement, MonoidAlgebra.one_def]

/-- Coordinates of a normal-form basis vector in the normal-form basis. -/
lemma repr_ite
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e a : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr (G.basis e) a = if a = e then 1 else 0 := by
  classical
  by_cases hae : a = e
  · subst a
    simp
  · simp [hae]

/-- The diagonal coordinate of a normal-form basis vector is `1`. -/
lemma basis_repr_self
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr (G.basis e) e = 1 := by
  simp

/-- Off-diagonal coordinates of a normal-form basis vector vanish. -/
lemma basis_repr_ne
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hae : a ≠ e) :
    G.basis.repr (G.basis e) a = 0 := by
  classical
  simp [hae]

/-- The canonical element attached to a normal-form word is the corresponding normal-form basis
vector. -/
lemma canonical_word_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : ULift.{u, 0} (Fin R.r → Fin p)) :
    denseGeneratorsElement p Q (R.wordEquiv e.down) =
      G.basis e := by
  exact (G.basis_apply e).symm

/-- The canonical element attached to the concrete ordered word is the same normal-form basis
vector. -/
lemma canonical_fin_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) :
    denseGeneratorsElement p Q (orderedWordFin R.gen e) =
      G.basis (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) := by
  rw [G.basis_apply]
  congr 1
  exact (R.wordEquiv_apply e).symm

/-- Coordinates of a concrete ordered-word group-basis element in the normal-form group basis. -/
lemma repr_fin_ite
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p)
    (a : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr
        (denseGeneratorsElement p Q (orderedWordFin R.gen e)) a =
      if a = (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0 := by
  rw [G.canonical_fin_basis e]
  exact G.repr_ite (ULift.up e) a

/-- The diagonal coordinate of a concrete ordered-word group-basis element is `1`. -/
lemma repr_fin_self
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) :
    G.basis.repr
        (denseGeneratorsElement p Q (orderedWordFin R.gen e))
        (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  simpa using G.repr_fin_ite e (ULift.up e)

/-- Off-diagonal coordinates of a concrete ordered-word group-basis element vanish. -/
lemma repr_fin_ne
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hae : a ≠ (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p))) :
    G.basis.repr
        (denseGeneratorsElement p Q (orderedWordFin R.gen e)) a =
      0 := by
  classical
  simpa [hae] using G.repr_fin_ite e a

/-- Coordinates of `[orderedWordFin e] - 1` in the normal-form group basis.

This is the coefficient-level form of the first binomial factor expansion: subtracting the
constant word only changes the two normal-form group-basis coordinates indexed by `e` and by
the zero exponent vector. -/
lemma basis_repr_ite
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p)
    (a : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) a =
      (if a = (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) -
        (if a = (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
            ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) := by
  classical
  let zeroE : ULift.{u, 0} (Fin R.r → Fin p) :=
    ULift.up (fun _ : Fin R.r => (0 : Fin p))
  have hcanonical :
      denseGeneratorsElement p Q (orderedWordFin R.gen e) =
        G.basis (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) :=
    G.canonical_fin_basis e
  have hone :
      (1 : denseGroupAlgebra p Q) =
        G.basis zeroE :=
    (G.basis_zero_one).symm
  calc
    G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) a =
        G.basis.repr
          (G.basis (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) -
            G.basis zeroE) a := by
          simp [groupAlgebraSub, hcanonical, hone]
    _ =
        G.basis.repr (G.basis (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p))) a -
          G.basis.repr (G.basis zeroE) a := by
          simp
    _ =
        (if a = (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) -
          (if a = zeroE then 1 else 0) := by
          rw [G.repr_ite (ULift.up e) a, G.repr_ite zeroE a]
    _ =
        (if a = (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) -
          (if a = (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
              ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) := by
          rfl

/-- A nonzero coordinate of `[orderedWordFin e] - 1` can only occur at the word `e` or at the
constant word. -/
lemma repr_fin_support
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hcoeff :
      G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) a ≠ 0) :
    a = (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) ∨
      a =
        (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
          ULift.{u, 0} (Fin R.r → Fin p)) := by
  classical
  by_contra hno
  have hne_e :
      a ≠ (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) := by
    intro ha
    exact hno (Or.inl ha)
  have hne_zero :
      a ≠
        (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
          ULift.{u, 0} (Fin R.r → Fin p)) := by
    intro ha
    exact hno (Or.inr ha)
  have hcoeff_zero :
      G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) a = 0 := by
    simpa [hne_e, hne_zero] using
      G.basis_repr_ite e a
  exact hcoeff hcoeff_zero

/-- The support statement above immediately gives coordinatewise support control. -/
lemma basis_repr_support
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hcoeff :
      G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) a ≠ 0) :
    exponentCoordinatewiseLE a.down e := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rcases G.repr_fin_support hcoeff with h | h
  · rw [h]
    exact exponent_coordinatewise_refl e
  · rw [h]
    exact exponent_coordinatewise_left e

/-- The top coordinate of `[orderedWordFin e] - 1` is `1` when `e` is nonzero. -/
lemma basis_repr_diagonal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    (he : e ≠ fun _ : Fin R.r => (0 : Fin p)) :
    G.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e))
        (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  classical
  have hne_zero :
      (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p)) ≠
        (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
          ULift.{u, 0} (Fin R.r → Fin p)) := by
    intro h
    exact he (congrArg ULift.down h)
  simpa [hne_zero] using
    G.basis_repr_ite e
      (ULift.up e : ULift.{u, 0} (Fin R.r → Fin p))

/-- The zero Jennings monomial has the same normal-form coordinates as the constant group word.

This is the degree-zero base case of the Step 7 triangular expansion. -/
lemma repr_monomial_ite
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (a : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr
        (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p))) a =
      if a =
          (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
            ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0 := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let e0 : Fin R.r → Fin p := fun _ => 0
  let e0u : ULift.{u, 0} (Fin R.r → Fin p) := ULift.up e0
  have hmonomial :
      jenningsMonomialFin p Q R.gen e0 =
        (1 : denseGroupAlgebra p Q) := by
    unfold jenningsMonomialFin
    simpa [e0] using
      (fin_prod_one
        (M := denseGroupAlgebra p Q) R.r)
  have hone_basis :
      (1 : denseGroupAlgebra p Q) = G.basis e0u := by
    simpa [e0, e0u] using (G.basis_zero_one).symm
  calc
    G.basis.repr
        (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p))) a =
        G.basis.repr (G.basis e0u) a := by
          simpa [e0] using congrArg (fun x => G.basis.repr x a) (hmonomial.trans hone_basis)
    _ = (if a = e0u then 1 else 0) := G.repr_ite e0u a
    _ =
        (if a =
          (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
            ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0) := by
          rfl

/-- The zero Jennings monomial has no support above the zero exponent. -/
lemma repr_jennings_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hcoeff :
      G.basis.repr
          (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p))) a ≠ 0) :
    exponentCoordinatewiseLE a.down (fun _ : Fin R.r => (0 : Fin p)) := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  by_cases ha :
      a =
        (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
          ULift.{u, 0} (Fin R.r → Fin p))
  · rw [ha]
    exact exponent_coordinatewise_refl (fun _ : Fin R.r => (0 : Fin p))
  · have hzero :
        G.basis.repr
            (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p))) a = 0 := by
      simpa [ha] using G.repr_monomial_ite a
    exact False.elim (hcoeff hzero)

/-- The diagonal coefficient of the zero Jennings monomial is `1`. -/
lemma repr_jennings_diagonal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R) :
    G.basis.repr
        (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p)))
        (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
          ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  simpa using
    G.repr_monomial_ite
      (ULift.up (fun _ : Fin R.r => (0 : Fin p)) :
        ULift.{u, 0} (Fin R.r → Fin p))

/-- A single Jennings monomial has coordinatewise triangular support in the normal-form group
basis.

This is the one-letter base case of the Step 7 expansion:
`u_i = [x_i] - 1`, so its only possible normal-form group-basis coordinates are the constant
word and the word `x_i`. -/
lemma basis_repr_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hcoeff :
      G.basis.repr
          (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i)) a ≠ 0) :
    exponentCoordinatewiseLE a.down (singleJenningsExponent (p := p) i) := by
  have hmonomial :
      jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i) =
        groupAlgebraSub p Q
          (orderedWordFin R.gen (singleJenningsExponent (p := p) i)) := by
    rw [monomial_single_exponent]
    rw [single_jennings_exponent]
  have hcoeff' :
      G.basis.repr
          (groupAlgebraSub p Q
            (orderedWordFin R.gen (singleJenningsExponent (p := p) i))) a ≠ 0 := by
    simpa [hmonomial] using hcoeff
  exact G.basis_repr_support hcoeff'

/-- The only possible nonzero coordinates of a single Jennings monomial are the constant word
and the corresponding single word. -/
lemma repr_monomial_cases
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hcoeff :
      G.basis.repr
          (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i)) a ≠ 0) :
    a.down = (fun _ : Fin R.r => (0 : Fin p)) ∨
      a.down = singleJenningsExponent (p := p) i := by
  exact
    or_single_exponent
      (p := p)
      (G.basis_repr_monomial i hcoeff)

/-- A normal-form group-basis coordinate outside the two one-letter possibilities is zero. -/
lemma repr_monomial_support
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hzero : a.down ≠ (fun _ : Fin R.r => (0 : Fin p)))
    (hsingle : a.down ≠ singleJenningsExponent (p := p) i) :
    G.basis.repr
        (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i)) a = 0 := by
  by_contra hcoeff_zero
  have hcoeff :
      G.basis.repr
          (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i)) a ≠ 0 :=
    hcoeff_zero
  rcases G.repr_monomial_cases i hcoeff with h | h
  · exact hzero h
  · exact hsingle h

/-- The diagonal coefficient of a single Jennings monomial is `1`. -/
lemma repr_single_diagonal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r) :
    G.basis.repr
        (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i))
        (ULift.up (singleJenningsExponent (p := p) i) :
          ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  have hmonomial :
      jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i) =
        groupAlgebraSub p Q
          (orderedWordFin R.gen (singleJenningsExponent (p := p) i)) := by
    rw [monomial_single_exponent]
    rw [single_jennings_exponent]
  have hdiag :
      G.basis.repr
          (groupAlgebraSub p Q
            (orderedWordFin R.gen (singleJenningsExponent (p := p) i)))
          (ULift.up (singleJenningsExponent (p := p) i) :
            ULift.{u, 0} (Fin R.r → Fin p)) = 1 :=
    G.basis_repr_diagonal
      (e := singleJenningsExponent (p := p) i)
      (single_jennings_zero (p := p) i)
  simpa [hmonomial] using hdiag

/-- A group-algebra element is supported below an exponent vector, with respect to the
normal-form group basis, if every nonzero normal-form coordinate has exponent vector
coordinatewise below it.

This packages the triangular-support half of Step 7 so that later binomial expansions can be
assembled by linearity instead of reproving the same coordinate argument for every sum. -/
def supportBelow
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p)
    (x : denseGroupAlgebra p Q) : Prop :=
  ∀ a : ULift.{u, 0} (Fin R.r → Fin p),
    G.basis.repr x a ≠ 0 → exponentCoordinatewiseLE a.down e

/-- The zero element has triangular support below every exponent vector. -/
lemma supportBelow_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) :
    G.supportBelow e (0 : denseGroupAlgebra p Q) := by
  intro a hcoeff
  have hzero :
      G.basis.repr (0 : denseGroupAlgebra p Q) a = 0 := by
    simp
  exact False.elim (hcoeff hzero)

/-- A normal-form basis vector is supported below any exponent vector above its index. -/
lemma support_below_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hae : exponentCoordinatewiseLE a.down e) :
    G.supportBelow e (G.basis a) := by
  intro b hcoeff
  by_cases hba : b = a
  · rw [hba]
    exact hae
  · have hzero : G.basis.repr (G.basis a) b = 0 :=
      G.basis_repr_ne (e := a) (a := b) hba
    exact False.elim (hcoeff hzero)

/-- Support-below is monotone in the bounding exponent vector. -/
lemma supportBelow_mono
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e f : Fin R.r → Fin p}
    {x : denseGroupAlgebra p Q}
    (hef : exponentCoordinatewiseLE e f)
    (hx : G.supportBelow e x) :
    G.supportBelow f x := by
  intro a hcoeff
  exact exponent_trans (hx a hcoeff) hef

/-- A coefficient outside the triangular support bound is zero. -/
lemma basis_repr_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {x : denseGroupAlgebra p Q}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hx : G.supportBelow e x)
    (ha : ¬ exponentCoordinatewiseLE a.down e) :
    G.basis.repr x a = 0 := by
  by_contra hcoeff_zero
  exact ha (hx a hcoeff_zero)

/-- A coefficient whose total degree is larger than the support bound must vanish. -/
lemma repr_below_total
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {x : denseGroupAlgebra p Q}
    {a : ULift.{u, 0} (Fin R.r → Fin p)}
    (hx : G.supportBelow e x)
    (hdeg : exponentTotalDegree e < exponentTotalDegree a.down) :
    G.basis.repr x a = 0 := by
  by_contra hcoeff_zero
  have hle :
      exponentTotalDegree a.down ≤ exponentTotalDegree e :=
    exponent_coordinatewise_degree (hx a hcoeff_zero)
  omega

/-- Support-below is closed under scalar multiplication. -/
lemma supportBelow_smul
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (c : ZMod p)
    {e : Fin R.r → Fin p}
    {x : denseGroupAlgebra p Q}
    (hx : G.supportBelow e x) :
    G.supportBelow e (c • x) := by
  intro a hcoeff
  by_cases hxa : G.basis.repr x a = 0
  · have hzero : G.basis.repr (c • x) a = 0 := by
      simp [hxa]
    exact False.elim (hcoeff hzero)
  · exact hx a hxa

/-- Support-below is closed under negation. -/
lemma supportBelow_neg
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {x : denseGroupAlgebra p Q}
    (hx : G.supportBelow e x) :
    G.supportBelow e (-x) := by
  intro a hcoeff
  by_cases hxa : G.basis.repr x a = 0
  · have hzero : G.basis.repr (-x) a = 0 := by
      simp [hxa]
    exact False.elim (hcoeff hzero)
  · exact hx a hxa

/-- Support-below is closed under addition. -/
lemma supportBelow_add
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {x y : denseGroupAlgebra p Q}
    (hx : G.supportBelow e x)
    (hy : G.supportBelow e y) :
    G.supportBelow e (x + y) := by
  intro a hcoeff
  by_cases hxa : G.basis.repr x a = 0
  · have hya : G.basis.repr y a ≠ 0 := by
      intro hyzero
      have hzero : G.basis.repr (x + y) a = 0 := by
        simp [hxa, hyzero]
      exact hcoeff hzero
    exact hy a hya
  · exact hx a hxa

/-- Support-below is closed under subtraction. -/
lemma supportBelow_sub
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {e : Fin R.r → Fin p}
    {x y : denseGroupAlgebra p Q}
    (hx : G.supportBelow e x)
    (hy : G.supportBelow e y) :
    G.supportBelow e (x - y) := by
  simpa [sub_eq_add_neg] using G.supportBelow_add hx (G.supportBelow_neg hy)

/-- Support-below is closed under finite sums. -/
lemma below_finset_sum
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {α : Type*}
    (s : Finset α)
    (f : α → denseGroupAlgebra p Q)
    {e : Fin R.r → Fin p}
    (hf : ∀ a ∈ s, G.supportBelow e (f a)) :
    G.supportBelow e (∑ a ∈ s, f a) := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    simpa using G.supportBelow_zero e
  · intro a s has ih hf
    have ha : G.supportBelow e (f a) :=
      hf a (Finset.mem_insert_self a s)
    have hs : G.supportBelow e (∑ b ∈ s, f b) := by
      refine ih ?_
      intro b hb
      exact hf b (Finset.mem_insert_of_mem hb)
    simpa [Finset.sum_insert has] using G.supportBelow_add ha hs

/-- A finite linear combination of normal-form basis vectors stays supported below `e` if all
appearing indices do. -/
lemma support_finset_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (s : Finset (ULift.{u, 0} (Fin R.r → Fin p)))
    (c : ULift.{u, 0} (Fin R.r → Fin p) → ZMod p)
    {e : Fin R.r → Fin p}
    (hle : ∀ a ∈ s, exponentCoordinatewiseLE a.down e) :
    G.supportBelow e (∑ a ∈ s, c a • G.basis a) := by
  refine G.below_finset_sum s (fun a => c a • G.basis a) ?_
  intro a ha
  exact G.supportBelow_smul (c a) (G.support_below_basis (hle a ha))

/-- A finite linear combination of normal-form basis vectors indexed through an arbitrary finite
set stays supported below `e` if every selected basis index is below `e`. -/
lemma support_below_finset
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    {α : Type*}
    (s : Finset α)
    (idx : α → ULift.{u, 0} (Fin R.r → Fin p))
    (c : α → ZMod p)
    {e : Fin R.r → Fin p}
    (hle : ∀ a ∈ s, exponentCoordinatewiseLE (idx a).down e) :
    G.supportBelow e (∑ a ∈ s, c a • G.basis (idx a)) := by
  refine G.below_finset_sum s (fun a => c a • G.basis (idx a)) ?_
  intro a ha
  exact G.supportBelow_smul (c a) (G.support_below_basis (hle a ha))

/-- The usual finite group-basis expansion, recorded in the normal-form order. -/
lemma group_basis_expansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (x : denseGroupAlgebra p Q) :
    x =
      ∑ a : ULift.{u, 0} (Fin R.r → Fin p),
        G.basis.repr x a • G.basis a := by
  classical
  simp

/-- The concrete normal-form word `[orderedWordFin e]` is supported exactly at `e`, hence below
`e`. -/
lemma support_below_canonical
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) :
    G.supportBelow e
      (denseGeneratorsElement p Q (orderedWordFin R.gen e)) := by
  rw [G.canonical_fin_basis e]
  exact G.support_below_basis (a := ULift.up e) (exponent_coordinatewise_refl e)

/-- The first binomial factor `[orderedWordFin e] - 1` is supported below `e`. -/
lemma support_below_fin
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) :
    G.supportBelow e (groupAlgebraSub p Q (orderedWordFin R.gen e)) := by
  intro a hcoeff
  exact G.basis_repr_support hcoeff

/-- Coordinate form of the normal-form group-basis coefficient formula for a one-coordinate
ordered word. -/
lemma repr_jennings_ite
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    (k : Fin p)
    (a : ULift.{u, 0} (Fin R.r → Fin p)) :
    G.basis.repr
        (denseGeneratorsElement p Q
          (orderedWordFin R.gen (coordinateJenningsExponent (p := p) i k))) a =
      if a =
          (ULift.up (coordinateJenningsExponent (p := p) i k) :
            ULift.{u, 0} (Fin R.r → Fin p)) then 1 else 0 := by
  exact G.repr_fin_ite
    (coordinateJenningsExponent (p := p) i k) a

/-- The diagonal normal-form coordinate of a one-coordinate ordered word is `1`. -/
lemma repr_jennings_self
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    (k : Fin p) :
    G.basis.repr
        (denseGeneratorsElement p Q
          (orderedWordFin R.gen (coordinateJenningsExponent (p := p) i k)))
        (ULift.up (coordinateJenningsExponent (p := p) i k) :
          ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  simpa using
    G.repr_jennings_ite i k
      (ULift.up (coordinateJenningsExponent (p := p) i k) :
        ULift.{u, 0} (Fin R.r → Fin p))

/-- A one-coordinate normal-form group word is supported below its one-coordinate exponent. -/
lemma support_jennings_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    (k : Fin p) :
    G.supportBelow (coordinateJenningsExponent (p := p) i k)
      (denseGeneratorsElement p Q
        (orderedWordFin R.gen (coordinateJenningsExponent (p := p) i k))) := by
  exact G.support_below_canonical
    (coordinateJenningsExponent (p := p) i k)

/-- The first binomial factor attached to a one-coordinate word is supported below that
one-coordinate exponent. -/
lemma support_below_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    (k : Fin p) :
    G.supportBelow (coordinateJenningsExponent (p := p) i k)
      (groupAlgebraSub p Q
        (orderedWordFin R.gen (coordinateJenningsExponent (p := p) i k))) := by
  exact G.support_below_fin
    (coordinateJenningsExponent (p := p) i k)

/-- The zero Jennings monomial is supported below the zero exponent. -/
lemma support_below_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R) :
    G.supportBelow (fun _ : Fin R.r => (0 : Fin p))
      (jenningsMonomialFin p Q R.gen (fun _ : Fin R.r => (0 : Fin p))) := by
  intro a hcoeff
  exact G.repr_jennings_monomial hcoeff

/-- A single Jennings monomial is supported below its single exponent vector. -/
lemma support_monomial_single
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r) :
    G.supportBelow (singleJenningsExponent (p := p) i)
      (jenningsMonomialFin p Q R.gen (singleJenningsExponent (p := p) i)) := by
  intro a hcoeff
  exact G.basis_repr_monomial i hcoeff

/-- A coefficient package for the one-variable binomial expansion
`u_i^k = ([x_i]-1)^k` in the normal-form group basis.

The finite sum is indexed by the values `l ≤ k`; the corresponding basis vector is the
normal-form word with exponent `coordinateJenningsExponent i l`. This is the exact
one-coordinate algebraic calculation needed for the support half of Step 7, and later for the
diagonal coefficient. -/
structure CoordinateJenningsData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R)
    (i : Fin R.r)
    (k : Fin p) : Type (u + 1) where
  coeff : Fin p → ZMod p
  expansion :
    jenningsMonomialFin p Q R.gen (coordinateJenningsExponent (p := p) i k) =
      ∑ l ∈ coordinateJenningsFinset k,
        coeff l •
          G.basis
            (ULift.up (coordinateJenningsExponent (p := p) i l) :
              ULift.{u, 0} (Fin R.r → Fin p))
  top_coeff :
    coeff k = 1

/-- The expansion certificate immediately implies one-coordinate triangular support. -/
lemma support_below_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {G : OBData (p := p) (Q := Q) R}
    {i : Fin R.r}
    {k : Fin p}
    (E : CoordinateJenningsData (p := p) (Q := Q) G i k) :
    G.supportBelow (coordinateJenningsExponent (p := p) i k)
      (jenningsMonomialFin p Q R.gen
        (coordinateJenningsExponent (p := p) i k)) := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [E.expansion]
  refine
    G.support_below_finset
      (coordinateJenningsFinset k)
      (fun l : Fin p =>
        (ULift.up (coordinateJenningsExponent (p := p) i l) :
          ULift.{u, 0} (Fin R.r → Fin p)))
      E.coeff ?_
  intro l hl
  exact
    exponent_coordinatewise_finset
      (p := p) (i := i) hl

/-- The one-coordinate expansion certificate has diagonal coefficient `1`. -/
lemma repr_monomial_diagonal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {G : OBData (p := p) (Q := Q) R}
    {i : Fin R.r}
    {k : Fin p}
    (E : CoordinateJenningsData (p := p) (Q := Q) G i k) :
    G.basis.repr
        (jenningsMonomialFin p Q R.gen
          (coordinateJenningsExponent (p := p) i k))
        (ULift.up (coordinateJenningsExponent (p := p) i k) :
          ULift.{u, 0} (Fin R.r → Fin p)) = 1 := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let top : ULift.{u, 0} (Fin R.r → Fin p) :=
    ULift.up (coordinateJenningsExponent (p := p) i k)
  rw [E.expansion]
  calc
    G.basis.repr
          (∑ l ∈ coordinateJenningsFinset k,
            E.coeff l •
              G.basis
                (ULift.up (coordinateJenningsExponent (p := p) i l) :
                  ULift.{u, 0} (Fin R.r → Fin p))) top =
        (∑ l ∈ coordinateJenningsFinset k,
          G.basis.repr
            (E.coeff l •
              G.basis
                (ULift.up (coordinateJenningsExponent (p := p) i l) :
                  ULift.{u, 0} (Fin R.r → Fin p)))) top := by
          simp
    _ =
        ∑ l ∈ coordinateJenningsFinset k,
          (G.basis.repr
            (E.coeff l •
              G.basis
                (ULift.up (coordinateJenningsExponent (p := p) i l) :
                  ULift.{u, 0} (Fin R.r → Fin p)))) top := by
          simp
    _ = 1 := by
        rw [Finset.sum_eq_single k]
        · simp [top, E.top_coeff]
        · intro l hl hlk
          have hne_idx :
              (ULift.up (coordinateJenningsExponent (p := p) i l) :
                ULift.{u, 0} (Fin R.r → Fin p)) ≠ top := by
            intro h
            apply hlk
            have hcoord :=
              congrArg (fun a : ULift.{u, 0} (Fin R.r → Fin p) => a.down i) h
            simpa [top, coordinate_jennings_self] using hcoord
          have hsingle :
              (Finsupp.single
                (ULift.up (coordinateJenningsExponent (p := p) i l) :
                  ULift.{u, 0} (Fin R.r → Fin p))
                (E.coeff l) :
                  ULift.{u, 0} (Fin R.r → Fin p) →₀ ZMod p) top = 0 :=
            Finsupp.single_eq_of_ne hne_idx.symm
          simpa using hsingle
        · intro hknot
          exact False.elim (hknot (self_jennings_finset k))

/-- Rewriting the coordinate-factor ordered product in Step 7 back to the standard definition
of `jenningsMonomialFin`. -/
lemma jennings_monomial_factors
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    finOrderedProd r
        (fun i : Fin r =>
          jenningsMonomialFin p Q x
            (coordinateJenningsExponent (p := p) i (e i))) =
      jenningsMonomialFin p Q x e := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  calc
    finOrderedProd r
        (fun i : Fin r =>
          jenningsMonomialFin p Q x
            (coordinateJenningsExponent (p := p) i (e i))) =
        finOrderedProd r
          (fun i : Fin r => groupAlgebraSub p Q (x i) ^ (e i).val) := by
          apply fin_prod_congr
          intro i
          exact monomial_fin_exponent
            (p := p) (Q := Q) x i (e i)
    _ = jenningsMonomialFin p Q x e := by
          exact (jennings_monomial_prod
            (p := p) (Q := Q) x e).symm

end OBData

/-- Step 7 first paragraph: the normal-form words are just the standard group basis in a new
order. -/
theorem ordered_basis_reps
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m) :
    Nonempty (OBData (p := p) (Q := Q) R) := by
  classical
  have hword_surjective : Function.Surjective R.wordEquiv := R.wordEquiv.surjective
  have hword_injective : Function.Injective R.wordEquiv := R.wordEquiv.injective
  let wordEquivULift : ULift.{u, 0} (Fin R.r → Fin p) ≃ Q :=
    { toFun := fun e => R.wordEquiv e.down
      invFun := fun q => ULift.up (R.wordEquiv.symm q)
      left_inv := by
        intro e
        cases e with
        | up e =>
            simp
      right_inv := by
        intro q
        simp }
  let groupBasis : Module.Basis Q (ZMod p) (denseGroupAlgebra p Q) :=
    Finsupp.basisSingleOne
  refine ⟨{
    basis := groupBasis.reindex wordEquivULift.symm
    basis_apply := ?_
  }⟩
  intro e
  rw [Module.Basis.reindex_apply]
  dsimp [groupBasis, wordEquivULift, denseGeneratorsElement]
  change
    Finsupp.basisSingleOne (R.wordEquiv e.down) =
      (Finsupp.single (R.wordEquiv e.down) (1 : ZMod p) : Q →₀ ZMod p)
  exact
    congrFun (Finsupp.coe_basisSingleOne (ι := Q) (R := ZMod p))
      (R.wordEquiv e.down)

/-- The direct triangular expansion of Jennings monomials in the normal-form group basis.

This is the algebraic half of Step 7 read in the direction
`u^e = ∏ᵢ ([x_i]-1)^{e_i}`. Expanding each factor in the already-established group basis gives
only normal-form words whose exponent vector is coordinatewise at most `e`; the coefficient of
the top word is `1`.

The inverse unitriangular argument below will turn this direct expansion into the statement that
the group words also expand triangularly in the Jennings monomials. -/
structure JenningsMonomialTriangular
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R) : Type (u + 1) where
  monomial_support_le :
    ∀ e a : ULift.{u, 0} (Fin R.r → Fin p),
      G.basis.repr (jenningsMonomialFin p Q R.gen e.down) a ≠ 0 →
        exponentCoordinatewiseLE a.down e.down
  monomial_diagonal_coeff :
    ∀ e : ULift.{u, 0} (Fin R.r → Fin p),
      G.basis.repr (jenningsMonomialFin p Q R.gen e.down) e = 1

/-- The triangular Jennings basis data promised by the second half of Step 7 of `S.tex`.

Starting from the reordered group basis, expand
`[R.wordEquiv e] = prod_i (1 + u_i)^(e_i)`. The coefficient of `u^e` is `1`, and every other
Jennings monomial in that expansion has exponent vector coordinatewise below `e`. Unitriangular
finite linear algebra then gives a genuine basis whose vectors are exactly the ordered Jennings
monomials. -/
structure JTData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (G : OBData (p := p) (Q := Q) R) : Type (u + 1) where
  basis :
    Module.Basis (ULift.{u, 0} (Fin R.r → Fin p))
      (ZMod p) (denseGroupAlgebra p Q)
  basis_apply :
    ∀ e : ULift.{u, 0} (Fin R.r → Fin p),
      basis e = jenningsMonomialFin p Q R.gen e.down
  group_word_support :
    ∀ e a : ULift.{u, 0} (Fin R.r → Fin p),
      basis.repr (G.basis e) a ≠ 0 →
        ∀ j : Fin R.r, (a.down j).val ≤ (e.down j).val
  group_diagonal_coeff :
    ∀ e : ULift.{u, 0} (Fin R.r → Fin p),
      basis.repr (G.basis e) e = 1

namespace JTData

/-- Package the triangular Jennings basis as the `MBData` used by the rest of the
formalization. -/
def monomialBasisData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {G : OBData (p := p) (Q := Q) R}
    (T : JTData (p := p) (Q := Q) G) :
    MBData.{u, u} (p := p) (Q := Q) R where
  ι := ULift.{u, 0} (Fin R.r → Fin p)
  decEq := inferInstance
  basis := T.basis
  weight := fun e => expWeight R.weight e.down
  monomialIndex :=
    { toFun := fun e => e.down
      invFun := fun e => ULift.up e
      left_inv := by
        intro e
        cases e
        rfl
      right_inv := by
        intro e
        rfl }
  basis_apply := by
    intro e
    exact T.basis_apply e
  weight_apply := by
    intro e
    rfl

end JTData

/-- The zero exponent vector gives the constant Jennings monomial. -/
lemma jennings_monomial_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q) :
    jenningsMonomialFin p Q x (fun _ : Fin r => (0 : Fin p)) =
      (1 : denseGroupAlgebra p Q) := by
  unfold jenningsMonomialFin
  simpa using
    (fin_prod_one
      (M := denseGroupAlgebra p Q) r)

/-- Every group-algebra element has a finite expansion in the chosen Jennings monomial basis.
This is just `Module.Basis.sum_repr`, rewritten through `MBData.basis_apply`. -/
lemma MBData.finite_jenningsExpansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, u} (p := p) (Q := Q) R)
    (x : denseGroupAlgebra p Q) :
    x =
      ∑ i : B.ι,
        B.basis.repr x i •
          jenningsMonomialFin p Q R.gen (B.monomialIndex i) := by
  classical
  letI : Fintype B.ι := Fintype.ofEquiv (Fin R.r → Fin p) B.monomialIndex.symm
  letI : DecidableEq B.ι := B.decEq
  calc
    x = ∑ i : B.ι, B.basis.repr x i • B.basis i := by
      simp
    _ =
      ∑ i : B.ι,
        B.basis.repr x i •
          jenningsMonomialFin p Q R.gen (B.monomialIndex i) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [B.basis_apply]

/-- If all coordinates of the monomial index vanish, then the index is the zero exponent
vector. -/
lemma MBData.monomi_zeroe_coord
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {i : B.ι}
    (hzero : ∀ j : Fin R.r, B.monomialIndex i j = 0) :
    B.monomialIndex i = (fun _ : Fin R.r => (0 : Fin p)) := by
  funext j
  exact hzero j

/-- If all coordinates of an index vanish, the index itself is the basis index corresponding to
the constant Jennings monomial. -/
lemma MBData.eqsymm_zeroexpofora_coordeqzero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {i : B.ι}
    (hzero : ∀ j : Fin R.r, B.monomialIndex i j = 0) :
    i = B.monomialIndex.symm (fun _ : Fin R.r => (0 : Fin p)) := by
  apply B.monomialIndex.injective
  simp [B.monomi_zeroe_coord hzero]

end TJennin
end Towers
