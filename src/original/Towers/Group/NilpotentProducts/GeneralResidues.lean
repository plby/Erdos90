import Mathlib.GroupTheory.Congruence.Defs
import Towers.Group.NilpotentProducts.GeneralLaw
import Towers.Group.NilpotentProducts.AdmissibleOrders

/-!
# Arbitrary-rank equation-(18) residue groups

This file proves the well-definedness of the multiplication table in
Struik's Theorem 2 for cyclic orders that are odd or zero.
-/

namespace Struik
namespace P1960

/-- The modulus of a pair coordinate. -/
def generalPairModulus {t : ℕ} (order : Fin t → ℕ)
    (q : Pair t) : ℕ :=
  Nat.gcd (order q.i) (order q.j)

/-- The modulus of a mixed triple coordinate. -/
def generalResiduesModulus {t : ℕ} (order : Fin t → ℕ)
    (q : Triple t) : ℕ :=
  Nat.gcd (Nat.gcd (order q.i) (order q.j)) (order q.k)

private lemma modulus_dvd_i
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ order q.i :=
  (Nat.gcd_dvd_left (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
    (Nat.gcd_dvd_left (order q.i) (order q.j))

private lemma modulus_dvd_j
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ order q.j :=
  (Nat.gcd_dvd_left (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
    (Nat.gcd_dvd_right (order q.i) (order q.j))

private lemma modulus_dvd_k
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ order q.k :=
  Nat.gcd_dvd_right (Nat.gcd (order q.i) (order q.j)) (order q.k)

private lemma modulus_dvd_ij
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ generalPairModulus order q.ij :=
  Nat.gcd_dvd_left (Nat.gcd (order q.i) (order q.j)) (order q.k)

private lemma modulus_dvd_ik
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ generalPairModulus order q.ik :=
  Nat.dvd_gcd (modulus_dvd_i order q)
    (modulus_dvd_k order q)

private lemma modulus_dvd_jk
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    generalResiduesModulus order q ∣ generalPairModulus order q.jk :=
  Nat.dvd_gcd (modulus_dvd_j order q)
    (modulus_dvd_k order q)

/-- Coordinatewise congruence modulo the orders prescribed in Theorem 2. -/
structure GMEq {t : ℕ}
    (order : Fin t → ℕ)
    (c d : GCoordi t) : Prop where
  single : ∀ i, c.single i ≡ d.single i [ZMOD (order i : ℤ)]
  pair : ∀ q, c.pair q ≡ d.pair q
    [ZMOD (generalPairModulus order q : ℤ)]
  pairLeft : ∀ q, c.pairLeft q ≡ d.pairLeft q
    [ZMOD (generalPairModulus order q : ℤ)]
  pairRight : ∀ q, c.pairRight q ≡ d.pairRight q
    [ZMOD (generalPairModulus order q : ℤ)]
  tripleFirst : ∀ q, c.tripleFirst q ≡ d.tripleFirst q
    [ZMOD (generalResiduesModulus order q : ℤ)]
  tripleSecond : ∀ q, c.tripleSecond q ≡ d.tripleSecond q
    [ZMOD (generalResiduesModulus order q : ℤ)]

namespace GMEq

theorem refl {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) :
    GMEq order c c :=
  ⟨fun _ => .refl _, fun _ => .refl _, fun _ => .refl _,
    fun _ => .refl _, fun _ => .refl _, fun _ => .refl _⟩

theorem symm {t : ℕ} {order : Fin t → ℕ}
    {c d : GCoordi t}
    (h : GMEq order c d) :
    GMEq order d c :=
  ⟨fun i => (h.single i).symm, fun q => (h.pair q).symm,
    fun q => (h.pairLeft q).symm, fun q => (h.pairRight q).symm,
    fun q => (h.tripleFirst q).symm, fun q => (h.tripleSecond q).symm⟩

theorem trans {t : ℕ} {order : Fin t → ℕ}
    {c d e : GCoordi t}
    (hcd : GMEq order c d)
    (hde : GMEq order d e) :
    GMEq order c e :=
  ⟨fun i => (hcd.single i).trans (hde.single i),
    fun q => (hcd.pair q).trans (hde.pair q),
    fun q => (hcd.pairLeft q).trans (hde.pairLeft q),
    fun q => (hcd.pairRight q).trans (hde.pairRight q),
    fun q => (hcd.tripleFirst q).trans (hde.tripleFirst q),
    fun q => (hcd.tripleSecond q).trans (hde.tripleSecond q)⟩

/-- The arbitrary-rank table (18) respects all prescribed residue moduli. -/
theorem mul {t : ℕ} {order : Fin t → ℕ}
    (horder : ∀ i, AOrd (order i))
    {c c' d d' : GCoordi t}
    (hc : GMEq order c c')
    (hd : GMEq order d d') :
    GMEq order
      (GCoordi.mul c d)
      (GCoordi.mul c' d') := by
  refine ⟨fun i => (hc.single i).add (hd.single i), ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have hcj := mod_dvd_nat (hc.single q.j)
      (Nat.gcd_dvd_right (order q.i) (order q.j))
    have hdi := mod_dvd_nat (hd.single q.i)
      (Nat.gcd_dvd_left (order q.i) (order q.j))
    exact ((hc.pair q).add (hd.pair q)).sub (hcj.mul hdi)
  · intro q
    have hcj := mod_dvd_nat (hc.single q.j)
      (Nat.gcd_dvd_right (order q.i) (order q.j))
    have hdi := mod_dvd_nat (hd.single q.i)
      (Nat.gcd_dvd_left (order q.i) (order q.j))
    have hchoose :=
      choose_admissible_order
        ((horder q.i).gcd (horder q.j)) hdi
    exact (((hc.pairLeft q).add (hd.pairLeft q)).sub
      (hcj.mul hchoose)).add ((hc.pair q).mul hdi)
  · intro q
    have hci := mod_dvd_nat (hc.single q.i)
      (Nat.gcd_dvd_left (order q.i) (order q.j))
    have hcj := mod_dvd_nat (hc.single q.j)
      (Nat.gcd_dvd_right (order q.i) (order q.j))
    have hdi := mod_dvd_nat (hd.single q.i)
      (Nat.gcd_dvd_left (order q.i) (order q.j))
    have hdj := mod_dvd_nat (hd.single q.j)
      (Nat.gcd_dvd_right (order q.i) (order q.j))
    have hchoose :=
      choose_admissible_order
        ((horder q.i).gcd (horder q.j)) hcj
    exact ((((hc.pairRight q).add (hd.pairRight q)).sub
      (hdi.mul hchoose)).add ((hc.pair q).mul hdj)).sub
      ((hdi.mul hdj).mul hcj)
  · intro q
    have hci := mod_dvd_nat (hc.single q.i)
      (modulus_dvd_i order q)
    have hcj := mod_dvd_nat (hc.single q.j)
      (modulus_dvd_j order q)
    have hck := mod_dvd_nat (hc.single q.k)
      (modulus_dvd_k order q)
    have hdi := mod_dvd_nat (hd.single q.i)
      (modulus_dvd_i order q)
    have hdj := mod_dvd_nat (hd.single q.j)
      (modulus_dvd_j order q)
    have hdk := mod_dvd_nat (hd.single q.k)
      (modulus_dvd_k order q)
    have hcij := mod_dvd_nat (hc.pair q.ij)
      (modulus_dvd_ij order q)
    have hcik := mod_dvd_nat (hc.pair q.ik)
      (modulus_dvd_ik order q)
    exact ((((((hc.tripleFirst q).add (hd.tripleFirst q)).add
      (hcik.mul hdj)).add (hcij.mul hdk)).sub
      ((hdi.mul hcj).mul hck)).sub ((hck.mul hdi).mul hdj)).sub
      ((hcj.mul hdi).mul hdk)
  · intro q
    have hck := mod_dvd_nat (hc.single q.k)
      (modulus_dvd_k order q)
    have hdi := mod_dvd_nat (hd.single q.i)
      (modulus_dvd_i order q)
    have hdj := mod_dvd_nat (hd.single q.j)
      (modulus_dvd_j order q)
    have hcik := mod_dvd_nat (hc.pair q.ik)
      (modulus_dvd_ik order q)
    have hcjk := mod_dvd_nat (hc.pair q.jk)
      (modulus_dvd_jk order q)
    exact ((((hc.tripleSecond q).add (hd.tripleSecond q)).add
      (hcjk.mul hdi)).add (hcik.mul hdj)).sub ((hck.mul hdi).mul hdj)

end GMEq

/-- The multiplicative congruence defining Theorem 2's residue coordinate
group. -/
def generalCon {t : ℕ}
    (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Con (GCoordi t) where
  r := GMEq order
  iseqv :=
    ⟨GMEq.refl order, GMEq.symm,
      GMEq.trans⟩
  mul' := GMEq.mul horder

/-- The arbitrary-rank residue coordinate group in Theorem 2. -/
abbrev GeneralResidueGroup {t : ℕ}
    (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :=
  (generalCon order horder).Quotient

/-- The explicit residue sets occurring in the arbitrary-rank equation-(18)
normal form. -/
@[ext]
structure GeneralResidues {t : ℕ} (order : Fin t → ℕ) where
  single : ∀ i : Fin t, ZMod (order i)
  pair : ∀ q : Pair t, ZMod (generalPairModulus order q)
  pairLeft : ∀ q : Pair t, ZMod (generalPairModulus order q)
  pairRight : ∀ q : Pair t, ZMod (generalPairModulus order q)
  tripleFirst :
    ∀ q : Triple t, ZMod (generalResiduesModulus order q)
  tripleSecond :
    ∀ q : Triple t, ZMod (generalResiduesModulus order q)

/-- Reduce integral arbitrary-rank coordinates modulo their prescribed
orders. -/
def generalResidueCast
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) :
    GeneralResidues order where
  single i := c.single i
  pair q := c.pair q
  pairLeft q := c.pairLeft q
  pairRight q := c.pairRight q
  tripleFirst q := c.tripleFirst q
  tripleSecond q := c.tripleSecond q

theorem general_residue_cast
    {t : ℕ} {order : Fin t → ℕ}
    {c d : GCoordi t} :
    GMEq order c d ↔
      generalResidueCast order c =
        generalResidueCast order d := by
  constructor
  · intro h
    ext i <;>
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2 <;>
      first
      | exact h.single i
      | exact h.pair i
      | exact h.pairLeft i
      | exact h.pairRight i
      | exact h.tripleFirst i
      | exact h.tripleSecond i
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.single h) i)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.pair h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.pairLeft h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.pairRight h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.tripleFirst h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun
          (congrArg GeneralResidues.tripleSecond h) q)

private noncomputable def generalResidueRepresentative
    {n : ℕ} (x : ZMod n) : ℤ :=
  Classical.choose (ZMod.intCast_surjective x)

@[simp] private theorem general_representative_cast
    {n : ℕ} (x : ZMod n) :
    (generalResidueRepresentative x : ZMod n) = x :=
  Classical.choose_spec (ZMod.intCast_surjective x)

private theorem general_cast_surjective
    {t : ℕ} (order : Fin t → ℕ) :
    Function.Surjective (generalResidueCast order) := by
  intro c
  refine ⟨{
    single := fun i => generalResidueRepresentative (c.single i)
    pair := fun q => generalResidueRepresentative (c.pair q)
    pairLeft := fun q => generalResidueRepresentative (c.pairLeft q)
    pairRight := fun q => generalResidueRepresentative (c.pairRight q)
    tripleFirst := fun q => generalResidueRepresentative (c.tripleFirst q)
    tripleSecond := fun q =>
      generalResidueRepresentative (c.tripleSecond q) }, ?_⟩
  ext <;> simp [generalResidueCast]

/-- Forget the quotient representative and retain the prescribed residue
coordinates. -/
noncomputable def generalResidueResidues
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    GeneralResidueGroup order horder →
      GeneralResidues order :=
  fun q =>
    Con.liftOn q (generalResidueCast order) fun _ _ h =>
      general_residue_cast.mp h

private theorem general_residues_bijective
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Bijective
      (generalResidueResidues order horder) := by
  constructor
  · intro q r hqr
    induction q using Con.induction_on with
    | _ c =>
      induction r using Con.induction_on with
      | _ d =>
        apply (generalCon order horder).eq.mpr
        exact general_residue_cast.mpr hqr
  · intro c
    obtain ⟨d, rfl⟩ :=
      general_cast_surjective order c
    exact
      ⟨(d : GeneralResidueGroup order horder), rfl⟩

/-- The quotient coordinate group is exactly the dependent product of
Struik's prescribed residue sets. -/
noncomputable def generalResidueEquiv
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    GeneralResidueGroup order horder ≃
      GeneralResidues order :=
  Equiv.ofBijective
    (generalResidueResidues order horder)
    (general_residues_bijective order horder)

end P1960
end Struik
