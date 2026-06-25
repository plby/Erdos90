import Mathlib.GroupTheory.Congruence.Defs
import Submission.Group.NilpotentProducts.RankThreeLaw
import Submission.Group.NilpotentProducts.AdmissibleOrders


/-!
# Struik (1960), equation (18) modulo the prescribed orders

This file formalizes the well-definedness assertion following equation (18).
The three generators are reduced modulo their orders, weight-two and repeated
weight-three commutators modulo the corresponding pairwise gcd, and the two
mixed weight-three commutators modulo the three-way gcd.
-/

namespace Struik
namespace P1960

open RLCoordi

/-- The modulus attached to a commutator involving generators `1` and `2`. -/
abbrev modulus12 (α₁ α₂ : ℕ) : ℕ :=
  Nat.gcd α₁ α₂

/-- The modulus attached to a commutator involving generators `1` and `3`. -/
abbrev modulus13 (α₁ α₃ : ℕ) : ℕ :=
  Nat.gcd α₁ α₃

/-- The modulus attached to a commutator involving generators `2` and `3`. -/
abbrev modulus23 (α₂ α₃ : ℕ) : ℕ :=
  Nat.gcd α₂ α₃

/-- The modulus attached to a weight-three commutator involving all three
generators. -/
abbrev modulus123 (α₁ α₂ α₃ : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd α₁ α₂) α₃

private lemma modulus_123_one (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ α₁ :=
  (Nat.gcd_dvd_left (Nat.gcd α₁ α₂) α₃).trans (Nat.gcd_dvd_left α₁ α₂)

private lemma modulus_123_two (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ α₂ :=
  (Nat.gcd_dvd_left (Nat.gcd α₁ α₂) α₃).trans (Nat.gcd_dvd_right α₁ α₂)

private lemma modulus_123_dvd (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ α₃ :=
  Nat.gcd_dvd_right (Nat.gcd α₁ α₂) α₃

private lemma modulus_123_12 (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ modulus12 α₁ α₂ :=
  Nat.gcd_dvd_left (Nat.gcd α₁ α₂) α₃

private lemma modulus_123_13 (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ modulus13 α₁ α₃ :=
  Nat.dvd_gcd (modulus_123_one α₁ α₂ α₃)
    (modulus_123_dvd α₁ α₂ α₃)

private lemma modulus_123_23 (α₁ α₂ α₃ : ℕ) :
    modulus123 α₁ α₂ α₃ ∣ modulus23 α₂ α₃ :=
  Nat.dvd_gcd (modulus_123_two α₁ α₂ α₃)
    (modulus_123_dvd α₁ α₂ α₃)

/-- Coordinatewise congruence modulo the orders prescribed in Theorem 1. -/
structure RRMod (α₁ α₂ α₃ : ℕ)
    (c d : RLCoordi) : Prop where
  c1 : c.c1 ≡ d.c1 [ZMOD (α₁ : ℤ)]
  c2 : c.c2 ≡ d.c2 [ZMOD (α₂ : ℤ)]
  c3 : c.c3 ≡ d.c3 [ZMOD (α₃ : ℤ)]
  c12 : c.c12 ≡ d.c12 [ZMOD (modulus12 α₁ α₂ : ℤ)]
  c13 : c.c13 ≡ d.c13 [ZMOD (modulus13 α₁ α₃ : ℤ)]
  c23 : c.c23 ≡ d.c23 [ZMOD (modulus23 α₂ α₃ : ℤ)]
  c121 : c.c121 ≡ d.c121 [ZMOD (modulus12 α₁ α₂ : ℤ)]
  c131 : c.c131 ≡ d.c131 [ZMOD (modulus13 α₁ α₃ : ℤ)]
  c232 : c.c232 ≡ d.c232 [ZMOD (modulus23 α₂ α₃ : ℤ)]
  c122 : c.c122 ≡ d.c122 [ZMOD (modulus12 α₁ α₂ : ℤ)]
  c133 : c.c133 ≡ d.c133 [ZMOD (modulus13 α₁ α₃ : ℤ)]
  c233 : c.c233 ≡ d.c233 [ZMOD (modulus23 α₂ α₃ : ℤ)]
  c123 :
    c.c123 ≡ d.c123 [ZMOD (modulus123 α₁ α₂ α₃ : ℤ)]
  c231 :
    c.c231 ≡ d.c231 [ZMOD (modulus123 α₁ α₂ α₃ : ℤ)]

namespace RRMod

theorem refl (α₁ α₂ α₃ : ℕ) (c : RLCoordi) :
    RRMod α₁ α₂ α₃ c c :=
  ⟨.refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _,
    .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩

theorem symm {α₁ α₂ α₃ : ℕ} {c d : RLCoordi}
    (h : RRMod α₁ α₂ α₃ c d) :
    RRMod α₁ α₂ α₃ d c :=
  ⟨h.c1.symm, h.c2.symm, h.c3.symm, h.c12.symm, h.c13.symm, h.c23.symm,
    h.c121.symm, h.c131.symm, h.c232.symm, h.c122.symm, h.c133.symm,
    h.c233.symm, h.c123.symm, h.c231.symm⟩

theorem trans {α₁ α₂ α₃ : ℕ} {c d e : RLCoordi}
    (hcd : RRMod α₁ α₂ α₃ c d)
    (hde : RRMod α₁ α₂ α₃ d e) :
    RRMod α₁ α₂ α₃ c e :=
  ⟨hcd.c1.trans hde.c1, hcd.c2.trans hde.c2, hcd.c3.trans hde.c3,
    hcd.c12.trans hde.c12, hcd.c13.trans hde.c13, hcd.c23.trans hde.c23,
    hcd.c121.trans hde.c121, hcd.c131.trans hde.c131,
    hcd.c232.trans hde.c232, hcd.c122.trans hde.c122,
    hcd.c133.trans hde.c133, hcd.c233.trans hde.c233,
    hcd.c123.trans hde.c123, hcd.c231.trans hde.c231⟩

private theorem mul_12
    {α₁ α₂ α₃ : ℕ} {c c' d d' : RLCoordi}
    (hc : RRMod α₁ α₂ α₃ c c')
    (hd : RRMod α₁ α₂ α₃ d d') :
    (c.c12 + d.c12 - c.c2 * d.c1) ≡
      (c'.c12 + d'.c12 - c'.c2 * d'.c1)
        [ZMOD (modulus12 α₁ α₂ : ℤ)] := by
  exact (hc.c12.add hd.c12).sub
    ((mod_dvd_nat hc.c2 (Nat.gcd_dvd_right α₁ α₂)).mul
      (mod_dvd_nat hd.c1 (Nat.gcd_dvd_left α₁ α₂)))

private theorem mul_13
    {α₁ α₂ α₃ : ℕ} {c c' d d' : RLCoordi}
    (hc : RRMod α₁ α₂ α₃ c c')
    (hd : RRMod α₁ α₂ α₃ d d') :
    (c.c13 + d.c13 - c.c3 * d.c1) ≡
      (c'.c13 + d'.c13 - c'.c3 * d'.c1)
        [ZMOD (modulus13 α₁ α₃ : ℤ)] := by
  exact (hc.c13.add hd.c13).sub
    ((mod_dvd_nat hc.c3 (Nat.gcd_dvd_right α₁ α₃)).mul
      (mod_dvd_nat hd.c1 (Nat.gcd_dvd_left α₁ α₃)))

private theorem mul_23
    {α₁ α₂ α₃ : ℕ} {c c' d d' : RLCoordi}
    (hc : RRMod α₁ α₂ α₃ c c')
    (hd : RRMod α₁ α₂ α₃ d d') :
    (c.c23 + d.c23 - c.c3 * d.c2) ≡
      (c'.c23 + d'.c23 - c'.c3 * d'.c2)
        [ZMOD (modulus23 α₂ α₃ : ℤ)] := by
  exact (hc.c23.add hd.c23).sub
    ((mod_dvd_nat hc.c3 (Nat.gcd_dvd_right α₂ α₃)).mul
      (mod_dvd_nat hd.c2 (Nat.gcd_dvd_left α₂ α₃)))

/-- Equation (18) respects all fourteen residue moduli whenever the three
generator orders are odd or zero. -/
theorem mul
    {α₁ α₂ α₃ : ℕ}
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃)
    {c c' d d' : RLCoordi}
    (hc : RRMod α₁ α₂ α₃ c c')
    (hd : RRMod α₁ α₂ α₃ d d') :
    RRMod α₁ α₂ α₃
      (RLCoordi.mul c d) (RLCoordi.mul c' d') := by
  let m12 := modulus12 α₁ α₂
  let m13 := modulus13 α₁ α₃
  let m23 := modulus23 α₂ α₃
  let m123 := modulus123 α₁ α₂ α₃
  have h1_12 := mod_dvd_nat hc.c1 (Nat.gcd_dvd_left α₁ α₂)
  have h1d_12 := mod_dvd_nat hd.c1 (Nat.gcd_dvd_left α₁ α₂)
  have h2_12 := mod_dvd_nat hc.c2 (Nat.gcd_dvd_right α₁ α₂)
  have h2d_12 := mod_dvd_nat hd.c2 (Nat.gcd_dvd_right α₁ α₂)
  have h1_13 := mod_dvd_nat hc.c1 (Nat.gcd_dvd_left α₁ α₃)
  have h1d_13 := mod_dvd_nat hd.c1 (Nat.gcd_dvd_left α₁ α₃)
  have h3_13 := mod_dvd_nat hc.c3 (Nat.gcd_dvd_right α₁ α₃)
  have h3d_13 := mod_dvd_nat hd.c3 (Nat.gcd_dvd_right α₁ α₃)
  have h2_23 := mod_dvd_nat hc.c2 (Nat.gcd_dvd_left α₂ α₃)
  have h2d_23 := mod_dvd_nat hd.c2 (Nat.gcd_dvd_left α₂ α₃)
  have h3_23 := mod_dvd_nat hc.c3 (Nat.gcd_dvd_right α₂ α₃)
  have h3d_23 := mod_dvd_nat hd.c3 (Nat.gcd_dvd_right α₂ α₃)
  have h1_123 := mod_dvd_nat hc.c1
    (modulus_123_one α₁ α₂ α₃)
  have h1d_123 := mod_dvd_nat hd.c1
    (modulus_123_one α₁ α₂ α₃)
  have h2_123 := mod_dvd_nat hc.c2
    (modulus_123_two α₁ α₂ α₃)
  have h2d_123 := mod_dvd_nat hd.c2
    (modulus_123_two α₁ α₂ α₃)
  have h3_123 := mod_dvd_nat hc.c3
    (modulus_123_dvd α₁ α₂ α₃)
  have h3d_123 := mod_dvd_nat hd.c3
    (modulus_123_dvd α₁ α₂ α₃)
  have h12_123 := mod_dvd_nat hc.c12
    (modulus_123_12 α₁ α₂ α₃)
  have h13_123 := mod_dvd_nat hc.c13
    (modulus_123_13 α₁ α₂ α₃)
  have h23_123 := mod_dvd_nat hc.c23
    (modulus_123_23 α₁ α₂ α₃)
  have hchoose1_12 :=
    choose_admissible_order (hα₁.gcd hα₂) h1d_12
  have hchoose2_12 :=
    choose_admissible_order (hα₁.gcd hα₂) h2_12
  have hchoose1_13 :=
    choose_admissible_order (hα₁.gcd hα₃) h1d_13
  have hchoose3_13 :=
    choose_admissible_order (hα₁.gcd hα₃) h3_13
  have hchoose2_23 :=
    choose_admissible_order (hα₂.gcd hα₃) h2d_23
  have hchoose3_23 :=
    choose_admissible_order (hα₂.gcd hα₃) h3_23
  refine ⟨hc.c1.add hd.c1, hc.c2.add hd.c2, hc.c3.add hd.c3,
    mul_12 hc hd, mul_13 hc hd, mul_23 hc hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hc.c121.add hd.c121).sub (h2_12.mul hchoose1_12)).add
      (hc.c12.mul h1d_12)
  · exact ((hc.c131.add hd.c131).sub (h3_13.mul hchoose1_13)).add
      (hc.c13.mul h1d_13)
  · exact ((hc.c232.add hd.c232).sub (h3_23.mul hchoose2_23)).add
      (hc.c23.mul h2d_23)
  · exact (((hc.c122.add hd.c122).sub (h1d_12.mul hchoose2_12)).add
      (hc.c12.mul h2d_12)).sub ((h1d_12.mul h2d_12).mul h2_12)
  · exact (((hc.c133.add hd.c133).sub (h1d_13.mul hchoose3_13)).add
      (hc.c13.mul h3d_13)).sub ((h1d_13.mul h3d_13).mul h3_13)
  · exact (((hc.c233.add hd.c233).sub (h2d_23.mul hchoose3_23)).add
      (hc.c23.mul h3d_23)).sub ((h2d_23.mul h3d_23).mul h3_23)
  · exact (((((hc.c123.add hd.c123).add (h13_123.mul h2d_123)).add
      (h12_123.mul h3d_123)).sub ((h1d_123.mul h2_123).mul h3_123)).sub
      ((h3_123.mul h1d_123).mul h2d_123)).sub
      ((h2_123.mul h1d_123).mul h3d_123)
  · exact (((hc.c231.add hd.c231).add (h23_123.mul h1d_123)).add
      (h13_123.mul h2d_123)).sub ((h3_123.mul h1d_123).mul h2d_123)

end RRMod

/-- The multiplicative congruence on integral equation-(18) coordinates
defined by Struik's prescribed residue ranges. -/
def rankResiduesCon
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Con RLCoordi where
  r := RRMod α₁ α₂ α₃
  iseqv :=
    ⟨RRMod.refl α₁ α₂ α₃, RRMod.symm,
      RRMod.trans⟩
  mul' := RRMod.mul hα₁ hα₂ hα₃

/-- The group of the fourteen residue coordinates in Theorem 1, with
multiplication induced by equation (18). -/
abbrev RankResiduesResidue
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :=
  (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).Quotient

/-- The fourteen explicit residue sets occurring in Theorem 1. -/
@[ext]
structure RankThreeResidues (α₁ α₂ α₃ : ℕ) where
  c1 : ZMod α₁
  c2 : ZMod α₂
  c3 : ZMod α₃
  c12 : ZMod (modulus12 α₁ α₂)
  c13 : ZMod (modulus13 α₁ α₃)
  c23 : ZMod (modulus23 α₂ α₃)
  c121 : ZMod (modulus12 α₁ α₂)
  c131 : ZMod (modulus13 α₁ α₃)
  c232 : ZMod (modulus23 α₂ α₃)
  c122 : ZMod (modulus12 α₁ α₂)
  c133 : ZMod (modulus13 α₁ α₃)
  c233 : ZMod (modulus23 α₂ α₃)
  c123 : ZMod (modulus123 α₁ α₂ α₃)
  c231 : ZMod (modulus123 α₁ α₂ α₃)

/-- Reduce an integral equation-(18) tuple into the fourteen residue sets. -/
def rankResiduesCast
    (α₁ α₂ α₃ : ℕ)
    (c : RLCoordi) :
    RankThreeResidues α₁ α₂ α₃ where
  c1 := c.c1
  c2 := c.c2
  c3 := c.c3
  c12 := c.c12
  c13 := c.c13
  c23 := c.c23
  c121 := c.c121
  c131 := c.c131
  c232 := c.c232
  c122 := c.c122
  c133 := c.c133
  c233 := c.c233
  c123 := c.c123
  c231 := c.c231

theorem rank_residues_cast
    {α₁ α₂ α₃ : ℕ} {c d : RLCoordi} :
    RRMod α₁ α₂ α₃ c d ↔
      rankResiduesCast α₁ α₂ α₃ c =
        rankResiduesCast α₁ α₂ α₃ d := by
  constructor
  · intro h
    ext <;>
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2 <;>
      first
      | exact h.c1
      | exact h.c2
      | exact h.c3
      | exact h.c12
      | exact h.c13
      | exact h.c23
      | exact h.c121
      | exact h.c131
      | exact h.c232
      | exact h.c122
      | exact h.c133
      | exact h.c233
      | exact h.c123
      | exact h.c231
  · intro h
    have h1 := congrArg RankThreeResidues.c1 h
    have h2 := congrArg RankThreeResidues.c2 h
    have h3 := congrArg RankThreeResidues.c3 h
    have h12 := congrArg RankThreeResidues.c12 h
    have h13 := congrArg RankThreeResidues.c13 h
    have h23 := congrArg RankThreeResidues.c23 h
    have h121 := congrArg RankThreeResidues.c121 h
    have h131 := congrArg RankThreeResidues.c131 h
    have h232 := congrArg RankThreeResidues.c232 h
    have h122 := congrArg RankThreeResidues.c122 h
    have h133 := congrArg RankThreeResidues.c133 h
    have h233 := congrArg RankThreeResidues.c233 h
    have h123 := congrArg RankThreeResidues.c123 h
    have h231 := congrArg RankThreeResidues.c231 h
    exact
      ⟨(ZMod.intCast_eq_intCast_iff _ _ _).1 h1,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h2,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h3,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h12,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h13,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h23,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h121,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h131,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h232,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h122,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h133,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h233,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h123,
        (ZMod.intCast_eq_intCast_iff _ _ _).1 h231⟩

private theorem rank_residues_surjective (α₁ α₂ α₃ : ℕ) :
    Function.Surjective (rankResiduesCast α₁ α₂ α₃) := by
  intro c
  obtain ⟨c1, hc1⟩ := ZMod.intCast_surjective c.c1
  obtain ⟨c2, hc2⟩ := ZMod.intCast_surjective c.c2
  obtain ⟨c3, hc3⟩ := ZMod.intCast_surjective c.c3
  obtain ⟨c12, hc12⟩ := ZMod.intCast_surjective c.c12
  obtain ⟨c13, hc13⟩ := ZMod.intCast_surjective c.c13
  obtain ⟨c23, hc23⟩ := ZMod.intCast_surjective c.c23
  obtain ⟨c121, hc121⟩ := ZMod.intCast_surjective c.c121
  obtain ⟨c131, hc131⟩ := ZMod.intCast_surjective c.c131
  obtain ⟨c232, hc232⟩ := ZMod.intCast_surjective c.c232
  obtain ⟨c122, hc122⟩ := ZMod.intCast_surjective c.c122
  obtain ⟨c133, hc133⟩ := ZMod.intCast_surjective c.c133
  obtain ⟨c233, hc233⟩ := ZMod.intCast_surjective c.c233
  obtain ⟨c123, hc123⟩ := ZMod.intCast_surjective c.c123
  obtain ⟨c231, hc231⟩ := ZMod.intCast_surjective c.c231
  refine ⟨⟨c1, c2, c3, c12, c13, c23, c121, c131, c232, c122,
    c133, c233, c123, c231⟩, ?_⟩
  ext <;> assumption

/-- Forget the quotient representative and retain its fourteen residues. -/
noncomputable def rankResiduesResidue
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃ →
      RankThreeResidues α₁ α₂ α₃ :=
  fun q =>
    Con.liftOn q (rankResiduesCast α₁ α₂ α₃) fun _c _d h =>
      rank_residues_cast.mp h

private theorem rank_residues_bijective
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Function.Bijective
      (rankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) := by
  constructor
  · intro q r hqr
    induction q using Con.induction_on with
    | _ c =>
      induction r using Con.induction_on with
      | _ d =>
        apply (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).eq.mpr
        exact rank_residues_cast.mpr hqr
  · intro c
    obtain ⟨d, rfl⟩ := rank_residues_surjective α₁ α₂ α₃ c
    exact ⟨(d : RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃), rfl⟩

/-- The quotient coordinate group has exactly the fourteen residue
coordinates specified by Struik. -/
noncomputable def rankThreeResidues
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃ ≃
      RankThreeResidues α₁ α₂ α₃ :=
  Equiv.ofBijective
    (rankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
    (rank_residues_bijective α₁ α₂ α₃ hα₁ hα₂ hα₃)

end P1960
end Struik
