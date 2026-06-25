import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Milne, Chapter 8, Proposition 8.11

The decomposition and inertia fields separate splitting, residue degree, and
ramification.  This file proves the ideal-theoretic assertions in Proposition
8.11 and records the associated degree identities from Mathlib's
Hilbert-theory API.
-/

namespace Submission.NumberTheory.Milne

open Module Ideal MulAction Pointwise

noncomputable section

section SubgroupEquivalences

variable {B G : Type*} [CommRing B]
  [Group G] [MulSemiringAction G B]

/-- Computing inertia inside the decomposition subgroup gives the original
inertia subgroup. -/
private def inertiaStabilizerEquiv (P : Ideal B) :
    inertia (stabilizer G P) P ≃* inertia G P where
  toFun σ := ⟨σ.1.1, σ.2⟩
  invFun σ := ⟨⟨σ.1, inertia_le_stabilizer P σ.2⟩, σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Computing inertia inside the inertia subgroup gives the whole inertia
subgroup. -/
private def inertiaInertiaEquiv (P : Ideal B) :
    inertia (inertia G P) P ≃* inertia G P where
  toFun σ := σ.1
  invFun σ := ⟨σ, σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Every element of the decomposition subgroup stabilizes the prime. -/
private def stabilizerStabilizerEquiv (P : Ideal B) :
    stabilizer (stabilizer G P) P ≃* stabilizer G P where
  toFun σ := σ.1
  invFun σ := ⟨σ, σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Every element of the inertia subgroup stabilizes the prime. -/
private def stabilizerInertiaEquiv (P : Ideal B) :
    stabilizer (inertia G P) P ≃* inertia G P where
  toFun σ := σ.1
  invFun σ := ⟨σ, inertia_le_stabilizer P σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end SubgroupEquivalences

section UniquePrime

variable {C B G : Type*} [CommRing C] [CommRing B] [Algebra C B]
  [Group G] [Finite G] [MulSemiringAction G B]

/-- Milne, Proposition 8.11(a): if the Galois group over the contracted
base is the stabilizer of `P`, then `P` is the only prime above its
contraction. -/
theorem decomposition_unique_prime
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [IsGaloisGroup (stabilizer G P) C B]
    [Q.LiesOver (P.under C)] : Q = P := by
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup
      (P.under C) P Q (stabilizer G P)
  change (σ : G) • P = Q at hσ
  rw [mem_stabilizer_iff.mp σ.2] at hσ
  exact hσ.symm

end UniquePrime

section DecompositionToInertia

variable {A C E B G : Type*}
  [CommRing A] [CommRing C] [CommRing E] [CommRing B]
  [Algebra A B] [Algebra C E] [Algebra E B] [Algebra C B]
  [IsScalarTower C E B]
  [Group G] [Finite G] [MulSemiringAction G B]
  {p : Ideal A} (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
  [IsGaloisGroup G A B]
  [IsGaloisGroup (stabilizer G P) C B]
  [IsGaloisGroup (inertia G P) E B]
  [IsDedekindDomain A] [IsDedekindDomain C]
  [IsDedekindDomain E] [IsDedekindDomain B]
  [Module.Finite A B] [Module.Finite C B] [Module.Finite E B]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree C E]
  [Module.IsTorsionFree E B] [Module.IsTorsionFree C B]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (C ⧸ P.under C) (B ⧸ P)]
  [Algebra.IsSeparable (E ⧸ P.under E) (B ⧸ P)]

include G in
/-- The numerical content of Milne, Proposition 8.11(b): the prime of the
decomposition ring has ramification index one in the inertia ring, and the
residue degree of that step is the original residue degree. -/
theorem decomposition_ramification_deg
    (hp : p ≠ ⊥) (hPD : P.under C ≠ ⊥) (hPI : P.under E ≠ ⊥) :
    (P.under C).ramificationIdx (P.under E) = 1 ∧
      (P.under C).inertiaDeg (P.under E) = p.inertiaDeg P := by
  let PD : Ideal C := P.under C
  let PI : Ideal E := P.under E
  letI : p.IsMaximal :=
    (show p.IsPrime from P.over_def p ▸ Ideal.IsPrime.under A P).isMaximal hp
  letI : PD.IsMaximal :=
    (show PD.IsPrime from Ideal.IsPrime.under C P).isMaximal hPD
  letI : PI.IsMaximal :=
    (show PI.IsPrime from Ideal.IsPrime.under E P).isMaximal hPI
  have heOrigNe : p.ramificationIdx P ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  have hcardI : Nat.card (inertia G P) = p.ramificationIdx P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p hp P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P G]
  have heD : PD.ramificationIdx P = p.ramificationIdx P := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx PD P (stabilizer G P),
      ← Ideal.card_inertia_eq_ramificationIdxIn
        (G := stabilizer G P) PD hPD P,
      Nat.card_congr (inertiaStabilizerEquiv (G := G) P).toEquiv]
    exact hcardI
  have heI : PI.ramificationIdx P = p.ramificationIdx P := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx PI P (inertia G P),
      ← Ideal.card_inertia_eq_ramificationIdxIn
        (G := inertia G P) PI hPI P]
    rw [show Nat.card (inertia (inertia G P) P) = Nat.card (inertia G P) from
      Nat.card_congr (inertiaInertiaEquiv (G := G) P).toEquiv]
    exact hcardI
  have heTower := Ideal.ramificationIdx_algebra_tower' PD PI P
  have heMiddle : PD.ramificationIdx PI = 1 := by
    rw [heD, heI] at heTower
    apply mul_right_cancel₀ heOrigNe
    simpa using heTower.symm
  refine ⟨heMiddle, ?_⟩
  have hcardD := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := stabilizer G P) PD P
  have hcardOrig := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := G) p P
  have hstabDCard :
      Nat.card (stabilizer (stabilizer G P) P) =
        Nat.card (stabilizer G P) :=
    Nat.card_congr (stabilizerStabilizerEquiv (G := G) P).toEquiv
  have hinDCard :
      Nat.card (inertia (stabilizer G P) P) = Nat.card (inertia G P) :=
    Nat.card_congr (inertiaStabilizerEquiv (G := G) P).toEquiv
  have hcardD' : Nat.card (stabilizer G P) =
      Nat.card (inertia G P) * Module.finrank (C ⧸ PD) (B ⧸ P) := by
    calc
      _ = Nat.card (stabilizer (stabilizer G P) P) := hstabDCard.symm
      _ = Nat.card (inertia (stabilizer G P) P) *
          Module.finrank (C ⧸ PD) (B ⧸ P) := hcardD
      _ = _ := congrArg (· * Module.finrank (C ⧸ PD) (B ⧸ P)) hinDCard
  have hfD : PD.inertiaDeg P = p.inertiaDeg P := by
    rw [Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap]
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := inertia G P))
    exact hcardD'.symm.trans hcardOrig
  have hcardI' := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := inertia G P) PI P
  have hstabICard :
      Nat.card (stabilizer (inertia G P) P) = Nat.card (inertia G P) :=
    Nat.card_congr (stabilizerInertiaEquiv (G := G) P).toEquiv
  have hinICard :
      Nat.card (inertia (inertia G P) P) = Nat.card (inertia G P) :=
    Nat.card_congr (inertiaInertiaEquiv (G := G) P).toEquiv
  have hcardI'' : Nat.card (inertia G P) =
      Nat.card (inertia G P) * Module.finrank (E ⧸ PI) (B ⧸ P) := by
    calc
      _ = Nat.card (stabilizer (inertia G P) P) := hstabICard.symm
      _ = Nat.card (inertia (inertia G P) P) *
          Module.finrank (E ⧸ PI) (B ⧸ P) := hcardI'
      _ = _ := congrArg (· * Module.finrank (E ⧸ PI) (B ⧸ P)) hinICard
  have hfI : PI.inertiaDeg P = 1 := by
    rw [Ideal.inertiaDeg_algebraMap]
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := inertia G P))
    simpa using hcardI''.symm
  have hfTower := Ideal.inertiaDeg_algebra_tower PD PI P
  rw [hfD, hfI, mul_one] at hfTower
  exact hfTower.symm

include G in
/-- Milne, Proposition 8.11(b): the decomposition prime is unramified in
the inertia ring, and its residue degree is the original residue degree. -/
theorem decomposition_unramified_deg
    [Module.Finite C E] [Module.Finite ℤ C] [CharZero C]
    (hp : p ≠ ⊥) (hPD : P.under C ≠ ⊥) (hPI : P.under E ≠ ⊥) :
    Algebra.IsUnramifiedAt C (P.under E) ∧
      (P.under C).inertiaDeg (P.under E) = p.inertiaDeg P := by
  have h := decomposition_ramification_deg
    (G := G) P hp hPD hPI
  refine ⟨?_, h.2⟩
  apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
    (R := C) (S := E) (p := P.under E) hPI).2
  simpa only [Ideal.under_under] using h.1

end DecompositionToInertia

section InertiaToTop

variable {A E B G : Type*}
  [CommRing A] [IsDedekindDomain A]
  [CommRing E] [IsDedekindDomain E]
  [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra E B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Module.Finite E B] [Module.IsTorsionFree E B]
  [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]
  {p : Ideal A} {q : Ideal E} (P : Ideal B)
  [p.IsMaximal] [q.IsMaximal] [P.IsMaximal]
  [P.LiesOver p] [P.LiesOver q]
  [IsGaloisGroup (P.inertia G) E B]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [Algebra.IsSeparable (E ⧸ q) (B ⧸ P)]

include G

omit [IsDedekindDomain E] [IsDedekindDomain B]
  [Module.Finite E B] [Module.IsTorsionFree E B]
  [q.IsMaximal] [Algebra.IsSeparable (E ⧸ q) (B ⧸ P)] in
/-- Milne, Proposition 8.11(c): the inertia prime has a unique prime above
it in the top ring. -/
theorem inertia_unique_prime
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver q] : Q = P := by
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup q P Q (P.inertia G)
  change (σ : G) • P = Q at hσ
  rw [mem_stabilizer_iff.mp (inertia_le_stabilizer P σ.2)] at hσ
  exact hσ.symm

omit [IsDedekindDomain E] [IsDedekindDomain B]
  [Module.Finite E B] [Module.IsTorsionFree E B] in
/-- Milne, Proposition 8.11(c): the residue degree above the inertia prime
is one. -/
theorem inertia_deg_one : q.inertiaDeg P = 1 := by
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := P.inertia G) q P
  have hstabCard :
      Nat.card (stabilizer (P.inertia G) P) = Nat.card (P.inertia G) :=
    Nat.card_congr (stabilizerInertiaEquiv (G := G) P).toEquiv
  have hinertiaCard :
      Nat.card (P.inertia (P.inertia G)) = Nat.card (P.inertia G) :=
    Nat.card_congr (inertiaInertiaEquiv (G := G) P).toEquiv
  have hcard' : Nat.card (P.inertia G) =
      Nat.card (P.inertia G) * finrank (E ⧸ q) (B ⧸ P) := by
    calc
      Nat.card (P.inertia G) = Nat.card (stabilizer (P.inertia G) P) :=
        hstabCard.symm
      _ = Nat.card (P.inertia (P.inertia G)) * finrank (E ⧸ q) (B ⧸ P) :=
        hcard
      _ = Nat.card (P.inertia G) * finrank (E ⧸ q) (B ⧸ P) :=
        congrArg (· * finrank (E ⧸ q) (B ⧸ P)) hinertiaCard
  rw [Ideal.inertiaDeg_algebraMap]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := inertia G P))
  simpa using hcard'.symm

omit [p.IsMaximal] [q.IsMaximal] in
/-- Milne, Proposition 8.11(c): all of the original ramification index
occurs above the inertia prime. -/
theorem inertia_field_idx
    (hp : p ≠ ⊥) (hq : q ≠ ⊥) :
    q.ramificationIdx P = p.ramificationIdx P := by
  calc
    q.ramificationIdx P = q.ramificationIdxIn B :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx q P (P.inertia G)).symm
    _ = Nat.card (P.inertia (P.inertia G)) :=
      (Ideal.card_inertia_eq_ramificationIdxIn q hq P).symm
    _ = Nat.card (P.inertia G) :=
      Nat.card_congr (inertiaInertiaEquiv (G := G) P).toEquiv
    _ = p.ramificationIdxIn B :=
      Ideal.card_inertia_eq_ramificationIdxIn p hp P
    _ = p.ramificationIdx P :=
      Ideal.ramificationIdxIn_eq_ramificationIdx p P G

end InertiaToTop

section CompleteSplitting

variable {A B G : Type*}
  [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]

/-- Complete splitting expressed as an ideal factorization.  Applied to
`L^D/K` when `D(P)` is normal, this is Milne, Proposition 8.11(d). -/
theorem primes_stabilizer_bot
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B)
    [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (hstab : stabilizer G P = ⊥) :
    Ideal.map (algebraMap A B) p = ∏ Q : p.primesOver B, Q.1 := by
  have hinertia : P.inertia G = ⊥ := by
    apply le_bot_iff.mp
    rw [← hstab]
    exact inertia_le_stabilizer P
  have he : p.ramificationIdxIn B = 1 := by
    rw [← card_inertia_eq_ramificationIdxIn (G := G) p hp P, hinertia]
    simp
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp]
  calc
    ∏ Q ∈ (p.primesOver B).toFinset, Q ^ p.ramificationIdx Q =
        ∏ Q ∈ (p.primesOver B).toFinset, Q := by
      apply Finset.prod_congr rfl
      intro Q hQ
      have hQ' : Q ∈ p.primesOver B := Set.mem_toFinset.mp hQ
      letI : Q.IsPrime := hQ'.1
      letI : Q.LiesOver p := hQ'.2
      rw [← ramificationIdxIn_eq_ramificationIdx p Q G, he, pow_one]
    _ = ∏ Q : p.primesOver B, Q.1 :=
      (Finset.prod_set_coe (p.primesOver B)).symm

/-- If a prime has trivial decomposition group, the Galois group indexes
the primes above its contraction. -/
noncomputable def primesStabilizerBot
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (hstab : stabilizer G P = ⊥) :
    G ≃ p.primesOver B :=
  QuotientGroup.quotientBot.toEquiv.symm |>.trans
    (Subgroup.quotientEquivOfEq hstab.symm) |>.trans
    (orbitEquivQuotientStabilizer G P).symm |>.trans
    (Equiv.setCongr (Algebra.IsInvariant.orbit_eq_primesOver A B G p P))

omit [IsDedekindDomain A] [IsDedekindDomain B] [Algebra.IsIntegral A B]
  [Module.Finite A B] [Module.IsTorsionFree A B] in
@[simp]
theorem equiv_stabilizer_bot
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (hstab : stabilizer G P = ⊥) (g : G) :
    (primesStabilizerBot p P hstab g : Ideal B) = g • P := by
  rfl

/-- Complete splitting with the factors explicitly indexed by Galois
conjugates.  This is the displayed factorization in Proposition 8.11(d)
for the quotient extension by a normal decomposition group. -/
theorem smul_stabilizer_bot
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B)
    [Fintype G] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (hstab : stabilizer G P = ⊥) :
    Ideal.map (algebraMap A B) p = ∏ g : G, g • P := by
  rw [primes_stabilizer_bot p hp P hstab]
  symm
  exact Fintype.prod_equiv
    (primesStabilizerBot p P hstab)
    (fun g : G ↦ g • P) (fun Q : p.primesOver B ↦ Q.1)
    (fun g ↦ by simp)

end CompleteSplitting

variable (A K L : Type*) {B : Type*}
  [Field K] [Field L] [Algebra K L]
  [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A} (P : Ideal B) [P.LiesOver p]
  [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B]
  [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Ring.HasFiniteQuotients A] [P.IsMaximal]

section DecompositionField

variable (D : Type*) [Field D] [Algebra D L]
  [IsDecompositionField K L P D]

include K P

/-- The extension above the decomposition field has degree `e f`. -/
theorem decomposition_top_degree (hp : p ≠ ⊥) :
    finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B :=
  IsDecompositionField.rank_left A K L P D hp

/-- The decomposition field has degree equal to the number of primes above
the base prime, the degree identity associated with the splitting part of
Proposition 8.11. -/
theorem decomposition_base_degree [IsGalois K L]
    [Algebra K D] [IsScalarTower K D L] (hp : p ≠ ⊥) :
    finrank K D = (p.primesOver B).ncard :=
  IsDecompositionField.rank_right A K L P D hp

end DecompositionField

section InertiaField

variable (E : Type*) [Field E] [Algebra E L]
  [IsInertiaField K L P E]

include K P

/-- The degree of the extension above the inertia field is the ramification
index, the numerical consequence of the total-ramification claim in
Proposition 8.11(c). -/
theorem inertia_top_degree (hp : p ≠ ⊥) :
    finrank E L = p.ramificationIdxIn B :=
  IsInertiaField.rank_left A K L P E hp

/-- The degree identity combining the splitting and residue-degree parts
below the inertia field. -/
theorem inertia_base_degree [IsGalois K L]
    [Algebra K E] [IsScalarTower K E L] (hp : p ≠ ⊥) :
    finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B :=
  IsInertiaField.rank_right A K L P E hp

end InertiaField

section Tower

variable (D E : Type*) [Field D] [Field E]
  [Algebra D L] [Algebra E L]
  [IsDecompositionField K L P D] [IsInertiaField K L P E]
  [IsGalois K L] [Algebra K D] [Algebra K E] [Algebra D E]
  [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L]

include K L P

/-- The inertia field over the decomposition field has degree equal to the
residue degree. -/
theorem inertia_decomposition_degree (hp : p ≠ ⊥) :
    finrank D E = p.inertiaDegIn B :=
  IsInertiaField.rank_decompositionField A K L P D E hp

end Tower

end

end Submission.NumberTheory.Milne
