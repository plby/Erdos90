import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Filtration
import Towers.NumberTheory.HigherRamification
import Towers.NumberTheory.Locals.MaximalUnramifiedExtension


/-!
# Ramification groups

This file formalizes the group-theoretic and congruence parts of Milne's
Lemma 7.57, Theorem 7.58, and Corollary 7.59.  For an ideal `P` stable under
a group action, the `i`th ramification group is the subgroup acting trivially
modulo `P ^ (i + 1)`.

Mathlib currently defines decomposition and inertia groups, but not the higher
ramification groups (the latter are explicitly listed as a TODO in
`Mathlib.RingTheory.Valuation.RamificationGroup`).
-/

namespace Towers.NumberTheory.Milne

open scoped Pointwise

section HigherRamification

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]

/-- The ideal-theoretic lower ramification filtration: `G_i` acts trivially on
`B / P^(i+1)`.  For a discrete valuation ring this is Milne's condition
`|sigma x - x| < |Pi|^i` for every integral `x`. -/
def idealRamificationGroup (P : Ideal B) (G : Type*) [Group G]
    [MulSemiringAction G B] (i : Nat) : Subgroup G :=
  (P ^ (i + 1)).inertia G

@[simp]
theorem ideal_ramification_group {P : Ideal B} {i : Nat} {sigma : G} :
    sigma ∈ idealRamificationGroup P G i ↔
      ∀ x : B, sigma • x - x ∈ P ^ (i + 1) :=
  Iff.rfl

@[simp]
theorem ideal_ramification_zero (P : Ideal B) :
    idealRamificationGroup P G 0 = P.inertia G := by
  simp [idealRamificationGroup]

/-- The ramification groups form a decreasing filtration. -/
theorem ideal_ramification_antitone (P : Ideal B) :
    Antitone (idealRamificationGroup P G) := by
  intro i j hij sigma hsigma x
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right hij 1) (hsigma x)

/-- Milne, Lemma 7.57, normality: if the prime ideal is stable under the whole
Galois group, every higher ramification group is normal. -/
theorem ideal_ramification_normal (P : Ideal B)
    (hP : ∀ sigma : G, sigma • P = P) (i : Nat) :
    (idealRamificationGroup P G i).Normal := by
  constructor
  intro sigma hsigma tau x
  have hmem : sigma • (tau⁻¹ • x) - tau⁻¹ • x ∈ P ^ (i + 1) :=
    hsigma (tau⁻¹ • x)
  have hsmul : tau • (sigma • (tau⁻¹ • x) - tau⁻¹ • x) ∈
      tau • (P ^ (i + 1)) :=
    Ideal.smul_mem_pointwise_smul tau _ _ hmem
  have hstable : tau • (P ^ (i + 1)) = P ^ (i + 1) := by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow,
      ← Ideal.pointwise_smul_def, hP]
  rw [hstable] at hsmul
  simpa [smul_sub, mul_smul] using hsmul

/-- Milne, Lemma 7.57, exhaustion in its finite-group form.  Separation says
that every nonidentity automorphism is detected modulo some power of `P`.
For a DVR this follows from the vanishing of the intersection of all powers
of its maximal ideal. -/
theorem ideal_eventually_bot [Finite G] (P : Ideal B)
    (hseparated : ∀ sigma : G, sigma ≠ 1 →
      ∃ i : Nat, sigma ∉ idealRamificationGroup P G i) :
    ∃ N : Nat, ∀ i ≥ N, idealRamificationGroup P G i = ⊥ := by
  classical
  letI := Fintype.ofFinite G
  let bound : G → Nat := fun sigma =>
    if h : sigma = 1 then 0 else Nat.find (hseparated sigma h)
  let N := Finset.univ.sup bound
  refine ⟨N, fun i hi => ?_⟩
  ext sigma
  simp only [Subgroup.mem_bot]
  constructor
  · intro hsigma
    by_contra hne
    have hbound : bound sigma ≤ N := Finset.le_sup (Finset.mem_univ sigma)
    have hmem : sigma ∈ idealRamificationGroup P G (bound sigma) :=
      ideal_ramification_antitone P (hbound.trans hi) hsigma
    have hnot : sigma ∉ idealRamificationGroup P G (bound sigma) := by
      dsimp [bound]
      rw [dif_neg hne]
      exact Nat.find_spec (hseparated sigma hne)
    exact hnot hmem
  · rintro rfl
    exact (idealRamificationGroup P G i).one_mem

/-- In a separated ideal-adic topology, a faithful finite action has trivial
higher ramification groups from some point onward.  This is the usual DVR
hypothesis used in Milne's proof of Lemma 7.57. -/
theorem eventually_i_inf
    [Finite G] [FaithfulSMul G B] (P : Ideal B)
    (hpow : (⨅ i : Nat, P ^ (i + 1)) = ⊥) :
    ∃ N : Nat, ∀ i ≥ N, idealRamificationGroup P G i = ⊥ := by
  apply ideal_eventually_bot P
  intro sigma hsigma
  have hex : ∃ x : B, sigma • x ≠ x := by
    by_contra h
    apply hsigma
    apply FaithfulSMul.eq_of_smul_eq_smul (α := B)
    intro x
    simpa using not_exists.mp h x
  obtain ⟨x, hx⟩ := hex
  by_contra h
  have hall : ∀ i : Nat, sigma • x - x ∈ P ^ (i + 1) := by
    intro i
    have hmem : sigma ∈ idealRamificationGroup P G i := by
      exact not_not.mp (not_exists.mp h i)
    exact hmem x
  have hinf : sigma • x - x ∈ ⨅ i : Nat, P ^ (i + 1) :=
    Ideal.mem_iInf.mpr hall
  rw [hpow] at hinf
  exact hx (sub_eq_zero.mp (by simpa using hinf))

/-- Milne, Lemma 7.57, exhaustion for a Noetherian local ring. Krull's intersection theorem
supplies the separation hypothesis automa, so a faithful finite action is detected modulo
some power of every proper ideal. In the valuation-ring application, the ideal is the maximal
ideal generated by a uniformizer. -/
theorem eventually_bot_ring
    [Finite G] [FaithfulSMul G B] [IsNoetherianRing B] [IsLocalRing B]
    (P : Ideal B) (hP : P ≠ ⊤) :
    ∃ N : Nat, ∀ i ≥ N, idealRamificationGroup P G i = ⊥ := by
  apply eventually_i_inf P
  apply le_antisymm
  · rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing P hP]
    refine le_iInf fun i => ?_
    cases i with
    | zero => simp
    | succ i => exact iInf_le_of_le i le_rfl
  · exact bot_le

/-- Milne, Lemma 7.57 in one statement: for a stable proper ideal in a Noetherian local ring,
the lower ramification groups are normal and eventually trivial. -/
theorem ramification_eventually_bot
    [Finite G] [FaithfulSMul G B] [IsNoetherianRing B] [IsLocalRing B]
    (P : Ideal B) (hP : P ≠ ⊤) (hstable : ∀ sigma : G, sigma • P = P) :
    (∀ i : Nat, (idealRamificationGroup P G i).Normal) ∧
      ∃ N : Nat, ∀ i ≥ N, idealRamificationGroup P G i = ⊥ := by
  exact ⟨ideal_ramification_normal P hstable,
    eventually_bot_ring P hP⟩

end HigherRamification

section Solvability

open scoped commutatorElement

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]

/-- A terminating filtration whose successive quotients are abelian gives a
solvable group.  The commutator inclusions are the subgroup-theoretic form of
the quotient embeddings in Milne's Corollary 7.59. -/
theorem solvable_commutator_filtration (F : Nat → Subgroup G)
    (hzero : F 0 = ⊤)
    (hstep : ∀ i : Nat, ⁅F i, F i⁆ ≤ F (i + 1))
    (hbot : ∃ N : Nat, F N = ⊥) : IsSolvable G := by
  obtain ⟨N, hN⟩ := hbot
  refine ⟨⟨N, le_bot_iff.mp ?_⟩⟩
  have hle : ∀ i : Nat, derivedSeries G i ≤ F i := by
    intro i
    induction i with
    | zero => simp [hzero]
    | succ i ih =>
        rw [derivedSeries_succ]
        exact (Subgroup.commutator_mono ih ih).trans (hstep i)
  exact (hle N).trans_eq hN

/-- A homomorphism from a subgroup to a commutative group detects that its
commutator subgroup lies in any prescribed subgroup containing the kernel.
This packages the kernel computations in Milne's proof of Corollary 7.59. -/
theorem commutator_abelian_detector
    {A : Type*} [CommGroup A] {H K : Subgroup G}
    (φ : H →* A)
    (hker : ∀ x : H, φ x = 1 → (x : G) ∈ K) :
    ⁅H, H⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  let xH : H := ⟨x, hx⟩
  let yH : H := ⟨y, hy⟩
  have hcomm : φ ⁅xH, yH⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  simpa [xH, yH] using hker ⁅xH, yH⁆ hcomm

/-- Milne, Corollary 7.59, solvability consequence in the ideal-theoretic
ramification filtration.  The maps `φ₀` and `φ i` abstract the injections
`G/G₀ ↪ Gal(l/k)`, `G₀/G₁ ↪ lˣ`, and `Gᵢ/Gᵢ₊₁ ↪ l`: their kernel conditions
say precisely that the corresponding successive quotients embed in
commutative groups. -/
theorem solvable_abelian_detectors
    [Finite G] [FaithfulSMul G B] [IsNoetherianRing B] [IsLocalRing B]
    (P : Ideal B) (hP : P ≠ ⊤)
    {A₀ : Type*} [CommGroup A₀] (φ₀ : G →* A₀)
    (hker₀ : ∀ σ : G, φ₀ σ = 1 → σ ∈ idealRamificationGroup P G 0)
    (A : Nat → Type*) [∀ i, CommGroup (A i)]
    (φ : ∀ i : Nat, idealRamificationGroup P G i →* A i)
    (hker : ∀ (i : Nat) (σ : idealRamificationGroup P G i),
      φ i σ = 1 → (σ : G) ∈ idealRamificationGroup P G (i + 1)) :
    IsSolvable G := by
  let F : Nat → Subgroup G
    | 0 => ⊤
    | i + 1 => idealRamificationGroup P G i
  apply solvable_commutator_filtration F
  · rfl
  · intro i
    cases i with
    | zero =>
        let φtop : (⊤ : Subgroup G) →* A₀ :=
          φ₀.comp (⊤ : Subgroup G).subtype
        have hkerTop : ∀ σ : (⊤ : Subgroup G), φtop σ = 1 →
            (σ : G) ∈ idealRamificationGroup P G 0 := by
          intro σ hσ
          exact hker₀ σ hσ
        simpa [F] using
          (commutator_abelian_detector φtop hkerTop)
    | succ i =>
        simpa [F, Nat.add_assoc] using
          (commutator_abelian_detector (φ i) (hker i))
  · obtain ⟨N, hN⟩ :=
      eventually_bot_ring (G := G) P hP
    exact ⟨N + 1, hN N le_rfl⟩

end Solvability

section UniformizerCriterion

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If `B` is generated over the fixed base ring by `Pi`, congruence of an
automorphism on `Pi` implies congruence on every element of `B`. -/
theorem inertia_adjoin_top (I : Ideal B) (Pi : B)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤) {sigma : G}
    (hPi : sigma • Pi - Pi ∈ I) :
    sigma ∈ I.inertia G := by
  intro x
  have hx : x ∈ Algebra.adjoin A ({Pi} : Set B) := by
    rw [hgen]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      simpa [Set.mem_singleton_iff.mp hy] using hPi
  | algebraMap r =>
      simp [smul_algebraMap]
  | add x y hx hy ihx ihy =>
      simpa [smul_add, add_sub_add_comm] using I.add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [smul_mul']
      rw [show sigma • x * sigma • y - x * y =
          sigma • x * (sigma • y - y) + (sigma • x - x) * y by ring]
      exact I.add_mem (I.mul_mem_left _ ihy) (I.mul_mem_right _ ihx)

/-- Milne, Theorem 7.58(b), in ideal form.  When the valuation ring is
generated over its maximal unramified subring by a uniformizer, membership in
`G_i` can be checked on that uniformizer alone. -/
theorem ideal_ramification_uniformizer (P : Ideal B) (Pi : B)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤) (i : Nat) (sigma : G) :
    sigma ∈ idealRamificationGroup P G i ↔
      sigma • Pi - Pi ∈ P ^ (i + 1) := by
  constructor
  · intro hsigma
    exact hsigma Pi
  · exact inertia_adjoin_top (P ^ (i + 1)) Pi hgen

end UniformizerCriterion

section PrincipalHigherRamificationCharacters

variable {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
  [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The coefficient `a_sigma` in
`sigma Pi = Pi + a_sigma Pi^(i+1)` for a principal maximal ideal. -/
noncomputable def principalRamificationCoefficient (Pi : B) (i : Nat)
    (sigma : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) : B :=
  Classical.choose <| (Ideal.mem_span_singleton.mp <| by
    simpa only [Ideal.span_singleton_pow] using sigma.property Pi)

omit [IsDomain B] in
theorem principal_ramification_spec (Pi : B) (i : Nat)
    (sigma : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :
    sigma.1 • Pi = Pi + principalRamificationCoefficient Pi i sigma * Pi ^ (i + 1) := by
  have h := Classical.choose_spec (Ideal.mem_span_singleton.mp <| by
    simpa only [Ideal.span_singleton_pow] using sigma.property Pi)
  dsimp [principalRamificationCoefficient]
  calc
    sigma.1 • Pi = Pi ^ (i + 1) * Classical.choose _ + Pi :=
      eq_add_of_sub_eq h
    _ = Pi + Classical.choose _ * Pi ^ (i + 1) := by ring

/-- `G_(i+1)`, regarded as a subgroup of `G_i`. -/
def idealRamificationStep (Pi : B) (i : Nat) :
    Subgroup (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :=
  (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G (i + 1)).subgroupOf
    (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i)

omit [IsDomain B] in
theorem ideal_ramification_step (Pi : B) (i : Nat)
    (sigma : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :
    sigma ∈ idealRamificationStep Pi i ↔
      (sigma : G) ∈ idealRamificationGroup (Ideal.span ({Pi} : Set B)) G (i + 1) :=
  Iff.rfl

instance ramification_step_normal (Pi : B) (i : Nat)
    [Fact (∀ sigma : G,
      sigma • Ideal.span ({Pi} : Set B) = Ideal.span ({Pi} : Set B))] :
    (idealRamificationStep (G := G) Pi i).Normal :=
  (ideal_ramification_normal (G := G) (Ideal.span ({Pi} : Set B))
    Fact.out (i + 1)).subgroupOf _

private theorem principal_ramification_mod
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (sigma tau : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :
    Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
        (principalRamificationCoefficient Pi i (sigma * tau)) =
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (principalRamificationCoefficient Pi i sigma) +
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (principalRamificationCoefficient Pi i tau) := by
  let a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i → B :=
    principalRamificationCoefficient Pi i
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  let q : B →+* B ⧸ P := Ideal.Quotient.mk P
  let u : B := 1 + a sigma * Pi ^ i
  have ha : ∀ rho, rho.1 • Pi = Pi + a rho * Pi ^ (i + 1) :=
    principal_ramification_spec Pi i
  have hfactor : sigma.1 • Pi = Pi * u := by
    rw [ha sigma]
    dsimp [u]
    rw [pow_succ]
    ring
  have heq :
      Pi + a (sigma * tau) * Pi ^ (i + 1) =
        (Pi + a sigma * Pi ^ (i + 1)) +
          (sigma.1 • a tau) * (sigma.1 • Pi) ^ (i + 1) := by
    calc
      _ = (sigma * tau).1 • Pi := (ha (sigma * tau)).symm
      _ = sigma.1 • (tau.1 • Pi) := by simp [mul_smul]
      _ = sigma.1 • (Pi + a tau * Pi ^ (i + 1)) := by rw [ha tau]
      _ = _ := by simp only [smul_add, smul_mul', smul_pow', ha sigma]
  have hcancelPi :
      a (sigma * tau) * Pi ^ (i + 1) =
        a sigma * Pi ^ (i + 1) +
          (sigma.1 • a tau) * (sigma.1 • Pi) ^ (i + 1) := by
    apply add_left_cancel (a := Pi)
    simpa [add_assoc] using heq
  have hcoeff :
      a (sigma * tau) = a sigma + (sigma.1 • a tau) * u ^ (i + 1) := by
    refine mul_right_cancel₀ (b := Pi ^ (i + 1)) (pow_ne_zero _ hPi) ?_
    rw [hfactor, mul_pow] at hcancelPi
    calc
      _ = a sigma * Pi ^ (i + 1) +
          (sigma.1 • a tau) * (Pi ^ (i + 1) * u ^ (i + 1)) := hcancelPi
      _ = _ := by ring
  have haction : q (sigma.1 • a tau) = q (a tau) := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.pow_le_self (Nat.succ_ne_zero i) (sigma.2 (a tau))
  have hqPi : q Pi = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self Pi
  have hqu : q u = 1 := by
    dsimp [u]
    simp [map_add, map_mul, map_pow, hqPi, zero_pow hi.ne']
  change q (a (sigma * tau)) = q (a sigma) + q (a tau)
  rw [hcoeff, map_add, map_mul, map_pow, haction, hqu]
  simp

/-- For `i > 0`, the uniformizer coefficient is an additive residue
character on `G_i`. -/
noncomputable def principalHigherRamification
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i) :
    idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i →*
      Multiplicative (B ⧸ Ideal.span ({Pi} : Set B)) where
  toFun sigma := Multiplicative.ofAdd <|
    Ideal.Quotient.mk _ (principalRamificationCoefficient Pi i sigma)
  map_one' := by
    change Ideal.Quotient.mk _
      (principalRamificationCoefficient (G := G) Pi i 1) = 0
    have h := principal_ramification_spec (G := G) Pi i
      (1 : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i)
    have hz : principalRamificationCoefficient (G := G) Pi i 1 * Pi ^ (i + 1) = 0 := by
      have h' : Pi = Pi +
          principalRamificationCoefficient (G := G) Pi i 1 * Pi ^ (i + 1) := by
        simpa using h
      exact add_eq_left.mp h'.symm
    have hc : principalRamificationCoefficient (G := G) Pi i 1 = 0 :=
      (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ hPi)
    simp [hc]
  map_mul' sigma tau := principal_ramification_mod Pi hPi i hi sigma tau

theorem principal_higher_ramification
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤) :
    (principalHigherRamification (G := G) Pi hPi i hi).ker =
      idealRamificationStep (G := G) Pi i := by
  ext sigma
  rw [MonoidHom.mem_ker, ideal_ramification_step]
  change Ideal.Quotient.mk _
      (principalRamificationCoefficient (G := G) Pi i sigma) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hc
    apply (ideal_ramification_uniformizer
      (A := A) (G := G) (Ideal.span ({Pi} : Set B)) Pi hgen (i + 1) sigma).2
    have hspec := principal_ramification_spec (G := G) Pi i sigma
    have hdiff : sigma.1 • Pi - Pi =
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) := by
      rw [hspec]
      ring
    rw [hdiff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases Ideal.mem_span_singleton.mp hc with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hb]
    ring
  · intro hsigma
    have hnext := hsigma Pi
    rw [Ideal.span_singleton_pow] at hnext
    change sigma.1 • Pi - Pi ∈ Ideal.span {Pi ^ (i + 1 + 1)} at hnext
    rw [Ideal.mem_span_singleton] at hnext
    rcases hnext with ⟨b, hb⟩
    have hspec := principal_ramification_spec (G := G) Pi i sigma
    have hdiff : sigma.1 • Pi - Pi =
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) := by
      rw [hspec]
      ring
    have heq :
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) =
          Pi ^ (i + 2) * b := by
      rw [← hdiff, hb]
    have hc : principalRamificationCoefficient (G := G) Pi i sigma = Pi * b := by
      apply mul_right_cancel₀ (pow_ne_zero (i + 1) hPi)
      calc
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) =
            Pi ^ (i + 2) * b := heq
        _ = (Pi * b) * Pi ^ (i + 1) := by ring
    rw [Ideal.mem_span_singleton]
    exact ⟨b, hc⟩

/-- For `i > 0`, `G_i / G_(i+1)` embeds in the additive group of the
residue ring. For a DVR maximal ideal this is its residue field. -/
theorem higher_residue_additive
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    [Fact (∀ sigma : G,
      sigma • Ideal.span ({Pi} : Set B) = Ideal.span ({Pi} : Set B))] :
    ∃ phi :
        (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i ⧸
          idealRamificationStep (G := G) Pi i) →*
            Multiplicative (B ⧸ Ideal.span ({Pi} : Set B)),
      Function.Injective phi := by
  let N := idealRamificationStep (G := G) Pi i
  let psi := principalHigherRamification (G := G) Pi hPi i hi
  have hker : psi.ker = N :=
    principal_higher_ramification (A := A) (G := G)
      Pi hPi i hi hgen
  have hN_le : N ≤ psi.ker := by rw [hker]
  refine ⟨QuotientGroup.lift N psi hN_le, ?_⟩
  exact Towers.lift_injective_ker N psi hN_le hker

private theorem principal_ratio_mod
    (Pi : B) (hPi : Pi ≠ 0)
    (sigma tau : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0) :
    Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
        (1 + principalRamificationCoefficient Pi 0 (sigma * tau)) =
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (1 + principalRamificationCoefficient Pi 0 sigma) *
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (1 + principalRamificationCoefficient Pi 0 tau) := by
  let a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 → B :=
    principalRamificationCoefficient Pi 0
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  let q : B →+* B ⧸ P := Ideal.Quotient.mk P
  let u : B := 1 + a sigma
  have ha : ∀ rho, rho.1 • Pi = Pi + a rho * Pi := by
    simpa using principal_ramification_spec (G := G) Pi 0
  have hfactor : sigma.1 • Pi = Pi * u := by
    rw [ha sigma]
    dsimp [u]
    ring
  have heq : Pi + a (sigma * tau) * Pi =
      (Pi + a sigma * Pi) + (sigma.1 • a tau) * (sigma.1 • Pi) := by
    calc
      _ = (sigma * tau).1 • Pi := (ha (sigma * tau)).symm
      _ = sigma.1 • (tau.1 • Pi) := by simp [mul_smul]
      _ = sigma.1 • (Pi + a tau * Pi) := by rw [ha tau]
      _ = _ := by simp only [smul_add, smul_mul', ha sigma]
  have hcancel : a (sigma * tau) * Pi =
      a sigma * Pi + (sigma.1 • a tau) * (sigma.1 • Pi) := by
    apply add_left_cancel (a := Pi)
    simpa [add_assoc] using heq
  have hcoeff : a (sigma * tau) = a sigma + (sigma.1 • a tau) * u := by
    apply mul_right_cancel₀ hPi
    rw [hfactor] at hcancel
    calc
      _ = a sigma * Pi + (sigma.1 • a tau) * (Pi * u) := hcancel
      _ = _ := by ring
  have haction : q (sigma.1 • a tau) = q (a tau) := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.pow_le_self (Nat.succ_ne_zero 0) (sigma.2 (a tau))
  change q (1 + a (sigma * tau)) = q (1 + a sigma) * q (1 + a tau)
  rw [hcoeff]
  simp only [map_add, map_one, map_mul, haction]
  dsimp [u]
  rw [map_add, map_one]
  ring

theorem principal_ratio_one (Pi : B) (hPi : Pi ≠ 0) :
    Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
      (1 + principalRamificationCoefficient (G := G) Pi 0
        (1 : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0)) = 1 := by
  have hspec := principal_ramification_spec (G := G) Pi 0
    (1 : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0)
  have hzero : principalRamificationCoefficient (G := G) Pi 0 1 = 0 := by
    apply mul_right_cancel₀ hPi
    have : Pi = Pi + principalRamificationCoefficient (G := G) Pi 0 1 * Pi := by
      simpa using hspec
    simpa using add_eq_left.mp this.symm
  simp [hzero]

/-- The reduction of `sigma Pi / Pi`, bundled as a residue-ring unit. -/
noncomputable def principalRatioUnit
    (Pi : B) (hPi : Pi ≠ 0)
    (sigma : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0) :
    (B ⧸ Ideal.span ({Pi} : Set B))ˣ :=
  Units.mkOfMulEqOne
    (Ideal.Quotient.mk _ (1 + principalRamificationCoefficient Pi 0 sigma))
    (Ideal.Quotient.mk _ (1 + principalRamificationCoefficient Pi 0 sigma⁻¹)) <| by
      rw [← principal_ratio_mod Pi hPi sigma sigma⁻¹]
      simpa using principal_ratio_one (G := G) Pi hPi

/-- The tame uniformizer character `G_0 → (B / (Pi))ˣ`. -/
noncomputable def principalRamificationRatio
    (Pi : B) (hPi : Pi ≠ 0) :
    idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 →*
      (B ⧸ Ideal.span ({Pi} : Set B))ˣ where
  toFun sigma := principalRatioUnit Pi hPi sigma
  map_one' := Units.ext (principal_ratio_one Pi hPi)
  map_mul' sigma tau := by
    apply Units.ext
    exact principal_ratio_mod Pi hPi sigma tau

theorem principal_ramification_step
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (sigma : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :
    principalRamificationCoefficient Pi i sigma ∈ Ideal.span ({Pi} : Set B) ↔
      sigma ∈ idealRamificationStep (G := G) Pi i := by
  rw [ideal_ramification_step]
  constructor
  · intro hc
    apply (ideal_ramification_uniformizer
      (A := A) (G := G) (Ideal.span ({Pi} : Set B)) Pi hgen (i + 1) sigma).2
    have hspec := principal_ramification_spec (G := G) Pi i sigma
    have hdiff : sigma.1 • Pi - Pi =
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) := by
      rw [hspec]
      ring
    rw [hdiff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases Ideal.mem_span_singleton.mp hc with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hb]
    ring
  · intro hsigma
    have hnext := hsigma Pi
    rw [Ideal.span_singleton_pow] at hnext
    change sigma.1 • Pi - Pi ∈ Ideal.span {Pi ^ (i + 1 + 1)} at hnext
    rw [Ideal.mem_span_singleton] at hnext
    rcases hnext with ⟨b, hb⟩
    have hspec := principal_ramification_spec (G := G) Pi i sigma
    have hdiff : sigma.1 • Pi - Pi =
        principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) := by
      rw [hspec]
      ring
    have heq : principalRamificationCoefficient (G := G) Pi i sigma * Pi ^ (i + 1) =
        Pi ^ (i + 2) * b := by
      rw [← hdiff, hb]
    have hc : principalRamificationCoefficient (G := G) Pi i sigma = Pi * b := by
      apply mul_right_cancel₀ (pow_ne_zero (i + 1) hPi)
      calc
        _ = Pi ^ (i + 2) * b := heq
        _ = (Pi * b) * Pi ^ (i + 1) := by ring
    rw [Ideal.mem_span_singleton]
    exact ⟨b, hc⟩

theorem principal_ramification_ratio
    (Pi : B) (hPi : Pi ≠ 0)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤) :
    (principalRamificationRatio (G := G) Pi hPi).ker =
      idealRamificationStep (G := G) Pi 0 := by
  ext sigma
  rw [MonoidHom.mem_ker]
  constructor
  · intro hsigma
    have hv := congrArg Units.val hsigma
    change Ideal.Quotient.mk _
      (1 + principalRamificationCoefficient (G := G) Pi 0 sigma) = 1 at hv
    rw [map_add, map_one] at hv
    have hzero : Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
        (principalRamificationCoefficient (G := G) Pi 0 sigma) = 0 := by
      simpa using add_eq_left.mp hv
    have hmem : principalRamificationCoefficient (G := G) Pi 0 sigma ∈
        Ideal.span ({Pi} : Set B) := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact (principal_ramification_step
      (A := A) (G := G) Pi hPi 0 hgen sigma).1 hmem
  · intro hsigma
    apply Units.ext
    change Ideal.Quotient.mk _
      (1 + principalRamificationCoefficient (G := G) Pi 0 sigma) = 1
    have hmem := (principal_ramification_step
      (A := A) (G := G) Pi hPi 0 hgen sigma).2 hsigma
    have hzero : Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
        (principalRamificationCoefficient (G := G) Pi 0 sigma) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simp [map_add, hzero]

/-- The tame quotient `G_0 / G_1` embeds in the units of the residue ring. -/
theorem tame_ramification_units
    (Pi : B) (hPi : Pi ≠ 0)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    [Fact (∀ sigma : G,
      sigma • Ideal.span ({Pi} : Set B) = Ideal.span ({Pi} : Set B))] :
    ∃ phi :
        (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 ⧸
          idealRamificationStep (G := G) Pi 0) →*
            (B ⧸ Ideal.span ({Pi} : Set B))ˣ,
      Function.Injective phi := by
  let N := idealRamificationStep (G := G) Pi 0
  let psi := principalRamificationRatio (G := G) Pi hPi
  have hker : psi.ker = N :=
    principal_ramification_ratio (A := A) (G := G) Pi hPi hgen
  have hN_le : N ≤ psi.ker := by rw [hker]
  refine ⟨QuotientGroup.lift N psi hN_le, ?_⟩
  exact Towers.lift_injective_ker N psi hN_le hker

end PrincipalHigherRamificationCharacters

section InertiaFixedField

open IsLocalRing

variable {K L B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing B] [MulSemiringAction Gal(L/K) B]

/-- The fixed field of the inertia group at `P`.  This is Milne's field `K₀`
in Theorem 7.58(a). -/
abbrev inertiaFixedField (P : Ideal B) : IntermediateField K L :=
  IntermediateField.fixedField (P.inertia Gal(L/K))

/-- If the prime is stable under the full Galois group, then its inertia group
is normal.  For a local extension this stability is automatic because the
valuation ring has a unique maximal ideal. -/
theorem inertia_forall_smul
    (P : Ideal B) (hstable : ∀ sigma : Gal(L/K), sigma • P = P) :
    (P.inertia Gal(L/K)).Normal := by
  rw [← ideal_ramification_zero (G := Gal(L/K)) P]
  exact ideal_ramification_normal P hstable 0

/-- Milne, Theorem 7.58(a), fixed-field assertion: the field fixed by inertia
is Galois over the base when the prime is stable under the full Galois group. -/
theorem inertia_fixed_galois
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) (hstable : ∀ sigma : Gal(L/K), sigma • P = P) :
    IsGalois K (inertiaFixedField (K := K) (L := L) P) := by
  letI : (P.inertia Gal(L/K)).Normal :=
    inertia_forall_smul P hstable
  infer_instance

/-- Milne, Theorem 7.58(a), Galois-quotient assertion: the Galois group of the
field fixed by inertia is canonically the full Galois group modulo inertia. -/
noncomputable def inertiaFixedGal
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) [hI : (P.inertia Gal(L/K)).Normal] :
    Gal(L/K) ⧸ (P.inertia Gal(L/K)) ≃*
      Gal(inertiaFixedField (K := K) (L := L) P/K) := by
  exact IsGalois.normalAutEquivQuotient (P.inertia Gal(L/K))

/-- The subgroup fixing the inertia fixed field is exactly the inertia group.
This identifies the fixed field intrinsically inside the Galois extension. -/
theorem inertia_fixed_fixing
    [FiniteDimensional K L]
    (P : Ideal B) :
    (inertiaFixedField (K := K) (L := L) P).fixingSubgroup =
      P.inertia Gal(L/K) :=
  IntermediateField.fixingSubgroup_fixedField _

/-- Every formally unramified integral stage is fixed pointwise by inertia.
This is the containment needed for the maximality assertion in Milne,
Theorem 7.58(a).  The proof uses formal unramifiedness to extend equality
modulo the maximal ideal to equality modulo all of its powers, followed by
Krull intersection in the ambient local ring. -/
theorem fraction_subalgebra_fixed
    {A : Type*} [CommRing A] [IsDomain A]
    [Algebra A B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [SMulDistribClass Gal(L/K) B L]
    [IsGaloisGroup Gal(L/K) A B]
    (U : Subalgebra A B) [Algebra.FormallyUnramified A U] :
    fractionFieldSubalgebra A B K L U ≤
      inertiaFixedField (K := K) (L := L) (maximalIdeal B) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨u, hu, rfl⟩
  change algebraMap B L u ∈
    IntermediateField.fixedField ((maximalIdeal B).inertia Gal(L/K))
  rw [IntermediateField.mem_fixedField_iff]
  intro sigma hsigma
  let g₁ : U →ₐ[A] B :=
    (MulSemiringAction.toAlgHom A B sigma).comp U.val
  let g₂ : U →ₐ[A] B := U.val
  have hpow : (⨅ i : ℕ, (maximalIdeal B) ^ i) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B)
      Ideal.IsPrime.ne_top'
  have hg : g₁ = g₂ := by
    apply Algebra.FormallyUnramified.ext_of_iInf (maximalIdeal B) hpow
    intro x
    rw [Ideal.Quotient.eq]
    exact hsigma (x : B)
  have hfix : sigma • (u : B) = u :=
    DFunLike.congr_fun hg ⟨u, hu⟩
  change sigma • algebraMap B L u = algebraMap B L u
  rw [← algebraMap.coe_smul', hfix]

/-- Milne, Theorem 7.58(a): in a finite local Galois extension, the field
generated by the maximal unramified integral stage is exactly the inertia
fixed field. -/
theorem inertia_fraction_subalgebra
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A]
    [Algebra A B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [SMulDistribClass Gal(L/K) B L]
    [IsGaloisGroup Gal(L/K) A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    inertiaFixedField (K := K) (L := L) (maximalIdeal B) =
      fractionFieldSubalgebra A B K L
        (maximalUnramifiedSubalgebra A B) := by
  let U := maximalUnramifiedSubalgebra A B
  let KU := fractionFieldSubalgebra A B K L U
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : Algebra.FormallyUnramified A U :=
    maximal_subalgebra_formally A B
  letI : IsDiscreteValuationRing U :=
    subalgebra_discrete_valuation A B
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A U)
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  let algUKU : Algebra U KU :=
    fractionIntermediateSubalgebra A B K L U
  letI : SMul U KU := algUKU.toSMul
  letI : Algebra U KU := algUKU
  letI : IsFractionRing U KU :=
    fraction_intermediate_subalgebra A B K L U
  letI : IsScalarTower A U KU := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap A L a = algebraMap B L (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B L a
  letI : Algebra U B := U.val.toRingHom.toAlgebra
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U B) :=
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral U B)).isLocalHom
        Subtype.val_injective
  let residueMap := IsScalarTower.toAlgHom (ResidueField A)
    (ResidueField U) (ResidueField B)
  let residueEquiv : ResidueField U ≃ₐ[ResidueField A]
      residueIntermediateField A B U :=
    AlgEquiv.ofInjectiveField residueMap
  have hresidueIntermediate : residueIntermediateField A B U = ⊤ := by
    change residueIntermediateField A B
      (unramifiedAdjoinIntermediate A B
        (⊤ : IntermediateField (ResidueField A) (ResidueField B))) = ⊤
    exact residue_intermediate_adjoin
      (A := A) (B := B)
      (⊤ : IntermediateField (ResidueField A) (ResidueField B))
  have hresidueDegree :
      Module.finrank (ResidueField A) (ResidueField U) =
        Module.finrank (ResidueField A) (ResidueField B) := by
    calc
      Module.finrank (ResidueField A) (ResidueField U) =
          Module.finrank (ResidueField A)
            (residueIntermediateField A B U) :=
        residueEquiv.toLinearEquiv.finrank_eq
      _ = Module.finrank (ResidueField A)
          (⊤ : IntermediateField (ResidueField A) (ResidueField B)) := by
        rw [hresidueIntermediate]
      _ = Module.finrank (ResidueField A) (ResidueField B) :=
        IntermediateField.finrank_top'
  have hKUdegree : Module.finrank K KU =
      Module.finrank (ResidueField A) (ResidueField B) := by
    have hdegree : Module.finrank K KU =
        Module.finrank (ResidueField A) (ResidueField U) := by
      letI : (maximalIdeal U).LiesOver (maximalIdeal A) := inferInstance
      letI : Algebra.IsUnramifiedAt A (maximalIdeal U) := inferInstance
      simpa using finrank_unramified_local
        (R := A) (S := U) (K := K) (L := KU) (maximalIdeal A)
          (IsDiscreteValuationRing.not_a_field A)
          (IsDiscreteValuationRing.not_a_field U)
    exact hdegree.trans hresidueDegree
  have hstab : MulAction.stabilizer Gal(L/K) (maximalIdeal B) = ⊤ :=
    stabilizer_maximal_top (R := A) (S := B) (G := Gal(L/K))
      (maximalIdeal A) (IsDiscreteValuationRing.not_a_field A)
  let K₀ := inertiaFixedField (K := K) (L := L) (maximalIdeal B)
  letI : Algebra.IsSeparable (A ⧸ maximalIdeal A)
      (B ⧸ maximalIdeal B) := by
    change Algebra.IsSeparable (ResidueField A) (ResidueField B)
    infer_instance
  have hcard : Nat.card Gal(L/K) =
      Nat.card ((maximalIdeal B).inertia Gal(L/K)) *
        Module.finrank (ResidueField A) (ResidueField B) := by
    simpa [hstab] using
      (Ideal.card_stabilizer_eq_card_inertia_mul_finrank
        (G := Gal(L/K)) (maximalIdeal A) (maximalIdeal B))
  have hindex : ((maximalIdeal B).inertia Gal(L/K)).index =
      Module.finrank (ResidueField A) (ResidueField B) := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.card_pos (α := (maximalIdeal B).inertia Gal(L/K)))
    exact ((maximalIdeal B).inertia Gal(L/K)).card_mul_index.trans hcard
  have hK₀degree : Module.finrank K K₀ =
      Module.finrank (ResidueField A) (ResidueField B) := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index K₀,
      inertia_fixed_fixing]
    exact hindex
  have hle : KU ≤ K₀ :=
    fraction_subalgebra_fixed U
  exact (IntermediateField.eq_of_le_of_finrank_eq hle
    (hKUdegree.trans hK₀degree.symm)).symm

end InertiaFixedField

section InertiaFixedFieldMaximality

open IsLocalRing

/-- Milne, Theorem 7.58(a), literal maximality assertion: the inertia fixed
field is the greatest finite unramified intermediate field.  Here
unramifiedness is the intrinsic predicate defined using the integral model
inside the integral closure, rather than a replacement field predicate. -/
theorem inertia_greatest_intermediate
    {A K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    [IsDiscreteValuationRing (integralClosure A L)]
    [HenselianLocalRing (integralClosure A L)]
    [IsLocalHom (algebraMap A (integralClosure A L))]
    [Module.Finite A (integralClosure A L)]
    [Module.IsTorsionFree A (integralClosure A L)]
    [IsFractionRing (integralClosure A L) L]
    [IsScalarTower A (integralClosure A L) L]
    [MulSemiringAction Gal(L/K) (integralClosure A L)]
    [SMulDistribClass Gal(L/K) (integralClosure A L) L]
    [IsGaloisGroup Gal(L/K) A (integralClosure A L)]
    [FiniteDimensional (ResidueField A)
      (ResidueField (integralClosure A L))]
    [Algebra.IsSeparable (ResidueField A)
      (ResidueField (integralClosure A L))] :
    IsGreatest
      {E : IntermediateField K L |
        FUInterm A K L E}
      (inertiaFixedField (K := K) (L := L)
        (maximalIdeal (integralClosure A L))) := by
  let B := integralClosure A L
  let U := maximalUnramifiedSubalgebra A B
  let F := fractionFieldSubalgebra A B K L U
  have hU : FUSubalg A B U :=
    ⟨maximal_subalgebra_finite A B,
      maximal_subalgebra_formally A B⟩
  have heq : inertiaFixedField (K := K) (L := L) (maximalIdeal B) = F :=
    inertia_fraction_subalgebra
      (A := A) (B := B) (K := K) (L := L)
  constructor
  · constructor
    · exact IntermediateField.essFiniteType_iff.mp inferInstance
    · rw [heq,
        intermediate_integral_fraction
          A K L U hU]
      exact hU
  · intro E hE
    let V := intermediateIntegralModel A K L E
    letI : Module.Finite A V := hE.2.1
    letI : Algebra.FormallyUnramified A V := hE.2.2
    rw [← fraction_intermediate_model A K L E]
    exact fraction_subalgebra_fixed V

end InertiaFixedFieldMaximality

section ResidueGaloisGroup

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]

/-- Milne, Theorem 7.58(a), quotient statement: the decomposition group
modulo inertia is the Galois group of the residue-field extension. -/
noncomputable def decompositionInertiaGal
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    MulAction.stabilizer G P ⧸
        (P.inertia G).subgroupOf (MulAction.stabilizer G P) ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P

/-- If the whole Galois group stabilizes `P`, reduction identifies the full
Galois group modulo inertia with the Galois group of the residue extension. -/
noncomputable def gal_stabilizer_top
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [hI : (P.inertia G).Normal]
    (hstab : MulAction.stabilizer G P = ⊤) :
    G ⧸ (P.inertia G) ≃* (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P := by
  let e : G ≃* MulAction.stabilizer G P :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hstab.symm)
  let f : G →* ((B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) :=
    (Ideal.Quotient.stabilizerHom P p G).comp e.toMonoidHom
  have hf_surjective : Function.Surjective f :=
    (Ideal.Quotient.stabilizerHom_surjective G p P).comp e.surjective
  have hf_ker : f.ker = P.inertia G := by
    ext sigma
    change Ideal.Quotient.stabilizerHom P p G (e sigma) = 1 ↔
      sigma ∈ P.inertia G
    rw [← MonoidHom.mem_ker, Ideal.Quotient.ker_stabilizerHom]
    rfl
  exact QuotientGroup.liftEquiv (P.inertia G) hf_surjective hf_ker.symm

/-- Milne, Theorem 7.58(a): for a stable prime, the Galois group of the
inertia fixed field is canonically the Galois group of the residue-field
extension. -/
noncomputable def inertiaGalResidue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MulSemiringAction Gal(L/K) B]
    [IsGaloisGroup Gal(L/K) A B]
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (hstable : ∀ sigma : Gal(L/K), sigma • P = P) :
    Gal(inertiaFixedField (K := K) (L := L) P/K) ≃*
      Gal((B ⧸ P)/(A ⧸ p)) := by
  have hstab : MulAction.stabilizer Gal(L/K) P = ⊤ := by
    apply top_unique
    intro sigma _
    exact MulAction.mem_stabilizer_iff.mpr (hstable sigma)
  letI : (P.inertia Gal(L/K)).Normal :=
    inertia_forall_smul P hstable
  exact (inertiaFixedGal P).symm.trans
    (gal_stabilizer_top p P hstab)

@[simp]
theorem decomposition_gal_mk
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (sigma : MulAction.stabilizer G P) :
    decompositionInertiaGal p P (QuotientGroup.mk sigma) =
      Ideal.Quotient.stabilizerHom P p G sigma :=
  rfl

omit [Finite G] in
/-- The inertia group is normal in the decomposition group, the normality
needed to form the quotient in Theorem 7.58(a). -/
lemma inertia_normal_decomposition (P : Ideal B) :
    ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).Normal :=
  inferInstance

end ResidueGaloisGroup

section CorollarySevenFiftyNine

open NumberField

noncomputable section

/-- The wild inertia subgroup is normal in inertia. This is the normality
needed to form Milne's quotient `G₀ / G₁`. -/
instance wildInertiaNormal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (Towers.number_wild_subgroup (L := L) P).Normal := by
  rw [← Towers.higher_ramification_one (L := L) P]
  exact Towers.number_higher_normal (L := L) P 1

/-- The arithmetic specialization of Milne's quotient `G₀ / G₁`. -/
abbrev numberInertiaWild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :=
  P.inertia (Gal(L/ℚ)) ⧸ Towers.number_wild_subgroup (L := L) P

/-- Milne, Corollary 7.59, tame quotient: reduction of the uniformizer
character embeds `G₀ / G₁` into the multiplicative group of the residue
field. -/
theorem number_wild_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ φ : numberInertiaWild L P →* P.ResidueFieldˣ,
      Function.Injective φ := by
  let N := Towers.number_wild_subgroup (L := L) P
  obtain ⟨χ, hχ⟩ :=
    Towers.tame_uniformizer_wild
      (L := L) hq P
  have hN_le : N ≤ χ.ker := by
    rw [hχ]
  refine ⟨QuotientGroup.lift N χ hN_le, ?_⟩
  exact Towers.lift_injective_ker N χ hN_le hχ

/-- Milne, Corollary 7.59, higher quotients: for `i ≥ 1`, the quotient
`Gᵢ / Gᵢ₊₁` embeds into the additive group of the residue field. The
`Multiplicative` wrapper lets the additive residue-field group serve as the
codomain of a multiplicative group homomorphism. -/
theorem number_higher_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (i : ℕ) (hi : 1 ≤ i) :
    ∃ φ : Towers.number_ramification_step (L := L) P i →*
        Multiplicative P.ResidueField,
      Function.Injective φ :=
  Towers.higher_ramification_additive
    (L := L) hq P i hi

/-- The inertia group at a finite prime is solvable. The wild inertia
subgroup is a finite `q`-group, while the tame quotient is detected by the
abelian group of residue-field units. -/
theorem number_inertia_solvable
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsSolvable (P.inertia (Gal(L/ℚ))) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let N := Towers.number_wild_subgroup (L := L) P
  have hNfinite : Finite N :=
    Towers.number_field_wild (L := L) hq P
  letI : Finite N := hNfinite
  have hNp : IsPGroup q N :=
    Towers.number_wild_group (L := L) hq P
  letI : Group.IsNilpotent N := IsPGroup.isNilpotent (G := N) hNp
  letI : IsSolvable N := IsNilpotent.to_isSolvable
  obtain ⟨χ, hχ⟩ :=
    Towers.tame_uniformizer_wild
      (L := L) hq P
  have hkerSolvable : IsSolvable χ.ker := by
    rw [hχ]
    infer_instance
  letI : IsSolvable χ.ker := hkerSolvable
  apply solvable_of_ker_le_range χ.ker.subtype χ
  intro σ hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

/-- Milne, Corollary 7.59, solvability conclusion in its arithmetic local
form: the decomposition group at a finite prime is solvable. Its inertia
subgroup is solvable by the ramification filtration, and its quotient is the
cyclic Galois group of the finite residue-field extension. -/
theorem decomposition_group_solvable
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsSolvable (MulAction.stabilizer (Gal(L/ℚ)) P) := by
  classical
  let D := MulAction.stabilizer (Gal(L/ℚ)) P
  let I := P.inertia (Gal(L/ℚ))
  let ID := I.subgroupOf D
  have hPmax : P.IsMaximal :=
    Towers.number_above_maximal (L := L) hq P
  letI : P.IsMaximal := hPmax
  have hIsolvable : IsSolvable I := number_inertia_solvable L hq P
  letI : IsSolvable I := hIsolvable
  have hIDsolvable : IsSolvable ID := by
    let eI : ID ≃* I :=
      Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer P)
    exact solvable_of_solvable_injective (f := eI.toMonoidHom) eI.injective
  letI : IsSolvable ID := hIDsolvable
  have hquotCyclic : IsCyclic (D ⧸ ID) := by
    simpa [D, ID, I] using
      (Towers.decomposition_inertia_cyclic (L := L) hq P)
  letI : IsCyclic (D ⧸ ID) := hquotCyclic
  letI : IsSolvable (D ⧸ ID) :=
    isSolvable_of_comm mul_comm'
  apply solvable_of_ker_le_range ID.subtype (QuotientGroup.mk' ID)
  intro σ hσ
  have hσI : σ ∈ ID := by
    simpa only [QuotientGroup.ker_mk'] using hσ
  exact ⟨⟨σ, hσI⟩, rfl⟩

/-- Milne, after Corollary 7.59: a Galois extension is unramified at a
finite prime exactly when its inertia group is trivial. -/
theorem number_inertia_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Algebra.IsUnramifiedAt ℤ P ↔ P.inertia (Gal(L/ℚ)) = ⊥ := by
  classical
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  have hp0 : Ideal.rationalPrimeIdeal q ≠ ⊥ :=
    rational_ne_bot hq
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  rw [unramified_ramification_idx
    (Ideal.rationalPrimeIdeal q) P hP0]
  have hcard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    Towers.inertia_ramification_idx (L := L) hq P
  constructor
  · intro he
    apply (P.inertia (Gal(L/ℚ))).eq_bot_of_card_eq
    rw [hcard, he]
  · intro hI
    rw [← hcard, hI, Subgroup.card_bot]

/-- Milne, after Corollary 7.59: ramification at a prime above `q` is tame
exactly when the first (wild) ramification subgroup is trivial. -/
theorem coprime_wild_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.Coprime q
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) ↔
      Towers.number_wild_subgroup (L := L) P = ⊥ := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  let I := P.inertia (Gal(L/ℚ))
  let W := Towers.number_wild_subgroup (L := L) P
  have hcard : Nat.card I =
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    Towers.inertia_ramification_idx (L := L) hq P
  have hWp : IsPGroup q W :=
    Towers.number_wild_group (L := L) hq P
  constructor
  · intro he
    have heI : Nat.Coprime q (Nat.card I) := by
      rw [hcard]
      exact he
    apply Towers.bot_coprime_card W hWp
    exact heI
  · intro hW
    obtain ⟨χ, hχ⟩ :=
      Towers.tame_uniformizer_wild
        (L := L) hq P
    have hχinj : Function.Injective χ :=
      (MonoidHom.ker_eq_bot_iff χ).mp (hχ.trans hW)
    have hdiv : Nat.card I ∣ Nat.card P.ResidueFieldˣ := by
      exact Subgroup.card_dvd_of_injective χ hχinj
    letI : CharP P.ResidueField q :=
      Towers.residue_char_p (L := L) hq P
    letI : Finite P.ResidueField :=
      Towers.number_local_residue (L := L) hq P
    letI : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
    obtain ⟨n, _hq', hncard⟩ := FiniteField.card P.ResidueField q
    have hnpos : 0 < (n : ℕ) := n.pos
    have hqpow : q ∣ q ^ (n : ℕ) := dvd_pow_self q hnpos.ne'
    have hone : 1 ≤ q ^ (n : ℕ) := Nat.one_le_pow _ _ hq.pos
    have hpowCoprime : Nat.Coprime (q ^ (n : ℕ)) (q ^ (n : ℕ) - 1) :=
      (Nat.coprime_self_sub_right hone).2 (Nat.coprime_one_right _)
    have hunits : Nat.Coprime q (Nat.card P.ResidueFieldˣ) := by
      rw [Nat.card_units, Nat.card_eq_fintype_card, hncard]
      exact hpowCoprime.of_dvd_left hqpow
    rw [← hcard]
    exact hunits.of_dvd_right hdiv

/-- Trivial inertia forces trivial wild inertia.  Here wild inertia is
defined as a subgroup of inertia, so this is the group-theoretic step from
Milne's unramified criterion to his tame criterion. -/
theorem wild_inertia_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (hI : P.inertia (Gal(L/ℚ)) = ⊥) :
    Towers.number_wild_subgroup (L := L) P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro sigma _hsigma
  apply Subtype.ext
  let tau : Gal(L/ℚ) := sigma
  have htauI : tau ∈ P.inertia (Gal(L/ℚ)) := sigma.property
  have htauBot : tau ∈ (⊥ : Subgroup Gal(L/ℚ)) := hI ▸ htauI
  have htau : tau = 1 := Subgroup.mem_bot.mp htauBot
  simpa [tau] using htau

/-- Milne, after Corollary 7.59: every unramified finite Galois number-field
extension is tamely ramified at the chosen prime. -/
theorem idx_coprime_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hunramified : Algebra.IsUnramifiedAt ℤ P) :
    Nat.Coprime q
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) := by
  apply (coprime_wild_bot
    L hq P).2
  apply wild_inertia_bot L P
  exact (number_inertia_bot L hq P).1
    hunramified

end

end CorollarySevenFiftyNine

end Towers.NumberTheory.Milne
