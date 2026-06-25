import Submission.ClassField.Characters.DedekindAnalyticConsequences
import Submission.ClassField.DirichletDensity.DirichletDensity

/-!
# Chapter V, Section 2, Theorem 2.5 (source statement)

The theorem concerns Dirichlet density of prime ideals in one ray class.
Here Dirichlet density is expressed by the normalized reciprocal-prime-ideal
sum used immediately before Theorem 2.5 in the source.  No natural-density
or mere infinitude assertion is substituted for it.
-/

namespace Submission.CField.Charac

open Filter IsDedekindDomain NumberField Set Topology
open Submission.CField.RCGroups
open scoped nonZeroDivisors

noncomputable section

universe u

/-- The ray class of a prime ideal away from the finite support of `m`. -/
def idealRayClass
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ m.finiteSupport) : StatementsRayGroup K m :=
  rayIntegralIdeal
    { ideal := p.asIdeal
      ne_zero := p.ne_bot
      primeTo := by
        intro q hq
        exact FractionalIdeal.count_maximal_coprime K q fun hpq ↦
          hp (hpq ▸ hq) }

theorem ray_proof_irrel
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (p : HeightOneSpectrum (𝓞 K))
    (hp h'p : p ∉ m.finiteSupport) :
    idealRayClass K m p hp =
      idealRayClass K m p h'p := by
  congr

/-- Prime ideals away from `m` whose ray class is the class of `a`. -/
def idealsRayClass
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (a : IIPrime K m) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ hp : p ∉ m.finiteSupport,
    idealRayClass K m p hp =
      rayIntegralIdeal a}

theorem prime_ideals_ray
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (a : IIPrime K m)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ idealsRayClass K m a ↔
      ∃ hp : p ∉ m.finiteSupport,
        idealRayClass K m p hp =
          rayIntegralIdeal a :=
  Iff.rfl

/-- The ray class number `h_m`.  Mathematically this quotient is finite; the
definition itself does not add a finiteness hypothesis absent from the
source theorem. -/
def rayClassNumber
    (K : Type u) [Field K] [NumberField K] (m : Modulus K) : ℕ :=
  Nat.card (StatementsRayGroup K m)

/-- Ratio-limit Dirichlet density used in Chapter V, Section 2. -/
def DirichletDensityRatio
    (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦
      Submission.CField.DDensit.primeReciprocalSum
        K T s /
        Real.log (1 / (s - 1)))
    (𝓝[>] 1) (𝓝 δ)

/-- The parallel formulation using the bounded-difference convention from
Chapter VI, Section 4.  It is kept separate from the ratio-limit statement
above because identifying the two conventions is itself an analytic fact. -/
def AnalyticDensityStatement
    (K : Type u) [Field K] [NumberField K] (m : Modulus K) : Prop :=
  ∀ a : IIPrime K m,
    Submission.CField.DDensit.PrimeDirichletDensity
      K (idealsRayClass K m a)
      ((1 : ℝ) / rayClassNumber K m)

/-- The exact bridge between the ratio-limit convention in Chapter V and
the bounded-difference convention packaged in Chapter VI. -/
def DirichletConventionBridge
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ),
    DirichletDensityRatio K T δ ↔
      Submission.CField.DDensit.PrimeDirichletDensity
        K T δ

theorem ratio_analytic_convention
    (K : Type u) [Field K] [NumberField K] (m : Modulus K)
    (hbridge : DirichletConventionBridge K) :
    (∀ a : IIPrime K m,
          DirichletDensityRatio K
            (idealsRayClass K m a)
            ((1 : ℝ) / rayClassNumber K m)
    ) ↔
      AnalyticDensityStatement K m := by
  constructor <;> intro h a
  · exact (hbridge _ _).mp (h a)
  · exact (hbridge _ _).mpr (h a)

/-- The prime-ideal locus depends only on the ray class of the chosen
integral ideal representative. -/
theorem ideals_ray_class
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (a b : IIPrime K m)
    (hab : rayIntegralIdeal a =
      rayIntegralIdeal b) :
    idealsRayClass K m a = idealsRayClass K m b := by
  ext p
  simp only [idealsRayClass, mem_setOf_eq]
  constructor
  · rintro ⟨hp, hpa⟩
    exact ⟨hp, hpa.trans hab⟩
  · rintro ⟨hp, hpb⟩
    exact ⟨hp, hpb.trans hab.symm⟩

/-- Consequently, the density assertion is independent of the chosen
integral representative of a ray class. -/
theorem ray_class_density
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (a b : IIPrime K m)
    (hab : rayIntegralIdeal a =
      rayIntegralIdeal b) :
    DirichletDensityRatio K
        (idealsRayClass K m a)
        ((1 : ℝ) / rayClassNumber K m) ↔
      DirichletDensityRatio K
        (idealsRayClass K m b)
        ((1 : ℝ) / rayClassNumber K m) := by
  rw [ideals_ray_class K m a b hab]

/-- The representative-free version of the prime locus. -/
def idealsRayValue
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (c : StatementsRayGroup K m) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ hp : p ∉ m.finiteSupport,
    idealRayClass K m p hp = c}

theorem ideals_ray_value
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (a : IIPrime K m) :
    idealsRayClass K m a =
      idealsRayValue K m
        (rayIntegralIdeal a) :=
  rfl

/-- The representative-free density theorem implies the literal
ideal-representative formulation without any further hypothesis. -/
theorem all_ray_values
    (K : Type u) [Field K] [NumberField K] (m : Modulus K)
    (h : ∀ c : StatementsRayGroup K m,
      DirichletDensityRatio K
        (idealsRayValue K m c)
        ((1 : ℝ) / rayClassNumber K m)) :
    (
      ∀ a : IIPrime K m,
          DirichletDensityRatio K
            (idealsRayClass K m a)
            ((1 : ℝ) / rayClassNumber K m)) := by
  intro a
  rw [ideals_ray_value]
  exact h _

/-- Conversely, the literal theorem gives the representative-free statement
for every ray class once integral representatives are available.  This
separates the algebraic representative issue from the analytic density
theorem. -/
theorem all_values_representatives
    (K : Type u) [Field K] [NumberField K] (m : Modulus K)
    (hrep : ∀ c : StatementsRayGroup K m,
      ∃ a : IIPrime K m,
        rayIntegralIdeal a = c)
    (h25 : (∀ a : IIPrime K m,
          DirichletDensityRatio K
            (idealsRayClass K m a)
            ((1 : ℝ) / rayClassNumber K m))) :
    ∀ c : StatementsRayGroup K m,
      DirichletDensityRatio K
        (idealsRayValue K m c)
        ((1 : ℝ) / rayClassNumber K m) := by
  intro c
  obtain ⟨a, ha⟩ := hrep c
  rw [← ha, ← ideals_ray_value]
  exact h25 a

end

end Submission.CField.Charac
