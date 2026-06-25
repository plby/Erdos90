import Towers.Group.Cohomology.MasseyTransgression
import Towers.Algebra.Magnus.UnitriangularMagnus
import Mathlib.LinearAlgebra.Finsupp.LinearCombination


/-!
# Magnus coefficients and transgression

This file develops the Magnus-filtration input to Efrat--Chapman, Section 9.
Degree-`n` Magnus coefficients give conjugation-invariant characters on the
`n`th Magnus subgroup and hence explicit transgression classes on its
quotient.
-/

noncomputable section

namespace EChapma
namespace MSeries
namespace MMassey

open MTransg
open scoped commutatorElement

universe u

variable {R X : Type u} [CommRing R]

/-- The Magnus-order subgroups form an antitone filtration. -/
theorem magnus_order_antitone :
    Antitone
      (magnusOrderSubgroup (R := R) (X := X)) := by
  intro m n hmn g hg
  change VanishesBelow (magnusDifference (R := R) g) m
  intro w hw
  exact hg w (hw.trans_le hmn)

/-- Every Magnus-order subgroup is normal. -/
instance magnus_order_normal
    (n : ℕ) :
    (magnusOrderSubgroup (R := R) (X := X) n).Normal := by
  constructor
  intro x hx g
  have hcommRaw :
      ⁅g, x⁆ ∈
        magnusOrderSubgroup (R := R) (X := X) (1 + n) :=
    magnus_difference_vanishes
      (magnus_vanishes_below g) hx
  have hcommSucc :
      ⁅g, x⁆ ∈
        magnusOrderSubgroup (R := R) (X := X) (n + 1) := by
    simpa [Nat.add_comm] using hcommRaw
  have hcomm :
      ⁅g, x⁆ ∈
        magnusOrderSubgroup (R := R) (X := X) n :=
    magnus_order_antitone
      (R := R) (X := X) (Nat.le_succ n) hcommSucc
  have hproduct :=
    (magnusOrderSubgroup (R := R) (X := X) n).mul_mem
      hcomm hx
  simpa [commutatorElement_def] using hproduct

/-- The degree-one exponent vector of a free-group element, with coefficients
in `R`. -/
def ringVectorHom :
    FreeGroup X →* Multiplicative (X →₀ R) :=
  FreeGroup.lift fun x =>
    Multiplicative.ofAdd (Finsupp.single x 1)

/-- The additive value of the ring-valued exponent vector. -/
def ringExponentVector (g : FreeGroup X) : X →₀ R :=
  Multiplicative.toAdd (ringVectorHom (R := R) (X := X) g)

@[simp]
theorem ring_vector_one :
    ringExponentVector (R := R) (X := X) 1 = 0 := by
  simp [ringExponentVector, ringVectorHom]

@[simp]
theorem ring_vector (x : X) :
    ringExponentVector (R := R) (FreeGroup.of x) =
      Finsupp.single x 1 := by
  simp [ringExponentVector, ringVectorHom]

@[simp]
theorem ring_exponent_vector (g h : FreeGroup X) :
    ringExponentVector (R := R) (g * h) =
      ringExponentVector (R := R) g +
        ringExponentVector (R := R) h := by
  simp [ringExponentVector, ringVectorHom]

/-- Every free-group element, regarded as an element of the order-one
Magnus subgroup. -/
def magnusOrderHom :
    FreeGroup X →*
      magnusOrderSubgroup (R := R) (X := X) 1 :=
  (MonoidHom.id (FreeGroup X)).codRestrict
    (magnusOrderSubgroup (R := R) (X := X) 1)
    (fun g => magnus_vanishes_below g)

/-- The coefficient of one degree-one word as a homomorphism on the whole
free group. -/
def degreeCoefficientHom (x : X) :
    FreeGroup X →* Multiplicative R :=
  (restrictedCoefficientHom (R := R) [x] (by simp)).comp
    (magnusOrderHom (R := R) (X := X))

/-- A coordinate of the ring exponent vector, as a multiplicative
homomorphism. -/
def ringExponentHom (x : X) :
    FreeGroup X →* Multiplicative R where
  toFun g :=
    Multiplicative.ofAdd
      (ringExponentVector (R := R) g x)
  map_one' := by simp
  map_mul' := by simp

/-- Degree-one Magnus coefficients are the coordinates of the exponent
vector. -/
theorem ring_exponent_coefficient
    (x : X) :
    ringExponentHom (R := R) x =
      degreeCoefficientHom (R := R) x := by
  apply FreeGroup.ext_hom
  intro y
  apply Multiplicative.toAdd.injective
  classical
  change
    ringExponentVector (R := R) (FreeGroup.of y) x =
      magnusSeries (R := R) (FreeGroup.of y)
        (FreeMonoid.ofList [x])
  rw [ring_vector]
  change
    (Finsupp.single y (1 : R)) x =
      magnusSeries (R := R) (FreeGroup.of y)
        (FreeMonoid.of x)
  rw [magnusSeries_of]
  rw [Finsupp.single_apply]
  by_cases hxy : x = y
  · subst y
    simp [variableSeries]
  · have hword : FreeMonoid.of x ≠ FreeMonoid.of y :=
      fun h => hxy (FreeMonoid.of_injective h)
    have hyx : y ≠ x := Ne.symm hxy
    simp [variableSeries, hword, hyx]

theorem vector_magnus_coefficient
    (g : FreeGroup X) (x : X) :
    ringExponentVector (R := R) g x =
      magnusSeries (R := R) g (FreeMonoid.of x) := by
  have h :=
    DFunLike.congr_fun
      (ring_exponent_coefficient
        (R := R) x) g
  exact congrArg Multiplicative.toAdd h

/-- Evaluation of the exponent vector against generator values. -/
def exponentVectorEvaluation (a : X → R) :
    FreeGroup X →* Multiplicative R :=
  (AddMonoidHom.toMultiplicative
      (Finsupp.linearCombination R a).toAddMonoidHom).comp
    (ringVectorHom (R := R) (X := X))

/-- Every additive character of a free group is evaluation against the
degree-one exponent vector. -/
theorem additive_vector_evaluation
    (b : Additive (FreeGroup X) →+ R) :
    AddMonoidHom.toMultiplicativeRight b =
      exponentVectorEvaluation
        (R := R)
        (fun x => b (Additive.ofMul (FreeGroup.of x))) := by
  apply FreeGroup.ext_hom
  intro x
  simp [exponentVectorEvaluation, ringVectorHom]

/-- Every additive character of the free group vanishes on Magnus order at
least two. -/
theorem additive_vanishes_magnus
    (b : Additive (FreeGroup X) →+ R)
    (g :
      magnusOrderSubgroup (R := R) (X := X) 2) :
    b (Additive.ofMul g.1) = 0 := by
  have hcoordinate :
      ∀ x,
        ringExponentVector (R := R) g.1 x = 0 := by
    intro x
    rw [vector_magnus_coefficient]
    have hdifference :=
      g.2 (FreeMonoid.of x) (by simp)
    have hone :
        (1 : MSeries R X) (FreeMonoid.of x) = 0 := by
      simp
    exact sub_eq_zero.mp hdifference |>.trans hone
  have hvector :
      ringExponentVector (R := R) g.1 = 0 := by
    ext x
    exact hcoordinate x
  have hb :=
    DFunLike.congr_fun
      (additive_vector_evaluation (R := R) b) g.1
  have hb' := congrArg Multiplicative.toAdd hb
  change
    b (Additive.ofMul g.1) =
      (Finsupp.linearCombination R
        (fun x => b (Additive.ofMul (FreeGroup.of x))))
        (ringExponentVector (R := R) g.1) at hb'
  simpa [hvector] using hb'

/-- Consequently every additive character vanishes on every Magnus subgroup
of order at least two. -/
theorem vanishes_magnus_subgroup
    {n : ℕ} (hn : 2 ≤ n)
    (b : Additive (FreeGroup X) →+ R)
    (g :
      magnusOrderSubgroup (R := R) (X := X) n) :
    b (Additive.ofMul g.1) = 0 :=
  additive_vanishes_magnus
    (R := R) b
    ⟨g.1,
      magnus_order_antitone
        (R := R) (X := X) hn g.2⟩

/-- A degree-`n` coefficient vanishes on the next Magnus subgroup. -/
theorem restricted_coefficient_succ
    (xs : List X) (hxs : 0 < xs.length)
    (g : magnusOrderSubgroup (R := R) (X := X) xs.length)
    (hg :
      g.1 ∈ magnusOrderSubgroup
        (R := R) (X := X) (xs.length + 1)) :
    MonoidHom.toAdditiveLeft
        (restrictedCoefficientHom (R := R) xs hxs)
        (Additive.ofMul g) =
      0 := by
  change
    magnusSeries (R := R) g.1 (FreeMonoid.ofList xs) = 0
  have hdifference :=
    hg (FreeMonoid.ofList xs) (by
      change xs.length < xs.length + 1
      omega)
  have hpositive :
      (1 : MSeries R X) (FreeMonoid.ofList xs) = 0 := by
    rw [one_apply]
    simp [FreeMonoid.length, hxs.ne']
  exact sub_eq_zero.mp hdifference |>.trans hpositive

/-- The degree-`n` coefficient character on the `n`th Magnus subgroup. -/
def coefficientAdditiveHom
    (xs : List X) (hxs : 0 < xs.length) :
    Additive
        (magnusOrderSubgroup
          (R := R) (X := X) xs.length) →+ R :=
  MonoidHom.toAdditiveLeft
    (restrictedCoefficientHom (R := R) xs hxs)

/-- Conjugation changes an order-`n` element by an order-`n+1`
commutator. -/
theorem conjugate_inv_magnus
    (n : ℕ)
    (g : FreeGroup X)
    (x : magnusOrderSubgroup (R := R) (X := X) n) :
    g * x.1 * g⁻¹ * x.1⁻¹ ∈
      magnusOrderSubgroup (R := R) (X := X) (n + 1) := by
  change
    VanishesBelow
      (magnusDifference
        (R := R) (g * x.1 * g⁻¹ * x.1⁻¹))
      (n + 1)
  have hcomm :
      VanishesBelow
        (magnusDifference (R := R) ⁅g, x.1⁆)
        (1 + n) :=
    magnus_difference_vanishes
      (magnus_vanishes_below g) x.2
  simpa [commutatorElement_def, Nat.add_comm] using hcomm

/-- Degree-`n` word coefficients are invariant under ambient conjugation. -/
def coefficientInvariantHom
    (xs : List X) (hxs : 0 < xs.length) :
    invariantHom (R := R)
      (magnusOrderSubgroup
        (R := R) (X := X) xs.length) := by
  let coefficient :=
    coefficientAdditiveHom (R := R) xs hxs
  refine ⟨coefficient, ?_⟩
  intro g x
  let comm :
      magnusOrderSubgroup (R := R) (X := X) xs.length :=
    ⟨g * x.1 * g⁻¹ * x.1⁻¹,
      (magnus_order_antitone
        (R := R) (X := X) (Nat.le_succ xs.length))
        (conjugate_inv_magnus
          (R := R) xs.length g x)⟩
  have hcommzero : coefficient (Additive.ofMul comm) = 0 :=
    restricted_coefficient_succ
      (R := R) xs hxs comm
      (conjugate_inv_magnus
        (R := R) xs.length g x)
  have hfactor :
      normalConjugate
          (magnusOrderSubgroup
            (R := R) (X := X) xs.length)
          g x =
        comm * x := by
    apply Subtype.ext
    dsimp [normalConjugate, comm]
    group
  rw [hfactor]
  change coefficient (Additive.ofMul (comm * x)) =
    coefficient (Additive.ofMul x)
  rw [show Additive.ofMul (comm * x) =
      Additive.ofMul comm + Additive.ofMul x by rfl,
    map_add, hcommzero, zero_add]

/-- The explicit transgression is injective on every Magnus subgroup of
order at least two. -/
theorem magnus_explicit_transgression
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
      (explicitTransgressionLinear (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n)) :=
  explicit_transgression_injective
    (R := R)
    (magnusOrderSubgroup (R := R) (X := X) n)
    (fun b g =>
      vanishes_magnus_subgroup
        (R := R) hn b g)

/-- Words of a fixed length, represented by lists. -/
abbrev DegreeWord (X : Type*) (n : ℕ) :=
  {xs : List X // xs.length = n}

/-- A defining system for an `n`-fold Massey product, using Mathlib's
inhomogeneous-cochain sign convention.  The omitted `(0,n)` entry is the
top-right entry of the corresponding unitriangular representation. -/
structure MDSystem
    (G R : Type u) [Group G] [CommRing R] (n : ℕ) where
  cochain : Fin (n + 1) → Fin (n + 1) → G → R
  defining :
    ∀ i j, i < j →
      (i ≠ 0 ∨ j ≠ Fin.last n) →
      ∀ q r,
        cochain i j r - cochain i j (q * r) + cochain i j q =
          -∑ k ∈ Finset.Ioo i j,
            cochain i k q * cochain k j r

/-- The 2-cochain represented by a Massey defining system. -/
def MDSystem.valueCochain
    {G R : Type u} [Group G] [CommRing R] {n : ℕ}
    (M : MDSystem G R n) :
    G × G → R :=
  fun qr =>
    ∑ k ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n),
      M.cochain 0 k qr.1 * M.cochain k (Fin.last n) qr.2

/-- A defining system whose value is a cocycle determines an actual class
in second group cohomology. -/
def MDSystem.valueClass
    {G R : Type u} [Group G] [CommRing R] [SMul G R]
    {n : ℕ} (M : MDSystem G R n)
    (htriv : ∀ g : G, ∀ r : R, g • r = r)
    (hM : groupCohomology.IsCocycle₂ M.valueCochain) :
    groupCohomology.H2 (Rep.trivial R G R) :=
  groupCohomology.H2π (Rep.trivial R G R)
    ⟨M.valueCochain, by
      rw [groupCohomology.mem_cocycles₂_iff]
      intro g h j
      simpa [htriv] using hM g h j⟩

/-- Values of defining systems with prescribed adjacent 1-cochains.  This
representative-level version maps into the usual Massey product of their
`H¹` classes. -/
def MasseyProductValues
    {G R : Type u} [Group G] [CommRing R] [SMul G R]
    (htriv : ∀ g : G, ∀ r : R, g • r = r)
    (n : ℕ) (a : Fin n → G → R) :
    Set (groupCohomology.H2 (Rep.trivial R G R)) :=
  {α | ∃ (M : MDSystem G R n)
      (hM : groupCohomology.IsCocycle₂ M.valueCochain),
      (∀ i, M.cochain i.castSucc i.succ = a i) ∧
        α = M.valueClass htriv hM}

/-- The word representation with its top-right entry forgotten. -/
def principalWordRepresentation
    (xs : List X) :
    FreeGroup X →*
      unitriangularIncidenceSubgroup R xs.length ×
        unitriangularIncidenceSubgroup R xs.length :=
  (principalUnitriangularRestriction (R := R) xs.length).comp
    (wordCoefficientRepresentation (R := R) xs)

/-- The projective word representation factored through the relevant
Magnus quotient. -/
def principalCoefficientRepresentation
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n) :
    (FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) →*
      unitriangularIncidenceSubgroup R n ×
        unitriangularIncidenceSubgroup R n := by
  rcases w with ⟨xs, rfl⟩
  let ρ :
      FreeGroup X →*
        unitriangularIncidenceSubgroup R xs.length ×
          unitriangularIncidenceSubgroup R xs.length :=
    principalWordRepresentation (R := R) xs
  exact QuotientGroup.lift
    (magnusOrderSubgroup (R := R) (X := X) xs.length) ρ
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      have hall :
          g ∈ barredCoefficientIntersection
            (R := R) (X := X) xs.length := by
        rw [←
          magnus_barred_intersection
            (R := R) (X := X) xs.length hn]
        exact hg
      have hw :=
        (Subgroup.mem_iInf.mp hall)
          (⟨xs, rfl⟩ : DegreeWord X xs.length)
      have hprincipal :=
        (ker_barred_representation
          (R := R) xs g).mp hw
      simpa [ρ, principalWordRepresentation] using
        hprincipal)

/-- The canonical 1-cochain obtained from an entry of the word
representation and the chosen quotient section. -/
def canonicalMasseyCochain
    {n : ℕ} (w : DegreeWord X n)
    (i j : Fin (n + 1)) :
    (FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) → R :=
  by
    rcases w with ⟨xs, rfl⟩
    exact fun q =>
      (((wordCoefficientRepresentation (R := R) xs
          (quotientSection
            (magnusOrderSubgroup
              (R := R) (X := X) xs.length) q)).1.1 :
        IncidenceAlgebra R (Fin (xs.length + 1))) i j)

/-- Away from the omitted top-right entry, the canonical cochains satisfy
the defining-system equation because the barred word representation is a
homomorphism on the Magnus quotient. -/
theorem massey_cochain_defining
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n)
    (i j : Fin (n + 1)) (hij : i < j)
    (hntop : i ≠ 0 ∨ j ≠ Fin.last n)
    (q r :
      FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) :
    canonicalMasseyCochain (R := R) w i j r -
          canonicalMasseyCochain (R := R) w i j (q * r) +
          canonicalMasseyCochain (R := R) w i j q =
      -∑ k ∈ Finset.Ioo i j,
        canonicalMasseyCochain (R := R) w i k q *
          canonicalMasseyCochain (R := R) w k j r := by
  rcases w with ⟨xs, rfl⟩
  let N :=
    magnusOrderSubgroup (R := R) (X := X) xs.length
  let sq : FreeGroup X := quotientSection N q
  let sr : FreeGroup X := quotientSection N r
  let sqr : FreeGroup X := quotientSection N (q * r)
  have hquot :
      QuotientGroup.mk' N (sq * sr) =
        QuotientGroup.mk' N sqr := by
    calc
      QuotientGroup.mk' N (sq * sr) =
          QuotientGroup.mk' N sq * QuotientGroup.mk' N sr := by
            rw [map_mul]
      _ = q * r := by
        rw [quotientSection_spec, quotientSection_spec]
      _ = QuotientGroup.mk' N sqr := by
        rw [quotientSection_spec]
  have hprincipal :
      principalWordRepresentation (R := R) xs (sq * sr) =
        principalWordRepresentation (R := R) xs sqr := by
    have h :=
      congrArg
        (principalCoefficientRepresentation
          (R := R) hn
          (⟨xs, rfl⟩ : DegreeWord X xs.length))
        hquot
    simpa [principalCoefficientRepresentation] using h
  have hentry :
      (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) =
        (((wordCoefficientRepresentation (R := R) xs (sq * sr)).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) := by
    by_cases hj : j.1 < xs.length
    · let i' : Fin xs.length := ⟨i.1, by omega⟩
      let j' : Fin xs.length := ⟨j.1, hj⟩
      have h :=
        congrArg
          (fun p =>
            ((p.1.1.1 :
                IncidenceAlgebra R (Fin xs.length)) i' j'))
          hprincipal
      change
        (((wordCoefficientRepresentation (R := R) xs (sq * sr)).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1)))
          i'.castSucc j'.castSucc) =
        (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1)))
          i'.castSucc j'.castSucc) at h
      simpa [i', j'] using h.symm
    · have hjlast : j.1 = xs.length := by omega
      have hi : 0 < i.1 := by
        rcases hntop with hi | hjne
        · have hival : i.1 ≠ 0 := by
            intro hzero
            apply hi
            apply Fin.ext
            simpa using hzero
          omega
        · exfalso
          apply hjne
          apply Fin.ext
          simp [hjlast]
      let i' : Fin xs.length := ⟨i.1 - 1, by omega⟩
      let j' : Fin xs.length := ⟨j.1 - 1, by omega⟩
      have h :=
        congrArg
          (fun p =>
            ((p.2.1.1 :
                IncidenceAlgebra R (Fin xs.length)) i' j'))
          hprincipal
      change
        (((wordCoefficientRepresentation (R := R) xs (sq * sr)).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1)))
          i'.succ j'.succ) =
        (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1)))
          i'.succ j'.succ) at h
      have hi' : i'.succ = i := by
        apply Fin.ext
        simp [i']
        omega
      have hj' : j'.succ = j := by
        apply Fin.ext
        simp [j']
        omega
      rw [hi', hj'] at h
      exact h.symm
  have hmul :=
    unitriangular_mul
      (wordCoefficientRepresentation (R := R) xs sq)
      (wordCoefficientRepresentation (R := R) xs sr)
      i j hij
  rw [← map_mul] at hmul
  change
    canonicalMasseyCochain
          (R := R) (⟨xs, rfl⟩ : DegreeWord X xs.length) i j r -
        canonicalMasseyCochain
          (R := R) (⟨xs, rfl⟩ : DegreeWord X xs.length) i j (q * r) +
        canonicalMasseyCochain
          (R := R) (⟨xs, rfl⟩ : DegreeWord X xs.length) i j q =
      -∑ k ∈ Finset.Ioo i j,
        canonicalMasseyCochain
              (R := R) (⟨xs, rfl⟩ : DegreeWord X xs.length) i k q *
          canonicalMasseyCochain
              (R := R) (⟨xs, rfl⟩ : DegreeWord X xs.length) k j r
  dsimp [canonicalMasseyCochain, sq, sr, sqr, N] at hentry hmul ⊢
  rw [hentry, hmul]
  abel

/-- The canonical defining system attached to a word. -/
def masseyDefiningSystem
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n) :
    MDSystem
      (FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) R n where
  cochain := canonicalMasseyCochain (R := R) w
  defining := massey_cochain_defining
    (R := R) hn w

/-- The invariant coefficient character belonging to a degree-`n` word. -/
def degreeInvariantHom
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    invariantHom (R := R)
      (magnusOrderSubgroup (R := R) (X := X) n) := by
  rcases w with ⟨xs, rfl⟩
  exact coefficientInvariantHom (R := R) xs hn

/-- The coboundary of a 1-cochain for a trivial action. -/
def trivialOneCoboundary
    {G A : Type u} [Group G] [AddCommGroup A]
    (a : G → A) :
    G × G → A :=
  fun qr => a qr.2 - a (qr.1 * qr.2) + a qr.1

/-- Subtracting a trivial-action coboundary from a 2-cocycle preserves the
2-cocycle equation. -/
theorem isCocycle₂_sub_trivialOneCoboundary
    {G A : Type u} [Group G] [AddCommGroup A] [SMul G A]
    (htriv : ∀ g : G, ∀ a : A, g • a = a)
    {f : G × G → A} (hf : groupCohomology.IsCocycle₂ f)
    (a : G → A) :
    groupCohomology.IsCocycle₂
      (fun qr => f qr - trivialOneCoboundary a qr) := by
  intro g h j
  rw [htriv]
  have hcocycle := hf g h j
  rw [htriv] at hcocycle
  dsimp [trivialOneCoboundary]
  calc
    f (g * h, j) - (a j - a (g * h * j) + a (g * h)) +
          (f (g, h) - (a h - a (g * h) + a g)) =
        (f (g * h, j) + f (g, h)) +
          (-a j + a (g * h * j) - a h - a g) := by
            abel
    _ =
        (f (h, j) + f (g, h * j)) +
          (-a j + a (g * h * j) - a h - a g) := by
            rw [hcocycle]
    _ =
        f (h, j) - (a j - a (h * j) + a h) +
          (f (g, h * j) -
            (a (h * j) - a (g * (h * j)) + a g)) := by
              have hassoc : g * h * j = g * (h * j) :=
                _root_.mul_assoc g h j
              rw [hassoc]
              abel

local instance magnusQuotientSMul (n : ℕ) :
    SMul
      (FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) R where
  smul _ r := r

/-- The omitted top-right entry, evaluated on the chosen quotient
representative. -/
def canonicalTopCochain
    {n : ℕ} (w : DegreeWord X n) :
    (FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) → R :=
  canonicalMasseyCochain (R := R) w 0 (Fin.last n)

/-- The factor-set transgression cochain is the coboundary of the omitted
top-right cochain plus the value cochain of the canonical defining system. -/
theorem transgression_coboundary_massey
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n)
    (q r :
      FreeGroup X ⧸
        magnusOrderSubgroup (R := R) (X := X) n) :
    transgressionCochain (R := R)
          (magnusOrderSubgroup (R := R) (X := X) n)
          (degreeInvariantHom (R := R) hn w) (q, r) =
      trivialOneCoboundary
          (canonicalTopCochain (R := R) w) (q, r) +
        (masseyDefiningSystem
          (R := R) hn w).valueCochain (q, r) := by
  rcases w with ⟨xs, rfl⟩
  let N :=
    magnusOrderSubgroup (R := R) (X := X) xs.length
  let z : N := factorSet N q r
  let sq : FreeGroup X := quotientSection N q
  let sr : FreeGroup X := quotientSection N r
  let sqr : FreeGroup X := quotientSection N (q * r)
  let i : Fin (xs.length + 1) := 0
  let j : Fin (xs.length + 1) := Fin.last xs.length
  have hij : i < j := by
    change 0 < xs.length
    exact hn
  have hfactor :
      z.1 * sqr = sq * sr := by
    dsimp [z, sq, sr, sqr, factorSet]
    group
  have hentry :=
    congrArg
      (fun g : FreeGroup X =>
        (((wordCoefficientRepresentation (R := R) xs g).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i j))
      hfactor
  change
    (((wordCoefficientRepresentation (R := R) xs (z.1 * sqr)).1.1 :
        IncidenceAlgebra R (Fin (xs.length + 1))) i j) =
      (((wordCoefficientRepresentation (R := R) xs (sq * sr)).1.1 :
        IncidenceAlgebra R (Fin (xs.length + 1))) i j) at hentry
  have hleft :=
    unitriangular_mul
      (wordCoefficientRepresentation (R := R) xs z.1)
      (wordCoefficientRepresentation (R := R) xs sqr)
      i j hij
  rw [← map_mul] at hleft
  have hright :=
    unitriangular_mul
      (wordCoefficientRepresentation (R := R) xs sq)
      (wordCoefficientRepresentation (R := R) xs sr)
      i j hij
  rw [← map_mul] at hright
  rw [hleft, hright] at hentry
  have hzsum :
      (∑ k ∈ Finset.Ioo i j,
        (((wordCoefficientRepresentation (R := R) xs z.1).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i k) *
          (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) k j)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hik : i < k := (Finset.mem_Ioo.mp hk).1
    have hkj : k < j := (Finset.mem_Ioo.mp hk).2
    have hsegmentPos :
        0 < (wordSegment xs i k).length := by
      rw [wordSegment_length xs i k hik.le]
      omega
    have hsegmentLt :
        (wordSegment xs i k).length < xs.length := by
      rw [wordSegment_length xs i k hik.le]
      have hjval : j.1 = xs.length := by
        simp [j]
      omega
    have hvanish :=
      z.2 (wordSegment xs i k) hsegmentLt
    have hone :
        (1 : MSeries R X) (wordSegment xs i k) = 0 := by
      rw [one_apply]
      simp [hsegmentPos.ne']
    have hzero :
        magnusSeries (R := R) z.1 (wordSegment xs i k) = 0 :=
      (sub_eq_zero.mp hvanish).trans hone
    rw [word_coefficient_representation xs z.1 i k hik.le,
      hzero]
    change
      (0 : R) *
          (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) k j) =
        (0 : R)
    exact
      MulZeroClass.zero_mul
        (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) k j)
  rw [hzsum, add_zero] at hentry
  have hfullSegment :
      wordSegment xs i j = FreeMonoid.ofList xs := by
    apply FreeMonoid.toList.injective
    simp [wordSegment, i, j]
  have htopZ :
      transgressionCochain (R := R) N
          (degreeInvariantHom
            (R := R) hn
            (⟨xs, rfl⟩ : DegreeWord X xs.length)) (q, r) =
        (((wordCoefficientRepresentation (R := R) xs z.1).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i j) := by
    rw [word_coefficient_representation xs z.1 i j hij.le,
      hfullSegment]
    rfl
  rw [htopZ]
  change
    (((wordCoefficientRepresentation (R := R) xs z.1).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) =
      (((wordCoefficientRepresentation (R := R) xs sr).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) -
        (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) +
        (((wordCoefficientRepresentation (R := R) xs sq).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) +
        ∑ k ∈ Finset.Ioo i j,
          (((wordCoefficientRepresentation (R := R) xs sq).1.1 :
              IncidenceAlgebra R (Fin (xs.length + 1))) i k) *
            (((wordCoefficientRepresentation (R := R) xs sr).1.1 :
              IncidenceAlgebra R (Fin (xs.length + 1))) k j)
  calc
    (((wordCoefficientRepresentation (R := R) xs z.1).1.1 :
          IncidenceAlgebra R (Fin (xs.length + 1))) i j) =
        (((wordCoefficientRepresentation (R := R) xs sq).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i j) +
          (((wordCoefficientRepresentation (R := R) xs sr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i j) +
          (∑ k ∈ Finset.Ioo i j,
            (((wordCoefficientRepresentation (R := R) xs sq).1.1 :
                IncidenceAlgebra R (Fin (xs.length + 1))) i k) *
              (((wordCoefficientRepresentation (R := R) xs sr).1.1 :
                IncidenceAlgebra R (Fin (xs.length + 1))) k j)) -
          (((wordCoefficientRepresentation (R := R) xs sqr).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1))) i j) := by
              rw [← hentry]
              abel
    _ = _ := by abel

/-- The value cochain of the canonical defining system is a 2-cocycle. -/
theorem canonical_massey_cocycle
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n) :
    groupCohomology.IsCocycle₂
      (masseyDefiningSystem
        (R := R) hn w).valueCochain := by
  let N :=
    magnusOrderSubgroup (R := R) (X := X) n
  let f :=
    transgressionCochain (R := R) N
      (degreeInvariantHom (R := R) hn w)
  let a := canonicalTopCochain (R := R) w
  have hf : groupCohomology.IsCocycle₂ f :=
    transgression_cochain_cocycle (R := R) N
      (degreeInvariantHom (R := R) hn w)
  have hsub :
      groupCohomology.IsCocycle₂
        (fun qr => f qr - trivialOneCoboundary a qr) :=
    isCocycle₂_sub_trivialOneCoboundary
      (fun _ _ => rfl) hf a
  intro q r s
  have hvalue (x y) :
      (masseyDefiningSystem
          (R := R) hn w).valueCochain (x, y) =
        f (x, y) - trivialOneCoboundary a (x, y) := by
    dsimp [f, a]
    rw [transgression_coboundary_massey
      (R := R) hn w x y]
    abel
  simpa [hvalue] using hsub q r s

/-- The actual low-degree cohomology class `ψ_w` attached to the canonical
word defining system. -/
def wordMasseyClass
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    groupCohomology.H2
      (Rep.trivial R
        (FreeGroup X ⧸
          magnusOrderSubgroup (R := R) (X := X) n) R) :=
  (masseyDefiningSystem (R := R) hn w).valueClass
    (fun _ _ => rfl)
    (canonical_massey_cocycle (R := R) hn w)

/-- The same word class in the explicit `Z²/B²` model. -/
def explicitMasseyClass
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    ExplicitH2 (R := R)
      (magnusOrderSubgroup (R := R) (X := X) n) :=
  explicitTransgressionLinear (R := R)
    (magnusOrderSubgroup (R := R) (X := X) n)
    (degreeInvariantHom (R := R) hn w)

/-- Efrat--Chapman, Lemma 9.1: the canonical word class is the
transgression of the top-right, degree-`n` coefficient character. -/
theorem word_massey_transgression
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    wordMasseyClass (R := R) hn w =
      transgressionClass (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n)
        (degreeInvariantHom (R := R) hn w) := by
  let N :=
    magnusOrderSubgroup (R := R) (X := X) n
  let M := masseyDefiningSystem (R := R) hn w
  let a := canonicalTopCochain (R := R) w
  let T :=
    transgressionCochain (R := R) N
      (degreeInvariantHom (R := R) hn w)
  have hcob :
      groupCohomology.IsCoboundary₂
        (fun qr => M.valueCochain qr - T qr) := by
    refine ⟨fun q => -a q, ?_⟩
    intro q r
    change
      -a r - -a (q * r) + -a q =
        M.valueCochain (q, r) - T (q, r)
    have hrelation :=
      transgression_coboundary_massey
        (R := R) hn w q r
    change
      T (q, r) =
        trivialOneCoboundary a (q, r) +
          M.valueCochain (q, r) at hrelation
    dsimp [trivialOneCoboundary] at hrelation
    rw [hrelation]
    abel
  change
    groupCohomology.H2π
        (Rep.trivial R
          (FreeGroup X ⧸ N) R)
        ⟨M.valueCochain, _⟩ =
      groupCohomology.H2π
        (Rep.trivial R
          (FreeGroup X ⧸ N) R)
        (transgressionCocycle (R := R) N
          (degreeInvariantHom (R := R) hn w))
  rw [groupCohomology.H2π_eq_iff]
  change
    (fun qr => M.valueCochain qr - T qr) ∈
      groupCohomology.coboundaries₂
        (Rep.trivial R (FreeGroup X ⧸ N) R)
  change
    (fun qr => M.valueCochain qr - T qr) ∈
      LinearMap.range
        (groupCohomology.d₁₂
          (Rep.trivial R (FreeGroup X ⧸ N) R)).hom
  rcases hcob with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  funext qr
  rcases qr with ⟨q, r⟩
  simpa [groupCohomology.d₁₂_hom_apply, M, T] using hb q r

/-- The canonical word class is genuinely a value of an `n`-fold Massey
defining system, with adjacent cochains given by the consecutive word
entries. -/
theorem word_massey_values
    {n : ℕ} (hn : 0 < n) (w : DegreeWord X n) :
    wordMasseyClass (R := R) hn w ∈
      MasseyProductValues (fun _ _ => rfl) n
        (fun i =>
          canonicalMasseyCochain
            (R := R) w i.castSucc i.succ) := by
  exact
    ⟨masseyDefiningSystem (R := R) hn w,
      canonical_massey_cocycle (R := R) hn w,
      fun _ => rfl, rfl⟩

/-- Linear combinations of degree-`n` word coefficient characters. -/
def coefficientCharacterMap
    {n : ℕ} (hn : 0 < n) :
    (DegreeWord X n →₀ R) →ₗ[R]
      invariantHom (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n) :=
  Finsupp.linearCombination R
    (fun w => degreeInvariantHom (R := R) hn w)

/-- The map `Ψ_(n,R)` in the explicit `Z²/B²` model. -/
def explicitMasseyLinear
    {n : ℕ} (hn : 0 < n) :
    (DegreeWord X n →₀ R) →ₗ[R]
      ExplicitH2 (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n) :=
  (explicitTransgressionLinear (R := R)
    (magnusOrderSubgroup (R := R) (X := X) n)).comp
      (coefficientCharacterMap (R := R) hn)

/-- The subgroup generated by the degree-`n` word classes. -/
def ExplicitMasseyImage
    {n : ℕ} (hn : 0 < n) :
    Submodule R
      (ExplicitH2 (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n)) :=
  LinearMap.range (explicitMasseyLinear (R := R) hn)

@[simp]
theorem explicit_massey_single
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) (r : R) :
    explicitMasseyLinear (R := R) hn
        (Finsupp.single w r) =
      r • explicitMasseyClass (R := R) hn w := by
  simp [explicitMasseyLinear,
    explicitMasseyClass, coefficientCharacterMap]

/-- The quotient of two consecutive Magnus-order subgroups. -/
abbrev MagnusLayer (n : ℕ) :=
  magnusOrderSubgroup (R := R) (X := X) n ⧸
    (magnusOrderSubgroup
      (R := R) (X := X) (n + 1)).subgroupOf
        (magnusOrderSubgroup (R := R) (X := X) n)

/-- Every consecutive Magnus layer is commutative.  In positive degree this
follows from the commutator estimate; degree zero is a trivial quotient. -/
instance magnus_layer_commutative
    (n : ℕ) :
    IsMulCommutative (MagnusLayer (R := R) (X := X) n) := by
  apply (Subgroup.Normal.quotient_commutative_iff_commutator_le).2
  change
    commutator (magnusOrderSubgroup (R := R) (X := X) n) ≤
      (magnusOrderSubgroup
        (R := R) (X := X) (n + 1)).subgroupOf
          (magnusOrderSubgroup (R := R) (X := X) n)
  by_cases hnzero : n = 0
  · subst n
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    exact magnus_vanishes_below (g : FreeGroup X)
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have hgAmbient :
      (g : FreeGroup X) ∈
        ⁅magnusOrderSubgroup (R := R) (X := X) n,
          magnusOrderSubgroup (R := R) (X := X) n⁆ := by
    rw [← Subgroup.map_subtype_commutator
      (magnusOrderSubgroup (R := R) (X := X) n)]
    exact
      Subgroup.mem_map_of_mem
        (magnusOrderSubgroup (R := R) (X := X) n).subtype hg
  have hdouble :
      (g : FreeGroup X) ∈
        magnusOrderSubgroup (R := R) (X := X) (n + n) := by
    exact
      Subgroup.commutator_le.mpr
        (fun x hx y hy =>
          magnus_difference_vanishes hx hy)
        hgAmbient
  exact
    magnus_order_antitone
      (R := R) (X := X)
      (by
        have hn : 0 < n := Nat.pos_of_ne_zero hnzero
        omega)
      hdouble

/-- A degree-`n` coefficient descends to the consecutive Magnus layer. -/
def degreeLayerHom
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    MagnusLayer (R := R) (X := X) n →*
      Multiplicative R := by
  rcases w with ⟨xs, rfl⟩
  let K :=
    (magnusOrderSubgroup
      (R := R) (X := X) (xs.length + 1)).subgroupOf
        (magnusOrderSubgroup
          (R := R) (X := X) xs.length)
  exact QuotientGroup.lift K
    (restrictedCoefficientHom (R := R) xs hn)
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      exact
        restricted_coefficient_succ
          (R := R) xs hn g hg)

/-- Additive form of a degree-`n` coefficient on the consecutive layer. -/
def degreeAdditiveHom
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n) :
    Additive (MagnusLayer (R := R) (X := X) n) →+ R :=
  MonoidHom.toAdditiveLeft
    (degreeLayerHom (R := R) hn w)

@[simp]
theorem degree_additive_mk
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n)
    (g : magnusOrderSubgroup (R := R) (X := X) n) :
    degreeAdditiveHom (R := R) hn w
        (Additive.ofMul
          (QuotientGroup.mk'
            ((magnusOrderSubgroup
              (R := R) (X := X) (n + 1)).subgroupOf
                (magnusOrderSubgroup (R := R) (X := X) n))
            g)) =
      magnusSeries (R := R) g.1
        (FreeMonoid.ofList w.1) := by
  rcases w with ⟨xs, rfl⟩
  rfl

/-- The upper coefficient pairing, bundled as an additive homomorphism from
the Magnus layer to the `R`-linear dual of the word module. -/
def upperCoefficientPairing
    {n : ℕ} (hn : 0 < n) :
    Additive (MagnusLayer (R := R) (X := X) n) →+
      ((DegreeWord X n →₀ R) →ₗ[R] R) where
  toFun q :=
    Finsupp.linearCombination R
      (fun w => degreeAdditiveHom (R := R) hn w q)
  map_zero' := by
    ext a
    simp [Finsupp.linearCombination_apply]
  map_add' := by
    intro q r
    ext a
    simp [Finsupp.linearCombination_apply]

@[simp]
theorem upper_pairing_single
    {n : ℕ} (hn : 0 < n)
    (q : Additive (MagnusLayer (R := R) (X := X) n))
    (w : DegreeWord X n) (r : R) :
    upperCoefficientPairing (R := R) hn q
        (Finsupp.single w r) =
      r * degreeAdditiveHom (R := R) hn w q := by
  simp [upperCoefficientPairing]

/-- The upper coefficient pairing has trivial left kernel. -/
theorem upper_pairing_imp
    {n : ℕ} (hn : 0 < n)
    (q : Additive (MagnusLayer (R := R) (X := X) n))
    (hq : upperCoefficientPairing (R := R) hn q = 0) :
    q = 0 := by
  let K :=
    (magnusOrderSubgroup
      (R := R) (X := X) (n + 1)).subgroupOf
        (magnusOrderSubgroup (R := R) (X := X) n)
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective K q.toMul
  have hqrepr :
      q = Additive.ofMul (QuotientGroup.mk' K g) := by
    apply Additive.ofMul.injective
    exact hg.symm
  have hdeep :
      g.1 ∈ magnusOrderSubgroup
        (R := R) (X := X) (n + 1) := by
    change
      VanishesBelow (magnusDifference (R := R) g.1) (n + 1)
    intro u hu
    by_cases hulow : u.length < n
    · exact g.2 u hulow
    · have hulength : u.length = n := by omega
      let w : DegreeWord X n :=
        ⟨u.toList, by
          simpa [FreeMonoid.length] using hulength⟩
      have hpair :=
        DFunLike.congr_fun hq (Finsupp.single w 1)
      have hcoefficient :
          degreeAdditiveHom (R := R) hn w
              (Additive.ofMul (QuotientGroup.mk' K g)) =
            0 := by
        rw [← hqrepr]
        simpa using hpair
      rw [degree_additive_mk] at hcoefficient
      have hseries :
          magnusSeries (R := R) g.1 u = 0 := by
        simpa [w, FreeMonoid.ofList_toList] using hcoefficient
      change
        magnusSeries (R := R) g.1 u -
            (1 : MSeries R X) u =
          0
      rw [hseries]
      simp [one_apply, hulength, hn.ne']
  apply Additive.ofMul.injective
  change q.toMul = 1
  rw [← hg]
  exact
    (QuotientGroup.eq_one_iff (N := K) g).mpr hdeep

/-- Equivalently, the upper coefficient pairing separates points of the
consecutive Magnus layer. -/
theorem upper_pairing_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (upperCoefficientPairing (R := R) (X := X) hn) := by
  intro q r hqr
  have hzero :
      upperCoefficientPairing (R := R) hn (q - r) = 0 := by
    rw [map_sub, hqr, sub_self]
  have hdiff :
      q - r = 0 :=
    upper_pairing_imp
      (R := R) hn (q - r) hzero
  exact sub_eq_zero.mp hdiff

@[simp]
theorem degree_invariant_hom
    {n : ℕ} (hn : 0 < n)
    (w : DegreeWord X n)
    (g : magnusOrderSubgroup (R := R) (X := X) n) :
    (degreeInvariantHom (R := R) hn w).1
        (Additive.ofMul g) =
      magnusSeries (R := R) g.1
        (FreeMonoid.ofList w.1) := by
  rcases w with ⟨xs, rfl⟩
  rfl

/-- Every combination of degree-`n` coefficient characters vanishes on the
next Magnus subgroup. -/
theorem coefficient_character_succ
    {n : ℕ} (hn : 0 < n)
    (a : DegreeWord X n →₀ R)
    (g : magnusOrderSubgroup (R := R) (X := X) n)
    (hg :
      g.1 ∈ magnusOrderSubgroup
        (R := R) (X := X) (n + 1)) :
    (coefficientCharacterMap (R := R) hn a).1
        (Additive.ofMul g) =
      0 := by
  rw [coefficientCharacterMap,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum]
  let ev :
      invariantHom (R := R)
          (magnusOrderSubgroup (R := R) (X := X) n) →ₗ[R] R := {
    toFun := fun f => f.1 (Additive.ofMul g)
    map_add' := by
      intro f h
      rfl
    map_smul' := by
      intro r f
      rfl
  }
  change
    ev (∑ w ∈ a.support,
      a w • degreeInvariantHom (R := R) hn w) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hwzero :
      (degreeInvariantHom (R := R) hn w).1
          (Additive.ofMul g) =
        0 := by
    rw [degree_invariant_hom]
    have hdifference :=
      hg (FreeMonoid.ofList w.1) (by
        change w.1.length < n + 1
        omega)
    have hone :
        (1 : MSeries R X) (FreeMonoid.ofList w.1) = 0 := by
      rw [one_apply]
      simp [FreeMonoid.length, w.2, hn.ne']
    exact sub_eq_zero.mp hdifference |>.trans hone
  simp [ev, hwzero]

/-- The span of all degree-`n` coefficient characters. -/
def CoefficientCharacterSpan
    {n : ℕ} (hn : 0 < n) :
    Submodule R
      (invariantHom (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n)) :=
  LinearMap.range (coefficientCharacterMap (R := R) hn)

/-- Transgression maps the coefficient-character span into the word-Massey
image. -/
def coefficientCharacterTransgression
    {n : ℕ} (hn : 0 < n) :
    CoefficientCharacterSpan (R := R) (X := X) hn →ₗ[R]
      ExplicitMasseyImage (R := R) (X := X) hn where
  toFun f :=
    ⟨explicitTransgressionLinear (R := R)
        (magnusOrderSubgroup (R := R) (X := X) n) f.1,
      by
        obtain ⟨a, ha⟩ := f.2
        refine ⟨a, ?_⟩
        change
          explicitMasseyLinear (R := R) hn a =
            explicitTransgressionLinear (R := R)
              (magnusOrderSubgroup (R := R) (X := X) n) f.1
        rw [explicitMasseyLinear, LinearMap.comp_apply, ha]⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    simp
  map_smul' := by
    intro r f
    apply Subtype.ext
    simp

/-- Injectivity of transgression restricts to the coefficient-character
span. -/
theorem coefficient_transgression_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
      (coefficientCharacterTransgression
        (R := R) (X := X) (lt_of_lt_of_le Nat.zero_lt_two hn)) := by
  intro f g hfg
  apply Subtype.ext
  apply magnus_explicit_transgression (R := R) (X := X) hn
  exact congrArg Subtype.val hfg

/-- Every element of the word-Massey image is the transgression of a
coefficient character. -/
theorem coeffi_trans_surje
    {n : ℕ} (hn : 0 < n) :
    Function.Surjective
      (coefficientCharacterTransgression
        (R := R) (X := X) hn) := by
  intro α
  obtain ⟨a, ha⟩ := α.2
  let f :
      CoefficientCharacterSpan (R := R) (X := X) hn :=
    ⟨coefficientCharacterMap (R := R) hn a, ⟨a, rfl⟩⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact ha

/-- The coefficient-character span and the word-Massey image are canonically
linearly equivalent for `n ≥ 2`. -/
noncomputable def coefficientMasseyImage
    {n : ℕ} (hn : 2 ≤ n) :
    CoefficientCharacterSpan
        (R := R) (X := X) (lt_of_lt_of_le Nat.zero_lt_two hn) ≃ₗ[R]
      ExplicitMasseyImage
        (R := R) (X := X) (lt_of_lt_of_le Nat.zero_lt_two hn) :=
  LinearEquiv.ofBijective
    (coefficientCharacterTransgression
      (R := R) (X := X) (lt_of_lt_of_le Nat.zero_lt_two hn))
    ⟨coefficient_transgression_injective
        (R := R) (X := X) hn,
      coeffi_trans_surje
        (R := R) (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn)⟩

/-- A coefficient character in the span descends to the consecutive Magnus
layer. -/
def coefficientCharacterHom
    {n : ℕ} (hn : 0 < n)
    (f : CoefficientCharacterSpan (R := R) (X := X) hn) :
    MagnusLayer (R := R) (X := X) n →*
      Multiplicative R := by
  let K :=
    (magnusOrderSubgroup
      (R := R) (X := X) (n + 1)).subgroupOf
        (magnusOrderSubgroup (R := R) (X := X) n)
  exact QuotientGroup.lift K
    (AddMonoidHom.toMultiplicativeRight f.1.1)
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change f.1.1 (Additive.ofMul g) = 0
      obtain ⟨a, ha⟩ := f.2
      rw [← ha]
      exact coefficient_character_succ
        (R := R) hn a g hg)

/-- Additive form of a coefficient character on the consecutive layer. -/
def coefficientCharacterAdditive
    {n : ℕ} (hn : 0 < n)
    (f : CoefficientCharacterSpan (R := R) (X := X) hn) :
    Additive (MagnusLayer (R := R) (X := X) n) →+ R :=
  MonoidHom.toAdditiveLeft
    (coefficientCharacterHom (R := R) hn f)

@[simp]
theorem coefficient_character_mk
    {n : ℕ} (hn : 0 < n)
    (f : CoefficientCharacterSpan (R := R) (X := X) hn)
    (g : magnusOrderSubgroup (R := R) (X := X) n) :
    coefficientCharacterAdditive (R := R) hn f
        (Additive.ofMul
          (QuotientGroup.mk'
            ((magnusOrderSubgroup
              (R := R) (X := X) (n + 1)).subgroupOf
                (magnusOrderSubgroup (R := R) (X := X) n))
            g)) =
      f.1.1 (Additive.ofMul g) :=
  rfl

/-- The coefficient pairing with the character span. -/
def coefficientCharacterPairing
    {n : ℕ} (hn : 0 < n) :
    Additive (MagnusLayer (R := R) (X := X) n) →+
      (CoefficientCharacterSpan (R := R) (X := X) hn →ₗ[R] R) where
  toFun q := {
    toFun := fun f =>
      coefficientCharacterAdditive (R := R) hn f q
    map_add' := by
      intro f g
      let K :=
        (magnusOrderSubgroup
          (R := R) (X := X) (n + 1)).subgroupOf
            (magnusOrderSubgroup (R := R) (X := X) n)
      obtain ⟨x, hx⟩ :=
        QuotientGroup.mk'_surjective K q.toMul
      have hq :
          q = Additive.ofMul (QuotientGroup.mk' K x) := by
        apply Additive.ofMul.injective
        exact hx.symm
      rw [hq]
      change
        (f + g).1.1 (Additive.ofMul x) =
          f.1.1 (Additive.ofMul x) +
            g.1.1 (Additive.ofMul x)
      rfl
    map_smul' := by
      intro r f
      let K :=
        (magnusOrderSubgroup
          (R := R) (X := X) (n + 1)).subgroupOf
            (magnusOrderSubgroup (R := R) (X := X) n)
      obtain ⟨x, hx⟩ :=
        QuotientGroup.mk'_surjective K q.toMul
      have hq :
          q = Additive.ofMul (QuotientGroup.mk' K x) := by
        apply Additive.ofMul.injective
        exact hx.symm
      rw [hq]
      rfl
  }
  map_zero' := by
    ext f
    change
      coefficientCharacterAdditive
          (R := R) hn f 0 =
        0
    exact
      (coefficientCharacterAdditive
        (R := R) hn f).map_zero
  map_add' := by
    intro q r
    ext f
    change
      coefficientCharacterAdditive
          (R := R) hn f (q + r) =
        coefficientCharacterAdditive
            (R := R) hn f q +
          coefficientCharacterAdditive
            (R := R) hn f r
    exact
      (coefficientCharacterAdditive
        (R := R) hn f).map_add q r

/-- A word combination, viewed as an element of the coefficient-character
span. -/
def coefficientCombinationSpan
    {n : ℕ} (hn : 0 < n)
    (a : DegreeWord X n →₀ R) :
    CoefficientCharacterSpan (R := R) (X := X) hn :=
  ⟨coefficientCharacterMap (R := R) hn a, ⟨a, rfl⟩⟩

/-- The character-span pairing agrees with the upper coefficient pairing. -/
theorem coefficient_pairing_combination
    {n : ℕ} (hn : 0 < n)
    (q : Additive (MagnusLayer (R := R) (X := X) n))
    (a : DegreeWord X n →₀ R) :
    coefficientCharacterPairing (R := R) hn q
        (coefficientCombinationSpan (R := R) hn a) =
      upperCoefficientPairing (R := R) hn q a := by
  let K :=
    (magnusOrderSubgroup
      (R := R) (X := X) (n + 1)).subgroupOf
        (magnusOrderSubgroup (R := R) (X := X) n)
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective K q.toMul
  have hq :
      q = Additive.ofMul (QuotientGroup.mk' K g) := by
    apply Additive.ofMul.injective
    exact hg.symm
  rw [hq]
  change
    coefficientCharacterAdditive
        (R := R) hn
        (coefficientCombinationSpan (R := R) hn a)
        (Additive.ofMul (QuotientGroup.mk' K g)) =
      Finsupp.linearCombination R
        (fun w =>
          degreeAdditiveHom (R := R) hn w
            (Additive.ofMul (QuotientGroup.mk' K g))) a
  calc
    coefficientCharacterAdditive
          (R := R) hn
          (coefficientCombinationSpan (R := R) hn a)
          (Additive.ofMul (QuotientGroup.mk' K g)) =
        (coefficientCharacterMap (R := R) hn a).1
          (Additive.ofMul g) := by
            simpa [K] using
              coefficient_character_mk
                (R := R) hn
                (coefficientCombinationSpan (R := R) hn a) g
    _ =
        Finsupp.linearCombination R
          (fun w =>
            magnusSeries (R := R) g.1
              (FreeMonoid.ofList w.1)) a := by
          let ev :
              invariantHom (R := R)
                  (magnusOrderSubgroup
                    (R := R) (X := X) n) →ₗ[R] R := {
            toFun := fun f => f.1 (Additive.ofMul g)
            map_add' := by
              intro f h
              rfl
            map_smul' := by
              intro r f
              rfl
          }
          change
            ev (coefficientCharacterMap (R := R) hn a) =
              Finsupp.linearCombination R
                (fun w =>
                  magnusSeries (R := R) g.1
                    (FreeMonoid.ofList w.1)) a
          rw [coefficientCharacterMap,
            Finsupp.linearCombination_apply,
            Finsupp.linearCombination_apply,
            map_finsuppSum]
          rw [Finsupp.sum, Finsupp.sum]
          apply Finset.sum_congr rfl
          intro w hw
          simp [ev, degree_invariant_hom]
    _ =
        Finsupp.linearCombination R
          (fun w =>
            degreeAdditiveHom (R := R) hn w
              (Additive.ofMul (QuotientGroup.mk' K g))) a := by
          rw [Finsupp.linearCombination_apply,
            Finsupp.linearCombination_apply,
            Finsupp.sum, Finsupp.sum]
          apply Finset.sum_congr rfl
          intro w hw
          rw [degree_additive_mk]

/-- The coefficient-character pairing has trivial left kernel. -/
theorem character_pairing_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (coefficientCharacterPairing
        (R := R) (X := X) hn) := by
  intro q r hqr
  apply upper_pairing_injective (R := R) (X := X) hn
  apply LinearMap.ext
  intro a
  have h :=
    DFunLike.congr_fun hqr
      (coefficientCombinationSpan (R := R) hn a)
  simpa [coefficient_pairing_combination
    (R := R) hn] using h

/-- The coefficient-character pairing has trivial right kernel. -/
theorem coefficient_character_pairing
    {n : ℕ} (hn : 0 < n)
    (f : CoefficientCharacterSpan (R := R) (X := X) hn)
    (hf :
      ∀ q,
        coefficientCharacterPairing (R := R) hn q f = 0) :
    f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro g
  let K :=
    (magnusOrderSubgroup
      (R := R) (X := X) (n + 1)).subgroupOf
        (magnusOrderSubgroup (R := R) (X := X) n)
  have h :=
    hf (Additive.ofMul
      (QuotientGroup.mk' K g))
  change f.1.1 (Additive.ofMul g) = 0
  simpa [coefficientCharacterPairing] using h

/-- The cohomological pairing, obtained by transporting the coefficient
pairing through transgression. -/
noncomputable def masseyPairing
    {n : ℕ} (hn : 2 ≤ n) :
    Additive (MagnusLayer (R := R) (X := X) n) →+
      (ExplicitMasseyImage
          (R := R) (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn) →ₗ[R] R) where
  toFun q := {
    toFun := fun α =>
      coefficientCharacterPairing
          (R := R) (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn) q
        ((coefficientMasseyImage
          (R := R) (X := X) hn).symm α)
    map_add' := by
      intro α β
      simp
    map_smul' := by
      intro r α
      simp
  }
  map_zero' := by
    ext α
    simp [coefficientCharacterPairing]
  map_add' := by
    intro q r
    ext α
    simp [coefficientCharacterPairing]

/-- The cohomological pairing has trivial left kernel. -/
theorem masseyPairing_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
      (masseyPairing (R := R) (X := X) hn) := by
  intro q r hqr
  apply character_pairing_injective
    (R := R) (X := X)
      (lt_of_lt_of_le Nat.zero_lt_two hn)
  apply LinearMap.ext
  intro f
  have h :=
    DFunLike.congr_fun hqr
      (coefficientMasseyImage
        (R := R) (X := X) hn f)
  simpa [masseyPairing] using h

/-- The cohomological pairing has trivial right kernel. -/
theorem massey_pairing_kernel
    {n : ℕ} (hn : 2 ≤ n)
    (α :
      ExplicitMasseyImage
        (R := R) (X := X)
        (lt_of_lt_of_le Nat.zero_lt_two hn))
    (hα :
      ∀ q, masseyPairing (R := R) (X := X) hn q α = 0) :
    α = 0 := by
  let e :=
    coefficientMasseyImage
      (R := R) (X := X) hn
  have hf :
      e.symm α = 0 := by
    apply coefficient_character_pairing
      (R := R) (X := X)
        (lt_of_lt_of_le Nat.zero_lt_two hn)
    intro q
    simpa [masseyPairing, e] using hα q
  calc
    α = e (e.symm α) := (e.apply_symm_apply α).symm
    _ = e 0 := congrArg e hf
    _ = 0 := e.map_zero

/-- Efrat--Chapman, Theorem 9.2, in the explicit low-degree model
`H² = Z²/B²`: the canonical pairing between the consecutive Magnus layer
and the image generated by the canonical defining-system values is
nondegenerate. -/
theorem masseyPairing_nondegenerate
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
        (masseyPairing (R := R) (X := X) hn) ∧
      ∀ α,
        (∀ q,
          masseyPairing (R := R) (X := X) hn q α = 0) →
        α = 0 :=
  ⟨masseyPairing_injective (R := R) (X := X) hn,
    massey_pairing_kernel (R := R) (X := X) hn⟩

/-- The finite-field specialization stated at the end of Section 9.  Under
the standard Magnus characterization of the mod-`p` Zassenhaus filtration,
this is the nondegenerate pairing on its consecutive layer. -/
theorem massey_pairing_nondegenerate
    {Y : Type} {p n : ℕ} [Fact p.Prime] (hn : 2 ≤ n) :
    Function.Injective
        (masseyPairing (R := ZMod p) (X := Y) hn) ∧
      ∀ α,
        (∀ q,
          masseyPairing (R := ZMod p) (X := Y) hn q α = 0) →
        α = 0 := by
  exact masseyPairing_nondegenerate
    (R := ZMod p) (X := Y) hn

end MMassey
end MSeries
end EChapma
