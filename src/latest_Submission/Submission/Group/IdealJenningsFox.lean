import Submission.Group.PresentedRelationIdeal

namespace Submission

open scoped BigOperators

open TBluepr

/-!
# Active relator API
-/

namespace pARelato

variable {r : ℕ} {depth : Fin r → ℕ} {m n : ℕ}

theorem depth_le (a : pARelato depth n) :
    depth (a : Fin r) ≤ n := by
  exact a.property

theorem exists_coe_iff (i : Fin r) :
    (∃ a : pARelato depth n, (a : Fin r) = i) ↔ depth i ≤ n := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hi
    exact ⟨⟨i, hi⟩, rfl⟩

theorem not_coe (i : Fin r) :
    (¬ ∃ a : pARelato depth n, (a : Fin r) = i) ↔ n < depth i := by
  rw [exists_coe_iff]
  omega

@[ext]
theorem ext {a b : pARelato depth n}
    (h : (a : Fin r) = (b : Fin r)) :
    a = b := by
  exact Subtype.ext h

def castLE (h : m ≤ n) :
    pARelato depth m → pARelato depth n :=
  fun a => ⟨(a : Fin r), le_trans a.property h⟩

@[simp]
theorem coe_castLE (h : m ≤ n) (a : pARelato depth m) :
    ((castLE (depth := depth) h a : pARelato depth n) : Fin r) =
      (a : Fin r) := by
  rfl

theorem castLE_injective (h : m ≤ n) :
    Function.Injective (castLE (depth := depth) h) := by
  intro a b hab
  apply ext
  simpa [castLE] using
    congrArg (fun x : pARelato depth n => (x : Fin r)) hab

theorem depth_ge_two
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (a : pARelato depth n) :
    2 ≤ depth (a : Fin r) := by
  exact hdepth2 _

theorem zassenhaus_mem
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {depth : Fin r → ℕ} {n : ℕ}
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (a : pARelato depth n) :
    rels (a : Fin r) ∈
      zassenhausFiltration p (FreeGroup (Fin d)) (depth (a : Fin r)) := by
  exact hdepth _

end pARelato


/-!
# Graded relator coefficient API

The relator source is a dependent family of augmentation layers.  In
particular, its coordinates are not scalars: the coordinate at a relator of
depth `e` lies in the layer of degree `n - e`.
-/

noncomputable abbrev presentedAllSource
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (n : ℕ) : Type :=
  ∀ i : Fin r, pALayer (p := p) rels (n - depth i)

namespace pHSrc

variable {p d r : ℕ} [Fact p.Prime]
variable {rels : Fin r → FreeGroup (Fin d)}
variable {depth : Fin r → ℕ}
variable {n : ℕ}

/-- Coordinate projection on the graded active-relator source. -/
noncomputable def eval (a : pARelato depth n) :
    pHSrc (p := p) rels depth n →ₗ[ZMod p]
      pALayer (p := p) rels (n - depth a.1) := by
  exact LinearMap.proj a

@[simp]
theorem eval_apply
    (a : pARelato depth n)
    (c : pHSrc (p := p) rels depth n) :
    eval (p := p) (rels := rels) a c = c a := by
  rfl

/-- Transport a graded coefficient along equality of active relators. -/
noncomputable def castCoefficient
    {a b : pARelato depth n}
    (h : a = b) :
    pALayer (p := p) rels (n - depth a.1) →ₗ[ZMod p]
      pALayer (p := p) rels (n - depth b.1) := by
  subst b
  exact LinearMap.id

/-- The graded coefficient vector supported at one active relator. -/
noncomputable def single (a : pARelato depth n) :
    pALayer (p := p) rels (n - depth a.1) →ₗ[ZMod p]
      pHSrc (p := p) rels depth n := by
  classical
  exact
    LinearMap.single (ZMod p)
      (fun a : pARelato depth n =>
        pALayer (p := p) rels (n - depth a.1))
      a

@[simp]
theorem single_apply
    (a b : pARelato depth n)
    (x : pALayer (p := p) rels (n - depth a.1)) :
    single (p := p) (rels := rels) a x b =
      if h : a = b then castCoefficient (p := p) (rels := rels) h x else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [single, castCoefficient]
  · simp [single, h, Ne.symm h]

@[simp]
theorem eval_single_same
    (a : pARelato depth n)
    (x : pALayer (p := p) rels (n - depth a.1)) :
    eval (p := p) (rels := rels) a
      ((single (p := p) (rels := rels) a) x) = x := by
  classical
  simp [eval, single]

theorem eval_single_ne
    {a b : pARelato depth n}
    (h : b ≠ a)
    (x : pALayer (p := p) rels (n - depth a.1)) :
    eval (p := p) (rels := rels) b
      ((single (p := p) (rels := rels) a) x) = 0 := by
  classical
  simp [eval, single, h]

@[ext]
theorem ext
    {c c' : pHSrc (p := p) rels depth n}
    (h : ∀ a : pARelato depth n, c a = c' a) :
    c = c' := by
  funext a
  exact h a

/-- The graded active-source basis expansion. -/
theorem sum_single
    (c : pHSrc (p := p) rels depth n) :
    (∑ a : pARelato depth n,
        (single (p := p) (rels := rels) a) (c a)) = c := by
  classical
  ext a
  simp [single]

/-- Restrict coefficients on all relators to active relators. -/
noncomputable def restrictActive :
    presentedAllSource (p := p) rels depth n →ₗ[ZMod p]
      pHSrc (p := p) rels depth n := by
  exact LinearMap.pi fun a => LinearMap.proj a.1

@[simp]
theorem restrictActive_apply
    (c : presentedAllSource (p := p) rels depth n)
    (a : pARelato depth n) :
    restrictActive (p := p) (rels := rels) (depth := depth) (n := n) c a =
      c (a : Fin r) := by
  rfl

/-- Extend active graded coefficients by zero to all relators. -/
noncomputable def extendByZero :
    pHSrc (p := p) rels depth n →ₗ[ZMod p]
      presentedAllSource (p := p) rels depth n := by
  classical
  refine
    { toFun := fun c i => if hi : depth i ≤ n then c ⟨i, hi⟩ else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro c c'
    funext i
    by_cases hi : depth i ≤ n <;> simp [hi]
  · intro a c
    funext i
    by_cases hi : depth i ≤ n <;> simp [hi]

theorem apply_of_le
    (c : pHSrc (p := p) rels depth n)
    {i : Fin r}
    (hi : depth i ≤ n) :
    extendByZero (p := p) (rels := rels) (depth := depth) (n := n) c i =
      c ⟨i, hi⟩ := by
  classical
  simp [extendByZero, hi]

theorem extend_zero_not
    (c : pHSrc (p := p) rels depth n)
    {i : Fin r}
    (hi : ¬ depth i ≤ n) :
    extendByZero (p := p) (rels := rels) (depth := depth) (n := n) c i = 0 := by
  classical
  simp [extendByZero, hi]

@[simp]
theorem restrict_active_extend :
    (restrictActive (p := p) (rels := rels) (depth := depth) (n := n)).comp
      (extendByZero (p := p) (rels := rels) (depth := depth) (n := n))
    =
    (LinearMap.id :
      pHSrc (p := p) rels depth n →ₗ[ZMod p]
        pHSrc (p := p) rels depth n) := by
  apply LinearMap.ext
  intro c
  funext a
  exact apply_of_le c a.property

theorem extend_zero_injective :
    Function.Injective
      (extendByZero (p := p) (rels := rels) (depth := depth) (n := n)) := by
  intro c c' h
  apply ext
  intro a
  have ha := congrFun h (a : Fin r)
  rw [apply_of_le c a.property,
    apply_of_le c' a.property] at ha
  exact ha

end pHSrc


/-!
# Graded generator-target coordinate API
-/

namespace pGTarget

variable {p d r : ℕ} [Fact p.Prime]
variable {rels : Fin r → FreeGroup (Fin d)}
variable {n : ℕ}

/-- Coordinate projection on the graded generator target. -/
noncomputable def eval (j : Fin d) :
    pGTarget (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels (n - 1) := by
  exact LinearMap.proj j

@[simp]
theorem eval_apply
    (j : Fin d)
    (v : pGTarget (p := p) rels n) :
    eval (p := p) (rels := rels) (n := n) j v = v j := by
  rfl

/-- The graded coordinate vector supported at one generator. -/
noncomputable def single (j : Fin d) :
    pALayer (p := p) rels (n - 1) →ₗ[ZMod p]
      pGTarget (p := p) rels n := by
  classical
  exact
    LinearMap.single (ZMod p)
      (fun _ : Fin d => pALayer (p := p) rels (n - 1))
      j

@[simp]
theorem single_apply
    (j k : Fin d)
    (x : pALayer (p := p) rels (n - 1)) :
    single (p := p) (rels := rels) (n := n) j x k =
      if k = j then x else 0 := by
  classical
  simp [single, Pi.single_apply]

@[simp]
theorem eval_single_same
    (j : Fin d)
    (x : pALayer (p := p) rels (n - 1)) :
    eval (p := p) (rels := rels) (n := n) j
      ((single (p := p) (rels := rels) (n := n) j) x) = x := by
  classical
  simp [eval, single]

theorem eval_single_ne
    {j k : Fin d}
    (h : k ≠ j)
    (x : pALayer (p := p) rels (n - 1)) :
    eval (p := p) (rels := rels) (n := n) k
      ((single (p := p) (rels := rels) (n := n) j) x) = 0 := by
  classical
  simp [eval, single, h]

@[ext]
theorem ext
    {v w : pGTarget (p := p) rels n}
    (h : ∀ j : Fin d, v j = w j) :
    v = w := by
  funext j
  exact h j

/-- The graded generator-target basis expansion. -/
theorem sum_single
    (v : pGTarget (p := p) rels n) :
    (∑ j : Fin d,
        (single (p := p) (rels := rels) (n := n) j) (v j)) = v := by
  classical
  ext j
  simp [single]

end pGTarget


/-!
# Quotient by the derivative-relation layer
-/

/-- The quotient map whose kernel is, by construction, the derivative-relation layer. -/
noncomputable def presentedHighRelation
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ) :
    pGTarget (p := p) rels n →ₗ[ZMod p]
      (pGTarget (p := p) rels n ⧸
        presentedHighDerivative (p := p) rels n) :=
  Submodule.mkQ (presentedHighDerivative (p := p) rels n)

theorem presented_high_relation
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ) :
    LinearMap.ker (presentedHighRelation (p := p) rels n) =
      presentedHighDerivative (p := p) rels n := by
  exact Submodule.ker_mkQ _

theorem presented_high_derivative
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ)
    (v : pGTarget (p := p) rels n) :
    v ∈ presentedHighDerivative (p := p) rels n ↔
      presentedHighRelation (p := p) rels n v = 0 := by
  change
    v ∈ presentedHighDerivative (p := p) rels n ↔
      (Submodule.mkQ
        (presentedHighDerivative (p := p) rels n)) v = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]


/-!
# Relators give derivative relations
-/

theorem presented_congr_hdepth
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth hdepth' :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 hdepth2' : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    presentedHighFox
        (p := p) rels depth hdepth hdepth2 n =
      presentedHighFox
        (p := p) rels depth hdepth' hdepth2' n := by
  rfl

theorem presented_high_fox
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    (presentedHighRelation (p := p) rels n).comp
      (presentedHighFox
        (p := p) rels depth hdepth hdepth2 n) = 0 := by
  apply LinearMap.ext
  intro c
  apply
    (presented_high_derivative
      (p := p) rels n _).mp
  exact
    presented_derivative_relation
      (p := p) rels depth hdepth hdepth2 n ⟨c, rfl⟩

theorem presented_high_ker
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    LinearMap.range
      (presentedHighFox
        (p := p) rels depth hdepth hdepth2 n)
      ≤
    LinearMap.ker (presentedHighRelation (p := p) rels n) := by
  exact
    LinearMap.range_le_ker_iff.mpr
      (presented_high_fox
        (p := p) rels depth hdepth hdepth2 n)

theorem high_fox_derivative
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (c : pHSrc (p := p) rels depth n) :
    presentedHighFox
        (p := p) rels depth hdepth hdepth2 n c
      ∈ presentedHighDerivative (p := p) rels n := by
  exact
    presented_derivative_relation
      (p := p) rels depth hdepth hdepth2 n ⟨c, rfl⟩


/-!
# Exactness formulation
-/

/-- The degree-`n` graded Fox complex is exact at the generator term. -/
def presentedHighComplex
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) : Prop :=
  LinearMap.range
      (presentedHighFox
        (p := p) rels depth hdepth hdepth2 n)
    =
  LinearMap.ker (presentedHighRelation (p := p) rels n)

/-- Elementwise version of the desired inclusion. -/
def elementwiseFoxSurjectivity
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) : Prop :=
  ∀ v : pGTarget (p := p) rels n,
    v ∈ presentedHighDerivative (p := p) rels n →
      ∃ c : pHSrc (p := p) rels depth n,
        presentedHighFox
          (p := p) rels depth hdepth hdepth2 n c = v

theorem elementwise_fox_surjectivity
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    elementwiseFoxSurjectivity
        (p := p) rels depth hdepth hdepth2 n
      ↔
    presentedHighDerivative (p := p) rels n ≤
      LinearMap.range
        (presentedHighFox
          (p := p) rels depth hdepth hdepth2 n) := by
  rfl

theorem presented_high_complex
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    presentedHighComplex
        (p := p) rels depth hdepth hdepth2 n
      ↔
    ∀ v : pGTarget (p := p) rels n,
      v ∈ LinearMap.ker (presentedHighRelation (p := p) rels n) →
        ∃ c : pHSrc (p := p) rels depth n,
          presentedHighFox
            (p := p) rels depth hdepth hdepth2 n c = v := by
  constructor
  · intro hExact v hv
    rw [← hExact] at hv
    exact hv
  · intro hSurj
    apply le_antisymm
    · exact
        presented_high_ker
          (p := p) rels depth hdepth hdepth2 n
    · exact hSurj

theorem derivative_complex_exact
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hExact :
      presentedHighComplex
        (p := p) rels depth hdepth hdepth2 n) :
    presentedHighDerivative (p := p) rels n =
      LinearMap.range
        (presentedHighFox
          (p := p) rels depth hdepth hdepth2 n) := by
  calc
    presentedHighDerivative (p := p) rels n =
        LinearMap.ker (presentedHighRelation (p := p) rels n) := by
      exact (presented_high_relation (p := p) rels n).symm
    _ =
        LinearMap.range
          (presentedHighFox
            (p := p) rels depth hdepth hdepth2 n) := hExact.symm

theorem presented_complex_exact
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hExact :
      presentedHighComplex
        (p := p) rels depth hdepth hdepth2 n) :
    presentedHighDerivative (p := p) rels n ≤
      LinearMap.range
        (presentedHighFox
          (p := p) rels depth hdepth hdepth2 n) := by
  exact
    (derivative_complex_exact
      (p := p) rels depth hdepth hdepth2 n hExact).le


/-!
# Graded matrix form of the Fox map
-/

/-- The graded Fox coefficient map from one active relator to one generator coordinate. -/
noncomputable def presentedHighCoefficient
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (a : pARelato depth n)
    (j : Fin d) :
    pALayer (p := p) rels (n - depth a.1) →ₗ[ZMod p]
      pALayer (p := p) rels (n - 1) :=
  (pGTarget.eval
      (p := p) (rels := rels) (n := n) j).comp
    ((presentedHighFox
      (p := p) rels depth hdepth hdepth2 n).comp
        (pHSrc.single
          (p := p) (rels := rels) a))

theorem presented_high_single
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (a : pARelato depth n)
    (x : pALayer (p := p) rels (n - depth a.1))
    (j : Fin d) :
    presentedHighFox
        (p := p) rels depth hdepth hdepth2 n
        ((pHSrc.single
          (p := p) (rels := rels) a) x) j =
      presentedHighCoefficient
        (p := p) rels depth hdepth hdepth2 n a j x := by
  rfl

theorem presented_high_images
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (c : pHSrc (p := p) rels depth n) :
    presentedHighFox
        (p := p) rels depth hdepth hdepth2 n c =
      ∑ a : pARelato depth n,
        presentedHighFox
          (p := p) rels depth hdepth hdepth2 n
          ((pHSrc.single
            (p := p) (rels := rels) a) (c a)) := by
  rw [← map_sum, pHSrc.sum_single]

theorem presented_high_coefficient
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (c : pHSrc (p := p) rels depth n)
    (j : Fin d) :
    presentedHighFox
        (p := p) rels depth hdepth hdepth2 n c j =
      ∑ a : pARelato depth n,
        presentedHighCoefficient
          (p := p) rels depth hdepth hdepth2 n a j (c a) := by
  rw [presented_high_images]
  simp only [Finset.sum_apply,
    presented_high_single]

theorem presented_high_coefficients
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (v : pGTarget (p := p) rels n) :
    v ∈ LinearMap.range
      (presentedHighFox
        (p := p) rels depth hdepth hdepth2 n)
      ↔
    ∃ c : pHSrc (p := p) rels depth n,
      ∀ j : Fin d,
        v j =
          ∑ a : pARelato depth n,
            presentedHighCoefficient
              (p := p) rels depth hdepth hdepth2 n a j (c a) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact
      ⟨c, fun j =>
        presented_high_coefficient
          (p := p) rels depth hdepth hdepth2 n c j⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext j
    rw [presented_high_coefficient]
    exact (hc j).symm

/-- Fox rows are the images of graded coefficients supported at one active relator. -/
noncomputable def presentedRowSet
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    Set (pGTarget (p := p) rels n) :=
  Set.range fun ax :
      Σ a : pARelato depth n,
        pALayer (p := p) rels (n - depth a.1) =>
    presentedHighFox
      (p := p) rels depth hdepth hdepth2 n
      ((pHSrc.single
        (p := p) (rels := rels) ax.1) ax.2)

theorem presented_row_set
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    LinearMap.range
      (presentedHighFox
        (p := p) rels depth hdepth hdepth2 n) =
      Submodule.span (ZMod p)
        (presentedRowSet
          (p := p) rels depth hdepth hdepth2 n) := by
  apply le_antisymm
  · rintro v ⟨c, rfl⟩
    rw [presented_high_images]
    exact
      Submodule.sum_mem _ fun a _ =>
        Submodule.subset_span
          ⟨⟨a, c a⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨⟨a, x⟩, rfl⟩
    exact
      ⟨(pHSrc.single
          (p := p) (rels := rels) a) x, rfl⟩

theorem high_row_derivative
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    presentedRowSet
        (p := p) rels depth hdepth hdepth2 n
      ⊆
    presentedHighDerivative (p := p) rels n := by
  rintro v ⟨⟨a, x⟩, rfl⟩
  exact
    high_fox_derivative
      (p := p) rels depth hdepth hdepth2 n
      ((pHSrc.single
        (p := p) (rels := rels) a) x)

theorem presented_row_derivative
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ) :
    Submodule.span (ZMod p)
      (presentedRowSet
        (p := p) rels depth hdepth hdepth2 n)
      ≤
    presentedHighDerivative (p := p) rels n := by
  exact
    Submodule.span_le.mpr
      (high_row_derivative
        (p := p) rels depth hdepth hdepth2 n)


/-!
# Filtered Jennings--Fox exactness as the main mathematical input
-/

/-- Filtered Jennings--Fox exactness, packaged in the exact-complex form. -/
theorem presented_complex_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    presentedHighComplex
      (p := p) rels depth hdepth hdepth2 n := by
  apply le_antisymm
  · exact
      presented_high_ker
        (p := p) rels depth hdepth hdepth2 n
  · rw [presented_high_relation]
    exact
      presented_derivative_exactness
        (p := p) rels depth hdepth hdepth2 hstrict n hn

/-- Elementwise Jennings--Fox exactness. -/
theorem elementwise_surjectivity_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    elementwiseFoxSurjectivity
      (p := p) rels depth hdepth hdepth2 n := by
  apply
    (elementwise_fox_surjectivity
      (p := p) rels depth hdepth hdepth2 n).mpr
  exact
    presented_complex_exact
      (p := p) rels depth hdepth hdepth2 n
      (presented_complex_exactness
        (p := p) rels depth hdepth hdepth2 hstrict n hn)

/-- Coordinate form of elementwise Jennings--Fox exactness. -/
theorem derivative_solvable_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    ∀ v : pGTarget (p := p) rels n,
      v ∈ presentedHighDerivative (p := p) rels n →
        ∃ c : pHSrc (p := p) rels depth n,
          ∀ j : Fin d,
            v j =
              ∑ a : pARelato depth n,
                presentedHighCoefficient
                  (p := p) rels depth hdepth hdepth2 n a j (c a) := by
  intro v hv
  rcases
      elementwise_surjectivity_exactness
        (p := p) rels depth hdepth hdepth2 hstrict n hn v hv with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro j
  rw [← hc]
  exact
    presented_high_coefficient
      (p := p) rels depth hdepth hdepth2 n c j

theorem derivative_row_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    presentedHighDerivative (p := p) rels n ≤
      Submodule.span (ZMod p)
        (presentedRowSet
          (p := p) rels depth hdepth hdepth2 n) := by
  rw [← presented_row_set
    (p := p) rels depth hdepth hdepth2 n]
  exact
    presented_complex_exact
      (p := p) rels depth hdepth hdepth2 n
      (presented_complex_exactness
        (p := p) rels depth hdepth hdepth2 hstrict n hn)

set_option linter.style.longLine false in
/-- The final desired inclusion, obtained from the exact-complex formulation. -/
theorem
    derivative_exactness_aux
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    presentedHighDerivative (p := p) rels n ≤
      LinearMap.range
        (presentedHighFox
          (p := p) rels depth hdepth hdepth2 n) := by
  exact
    presented_complex_exact
      (p := p) rels depth hdepth hdepth2 n
      (presented_complex_exactness
        (p := p) rels depth hdepth hdepth2 hstrict n hn)

end Submission
