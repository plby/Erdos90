import Towers.Algebra.PBW

namespace Towers
namespace Group

universe u v w
open Towers.Algebra


/-- Relation degree shift. -/
abbrev relationDegreeShift := ℕ

/-- Graded relator module, with module structure in each degree and a global
shift recording the relator depth. -/
structure gRModule (R : Type u) [Semiring R] where
  piece : ℕ → Type v
  [addPiece : ∀ n, AddCommMonoid (piece n)]
  [modulePiece : ∀ n, Module R (piece n)]
  shift : ℕ
  relatorIndex : Type w
  relatorDegree : relatorIndex → ℕ
  degreeGenerators : ∀ n, Set (piece n)
  generators_live_degree : ∀ i, (degreeGenerators (relatorDegree i + shift)).Nonempty
  spans : ∀ n, Submodule.span R (degreeGenerators n) = ⊤

/-- The displayed generators in the shifted relator degree are nonempty. -/
theorem gRModule.generators_nonempty {R : Type u} [Semiring R]
    (M : gRModule R) (i : M.relatorIndex) :
    (M.degreeGenerators (M.relatorDegree i + M.shift)).Nonempty :=
  M.generators_live_degree i

/-- Each homogeneous degree is spanned by the displayed generators. -/
theorem gRModule.span_eq_top {R : Type u} [Semiring R]
    (M : gRModule R) (n : ℕ) :
    (letI := M.addPiece n; letI := M.modulePiece n;
      Submodule.span R (M.degreeGenerators n) = ⊤) := by
  exact M.spans n


/-- Fox initial map between graded modules, linear in each homogeneous degree. -/
structure fIMap (R : Type u) [Semiring R] where
  domain : ℕ → Type v
  codomain : ℕ → Type w
  [addDomain : ∀ n, AddCommMonoid (domain n)]
  [modDomain : ∀ n, Module R (domain n)]
  [addCodomain : ∀ n, AddCommMonoid (codomain n)]
  [modCodomain : ∀ n, Module R (codomain n)]
  map : ∀ n, domain n →ₗ[R] codomain n
  kernel : ∀ n, Submodule R (domain n) := fun n => LinearMap.ker (map n)
  range : ∀ n, Submodule R (codomain n) := fun n => LinearMap.range (map n)
  threshold : ℕ
  surjective_above : ∀ n, threshold ≤ n → Function.Surjective (map n)
  injective_above : ∀ n, threshold ≤ n → Function.Injective (map n)

/-- Above the threshold, a Fox initial map is surjective by its recorded
high-degree exactness data. -/
theorem fIMap.surj_threshold_le {R : Type u} [Semiring R]
    (F : fIMap R) (n : ℕ) (hn : F.threshold ≤ n) :
    Function.Surjective (F.map n) :=
  F.surjective_above n hn

/-- Named accessor for injectivity above the threshold. -/
theorem fIMap.inj_threshold_le {R : Type u} [Semiring R]
    (F : fIMap R) (n : ℕ) (hn : F.threshold ≤ n) :
    Function.Injective (F.map n) :=
  F.injective_above n hn


/-- Above the threshold, the actual kernel of the linear map is trivial. -/
theorem fIMap.lin_kereq_botabove {R : Type u} [Semiring R]
    (F : fIMap R) (n : ℕ) (hn : F.threshold ≤ n) :
    letI := F.addDomain n; letI := F.modDomain n
    letI := F.addCodomain n; letI := F.modCodomain n
    LinearMap.ker (F.map n) = ⊥ := by
  letI := F.addDomain n; letI := F.modDomain n
  letI := F.addCodomain n; letI := F.modCodomain n
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    apply F.injective_above n hn
    change F.map n x = F.map n 0
    simpa using hx
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst x
    simp

/-- The stored kernel in a Fox initial map is available degreewise. -/
theorem fIMap.inj_map_threshold {R : Type u} [Semiring R]
    (F : fIMap R) {n : ℕ} (hn : F.threshold ≤ n) :
    Function.Injective (F.map n) :=
  F.injective_above n hn

/-- Presentation relation module, with a boundary map from formal relators into
the ambient module and a spanning assertion for relator images. -/
structure pRModule (R : Type u) [Semiring R] where
  pres : presentations.{v}
  moduleCarrier : Type w
  [addM : AddCommMonoid moduleCarrier]
  [modM : Module R moduleCarrier]
  relatorVector : pres.rels → moduleCarrier
  relationSpan : Submodule R moduleCarrier := Submodule.span R (Set.range relatorVector)
  formalRelators : Type (max u v w)
  [addFormal : AddCommMonoid formalRelators]
  [modFormal : Module R formalRelators]
  basisVector : pres.rels → formalRelators
  basis_spans : Submodule.span R (Set.range basisVector) = ⊤
  boundary : formalRelators →ₗ[R] moduleCarrier
  boundary_basis : ∀ r, boundary (basisVector r) = relatorVector r
  range_boundary : LinearMap.range boundary = relationSpan
  spans_relations : relationSpan = Submodule.span R (Set.range relatorVector)

attribute [instance] pRModule.addM pRModule.modM
attribute [instance] pRModule.addFormal pRModule.modFormal

/-- The formal relator vectors span the formal relator module. -/
theorem pRModule.basis_span_top {R : Type u} [Semiring R]
    (P : pRModule R) :
    Submodule.span R (Set.range P.basisVector) = ⊤ :=
  P.basis_spans

/-- Each displayed relator vector lies in the relation span. -/
theorem pRModule.relator_vector_memspan {R : Type u} [Semiring R]
    (P : pRModule R) (r : P.pres.rels) :
    P.relatorVector r ∈ P.relationSpan := by
  rw [P.spans_relations]
  exact Submodule.subset_span ⟨r, rfl⟩

/-- Each basis vector maps into the relation span under the boundary. -/
theorem pRModule.bound_basis_memspan {R : Type u} [Semiring R]
    (P : pRModule R) (r : P.pres.rels) :
    P.boundary (P.basisVector r) ∈ P.relationSpan := by
  rw [P.boundary_basis r]
  exact P.relator_vector_memspan r

/-- Boundary sends a formal basis vector to its relator vector. -/
theorem pRModule.boundary_basis_apply {R : Type u} [Semiring R]
    (P : pRModule R) (r : P.pres.rels) :
    P.boundary (P.basisVector r) = P.relatorVector r :=
  P.boundary_basis r

/-- The range of the boundary is the recorded relation span. -/
theorem pRModule.range_boundary_eq {R : Type u} [Semiring R]
    (P : pRModule R) : LinearMap.range P.boundary = P.relationSpan :=
  P.range_boundary

/-- Hilbert series of an algebra. -/
abbrev algebraHilbertH (R : Type u) := hilbertSeries R

/-- Hilbert series of a module. -/
abbrev moduleHilbertSeries (R : Type u) := hilbertSeries R

/-- Relator series. -/
abbrev relatorSeriesR (R : Type u) := hilbertSeries R

/-- The standard coefficient sequence for `1 - d t + Σ r_q t^q`. -/
def standardGSCoefficients (R : Type u) [Ring R] (d : R) (r : ℕ → R) : ℕ → R :=
  fun n => if n = 0 then 1 else if n = 1 then r 1 - d else r n

@[simp] theorem standard_coefficients_zero (R : Type u) [Ring R]
    (d : R) (r : ℕ → R) : standardGSCoefficients R d r 0 = 1 := by
  simp [standardGSCoefficients]

@[simp] theorem standard_coefficients_one (R : Type u) [Ring R]
    (d : R) (r : ℕ → R) : standardGSCoefficients R d r 1 = r 1 - d := by
  simp [standardGSCoefficients]

theorem standard_gs_coefficients (R : Type u) [Ring R]
    (d : R) (r : ℕ → R) {n : ℕ} (hn : 2 ≤ n) :
    standardGSCoefficients R d r n = r n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  simp [standardGSCoefficients, hn0, hn1]

/-- GS series polynomial data, retaining the generator number and relator-depth
coefficients in addition to the resulting coefficient sequence. -/
structure gSPoly (R : Type u) [Ring R] where
  generatorCoeff : R
  relatorCoeff : ℕ → R
  coeff : ℕ → R
  coeff_spec : coeff = standardGSCoefficients R generatorCoeff relatorCoeff
  coeff_zero : coeff 0 = 1
  coeff_one : coeff 1 = relatorCoeff 1 - generatorCoeff
  coeff_ge_two : ∀ n, 2 ≤ n → coeff n = relatorCoeff n


/-- Build the standard GS polynomial from generator and relator coefficients. -/
def gSPoly.standard (R : Type u) [Ring R] (d : R) (r : ℕ → R) :
    gSPoly R where
  generatorCoeff := d
  relatorCoeff := r
  coeff := standardGSCoefficients R d r
  coeff_spec := rfl
  coeff_zero := by simp [standardGSCoefficients]
  coeff_one := by simp [standardGSCoefficients]
  coeff_ge_two := by
    intro n hn
    exact standard_gs_coefficients R d r hn

@[simp] theorem gSPoly.standard_coeff (R : Type u) [Ring R]
    (d : R) (r : ℕ → R) (n : ℕ) :
    (gSPoly.standard R d r).coeff n = standardGSCoefficients R d r n := rfl


@[simp] theorem gSPoly.coeff_zero_apply (R : Type u) [Ring R]
    (P : gSPoly R) : P.coeff 0 = 1 := P.coeff_zero

@[simp] theorem gSPoly.coeff_one_apply (R : Type u) [Ring R]
    (P : gSPoly R) : P.coeff 1 = P.relatorCoeff 1 - P.generatorCoeff :=
  P.coeff_one

/-- In degrees at least two, a GS polynomial coefficient is the relator coefficient. -/
theorem gSPoly.coeff_ge_twoa (R : Type u) [Ring R]
    (P : gSPoly R) {n : ℕ} (hn : 2 ≤ n) :
    P.coeff n = P.relatorCoeff n := P.coeff_ge_two n hn

/-- GS polynomial, same structured representation as a coefficient sequence. -/
abbrev gsPolynomial (R : Type u) [Ring R] := gSPoly R

/-- Coefficient sequence of a GS polynomial is the standard coefficient sequence. -/
theorem gSPoly.coeff_spec_apply (R : Type u) [Ring R]
    (P : gSPoly R) (n : ℕ) :
    P.coeff n = standardGSCoefficients R P.generatorCoeff P.relatorCoeff n := by
  rw [P.coeff_spec]

/-- A positive evaluation parameter. -/
def pEParame (R : Type u) [Zero R] [Preorder R] (t : R) : Prop :=
  0 < t


/-- A positive evaluation parameter is nonzero in a preorder. -/
theorem pEParame.ne_zero {R : Type u} [Zero R] [Preorder R]
    {t : R} (h : pEParame R t) : t ≠ 0 :=
  ne_of_gt h


/-- Truncated evaluation of a coefficient sequence at a parameter. -/
def truncatedSeriesEval (R : Type u) [Semiring R] (coeff : ℕ → R) (t : R) (N : ℕ) : R :=
  Finset.sum (Finset.range (N + 1)) (fun n => coeff n * t ^ n)

@[simp] theorem truncated_series_zero {R : Type u} [Semiring R]
    (coeff : ℕ → R) (t : R) :
    truncatedSeriesEval R coeff t 0 = coeff 0 := by
  simp [truncatedSeriesEval]

/-- Extend a truncated series evaluation by one final coefficient. -/
theorem truncated_series_succ {R : Type u} [Semiring R]
    (coeff : ℕ → R) (t : R) (N : ℕ) :
    truncatedSeriesEval R coeff t (N + 1) =
      truncatedSeriesEval R coeff t N + coeff (N + 1) * t ^ (N + 1) := by
  simp [truncatedSeriesEval, Finset.sum_range_succ, Nat.add_assoc]

/-- Truncated evaluation of a structured GS polynomial. -/
def gSPoly.evalTruncated (R : Type u) [Ring R]
    (P : gSPoly R) (t : R) (N : ℕ) : R :=
  Finset.sum (Finset.range (N + 1)) (fun n => P.coeff n * t ^ n)

/-- The zeroth truncation of a standard GS polynomial is `1`. -/
@[simp] theorem gSPoly.standard_eval_zero (R : Type u) [Ring R]
    (d t : R) (r : ℕ → R) :
    (gSPoly.standard R d r).evalTruncated R t 0 = 1 := by
  simp [gSPoly.evalTruncated, gSPoly.standard, standardGSCoefficients]


/-- The structured evaluation agrees with the generic coefficient evaluator. -/
theorem gSPoly.evalTruncated_eq (R : Type u) [Ring R]
    (P : gSPoly R) (t : R) (N : ℕ) :
    P.evalTruncated R t N = truncatedSeriesEval R P.coeff t N := rfl


/-- Structured truncated evaluation satisfies the same one-step recurrence. -/
theorem gSPoly.evalTruncated_succ (R : Type u) [Ring R]
    (P : gSPoly R) (t : R) (N : ℕ) :
    P.evalTruncated R t (N + 1) =
      P.evalTruncated R t N + P.coeff (N + 1) * t ^ (N + 1) := by
  simp [gSPoly.evalTruncated, Finset.sum_range_succ, Nat.add_assoc]

@[simp] theorem gSPoly.evalTruncated_zero (R : Type u) [Ring R]
    (P : gSPoly R) (t : R) : P.evalTruncated R t 0 = P.coeff 0 := by
  simp [gSPoly.evalTruncated]

/-- Evaluation point for a GS test. -/
structure gTValue (R : Type u) [Zero R] [One R] [Preorder R] where
  t : R
  positive : 0 < t
  below_one : t < 1


/-- Package a test value from the usual open-unit inequalities. -/
def gTValue.mkOfBounds (R : Type u) [Zero R] [One R] [Preorder R]
    (t : R) (hpos : 0 < t) (hlt : t < 1) : gTValue R where
  t := t
  positive := hpos
  below_one := hlt

@[simp] theorem gTValue.mk_bounds_t {R : Type u} [Zero R] [One R] [Preorder R]
    (t : R) (hpos : 0 < t) (hlt : t < 1) :
    (gTValue.mkOfBounds R t hpos hlt).t = t := rfl

@[simp] theorem gTValue.mk_bounds_pos {R : Type u} [Zero R] [One R] [Preorder R]
    (t : R) (hpos : 0 < t) (hlt : t < 1) :
    (gTValue.mkOfBounds R t hpos hlt).positive = hpos := rfl

@[simp] theorem gTValue.mk_bounds_belowone {R : Type u} [Zero R] [One R] [Preorder R]
    (t : R) (hpos : 0 < t) (hlt : t < 1) :
    (gTValue.mkOfBounds R t hpos hlt).below_one = hlt := rfl

/-- A positive test value is automa nonzero in a preorder-like setting when supplied
as part of the package; this projection is named for downstream rewriting. -/
theorem gTValue.t_ne_zero {R : Type u} [Zero R] [One R] [Preorder R]
    (τ : gTValue R) : τ.t ≠ 0 :=
  ne_of_gt τ.positive


/-- A GS test value is positive. -/
theorem gTValue.positive_t {R : Type u} [Zero R] [One R] [Preorder R]
    (τ : gTValue R) : 0 < τ.t := τ.positive

/-- A GS test value lies below one. -/
theorem gTValue.lt_one {R : Type u} [Zero R] [One R] [Preorder R]
    (τ : gTValue R) : τ.t < 1 := τ.below_one

/-- Golod-Shafarevich defect at a test value, represented by a concrete
truncated evaluation witness that is already negative. -/
structure gSDefect (R : Type u) [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  polynomial : gSPoly R
  test : gTValue R
  cutoff : ℕ
  value : R
  value_eq : value = truncatedSeriesEval R polynomial.coeff test.t cutoff
  negative : value < 0

/-- Build a GS defect directly from a negative truncated evaluation. -/
def gSDefect.ofNegativeEval (R : Type u) [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (P : gSPoly R) (τ : gTValue R) (N : ℕ)
    (hneg : truncatedSeriesEval R P.coeff τ.t N < 0) : gSDefect R where
  polynomial := P
  test := τ
  cutoff := N
  value := truncatedSeriesEval R P.coeff τ.t N
  value_eq := rfl
  negative := hneg

/-- The stored defect value is the advertised truncated evaluation. -/
theorem gSDefect.value_spec {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R) :
    D.value = truncatedSeriesEval R D.polynomial.coeff D.test.t D.cutoff := D.value_eq

/-- A defect witnesses negativity of the corresponding truncated evaluation. -/
theorem gSDefect.eval_negative {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R) :
    truncatedSeriesEval R D.polynomial.coeff D.test.t D.cutoff < 0 := by
  rw [← D.value_eq]
  exact D.negative

@[simp] theorem gSDefect.neg_eval_value {R : Type u}
    [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (P : gSPoly R) (τ : gTValue R) (N : ℕ)
    (hneg : truncatedSeriesEval R P.coeff τ.t N < 0) :
    (gSDefect.ofNegativeEval R P τ N hneg).value =
      truncatedSeriesEval R P.coeff τ.t N := rfl

/-- The stored defect value is negative. -/
theorem gSDefect.value_negative {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R) : D.value < 0 :=
  D.negative

/-- One convolution term contributed by an active relator to the GS recurrence. -/
structure aCTerm (R : Type u) [Mul R] where
  targetDegree : ℕ
  depth : ℕ
  sourceDegree : ℕ
  source_degree_eq : sourceDegree + depth = targetDegree
  relatorCoeff : R
  hilbertCoeff : R
  active : depth ≤ targetDegree
  coefficient : R
  coefficient_eq : coefficient = relatorCoeff * hilbertCoeff


/-- The canonical convolution term at target degree `q` contributed by a relator
of depth `d`, with source degree `q-d`. -/
def aCTerm.ofDepth {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) : aCTerm R where
  targetDegree := q
  depth := d
  sourceDegree := q - d
  source_degree_eq := by exact Nat.sub_add_cancel h
  relatorCoeff := a
  hilbertCoeff := b
  active := h
  coefficient := a * b
  coefficient_eq := rfl

@[simp] theorem aCTerm.ofDepth_source {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) :
    (aCTerm.ofDepth q d h a b).sourceDegree = q - d := rfl

@[simp] theorem aCTerm.ofDepth_coeff {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) :
    (aCTerm.ofDepth q d h a b).coefficient = a * b := rfl

@[simp] theorem aCTerm.ofDepth_target {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) :
    (aCTerm.ofDepth q d h a b).targetDegree = q := rfl

@[simp] theorem aCTerm.ofDepth_depth {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) :
    (aCTerm.ofDepth q d h a b).depth = d := rfl

/-- The stored coefficient is always the product of the relator and Hilbert coefficients. -/
theorem aCTerm.coefficient_spec {R : Type u} [Mul R]
    (T : aCTerm R) :
    T.coefficient = T.relatorCoeff * T.hilbertCoeff := T.coefficient_eq

/-- The source degree plus depth recovers the target degree. -/
theorem aCTerm.source_add_depth {R : Type u} [Mul R]
    (T : aCTerm R) :
    T.sourceDegree + T.depth = T.targetDegree :=
  T.source_degree_eq

/-- The depth of an active convolution term is bounded by its target degree. -/
theorem aCTerm.depth_le_target {R : Type u} [Mul R]
    (T : aCTerm R) : T.depth ≤ T.targetDegree :=
  T.active

/-- The source degree of any active convolution term is the target minus depth. -/
theorem aCTerm.source_eq_sub {R : Type u} [Mul R]
    (T : aCTerm R) :
    T.sourceDegree = T.targetDegree - T.depth := by
  rw [← T.source_add_depth]
  simp

/-- For a canonical term, source plus depth simplifies to the target. -/
@[simp] theorem aCTerm.depth_source_adddepth {R : Type u} [Mul R]
    (q d : ℕ) (h : d ≤ q) (a b : R) :
    (aCTerm.ofDepth q d h a b).sourceDegree +
      (aCTerm.ofDepth q d h a b).depth = q := by
  exact Nat.sub_add_cancel h


/-- A filtration-compatible quotient. -/
structure fCQuot (G : Type u) [Group G] where
  filtration : DFilt G
  quotient : nSubgro G
  level : ℕ
  compatible : quotient.carrier = filtration level
  projection : G →* quotientGroup quotient := QuotientGroup.mk' quotient.carrier
  /-- The displayed projection is the canonical quotient map, not an arbitrary
  epimorphism with the same codomain. -/
  projection_canonical : projection = QuotientGroup.mk' quotient.carrier
  projection_surjective : Function.Surjective projection
  kernel_eq : MonoidHom.ker projection = quotient.carrier
  finite_quotient : Finite (quotientGroup quotient)


/-- The canonical compatible quotient attached to a finite filtration term. -/
def fCQuot.ofTerm {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F n))) :
    fCQuot G where
  filtration := F
  quotient := filtrationNormalTerm F n
  level := n
  compatible := rfl
  projection := QuotientGroup.mk' (F n)
  projection_canonical := rfl
  projection_surjective := by
    simpa using QuotientGroup.mk'_surjective (F n)
  kernel_eq := by
    ext g
    change (QuotientGroup.mk' (F n)) g = 1 ↔ g ∈ F n
    exact QuotientGroup.eq_one_iff (N := F n) g
  finite_quotient := hfin

@[simp] theorem fCQuot.ofTerm_level {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F n))) :
    (fCQuot.ofTerm F n hfin).level = n := rfl

@[simp] theorem fCQuot.ofTerm_filtration {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F n))) :
    (fCQuot.ofTerm F n hfin).filtration = F := rfl

@[simp] theorem fCQuot.term_projection_apply {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F n))) (g : G) :
    (fCQuot.ofTerm F n hfin).projection g = QuotientGroup.mk' (F n) g := rfl

/-- Compatible quotients really have the filtration term as kernel. -/
theorem fCQuot.mem_kernel_iff {G : Type u} [Group G]
    (Q : fCQuot G) (g : G) :
    g ∈ MonoidHom.ker Q.projection ↔ g ∈ Q.filtration Q.level := by
  rw [Q.kernel_eq, Q.compatible]

/-- The canonical projection of a compatible quotient kills exactly its level term. -/
theorem fCQuot.projection_eq_oneiff {G : Type u} [Group G]
    (Q : fCQuot G) (g : G) :
    Q.projection g = 1 ↔ g ∈ Q.filtration Q.level := by
  change g ∈ MonoidHom.ker Q.projection ↔ g ∈ Q.filtration Q.level
  exact Q.mem_kernel_iff g


/-- The quotient subgroup of a compatible quotient is the recorded filtration term. -/
theorem fCQuot.quotient_eq_term {G : Type u} [Group G]
    (Q : fCQuot G) : Q.quotient.carrier = Q.filtration Q.level :=
  Q.compatible

/-- The displayed projection is canonical. -/
theorem fCQuot.projection_eq_canonical {G : Type u} [Group G]
    (Q : fCQuot G) :
    Q.projection = QuotientGroup.mk' Q.quotient.carrier :=
  Q.projection_canonical

/-- The quotient in a compatible quotient package is finite. -/
theorem fCQuot.finite_quotient' {G : Type u} [Group G]
    (Q : fCQuot G) : Finite (quotientGroup Q.quotient) :=
  Q.finite_quotient

/-- If two compatible quotients come from the same filtration and the target is at
an earlier level, there is the canonical transition map between them. -/
noncomputable def fCQuot.transition {G : Type u} [Group G]
    (Q R : fCQuot G) (hF : Q.filtration = R.filtration)
    (hle : R.level ≤ Q.level) : quotientGroup Q.quotient →* quotientGroup R.quotient :=
  quotientMapLE Q.quotient R.quotient (by
    intro x hx
    have hxQ : x ∈ Q.filtration Q.level := by
      rw [Q.compatible] at hx
      exact hx
    have hxEarlier : x ∈ Q.filtration R.level :=
      DFilt.mono_membership Q.filtration hle hxQ
    rw [R.compatible]
    rwa [← hF])

@[simp] theorem fCQuot.transition_mk {G : Type u} [Group G]
    (Q R : fCQuot G) (hF : Q.filtration = R.filtration)
    (hle : R.level ≤ Q.level) (g : G) :
    fCQuot.transition Q R hF hle
        (QuotientGroup.mk' Q.quotient.carrier g) =
      QuotientGroup.mk' R.quotient.carrier g := by
  unfold fCQuot.transition
  exact quotient_mk Q.quotient R.quotient _ g

/-- Transition maps commute with the displayed quotient projections. -/
theorem fCQuot.transition_projection {G : Type u} [Group G]
    (Q R : fCQuot G) (hF : Q.filtration = R.filtration)
    (hle : R.level ≤ Q.level) (g : G) :
    fCQuot.transition Q R hF hle (Q.projection g) = R.projection g := by
  rw [Q.projection_canonical, R.projection_canonical]
  exact fCQuot.transition_mk Q R hF hle g

/-- Surjectivity of the displayed projection, as a named theorem. -/
theorem fCQuot.projection_surj {G : Type u} [Group G]
    (Q : fCQuot G) : Function.Surjective Q.projection :=
  Q.projection_surjective

/-- The canonical cutoff quotient also yields a filtration-compatible quotient. -/
def cDN.toCompatible {G : Type u} [Group G]
    (Q : cDN G)
    (hcanon : Q.projection = QuotientGroup.mk' Q.quotient.carrier)
    (hsurj : Function.Surjective Q.projection)
    (hker : MonoidHom.ker Q.projection = Q.quotient.carrier) :
    fCQuot G where
  filtration := Q.filtration
  quotient := Q.quotient
  level := Q.N
  compatible := Q.kernel_is_term
  projection := Q.projection
  projection_canonical := hcanon
  projection_surjective := hsurj
  kernel_eq := hker
  finite_quotient := Q.finite_quotient


/-- A low-degree isomorphism between graded families. -/
structure lDIsomor (A : ℕ → Type u) (B : ℕ → Type v) where
  cutoff : ℕ
  equiv : ∀ n, n ≤ cutoff → A n ≃ B n
  sourceTransition : ∀ n, A (n + 1) → A n
  targetTransition : ∀ n, B (n + 1) → B n
  commute : ∀ n (h : n + 1 ≤ cutoff) (x : A (n + 1)),
    equiv n (Nat.le_trans (Nat.le_succ n) h) (sourceTransition n x) =
      targetTransition n (equiv (n + 1) h x)

/-- Identity low-degree isomorphism for a graded family with chosen transitions. -/
def lDIsomor.refl (A : ℕ → Type u) (cutoff : ℕ)
    (τ : ∀ n, A (n + 1) → A n) : lDIsomor A A where
  cutoff := cutoff
  equiv := fun _ _ => Equiv.refl _
  sourceTransition := τ
  targetTransition := τ
  commute := by intro n h x; rfl

/-- Restrict a low-degree isomorphism to a smaller cutoff. -/
def lDIsomor.restrict {A : ℕ → Type u} {B : ℕ → Type v}
    (L : lDIsomor A B) (c : ℕ) (hc : c ≤ L.cutoff) :
    lDIsomor A B where
  cutoff := c
  equiv := fun n hn => L.equiv n (Nat.le_trans hn hc)
  sourceTransition := L.sourceTransition
  targetTransition := L.targetTransition
  commute := by
    intro n hn x
    exact L.commute n (Nat.le_trans hn hc) x

@[simp] theorem lDIsomor.refl_cutoff (A : ℕ → Type u) (cutoff : ℕ)
    (τ : ∀ n, A (n + 1) → A n) :
    (lDIsomor.refl A cutoff τ).cutoff = cutoff := rfl

@[simp] theorem lDIsomor.restrict_cutoff {A : ℕ → Type u} {B : ℕ → Type v}
    (L : lDIsomor A B) (c : ℕ) (hc : c ≤ L.cutoff) :
    (L.restrict c hc).cutoff = c := rfl

@[simp] theorem lDIsomor.refl_equiv_apply (A : ℕ → Type u) (cutoff : ℕ)
    (τ : ∀ n, A (n + 1) → A n) {n : ℕ} (h : n ≤ cutoff) (x : A n) :
    (lDIsomor.refl A cutoff τ).equiv n h x = x := rfl

/-- Obstruction to preserving exact depth: a concrete element whose image under a
filtered map has strictly smaller exact depth. -/
structure dLObstru {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) (φ : G →* H) where
  element : G
  originalDepth : ℕ
  loweredDepth : ℕ
  original_exact : exactDepth F element originalDepth
  image_exact : exactDepth E (φ element) loweredDepth
  lowers : loweredDepth < originalDepth

/-- A depth-lowering obstruction records a strict drop in depth. -/
theorem dLObstru.depth_lt {G : Type u} {H : Type v} [Group G] [Group H]
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (O : dLObstru F E φ) : O.loweredDepth < O.originalDepth :=
  O.lowers

/-- The original element has the recorded exact depth. -/
theorem dLObstru.original_exact_depth {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (O : dLObstru F E φ) :
    exactDepth F O.element O.originalDepth :=
  O.original_exact

/-- The image has the recorded lower exact depth. -/
theorem dLObstru.image_exact_depth {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (O : dLObstru F E φ) :
    exactDepth E (φ O.element) O.loweredDepth :=
  O.image_exact



end Group
end Towers

/-!
## Statements migrated from `Towers.Theorems`

These declarations keep their historical `Towers.Theorems` namespace while living
next to the API they describe.
-/

namespace Towers
namespace Theorems

open Towers.Group
open Towers.Algebra
open Towers.Topology
open scoped BigOperators

universe u v w x

/-- A coefficient sequence has finite support from some degree onward. -/
def SeriesFiniteSupport {R : Type u} [Zero R] (H : ℕ → R) : Prop :=
  ∃ N, ∀ n, N ≤ n → H n = 0
/-- A coefficient sequence is pointwise nonnegative. -/
def CoefficientsNonnegative {R : Type u} [Zero R] [Preorder R] (H : ℕ → R) : Prop :=
  ∀ n, 0 ≤ H n
/-- A nonnegative evaluation parameter for finite truncated evaluations. -/
def nonnegativeEvaluationParameter (R : Type u) [Zero R] [Preorder R] (t : R) : Prop :=
  0 ≤ t
/-- Two graded families agree up to a cutoff. -/
def AgreeUpTo (A : ℕ → Type u) (B : ℕ → Type v) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → Nonempty (A n ≃ B n)
/-- A degreewise predicate holds in all sufficiently high degrees. -/
def HoldsHighDegrees (threshold : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ n, threshold ≤ n → P n
/-- Truncated evaluations of a coefficient sequence are all nonnegative. -/
def TruncatedEvaluationsNonnegative {R : Type u} [Semiring R] [Preorder R]
    (H : ℕ → R) (t : R) : Prop :=
  ∀ N, 0 ≤ truncatedSeriesEval R H t N
/-- Finite support makes truncated evaluations eventually constant. -/
def TruncatedEventuallyConstant {R : Type u} [Semiring R]
    (H : ℕ → R) (t : R) : Prop :=
  ∃ N, ∀ M, N ≤ M → truncatedSeriesEval R H t M = truncatedSeriesEval R H t N
/-- A linearization is known to detect whether a relator has depth at least two. -/
def LinearizationDetectsTwo {R : Type u} {α : Type v} [Semiring R]
    (_relator : FreeGroup α) (linear : α → R) (depthAtLeastTwo : Prop) : Prop :=
  (∀ a, linear a = 0) ↔ depthAtLeastTwo
/-- The initial Fox form does not depend on the chosen representative data. -/
def FormRepresentativeInvariant {R : Type u} {α : Type v} [Ring R]
    (F G : iFForm R α) : Prop :=
  F.relator = G.relator → F.degree = G.degree → F.coeff = G.coeff
/-- The degree of an initial Fox form is compatible with a relator-depth function. -/
def FoxFormCompatible {R : Type u} {α : Type v} [Ring R]
    (depth : FreeGroup α → ℕ) (F : iFForm R α) : Prop :=
  F.degree + 1 = depth F.relator
/-- High-degree Fox exactness, using the actual linear map kernel and range. -/
def FoxHighExact {R : Type u} [Semiring R] (F : fIMap R) : Prop :=
  HoldsHighDegrees F.threshold (fun n =>
    letI := F.addDomain n; letI := F.modDomain n
    letI := F.addCodomain n; letI := F.modCodomain n
    Function.Surjective (F.map n) ∧ LinearMap.ker (F.map n) = ⊥)
/-- Initial Fox forms do not depend on representative choices at fixed depth. -/
theorem formIndependentRepresentative {R : Type u} {α : Type v} [Ring R]
    (F G : iFForm R α)
    (hrel : F.relator = G.relator) (_hdeg : F.degree = G.degree) :
    F.coeff = G.coeff
  := by
  funext a
  simp [iFForm.coeff, initialFoxCoefficients, hrel]
/-- Vanishing degree-one linearization is equivalent to depth at least two when
the supplied linearization is known to detect that depth predicate. -/
theorem linearizationLeastTwo {R : Type u} {α : Type v} [Semiring R]
    (relator : FreeGroup α) (linear : α → R) (depthAtLeastTwo : Prop)
    (hlinear : LinearizationDetectsTwo relator linear depthAtLeastTwo) :
    (∀ a, linear a = 0) ↔ depthAtLeastTwo
  := by
  simpa [LinearizationDetectsTwo] using hlinear

private lemma prime_dvd_ne {p a n : ℕ}
    (hp : Nat.Prime p) (ha1 : a ≠ 1) (hdiv : a ∣ p ^ n) :
    p ∣ a := by
  cases n with
  | zero =>
      exfalso
      have h1 : a ∣ 1 := by simpa using hdiv
      exact ha1 (Nat.dvd_one.mp h1)
  | succ n =>
      obtain ⟨q, hqprime, hqdiva⟩ := Nat.exists_prime_and_dvd ha1
      have hqdivpow : q ∣ p ^ (n + 1) := dvd_trans hqdiva hdiv
      have hqdivp : q ∣ p := hqprime.dvd_of_dvd_pow hqdivpow
      have hqeqp : q = p := Nat.prime_dvd_prime_iff_eq hqprime hp |>.mp hqdivp
      simpa [hqeqp] using hqdiva

private def zeroOrNonzero (V : Type*) [Zero V] [DecidableEq V] :
    V ≃ Option {v : V // v ≠ 0} where
  toFun v := if h : v = 0 then none else some ⟨v, h⟩
  invFun
    | none => 0
    | some v => v.1
  left_inv := by
    intro v
    by_cases h : v = 0 <;> simp [h]
  right_inv := by
    intro v
    cases v with
    | none => simp
    | some v => simp [v.2]

private lemma zmod_module_nontrivial {p : ℕ} (hp : Nat.Prime p)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Fintype V] [Nontrivial V] :
    p ∣ Fintype.card V := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card V = p ^ Module.finrank (ZMod p) V := by
    simpa [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := V))
  cases hdim : Module.finrank (ZMod p) V with
  | zero =>
      exfalso
      have hcard1 : Fintype.card V = 1 := by simp [hcard, hdim]
      have hsub : Subsingleton V :=
        Fintype.card_le_one_iff_subsingleton.mp (by simp [hcard1])
      obtain ⟨x, y, hxy⟩ := exists_pair_ne V
      exact hxy (Subsingleton.elim x y)
  | succ d =>
      rw [hcard, hdim, pow_succ]
      exact dvd_mul_left p (p ^ d)

private lemma nonzero_zmod_module {p : ℕ} (hp : Nat.Prime p)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Fintype V] [DecidableEq V]
    [Nontrivial V] :
    ¬ p ∣ Fintype.card {v : V // v ≠ 0} := by
  classical
  have hV : p ∣ Fintype.card V :=
    zmod_module_nontrivial (p := p) hp V
  intro hX
  have hcardOpt :
      Fintype.card V = Fintype.card (Option {v : V // v ≠ 0}) :=
    Fintype.card_congr (zeroOrNonzero V)
  have hcard :
      Fintype.card V = Fintype.card {v : V // v ≠ 0} + 1 := by
    simpa using hcardOpt
  have hsum : p ∣ Fintype.card {v : V // v ≠ 0} + 1 := by
    rwa [hcard] at hV
  have hone : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right hX).mpr hsum
  exact hp.not_dvd_one hone

private lemma fixed_point_card {p : ℕ} {H X : Type*}
    [Group H] [Fintype H] [MulAction H X] [Fintype X]
    (hp : Nat.Prime p) (hH : ∃ n : ℕ, Fintype.card H = p ^ n)
    (hX : ¬ p ∣ Fintype.card X) :
    ∃ x : X, ∀ h : H, h • x = x := by
  classical
  rcases hH with ⟨n, hcardH⟩
  by_contra hnofix
  push Not at hnofix
  let rel := MulAction.orbitRel H X
  let q : X → Quotient rel := Quotient.mk rel
  have hfiber_dvd :
      ∀ c : Quotient rel, p ∣ Fintype.card {x : X // q x = c} := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    let e : {y : X // q y = q x} ≃ MulAction.orbit H x :=
    {
      toFun y := by
        refine ⟨y.1, ?_⟩
        exact Quotient.exact y.2
      invFun y := by
        refine ⟨y.1, ?_⟩
        exact Quotient.sound y.2
      left_inv := by intro y; ext; rfl
      right_inv := by intro y; ext; rfl
    }
    haveI : Nonempty (MulAction.orbit H x) := ⟨⟨x, ⟨1, by simp⟩⟩⟩
    have horbit1 : Fintype.card (MulAction.orbit H x) ≠ 1 := by
      intro h1
      have hsub : Subsingleton (MulAction.orbit H x) :=
        Fintype.card_le_one_iff_subsingleton.mp (by simp [h1])
      have hxfix : ∀ h : H, h • x = x := by
        intro h
        have hEq :
            (⟨h • x, ⟨h, rfl⟩⟩ : MulAction.orbit H x) =
              ⟨x, ⟨1, by simp⟩⟩ := Subsingleton.elim _ _
        exact congrArg Subtype.val hEq
      rcases hnofix x with ⟨h, hh⟩
      exact hh (hxfix h)
    have hstab :
        Fintype.card (MulAction.orbit H x) *
            Fintype.card (MulAction.stabilizer H x) =
          Fintype.card H := by
      simpa using MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := H) x
    have hdivpow : Fintype.card (MulAction.orbit H x) ∣ p ^ n := by
      refine ⟨Fintype.card (MulAction.stabilizer H x), ?_⟩
      exact (hstab.trans hcardH).symm
    have hpdivorbit : p ∣ Fintype.card (MulAction.orbit H x) :=
      prime_dvd_ne hp horbit1 hdivpow
    rw [Fintype.card_congr e]
    exact hpdivorbit
  have hsum :
      Fintype.card X =
        ∑ c : Quotient rel, Fintype.card {x : X // q x = c} :=
    by
      have h :=
        (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset X))
          (t := (Finset.univ : Finset (Quotient rel))) (f := q)
          (by intro x hx; simp))
      have h' :
          (Finset.univ : Finset X).card =
            ∑ c : Quotient rel,
              ((Finset.univ : Finset X).filter fun x => q x = c).card := by
        simpa only [Finset.mem_univ, if_true] using h
      change (Finset.univ : Finset X).card =
        ∑ c : Quotient rel, Fintype.card {x : X // q x = c}
      rw [h']
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact (Fintype.card_subtype (fun x : X => q x = c)).symm
  have hdivX : p ∣ Fintype.card X := by
    rw [hsum]
    exact Finset.dvd_sum (s := Finset.univ) (fun c _ => hfiber_dvd c)
  exact hX hdivX

private lemma ne_vector_card {p : ℕ} {H V : Type*}
    [Group H] [Fintype H]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    [MulAction H V] (hp : Nat.Prime p)
    (hH : ∃ n : ℕ, Fintype.card H = p ^ n)
    (hzero : ∀ h : H, h • (0 : V) = 0) [Nontrivial V] :
    ∃ v : V, v ≠ 0 ∧ ∀ h : H, h • v = v := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidableEq V := Classical.decEq V
  let X := {v : V // v ≠ 0}
  letI : MulAction H X :=
  {
    smul h x := by
      refine ⟨h • x.1, ?_⟩
      intro hx0
      apply x.2
      calc
        x.1 = h⁻¹ • (h • x.1) := by simp
        _ = h⁻¹ • (0 : V) := by rw [hx0]
        _ = 0 := hzero h⁻¹
    one_smul x := by
      ext
      exact one_smul H x.1
    mul_smul h₁ h₂ x := by
      ext
      exact mul_smul h₁ h₂ x.1
  }
  have hnot : ¬ p ∣ Fintype.card X := by
    simpa [X] using nonzero_zmod_module (p := p) hp V
  obtain ⟨x, hx⟩ :=
    fixed_point_card (p := p) (H := H) (X := X) hp hH hnot
  exact ⟨x.1, x.2, fun h => congrArg Subtype.val (hx h)⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass search for the group-algebra scalar action needs extra room.
private noncomputable def leftRegularLinear {p : ℕ} {G : Type u} [Group G]
    (J : Ideal (MonoidAlgebra (ZMod p) G)) (g : G) :
    J →ₗ[ZMod p] J where
  toFun x :=
    ⟨MonoidAlgebra.of (ZMod p) G g * (x : MonoidAlgebra (ZMod p) G),
      J.mul_mem_left _ x.2⟩
  map_add' := by
    intro x y
    ext
    simp [mul_add]
  map_smul' := by
    intro r x
    ext
    simp [_root_.Algebra.smul_def]

set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass search for the group-algebra scalar action needs extra room.
private noncomputable def leftIdealLinear {p : ℕ} {G : Type u} [Group G]
    (J : Ideal (MonoidAlgebra (ZMod p) G)) (x : J) :
    MonoidAlgebra (ZMod p) G →ₗ[ZMod p] J where
  toFun a := ⟨a * (x : MonoidAlgebra (ZMod p) G), J.mul_mem_left _ x.2⟩
  map_add' := by
    intro a b
    ext
    simp [add_mul]
  map_smul' := by
    intro r a
    ext
    simp [_root_.Algebra.smul_def, mul_assoc]

private noncomputable instance dualRegularAction {p : ℕ} {G : Type u} [Group G]
    (J : Ideal (MonoidAlgebra (ZMod p) G)) :
    MulAction G (J →ₗ[ZMod p] ZMod p) where
  smul g φ := φ.comp (leftRegularLinear J g⁻¹)
  one_smul φ := by
    ext x
    apply congrArg φ
    ext
    simp [leftRegularLinear]
  mul_smul g h φ := by
    ext x
    apply congrArg φ
    ext
    simp [leftRegularLinear, mul_assoc]

private lemma left_invariant_form {p : ℕ} {G : Type u} [Group G] [Fintype G]
    (hp : Nat.Prime p) (hcardG : ∃ n : ℕ, Fintype.card G = p ^ n)
    (J : Ideal (MonoidAlgebra (ZMod p) G)) (hJne : J ≠ ⊥) :
    ∃ φ : J →ₗ[ZMod p] ZMod p, φ ≠ 0 ∧
      ∀ g : G, ∀ x : J, φ (leftRegularLinear J g x) = φ x := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : DecidableEq G := Classical.typeDecidableEq G
  letI : Fintype (MonoidAlgebra (ZMod p) G) :=
    by
      dsimp [MonoidAlgebra]
      infer_instance
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype (J →ₗ[ZMod p] ZMod p) :=
    Fintype.ofInjective
      (fun φ : J →ₗ[ZMod p] ZMod p => (φ : J → ZMod p))
      (by
        intro φ ψ h
        ext x
        exact congrFun h x)
  have hJnonzero : ∃ x : J, x ≠ 0 := by
    by_contra h
    apply hJne
    ext a
    constructor
    · intro ha
      have hall : ∀ x : J, x = 0 := by
        intro x
        by_contra hx
        exact h ⟨x, hx⟩
      have hx0 := hall ⟨a, ha⟩
      simpa using congrArg Subtype.val hx0
    · intro ha
      rw [ha]
      exact J.zero_mem
  rcases hJnonzero with ⟨x, hx⟩
  obtain ⟨φ₀, hφ₀x⟩ :=
    Module.Projective.exists_dual_ne_zero (ZMod p) hx
  have hφ₀ne : φ₀ ≠ 0 := by
    intro hφ
    simp [hφ] at hφ₀x
  letI : Nontrivial (J →ₗ[ZMod p] ZMod p) := ⟨⟨φ₀, 0, hφ₀ne⟩⟩
  obtain ⟨φ, hφne, hfix⟩ :=
    ne_vector_card (p := p) (H := G)
      (V := J →ₗ[ZMod p] ZMod p) hp hcardG
      (by intro g; ext x; rfl)
  refine ⟨φ, hφne, ?_⟩
  intro g x
  have h := congrArg (fun ψ : J →ₗ[ZMod p] ZMod p => ψ x) (hfix g⁻¹)
  change φ (leftRegularLinear J ((g⁻¹)⁻¹) x) = φ x at h
  simpa using h

private lemma left_invariant_mul {p : ℕ} {G : Type u} [Group G]
    (J : Ideal (MonoidAlgebra (ZMod p) G)) (φ : J →ₗ[ZMod p] ZMod p)
    (hinv : ∀ g : G, ∀ x : J, φ (leftRegularLinear J g x) = φ x)
    (a : MonoidAlgebra (ZMod p) G) (x : J) :
    φ ⟨a * (x : MonoidAlgebra (ZMod p) G), J.mul_mem_left a x.2⟩ =
      (Towers.GroupAlgebra.augmentation (ZMod p) G a) * φ x := by
  classical
  let L : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p :=
    φ.comp (leftIdealLinear J x)
  let R : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p :=
  { toFun := fun a => (Towers.GroupAlgebra.augmentation (ZMod p) G a) * φ x
    map_add' := by intro a b; simp [map_add, add_mul]
    map_smul' := by
      intro r a
      simp [_root_.Algebra.smul_def, mul_assoc, Towers.GroupAlgebra.augmentation,
        Towers.GroupAlgebra.trivialCharacter] }
  have hLR : L = R := by
    ext g
    simpa [L, R, leftIdealLinear, leftRegularLinear,
      Towers.GroupAlgebra.augmentation, Towers.GroupAlgebra.trivialCharacter] using hinv g x
  exact congrArg (fun f : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p => f a) hLR

set_option synthInstance.maxHeartbeats 1000000 in
-- Simplifying the auxiliary ideal requires deeper typeclass normalization.
set_option maxHeartbeats 2000000 in
-- The proof also needs more elaboration time after typeclass synthesis.
private lemma ne_self_bot {p : ℕ} {G : Type u}
    [Group G] [Fintype G] (hp : Nat.Prime p)
    (hcardG : ∃ n : ℕ, Fintype.card G = p ^ n)
    (J : Ideal (MonoidAlgebra (ZMod p) G)) (hJne : J ≠ ⊥) :
    Towers.Algebra.augmentationIdeal (ZMod p) G * J ≠ J := by
  classical
  obtain ⟨φ, hφne, hinv⟩ :=
    left_invariant_form (p := p) (G := G) hp hcardG J hJne
  let K : Ideal (MonoidAlgebra (ZMod p) G) :=
  { carrier := {a | ∃ ha : a ∈ J, φ ⟨a, ha⟩ = 0}
    zero_mem' := by
      refine ⟨J.zero_mem, ?_⟩
      change φ (0 : J) = 0
      exact φ.map_zero
    add_mem' := by
      intro a b ha hb
      rcases ha with ⟨haJ, hφa⟩
      rcases hb with ⟨hbJ, hφb⟩
      refine ⟨J.add_mem haJ hbJ, ?_⟩
      simpa [hφa, hφb] using
        (φ.map_add (⟨a, haJ⟩ : J) (⟨b, hbJ⟩ : J))
    smul_mem' := by
      intro r a ha
      rcases ha with ⟨haJ, hφa⟩
      refine ⟨J.mul_mem_left r haJ, ?_⟩
      have h :=
        left_invariant_mul J φ hinv r (⟨a, haJ⟩ : J)
      simpa [hφa] using h }
  have hIJleK : Towers.Algebra.augmentationIdeal (ZMod p) G * J ≤ K := by
    refine Ideal.mul_le.mpr ?_
    intro a ha b hb
    refine ⟨J.mul_mem_left a hb, ?_⟩
    have haug : Towers.GroupAlgebra.augmentation (ZMod p) G a = 0 := by
      simpa [Towers.Algebra.augmentationIdeal, Towers.GroupAlgebra.augmentationIdeal] using ha
    have h :=
      left_invariant_mul J φ hinv a (⟨b, hb⟩ : J)
    simpa [haug] using h
  intro hEq
  have hJleK : J ≤ K := by
    intro a ha
    have ha' : a ∈ Towers.Algebra.augmentationIdeal (ZMod p) G * J := by
      simpa [hEq] using ha
    exact hIJleK ha'
  have hex : ∃ x : J, φ x ≠ 0 := by
    by_contra h
    apply hφne
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  rcases hex with ⟨x, hx⟩
  rcases hJleK x.2 with ⟨hxJ, hφx⟩
  have hx' : (⟨x.1, hxJ⟩ : J) = x := Subtype.ext rfl
  exact hx (by simpa [hx'] using hφx)

private lemma pow_augmentation_bot {p : ℕ} {G : Type u}
    [Group G] [Fintype G] (hp : Nat.Prime p)
    (hcardG : ∃ n : ℕ, Fintype.card G = p ^ n) :
    ∃ n : ℕ, (Towers.Algebra.augmentationIdeal (ZMod p) G) ^ n = ⊥ := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : DecidableEq G := Classical.typeDecidableEq G
  letI : Fintype (MonoidAlgebra (ZMod p) G) :=
    by
      dsimp [MonoidAlgebra]
      infer_instance
  let A := MonoidAlgebra (ZMod p) G
  let I : Ideal A := Towers.Algebra.augmentationIdeal (ZMod p) G
  haveI : I.IsTwoSided := by
    dsimp [I, Towers.Algebra.augmentationIdeal, Towers.GroupAlgebra.augmentationIdeal]
    infer_instance
  let f : ℕ → ℕ := fun n => Fintype.card ↥(I ^ n)
  have hexMin : ∃ c : ℕ, ∃ n : ℕ, f n = c := ⟨f 0, ⟨0, rfl⟩⟩
  let c := Nat.find hexMin
  have hcSpec : ∃ n : ℕ, f n = c := Nat.find_spec hexMin
  rcases hcSpec with ⟨N, hN⟩
  have hcMin : ∀ d : ℕ, (∃ n : ℕ, f n = d) → c ≤ d := by
    intro d hd
    exact Nat.find_min' hexMin hd
  let J : Ideal A := I ^ N
  by_cases hJbot : J = ⊥
  · refine ⟨N, ?_⟩
    simpa [I, J]
      using hJbot
  · have hproper : I * J ≠ J := by
      simpa [I] using
        ne_self_bot (p := p) (G := G) hp hcardG J hJbot
    have hmul_le : I * J ≤ J := by
      refine Ideal.mul_le.mpr ?_
      intro a ha b hb
      exact J.mul_mem_left a hb
    let e : (I * J) ↪ J :=
    {
      toFun x := ⟨x.1, hmul_le x.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : J => (z : A)) hxy
    }
    have hnotSurj : ¬ Function.Surjective e := by
      intro hs
      apply hproper
      ext a
      constructor
      · intro ha
        exact hmul_le ha
      · intro ha
        rcases hs ⟨a, ha⟩ with ⟨y, hy⟩
        have hyval : y.1 = a := congrArg Subtype.val hy
        simpa [hyval] using y.2
    have hltCard : Fintype.card ↥(I * J) < Fintype.card ↥J :=
      Fintype.card_lt_of_injective_not_surjective e e.injective hnotSurj
    have hlt : f (N + 1) < f N := by
      change Fintype.card ↥(I ^ (N + 1)) < Fintype.card ↥(I ^ N)
      have hpows : I ^ (N + 1) = I * J := by
        change I ^ (N + 1) = I * I ^ N
        exact Ideal.IsTwoSided.pow_succ (I := I) N
      rw [hpows]
      exact hltCard
    have hge : f N ≤ f (N + 1) := by
      have := hcMin (f (N + 1)) ⟨N + 1, rfl⟩
      simpa [hN] using this
    exact False.elim ((not_lt_of_ge hge) hlt)
/-- The augmentation ideal of a finite p-group is nilpotent. -/
theorem nilpotencePGroups {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    ∃ N : nIIdeal (ZMod p) G,
      ∀ n, N.1 ≤ n → powersAugmentationIdeal (ZMod p) G n = ⊥
  := by
  classical
  rcases hG with ⟨hp, hfinG, hcardNat⟩
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Finite G := hfinG
  letI : Fintype G := Fintype.ofFinite G
  have hcardG : ∃ n : ℕ, Fintype.card G = p ^ n := by
    rcases hcardNat with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using hn
  have hnil : ∃ n : ℕ, powersAugmentationIdeal (ZMod p) G n = ⊥ := by
    simpa [powersAugmentationIdeal] using
      pow_augmentation_bot (p := p) (G := G) hp hcardG
  let P : ℕ → Prop := fun n => powersAugmentationIdeal (ZMod p) G n = ⊥
  have hP : ∃ n : ℕ, P n := hnil
  let n0 := Nat.find hP
  have hn0 : P n0 := Nat.find_spec hP
  have hmin : ∀ m, m < n0 → powersAugmentationIdeal (ZMod p) G m ≠ ⊥ := by
    intro m hm hmP
    exact (not_lt_of_ge (Nat.find_min' hP hmP)) hm
  let N : nIIdeal (ZMod p) G := ⟨n0, hn0, hmin⟩
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  dsimp [N]
  haveI : (Towers.Algebra.augmentationIdeal (ZMod p) G).IsTwoSided := by
    dsimp [Towers.Algebra.augmentationIdeal, Towers.GroupAlgebra.augmentationIdeal]
    infer_instance
  have hpows :
      Towers.Algebra.augmentationIdeal (ZMod p) G ^ (n0 + d) =
        Towers.Algebra.augmentationIdeal (ZMod p) G ^ n0 *
          Towers.Algebra.augmentationIdeal (ZMod p) G ^ d :=
    Ideal.IsTwoSided.pow_add (I := Towers.Algebra.augmentationIdeal (ZMod p) G) n0 d
  change Towers.Algebra.augmentationIdeal (ZMod p) G ^ (n0 + d) = ⊥
  rw [hpows]
  rw [show Towers.Algebra.augmentationIdeal (ZMod p) G ^ n0 = ⊥ by
    simpa [powersAugmentationIdeal] using hn0]
  simp
/-- Finite p-groups have finite-support Hilbert series. -/
theorem finiteSupport {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : algebraHilbertH R) (N : nIIdeal R G)
    (hcoeff : ∀ n, powersAugmentationIdeal R G n = ⊥ → H n = 0) :
    SeriesFiniteSupport H
  := by
  refine ⟨N.1, ?_⟩
  intro n hn
  exact hcoeff n (nilpotentHighLayers N.1 N.2.1 hn)
/-- A displayed low-degree comparison gives equivalences below any smaller cutoff. -/
theorem agreesLowDegrees
    {source : ℕ → Type u} {target : ℕ → Type v}
    (L : lDIsomor source target) {cutoff n : ℕ}
    (hcutoff : cutoff ≤ L.cutoff) :
    n ≤ cutoff → Nonempty (source n ≃ target n)
  := by
  intro hn
  exact ⟨L.equiv n (Nat.le_trans hn hcutoff)⟩
/-- Fox calculus supplies derivative degree estimates through a recorded estimate package. -/
theorem foxCalculusEstimates (E : fDEstima) :
    E.derivativeLowerBound + 1 ≤ E.relatorDepth
  := by
  exact E.succ_bound
/-- A concrete right augmentation degree is bounded by the derivative estimate. -/
theorem rightAugmentationDegree (E : fDEstima) {d : ℕ}
    (hd : E.derivativeDegree = some d) :
    E.derivativeLowerBound ≤ d
  := by
  exact E.bound_eq_some hd
/-- Truncated Fox/Jennings comparison in bounded degree, from a low-degree comparison. -/
theorem foxJenningsTheorem {source : ℕ → Type u} {target : ℕ → Type v}
    (L : lDIsomor source target) :
    AgreeUpTo source target L.cutoff
  := by
  intro n hn
  exact ⟨L.equiv n hn⟩
/-- A finite-degree consequence follows through an actual low-degree comparison. -/
theorem presentationSensitiveConsequence
    {source : ℕ → Type u} {target : ℕ → Type v}
    (L : lDIsomor source target) {cutoff n : ℕ}
    (hcutoff : cutoff ≤ L.cutoff) :
    n ≤ cutoff → Nonempty (source n ≃ target n)
  := by
  intro hn
  exact ⟨L.equiv n (Nat.le_trans hn hcutoff)⟩
/-- A depth-q relator estimate puts derivatives in augmentation degree at least `q - 1`. -/
theorem qIMinus (E : fDEstima) :
    E.derivativeLowerBound + 1 ≤ E.relatorDepth
  := by
  exact E.succ_bound
/-- The initial Fox form has degree q-1. -/
theorem formQ1 {R : Type u} {α : Type v} [Ring R]
    (F : iFForm R α) (depth : FreeGroup α → ℕ) {q : ℕ}
    (hcompat : FoxFormCompatible depth F) (hdepth : depth F.relator = q) :
    F.degree = q - 1
  := by
  have hq : F.degree + 1 = q := hcompat.trans hdepth
  omega
/-- Initial relation vectors are homogeneous in their recorded degree. -/
theorem initialVectorHomogeneous {R : Type u} {α : Type v} [Ring R]
    (V : iRVector R α) :
    V.initialForm.degree = V.degree
  := by
  exact V.initialForm_degree
/-- Fox initial maps land in syzygies. -/
theorem foxLandsSyzygies {R : Type u} [Semiring R]
    (F : fIMap R) (n : ℕ) (x : F.domain n) :
    (letI := F.addDomain n; letI := F.modDomain n
     letI := F.addCodomain n; letI := F.modCodomain n
     F.map n x = 0 → x ∈ LinearMap.ker (F.map n))
  := by
  intro hx
  exact hx
/-- Each active relator gives a syzygy. -/
theorem easyThatSyzygies {R : Type u} [Semiring R]
    (F : fIMap R) (n : ℕ) (x : F.domain n) :
    (letI := F.addDomain n; letI := F.modDomain n
     letI := F.addCodomain n; letI := F.modCodomain n
     F.map n x = 0 → x ∈ LinearMap.ker (F.map n))
  := by
  intro hx
  exact hx
/-- In high degrees, Fox initial maps generate all syzygies. -/
theorem highFoxSyzygies {R : Type u} [Semiring R]
    (F : fIMap R) :
    HoldsHighDegrees F.threshold (fun n => Function.Surjective (F.map n))
  := by
  exact fun n hn => F.surj_threshold_le n hn
/-- High-degree strict Fox exactness. -/
theorem highFoxExact {R : Type u} [Semiring R] (F : fIMap R) :
    ∀ n, F.threshold ≤ n →
      (letI := F.addDomain n; letI := F.modDomain n
       letI := F.addCodomain n; letI := F.modCodomain n
       LinearMap.ker (F.map n) = ⊥)
  := by
  exact fun n hn => F.lin_kereq_botabove n hn
/-- High-degree associated-graded relation module exactness, from explicit
high-degree exactness data. -/
theorem associatedGradedExactness {R : Type u} [Semiring R]
    {A B C : ℕ → Type v}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (B n)] [∀ n, AddCommMonoid (C n)]
    [∀ n, Module R (A n)] [∀ n, Module R (B n)] [∀ n, Module R (C n)]
    (f : ∀ n, A n →ₗ[R] B n) (g : ∀ n, B n →ₗ[R] C n) (threshold : ℕ)
    (h_exact : HoldsHighDegrees threshold (fun n =>
      LinearMap.range (f n) = LinearMap.ker (g n))) :
    HoldsHighDegrees threshold (fun n =>
      LinearMap.range (f n) = LinearMap.ker (g n))
  := by
  exact h_exact
/-- Converse syzygy generation by active relators. -/
theorem converseSyzygyGeneration {R : Type u} [Semiring R]
    (F : fIMap R) :
    HoldsHighDegrees F.threshold (fun n =>
      letI := F.addDomain n; letI := F.modDomain n
      letI := F.addCodomain n; letI := F.modCodomain n
      ∀ x : F.domain n, x ∈ LinearMap.ker (F.map n) → F.map n x = 0)
  := by
  intro n hn x hx
  exact hx
/-- Associated-graded relation modules are exact when their displayed degreewise
maps are exact. -/
theorem associatedModuleExactness {R : Type u} [Semiring R]
    {A B C : ℕ → Type v}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (B n)] [∀ n, AddCommMonoid (C n)]
    [∀ n, Module R (A n)] [∀ n, Module R (B n)] [∀ n, Module R (C n)]
    (f : ∀ n, A n →ₗ[R] B n) (g : ∀ n, B n →ₗ[R] C n)
    (h_exact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n)) :
    ∀ n, LinearMap.range (f n) = LinearMap.ker (g n)
  := by
  exact h_exact
/-- Fox maps respect relation-degree shifts. -/
theorem foxRespectsShifts {R : Type u} [Semiring R]
    (F : fIMap R) {n : ℕ} :
    (letI := F.addDomain n; letI := F.modDomain n
     letI := F.addCodomain n; letI := F.modCodomain n
     F.map n '' (Set.univ : Set (F.domain n)) ⊆ LinearMap.range (F.map n))
  := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩
/-- Presented relator Fox initial exactness in all sufficiently high degrees. -/
theorem presentedHighDegrees {R : Type u} [Semiring R]
    (F : fIMap R) :
    ∀ n, F.threshold ≤ n →
      (letI := F.addDomain n; letI := F.modDomain n
       letI := F.addCodomain n; letI := F.modCodomain n
       LinearMap.ker (F.map n) = ⊥)
  := by
  exact fun n hn => F.lin_kereq_botabove n hn
/-- The graded relation module is generated by its recorded initial relators. -/
theorem gradedGeneratedRelators {R : Type u} [Semiring R]
    (M : gRModule R) :
    ∀ n, letI := M.addPiece n; letI := M.modulePiece n;
      Submodule.span R (M.degreeGenerators n) = ⊤
  := by
  intro n
  exact M.span_eq_top n
/-- Finite p-group Hilbert series terminate. -/
theorem hilbertSeriesTerminates {p : ℕ} {G : Type u} [Group G]
    (H : algebraHilbertH (ZMod p))
    (N : nIIdeal (ZMod p) G)
    (hcoeff : ∀ n, powersAugmentationIdeal (ZMod p) G n = ⊥ → H n = 0) :
    SeriesFiniteSupport H
  := by
  exact finiteSupport H N hcoeff
/-- A graded relation module generated by its displayed homogeneous relators has
degreewise rank bounded by the cardinality of those relators. -/
theorem relationModuleInequality {R : Type u} [Semiring R] [StrongRankCondition R]
    (M : gRModule R) :
    cIneq
      (fun n =>
        letI := M.addPiece n
        letI := M.modulePiece n
        Module.rank R (M.piece n))
      (fun n => Cardinal.mk (M.degreeGenerators n))
  := by
  intro n
  letI := M.addPiece n
  letI := M.modulePiece n
  calc
    Module.rank R (M.piece n)
        = Module.rank R (Submodule.span R (M.degreeGenerators n)) := by
          rw [M.spans n, rank_top]
    _ ≤ Cardinal.mk (M.degreeGenerators n) := rank_span_le (R := R) (s := M.degreeGenerators n)
/-- Relation-module inequalities give a GS coefficient recurrence. -/
theorem recurrenceGsSeries {R : Type u} [Ring R]
    (generatorCoeff : R) (relatorCoeff : ℕ → R) (n : ℕ) :
    standardGSCoefficients R generatorCoeff relatorCoeff n =
      if n = 0 then 1 else if n = 1 then relatorCoeff 1 - generatorCoeff else relatorCoeff n
  := by
  rfl
/-- Hilbert-series inequality. -/
theorem hilbertSeriesInequality {R : Type u} [Preorder R]
    (lhs rhs : hilbertSeries R) (h : lhs ≤ rhs) :
    cIneq lhs rhs
  := by
  intro n
  exact h n
/-- Coefficientwise inequalities are the degreewise form of the Hilbert inequality. -/
theorem coefficientInequalities {R : Type u} [Preorder R]
    (lhs rhs : hilbertSeries R) :
    cIneq lhs rhs ↔ ∀ n, lhs n ≤ rhs n
  := by
  rfl
/-- Hilbert-series multiplication is coefficient convolution. -/
theorem hilbertConvolutionRule {R : Type u} [Semiring R]
    (a b : hilbertSeries R) (n : ℕ) :
    hilbertSeriesMul a b n = Finset.sum (Finset.range (n + 1)) (fun i => a i * b (n - i))
  := by
  rfl
/-- Relation coefficients control the GS coefficients in degrees at least two. -/
theorem relationInequalityGives {R : Type u} [Ring R] [Preorder R]
    (P : gSPoly R) :
    ∀ n, 2 ≤ n → P.coeff n ≤ P.relatorCoeff n
  := by
  intro n hn
  rw [P.coeff_ge_two n hn]
/-- Coefficientwise nonnegativity gives nonnegative finite truncated evaluations. -/
theorem coefficientwiseNonnegativityImplies {R : Type u}
    [Semiring R] [PartialOrder R] [IsOrderedRing R] (H : hilbertSeries R) {t : R} :
    CoefficientsNonnegative H → nonnegativeEvaluationParameter R t →
      TruncatedEvaluationsNonnegative H t
  := by
  intro hH ht
  have coeff_mul_pow_nonneg :
      ∀ (a : R), 0 ≤ a → ∀ n : ℕ, 0 ≤ a * t ^ n := by
    intro a ha n
    induction n with
    | zero =>
        simpa using ha
    | succ n ih =>
        simpa [pow_succ, mul_assoc] using mul_nonneg ih ht
  intro N
  exact Finset.sum_nonneg (by
    intro n _hn
    exact coeff_mul_pow_nonneg (H n) (hH n) n)
/-- A negative GS value rules out finiteness. -/
theorem negativeImpliesInfinitude {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R)
    (finite_support_gives_positivity :
      SeriesFiniteSupport D.polynomial.coeff →
        TruncatedEvaluationsNonnegative D.polynomial.coeff D.test.t) :
    ¬ SeriesFiniteSupport D.polynomial.coeff
  := by
  intro hfinite
  have hnonneg := finite_support_gives_positivity hfinite D.cutoff
  exact (not_le_of_gt D.eval_negative) hnonneg
/-- Finite support justifies evaluating coefficientwise inequalities. -/
theorem supportJustifiesEvaluation {R : Type u} [Semiring R] [Preorder R]
    (H : hilbertSeries R) {t : R} :
    SeriesFiniteSupport H → pEParame R t →
      TruncatedEventuallyConstant H t
  := by
  intro hfinite _ht
  rcases hfinite with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro M hNM
  induction M, hNM using Nat.le_induction with
  | base =>
      rfl
  | succ M hNM ih =>
      rw [truncated_series_succ, ih]
      have hzero : H (M + 1) = 0 := hN (M + 1) (Nat.le_trans hNM (Nat.le_succ M))
      simp [hzero]
/-- Negative polynomial values contradict finite-support positivity. -/
theorem gsContradictionValue {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R)
    (finite_support_gives_positivity :
      SeriesFiniteSupport D.polynomial.coeff →
        TruncatedEvaluationsNonnegative D.polynomial.coeff D.test.t) :
    SeriesFiniteSupport D.polynomial.coeff → False
  := by
  intro hfinite
  have hnonneg := finite_support_gives_positivity hfinite D.cutoff
  exact (not_le_of_gt D.eval_negative) hnonneg
/-- The final Golod-Shafarevich positivity/contradiction statement. -/
theorem gsPositivityContradiction {R : Type u} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (D : gSDefect R)
    (finite_support_gives_positivity :
      SeriesFiniteSupport D.polynomial.coeff →
        TruncatedEvaluationsNonnegative D.polynomial.coeff D.test.t) :
    ¬ SeriesFiniteSupport D.polynomial.coeff
  := by
  intro hfinite
  have hnonneg := finite_support_gives_positivity hfinite D.cutoff
  exact (not_le_of_gt D.eval_negative) hnonneg
/-- Active relator terms use the shifted Hilbert coefficient for their depth. -/
theorem activeMatchShifts {R : Type u} [Zero R]
    (H : hilbertSeries R) {n q : ℕ} (h : q ≤ n) :
    shiftedHilbertCoefficient 0 H n q = H (n - q)
  := by
  exact shifted_hilbert_coefficient 0 H h
/-- A sufficiently deep-kernel comparison supplies low-degree isomorphisms. -/
theorem deepGivesIsomorphism {A : ℕ → Type u} {B : ℕ → Type v}
    (L : lDIsomor A B) :
    AgreeUpTo A B L.cutoff
  := by
  intro n hn
  exact ⟨L.equiv n hn⟩
/-- A cutoff quotient comparison preserves low-degree layers through its cutoff. -/
theorem preservesLowLayers {A : ℕ → Type u} {B : ℕ → Type v}
    (L : lDIsomor A B) :
    AgreeUpTo A B L.cutoff
  := by
  exact deepGivesIsomorphism L
/-- Without a depth-lowering obstruction, the image cannot have smaller exact depth.

The stronger preservation claim is false: absence of a lower-depth image does not
rule out the image having larger exact depth, or no exact depth at all. -/
theorem absenceLoweringPreserves {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    {φ : G →* H} {x : G} {n : ℕ} :
    (¬ Nonempty (dLObstru F E φ)) → exactDepth F x n →
      ∀ ⦃m : ℕ⦄, exactDepth E (φ x) m → n ≤ m
  := by
  intro hno hx m hm
  by_contra hnm
  exact hno ⟨{
    element := x
    originalDepth := n
    loweredDepth := m
    original_exact := hx
    image_exact := hm
    lowers := Nat.lt_of_not_ge hnm
  }⟩
/-- Finite truncations suffice for bounded-degree claims. -/
theorem truncationSufficesClaims {R : Type u}
    (H : hilbertSeries R) (N : cutoffDegree) :
    ∃ T : tHSeries H N,
      ∀ (n : ℕ) (hn : n ≤ N), T.1 ⟨n, hn⟩ = H n
  := by
  refine ⟨⟨fun n => H n.1, ?_⟩, ?_⟩
  · intro n
    rfl
  · intro n hn
    rfl

end Theorems
end Towers
