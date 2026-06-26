import Towers.Group.PresentationDepth

namespace Towers
namespace Group

universe u v w

/-- A homomorphism preserving two filtrations. -/
structure fPHom {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) where
  hom : G →* H
  preserves : ∀ n x, x ∈ F n → hom x ∈ E n
  term_image_le : ∀ n, (F n).map hom ≤ E n

/-- Identity filtration-preserving homomorphism. -/
def fPHom.id {G : Type u} [Group G]
    (F : DFilt G) : fPHom F F where
  hom := MonoidHom.id G
  preserves := by intro n x hx; simpa using hx
  term_image_le := by
    intro n y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using hx

/-- Composition of filtration-preserving homomorphisms. -/
def fPHom.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : fPHom E D)
    (α : fPHom F E) : fPHom F D where
  hom := β.hom.comp α.hom
  preserves := by
    intro n x hx
    exact β.preserves n (α.hom x) (α.preserves n x hx)
  term_image_le := by
    intro n z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact β.preserves n (α.hom x) (α.preserves n x hx)

/-- Pointwise preservation of filtration terms, as a named lemma. -/
theorem fPHom.map_mem {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : fPHom F E) {n : ℕ} {x : G} (hx : x ∈ F n) :
    φ.hom x ∈ E n :=
  φ.preserves n x hx

/-- Image of each filtration term lies in the target term. -/
theorem fPHom.term_image_le' {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : fPHom F E) (n : ℕ) :
    (F n).map φ.hom ≤ E n :=
  φ.term_image_le n

@[simp] theorem fPHom.id_hom {G : Type u} [Group G]
    (F : DFilt G) :
    (fPHom.id F).hom = MonoidHom.id G := rfl

@[simp] theorem fPHom.comp_hom {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : fPHom E D)
    (α : fPHom F E) :
    (fPHom.comp β α).hom = β.hom.comp α.hom := rfl

@[simp] theorem fPHom.comp_apply {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : fPHom E D)
    (α : fPHom F E) (g : G) :
    (fPHom.comp β α).hom g = β.hom (α.hom g) := rfl

/-- A filtration-preserving surjection that is strict-on-terms in the weak sense of surjectivity. -/
structure sFSurjec {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) extends
    fPHom F E where
  surjective : Function.Surjective hom
  maps_onto_terms : DFilt.MapsOnto F E hom
  term_surjective : ∀ n (y : E n), ∃ x : F n, hom x.1 = y.1




/-- Identity map as a strict filtered surjection. -/
def sFSurjec.id {G : Type u} [Group G]
    (F : DFilt G) : sFSurjec F F where
  tofPHom := fPHom.id F
  surjective := by intro x; exact ⟨x, rfl⟩
  maps_onto_terms := by
    intro n
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  term_surjective := by
    intro n y
    exact ⟨y, rfl⟩


/-- Composition of strict filtered surjections is strict. -/
def sFSurjec.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : sFSurjec E D) (α : sFSurjec F E) :
    sFSurjec F D where
  tofPHom := fPHom.comp β.tofPHom α.tofPHom
  surjective := by
    intro z
    rcases β.surjective z with ⟨y, rfl⟩
    rcases α.surjective y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  maps_onto_terms := by
    intro n
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      exact β.preserves n (α.hom x) (α.preserves n x hx)
    · intro hz
      let zd : D n := ⟨z, hz⟩
      rcases β.term_surjective n zd with ⟨y, hy⟩
      rcases α.term_surjective n y with ⟨x, hx⟩
      refine ⟨x.1, x.2, ?_⟩
      change β.hom (α.hom x.1) = z
      rw [hx, hy]
  term_surjective := by
    intro n z
    rcases β.term_surjective n z with ⟨y, hy⟩
    rcases α.term_surjective n y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change β.hom (α.hom x.1) = z.1
    rw [hx, hy]

/-- A strict filtered surjection is surjective on the underlying groups. -/
theorem sFSurjec.surj {G : Type u} {H : Type v} [Group G] [Group H]
    {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) : Function.Surjective φ.hom :=
  φ.surjective

/-- A strict filtered surjection maps onto filtration terms. -/
theorem sFSurjec.maps_onto_terms' {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) : DFilt.MapsOnto F E φ.hom :=
  φ.maps_onto_terms

/-- Termwise surjectivity, exposed as a named accessor. -/
theorem sFSurjec.term_surj {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) (n : ℕ) (y : E n) :
    ∃ x : F n, φ.hom x.1 = y.1 :=
  φ.term_surjective n y

/-- Strict filtered surjections preserve membership in filtration terms. -/
theorem sFSurjec.map_mem {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) {n : ℕ} {x : G} (hx : x ∈ F n) :
    φ.hom x ∈ E n :=
  φ.preserves n x hx

@[simp] theorem sFSurjec.id_hom {G : Type u} [Group G]
    (F : DFilt G) :
    (sFSurjec.id F).hom = MonoidHom.id G := rfl

@[simp] theorem sFSurjec.comp_hom {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : sFSurjec E D) (α : sFSurjec F E) :
    (sFSurjec.comp β α).hom = β.hom.comp α.hom := rfl

@[simp] theorem sFSurjec.comp_apply {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : sFSurjec E D) (α : sFSurjec F E) (g : G) :
    (sFSurjec.comp β α).hom g = β.hom (α.hom g) := rfl

/-- The homomorphism induced on a filtration term by a filtration-preserving map. -/
def filtrationTermMap {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) (φ : G →* H)
    (hφ : ∀ n, (F n).map φ ≤ E n) (n : ℕ) : F n →* E n where
  toFun x := ⟨φ x.1, hφ n ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- The induced map on each filtration term of a strict filtered surjection is surjective. -/
theorem sFSurjec.termMap_surjective {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) (n : ℕ) :
    Function.Surjective (filtrationTermMap F E φ.hom φ.term_image_le n) := by
  intro y
  rcases φ.term_surjective n y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  ext
  exact hx

/-- The induced homomorphism on concrete graded quotient layers. -/
noncomputable def inducedLayerMap {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) (φ : G →* H)
    (hφ : ∀ n, (F n).map φ ≤ E n) (n : ℕ) :
    filtrationLayer F n →* filtrationLayer E n :=
  QuotientGroup.map _ _ (filtrationTermMap F E φ hφ n) (by
    intro x hx
    change φ x.1 ∈ E (n + 1)
    exact hφ (n + 1) ⟨x.1, hx, rfl⟩)


/-- A strict filtered surjection is surjective on each concrete graded layer. -/
theorem sFSurjec.induced_layer_mapsurj {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : sFSurjec F E) (n : ℕ) :
    Function.Surjective (inducedLayerMap F E φ.hom φ.term_image_le n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  rcases φ.term_surjective n y with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  change inducedLayerMap F E φ.hom φ.term_image_le n (QuotientGroup.mk x) = QuotientGroup.mk y
  change QuotientGroup.mk (filtrationTermMap F E φ.hom φ.term_image_le n x) = QuotientGroup.mk y
  congr 1
  exact Subtype.ext hx

/-- An induced map on associated graded objects, represented by the actual quotient-layer maps. -/
structure iAGraded {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) where
  hom : G →* H
  preserves : ∀ n, (F n).map hom ≤ E n
  map : ∀ n, filtrationLayer F n →* filtrationLayer E n :=
    fun n => inducedLayerMap F E hom preserves n
  /-- Compatibility with representatives in each filtration term. -/
  map_mk : ∀ n (x : F n),
    map n (QuotientGroup.mk x) =
      QuotientGroup.mk (filtrationTermMap F E hom preserves n x)

/-- Identity map on an associated graded object. -/
noncomputable def iAGraded.id {G : Type u} [Group G]
    (F : DFilt G) : iAGraded F F where
  hom := MonoidHom.id G
  preserves := by
    intro n x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  map := fun n => MonoidHom.id (filtrationLayer F n)
  map_mk := by
    intro n x
    rfl

/-- Composition of induced maps on associated graded objects. -/
noncomputable def iAGraded.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : iAGraded E D) (α : iAGraded F E) :
    iAGraded F D where
  hom := β.hom.comp α.hom
  preserves := by
    intro n z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact β.preserves n ⟨α.hom x, α.preserves n ⟨x, hx, rfl⟩, rfl⟩
  map := fun n => (β.map n).comp (α.map n)
  map_mk := by
    intro n x
    rw [MonoidHom.comp_apply, α.map_mk, β.map_mk]
    rfl

/-- Representative compatibility for an induced associated-graded map. -/
@[simp] theorem iAGraded.map_mk_apply {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : iAGraded F E) (n : ℕ) (x : F n) :
    φ.map n (QuotientGroup.mk x) =
      QuotientGroup.mk (filtrationTermMap F E φ.hom φ.preserves n x) :=
  φ.map_mk n x

/-- The underlying homomorphism of an induced associated-graded map preserves terms. -/
theorem iAGraded.preserves_term {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (φ : iAGraded F E) (n : ℕ) :
    (F n).map φ.hom ≤ E n :=
  φ.preserves n

@[simp] theorem iAGraded.id_hom {G : Type u} [Group G]
    (F : DFilt G) :
    (iAGraded.id F).hom = MonoidHom.id G := rfl

@[simp] theorem iAGraded.comp_hom {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : iAGraded E D) (α : iAGraded F E) :
    (iAGraded.comp β α).hom = β.hom.comp α.hom := rfl

@[simp] theorem iAGraded.comp_map {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (β : iAGraded E D) (α : iAGraded F E) (n : ℕ) :
    (iAGraded.comp β α).map n = (β.map n).comp (α.map n) := rfl

/-- A quotient map with a depth-preservation assertion. -/
structure dPQuot {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) where
  hom : G →* H
  surjective : Function.Surjective hom
  preserves_terms : ∀ n x, x ∈ F n → hom x ∈ E n
  reflects_terms : ∀ n y, y ∈ E n → ∃ x, x ∈ F n ∧ hom x = y
  preserves_exact : ∀ n x, exactDepth F x n → exactDepth E (hom x) n


/-- A depth-preserving quotient map is a strict filtered surjection on terms. -/
def dPQuot.strict_filtered_surjection {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) : sFSurjec F E where
  hom := q.hom
  preserves := q.preserves_terms
  term_image_le := by
    intro n y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact q.preserves_terms n x hx
  surjective := q.surjective
  maps_onto_terms := by
    intro n
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      exact q.preserves_terms n x hx
    · intro hy
      rcases q.reflects_terms n y hy with ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩
  term_surjective := by
    intro n y
    rcases q.reflects_terms n y.1 y.2 with ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, hxy⟩

/-- Depth-preserving quotient maps preserve term membership. -/
theorem dPQuot.map_mem {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) {n : ℕ} {x : G} (hx : x ∈ F n) :
    q.hom x ∈ E n :=
  q.preserves_terms n x hx

/-- Depth-preserving quotient maps reflect term membership up to a preimage. -/
theorem dPQuot.exists_preimage_mem {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) {n : ℕ} {y : H} (hy : y ∈ E n) :
    ∃ x, x ∈ F n ∧ q.hom x = y :=
  q.reflects_terms n y hy

/-- Named accessor for exact-depth preservation. -/
theorem dPQuot.preserves_exact_depth {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) {n : ℕ} {x : G} (hx : exactDepth F x n) :
    exactDepth E (q.hom x) n :=
  q.preserves_exact n x hx

@[simp] theorem dPQuot.toStrict_hom {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) :
    (q.strict_filtered_surjection).hom = q.hom := rfl

/-- The strict surjection associated to a depth-preserving quotient is surjective. -/
theorem dPQuot.toStrict_surjective {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : dPQuot F E) :
    Function.Surjective q.strict_filtered_surjection.hom :=
  q.surjective

/-- A window of active degrees. -/
structure aDWindow where
  lo : ℕ
  hi : ℕ
  valid : lo ≤ hi
  degrees : Finset ℕ := Finset.Icc lo hi
  degrees_spec : ∀ n, n ∈ degrees ↔ lo ≤ n ∧ n ≤ hi

/-- Membership in an active degree window. -/
def aDWindow.contains (W : aDWindow) (n : ℕ) : Prop :=
  W.lo ≤ n ∧ n ≤ W.hi


/-- Canonical active window with degrees exactly `Icc lo hi`. -/
def aDWindow.ofBounds (lo hi : ℕ) (h : lo ≤ hi) : aDWindow where
  lo := lo
  hi := hi
  valid := h
  degrees := Finset.Icc lo hi
  degrees_spec := by intro n; simp

@[simp] theorem aDWindow.mem_degrees_iff (W : aDWindow) (n : ℕ) :
    n ∈ W.degrees ↔ W.contains n := W.degrees_spec n

@[simp] theorem aDWindow.ofBounds_contains (lo hi n : ℕ) (h : lo ≤ hi) :
    (aDWindow.ofBounds lo hi h).contains n ↔ lo ≤ n ∧ n ≤ hi := Iff.rfl

/-- The lower endpoint belongs to an active degree window. -/
theorem aDWindow.lo_mem (W : aDWindow) : W.lo ∈ W.degrees := by
  rw [W.mem_degrees_iff]
  exact ⟨le_rfl, W.valid⟩

/-- The upper endpoint belongs to an active degree window. -/
theorem aDWindow.hi_mem (W : aDWindow) : W.hi ∈ W.degrees := by
  rw [W.mem_degrees_iff]
  exact ⟨W.valid, le_rfl⟩

@[simp] theorem aDWindow.ofBounds_lo (lo hi : ℕ) (h : lo ≤ hi) :
    (aDWindow.ofBounds lo hi h).lo = lo := rfl

@[simp] theorem aDWindow.ofBounds_hi (lo hi : ℕ) (h : lo ≤ hi) :
    (aDWindow.ofBounds lo hi h).hi = hi := rfl

/-- Membership in the stored finset is exactly the two endpoint inequalities. -/
theorem aDWindow.mem_iff_bounds (W : aDWindow) {n : ℕ} :
    n ∈ W.degrees ↔ W.lo ≤ n ∧ n ≤ W.hi := W.degrees_spec n

/-- The endpoint inequality stored in an active window. -/
theorem aDWindow.valid_bounds (W : aDWindow) : W.lo ≤ W.hi :=
  W.valid

/-- The degree finset of an active window is nonempty. -/
theorem aDWindow.degrees_nonempty (W : aDWindow) : W.degrees.Nonempty :=
  ⟨W.lo, W.lo_mem⟩

/-- Membership in an active window implies the lower bound. -/
theorem aDWindow.lo_le_mem (W : aDWindow) {n : ℕ}
    (hn : n ∈ W.degrees) : W.lo ≤ n :=
  (W.degrees_spec n).1 hn |>.1

/-- Membership in an active window implies the upper bound. -/
theorem aDWindow.le_hi_mem (W : aDWindow) {n : ℕ}
    (hn : n ∈ W.degrees) : n ≤ W.hi :=
  (W.degrees_spec n).1 hn |>.2

/-- The multiset of relator depths for a finite indexed relator set. -/
noncomputable def depthMultisetRelators {α : Type u} {R : relatorSet α}
    [Fintype R] (d : R → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset R).val.map d

/-- Count relators at a given depth. -/
noncomputable def depthCountingFunction
    {α : Type u} {R : relatorSet α} (d : R → ℕ) (n : ℕ) : ℕ :=
  relatorCountR d n

/-- A cutoff quotient at degree `N`, tied to an actual filtration term. -/
structure cDN (G : Type u) [Group G] where
  filtration : DFilt G
  N : ℕ
  quotient : nSubgro G
  kernel_is_term : quotient.carrier = filtration N
  finite_quotient : Finite (quotientGroup quotient)
  projection : G →* quotientGroup quotient := QuotientGroup.mk' quotient.carrier


/-- Canonical cutoff quotient by the nth filtration term. -/
def cDN.ofTerm {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) : cDN G where
  filtration := F
  N := N
  quotient := filtrationNormalTerm F N
  kernel_is_term := rfl
  finite_quotient := hfin
  projection := QuotientGroup.mk' (F N)

@[simp] theorem cDN.ofTerm_projection {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) (g : G) :
    (cDN.ofTerm F N hfin).projection g = QuotientGroup.mk' (F N) g := rfl


@[simp] theorem cDN.ofTerm_N {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) :
    (cDN.ofTerm F N hfin).N = N := rfl

@[simp] theorem cDN.ofTerm_filtration {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) :
    (cDN.ofTerm F N hfin).filtration = F := rfl

/-- The kernel term recorded by a cutoff quotient, as a membership equivalence. -/
theorem cDN.mem_kernel_term {G : Type u} [Group G]
    (Q : cDN G) {g : G} :
    g ∈ Q.quotient.carrier ↔ g ∈ Q.filtration Q.N := by
  rw [Q.kernel_is_term]

/-- For the canonical cutoff quotient, the projection kills exactly the filtration term. -/
theorem cDN.term_projectioneq_oneiff {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) (g : G) :
    (cDN.ofTerm F N hfin).projection g = 1 ↔ g ∈ F N := by
  change QuotientGroup.mk' (F N) g = 1 ↔ g ∈ F N
  exact QuotientGroup.eq_one_iff (N := F N) g

/-- The canonical cutoff quotient projection is surjective. -/
theorem cDN.term_projection_surj {G : Type u} [Group G]
    (F : DFilt G) (N : ℕ)
    (hfin : Finite (quotientGroup (filtrationNormalTerm F N))) :
    Function.Surjective (cDN.ofTerm F N hfin).projection :=
  QuotientGroup.mk'_surjective (F N)

/-- The finite quotient certificate stored in a cutoff quotient. -/
theorem cDN.finite_quotient' {G : Type u} [Group G]
    (Q : cDN G) : Finite (quotientGroup Q.quotient) :=
  Q.finite_quotient

/-- A finite truncation of a Hilbert series through degree `N`, retaining the
proof that the truncated coefficients are the original ones. -/
def tHSeries {R : Type u} (H : hilbertSeries R) (N : ℕ) : Type u :=
  {f : ((n : {n : ℕ // n ≤ N}) → R) // ∀ n, f n = H n.1}

/-- Evaluate a finite Hilbert truncation at a bounded degree. -/
theorem tHSeries.coe_apply {R : Type u}
    (H : hilbertSeries R) (N : ℕ) (f : tHSeries H N)
    (n : {n : ℕ // n ≤ N}) : f.1 n = H n.1 :=
  f.2 n

/-- Jennings graded Lie algebra data, with additive structures and the basic
homogeneous bilinearity laws for bracket and zero-preservation for the `p` map. -/
structure jGLie (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  graded : ℕ → Type u
  [addG : ∀ n, AddCommGroup (graded n)]
  bracket : ∀ m n, graded m → graded n → graded (m+n)
  pmap : ∀ n, graded n → graded (p*n)
  bracket_add_left : ∀ m n (x y : graded m) (z : graded n),
    bracket m n (x + y) z = bracket m n x z + bracket m n y z
  bracket_add_right : ∀ m n (x : graded m) (y z : graded n),
    bracket m n x (y + z) = bracket m n x y + bracket m n x z
  bracket_self : ∀ n (x : graded n), bracket n n x x = 0
  bracket_skew : ∀ m n (x : graded m) (y : graded n),
    HEq (bracket m n x y) (- bracket n m y x)
  pmap_zero : ∀ n, pmap n 0 = 0

attribute [instance] jGLie.addG
/-- The prime attached to a Jennings graded Lie algebra. -/
theorem jGLie.prime_p {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) : Nat.Prime p := J.prime

/-- Jennings graded Lie data supplies the usual prime fact for its exponent. -/
@[reducible] def jGLie.fact_prime {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) : Fact p.Prime :=
  ⟨J.prime⟩

/-- Alternating bracket law in a Jennings graded Lie algebra. -/
theorem jGLie.bracket_self_eqzero {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) (n : ℕ) (x : J.graded n) :
    J.bracket n n x x = 0 := J.bracket_self n x


@[simp] theorem jGLie.pmap_zero_apply {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) (n : ℕ) : J.pmap n 0 = 0 :=
  J.pmap_zero n

/-- Left additivity of the Jennings bracket, as a named theorem. -/
theorem jGLie.bracket_add_leftapply {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) (m n : ℕ)
    (x y : J.graded m) (z : J.graded n) :
    J.bracket m n (x + y) z = J.bracket m n x z + J.bracket m n y z :=
  J.bracket_add_left m n x y z

/-- Right additivity of the Jennings bracket, as a named theorem. -/
theorem jGLie.bracket_add_rightapply {p : ℕ} {G : Type u} [Group G]
    (J : jGLie p G) (m n : ℕ)
    (x : J.graded m) (y z : J.graded n) :
    J.bracket m n x (y + z) = J.bracket m n x y + J.bracket m n x z :=
  J.bracket_add_right m n x y z

/-- A filtration on a restricted enveloping algebra by `R`-submodules, with
multiplication respecting degrees. -/
structure rEFilt (R : Type u) [CommSemiring R] where
  A : Type v
  [semiringA : Semiring A]
  [algebraA : Algebra R A]
  filt : ℕ → Submodule R A
  one_mem_zero : (1 : A) ∈ filt 0
  exhaustive_zero : filt 0 = ⊤
  antitone : ∀ {m n}, m ≤ n → filt n ≤ filt m
  mul_mem : ∀ m n {x y : A}, x ∈ filt m → y ∈ filt n → x * y ∈ filt (m + n)
  left_mul_mem : ∀ n (a : A) {x : A}, x ∈ filt n → a * x ∈ filt n
  right_mul_mem : ∀ n (a : A) {x : A}, x ∈ filt n → x * a ∈ filt n

attribute [instance] rEFilt.semiringA
attribute [instance] rEFilt.algebraA

/-- The zeroth filtration term is the whole algebra. -/
@[simp] theorem rEFilt.filt_zero_eqtop {R : Type u} [CommSemiring R]
    (F : rEFilt R) : F.filt 0 = ⊤ :=
  F.exhaustive_zero

/-- Antitonicity of the enveloping filtration, as a named inclusion. -/
theorem rEFilt.subset_of_le {R : Type u} [CommSemiring R]
    (F : rEFilt R) {m n : ℕ} (h : m ≤ n) :
    F.filt n ≤ F.filt m :=
  F.antitone h

/-- Left ideal stability of an enveloping filtration term. -/
theorem rEFilt.left_mul_mem' {R : Type u} [CommSemiring R]
    (F : rEFilt R) {n : ℕ} (a : F.A) {x : F.A}
    (hx : x ∈ F.filt n) : a * x ∈ F.filt n :=
  F.left_mul_mem n a hx

/-- Right ideal stability of an enveloping filtration term. -/
theorem rEFilt.right_mul_mem' {R : Type u} [CommSemiring R]
    (F : rEFilt R) {n : ℕ} (a : F.A) {x : F.A}
    (hx : x ∈ F.filt n) : x * a ∈ F.filt n :=
  F.right_mul_mem n a hx

/-- Multiplication respects filtration degrees. -/
theorem rEFilt.mul_mem' {R : Type u} [CommSemiring R]
    (F : rEFilt R) {m n : ℕ} {x y : F.A}
    (hx : x ∈ F.filt m) (hy : y ∈ F.filt n) : x * y ∈ F.filt (m + n) :=
  F.mul_mem m n hx hy

/-- Initial class of a group element in a graded layer. -/
structure iEClass {G : Type u} [Group G] (F : DFilt G) (g : G) where
  degree : ℕ
  mem : g ∈ F degree
  not_deeper : g ∉ F (degree + 1)
  exact : exactDepth F g degree := ⟨mem, not_deeper⟩
  representative : F degree := ⟨g, mem⟩


/-- Build an initial class package from an exact-depth proof. -/
def iEClass.ofExact {G : Type u} [Group G]
    {F : DFilt G} {g : G} {n : ℕ} (h : exactDepth F g n) :
    iEClass F g where
  degree := n
  mem := h.1
  not_deeper := h.2
  exact := h
  representative := ⟨g, h.1⟩

/-- The actual quotient-layer class represented by an initial group element. -/
def iEClass.layerClass {G : Type u} [Group G]
    {F : DFilt G} {g : G} (c : iEClass F g) :
    filtrationLayer F c.degree :=
  QuotientGroup.mk c.representative

@[simp] theorem iEClass.layerClass_mk {G : Type u} [Group G]
    {F : DFilt G} {g : G} (c : iEClass F g) :
    c.layerClass = QuotientGroup.mk c.representative := rfl

@[simp] theorem iEClass.ofExact_degree {G : Type u} [Group G]
    {F : DFilt G} {g : G} {n : ℕ} (h : exactDepth F g n) :
    (iEClass.ofExact h).degree = n := rfl

@[simp] theorem iEClass.exact_repr_val {G : Type u} [Group G]
    {F : DFilt G} {g : G} {n : ℕ} (h : exactDepth F g n) :
    (iEClass.ofExact h).representative.1 = g := rfl

/-- The stored exact-depth proof can be projected by name. -/
theorem iEClass.exact_depth {G : Type u} [Group G]
    {F : DFilt G} {g : G} (c : iEClass F g) :
    exactDepth F g c.degree := c.exact

/-- Membership of an initial class in its recorded filtration term. -/
theorem iEClass.mem_term {G : Type u} [Group G]
    {F : DFilt G} {g : G} (c : iEClass F g) :
    g ∈ F c.degree :=
  c.mem

/-- An initial class is not in the next filtration term. -/
theorem iEClass.not_mem_next {G : Type u} [Group G]
    {F : DFilt G} {g : G} (c : iEClass F g) :
    g ∉ F (c.degree + 1) :=
  c.not_deeper

/-- Active relators in degree `n`. -/
def aSN {α : Type u} {R : relatorSet α} (d : R → ℕ) (n : ℕ) : Set R :=
  {r | d r ≤ n}

/-- Shift a Hilbert coefficient by a relator depth. -/
def shiftedHilbertCoefficient {R : Type u} (zero : R) (H : hilbertSeries R) (n q : ℕ) : R :=
  if q ≤ n then H (n - q) else zero


@[simp] theorem shifted_hilbert_coefficient {R : Type u} (zero : R)
    (H : hilbertSeries R) {n q : ℕ} (h : q ≤ n) :
    shiftedHilbertCoefficient zero H n q = H (n - q) := by
  simp [shiftedHilbertCoefficient, h]

@[simp] theorem shifted_hilbert_not {R : Type u} (zero : R)
    (H : hilbertSeries R) {n q : ℕ} (h : ¬ q ≤ n) :
    shiftedHilbertCoefficient zero H n q = zero := by
  simp [shiftedHilbertCoefficient, h]

/-- Active terms indexed by depth. -/
def aTDepth
    {α : Type u} {Rels : relatorSet α} (d : Rels → ℕ) (n : ℕ) :
    Set (Rels × ℕ) :=
  {rq | d rq.1 = rq.2 ∧ rq.2 ≤ n}

@[simp] theorem aSN.mem_iff {α : Type u} {R : relatorSet α}
    (d : R → ℕ) (n : ℕ) (r : R) :
    r ∈ aSN d n ↔ d r ≤ n := Iff.rfl

@[simp] theorem aTDepth.mem_iff {α : Type u} {Rels : relatorSet α}
    (d : Rels → ℕ) (n : ℕ) (rq : Rels × ℕ) :
    rq ∈ aTDepth d n ↔ d rq.1 = rq.2 ∧ rq.2 ≤ n := Iff.rfl

/-- An active term's relator is active at the ambient degree. -/
theorem aTDepth.rel_active {α : Type u} {Rels : relatorSet α}
    {d : Rels → ℕ} {n : ℕ} {rq : Rels × ℕ}
    (h : rq ∈ aTDepth d n) : d rq.1 ≤ n := by
  rcases h with ⟨heq, hle⟩
  simpa [heq] using hle

/-- Active relator sets are monotone in the ambient degree. -/
theorem aSN.mono {α : Type u} {R : relatorSet α}
    {d : R → ℕ} {m n : ℕ} (h : m ≤ n) :
    aSN d m ⊆ aSN d n := by
  intro r hr
  exact Nat.le_trans hr h

/-- Active depth-tagged terms are monotone in the ambient degree. -/
theorem aTDepth.mono {α : Type u} {Rels : relatorSet α}
    {d : Rels → ℕ} {m n : ℕ} (h : m ≤ n) :
    aTDepth d m ⊆ aTDepth d n := by
  intro rq hr
  rcases hr with ⟨hd, hm⟩
  exact ⟨hd, Nat.le_trans hm h⟩

/-- Coefficientwise inequality between two coefficient sequences. -/
def cIneq {R : Type u} [Preorder R] (a b : ℕ → R) : Prop :=
  ∀ n, a n ≤ b n

/-- Coefficientwise addition of formal series. -/
def hilbertSeriesAdd {R : Type u} [Add R] (a b : ℕ → R) : ℕ → R :=
  fun n => a n + b n

/-- Cauchy product of coefficient sequences (finite convolution in each degree). -/
def hilbertSeriesMul {R : Type u} [Semiring R] (a b : ℕ → R) : ℕ → R :=
  fun n => Finset.sum (Finset.range (n + 1)) (fun i => a i * b (n - i))

@[simp] theorem hilbert_series_add {R : Type u} [Add R]
    (a b : ℕ → R) (n : ℕ) : hilbertSeriesAdd a b n = a n + b n := rfl

@[simp] theorem hilbert_series_mul {R : Type u} [Semiring R]
    (a b : ℕ → R) (n : ℕ) :
    hilbertSeriesMul a b n = Finset.sum (Finset.range (n + 1))
      (fun i => a i * b (n - i)) := rfl

/-- Coefficientwise inequality is reflexive for preorder coefficients. -/
theorem coefficientwiseInequality_refl {R : Type u} [Preorder R] (a : ℕ → R) :
    cIneq a a := fun _ => le_rfl

/-- Coefficientwise inequality is transitive for preorder coefficients. -/
theorem coefficientwiseInequality_trans {R : Type u} [Preorder R] {a b c : ℕ → R}
    (hab : cIneq a b) (hbc : cIneq b c) :
    cIneq a c := fun n => le_trans (hab n) (hbc n)

/-- Apply a coefficientwise inequality at a degree. -/
theorem cIneq.apply {R : Type u} [Preorder R]
    {a b : ℕ → R} (h : cIneq a b) (n : ℕ) : a n ≤ b n :=
  h n

/-- Addition of Hilbert coefficient sequences is pointwise commutative when coefficients are. -/
theorem hilbert_series_comm {R : Type u} [AddCommSemigroup R]
    (a b : ℕ → R) : hilbertSeriesAdd a b = hilbertSeriesAdd b a := by
  funext n
  simp [hilbertSeriesAdd, add_comm]


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

universe u v w x

/-- A map preserves exact depth once all depth-lowering obstructions are excluded. -/
def LoweringPreservesExact {G : Type u} {H : Type v} [Group G] [Group H]
    (F : DFilt G) (E : DFilt H) (φ : G →* H) : Prop :=
  ∀ ⦃x : G⦄ ⦃n : ℕ⦄, exactDepth F x n → exactDepth E (φ x) n
/-- Filtration-preserving homomorphisms map terms into terms. -/
theorem homCompatibilityDn {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H) {n : ℕ} {x : G} :
    x ∈ GroupAlgebra.zSubgro p G n →
      φ x ∈ GroupAlgebra.zSubgro p H n
  := by
  exact fun hx => GroupAlgebra.zassenhaus_subgroup_comap p G φ n hx
/-- Surjective homomorphisms preserve Zassenhaus terms.  Termwise surjectivity is a
separate strictness hypothesis; it is not a consequence of abstract surjectivity
alone from the local API. -/
theorem surjectionCompatibilityDN {p : ℕ} [Fact p.Prime]
    {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H) (_hφ : Function.Surjective φ) (n : ℕ) :
    (GroupAlgebra.zSubgro p G n).map φ ≤
      GroupAlgebra.zSubgro p H n
  := by
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact homCompatibilityDn (p := p) φ hx
/-- Quotients inherit filtrations through strict filtered surjections. -/
theorem quotientFiltrationInheritance {p : ℕ} {G : Type u} [Group G]
    (N : nSubgro G) :
    ∃ E : DFilt (quotientGroup N),
      DFilt.MapsOnto (GroupAlgebra.zassenhausFiltration p G) E N.projection
  := by
  let E : DFilt (quotientGroup N) := {
    term := fun n => (GroupAlgebra.zSubgro p G n).map N.projection
    antitone' := by
      intro m n hmn y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨x, GroupAlgebra.zassenhausSubgroup_antitone p G hmn hx, rfl⟩
    normal' := by
      intro n
      haveI : (GroupAlgebra.zSubgro p G n).Normal :=
        GroupAlgebra.zassenhausSubgroup_normal p G n
      exact (show (GroupAlgebra.zSubgro p G n).Normal from inferInstance).map
        N.projection N.projection_surjective
    one_eq_top' := by
      rw [GroupAlgebra.zassenhaus_one_top]
      exact Subgroup.map_top_of_surjective N.projection N.projection_surjective
  }
  exact ⟨E, fun n => rfl⟩
/-- Zassenhaus functoriality packages homomorphism, surjection, and quotient compatibility. -/
theorem functorialityZassenhausFiltrations {p : ℕ} {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    (β : H →* K) (α : G →* H) :
    ∃ γ : fPHom
        (GroupAlgebra.zassenhausFiltration p G) (GroupAlgebra.zassenhausFiltration p K),
      γ.hom = β.comp α
  := by
  let γ : fPHom
      (GroupAlgebra.zassenhausFiltration p G) (GroupAlgebra.zassenhausFiltration p K) := by
    refine
      { hom := β.comp α
        preserves := ?_
        term_image_le := ?_ }
    · intro n x hx
      exact homCompatibilityDn (p := p) (β.comp α) hx
    · intro n z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact homCompatibilityDn (p := p) (β.comp α) hx
  exact ⟨γ, rfl⟩
/-- A filtered map induces a map on associated graded layers. -/
theorem inducesGraded {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H)
    (hφ : ∀ n, (GroupAlgebra.zSubgro p G n).map φ ≤
      GroupAlgebra.zSubgro p H n) :
    ∃ M : iAGraded
        (GroupAlgebra.zassenhausFiltration p G) (GroupAlgebra.zassenhausFiltration p H),
      M.hom = φ ∧
      ∀ n (x : GroupAlgebra.zassenhausFiltration p G n),
        M.map n (QuotientGroup.mk x) =
          QuotientGroup.mk (filtrationTermMap
            (GroupAlgebra.zassenhausFiltration p G)
            (GroupAlgebra.zassenhausFiltration p H) φ hφ n x)
  := by
  let M : iAGraded
      (GroupAlgebra.zassenhausFiltration p G) (GroupAlgebra.zassenhausFiltration p H) := by
    refine
      { hom := φ
        preserves := hφ
        map_mk := ?_ }
    intro n x
    rfl
  refine ⟨M, ?_, ?_⟩
  · rfl
  · intro n x
    exact M.map_mk n x
/-- A termwise-onto prime-`p` filtered map induces surjections on associated graded layers. -/
theorem surjectionInducesGraded {p : ℕ} [Fact p.Prime]
    {G : Type u} {H : Type v}
    [Group G] [Group H] (φ : G →* H) (_hφ : Function.Surjective φ)
    (hterm : ∀ n, (GroupAlgebra.zSubgro p G n).map φ ≤
      GroupAlgebra.zSubgro p H n)
    (honto : DFilt.MapsOnto
      (GroupAlgebra.zassenhausFiltration p G)
      (GroupAlgebra.zassenhausFiltration p H) φ) (n : ℕ) :
    Function.Surjective (inducedLayerMap
      (GroupAlgebra.zassenhausFiltration p G) (GroupAlgebra.zassenhausFiltration p H)
      φ hterm n)
  := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  have hy : y.1 ∈ (GroupAlgebra.zSubgro p G n).map φ := by
    have hy' : y.1 ∈ (GroupAlgebra.zassenhausFiltration p G n).map φ := by
      rw [honto n]
      exact y.2
    simpa [GroupAlgebra.zassenhausFiltration_term] using hy'
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
  refine ⟨QuotientGroup.mk (⟨x, hx⟩ :
    GroupAlgebra.zassenhausFiltration p G n), ?_⟩
  change QuotientGroup.mk
      (filtrationTermMap
        (GroupAlgebra.zassenhausFiltration p G)
        (GroupAlgebra.zassenhausFiltration p H) φ hterm n ⟨x, hx⟩) =
    QuotientGroup.mk y
  congr 1
  exact Subtype.ext hxy
/-- Depth-preserving quotient maps preserve exact depths. -/
theorem preservationDepthQuotients {G : Type u} {H : Type v} [Group G] [Group H]
    {F : DFilt G} {E : DFilt H}
    (q : G →* H)
    (hterm : ∀ n {x : G}, x ∈ F n → q x ∈ E n)
    (hnot_deeper : ∀ n {x : G}, x ∉ F (n + 1) → q x ∉ E (n + 1))
    {n : ℕ} {x : G} :
    exactDepth F x n → exactDepth E (q x) n
  := by
  intro hx
  exact ⟨hterm n hx.1, hnot_deeper n hx.2⟩
/-- Lower-bound depth descends under a depth-preserving quotient. -/
theorem lowerBoundDescends {G : Type u} {H : Type v} [Group G] [Group H]
    {F : DFilt G} {E : DFilt H}
    (q : G →* H)
    (hterm : ∀ n {x : G}, x ∈ F n → q x ∈ E n) {n : ℕ} {x : G} :
    lowerBoundDepth F x n → lowerBoundDepth E (q x) n
  := by
  exact fun hx => hterm n hx

/-- Exact depth descends under controlled quotients. -/
theorem exactDescendsControlled {G : Type u} {H : Type v}
    [Group G] [Group H] {F : DFilt G} {E : DFilt H}
    (q : G →* H)
    (hterm : ∀ n {x : G}, x ∈ F n → q x ∈ E n)
    (hnot_deeper : ∀ n {x : G}, x ∉ F (n + 1) → q x ∉ E (n + 1))
    {x : G} {n : ℕ} :
    exactDepth F x n → exactDepth E (q x) n
  := by
  intro hx
  exact ⟨hterm n hx.1, hnot_deeper n hx.2⟩

end Theorems
end Towers
