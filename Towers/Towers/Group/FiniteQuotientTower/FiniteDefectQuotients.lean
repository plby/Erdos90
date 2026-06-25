import Towers.Group.FiniteQuotientTower.KernelObstructions


noncomputable section

namespace Towers
namespace Group

open PRFact

universe u

namespace cSQuotie

variable
    (S : cSQuotie.{u})
    {H : Type u}
    [Group H]
    (φ : inverseLimit S →* H)

/--
The finite defect subgroup at level `n` is the image of the descent kernel in
the `n`th finite quotient coordinate.
-/
def finiteDefectSubgroup
    (n : ℕ) :
    Subgroup (S.obj n) :=
  φ.ker.map (inverseLimitProjection S n)

/--
A finite defect subgroup is trivial exactly when the corresponding finite
projection kills the descent kernel.
-/
lemma defect_bot_projection
    (n : ℕ) :
    S.finiteDefectSubgroup φ n = ⊥ ↔
      φ.ker ≤ (inverseLimitProjection S n).ker := by
  constructor
  · intro hdefect x hx
    rw [MonoidHom.mem_ker]
    have hximage :
        inverseLimitProjection S n x ∈ S.finiteDefectSubgroup φ n :=
      ⟨x, hx, rfl⟩
    rw [hdefect, Subgroup.mem_bot] at hximage
    exact hximage
  · intro hkernel
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker]
      exact hkernel hx
    · exact bot_le

/--
A surjective inverse-limit descent is injective exactly when every finite
defect subgroup vanishes.
-/
lemma injective_forall_bot :
    Function.Injective φ ↔
      ∀ n : ℕ, S.finiteDefectSubgroup φ n = ⊥ := by
  rw [S.injective_projection_kernels φ]
  exact forall_congr' fun n =>
    (S.defect_bot_projection φ n).symm

/--
Failure of injectivity is detected by one nontrivial finite defect subgroup.
-/
lemma not_ne_bot :
    ¬ Function.Injective φ ↔
      ∃ n : ℕ, S.finiteDefectSubgroup φ n ≠ ⊥ := by
  rw [S.injective_forall_bot φ]
  simp only [not_forall]

/--
When finite inverse-limit projections are onto, each finite defect subgroup is
normal in its finite quotient layer.
-/
def defectNormalSubgroup
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    nSubgro (S.obj n) where
  carrier := S.finiteDefectSubgroup φ n
  normal' := Subgroup.Normal.map inferInstance
    (inverseLimitProjection S n) (hprojection n)

/--
The largest quotient of the `n`th finite layer on which the image of the
descent kernel vanishes.
-/
abbrev finiteDefectQuotient
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :=
  quotientGroup (S.defectNormalSubgroup φ hprojection n)

/--
The quotient map from a finite layer to its finite defect quotient.
-/
def defectQuotient
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    S.obj n →* S.finiteDefectQuotient φ hprojection n :=
  (S.defectNormalSubgroup φ hprojection n).projection

/--
The finite defect quotient map loses no information exactly when the finite
defect subgroup at that layer is trivial.
-/
lemma fin_defect_bot
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    Function.Injective (S.defectQuotient φ hprojection n) ↔
      S.finiteDefectSubgroup φ n = ⊥ := by
  constructor
  · intro hInjective
    have hker :
        (S.defectQuotient φ hprojection n).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff
        (S.defectQuotient φ hprojection n)).mpr hInjective
    change (S.defectNormalSubgroup φ hprojection n).projection.ker = ⊥ at hker
    rw [(S.defectNormalSubgroup φ hprojection n).ker_projection] at hker
    exact hker
  · intro hdefect
    apply (MonoidHom.ker_eq_bot_iff
      (S.defectQuotient φ hprojection n)).mp
    change (S.defectNormalSubgroup φ hprojection n).projection.ker = ⊥
    rw [(S.defectNormalSubgroup φ hprojection n).ker_projection]
    exact hdefect

/--
The finite defect quotient map is an isomorphism exactly when the finite defect
subgroup at that layer is trivial.
-/
lemma defect_bijective_bot
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    Function.Bijective (S.defectQuotient φ hprojection n) ↔
      S.finiteDefectSubgroup φ n = ⊥ := by
  constructor
  · intro hbijective
    exact (S.fin_defect_bot
      φ hprojection n).mp hbijective.1
  · intro hdefect
    exact ⟨(S.fin_defect_bot
      φ hprojection n).mpr hdefect,
      (S.defectNormalSubgroup φ hprojection n).projection_surjective⟩

/--
At a defect-free finite layer, the finite defect quotient is canonically the
original finite quotient layer.
-/
def finiteDefectBot
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ)
    (hdefect : S.finiteDefectSubgroup φ n = ⊥) :
    S.obj n ≃* S.finiteDefectQuotient φ hprojection n :=
  MulEquiv.ofBijective
    (S.defectQuotient φ hprojection n)
    ((S.defect_bijective_bot
      φ hprojection n).mpr hdefect)

/--
The canonical equivalence at a defect-free finite layer is induced by the
finite defect quotient map.
-/
lemma defect_bot_monoid
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ)
    (hdefect : S.finiteDefectSubgroup φ n = ⊥) :
    (S.finiteDefectBot φ hprojection n hdefect).toMonoidHom =
      S.defectQuotient φ hprojection n := by
  rfl

/--
A finite layer is defect-free exactly when its projection descends uniquely
through the target.
-/
lemma defect_uniquely_through
    (hφ : Function.Surjective φ)
    (n : ℕ) :
    S.finiteDefectSubgroup φ n = ⊥ ↔
      FactorsUniquelyThrough φ (inverseLimitProjection S n) := by
  exact (S.defect_bot_projection φ n).trans
    (S.projection_unique_through
      φ hφ n).symm

/--
A finite defect quotient recovers its original finite layer exactly when that
finite projection descends uniquely through the target.
-/
lemma projection_uniquely_through
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    Function.Injective (S.defectQuotient φ hprojection n) ↔
      FactorsUniquelyThrough φ (inverseLimitProjection S n) := by
  exact (S.fin_defect_bot
    φ hprojection n).trans
      (S.defect_uniquely_through
        φ hφ n)

/--
A surjective inverse-limit descent is injective exactly when every finite
defect quotient recovers its original finite layer.
-/
lemma injective_forall_defect
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    Function.Injective φ ↔
      ∀ n : ℕ, Function.Injective (S.defectQuotient φ hprojection n) := by
  rw [S.injective_forall_bot φ]
  exact forall_congr' fun n =>
    (S.fin_defect_bot
      φ hprojection n).symm

/--
Failure of injectivity is detected by one finite defect quotient that genuinely
collapses its original finite layer.
-/
lemma not_injective_quotient
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    ¬ Function.Injective φ ↔
      ∃ n : ℕ, ¬ Function.Injective (S.defectQuotient φ hprojection n) := by
  rw [S.injective_forall_defect φ hprojection]
  simp only [not_forall]

/--
For a noninjective descent, the first finite quotient layer carrying a
nontrivial finite defect subgroup.
-/
def firstDefectDepth
    (hnot : ¬ Function.Injective φ) :
    ℕ := by
  classical
  exact Nat.find ((S.not_ne_bot φ).mp hnot)

/--
The first finite defect depth really carries a nontrivial finite defect
subgroup.
-/
lemma defect_ne_bot
    (hnot : ¬ Function.Injective φ) :
    S.finiteDefectSubgroup φ (S.firstDefectDepth φ hnot) ≠ ⊥ := by
  classical
  exact Nat.find_spec ((S.not_ne_bot φ).mp hnot)

/--
Every earlier finite quotient layer is defect-free before the first finite
defect depth.
-/
lemma bot_first_depth
    (hnot : ¬ Function.Injective φ)
    {m : ℕ}
    (hm : m < S.firstDefectDepth φ hnot) :
    S.finiteDefectSubgroup φ m = ⊥ := by
  classical
  by_contra hdefect
  exact (Nat.find_min
    ((S.not_ne_bot φ).mp hnot)
    hm) hdefect

/--
The first finite defect quotient genuinely collapses its original finite layer.
-/
lemma fin_defect_depth
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (hnot : ¬ Function.Injective φ) :
    ¬ Function.Injective
      (S.defectQuotient φ hprojection
        (S.firstDefectDepth φ hnot)) := by
  intro hInjective
  exact S.defect_ne_bot φ hnot
    ((S.fin_defect_bot
      φ hprojection (S.firstDefectDepth φ hnot)).mp hInjective)

/--
Every earlier finite defect quotient still recovers its original finite layer
before the first finite defect depth.
-/
lemma fin_defect_injective
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (hnot : ¬ Function.Injective φ)
    {m : ℕ}
    (hm : m < S.firstDefectDepth φ hnot) :
    Function.Injective (S.defectQuotient φ hprojection m) := by
  apply (S.fin_defect_bot
    φ hprojection m).mpr
  exact S.bot_first_depth φ hnot hm

/--
The canonical map from the inverse limit to the `n`th finite defect quotient.
-/
def finiteDefectProjection
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    inverseLimit S →* S.finiteDefectQuotient φ hprojection n :=
  (S.defectQuotient φ hprojection n).comp
    (inverseLimitProjection S n)

/--
The finite defect quotient projection kills the whole descent kernel.
-/
lemma kernel_defect_projection
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    φ.ker ≤ (S.finiteDefectProjection φ hprojection n).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, finiteDefectProjection, MonoidHom.comp_apply,
    defectQuotient, nSubgro.projection]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨x, hx, rfl⟩

/--
Assuming the descent is onto, every finite defect quotient is an actual finite
quotient of the target group.
-/
def finiteDefectFactor
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    H →* S.finiteDefectQuotient φ hprojection n := by
  letI : TopologicalSpace (inverseLimit S) := ⊤
  letI : IndiscreteTopology (inverseLimit S) := inferInstance
  letI : IsTopologicalGroup (inverseLimit S) := inferInstance
  exact factorSurjective
    φ
    (S.finiteDefectProjection φ hprojection n)
    hφ
    (S.kernel_defect_projection φ hprojection n)

/--
The target finite defect quotient factor descends the finite defect quotient
projection from the inverse limit.
-/
lemma defect_factor_comp
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    (S.finiteDefectFactor φ hφ hprojection n).comp φ =
      S.finiteDefectProjection φ hprojection n := by
  letI : TopologicalSpace (inverseLimit S) := ⊤
  letI : IndiscreteTopology (inverseLimit S) := inferInstance
  letI : IsTopologicalGroup (inverseLimit S) := inferInstance
  exact factor_map_of
    φ
    (S.finiteDefectProjection φ hprojection n)
    hφ
    (S.kernel_defect_projection φ hprojection n)

/--
Every finite defect quotient factor from the target group is onto.
-/
lemma defect_factor_surjective
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    Function.Surjective (S.finiteDefectFactor φ hφ hprojection n) := by
  intro y
  rcases (S.defectNormalSubgroup φ hprojection n).projection_surjective y with
    ⟨yn, rfl⟩
  rcases hprojection n yn with ⟨x, rfl⟩
  exact ⟨φ x, by
    simpa [finiteDefectProjection, defectQuotient,
      nSubgro.projection] using congrArg
        (fun ψ : inverseLimit S →* S.finiteDefectQuotient φ hprojection n =>
          ψ x)
        (S.defect_factor_comp φ hφ hprojection n)⟩

/--
Any finite-layer map whose pullback descends through the target kills the
finite defect subgroup.
-/
lemma defect_pullback_through
    {P : Type u}
    [Group P]
    (n : ℕ)
    (γ : S.obj n →* P)
    (hfactor : FactorsThrough φ (γ.comp (inverseLimitProjection S n))) :
    S.finiteDefectSubgroup φ n ≤ γ.ker := by
  rintro y ⟨x, hx, rfl⟩
  rcases hfactor with ⟨β, hβ⟩
  rw [MonoidHom.mem_ker]
  have hβx := congrArg (fun ψ : inverseLimit S →* P => ψ x) hβ
  change β (φ x) = γ (inverseLimitProjection S n x) at hβx
  rw [← hβx, MonoidHom.mem_ker.mp hx, β.map_one]

/--
The finite defect quotient is universal among finite-layer maps whose pullback
descends through the target.
-/
lemma uniquely_through_pullback
    {P : Type u}
    [Group P]
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ)
    (γ : S.obj n →* P)
    (hfactor : FactorsThrough φ (γ.comp (inverseLimitProjection S n))) :
    FactorsUniquelyThrough
      (S.defectQuotient φ hprojection n)
      γ := by
  letI : TopologicalSpace (S.obj n) := ⊤
  letI : IndiscreteTopology (S.obj n) := inferInstance
  letI : IsTopologicalGroup (S.obj n) := inferInstance
  apply factors_uniquely_ker
    (S.defectQuotient φ hprojection n)
    γ
    (S.defectNormalSubgroup φ hprojection n).projection_surjective
  change (S.defectNormalSubgroup φ hprojection n).projection.ker ≤ γ.ker
  rw [(S.defectNormalSubgroup φ hprojection n).ker_projection]
  exact S.defect_pullback_through φ n γ hfactor

/--
Canonical transition maps carry deeper finite defect subgroups into shallower
finite defect subgroups.
-/
lemma defect_subgroup_transition
    {m n : ℕ}
    (hmn : m ≤ n) :
    (S.finiteDefectSubgroup φ n).map (S.map hmn) ≤
      S.finiteDefectSubgroup φ m := by
  rintro y ⟨yn, hyn, rfl⟩
  rcases hyn with ⟨x, hx, rfl⟩
  exact ⟨x, hx, (limit_projection_compat S hmn x).symm⟩

/--
Canonical transition map between finite defect quotients.
-/
def finiteDefectTransition
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    {m n : ℕ}
    (hmn : m ≤ n) :
    S.finiteDefectQuotient φ hprojection n →*
      S.finiteDefectQuotient φ hprojection m := by
  letI : (S.finiteDefectSubgroup φ n).Normal :=
    (S.defectNormalSubgroup φ hprojection n).normal'
  letI : (S.finiteDefectSubgroup φ m).Normal :=
    (S.defectNormalSubgroup φ hprojection m).normal'
  exact QuotientGroup.map
    (S.finiteDefectSubgroup φ n)
    (S.finiteDefectSubgroup φ m)
    (S.map hmn)
    (Subgroup.map_le_iff_le_comap.mp
      (S.defect_subgroup_transition φ hmn))

/--
Finite defect quotient transitions are compatible with the quotient maps from
the original finite layers.
-/
lemma defect_transition_comp
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    {m n : ℕ}
    (hmn : m ≤ n) :
    (S.finiteDefectTransition φ hprojection hmn).comp
        (S.defectQuotient φ hprojection n) =
      (S.defectQuotient φ hprojection m).comp (S.map hmn) := by
  apply MonoidHom.ext
  intro x
  letI : (S.finiteDefectSubgroup φ n).Normal :=
    (S.defectNormalSubgroup φ hprojection n).normal'
  letI : (S.finiteDefectSubgroup φ m).Normal :=
    (S.defectNormalSubgroup φ hprojection m).normal'
  exact QuotientGroup.map_mk'
    (S.finiteDefectSubgroup φ n)
    (S.finiteDefectSubgroup φ m)
    (S.map hmn)
    (Subgroup.map_le_iff_le_comap.mp
      (S.defect_subgroup_transition φ hmn))
    x

/--
Finite defect quotient transitions are onto.
-/
lemma defect_transition_surjective
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    {m n : ℕ}
    (hmn : m ≤ n) :
    Function.Surjective (S.finiteDefectTransition φ hprojection hmn) := by
  intro y
  rcases (S.defectNormalSubgroup φ hprojection m).projection_surjective y with
    ⟨ym, rfl⟩
  rcases S.map_surj hmn ym with ⟨yn, rfl⟩
  exact ⟨S.defectQuotient φ hprojection n yn, by
    simpa using congrArg
      (fun ψ : S.obj n →* S.finiteDefectQuotient φ hprojection m => ψ yn)
      (S.defect_transition_comp φ hprojection hmn)⟩

/--
The finite defect quotients form a compatible finite quotient tower.
-/
def finiteDefectSystem
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    cSQuotie where
  obj := S.finiteDefectQuotient φ hprojection
  group_obj := fun _n => inferInstance
  finite_obj := fun _n => inferInstance
  map := fun {_m _n} hmn => S.finiteDefectTransition φ hprojection hmn
  map_surjective := fun {_m _n} hmn =>
    S.defect_transition_surjective φ hprojection hmn
  map_id := by
    intro n
    apply MonoidHom.ext
    intro x
    rcases (S.defectNormalSubgroup φ hprojection n).projection_surjective x with
      ⟨xn, rfl⟩
    simpa only [MonoidHom.comp_apply, S.map_id_apply] using congrArg
      (fun ψ : S.obj n →* S.finiteDefectQuotient φ hprojection n => ψ xn)
      (S.defect_transition_comp φ hprojection
        (Nat.le_refl n))
  map_comp := by
    intro k m n hkm hmn
    apply MonoidHom.ext
    intro x
    rcases (S.defectNormalSubgroup φ hprojection n).projection_surjective x with
      ⟨xn, rfl⟩
    change S.finiteDefectTransition φ hprojection hkm
        (S.finiteDefectTransition φ hprojection hmn
          (S.defectQuotient φ hprojection n xn)) =
      S.finiteDefectTransition φ hprojection (Nat.le_trans hkm hmn)
        (S.defectQuotient φ hprojection n xn)
    calc
      S.finiteDefectTransition φ hprojection hkm
          (S.finiteDefectTransition φ hprojection hmn
            (S.defectQuotient φ hprojection n xn)) =
          S.finiteDefectTransition φ hprojection hkm
            (S.defectQuotient φ hprojection m (S.map hmn xn)) := by
            exact congrArg
              (S.finiteDefectTransition φ hprojection hkm)
              (by
                simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun
                  (S.defect_transition_comp φ hprojection hmn)
                  xn)
      _ = S.defectQuotient φ hprojection k
          (S.map hkm (S.map hmn xn)) := by
            simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun
              (S.defect_transition_comp φ hprojection hkm)
              (S.map hmn xn)
      _ = S.defectQuotient φ hprojection k
          (S.map (Nat.le_trans hkm hmn) xn) := by
            rw [S.map_comp_apply hkm hmn xn]
      _ = S.finiteDefectTransition φ hprojection (Nat.le_trans hkm hmn)
          (S.defectQuotient φ hprojection n xn) := by
            simpa only [MonoidHom.comp_apply] using
              (DFunLike.congr_fun
              (S.defect_transition_comp φ hprojection
                (Nat.le_trans hkm hmn))
              xn).symm

/--
Finite defect quotient factors from the target group are compatible with finite
defect quotient transition maps.
-/
lemma defect_transition_factor
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    {m n : ℕ}
    (hmn : m ≤ n) :
    (S.finiteDefectTransition φ hprojection hmn).comp
        (S.finiteDefectFactor φ hφ hprojection n) =
      S.finiteDefectFactor φ hφ hprojection m := by
  apply MonoidHom.ext
  intro y
  rcases hφ y with ⟨x, rfl⟩
  have hn := congrArg
    (fun ψ : inverseLimit S →* S.finiteDefectQuotient φ hprojection n => ψ x)
    (S.defect_factor_comp φ hφ hprojection n)
  have hm := congrArg
    (fun ψ : inverseLimit S →* S.finiteDefectQuotient φ hprojection m => ψ x)
    (S.defect_factor_comp φ hφ hprojection m)
  change S.finiteDefectFactor φ hφ hprojection n (φ x) =
    S.finiteDefectProjection φ hprojection n x at hn
  change S.finiteDefectFactor φ hφ hprojection m (φ x) =
    S.finiteDefectProjection φ hprojection m x at hm
  change S.finiteDefectTransition φ hprojection hmn
      (S.finiteDefectFactor φ hφ hprojection n (φ x)) =
    S.finiteDefectFactor φ hφ hprojection m (φ x)
  rw [hn, hm]
  change S.finiteDefectTransition φ hprojection hmn
      (S.defectQuotient φ hprojection n
        (inverseLimitProjection S n x)) =
    S.defectQuotient φ hprojection m
      (inverseLimitProjection S m x)
  calc
    S.finiteDefectTransition φ hprojection hmn
        (S.defectQuotient φ hprojection n
          (inverseLimitProjection S n x)) =
        S.defectQuotient φ hprojection m
          (S.map hmn (inverseLimitProjection S n x)) := by
          simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun
            (S.defect_transition_comp φ hprojection hmn)
            (inverseLimitProjection S n x)
    _ = S.defectQuotient φ hprojection m
        (inverseLimitProjection S m x) := by
          rw [limit_projection_compat S hmn x]

/--
The finite-level saturation of a subgroup consists of the threads lying in that
subgroup modulo every finite projection kernel.
-/
def finiteLevelSaturation
    (K : Subgroup (inverseLimit S)) :
    Subgroup (inverseLimit S) :=
  ⨅ n : ℕ, K ⊔ (inverseLimitProjection S n).ker

/--
Every subgroup lies inside its finite-level saturation.
-/
lemma level_saturation
    (K : Subgroup (inverseLimit S)) :
    K ≤ S.finiteLevelSaturation K := by
  intro x hx
  rw [finiteLevelSaturation, Subgroup.mem_iInf]
  intro n
  exact (le_sup_left : K ≤ K ⊔ (inverseLimitProjection S n).ker) hx

/--
Membership in the finite-level saturation is a finite-coordinate congruence
condition modulo the subgroup.
-/
lemma finite_level_saturation
    (K : Subgroup (inverseLimit S))
    (x : inverseLimit S) :
    x ∈ S.finiteLevelSaturation K ↔
      ∀ n : ℕ, x ∈ K ⊔ (inverseLimitProjection S n).ker := by
  rw [finiteLevelSaturation, Subgroup.mem_iInf]

/--
The kernel of a finite defect quotient projection is the original descent
kernel enlarged by the corresponding finite projection kernel.
-/
lemma defect_projection_sup
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    (S.finiteDefectProjection φ hprojection n).ker =
      φ.ker ⊔ (inverseLimitProjection S n).ker := by
  rw [finiteDefectProjection, ← MonoidHom.comap_ker,
    defectQuotient, nSubgro.ker_projection]
  change (S.finiteDefectSubgroup φ n).comap (inverseLimitProjection S n) =
    φ.ker ⊔ (inverseLimitProjection S n).ker
  rw [finiteDefectSubgroup, Subgroup.comap_map_eq]

/--
Finite defect quotient transitions are compatible with the finite defect
quotient projections from the original inverse limit.
-/
lemma defect_comp_projection
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    {m n : ℕ}
    (hmn : m ≤ n) :
    (S.finiteDefectTransition φ hprojection hmn).comp
        (S.finiteDefectProjection φ hprojection n) =
      S.finiteDefectProjection φ hprojection m := by
  apply MonoidHom.ext
  intro x
  change S.finiteDefectTransition φ hprojection hmn
      (S.defectQuotient φ hprojection n
        (inverseLimitProjection S n x)) =
    S.defectQuotient φ hprojection m
      (inverseLimitProjection S m x)
  calc
    S.finiteDefectTransition φ hprojection hmn
        (S.defectQuotient φ hprojection n
          (inverseLimitProjection S n x)) =
        S.defectQuotient φ hprojection m
          (S.map hmn (inverseLimitProjection S n x)) := by
          simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun
            (S.defect_transition_comp φ hprojection hmn)
            (inverseLimitProjection S n x)
    _ = S.defectQuotient φ hprojection m
        (inverseLimitProjection S m x) := by
          rw [limit_projection_compat S hmn x]

/--
The canonical completion map from the original inverse limit to the inverse
limit of the finite defect quotient tower.
-/
def finiteDefectCompletion
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    inverseLimit S →*
      inverseLimit (S.finiteDefectSystem φ hprojection) :=
  inverseLimitLift
    (S.finiteDefectSystem φ hprojection)
    (S.finiteDefectProjection φ hprojection)
    (fun hmn => S.defect_comp_projection φ hprojection hmn)

/--
The coordinates of the finite defect quotient completion map are the finite
defect quotient projections.
-/
lemma defect_completion_coordinate
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    (inverseLimitProjection (S.finiteDefectSystem φ hprojection) n).comp
        (S.finiteDefectCompletion φ hprojection) =
      S.finiteDefectProjection φ hprojection n := by
  exact limit_projection_lift
    (S.finiteDefectSystem φ hprojection)
    (S.finiteDefectProjection φ hprojection)
    (fun hmn => S.defect_comp_projection φ hprojection hmn)
    n

/--
The kernel of the finite defect quotient completion map is exactly the
finite-level saturation of the descent kernel.
-/
lemma defect_level_saturation
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    (S.finiteDefectCompletion φ hprojection).ker =
      S.finiteLevelSaturation φ.ker := by
  ext x
  constructor
  · intro hx
    rw [S.finite_level_saturation φ.ker x]
    intro n
    rw [← S.defect_projection_sup φ hprojection n]
    rw [MonoidHom.mem_ker]
    have hcoordinate := congrArg
      (fun ψ : inverseLimit S →*
          S.finiteDefectQuotient φ hprojection n =>
        ψ x)
      (S.defect_completion_coordinate φ hprojection n)
    change inverseLimitProjection (S.finiteDefectSystem φ hprojection) n
        (S.finiteDefectCompletion φ hprojection x) =
      S.finiteDefectProjection φ hprojection n x at hcoordinate
    rw [← hcoordinate, MonoidHom.mem_ker.mp hx]
    exact limit_projection_one (S.finiteDefectSystem φ hprojection) n
  · intro hx
    rw [MonoidHom.mem_ker]
    apply (S.finiteDefectSystem φ hprojection).inverse_limit_projections
    intro n
    have hxprojection :
        x ∈ (S.finiteDefectProjection φ hprojection n).ker := by
      rw [S.defect_projection_sup φ hprojection n]
      exact (S.finite_level_saturation φ.ker x).mp hx n
    have hcoordinate := congrArg
      (fun ψ : inverseLimit S →*
          S.finiteDefectQuotient φ hprojection n =>
        ψ x)
      (S.defect_completion_coordinate φ hprojection n)
    change inverseLimitProjection (S.finiteDefectSystem φ hprojection) n
        (S.finiteDefectCompletion φ hprojection x) =
      S.finiteDefectProjection φ hprojection n x at hcoordinate
    rw [hcoordinate]
    exact MonoidHom.mem_ker.mp hxprojection

/--
Assuming the descent is onto, its finite defect quotient factors assemble into
one comparison map from the target to the finite defect quotient inverse limit.
-/
def finiteDefectComparison
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    H →* inverseLimit (S.finiteDefectSystem φ hprojection) :=
  inverseLimitLift
    (S.finiteDefectSystem φ hprojection)
    (S.finiteDefectFactor φ hφ hprojection)
    (fun hmn => S.defect_transition_factor φ hφ hprojection hmn)

/--
The coordinates of the target finite defect quotient comparison map are the
finite defect quotient factors.
-/
lemma finite_defect_comparison
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n))
    (n : ℕ) :
    (inverseLimitProjection (S.finiteDefectSystem φ hprojection) n).comp
        (S.finiteDefectComparison φ hφ hprojection) =
      S.finiteDefectFactor φ hφ hprojection n := by
  exact limit_projection_lift
    (S.finiteDefectSystem φ hprojection)
    (S.finiteDefectFactor φ hφ hprojection)
    (fun hmn => S.defect_transition_factor φ hφ hprojection hmn)
    n

/--
The target comparison map recovers the finite defect quotient completion map
after precomposition with the original descent.
-/
lemma finite_defect_comp
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    (S.finiteDefectComparison φ hφ hprojection).comp φ =
      S.finiteDefectCompletion φ hprojection := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  have hfactor := congrArg
    (fun ψ : inverseLimit S →* S.finiteDefectQuotient φ hprojection n =>
      ψ x)
    (S.defect_factor_comp φ hφ hprojection n)
  change S.finiteDefectFactor φ hφ hprojection n (φ x) =
    S.finiteDefectProjection φ hprojection n x at hfactor
  exact hfactor

/--
The target is separated by its finite defect quotient tower exactly when the
original descent kernel is already finite-level saturated.
-/
lemma fin_level_saturation
    (hφ : Function.Surjective φ)
    (hprojection : ∀ n : ℕ, Function.Surjective (inverseLimitProjection S n)) :
    Function.Injective (S.finiteDefectComparison φ hφ hprojection) ↔
      S.finiteLevelSaturation φ.ker = φ.ker := by
  constructor
  · intro hInjective
    apply le_antisymm
    · rw [← S.defect_level_saturation φ hprojection]
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have hcomparison := congrArg
        (fun ψ : inverseLimit S →*
            inverseLimit (S.finiteDefectSystem φ hprojection) =>
          ψ x)
        (S.finite_defect_comp φ hφ hprojection)
      change S.finiteDefectComparison φ hφ hprojection (φ x) =
        S.finiteDefectCompletion φ hprojection x at hcomparison
      exact hInjective
        (hcomparison.trans (hx.trans
          (S.finiteDefectComparison φ hφ hprojection).map_one.symm))
    · exact S.level_saturation φ.ker
  · intro hsaturation
    apply (MonoidHom.ker_eq_bot_iff
      (S.finiteDefectComparison φ hφ hprojection)).mp
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_bot]
      rcases hφ y with ⟨x, rfl⟩
      rw [MonoidHom.mem_ker] at hy
      have hcomparison := congrArg
        (fun ψ : inverseLimit S →*
            inverseLimit (S.finiteDefectSystem φ hprojection) =>
          ψ x)
        (S.finite_defect_comp φ hφ hprojection)
      change S.finiteDefectComparison φ hφ hprojection (φ x) =
        S.finiteDefectCompletion φ hprojection x at hcomparison
      have hxcompletion :
          S.finiteDefectCompletion φ hprojection x = 1 :=
        hcomparison.symm.trans hy
      have hxsaturation :
          x ∈ S.finiteLevelSaturation φ.ker := by
        rw [← S.defect_level_saturation φ hprojection,
          MonoidHom.mem_ker]
        exact hxcompletion
      exact MonoidHom.mem_ker.mp (hsaturation ▸ hxsaturation)
    · exact bot_le

end cSQuotie

end Group
end Towers
