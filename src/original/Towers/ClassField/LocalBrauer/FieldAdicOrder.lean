import Towers.NumberTheory.Locals.LocalDegreeFormula
import Towers.ClassField.LocalBrauer.LocalFieldOrder

/-!
# Local-field order and maximal-ideal adic order

The normalized order supplied by the local-field value group agrees with the
normalized adic order of the maximal ideal in the integer ring.  This lets us
transport the usual ramification-index restriction formula directly to the
order used in the local Brauer invariant.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel

/-- Two surjective additive homomorphisms to `ℤ` which induce the same order
on their source are equal. -/
theorem surjective_add_hom
    {G : Type*} [AddCommGroup G] (f g : G →+ ℤ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : ∀ x y, f x ≤ f y ↔ g x ≤ g y) : f = g := by
  obtain ⟨u, hu⟩ := hf 1
  obtain ⟨v, hv⟩ := hg 1
  have hgu_pos : 0 < g u := by
    have hnot : ¬g u ≤ g 0 := by
      intro h
      have := (hfg u 0).2 h
      simp [hu] at this
    simpa using lt_of_not_ge hnot
  have hfv_pos : 0 < f v := by
    have hnot : ¬f v ≤ f 0 := by
      intro h
      have := (hfg v 0).1 h
      simp [hv] at this
    simpa using lt_of_not_ge hnot
  have hgu_le_one : g u ≤ 1 := by
    have huv : f u ≤ f v := by
      rw [hu]
      omega
    simpa [hv] using (hfg u v).1 huv
  have hgu : g u = 1 := by omega
  ext x
  let n : ℤ := f x
  have hfn : f (n • u) = f x := by
    simp [n, hu]
  have hle : g (n • u) ≤ g x :=
    (hfg (n • u) x).1 hfn.le
  have hge : g x ≤ g (n • u) :=
    (hfg x (n • u)).1 hfn.ge
  have hgx : g x = f x := by
    calc
      g x = g (n • u) := le_antisymm hge hle
      _ = f x := by simp [n, hgu]
  exact hgx.symm

/-- The normalized adic order as an additive homomorphism on the unit group
of the fraction field. -/
def normalizedAdicHom
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : IsDedekindDomain.HeightOneSpectrum A) : Additive Kˣ →+ ℤ where
  toFun x :=
    Towers.NumberTheory.Milne.normalizedAdicOrder p x.toMul
  map_zero' := by
    simp [Towers.NumberTheory.Milne.normalizedAdicOrder]
  map_add' x y := by
    have hx : p.valuation K (x.toMul : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact x.toMul.ne_zero
    have hy : p.valuation K (y.toMul : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact y.toMul.ne_zero
    change -WithZero.log
        (p.valuation K ((x.toMul : K) * (y.toMul : K))) = _
    rw [map_mul, WithZero.log_mul hx hy]
    simp only [Towers.NumberTheory.Milne.normalizedAdicOrder]
    abel

@[simp]
theorem normalized_adic_order
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : IsDedekindDomain.HeightOneSpectrum A) (x : Additive Kˣ) :
    normalizedAdicHom p x =
      Towers.NumberTheory.Milne.normalizedAdicOrder p x.toMul :=
  rfl

/-- The adic-order homomorphism is onto. -/
theorem normalized_adic_surjective
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : IsDedekindDomain.HeightOneSpectrum A) :
    Function.Surjective (normalizedAdicHom (K := K) p) := by
  intro z
  obtain ⟨x, hx⟩ :=
    Towers.NumberTheory.Milne.normalized_order_surjective
      p (K := K) z
  exact ⟨Additive.ofMul x, hx⟩

/-- Comparing normalized adic orders reverses comparison of the associated
multiplicative valuations. -/
theorem normalized_adic_valuation
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : IsDedekindDomain.HeightOneSpectrum A) (x y : Kˣ) :
    normalizedAdicHom p (Additive.ofMul x) ≤
        normalizedAdicHom p (Additive.ofMul y) ↔
      p.valuation K (y : K) ≤ p.valuation K (x : K) := by
  have hx : p.valuation K (x : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact x.ne_zero
  have hy : p.valuation K (y : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact y.ne_zero
  change -WithZero.log (p.valuation K (x : K)) ≤
      -WithZero.log (p.valuation K (y : K)) ↔ _
  rw [neg_le_neg_iff, WithZero.log_le_log hy hx]

/-- The local-field normalized order is the normalized adic order at the
maximal ideal of its integer ring. -/
theorem normalized_adic_hom
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))] :
    localUnitOrder K =
      normalizedAdicHom (K := K)
        (IsDiscreteValuationRing.maximalIdeal 𝒪[K]) := by
  let p := IsDiscreteValuationRing.maximalIdeal 𝒪[K]
  have hequiv :
      (p.valuation K).IsEquiv (valuation K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        IsDiscreteValuationRing.exists_lift_of_le_one hx
      rw [← ha]
      exact (Valuation.mem_integer_iff (valuation K) _).2 a.property
    · intro hx
      let a : 𝒪[K] :=
        ⟨x, (Valuation.mem_integer_iff (valuation K) _).1 hx⟩
      simpa [a] using p.valuation_le_one (K := K) a
  apply surjective_add_hom
  · exact local_order_surjective K
  · exact normalized_adic_surjective (K := K) p
  · intro x y
    change localUnitOrder K (Additive.ofMul x.toMul) ≤
        localUnitOrder K (Additive.ofMul y.toMul) ↔
      normalizedAdicHom (K := K) p (Additive.ofMul x.toMul) ≤
        normalizedAdicHom (K := K) p (Additive.ofMul y.toMul)
    rw [local_order_valuation K]
    rw [normalized_adic_valuation (K := K) p]
    exact hequiv.le_iff_le.symm

/-- Normalized local-field order scales under a finite extension by the
ramification index of the maximal ideals.  The algebra and scalar-tower
hypotheses say that the chosen map of integer rings is the restriction of
the field extension map. -/
theorem algebra_ramification_idx
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField L] [IsUltrametricDist L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [Valuation.Compatible (NormedField.valuation (K := L))]
    [Algebra K L] [Algebra 𝒪[K] 𝒪[L]]
    [Module.IsTorsionFree 𝒪[K] 𝒪[L]]
    [IsScalarTower 𝒪[K] K L] [IsScalarTower 𝒪[K] 𝒪[L] L]
    [(IsDiscreteValuationRing.maximalIdeal 𝒪[L]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal]
    (x : Kˣ) :
    localUnitOrder L
        (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) *
        localUnitOrder K (Additive.ofMul x) := by
  rw [normalized_adic_hom K,
    normalized_adic_hom L]
  exact
    Towers.NumberTheory.Milne.normalized_adic_ramification
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K])
      (IsDiscreteValuationRing.maximalIdeal 𝒪[L]) x

end

end Towers.CField.LBrauer
