import Submission.Group.DegreeOne
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Functorial first Zassenhaus quotient under degree-one reverse inclusion

If the target satisfies the reverse degree-one inclusion `D₂ ≤ G^p [G,G]`, then
surjections with kernel in the source `D₂` are injective on first Zassenhaus
quotients.  This packages the resulting bijections/equivalences.
-/

namespace Submission

open GroupAlgebra

variable (p : ℕ) {G H : Type*} [Group G] [Group H]

/-- Injectivity on `G/D₂ → H/D₂` from a surjection whose kernel lies in `D₂`,
assuming the target has `D₂ ≤ H^p[H,H]`. -/
theorem zQTwo.map_injsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    Function.Injective (zQuot.map p G f 2) := by
  apply zQuot.map_inj_comaple (p := p) (G := G) f
  intro x hx
  have hxF : x ∈ (modPFrattini p H).comap f := hHrev hx
  rw [mod_comap_surjective (p := p) f hs] at hxF
  have hsup : modPFrattini p G ⊔ f.ker ≤ zSubgro p G 2 :=
    sup_le (mod_p_two p G) hker
  exact hsup hxF

/-- Bijectivity on first Zassenhaus quotients under the same hypotheses. -/
theorem zQTwo.map_bijsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    Function.Bijective (zQuot.map p G f 2) :=
  ⟨zQTwo.map_injsurj_kerle (p := p) f hs hHrev hker,
    zQuot.map_surjective p G f hs 2⟩

/-- Additive bijectivity on first Zassenhaus quotients. -/
theorem zTAdditi.mapadd_bijsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    Function.Bijective (zTAdditi.mapAdd p G f) := by
  constructor
  · intro x y hxy
    induction x using Additive.rec with
    | ofMul x' =>
      induction y using Additive.rec with
      | ofMul y' =>
        apply congrArg Additive.ofMul
        exact (zQTwo.map_injsurj_kerle
          (p := p) f hs hHrev hker) hxy
  · exact zTAdditi.mapAdd_surjective (p := p) (G := G) f hs

/-- Linear bijectivity on first Zassenhaus quotients. -/
theorem zTAdditi.maplin_bijsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    Function.Bijective (zTAdditi.mapLinear p G f) := by
  constructor
  · intro x y hxy
    exact (zTAdditi.mapadd_bijsurj_kerle
      (p := p) f hs hHrev hker).1 hxy
  · exact zTAdditi.mapLinear_surjective (p := p) (G := G) f hs

/-- The induced multiplicative map has trivial kernel under the degree-one hypotheses. -/
theorem zQTwo.mapker_eqbot_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zQuot.map p G f 2).ker = ⊥ := by
  exact (MonoidHom.ker_eq_bot_iff (zQuot.map p G f 2)).2
    (zQTwo.map_injsurj_kerle
      (p := p) f hs hHrev hker)

/-- The induced multiplicative map has full range under the degree-one hypotheses. -/
theorem zQTwo.maprange_eqtop_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zQuot.map p G f 2).range = ⊤ := by
  have _hHrev := hHrev
  have _hker := hker
  exact (MonoidHom.range_eq_top).2 (zQuot.map_surjective p G f hs 2)

/-- The induced additive map has trivial kernel under the degree-one hypotheses. -/
theorem zTAdditi.mapadd_kereqbot_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zTAdditi.mapAdd p G f).ker = ⊥ := by
  exact (AddMonoidHom.ker_eq_bot_iff (zTAdditi.mapAdd p G f)).2
    (zTAdditi.mapadd_bijsurj_kerle
      (p := p) f hs hHrev hker).1

/-- The induced additive map has full range under the degree-one hypotheses. -/
theorem zTAdditi.mapadd_rangeeqtop_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zTAdditi.mapAdd p G f).range = ⊤ := by
  exact (AddMonoidHom.range_eq_top).2
    (zTAdditi.mapadd_bijsurj_kerle
      (p := p) f hs hHrev hker).2

/-- The induced linear map has trivial kernel under the degree-one hypotheses. -/
theorem zTAdditi.maplin_kereqbot_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    LinearMap.ker (zTAdditi.mapLinear p G f) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (zTAdditi.maplin_bijsurj_kerle
      (p := p) f hs hHrev hker).1

/-- The induced linear map has full range under the degree-one hypotheses. -/
theorem zTAdditi.maplin_rangeeqtop_surjkerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    LinearMap.range (zTAdditi.mapLinear p G f) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (zTAdditi.maplin_bijsurj_kerle
      (p := p) f hs hHrev hker).2

/-- Multiplicative equivalence on first Zassenhaus quotients under the same hypotheses. -/
noncomputable def zQTwo.equiv_surj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    zQuot p G 2 ≃* zQuot p H 2 :=
  MulEquiv.ofBijective (zQuot.map p G f 2)
    (zQTwo.map_bijsurj_kerle
      (p := p) f hs hHrev hker)

@[simp] theorem zQTwo.equiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (x : zQuot p G 2) :
    zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker x =
      zQuot.map p G f 2 x := rfl

@[simp] theorem zQTwo.equivsurj_kerle_monoidhom
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).toMonoidHom =
      zQuot.map p G f 2 := rfl

@[simp] theorem zQTwo.equivsurj_kerle_symmapplymap
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (x : zQuot p G 2) :
    (zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).symm
        (zQuot.map p G f 2 x) = x := by
  exact (zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).left_inv x

@[simp] theorem zQTwo.mapapply_equivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (y : zQuot p H 2) :
    zQuot.map p G f 2
        ((zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).symm y) = y := by
  change zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker
      ((zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).symm y) = y
  exact (zQTwo.equiv_surj_kerle (p := p) f hs hHrev hker).right_inv y

/-- Characterize equality to the induced map via the inverse equivalence. -/
theorem zQTwo.mapeqiff_eqequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2)
    (x : zQuot p G 2) (y : zQuot p H 2) :
    zQuot.map p G f 2 x = y ↔
      x = (zQTwo.equiv_surj_kerle (p := p)
        f hs hHrev hker).symm y := by
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Additive equivalence on first Zassenhaus quotients under the same hypotheses. -/
noncomputable def zTAdditi.add_equivsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    zTAdditi p G ≃+ zTAdditi p H :=
  AddEquiv.ofBijective (zTAdditi.mapAdd p G f)
    (zTAdditi.mapadd_bijsurj_kerle
      (p := p) f hs hHrev hker)

@[simp] theorem zTAdditi.addequiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (x : zTAdditi p G) :
    zTAdditi.add_equivsurj_kerle (p := p) f hs hHrev hker x =
      zTAdditi.mapAdd p G f x := rfl

@[simp] theorem zTAdditi.addequiv_surjkerle_addmonoidhom
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zTAdditi.add_equivsurj_kerle (p := p)
      f hs hHrev hker).toAddMonoidHom =
      zTAdditi.mapAdd p G f := rfl

@[simp] theorem zTAdditi.addequivsurj_kerlesymm_applymapadd
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (x : zTAdditi p G) :
    (zTAdditi.add_equivsurj_kerle (p := p)
        f hs hHrev hker).symm (zTAdditi.mapAdd p G f x) = x := by
  exact (zTAdditi.add_equivsurj_kerle (p := p)
    f hs hHrev hker).left_inv x

@[simp] theorem zTAdditi.mapaddapply_addequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (y : zTAdditi p H) :
    zTAdditi.mapAdd p G f
        ((zTAdditi.add_equivsurj_kerle (p := p)
          f hs hHrev hker).symm y) = y := by
  change zTAdditi.add_equivsurj_kerle (p := p)
      f hs hHrev hker
      ((zTAdditi.add_equivsurj_kerle (p := p)
        f hs hHrev hker).symm y) = y
  exact (zTAdditi.add_equivsurj_kerle (p := p)
    f hs hHrev hker).right_inv y

/-- Characterize equality to the additive induced map via the inverse equivalence. -/
theorem zTAdditi.mapaddeq_iffeqaddequiv_surjkerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2)
    (x : zTAdditi p G) (y : zTAdditi p H) :
    zTAdditi.mapAdd p G f x = y ↔
      x = (zTAdditi.add_equivsurj_kerle (p := p)
        f hs hHrev hker).symm y := by
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Linear equivalence on first Zassenhaus quotients under the same hypotheses. -/
noncomputable def zTAdditi.lin_equivsurj_kerle
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    zTAdditi p G ≃ₗ[ZMod p] zTAdditi p H :=
  LinearEquiv.ofBijective (zTAdditi.mapLinear p G f)
    (zTAdditi.maplin_bijsurj_kerle
      (p := p) f hs hHrev hker)

@[simp] theorem zTAdditi.linequiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2)
    (x : zTAdditi p G) :
    zTAdditi.lin_equivsurj_kerle (p := p)
      f hs hHrev hker x = zTAdditi.mapLinear p G f x := rfl

@[simp] theorem zTAdditi.linequiv_surjker_lelinmap
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) :
    (zTAdditi.lin_equivsurj_kerle (p := p)
      f hs hHrev hker).toLinearMap =
      zTAdditi.mapLinear p G f := rfl

@[simp] theorem zTAdditi.linequivsurj_kerlesymm_applymaplin
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (x : zTAdditi p G) :
    (zTAdditi.lin_equivsurj_kerle (p := p)
        f hs hHrev hker).symm (zTAdditi.mapLinear p G f x) = x := by
  exact (zTAdditi.lin_equivsurj_kerle (p := p)
    f hs hHrev hker).left_inv x

@[simp] theorem zTAdditi.maplinapply_linequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2) (y : zTAdditi p H) :
    zTAdditi.mapLinear p G f
        ((zTAdditi.lin_equivsurj_kerle (p := p)
          f hs hHrev hker).symm y) = y := by
  change zTAdditi.lin_equivsurj_kerle (p := p)
      f hs hHrev hker
      ((zTAdditi.lin_equivsurj_kerle (p := p)
        f hs hHrev hker).symm y) = y
  exact (zTAdditi.lin_equivsurj_kerle (p := p)
    f hs hHrev hker).right_inv y

/-- Characterize equality to the linear induced map via the inverse equivalence. -/
theorem zTAdditi.maplineq_iffeqlinequiv_surjkerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hHrev : zSubgro p H 2 ≤ modPFrattini p H)
    (hker : f.ker ≤ zSubgro p G 2)
    (x : zTAdditi p G) (y : zTAdditi p H) :
    zTAdditi.mapLinear p G f x = y ↔
      x = (zTAdditi.lin_equivsurj_kerle (p := p)
        f hs hHrev hker).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (zTAdditi.linequivsurj_kerlesymm_applymaplin
      (p := p) f hs hHrev hker x).symm
  · intro h
    rw [h]
    exact zTAdditi.maplinapply_linequivsurj_kerlesymm
      (p := p) f hs hHrev hker y

end Submission
