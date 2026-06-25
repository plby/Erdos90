import Submission.Group.FrattiniFunctor
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.FieldTheory.Finiteness

/-!
# Isomorphisms of mod-`p` Frattini quotients from kernel criteria

A surjective homomorphism whose kernel is contained in `G^p [G,G]` induces
multiplicative, additive, and linear equivalences on mod-`p` Frattini quotients.
-/

namespace Submission

variable (p : ℕ) {G H : Type*} [Group G] [Group H]

/-- Multiplicative equivalence on Frattini quotients induced by a suitable
surjection. -/
noncomputable def mFQuot.equiv_surj_kerle (f : G →* H)
    (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    mFQuot p G ≃* mFQuot p H :=
  MulEquiv.ofBijective (mFQuot.map (p := p) f)
    (mFQuot.map_bijsurj_kerle (p := p) f hs hker)

@[simp] theorem mFQuot.equiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFQuot p G) :
    mFQuot.equiv_surj_kerle (p := p) f hs hker x =
      mFQuot.map (p := p) f x := rfl

/-- Representative formula for the multiplicative Frattini equivalence. -/
@[simp] theorem mFQuot.equiv_surjker_lemk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) :
    mFQuot.equiv_surj_kerle (p := p) f hs hker
        (mFQuot.mk p G g) =
      mFQuot.mk p H (f g) := rfl

/-- Additive equivalence on additive Frattini quotients induced by a suitable
surjection. -/
noncomputable def mFAdditi.add_equivsurj_kerle (f : G →* H)
    (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    mFAdditi p G ≃+ mFAdditi p H :=
  AddEquiv.ofBijective (mFAdditi.mapAdd (p := p) f)
    (mFAdditi.mapadd_bijsurj_kerle (p := p) f hs hker)

@[simp] theorem mFAdditi.addequiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFAdditi p G) :
    mFAdditi.add_equivsurj_kerle (p := p) f hs hker x =
      mFAdditi.mapAdd (p := p) f x := rfl

/-- Representative formula for the additive Frattini equivalence. -/
@[simp] theorem mFAdditi.addequiv_surjker_lemk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) :
    mFAdditi.add_equivsurj_kerle (p := p) f hs hker
        (Additive.ofMul (mFQuot.mk p G g)) =
      Additive.ofMul (mFQuot.mk p H (f g)) := rfl

/-- `ZMod p`-linear equivalence on Frattini quotients induced by a suitable
surjection. -/
noncomputable def mFAdditi.lin_equivsurj_kerle (f : G →* H)
    (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    mFAdditi p G ≃ₗ[ZMod p] mFAdditi p H :=
  LinearEquiv.ofBijective (mFAdditi.mapLinear (p := p) f)
    (mFAdditi.maplin_bijsurj_kerle (p := p) f hs hker)

@[simp] theorem mFAdditi.linequiv_surjker_leapply
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFAdditi p G) :
    mFAdditi.lin_equivsurj_kerle (p := p) f hs hker x =
      mFAdditi.mapLinear (p := p) f x := rfl

/-- Representative formula for the linear Frattini equivalence. -/
@[simp] theorem mFAdditi.linequiv_surjker_lemk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) :
    mFAdditi.lin_equivsurj_kerle (p := p) f hs hker
        (Additive.ofMul (mFQuot.mk p G g)) =
      Additive.ofMul (mFQuot.mk p H (f g)) := rfl

@[simp] theorem mFQuot.equivsurj_kerle_monoidhom
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) :
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toMonoidHom =
      mFQuot.map (p := p) f := rfl

@[simp] theorem mFQuot.equivsurj_kerle_symmapplymap
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFQuot p G) :
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).symm
        (mFQuot.map (p := p) f x) = x := by
  exact (mFQuot.equiv_surj_kerle (p := p) f hs hker).left_inv x

@[simp] theorem mFQuot.mapapply_equivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (y : mFQuot p H) :
    mFQuot.map (p := p) f
        ((mFQuot.equiv_surj_kerle (p := p) f hs hker).symm y) = y := by
  change mFQuot.equiv_surj_kerle (p := p) f hs hker
      ((mFQuot.equiv_surj_kerle (p := p) f hs hker).symm y) = y
  exact (mFQuot.equiv_surj_kerle (p := p) f hs hker).right_inv y

/-- The induced Frattini equivalence of the identity homomorphism is the identity. -/
@[simp] theorem mFQuot.equiv_surjker_leid
    (hs : Function.Surjective (MonoidHom.id G))
    (hker : (MonoidHom.id G).ker ≤ modPFrattini p G) :
    mFQuot.equiv_surj_kerle (p := p) (MonoidHom.id G) hs hker =
      MulEquiv.refl (mFQuot p G) := by
  ext x
  simp [mFQuot.equiv_surjker_leapply]

/-- Surjectivity of a composite of surjective group homomorphisms (local wrapper). -/
theorem mFQuot.surjective_comp {K : Type*} [Group K]
    (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g) :
    Function.Surjective (g.comp f) := by
  intro k
  rcases hsg k with ⟨h, rfl⟩
  rcases hsf h with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Kernel containment for a composite of Frattini-isomorphism-inducing maps. -/
theorem mFQuot.kercomp_lemod_pfratt
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    (g.comp f).ker ≤ modPFrattini p G := by
  intro x hx
  have hxpre : x ∈ (modPFrattini p H).comap f := by
    exact hkg hx
  rw [mod_comap_surjective (p := p) f hsf] at hxpre
  exact (sup_le le_rfl hkf) hxpre

/-- Composition law for induced Frattini equivalences. -/
theorem mFQuot.equiv_surjker_lecomp
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H)
    (hsc : Function.Surjective (g.comp f))
    (hkc : (g.comp f).ker ≤ modPFrattini p G) :
    mFQuot.equiv_surj_kerle (p := p) (g.comp f) hsc hkc =
      (mFQuot.equiv_surj_kerle (p := p) f hsf hkf).trans
        (mFQuot.equiv_surj_kerle (p := p) g hsg hkg) := by
  ext x
  simp [mFQuot.equiv_surjker_leapply,
    mFQuot.map_comp]

/-- Composition law using canonical composite hypotheses. -/
theorem mFQuot.equivsurj_kerle_compcanon
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    mFQuot.equiv_surj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg) =
      (mFQuot.equiv_surj_kerle (p := p) f hsf hkf).trans
        (mFQuot.equiv_surj_kerle (p := p) g hsg hkg) := by
  exact mFQuot.equiv_surjker_lecomp (p := p) f g hsf hsg hkf hkg _ _

/-- Inverse form of the canonical composition law for induced Frattini equivalences. -/
theorem mFQuot.equivsurj_kerle_compcanonsymm
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    (mFQuot.equiv_surj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg)).symm =
      ((mFQuot.equiv_surj_kerle (p := p) (f := g)
          (hs := hsg) (hker := hkg)).symm).trans
        ((mFQuot.equiv_surj_kerle (p := p) (f := f)
          (hs := hsf) (hker := hkf)).symm) := by
  rw [mFQuot.equivsurj_kerle_compcanon (p := p) f g hsf hsg hkf hkg]
  rfl

/-- Inverse representative formula for an induced Frattini equivalence, given a chosen lift. -/
theorem mFQuot.equivsurj_kerlesymm_mkapplyeq
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) (h : H) (hh : f g = h) :
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).symm
        (mFQuot.mk p H h) =
      mFQuot.mk p G g := by
  subst h
  exact mFQuot.equivsurj_kerle_symmapplymap
    (p := p) f hs hker (mFQuot.mk p G g)

/-- Choose a representative for the inverse of an induced Frattini equivalence. -/
theorem mFQuot.existslift_equivsurjker_lesymmmk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (h : H) :
    ∃ g : G, f g = h ∧
      (mFQuot.equiv_surj_kerle (p := p) f hs hker).symm
        (mFQuot.mk p H h) = mFQuot.mk p G g := by
  rcases hs h with ⟨g, rfl⟩
  refine ⟨g, rfl, ?_⟩
  exact mFQuot.equivsurj_kerlesymm_mkapplyeq
    (p := p) f hs hker g (f g) rfl

/-- Characterize equality to the induced Frattini quotient map via the inverse equivalence. -/
theorem mFQuot.mapeqiff_eqequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G)
    (x : mFQuot p G) (y : mFQuot p H) :
    mFQuot.map (p := p) f x = y ↔
      x = (mFQuot.equiv_surj_kerle (p := p) f hs hker).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (mFQuot.equivsurj_kerle_symmapplymap
      (p := p) f hs hker x).symm
  · intro h
    rw [h]
    exact mFQuot.mapapply_equivsurj_kerlesymm
      (p := p) f hs hker y

@[simp] theorem mFAdditi.addequiv_surjkerle_addmonoidhom
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) :
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toAddMonoidHom =
      mFAdditi.mapAdd (p := p) f := rfl

@[simp] theorem mFAdditi.addequivsurj_kerlesymm_applymapadd
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFAdditi p G) :
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm
        (mFAdditi.mapAdd (p := p) f x) = x := by
  exact (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).left_inv x

@[simp] theorem mFAdditi.mapaddapply_addequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (y : mFAdditi p H) :
    mFAdditi.mapAdd (p := p) f
        ((mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm y) = y := by
  change mFAdditi.add_equivsurj_kerle (p := p) f hs hker
      ((mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm y) = y
  exact (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).right_inv y

/-- The induced additive Frattini equivalence of the identity homomorphism is the identity. -/
@[simp] theorem mFAdditi.addequiv_surjker_leid
    (hs : Function.Surjective (MonoidHom.id G))
    (hker : (MonoidHom.id G).ker ≤ modPFrattini p G) :
    mFAdditi.add_equivsurj_kerle (p := p) (MonoidHom.id G) hs hker =
      AddEquiv.refl (mFAdditi p G) := by
  ext x
  simp [mFAdditi.addequiv_surjker_leapply]

/-- Composition law for induced additive Frattini equivalences. -/
theorem mFAdditi.addequiv_surjker_lecomp
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H)
    (hsc : Function.Surjective (g.comp f))
    (hkc : (g.comp f).ker ≤ modPFrattini p G) :
    mFAdditi.add_equivsurj_kerle (p := p) (g.comp f) hsc hkc =
      (mFAdditi.add_equivsurj_kerle (p := p) f hsf hkf).trans
        (mFAdditi.add_equivsurj_kerle (p := p) g hsg hkg) := by
  ext x
  simp [mFAdditi.addequiv_surjker_leapply,
    mFAdditi.mapAdd_comp]

/-- Additive composition law using canonical composite hypotheses. -/
theorem mFAdditi.addequiv_surjker_lecompcanon
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    mFAdditi.add_equivsurj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg) =
      (mFAdditi.add_equivsurj_kerle (p := p) f hsf hkf).trans
        (mFAdditi.add_equivsurj_kerle (p := p) g hsg hkg) := by
  exact mFAdditi.addequiv_surjker_lecomp (p := p) f g hsf hsg hkf hkg _ _

/-- Inverse form of the canonical composition law for induced additive Frattini equivalences. -/
theorem mFAdditi.addequiv_surjkerle_compcanonsymm
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    (mFAdditi.add_equivsurj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg)).symm =
      ((mFAdditi.add_equivsurj_kerle (p := p) (f := g)
          (hs := hsg) (hker := hkg)).symm).trans
        ((mFAdditi.add_equivsurj_kerle (p := p) (f := f)
          (hs := hsf) (hker := hkf)).symm) := by
  rw [mFAdditi.addequiv_surjker_lecompcanon (p := p) f g hsf hsg hkf hkg]
  rfl

/-- Inverse representative formula for an induced additive Frattini equivalence, given a lift. -/
theorem mFAdditi.addequivsurj_kerlesymm_mkapplyeq
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) (h : H) (hh : f g = h) :
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm
        (Additive.ofMul (mFQuot.mk p H h)) =
      Additive.ofMul (mFQuot.mk p G g) := by
  subst h
  exact mFAdditi.addequivsurj_kerlesymm_applymapadd
    (p := p) f hs hker (Additive.ofMul (mFQuot.mk p G g))

/-- Choose a representative for the inverse of an induced additive Frattini equivalence. -/
theorem mFAdditi.existsliftadd_equivsurjker_lesymmmk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (h : H) :
    ∃ g : G, f g = h ∧
      (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm
        (Additive.ofMul (mFQuot.mk p H h)) =
          Additive.ofMul (mFQuot.mk p G g) := by
  rcases hs h with ⟨g, rfl⟩
  refine ⟨g, rfl, ?_⟩
  exact mFAdditi.addequivsurj_kerlesymm_mkapplyeq
    (p := p) f hs hker g (f g) rfl

/-- Characterize equality to the additive Frattini map via the inverse equivalence. -/
theorem mFAdditi.mapaddeq_iffeqaddequiv_surjkerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G)
    (x : mFAdditi p G) (y : mFAdditi p H) :
    mFAdditi.mapAdd (p := p) f x = y ↔
      x = (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (mFAdditi.addequivsurj_kerlesymm_applymapadd
      (p := p) f hs hker x).symm
  · intro h
    rw [h]
    exact mFAdditi.mapaddapply_addequivsurj_kerlesymm
      (p := p) f hs hker y

@[simp] theorem mFAdditi.linequiv_surjker_lelinmap
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) :
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).toLinearMap =
      mFAdditi.mapLinear (p := p) f := rfl

@[simp] theorem mFAdditi.linequivsurj_kerlesymm_applymaplin
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (x : mFAdditi p G) :
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm
        (mFAdditi.mapLinear (p := p) f x) = x := by
  exact (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).left_inv x

@[simp] theorem mFAdditi.maplinapply_linequivsurj_kerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (y : mFAdditi p H) :
    mFAdditi.mapLinear (p := p) f
        ((mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm y) = y := by
  change mFAdditi.lin_equivsurj_kerle (p := p) f hs hker
      ((mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm y) = y
  exact (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).right_inv y

/-- The induced linear Frattini equivalence of the identity homomorphism is the identity. -/
@[simp] theorem mFAdditi.linequiv_surjker_leid
    (hs : Function.Surjective (MonoidHom.id G))
    (hker : (MonoidHom.id G).ker ≤ modPFrattini p G) :
    mFAdditi.lin_equivsurj_kerle (p := p) (MonoidHom.id G) hs hker =
      LinearEquiv.refl (ZMod p) (mFAdditi p G) := by
  ext x
  simp [mFAdditi.linequiv_surjker_leapply]

/-- Composition law for induced linear Frattini equivalences. -/
theorem mFAdditi.linequiv_surjker_lecomp
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H)
    (hsc : Function.Surjective (g.comp f))
    (hkc : (g.comp f).ker ≤ modPFrattini p G) :
    mFAdditi.lin_equivsurj_kerle (p := p) (g.comp f) hsc hkc =
      (mFAdditi.lin_equivsurj_kerle (p := p) f hsf hkf).trans
        (mFAdditi.lin_equivsurj_kerle (p := p) g hsg hkg) := by
  ext x
  simp [mFAdditi.linequiv_surjker_leapply,
    mFAdditi.mapLinear_comp]

/-- Linear composition law using canonical composite hypotheses. -/
theorem mFAdditi.linequiv_surjker_lecompcanon
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    mFAdditi.lin_equivsurj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg) =
      (mFAdditi.lin_equivsurj_kerle (p := p) f hsf hkf).trans
        (mFAdditi.lin_equivsurj_kerle (p := p) g hsg hkg) := by
  exact mFAdditi.linequiv_surjker_lecomp (p := p) f g hsf hsg hkf hkg _ _

/-- Inverse form of the canonical composition law for induced linear Frattini equivalences. -/
theorem mFAdditi.linequiv_surjkerle_compcanonsymm
    {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hkf : f.ker ≤ modPFrattini p G) (hkg : g.ker ≤ modPFrattini p H) :
    (mFAdditi.lin_equivsurj_kerle (p := p) (g.comp f)
        (mFQuot.surjective_comp f g hsf hsg)
        (mFQuot.kercomp_lemod_pfratt (p := p) f g hsf hkf hkg)).symm =
      ((mFAdditi.lin_equivsurj_kerle (p := p) (f := g)
          (hs := hsg) (hker := hkg)).symm).trans
        ((mFAdditi.lin_equivsurj_kerle (p := p) (f := f)
          (hs := hsf) (hker := hkf)).symm) := by
  rw [mFAdditi.linequiv_surjker_lecompcanon (p := p) f g hsf hsg hkf hkg]
  rfl

/-- Inverse representative formula for an induced linear Frattini equivalence, given a lift. -/
theorem mFAdditi.linequivsurj_kerlesymm_mkapplyeq
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (g : G) (h : H) (hh : f g = h) :
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm
        (Additive.ofMul (mFQuot.mk p H h)) =
      Additive.ofMul (mFQuot.mk p G g) := by
  subst h
  exact mFAdditi.linequivsurj_kerlesymm_applymaplin
    (p := p) f hs hker (Additive.ofMul (mFQuot.mk p G g))

/-- Choose a representative for the inverse of an induced linear Frattini equivalence. -/
theorem mFAdditi.existsliftlin_equivsurjker_lesymmmk
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G) (h : H) :
    ∃ g : G, f g = h ∧
      (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm
        (Additive.ofMul (mFQuot.mk p H h)) =
          Additive.ofMul (mFQuot.mk p G g) := by
  rcases hs h with ⟨g, rfl⟩
  refine ⟨g, rfl, ?_⟩
  exact mFAdditi.linequivsurj_kerlesymm_mkapplyeq
    (p := p) f hs hker g (f g) rfl

/-- Characterize equality to the linear Frattini map via the inverse equivalence. -/
theorem mFAdditi.maplineq_iffeqlinequiv_surjkerlesymm
    (f : G →* H) (hs : Function.Surjective f)
    (hker : f.ker ≤ modPFrattini p G)
    (x : mFAdditi p G) (y : mFAdditi p H) :
    mFAdditi.mapLinear (p := p) f x = y ↔
      x = (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (mFAdditi.linequivsurj_kerlesymm_applymaplin
      (p := p) f hs hker x).symm
  · intro h
    rw [h]
    exact mFAdditi.maplinapply_linequivsurj_kerlesymm
      (p := p) f hs hker y


/-- Additive form of the product equivalence for mod-`p` Frattini quotients. -/
noncomputable def mFAdditi.prodAddEquiv (G H : Type*) [Group G] [Group H] :
    mFAdditi p (G × H) ≃+
      (mFAdditi p G × mFAdditi p H) :=
{ toFun := fun x =>
    (Additive.ofMul ((mFQuot.prodEquiv p G H x.toMul).1),
      Additive.ofMul ((mFQuot.prodEquiv p G H x.toMul).2))
  invFun := fun y =>
    Additive.ofMul ((mFQuot.prodEquiv p G H).symm (y.1.toMul, y.2.toMul))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    change Additive.ofMul ((mFQuot.prodEquiv p G H).symm
        (mFQuot.prodEquiv p G H q)) = Additive.ofMul q
    rw [MulEquiv.symm_apply_apply]
  right_inv := by
    intro y
    rcases y with ⟨a, b⟩
    cases a using Additive.rec
    cases b using Additive.rec
    rename_i qa qb
    change (Additive.ofMul ((mFQuot.prodEquiv p G H
        ((mFQuot.prodEquiv p G H).symm (qa, qb))).1),
      Additive.ofMul ((mFQuot.prodEquiv p G H
        ((mFQuot.prodEquiv p G H).symm (qa, qb))).2)) =
        (Additive.ofMul qa, Additive.ofMul qb)
    rw [MulEquiv.apply_symm_apply]
  map_add' := by
    intro x y
    cases x using Additive.rec
    cases y using Additive.rec
    simp [ofMul_mul] }

@[simp] theorem mFAdditi.prod_add_equivmul (G H : Type*) [Group G] [Group H]
    (g : G) (h : H) :
    mFAdditi.prodAddEquiv (p := p) G H
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) := rfl


/-- First projection of the additive Frattini product equivalence. -/
@[simp] theorem mFAdditi.prod_add_equivfst (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodAddEquiv (p := p) G H x).1 =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro gh
  rcases gh with ⟨g, h⟩
  rfl

/-- Second projection of the additive Frattini product equivalence. -/
@[simp] theorem mFAdditi.prod_add_equivsnd (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodAddEquiv (p := p) G H x).2 =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro gh
  rcases gh with ⟨g, h⟩
  rfl


/-- The second additive product coordinate is zero when the right factor is trivial. -/
@[simp] theorem mFAdditi.prodadd_equivright_trivialsnd
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    (mFAdditi.prodAddEquiv (p := p) G E x).2 = 0 :=
  Subsingleton.elim _ _

/-- The first additive product coordinate is zero when the left factor is trivial. -/
@[simp] theorem mFAdditi.prodadd_equivleft_trivialfst
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    (mFAdditi.prodAddEquiv (p := p) E G x).1 = 0 :=
  Subsingleton.elim _ _


@[simp] theorem mFAdditi.prod_addequiv_symmmul (G H : Type*) [Group G] [Group H]
    (g : G) (h : H) :
    (mFAdditi.prodAddEquiv (p := p) G H).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := by
  apply (mFAdditi.prodAddEquiv (p := p) G H).injective
  simp only [AddEquiv.apply_symm_apply]
  change (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) = _
  rw [mFAdditi.prod_add_equivmul]

/-- Inserting in the first factor is the inverse product equivalence on `(x, 0)`. -/
@[simp] theorem mFAdditi.prod_addequiv_symminl
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    (mFAdditi.prodAddEquiv (p := p) G H).symm (x, 0) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change (mFAdditi.prodAddEquiv (p := p) G H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
       Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) (1 : H))) = _
  rw [mFAdditi.prod_addequiv_symmmul]
  rfl

/-- Inserting in the second factor is the inverse product equivalence on `(0, y)`. -/
@[simp] theorem mFAdditi.prod_addequiv_symminr
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    (mFAdditi.prodAddEquiv (p := p) G H).symm (0, y) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) y := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  change (mFAdditi.prodAddEquiv (p := p) G H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) (1 : G)),
       Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) = _
  rw [mFAdditi.prod_addequiv_symmmul]
  rfl

/-- Inverse additive product splitting with a trivial right factor ignores that coordinate. -/
@[simp] theorem mFAdditi.prodadd_equivsymm_righttrivial
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) (y : mFAdditi p E) :
    (mFAdditi.prodAddEquiv (p := p) G E).symm (x, y) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl G E) x := by
  have hy : y = 0 := Subsingleton.elim y 0
  subst y
  simp

/-- Inverse additive product splitting with a trivial left factor ignores that coordinate. -/
@[simp] theorem mFAdditi.prodadd_equivsymm_lefttrivial
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p E) (y : mFAdditi p G) :
    (mFAdditi.prodAddEquiv (p := p) E G).symm (x, y) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr E G) y := by
  have hx : x = 0 := Subsingleton.elim x 0
  subst x
  simp

/-- Linear form of the product equivalence for mod-`p` Frattini quotients. -/
noncomputable def mFAdditi.prodLinearEquiv [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    mFAdditi p (G × H) ≃ₗ[ZMod p]
      (mFAdditi p G × mFAdditi p H) :=
  let e := mFAdditi.prodAddEquiv (p := p) G H
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) <| by
    constructor
    · intro x y h
      exact e.injective h
    · intro y
      rcases e.surjective y with ⟨x, hx⟩
      exact ⟨x, hx⟩

@[simp] theorem mFAdditi.prod_lin_equivapply [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p (G × H)) :
    mFAdditi.prodLinearEquiv (p := p) G H x =
      mFAdditi.prodAddEquiv (p := p) G H x := rfl

@[simp] theorem mFAdditi.prod_lin_equivmul [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (g : G) (h : H) :
    mFAdditi.prodLinearEquiv (p := p) G H
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) := rfl

/-- First projection of the linear Frattini product equivalence. -/
@[simp] theorem mFAdditi.prod_lin_equivfst [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodLinearEquiv (p := p) G H x).1 =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G H) x := by
  rw [mFAdditi.prod_lin_equivapply]
  rw [mFAdditi.prod_add_equivfst]
  rfl

/-- Second projection of the linear Frattini product equivalence. -/
@[simp] theorem mFAdditi.prod_lin_equivsnd [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodLinearEquiv (p := p) G H x).2 =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd G H) x := by
  rw [mFAdditi.prod_lin_equivapply]
  rw [mFAdditi.prod_add_equivsnd]
  rfl


/-- The second linear product coordinate is zero when the right factor is trivial. -/
@[simp] theorem mFAdditi.prodlin_equivright_trivialsnd [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    (mFAdditi.prodLinearEquiv (p := p) G E x).2 = 0 :=
  Subsingleton.elim _ _

/-- The first linear product coordinate is zero when the left factor is trivial. -/
@[simp] theorem mFAdditi.prodlin_equivleft_trivialfst [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    (mFAdditi.prodLinearEquiv (p := p) E G x).1 = 0 :=
  Subsingleton.elim _ _


@[simp] theorem mFAdditi.prod_linequiv_symmmul [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (g : G) (h : H) :
    (mFAdditi.prodLinearEquiv (p := p) G H).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := by
  apply (mFAdditi.prodLinearEquiv (p := p) G H).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl


/-- Inserting in the first factor is the inverse linear product equivalence on `(x, 0)`. -/
@[simp] theorem mFAdditi.prod_linequiv_symminl [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    (mFAdditi.prodLinearEquiv (p := p) G H).symm (x, 0) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change (mFAdditi.prodLinearEquiv (p := p) G H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) g),
       Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) (1 : H))) = _
  rw [mFAdditi.prod_linequiv_symmmul]
  rfl

/-- Inserting in the second factor is the inverse linear product equivalence on `(0, y)`. -/
@[simp] theorem mFAdditi.prod_linequiv_symminr [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    (mFAdditi.prodLinearEquiv (p := p) G H).symm (0, y) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) y := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  change (mFAdditi.prodLinearEquiv (p := p) G H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) (1 : G)),
       Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) h)) = _
  rw [mFAdditi.prod_linequiv_symmmul]
  rfl


/-- Inverse linear product splitting with a trivial right factor ignores that coordinate. -/
@[simp] theorem mFAdditi.prodlin_equivsymm_righttrivial [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) (y : mFAdditi p E) :
    (mFAdditi.prodLinearEquiv (p := p) G E).symm (x, y) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl G E) x := by
  have hy : y = 0 := Subsingleton.elim y 0
  subst y
  simp

/-- Inverse linear product splitting with a trivial left factor ignores that coordinate. -/
@[simp] theorem mFAdditi.prodlin_equivsymm_lefttrivial [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p E) (y : mFAdditi p G) :
    (mFAdditi.prodLinearEquiv (p := p) E G).symm (x, y) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr E G) y := by
  have hx : x = 0 := Subsingleton.elim x 0
  subst x
  simp

/-- Characterize equality to the additive product equivalence via its inverse. -/
theorem mFAdditi.prodadd_equiveq_iffeqsymm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H))
    (y : mFAdditi p G × mFAdditi p H) :
    mFAdditi.prodAddEquiv (p := p) G H x = y ↔
      x = (mFAdditi.prodAddEquiv (p := p) G H).symm y := by
  constructor
  · intro h
    rw [← h]
    exact ((mFAdditi.prodAddEquiv (p := p) G H).left_inv x).symm
  · intro h
    rw [h]
    exact (mFAdditi.prodAddEquiv (p := p) G H).right_inv y

/-- Characterize equality to the inverse additive product equivalence. -/
theorem mFAdditi.eqprod_addequiv_symmiff
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H))
    (y : mFAdditi p G × mFAdditi p H) :
    x = (mFAdditi.prodAddEquiv (p := p) G H).symm y ↔
      mFAdditi.prodAddEquiv (p := p) G H x = y := by
  exact (mFAdditi.prodadd_equiveq_iffeqsymm (p := p) G H x y).symm

/-- Characterize equality to the linear product equivalence via its inverse. -/
theorem mFAdditi.prodlin_equiveq_iffeqsymm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H))
    (y : mFAdditi p G × mFAdditi p H) :
    mFAdditi.prodLinearEquiv (p := p) G H x = y ↔
      x = (mFAdditi.prodLinearEquiv (p := p) G H).symm y := by
  constructor
  · intro h
    rw [← h]
    exact ((mFAdditi.prodLinearEquiv (p := p) G H).left_inv x).symm
  · intro h
    rw [h]
    exact (mFAdditi.prodLinearEquiv (p := p) G H).right_inv y

/-- Characterize equality to the inverse linear product equivalence. -/
theorem mFAdditi.eqprod_linequiv_symmiff [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H))
    (y : mFAdditi p G × mFAdditi p H) :
    x = (mFAdditi.prodLinearEquiv (p := p) G H).symm y ↔
      mFAdditi.prodLinearEquiv (p := p) G H x = y := by
  exact (mFAdditi.prodlin_equiveq_iffeqsymm (p := p) G H x y).symm



@[simp] theorem mFAdditi.prodadd_equivsymm_applyapply
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodAddEquiv (p := p) G H).symm
        (mFAdditi.prodAddEquiv (p := p) G H x) = x := by
  exact (mFAdditi.prodAddEquiv (p := p) G H).left_inv x

@[simp] theorem mFAdditi.prodadd_equivapply_symmapply
    (G H : Type*) [Group G] [Group H]
    (y : mFAdditi p G × mFAdditi p H) :
    mFAdditi.prodAddEquiv (p := p) G H
        ((mFAdditi.prodAddEquiv (p := p) G H).symm y) = y := by
  exact (mFAdditi.prodAddEquiv (p := p) G H).right_inv y

@[simp] theorem mFAdditi.prodlin_equivsymm_applyapply [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodLinearEquiv (p := p) G H).symm
        (mFAdditi.prodLinearEquiv (p := p) G H x) = x := by
  exact (mFAdditi.prodLinearEquiv (p := p) G H).left_inv x

@[simp] theorem mFAdditi.prodlin_equivapply_symmapply [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (y : mFAdditi p G × mFAdditi p H) :
    mFAdditi.prodLinearEquiv (p := p) G H
        ((mFAdditi.prodLinearEquiv (p := p) G H).symm y) = y := by
  exact (mFAdditi.prodLinearEquiv (p := p) G H).right_inv y


/-- The additive Frattini map induced by insertion into the first factor is injective. -/
theorem mFAdditi.map_add_inlinj
    (G H : Type*) [Group G] [Group H] :
    Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H)) := by
  intro x y h
  rw [← mFAdditi.prod_addequiv_symminl (p := p) G H x,
      ← mFAdditi.prod_addequiv_symminl (p := p) G H y] at h
  have hpair := congrArg (fun z => mFAdditi.prodAddEquiv (p := p) G H z) h
  have hp : (x, (0 : mFAdditi p H)) = (y, 0) := by
    simpa only [AddEquiv.apply_symm_apply] using hpair
  exact congrArg Prod.fst hp

/-- The additive Frattini map induced by insertion into the second factor is injective. -/
theorem mFAdditi.map_add_inrinj
    (G H : Type*) [Group G] [Group H] :
    Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H)) := by
  intro x y h
  rw [← mFAdditi.prod_addequiv_symminr (p := p) G H x,
      ← mFAdditi.prod_addequiv_symminr (p := p) G H y] at h
  have hpair := congrArg (fun z => mFAdditi.prodAddEquiv (p := p) G H z) h
  have hp : ((0 : mFAdditi p G), x) = (0, y) := by
    simpa only [AddEquiv.apply_symm_apply] using hpair
  exact congrArg Prod.snd hp

/-- The first projection additive Frattini map is surjective. -/
theorem mFAdditi.map_add_fstsurj
    (G H : Type*) [Group G] [Group H] :
    Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)) := by
  intro x
  refine ⟨(mFAdditi.prodAddEquiv (p := p) G H).symm
      (x, (0 : mFAdditi p H)), ?_⟩
  have h := congrArg Prod.fst (AddEquiv.apply_symm_apply
    (mFAdditi.prodAddEquiv (p := p) G H)
    (x, (0 : mFAdditi p H)))
  simpa [mFAdditi.prod_add_equivfst] using h

/-- The second projection additive Frattini map is surjective. -/
theorem mFAdditi.map_add_sndsurj
    (G H : Type*) [Group G] [Group H] :
    Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)) := by
  intro y
  refine ⟨(mFAdditi.prodAddEquiv (p := p) G H).symm
      ((0 : mFAdditi p G), y), ?_⟩
  have h := congrArg Prod.snd (AddEquiv.apply_symm_apply
    (mFAdditi.prodAddEquiv (p := p) G H)
    ((0 : mFAdditi p G), y))
  simpa [mFAdditi.prod_add_equivsnd] using h


@[simp] theorem mFAdditi.map_add_fstinl
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem mFAdditi.map_add_sndinl
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x) = 0 := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem mFAdditi.map_add_fstinr
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) y) = 0 := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl

@[simp] theorem mFAdditi.map_add_sndinr
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) y) = y := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl

@[simp] theorem mFAdditi.map_lin_fstinl [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem mFAdditi.map_lin_sndinl [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (x : mFAdditi p G) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x) = 0 := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem mFAdditi.map_lin_fstinr [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) y) = 0 := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl

@[simp] theorem mFAdditi.map_lin_sndinr [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] (y : mFAdditi p H) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) y) = y := by
  cases y using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro h
  rfl
/-- Extensionality for additive product Frattini classes via the two projections. -/
theorem mFAdditi.prod_ext (G H : Type*) [Group G] [Group H]
    {x y : mFAdditi p (G × H)}
    (hfst : mFAdditi.mapAdd (p := p) (MonoidHom.fst G H) x =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G H) y)
    (hsnd : mFAdditi.mapAdd (p := p) (MonoidHom.snd G H) x =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd G H) y) : x = y := by
  apply (mFAdditi.prodAddEquiv (p := p) G H).injective
  ext
  · simpa [mFAdditi.prod_add_equivfst] using hfst
  · simpa [mFAdditi.prod_add_equivsnd] using hsnd

/-- Extensionality for linear product Frattini classes via the two projections. -/
theorem mFAdditi.prod_linear_ext [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    {x y : mFAdditi p (G × H)}
    (hfst : mFAdditi.mapLinear (p := p) (MonoidHom.fst G H) x =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G H) y)
    (hsnd : mFAdditi.mapLinear (p := p) (MonoidHom.snd G H) x =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd G H) y) : x = y := by
  apply (mFAdditi.prodLinearEquiv (p := p) G H).injective
  ext
  · simpa [mFAdditi.prod_lin_equivfst] using hfst
  · simpa [mFAdditi.prod_lin_equivsnd] using hsnd

/-- Extensionality for right-associated triple additive Frattini classes via three projections. -/
theorem mFAdditi.prod_triple_ext (G H K : Type*) [Group G] [Group H] [Group K]
    {x y : mFAdditi p (G × H × K)}
    (h₁ : mFAdditi.mapAdd (p := p) (MonoidHom.fst G (H × K)) x =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G (H × K)) y)
    (h₂ : mFAdditi.mapAdd (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) y))
    (h₃ : mFAdditi.mapAdd (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) y)) : x = y := by
  apply mFAdditi.prod_ext (p := p) G (H × K) h₁
  exact mFAdditi.prod_ext (p := p) H K h₂ h₃

/-- Extensionality for right-associated triple linear Frattini classes via three projections. -/
theorem mFAdditi.prod_triple_linext [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    {x y : mFAdditi p (G × H × K)}
    (h₁ : mFAdditi.mapLinear (p := p) (MonoidHom.fst G (H × K)) x =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G (H × K)) y)
    (h₂ : mFAdditi.mapLinear (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) y))
    (h₃ : mFAdditi.mapLinear (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) y)) : x = y := by
  apply mFAdditi.prod_linear_ext (p := p) G (H × K) h₁
  exact mFAdditi.prod_linear_ext (p := p) H K h₂ h₃


/-- Extensionality for left-associated triple additive Frattini classes via three projections. -/
theorem mFAdditi.prod_triple_leftext
    (G H K : Type*) [Group G] [Group H] [Group K]
    {x y : mFAdditi p ((G × H) × K)}
    (h₁ : mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) y))
    (h₂ : mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) y))
    (h₃ : mFAdditi.mapAdd (p := p) (MonoidHom.snd (G × H) K) x =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd (G × H) K) y) : x = y := by
  apply mFAdditi.prod_ext (p := p) (G × H) K
  · exact mFAdditi.prod_ext (p := p) G H h₁ h₂
  · exact h₃

/-- Extensionality for left-associated triple linear Frattini classes via three projections. -/
theorem mFAdditi.prod_tripleleft_linext [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    {x y : mFAdditi p ((G × H) × K)}
    (h₁ : mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) y))
    (h₂ : mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) y))
    (h₃ : mFAdditi.mapLinear (p := p) (MonoidHom.snd (G × H) K) x =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd (G × H) K) y) : x = y := by
  apply mFAdditi.prod_linear_ext (p := p) (G × H) K
  · exact mFAdditi.prod_linear_ext (p := p) G H h₁ h₂
  · exact h₃


/-- The inverse additive product equivalence is the sum of the two insertion maps. -/
theorem mFAdditi.prodadd_equivsymmeq_addinlinr
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G) (y : mFAdditi p H) :
    (mFAdditi.prodAddEquiv (p := p) G H).symm (x, y) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x +
        mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) y := by
  apply (mFAdditi.prodAddEquiv (p := p) G H).injective
  ext <;> simp

/-- The inverse linear product equivalence is the sum of the two insertion maps. -/
theorem mFAdditi.prodlin_equivsymmeq_addinlinr [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G) (y : mFAdditi p H) :
    (mFAdditi.prodLinearEquiv (p := p) G H).symm (x, y) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x +
        mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) y := by
  apply (mFAdditi.prodLinearEquiv (p := p) G H).injective
  ext <;> simp

/-- Reconstruct an additive product quotient class from its two projected components. -/
theorem mFAdditi.mapadd_inlfst_addinrsnd
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.inl G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst G H) x) +
      mFAdditi.mapAdd (p := p) (MonoidHom.inr G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G H) x) = x := by
  apply (mFAdditi.prodAddEquiv (p := p) G H).injective
  ext <;> simp

/-- Reconstruct a linear product quotient class from its two projected components. -/
theorem mFAdditi.maplin_inlfst_addinrsnd [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.inl G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst G H) x) +
      mFAdditi.mapLinear (p := p) (MonoidHom.inr G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G H) x) = x := by
  apply (mFAdditi.prodLinearEquiv (p := p) G H).injective
  ext <;> simp

@[simp] theorem mFAdditi.map_add_inlker
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H)).ker = ⊥ := by
  exact (AddMonoidHom.ker_eq_bot_iff _).2
    (mFAdditi.map_add_inlinj (p := p) G H)

@[simp] theorem mFAdditi.map_add_inrker
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H)).ker = ⊥ := by
  exact (AddMonoidHom.ker_eq_bot_iff _).2
    (mFAdditi.map_add_inrinj (p := p) G H)

@[simp] theorem mFAdditi.map_add_fstrange
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)).range = ⊤ := by
  exact (AddMonoidHom.range_eq_top).2
    (mFAdditi.map_add_fstsurj (p := p) G H)

@[simp] theorem mFAdditi.map_add_sndrange
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)).range = ⊤ := by
  exact (AddMonoidHom.range_eq_top).2
    (mFAdditi.map_add_sndsurj (p := p) G H)

/-- The Frattini map induced by insertion into the first factor is injective. -/
theorem mFAdditi.map_lin_inlinj [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H)) := by
  intro x y h
  rw [← mFAdditi.prod_linequiv_symminl (p := p) G H x,
      ← mFAdditi.prod_linequiv_symminl (p := p) G H y] at h
  have hpair := congrArg (fun z => mFAdditi.prodLinearEquiv (p := p) G H z) h
  have hp : (x, (0 : mFAdditi p H)) = (y, 0) := by
    simpa only [LinearEquiv.apply_symm_apply] using hpair
  exact congrArg Prod.fst hp

/-- The Frattini map induced by insertion into the second factor is injective. -/
theorem mFAdditi.map_lin_inrinj [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H)) := by
  intro x y h
  rw [← mFAdditi.prod_linequiv_symminr (p := p) G H x,
      ← mFAdditi.prod_linequiv_symminr (p := p) G H y] at h
  have hpair := congrArg (fun z => mFAdditi.prodLinearEquiv (p := p) G H z) h
  have hp : ((0 : mFAdditi p G), x) = (0, y) := by
    simpa only [LinearEquiv.apply_symm_apply] using hpair
  exact congrArg Prod.snd hp

/-- The first projection Frattini map is surjective. -/
theorem mFAdditi.map_lin_fstsurj [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)) := by
  intro x
  refine ⟨mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x, ?_⟩
  simp

/-- The second projection Frattini map is surjective. -/
theorem mFAdditi.map_lin_sndsurj [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)) := by
  intro y
  refine ⟨mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) y, ?_⟩
  simp

@[simp] theorem mFAdditi.map_lin_inlker [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    LinearMap.ker (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H)) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (mFAdditi.map_lin_inlinj (p := p) G H)

@[simp] theorem mFAdditi.map_lin_inrker [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    LinearMap.ker (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H)) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (mFAdditi.map_lin_inrinj (p := p) G H)

@[simp] theorem mFAdditi.map_lin_fstrange [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    LinearMap.range (mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (mFAdditi.map_lin_fstsurj (p := p) G H)

@[simp] theorem mFAdditi.map_lin_sndrange [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    LinearMap.range (mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (mFAdditi.map_lin_sndsurj (p := p) G H)

/-- Naturality of the additive Frattini product equivalence. -/
theorem mFAdditi.prod_add_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    (mFAdditi.prodAddEquiv (p := p) G₂ H₂).toAddMonoidHom.comp
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) =
      (AddMonoidHom.prodMap (mFAdditi.mapAdd (p := p) f)
        (mFAdditi.mapAdd (p := p) g)).comp
        (mFAdditi.prodAddEquiv (p := p) G₁ H₁).toAddMonoidHom := by
  ext x <;> cases x using Additive.rec <;> rfl

/-- Naturality of the linear Frattini product equivalence. -/
theorem mFAdditi.prod_lin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).toLinearMap.comp
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) =
      (LinearMap.prodMap (mFAdditi.mapLinear (p := p) f)
        (mFAdditi.mapLinear (p := p) g)).comp
        (mFAdditi.prodLinearEquiv (p := p) G₁ H₁).toLinearMap := by
  ext x <;> cases x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro a
      rcases a with ⟨a, b⟩
      rfl

/-- Pointwise form of naturality of the additive Frattini product equivalence. -/
theorem mFAdditi.prodadd_equivmap_prodmap
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.prodAddEquiv (p := p) G₂ H₂
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) =
      (mFAdditi.mapAdd (p := p) f
          (mFAdditi.prodAddEquiv (p := p) G₁ H₁ x).1,
        mFAdditi.mapAdd (p := p) g
          (mFAdditi.prodAddEquiv (p := p) G₁ H₁ x).2) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Pointwise form of naturality of the linear Frattini product equivalence. -/
theorem mFAdditi.prodlin_equivmap_prodmap [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.prodLinearEquiv (p := p) G₂ H₂
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) =
      (mFAdditi.mapLinear (p := p) f
          (mFAdditi.prodLinearEquiv (p := p) G₁ H₁ x).1,
        mFAdditi.mapLinear (p := p) g
          (mFAdditi.prodLinearEquiv (p := p) G₁ H₁ x).2) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- The additive product equivalence is compatible with swapping factors. -/
theorem mFAdditi.prodadd_equivmap_prodcomm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodAddEquiv (p := p) H G
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      ((mFAdditi.prodAddEquiv (p := p) G H x).2,
        (mFAdditi.prodAddEquiv (p := p) G H x).1) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- The linear product equivalence is compatible with swapping factors. -/
theorem mFAdditi.prodlin_equivmap_prodcomm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodLinearEquiv (p := p) H G
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      ((mFAdditi.prodLinearEquiv (p := p) G H x).2,
        (mFAdditi.prodLinearEquiv (p := p) G H x).1) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Injectivity of an additive product-induced Frattini map follows factorwise. -/
theorem mFAdditi.mapadd_prodmap_injinj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Injective (mFAdditi.mapAdd (p := p) f))
    (hg : Function.Injective (mFAdditi.mapAdd (p := p) g)) :
    Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) := by
  intro x y hxy
  apply (mFAdditi.prodAddEquiv (p := p) G₁ H₁).injective
  have hp := congrArg (fun z => mFAdditi.prodAddEquiv (p := p) G₂ H₂ z) hxy
  change mFAdditi.prodAddEquiv (p := p) G₂ H₂
      (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) =
    mFAdditi.prodAddEquiv (p := p) G₂ H₂
      (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) y) at hp
  rw [mFAdditi.prodadd_equivmap_prodmap,
      mFAdditi.prodadd_equivmap_prodmap] at hp
  exact Prod.ext (hf (congrArg Prod.fst hp)) (hg (congrArg Prod.snd hp))

/-- Surjectivity of an additive product-induced Frattini map follows factorwise. -/
theorem mFAdditi.mapadd_prodmap_surjsurj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Surjective (mFAdditi.mapAdd (p := p) f))
    (hg : Function.Surjective (mFAdditi.mapAdd (p := p) g)) :
    Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) := by
  intro y
  let yp := mFAdditi.prodAddEquiv (p := p) G₂ H₂ y
  rcases hf yp.1 with ⟨a, ha⟩
  rcases hg yp.2 with ⟨b, hb⟩
  refine ⟨(mFAdditi.prodAddEquiv (p := p) G₁ H₁).symm (a, b), ?_⟩
  apply (mFAdditi.prodAddEquiv (p := p) G₂ H₂).injective
  rw [mFAdditi.prodadd_equivmap_prodmap]
  simpa [yp, ha, hb] using (show
    (mFAdditi.mapAdd (p := p) f a,
      mFAdditi.mapAdd (p := p) g b) = yp by
        rw [ha, hb])

/-- Bijectivity of an additive product-induced Frattini map follows factorwise. -/
theorem mFAdditi.mapadd_prodmap_bijbij
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Bijective (mFAdditi.mapAdd (p := p) f))
    (hg : Function.Bijective (mFAdditi.mapAdd (p := p) g)) :
    Function.Bijective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) :=
  ⟨mFAdditi.mapadd_prodmap_injinj (p := p) f g hf.1 hg.1,
    mFAdditi.mapadd_prodmap_surjsurj (p := p) f g hf.2 hg.2⟩

/-- Injectivity of a linear product-induced Frattini map follows factorwise. -/
theorem mFAdditi.maplin_prodmap_injinj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Injective (mFAdditi.mapLinear (p := p) f))
    (hg : Function.Injective (mFAdditi.mapLinear (p := p) g)) :
    Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) := by
  intro x y hxy
  apply (mFAdditi.prodLinearEquiv (p := p) G₁ H₁).injective
  have hp := congrArg (fun z => mFAdditi.prodLinearEquiv (p := p) G₂ H₂ z) hxy
  change mFAdditi.prodLinearEquiv (p := p) G₂ H₂
      (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) =
    mFAdditi.prodLinearEquiv (p := p) G₂ H₂
      (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) y) at hp
  rw [mFAdditi.prodlin_equivmap_prodmap,
      mFAdditi.prodlin_equivmap_prodmap] at hp
  exact Prod.ext (hf (congrArg Prod.fst hp)) (hg (congrArg Prod.snd hp))

/-- Surjectivity of a linear product-induced Frattini map follows factorwise. -/
theorem mFAdditi.maplin_prodmap_surjsurj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Surjective (mFAdditi.mapLinear (p := p) f))
    (hg : Function.Surjective (mFAdditi.mapLinear (p := p) g)) :
    Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) := by
  intro y
  let yp := mFAdditi.prodLinearEquiv (p := p) G₂ H₂ y
  rcases hf yp.1 with ⟨a, ha⟩
  rcases hg yp.2 with ⟨b, hb⟩
  refine ⟨(mFAdditi.prodLinearEquiv (p := p) G₁ H₁).symm (a, b), ?_⟩
  apply (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).injective
  rw [mFAdditi.prodlin_equivmap_prodmap]
  simpa [yp, ha, hb] using (show
    (mFAdditi.mapLinear (p := p) f a,
      mFAdditi.mapLinear (p := p) g b) = yp by
        rw [ha, hb])

/-- Bijectivity of a linear product-induced Frattini map follows factorwise. -/
theorem mFAdditi.maplin_prodmap_bijbij [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (hf : Function.Bijective (mFAdditi.mapLinear (p := p) f))
    (hg : Function.Bijective (mFAdditi.mapLinear (p := p) g)) :
    Function.Bijective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) :=
  ⟨mFAdditi.maplin_prodmap_injinj (p := p) f g hf.1 hg.1,
    mFAdditi.maplin_prodmap_surjsurj (p := p) f g hf.2 hg.2⟩

/-- Injectivity of an additive product-induced map implies injectivity on the first factor. -/
theorem mFAdditi.mapadd_injleft_prodmapinj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g))) :
    Function.Injective (mFAdditi.mapAdd (p := p) f) := by
  intro x y hxy
  apply mFAdditi.map_add_inlinj (p := p) G₁ H₁
  apply h
  rw [mFAdditi.map_addprod_mapinl,
      mFAdditi.map_addprod_mapinl, hxy]

/-- Injectivity of an additive product-induced map implies injectivity on the second factor. -/
theorem mFAdditi.mapadd_injright_prodmapinj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g))) :
    Function.Injective (mFAdditi.mapAdd (p := p) g) := by
  intro x y hxy
  apply mFAdditi.map_add_inrinj (p := p) G₁ H₁
  apply h
  rw [mFAdditi.map_addprod_mapinr,
      mFAdditi.map_addprod_mapinr, hxy]

/-- Surjectivity of an additive product-induced map implies surjectivity on the first factor. -/
theorem mFAdditi.mapadd_surjleft_prodmapsurj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g))) :
    Function.Surjective (mFAdditi.mapAdd (p := p) f) := by
  intro z
  let target := (mFAdditi.prodAddEquiv (p := p) G₂ H₂).symm
    (z, (0 : mFAdditi p H₂))
  rcases h target with ⟨x, hx⟩
  refine ⟨mFAdditi.mapAdd (p := p) (MonoidHom.fst G₁ H₁) x, ?_⟩
  calc
    mFAdditi.mapAdd (p := p) f
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst G₁ H₁) x) =
        mFAdditi.mapAdd (p := p) (MonoidHom.fst G₂ H₂)
          (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) :=
      mFAdditi.map_addfst_prodmap (p := p) f g x
    _ = mFAdditi.mapAdd (p := p) (MonoidHom.fst G₂ H₂) target := by rw [hx]
    _ = z := by simp [target]

/-- Surjectivity of an additive product-induced map implies surjectivity on the second factor. -/
theorem mFAdditi.mapadd_surjright_prodmapsurj
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g))) :
    Function.Surjective (mFAdditi.mapAdd (p := p) g) := by
  intro z
  let target := (mFAdditi.prodAddEquiv (p := p) G₂ H₂).symm
    ((0 : mFAdditi p G₂), z)
  rcases h target with ⟨x, hx⟩
  refine ⟨mFAdditi.mapAdd (p := p) (MonoidHom.snd G₁ H₁) x, ?_⟩
  calc
    mFAdditi.mapAdd (p := p) g
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G₁ H₁) x) =
        mFAdditi.mapAdd (p := p) (MonoidHom.snd G₂ H₂)
          (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) :=
      mFAdditi.map_addsnd_prodmap (p := p) f g x
    _ = mFAdditi.mapAdd (p := p) (MonoidHom.snd G₂ H₂) target := by rw [hx]
    _ = z := by simp [target]

/-- Factorwise criterion for injectivity of an additive product-induced map. -/
theorem mFAdditi.mapadd_prodmap_injiff
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Injective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Injective (mFAdditi.mapAdd (p := p) f) ∧
        Function.Injective (mFAdditi.mapAdd (p := p) g) := by
  constructor
  · intro h
    exact ⟨mFAdditi.mapadd_injleft_prodmapinj (p := p) f g h,
      mFAdditi.mapadd_injright_prodmapinj (p := p) f g h⟩
  · intro h
    exact mFAdditi.mapadd_prodmap_injinj (p := p) f g h.1 h.2

/-- Factorwise criterion for surjectivity of an additive product-induced map. -/
theorem mFAdditi.mapadd_prodmap_surjiff
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Surjective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Surjective (mFAdditi.mapAdd (p := p) f) ∧
        Function.Surjective (mFAdditi.mapAdd (p := p) g) := by
  constructor
  · intro h
    exact ⟨mFAdditi.mapadd_surjleft_prodmapsurj (p := p) f g h,
      mFAdditi.mapadd_surjright_prodmapsurj (p := p) f g h⟩
  · intro h
    exact mFAdditi.mapadd_prodmap_surjsurj (p := p) f g h.1 h.2

/-- Factorwise criterion for bijectivity of an additive product-induced map. -/
theorem mFAdditi.mapadd_prodmap_bijiff
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Bijective (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Bijective (mFAdditi.mapAdd (p := p) f) ∧
        Function.Bijective (mFAdditi.mapAdd (p := p) g) := by
  constructor
  · intro h
    have hi := (mFAdditi.mapadd_prodmap_injiff (p := p) f g).mp h.1
    have hs := (mFAdditi.mapadd_prodmap_surjiff (p := p) f g).mp h.2
    exact ⟨⟨hi.1, hs.1⟩, ⟨hi.2, hs.2⟩⟩
  · intro h
    exact mFAdditi.mapadd_prodmap_bijbij (p := p) f g h.1 h.2

/-- Injectivity of a linear product-induced map implies injectivity on the first factor. -/
theorem mFAdditi.maplin_injleft_prodmapinj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g))) :
    Function.Injective (mFAdditi.mapLinear (p := p) f) := by
  intro x y hxy
  apply mFAdditi.map_lin_inlinj (p := p) G₁ H₁
  apply h
  rw [mFAdditi.map_linprod_mapinl,
      mFAdditi.map_linprod_mapinl, hxy]

/-- Injectivity of a linear product-induced map implies injectivity on the second factor. -/
theorem mFAdditi.maplin_injright_prodmapinj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g))) :
    Function.Injective (mFAdditi.mapLinear (p := p) g) := by
  intro x y hxy
  apply mFAdditi.map_lin_inrinj (p := p) G₁ H₁
  apply h
  rw [mFAdditi.map_linprod_mapinr,
      mFAdditi.map_linprod_mapinr, hxy]

/-- Surjectivity of a linear product-induced map implies surjectivity on the first factor. -/
theorem mFAdditi.maplin_surjleft_prodmapsurj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g))) :
    Function.Surjective (mFAdditi.mapLinear (p := p) f) := by
  intro z
  let target := (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).symm
    (z, (0 : mFAdditi p H₂))
  rcases h target with ⟨x, hx⟩
  refine ⟨mFAdditi.mapLinear (p := p) (MonoidHom.fst G₁ H₁) x, ?_⟩
  calc
    mFAdditi.mapLinear (p := p) f
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst G₁ H₁) x) =
        mFAdditi.mapLinear (p := p) (MonoidHom.fst G₂ H₂)
          (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) :=
      mFAdditi.map_linfst_prodmap (p := p) f g x
    _ = mFAdditi.mapLinear (p := p) (MonoidHom.fst G₂ H₂) target := by rw [hx]
    _ = z := by simp [target]

/-- Surjectivity of a linear product-induced map implies surjectivity on the second factor. -/
theorem mFAdditi.maplin_surjright_prodmapsurj [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (h : Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g))) :
    Function.Surjective (mFAdditi.mapLinear (p := p) g) := by
  intro z
  let target := (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).symm
    ((0 : mFAdditi p G₂), z)
  rcases h target with ⟨x, hx⟩
  refine ⟨mFAdditi.mapLinear (p := p) (MonoidHom.snd G₁ H₁) x, ?_⟩
  calc
    mFAdditi.mapLinear (p := p) g
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G₁ H₁) x) =
        mFAdditi.mapLinear (p := p) (MonoidHom.snd G₂ H₂)
          (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) :=
      mFAdditi.map_linsnd_prodmap (p := p) f g x
    _ = mFAdditi.mapLinear (p := p) (MonoidHom.snd G₂ H₂) target := by rw [hx]
    _ = z := by simp [target]

/-- Factorwise criterion for injectivity of a linear product-induced map. -/
theorem mFAdditi.maplin_prodmap_injiff [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Injective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Injective (mFAdditi.mapLinear (p := p) f) ∧
        Function.Injective (mFAdditi.mapLinear (p := p) g) := by
  constructor
  · intro h
    exact ⟨mFAdditi.maplin_injleft_prodmapinj (p := p) f g h,
      mFAdditi.maplin_injright_prodmapinj (p := p) f g h⟩
  · intro h
    exact mFAdditi.maplin_prodmap_injinj (p := p) f g h.1 h.2

/-- Factorwise criterion for surjectivity of a linear product-induced map. -/
theorem mFAdditi.maplin_prodmap_surjiff [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Surjective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Surjective (mFAdditi.mapLinear (p := p) f) ∧
        Function.Surjective (mFAdditi.mapLinear (p := p) g) := by
  constructor
  · intro h
    exact ⟨mFAdditi.maplin_surjleft_prodmapsurj (p := p) f g h,
      mFAdditi.maplin_surjright_prodmapsurj (p := p) f g h⟩
  · intro h
    exact mFAdditi.maplin_prodmap_surjsurj (p := p) f g h.1 h.2

/-- Factorwise criterion for bijectivity of a linear product-induced map. -/
theorem mFAdditi.maplin_prodmap_bijiff [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    Function.Bijective (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) ↔
      Function.Bijective (mFAdditi.mapLinear (p := p) f) ∧
        Function.Bijective (mFAdditi.mapLinear (p := p) g) := by
  constructor
  · intro h
    have hi := (mFAdditi.maplin_prodmap_injiff (p := p) f g).mp h.1
    have hs := (mFAdditi.maplin_prodmap_surjiff (p := p) f g).mp h.2
    exact ⟨⟨hi.1, hs.1⟩, ⟨hi.2, hs.2⟩⟩
  · intro h
    exact mFAdditi.maplin_prodmap_bijbij (p := p) f g h.1 h.2

/-- Kernel-triviality of an additive product-induced map is factorwise. -/
theorem mFAdditi.mapadd_prodmapker_eqbotiff
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)).ker = ⊥ ↔
      (mFAdditi.mapAdd (p := p) f).ker = ⊥ ∧
        (mFAdditi.mapAdd (p := p) g).ker = ⊥ := by
  rw [AddMonoidHom.ker_eq_bot_iff, AddMonoidHom.ker_eq_bot_iff,
    AddMonoidHom.ker_eq_bot_iff]
  exact mFAdditi.mapadd_prodmap_injiff (p := p) f g

/-- Full-range property of an additive product-induced map is factorwise. -/
theorem mFAdditi.mapadd_prodmaprange_eqtopiff
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)).range = ⊤ ↔
      (mFAdditi.mapAdd (p := p) f).range = ⊤ ∧
        (mFAdditi.mapAdd (p := p) g).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top, AddMonoidHom.range_eq_top, AddMonoidHom.range_eq_top]
  exact mFAdditi.mapadd_prodmap_surjiff (p := p) f g

/-- Kernel-triviality of a linear product-induced map is factorwise. -/
theorem mFAdditi.maplin_prodmapker_eqbotiff [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    LinearMap.ker (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) = ⊥ ↔
      LinearMap.ker (mFAdditi.mapLinear (p := p) f) = ⊥ ∧
        LinearMap.ker (mFAdditi.mapLinear (p := p) g) = ⊥ := by
  rw [LinearMap.ker_eq_bot, LinearMap.ker_eq_bot, LinearMap.ker_eq_bot]
  exact mFAdditi.maplin_prodmap_injiff (p := p) f g

/-- Full-range property of a linear product-induced map is factorwise. -/
theorem mFAdditi.maplin_prodmaprange_eqtopiff [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) :
    LinearMap.range (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)) = ⊤ ↔
      LinearMap.range (mFAdditi.mapLinear (p := p) f) = ⊤ ∧
        LinearMap.range (mFAdditi.mapLinear (p := p) g) = ⊤ := by
  rw [LinearMap.range_eq_top, LinearMap.range_eq_top, LinearMap.range_eq_top]
  exact mFAdditi.maplin_prodmap_surjiff (p := p) f g

/-- Naturality of the inverse additive Frattini product equivalence. -/
theorem mFAdditi.prod_addequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p G₁ × mFAdditi p H₁) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)
        ((mFAdditi.prodAddEquiv (p := p) G₁ H₁).symm x) =
      (mFAdditi.prodAddEquiv (p := p) G₂ H₂).symm
        (mFAdditi.mapAdd (p := p) f x.1,
          mFAdditi.mapAdd (p := p) g x.2) := by
  rcases x with ⟨x, y⟩
  cases x using Additive.rec
  cases y using Additive.rec
  rename_i q r
  refine QuotientGroup.induction_on q ?_
  intro a
  refine QuotientGroup.induction_on r ?_
  intro b
  change mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g)
      ((mFAdditi.prodAddEquiv (p := p) G₁ H₁).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G₁) a),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H₁) b))) =
    (mFAdditi.prodAddEquiv (p := p) G₂ H₂).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G₂) (f a)),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p H₂) (g b)))
  rw [mFAdditi.prod_addequiv_symmmul]
  rw [mFAdditi.prod_addequiv_symmmul]
  rfl

/-- Naturality of the inverse linear Frattini product equivalence. -/
theorem mFAdditi.prod_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p G₁ × mFAdditi p H₁) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)
        ((mFAdditi.prodLinearEquiv (p := p) G₁ H₁).symm x) =
      (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).symm
        (mFAdditi.mapLinear (p := p) f x.1,
          mFAdditi.mapLinear (p := p) g x.2) := by
  rcases x with ⟨x, y⟩
  cases x using Additive.rec
  cases y using Additive.rec
  rename_i q r
  refine QuotientGroup.induction_on q ?_
  intro a
  refine QuotientGroup.induction_on r ?_
  intro b
  change mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g)
      ((mFAdditi.prodLinearEquiv (p := p) G₁ H₁).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G₁) a),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H₁) b))) =
    (mFAdditi.prodLinearEquiv (p := p) G₂ H₂).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G₂) (f a)),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p H₂) (g b)))
  rw [mFAdditi.prod_linequiv_symmmul]
  rw [mFAdditi.prod_linequiv_symmmul]
  rfl



/-- The additive Frattini map induced by swapping product factors is involutive. -/
@[simp] theorem mFAdditi.mapadd_prodcommmap_addprodcomm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- The linear Frattini map induced by swapping product factors is involutive. -/
@[simp] theorem mFAdditi.maplin_prodcommmap_linprodcomm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl



/-- Additive right-unit equivalence for a subsingleton product factor. -/
noncomputable def mFAdditi.prod_righttrivial_addequiv
    (G E : Type*) [Group G] [Group E] [Subsingleton E] :
    mFAdditi p (G × E) ≃+ mFAdditi p G :=
{ toFun := mFAdditi.mapAdd (p := p) (MonoidHom.fst G E)
  invFun := mFAdditi.mapAdd (p := p) (MonoidHom.inl G E)
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, e⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prodright_trivialadd_equivapply
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    mFAdditi.prod_righttrivial_addequiv (p := p) G E x =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G E) x := rfl

@[simp] theorem mFAdditi.prodright_trivialadd_equivsymmapply
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) :
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).symm x =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl G E) x := rfl

@[simp] theorem mFAdditi.prodright_trivialadd_equivmk
    (G E : Type*) [Group G] [Group E] [Subsingleton E] (g : G) (e : E) :
    mFAdditi.prod_righttrivial_addequiv (p := p) G E
      (Additive.ofMul (mFQuot.mk p (G × E) (g, e))) =
    Additive.ofMul (mFQuot.mk p G g) := rfl

@[simp] theorem mFAdditi.prodright_trivialadd_equivsymmmk
    (G E : Type*) [Group G] [Group E] [Subsingleton E] (g : G) :
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).symm
      (Additive.ofMul (mFQuot.mk p G g)) =
    Additive.ofMul (mFQuot.mk p (G × E) (g, 1)) := rfl

/-- Additive left-unit equivalence for a subsingleton product factor. -/
noncomputable def mFAdditi.prod_lefttrivial_addequiv
    (E G : Type*) [Group E] [Group G] [Subsingleton E] :
    mFAdditi p (E × G) ≃+ mFAdditi p G :=
{ toFun := mFAdditi.mapAdd (p := p) (MonoidHom.snd E G)
  invFun := mFAdditi.mapAdd (p := p) (MonoidHom.inr E G)
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨e, g⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prodleft_trivialadd_equivapply
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    mFAdditi.prod_lefttrivial_addequiv (p := p) E G x =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd E G) x := rfl

@[simp] theorem mFAdditi.prodleft_trivialadd_equivsymmapply
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p G) :
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).symm x =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr E G) x := rfl

@[simp] theorem mFAdditi.prodleft_trivialadd_equivmk
    (E G : Type*) [Group E] [Group G] [Subsingleton E] (e : E) (g : G) :
    mFAdditi.prod_lefttrivial_addequiv (p := p) E G
      (Additive.ofMul (mFQuot.mk p (E × G) (e, g))) =
    Additive.ofMul (mFQuot.mk p G g) := rfl

@[simp] theorem mFAdditi.prodleft_trivialadd_equivsymmmk
    (E G : Type*) [Group E] [Group G] [Subsingleton E] (g : G) :
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).symm
      (Additive.ofMul (mFQuot.mk p G g)) =
    Additive.ofMul (mFQuot.mk p (E × G) (1, g)) := rfl


/-- Naturality of the additive right trivial-factor equivalence. -/
theorem mFAdditi.prodright_trivialadd_equivnatural
    {G₁ G₂ E₁ E₂ : Type*} [Group G₁] [Group G₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × E₁)) :
    mFAdditi.mapAdd (p := p) f
        (mFAdditi.prod_righttrivial_addequiv (p := p) G₁ E₁ x) =
      mFAdditi.prod_righttrivial_addequiv (p := p) G₂ E₂
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f e) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, t⟩
  rfl

/-- Naturality of the inverse additive right trivial-factor equivalence. -/
theorem mFAdditi.prodright_trivialadd_equisymmnatu
    {G₁ G₂ E₁ E₂ : Type*} [Group G₁] [Group G₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂)
    (x : mFAdditi p G₁) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f e)
        ((mFAdditi.prod_righttrivial_addequiv (p := p) G₁ E₁).symm x) =
      (mFAdditi.prod_righttrivial_addequiv (p := p) G₂ E₂).symm
        (mFAdditi.mapAdd (p := p) f x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change Additive.ofMul (mFQuot.mk p (G₂ × E₂) (f g, e 1)) =
    Additive.ofMul (mFQuot.mk p (G₂ × E₂) (f g, 1))
  rw [map_one]

/-- Naturality of the additive left trivial-factor equivalence. -/
theorem mFAdditi.prodleft_trivialadd_equivnatural
    {E₁ E₂ G₁ G₂ : Type*} [Group E₁] [Group E₂] [Group G₁] [Group G₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (e : E₁ →* E₂) (f : G₁ →* G₂)
    (x : mFAdditi p (E₁ × G₁)) :
    mFAdditi.mapAdd (p := p) f
        (mFAdditi.prod_lefttrivial_addequiv (p := p) E₁ G₁ x) =
      mFAdditi.prod_lefttrivial_addequiv (p := p) E₂ G₂
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap e f) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨t, g⟩
  rfl

/-- Naturality of the inverse additive left trivial-factor equivalence. -/
theorem mFAdditi.prodleft_trivialadd_equisymmnatu
    {E₁ E₂ G₁ G₂ : Type*} [Group E₁] [Group E₂] [Group G₁] [Group G₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (e : E₁ →* E₂) (f : G₁ →* G₂)
    (x : mFAdditi p G₁) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap e f)
        ((mFAdditi.prod_lefttrivial_addequiv (p := p) E₁ G₁).symm x) =
      (mFAdditi.prod_lefttrivial_addequiv (p := p) E₂ G₂).symm
        (mFAdditi.mapAdd (p := p) f x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change Additive.ofMul (mFQuot.mk p (E₂ × G₂) (e 1, f g)) =
    Additive.ofMul (mFQuot.mk p (E₂ × G₂) (1, f g))
  rw [map_one]


/-- Linear right-unit equivalence for a subsingleton product factor. -/
noncomputable def mFAdditi.prod_righttrivial_linequiv [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E] :
    mFAdditi p (G × E) ≃ₗ[ZMod p] mFAdditi p G :=
{ toFun := mFAdditi.mapLinear (p := p) (MonoidHom.fst G E)
  invFun := mFAdditi.mapLinear (p := p) (MonoidHom.inl G E)
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, e⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prodright_triviallin_equivapply [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    mFAdditi.prod_righttrivial_linequiv (p := p) G E x =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G E) x := rfl

@[simp] theorem mFAdditi.prodright_triviallin_equivsymmapply [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) :
    (mFAdditi.prod_righttrivial_linequiv (p := p) G E).symm x =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl G E) x := rfl

@[simp] theorem mFAdditi.prodright_triviallin_equivmk [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E] (g : G) (e : E) :
    mFAdditi.prod_righttrivial_linequiv (p := p) G E
      (Additive.ofMul (mFQuot.mk p (G × E) (g, e))) =
    Additive.ofMul (mFQuot.mk p G g) := rfl

@[simp] theorem mFAdditi.prodright_triviallin_equivsymmmk [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E] (g : G) :
    (mFAdditi.prod_righttrivial_linequiv (p := p) G E).symm
      (Additive.ofMul (mFQuot.mk p G g)) =
    Additive.ofMul (mFQuot.mk p (G × E) (g, 1)) := rfl

/-- Linear left-unit equivalence for a subsingleton product factor. -/
noncomputable def mFAdditi.prod_lefttrivial_linequiv [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E] :
    mFAdditi p (E × G) ≃ₗ[ZMod p] mFAdditi p G :=
{ toFun := mFAdditi.mapLinear (p := p) (MonoidHom.snd E G)
  invFun := mFAdditi.mapLinear (p := p) (MonoidHom.inr E G)
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨e, g⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prodleft_triviallin_equivapply [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    mFAdditi.prod_lefttrivial_linequiv (p := p) E G x =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd E G) x := rfl

@[simp] theorem mFAdditi.prodleft_triviallin_equivsymmapply [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p G) :
    (mFAdditi.prod_lefttrivial_linequiv (p := p) E G).symm x =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr E G) x := rfl

@[simp] theorem mFAdditi.prodleft_triviallin_equivmk [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E] (e : E) (g : G) :
    mFAdditi.prod_lefttrivial_linequiv (p := p) E G
      (Additive.ofMul (mFQuot.mk p (E × G) (e, g))) =
    Additive.ofMul (mFQuot.mk p G g) := rfl

@[simp] theorem mFAdditi.prodleft_triviallin_equivsymmmk [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E] (g : G) :
    (mFAdditi.prod_lefttrivial_linequiv (p := p) E G).symm
      (Additive.ofMul (mFQuot.mk p G g)) =
    Additive.ofMul (mFQuot.mk p (E × G) (1, g)) := rfl


/-- Naturality of the linear right trivial-factor equivalence. -/
theorem mFAdditi.prodright_triviallin_equivnatural [Fact p.Prime]
    {G₁ G₂ E₁ E₂ : Type*} [Group G₁] [Group G₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × E₁)) :
    mFAdditi.mapLinear (p := p) f
        (mFAdditi.prod_righttrivial_linequiv (p := p) G₁ E₁ x) =
      mFAdditi.prod_righttrivial_linequiv (p := p) G₂ E₂
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f e) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, t⟩
  rfl

/-- Naturality of the inverse linear right trivial-factor equivalence. -/
theorem mFAdditi.prodright_triviallin_equisymmnatu [Fact p.Prime]
    {G₁ G₂ E₁ E₂ : Type*} [Group G₁] [Group G₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂)
    (x : mFAdditi p G₁) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f e)
        ((mFAdditi.prod_righttrivial_linequiv (p := p) G₁ E₁).symm x) =
      (mFAdditi.prod_righttrivial_linequiv (p := p) G₂ E₂).symm
        (mFAdditi.mapLinear (p := p) f x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change Additive.ofMul (mFQuot.mk p (G₂ × E₂) (f g, e 1)) =
    Additive.ofMul (mFQuot.mk p (G₂ × E₂) (f g, 1))
  rw [map_one]

/-- Naturality of the linear left trivial-factor equivalence. -/
theorem mFAdditi.prodleft_triviallin_equivnatural [Fact p.Prime]
    {E₁ E₂ G₁ G₂ : Type*} [Group E₁] [Group E₂] [Group G₁] [Group G₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (e : E₁ →* E₂) (f : G₁ →* G₂)
    (x : mFAdditi p (E₁ × G₁)) :
    mFAdditi.mapLinear (p := p) f
        (mFAdditi.prod_lefttrivial_linequiv (p := p) E₁ G₁ x) =
      mFAdditi.prod_lefttrivial_linequiv (p := p) E₂ G₂
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap e f) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨t, g⟩
  rfl

/-- Naturality of the inverse linear left trivial-factor equivalence. -/
theorem mFAdditi.prodleft_triviallin_equisymmnatu [Fact p.Prime]
    {E₁ E₂ G₁ G₂ : Type*} [Group E₁] [Group E₂] [Group G₁] [Group G₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (e : E₁ →* E₂) (f : G₁ →* G₂)
    (x : mFAdditi p G₁) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap e f)
        ((mFAdditi.prod_lefttrivial_linequiv (p := p) E₁ G₁).symm x) =
      (mFAdditi.prod_lefttrivial_linequiv (p := p) E₂ G₂).symm
        (mFAdditi.mapLinear (p := p) f x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  change Additive.ofMul (mFQuot.mk p (E₂ × G₂) (e 1, f g)) =
    Additive.ofMul (mFQuot.mk p (E₂ × G₂) (1, f g))
  rw [map_one]

/-- Additive equivalence obtained by deleting a trivial middle factor. -/
noncomputable def mFAdditi.prod_middletrivial_addequiv
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E] :
    mFAdditi p ((G × E) × H) ≃+
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
  invFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.inl G E) (MonoidHom.id H))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨ge, h⟩
    rcases ge with ⟨g, e⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prodmiddle_trivialadd_equivapply
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prod_middletrivial_addequiv (p := p) G E H x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x := rfl

@[simp] theorem mFAdditi.prodmiddle_trivialadd_equivsymmapply
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prod_middletrivial_addequiv (p := p) G E H).symm x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.inl G E) (MonoidHom.id H)) x := rfl

@[simp] theorem mFAdditi.prodmiddle_trivialadd_equivmk
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (e : E) (h : H) :
    mFAdditi.prod_middletrivial_addequiv (p := p) G E H
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × E) × H)) ((g, e), h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodmiddle_trivialadd_equivsymmmk
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prod_middletrivial_addequiv (p := p) G E H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × E) × H)) ((g, 1), h)) := rfl

/-- Naturality of the additive middle-trivial equivalence. -/
theorem mFAdditi.prodmiddle_trivialadd_equivnatural
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p ((G₁ × E₁) × H₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prod_middletrivial_addequiv (p := p) G₁ E₁ H₁ x) =
      mFAdditi.prod_middletrivial_addequiv (p := p) G₂ E₂ H₂
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.prodMap f e) h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, k⟩
  rcases ge with ⟨g, u⟩
  rfl

/-- Naturality of the inverse additive middle-trivial equivalence. -/
theorem mFAdditi.prodmiddle_trivialadd_equisymmnatu
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.prodMap f e) h)
        ((mFAdditi.prod_middletrivial_addequiv (p := p) G₁ E₁ H₁).symm x) =
      (mFAdditi.prod_middletrivial_addequiv (p := p) G₂ E₂ H₂).symm
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, k⟩
  change Additive.ofMul (mFQuot.mk p ((G₂ × E₂) × H₂)
      ((f g, e 1), h k)) =
    Additive.ofMul (mFQuot.mk p ((G₂ × E₂) × H₂)
      ((f g, 1), h k))
  rw [map_one]

/-- Linear equivalence obtained by deleting a trivial middle factor. -/
noncomputable def mFAdditi.prod_middletrivial_linequiv [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E] :
    mFAdditi p ((G × E) × H) ≃ₗ[ZMod p]
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
  invFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.inl G E) (MonoidHom.id H))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨ge, h⟩
    rcases ge with ⟨g, e⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prodmiddle_triviallin_equivapply [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prod_middletrivial_linequiv (p := p) G E H x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x := rfl

@[simp] theorem mFAdditi.prodmiddle_triviallin_equivsymmapply
    [Fact p.Prime] (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prod_middletrivial_linequiv (p := p) G E H).symm x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.inl G E) (MonoidHom.id H)) x := rfl

@[simp] theorem mFAdditi.prodmiddle_triviallin_equivmk [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (e : E) (h : H) :
    mFAdditi.prod_middletrivial_linequiv (p := p) G E H
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × E) × H)) ((g, e), h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodmiddle_triviallin_equivsymmmk
    [Fact p.Prime] (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prod_middletrivial_linequiv (p := p) G E H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × E) × H)) ((g, 1), h)) := rfl

/-- Naturality of the linear middle-trivial equivalence. -/
theorem mFAdditi.prodmiddle_triviallin_equivnatural [Fact p.Prime]
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p ((G₁ × E₁) × H₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prod_middletrivial_linequiv (p := p) G₁ E₁ H₁ x) =
      mFAdditi.prod_middletrivial_linequiv (p := p) G₂ E₂ H₂
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.prodMap f e) h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, k⟩
  rcases ge with ⟨g, u⟩
  rfl

/-- Naturality of the inverse linear middle-trivial equivalence. -/
theorem mFAdditi.prodmiddle_triviallin_equisymmnatu
    [Fact p.Prime]
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.prodMap f e) h)
        ((mFAdditi.prod_middletrivial_linequiv (p := p) G₁ E₁ H₁).symm x) =
      (mFAdditi.prod_middletrivial_linequiv (p := p) G₂ E₂ H₂).symm
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, k⟩
  change Additive.ofMul (mFQuot.mk p ((G₂ × E₂) × H₂)
      ((f g, e 1), h k)) =
    Additive.ofMul (mFQuot.mk p ((G₂ × E₂) × H₂)
      ((f g, 1), h k))
  rw [map_one]

/-- Additive product splitting of the inverse right-trivial unitor. -/
@[simp] theorem mFAdditi.prodaddequiv_prodrightriv_addequivsymm
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) :
    mFAdditi.prodAddEquiv (p := p) G E
        ((mFAdditi.prod_righttrivial_addequiv (p := p) G E).symm x) =
      (x, 0) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Additive product splitting of the inverse left-trivial unitor. -/
@[simp] theorem mFAdditi.prodaddequiv_prodlefttrivial_addequivsymm
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p G) :
    mFAdditi.prodAddEquiv (p := p) E G
        ((mFAdditi.prod_lefttrivial_addequiv (p := p) E G).symm x) =
      (0, x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Linear product splitting of the inverse right-trivial unitor. -/
@[simp] theorem mFAdditi.prodlinequiv_prodrightriv_linequivsymm
    [Fact p.Prime] (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p G) :
    mFAdditi.prodLinearEquiv (p := p) G E
        ((mFAdditi.prod_righttrivial_linequiv (p := p) G E).symm x) =
      (x, 0) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Linear product splitting of the inverse left-trivial unitor. -/
@[simp] theorem mFAdditi.prodlinequiv_prodlefttrivial_linequivsymm
    [Fact p.Prime] (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p G) :
    mFAdditi.prodLinearEquiv (p := p) E G
        ((mFAdditi.prod_lefttrivial_linequiv (p := p) E G).symm x) =
      (0, x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl



/-- Additive equivalence induced by swapping the two factors of a product. -/
noncomputable def mFAdditi.prod_comm_addequiv
    (G H : Type*) [Group G] [Group H] :
    mFAdditi p (G × H) ≃+ mFAdditi p (H × G) :=
{ toFun := mFAdditi.mapAdd (p := p)
    (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
  invFun := mFAdditi.mapAdd (p := p)
    (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
  left_inv := by
    intro x
    exact mFAdditi.mapadd_prodcommmap_addprodcomm (p := p) G H x
  right_inv := by
    intro x
    exact mFAdditi.mapadd_prodcommmap_addprodcomm (p := p) H G x
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prod_commadd_equivapply
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prod_comm_addequiv (p := p) G H x =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x := rfl

@[simp] theorem mFAdditi.prod_commadd_equivsymm
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.prod_comm_addequiv (p := p) G H).symm =
      mFAdditi.prod_comm_addequiv (p := p) H G := by
  rfl


/-- Additive swap-unit coherence for a trivial right factor. -/
theorem mFAdditi.prodcomm_addequiv_trivialright
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    mFAdditi.prod_lefttrivial_addequiv (p := p) E G
        (mFAdditi.prod_comm_addequiv (p := p) G E x) =
      mFAdditi.prod_righttrivial_addequiv (p := p) G E x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, e⟩
  rfl

/-- Additive swap-unit coherence for a trivial left factor. -/
theorem mFAdditi.prodcomm_addequiv_trivialleft
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    mFAdditi.prod_righttrivial_addequiv (p := p) G E
        (mFAdditi.prod_comm_addequiv (p := p) E G x) =
      mFAdditi.prod_lefttrivial_addequiv (p := p) E G x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨e, g⟩
  rfl

/-- Linear equivalence induced by swapping the two factors of a product. -/
noncomputable def mFAdditi.prod_comm_linequiv [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    mFAdditi p (G × H) ≃ₗ[ZMod p] mFAdditi p (H × G) :=
{ toFun := mFAdditi.mapLinear (p := p)
    (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
  invFun := mFAdditi.mapLinear (p := p)
    (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
  left_inv := by
    intro x
    exact mFAdditi.maplin_prodcommmap_linprodcomm (p := p) G H x
  right_inv := by
    intro x
    exact mFAdditi.maplin_prodcommmap_linprodcomm (p := p) H G x
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prod_commlin_equivapply [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prod_comm_linequiv (p := p) G H x =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x := rfl

@[simp] theorem mFAdditi.prod_commlin_equivsymm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    (mFAdditi.prod_comm_linequiv (p := p) G H).symm =
      mFAdditi.prod_comm_linequiv (p := p) H G := by
  rfl


/-- Linear swap-unit coherence for a trivial right factor. -/
theorem mFAdditi.prodcomm_linequiv_trivialright [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × E)) :
    mFAdditi.prod_lefttrivial_linequiv (p := p) E G
        (mFAdditi.prod_comm_linequiv (p := p) G E x) =
      mFAdditi.prod_righttrivial_linequiv (p := p) G E x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, e⟩
  rfl

/-- Linear swap-unit coherence for a trivial left factor. -/
theorem mFAdditi.prodcomm_linequiv_trivialleft [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    (x : mFAdditi p (E × G)) :
    mFAdditi.prod_righttrivial_linequiv (p := p) G E
        (mFAdditi.prod_comm_linequiv (p := p) E G x) =
      mFAdditi.prod_lefttrivial_linequiv (p := p) E G x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨e, g⟩
  rfl

/-- Naturality of the additive swap map under factorwise product maps. -/
theorem mFAdditi.map_addprod_commnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap g f)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodComm (M := G₁) (N := H₁)).toMonoidHom x) =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := G₂) (N := H₂)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Naturality of the linear swap map under factorwise product maps. -/
theorem mFAdditi.map_linprod_commnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap g f)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodComm (M := G₁) (N := H₁)).toMonoidHom x) =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := G₂) (N := H₂)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Packaged additive swap naturality under factorwise product maps. -/
theorem mFAdditi.prod_commadd_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap g f)
        (mFAdditi.prod_comm_addequiv (p := p) G₁ H₁ x) =
      mFAdditi.prod_comm_addequiv (p := p) G₂ H₂
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f g) x) := by
  simpa using mFAdditi.map_addprod_commnatural (p := p) f g x

/-- Packaged linear swap naturality under factorwise product maps. -/
theorem mFAdditi.prod_commlin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap g f)
        (mFAdditi.prod_comm_linequiv (p := p) G₁ H₁ x) =
      mFAdditi.prod_comm_linequiv (p := p) G₂ H₂
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f g) x) := by
  simpa using mFAdditi.map_linprod_commnatural (p := p) f g x


/-- Additive product equivalence formula using the packaged swap equivalence. -/
theorem mFAdditi.prodadd_equivprod_commaddequiv
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodAddEquiv (p := p) H G
        (mFAdditi.prod_comm_addequiv (p := p) G H x) =
      ((mFAdditi.prodAddEquiv (p := p) G H x).2,
        (mFAdditi.prodAddEquiv (p := p) G H x).1) := by
  simpa using mFAdditi.prodadd_equivmap_prodcomm (p := p) G H x

/-- Linear product equivalence formula using the packaged swap equivalence. -/
theorem mFAdditi.prodlin_equivprod_commlinequiv [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodLinearEquiv (p := p) H G
        (mFAdditi.prod_comm_linequiv (p := p) G H x) =
      ((mFAdditi.prodLinearEquiv (p := p) G H x).2,
        (mFAdditi.prodLinearEquiv (p := p) G H x).1) := by
  simpa using mFAdditi.prodlin_equivmap_prodcomm (p := p) G H x

/-- Swapping after additive first-factor insertion gives second-factor insertion. -/
@[simp] theorem mFAdditi.map_addprod_comminl
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr H G) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Swapping after additive second-factor insertion gives first-factor insertion. -/
@[simp] theorem mFAdditi.map_addprod_comminr
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p H) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl H G) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- Swapping after linear first-factor insertion gives second-factor insertion. -/
@[simp] theorem mFAdditi.map_linprod_comminl [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr H G) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Swapping after linear second-factor insertion gives first-factor insertion. -/
@[simp] theorem mFAdditi.map_linprod_comminr [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p H) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl H G) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- First additive projection after swapping factors is the original second projection. -/
@[simp] theorem mFAdditi.map_addfst_prodcomm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst H G)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Second additive projection after swapping factors is the original first projection. -/
@[simp] theorem mFAdditi.map_addsnd_prodcomm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd H G)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- First linear projection after swapping factors is the original second projection. -/
@[simp] theorem mFAdditi.map_linfst_prodcomm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst H G)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Second linear projection after swapping factors is the original first projection. -/
@[simp] theorem mFAdditi.map_linsnd_prodcomm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd H G)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G H) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, b⟩
  rfl

/-- Inverse additive product equivalences are compatible with swapping factors. -/
theorem mFAdditi.mapadd_prodcommprod_addequivsymm
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G × mFAdditi p H) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        ((mFAdditi.prodAddEquiv (p := p) G H).symm x) =
      (mFAdditi.prodAddEquiv (p := p) H G).symm (x.2, x.1) := by
  rcases x with ⟨x, y⟩
  cases x using Additive.rec
  cases y using Additive.rec
  rename_i q r
  refine QuotientGroup.induction_on q ?_
  intro a
  refine QuotientGroup.induction_on r ?_
  intro b
  change mFAdditi.mapAdd (p := p)
      (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
      ((mFAdditi.prodAddEquiv (p := p) G H).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) a),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) b))) =
    (mFAdditi.prodAddEquiv (p := p) H G).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) b),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) a))
  rw [mFAdditi.prod_addequiv_symmmul]
  rw [mFAdditi.prod_addequiv_symmmul]
  rfl

/-- Inverse linear product equivalences are compatible with swapping factors. -/
theorem mFAdditi.maplin_prodcommprod_linequivsymm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    (x : mFAdditi p G × mFAdditi p H) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
        ((mFAdditi.prodLinearEquiv (p := p) G H).symm x) =
      (mFAdditi.prodLinearEquiv (p := p) H G).symm (x.2, x.1) := by
  rcases x with ⟨x, y⟩
  cases x using Additive.rec
  cases y using Additive.rec
  rename_i q r
  refine QuotientGroup.induction_on q ?_
  intro a
  refine QuotientGroup.induction_on r ?_
  intro b
  change mFAdditi.mapLinear (p := p)
      (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
      ((mFAdditi.prodLinearEquiv (p := p) G H).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) a),
          Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) b))) =
    (mFAdditi.prodLinearEquiv (p := p) H G).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p H) b),
        Additive.ofMul (QuotientGroup.mk' (modPFrattini p G) a))
  rw [mFAdditi.prod_linequiv_symmmul]
  rw [mFAdditi.prod_linequiv_symmmul]
  rfl





/-- Associator sends first-factor additive insertion to first-factor insertion. -/
@[simp] theorem mFAdditi.mapadd_prodassoc_inlinl
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p G) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl (G × H) K)
          (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl G (H × K)) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Associator sends middle-factor additive insertion to nested right-left insertion. -/
@[simp] theorem mFAdditi.mapadd_prodassoc_inlinr
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p H) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl (G × H) K)
          (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr G (H × K))
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl H K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- Associator sends last-factor additive insertion to nested right-right insertion. -/
@[simp] theorem mFAdditi.map_addprod_associnr
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p K) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr (G × H) K) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr G (H × K))
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr H K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro c
  rfl


/-- First projection after additive associator is the nested first-first projection. -/
@[simp] theorem mFAdditi.map_addfst_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst G (H × K))
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Middle projection after additive associator is the nested first-second projection. -/
@[simp] theorem mFAdditi.mapadd_fstsnd_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K))
          (mFAdditi.mapAdd (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Last projection after additive associator is the outer second projection. -/
@[simp] theorem mFAdditi.mapadd_sndsnd_prodassoc
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K))
          (mFAdditi.mapAdd (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd (G × H) K) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Inverse associator sends first-factor additive insertion to nested left-left insertion. -/
@[simp] theorem mFAdditi.mapadd_prodassoc_symminl
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p G) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl G (H × K)) x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl (G × H) K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inl G H) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Inverse associator sends middle-factor additive insertion to nested left-right insertion. -/
@[simp] theorem mFAdditi.mapadd_prodassoc_symminrinl
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p H) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G (H × K))
          (mFAdditi.mapAdd (p := p) (MonoidHom.inl H K) x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inl (G × H) K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G H) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- Inverse associator sends last-factor additive insertion to outer right insertion. -/
@[simp] theorem mFAdditi.mapadd_prodassoc_symminrinr
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p K) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.inr G (H × K))
          (mFAdditi.mapAdd (p := p) (MonoidHom.inr H K) x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.inr (G × H) K) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro c
  rfl


/-- First nested projection after inverse additive associator is target first projection. -/
@[simp] theorem mFAdditi.mapadd_fstfst_prodassocsymm
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K)
          (mFAdditi.mapAdd (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst G (H × K)) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Second nested projection after inverse additive associator is target middle projection. -/
@[simp] theorem mFAdditi.mapadd_sndfst_prodassocsymm
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapAdd (p := p) (MonoidHom.fst (G × H) K)
          (mFAdditi.mapAdd (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)) =
      mFAdditi.mapAdd (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Outer second projection after inverse additive associator is target last projection. -/
@[simp] theorem mFAdditi.mapadd_sndprod_assocsymm
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.snd (G × H) K)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x) =
      mFAdditi.mapAdd (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapAdd (p := p) (MonoidHom.snd G (H × K)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl


/-- Associating and then unassociating product factors is identity additively. -/
@[simp] theorem mFAdditi.mapaddprod_assocsymmmap_addprodassoc
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Unassociating and then associating product factors is identity additively. -/
@[simp] theorem mFAdditi.mapaddprod_assocmapadd_prodassocsymm
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Naturality of the additive associator map under factorwise product maps. -/
theorem mFAdditi.map_addprod_assocnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p ((G₁ × H₁) × K₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h))
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G₁) (N := H₁) (P := K₁)).toMonoidHom x) =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G₂) (N := H₂) (P := K₂)).toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Naturality of the inverse additive associator map under factorwise product maps. -/
theorem mFAdditi.mapadd_prodassoc_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p (G₁ × H₁ × K₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G₁) (N := H₁) (P := K₁)).symm.toMonoidHom x) =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G₂) (N := H₂) (P := K₂)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl


/-- Triangle coherence for additive associators with a trivial middle factor. -/
theorem mFAdditi.mapadd_prodassoc_trivialtriangle
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := E) (P := H)).toMonoidHom x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  have he : e = 1 := Subsingleton.elim e 1
  subst e
  rfl

/-- Inverse triangle coherence for additive associators with a trivial middle factor. -/
theorem mFAdditi.mapadd_prodassoc_symmtrivtria
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × E × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := E) (P := H)).symm.toMonoidHom x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  have he : e = 1 := Subsingleton.elim e 1
  subst e
  rfl


/-- Pentagon coherence for additive product associator maps. -/
theorem mFAdditi.map_addprod_assocpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (((G × H) × K) × L)) :
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom
      (mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom x) =
    mFAdditi.mapAdd (p := p)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom)
      (mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) x)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨abc, d⟩
  rcases abc with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Pentagon coherence for linear product associator maps. -/
theorem mFAdditi.map_linprod_assocpentagon [Fact p.Prime]
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (((G × H) × K) × L)) :
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom
      (mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom x) =
    mFAdditi.mapLinear (p := p)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom)
      (mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) x)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨abc, d⟩
  rcases abc with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Hexagon coherence for moving a left factor past a binary product additively. -/
theorem mFAdditi.mapadd_prodcomm_assohexaleft
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom x =
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom
      (mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom)
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom
          (mFAdditi.mapAdd (p := p)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K))
            (mFAdditi.mapAdd (p := p)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)))) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor additively. -/
theorem mFAdditi.mapadd_prodcomm_assohexarigh
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom x =
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom
      (mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H))
        (mFAdditi.mapAdd (p := p)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom
          (mFAdditi.mapAdd (p := p)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom)
            (mFAdditi.mapAdd (p := p)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)))) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Hexagon coherence for moving a left factor past a binary product linearly. -/
theorem mFAdditi.maplin_prodcomm_assohexaleft [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom x =
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom
      (mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom
          (mFAdditi.mapLinear (p := p)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K))
            (mFAdditi.mapLinear (p := p)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)))) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor linearly. -/
theorem mFAdditi.maplin_prodcomm_assohexarigh [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom x =
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom
      (mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H))
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom
          (mFAdditi.mapLinear (p := p)
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom)
            (mFAdditi.mapLinear (p := p)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)))) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Inverse pentagon coherence for additive product associator maps. -/
theorem mFAdditi.mapadd_prodassoc_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (G × H × K × L)) :
    mFAdditi.mapAdd (p := p)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom
      (mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom x) =
    mFAdditi.mapAdd (p := p)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L))
      (mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) x)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl

/-- Inverse pentagon coherence for linear product associator maps. -/
theorem mFAdditi.maplin_prodassoc_symmpentagon [Fact p.Prime]
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (G × H × K × L)) :
    mFAdditi.mapLinear (p := p)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom
      (mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom x) =
    mFAdditi.mapLinear (p := p)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L))
      (mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) x)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl


/-- Additive equivalence induced by associating three product factors. -/
noncomputable def mFAdditi.prod_assoc_addequiv
    (G H K : Type*) [Group G] [Group H] [Group K] :
    mFAdditi p ((G × H) × K) ≃+
      mFAdditi p (G × H × K) :=
{ toFun := mFAdditi.mapAdd (p := p)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
  invFun := mFAdditi.mapAdd (p := p)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
  left_inv := by
    intro x
    exact mFAdditi.mapaddprod_assocsymmmap_addprodassoc (p := p) G H K x
  right_inv := by
    intro x
    exact mFAdditi.mapaddprod_assocmapadd_prodassocsymm (p := p) G H K x
  map_add' := by
    intro x y
    exact map_add _ x y }

/-- Associator sends first-factor linear insertion to first-factor insertion. -/
@[simp] theorem mFAdditi.maplin_prodassoc_inlinl [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p G) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl (G × H) K)
          (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl G (H × K)) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Associator sends middle-factor linear insertion to nested right-left insertion. -/
@[simp] theorem mFAdditi.maplin_prodassoc_inlinr [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p H) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl (G × H) K)
          (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr G (H × K))
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl H K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- Associator sends last-factor linear insertion to nested right-right insertion. -/
@[simp] theorem mFAdditi.map_linprod_associnr [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p K) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr (G × H) K) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr G (H × K))
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr H K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro c
  rfl


/-- First projection after linear associator is the nested first-first projection. -/
@[simp] theorem mFAdditi.map_linfst_prodassoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst G (H × K))
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Middle projection after linear associator is the nested first-second projection. -/
@[simp] theorem mFAdditi.maplin_fstsnd_prodassoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K))
          (mFAdditi.mapLinear (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Last projection after linear associator is the outer second projection. -/
@[simp] theorem mFAdditi.maplin_sndsnd_prodassoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K))
          (mFAdditi.mapLinear (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd (G × H) K) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Inverse associator sends first-factor linear insertion to nested left-left insertion. -/
@[simp] theorem mFAdditi.maplin_prodassoc_symminl [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p G) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl G (H × K)) x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl (G × H) K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inl G H) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Inverse associator sends middle-factor linear insertion to nested left-right insertion. -/
@[simp] theorem mFAdditi.maplin_prodassoc_symminrinl [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p H) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G (H × K))
          (mFAdditi.mapLinear (p := p) (MonoidHom.inl H K) x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inl (G × H) K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G H) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro b
  rfl

/-- Inverse associator sends last-factor linear insertion to outer right insertion. -/
@[simp] theorem mFAdditi.maplin_prodassoc_symminrinr [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p K) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p) (MonoidHom.inr G (H × K))
          (mFAdditi.mapLinear (p := p) (MonoidHom.inr H K) x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.inr (G × H) K) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro c
  rfl


/-- First nested projection after inverse linear associator is target first projection. -/
@[simp] theorem mFAdditi.maplin_fstfst_prodassocsymm [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.fst G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K)
          (mFAdditi.mapLinear (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst G (H × K)) x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Second nested projection after inverse linear associator is target middle projection. -/
@[simp] theorem mFAdditi.maplin_sndfst_prodassocsymm [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd G H)
        (mFAdditi.mapLinear (p := p) (MonoidHom.fst (G × H) K)
          (mFAdditi.mapLinear (p := p)
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x)) =
      mFAdditi.mapLinear (p := p) (MonoidHom.fst H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Outer second projection after inverse linear associator is target last projection. -/
@[simp] theorem mFAdditi.maplin_sndprod_assocsymm [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.snd (G × H) K)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x) =
      mFAdditi.mapLinear (p := p) (MonoidHom.snd H K)
        (mFAdditi.mapLinear (p := p) (MonoidHom.snd G (H × K)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl


/-- Associating and then unassociating product factors is identity linearly. -/
@[simp] theorem mFAdditi.maplinprod_assocsymmmap_linprodassoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Unassociating and then associating product factors is identity linearly. -/
@[simp] theorem mFAdditi.maplinprod_assocmaplin_prodassocsymm [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x) = x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Naturality of the linear associator map under factorwise product maps. -/
theorem mFAdditi.map_linprod_assocnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p ((G₁ × H₁) × K₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h))
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G₁) (N := H₁) (P := K₁)).toMonoidHom x) =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G₂) (N := H₂) (P := K₂)).toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl

/-- Naturality of the inverse linear associator map under factorwise product maps. -/
theorem mFAdditi.maplin_prodassoc_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p (G₁ × H₁ × K₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G₁) (N := H₁) (P := K₁)).symm.toMonoidHom x) =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G₂) (N := H₂) (P := K₂)).symm.toMonoidHom
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl


/-- Triangle coherence for linear associators with a trivial middle factor. -/
theorem mFAdditi.maplin_prodassoc_trivialtriangle [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := E) (P := H)).toMonoidHom x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  have he : e = 1 := Subsingleton.elim e 1
  subst e
  rfl

/-- Inverse triangle coherence for linear associators with a trivial middle factor. -/
theorem mFAdditi.maplin_prodassoc_symmtrivtria [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × E × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
        (mFAdditi.mapLinear (p := p)
          (MulEquiv.prodAssoc (M := G) (N := E) (P := H)).symm.toMonoidHom x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  have he : e = 1 := Subsingleton.elim e 1
  subst e
  rfl


/-- Linear equivalence induced by associating three product factors. -/
noncomputable def mFAdditi.prod_assoc_linequiv [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K] :
    mFAdditi p ((G × H) × K) ≃ₗ[ZMod p]
      mFAdditi p (G × H × K) :=
{ toFun := mFAdditi.mapLinear (p := p)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
  invFun := mFAdditi.mapLinear (p := p)
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
  left_inv := by
    intro x
    exact mFAdditi.maplinprod_assocsymmmap_linprodassoc (p := p) G H K x
  right_inv := by
    intro x
    exact mFAdditi.maplinprod_assocmaplin_prodassocsymm (p := p) G H K x
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }


/-- Packaged additive associator naturality under factorwise product maps. -/
theorem mFAdditi.prod_assocadd_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p ((G₁ × H₁) × K₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h))
        (mFAdditi.prod_assoc_addequiv (p := p) G₁ H₁ K₁ x) =
      mFAdditi.prod_assoc_addequiv (p := p) G₂ H₂ K₂
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h) x) := by
  simpa using mFAdditi.map_addprod_assocnatural (p := p) f g h x

/-- Packaged inverse additive associator naturality under factorwise product maps. -/
theorem mFAdditi.prodassoc_addequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p (G₁ × H₁ × K₁)) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
        ((mFAdditi.prod_assoc_addequiv (p := p) G₁ H₁ K₁).symm x) =
      (mFAdditi.prod_assoc_addequiv (p := p) G₂ H₂ K₂).symm
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h)) x) := by
  simpa using mFAdditi.mapadd_prodassoc_symmnatural (p := p) f g h x

/-- Packaged linear associator naturality under factorwise product maps. -/
theorem mFAdditi.prod_assoclin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p ((G₁ × H₁) × K₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f (MonoidHom.prodMap g h))
        (mFAdditi.prod_assoc_linequiv (p := p) G₁ H₁ K₁ x) =
      mFAdditi.prod_assoc_linequiv (p := p) G₂ H₂ K₂
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) x) := by
  simpa using mFAdditi.map_linprod_assocnatural (p := p) f g h x

/-- Packaged inverse linear associator naturality under factorwise product maps. -/
theorem mFAdditi.prodassoc_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂)
    (x : mFAdditi p (G₁ × H₁ × K₁)) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
        ((mFAdditi.prod_assoc_linequiv (p := p) G₁ H₁ K₁).symm x) =
      (mFAdditi.prod_assoc_linequiv (p := p) G₂ H₂ K₂).symm
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) x) := by
  simpa using mFAdditi.maplin_prodassoc_symmnatural (p := p) f g h x


/-- Pentagon coherence for packaged additive product associator equivalences. -/
theorem mFAdditi.prod_assocadd_equivpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (((G × H) × K) × L)) :
    mFAdditi.prod_assoc_addequiv (p := p) G H (K × L)
      (mFAdditi.prod_assoc_addequiv (p := p) (G × H) K L x) =
    mFAdditi.mapAdd (p := p)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom)
      (mFAdditi.prod_assoc_addequiv (p := p) G (H × K) L
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) x)) := by
  simpa using mFAdditi.map_addprod_assocpentagon (p := p) G H K L x

/-- Pentagon coherence for packaged linear product associator equivalences. -/
theorem mFAdditi.prod_assoclin_equivpentagon [Fact p.Prime]
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (((G × H) × K) × L)) :
    mFAdditi.prod_assoc_linequiv (p := p) G H (K × L)
      (mFAdditi.prod_assoc_linequiv (p := p) (G × H) K L x) =
    mFAdditi.mapLinear (p := p)
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom)
      (mFAdditi.prod_assoc_linequiv (p := p) G (H × K) L
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) x)) := by
  simpa using mFAdditi.map_linprod_assocpentagon (p := p) G H K L x

/-- Inverse pentagon coherence for packaged additive product associator equivalences. -/
theorem mFAdditi.prodassoc_addequiv_symmpentagon
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (G × H × K × L)) :
    (mFAdditi.prod_assoc_addequiv (p := p) (G × H) K L).symm
      ((mFAdditi.prod_assoc_addequiv (p := p) G H (K × L)).symm x) =
    mFAdditi.mapAdd (p := p)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L))
      ((mFAdditi.prod_assoc_addequiv (p := p) G (H × K) L).symm
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) x)) := by
  simpa using mFAdditi.mapadd_prodassoc_symmpentagon (p := p) G H K L x

/-- Inverse pentagon coherence for packaged linear product associator equivalences. -/
theorem mFAdditi.prodassoc_linequiv_symmpentagon [Fact p.Prime]
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L]
    (x : mFAdditi p (G × H × K × L)) :
    (mFAdditi.prod_assoc_linequiv (p := p) (G × H) K L).symm
      ((mFAdditi.prod_assoc_linequiv (p := p) G H (K × L)).symm x) =
    mFAdditi.mapLinear (p := p)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L))
      ((mFAdditi.prod_assoc_linequiv (p := p) G (H × K) L).symm
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) x)) := by
  simpa using mFAdditi.maplin_prodassoc_symmpentagon (p := p) G H K L x


/-- Packaged additive hexagon coherence for moving a left factor past a binary product. -/
theorem mFAdditi.prodcomm_addequiv_assohexaleft
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.prod_comm_addequiv (p := p) G (H × K) x =
      (mFAdditi.prod_assoc_addequiv (p := p) H K G).symm
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom)
          (mFAdditi.prod_assoc_addequiv (p := p) H G K
            (mFAdditi.mapAdd (p := p)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K))
              ((mFAdditi.prod_assoc_addequiv (p := p) G H K).symm x)))) := by
  simpa using mFAdditi.mapadd_prodcomm_assohexaleft (p := p) G H K x

/-- Packaged additive hexagon coherence for moving a binary product past a right factor. -/
theorem mFAdditi.prodcomm_addequiv_assohexarigh
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.prod_comm_addequiv (p := p) (G × H) K x =
      mFAdditi.prod_assoc_addequiv (p := p) K G H
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H))
          ((mFAdditi.prod_assoc_addequiv (p := p) G K H).symm
            (mFAdditi.mapAdd (p := p)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom)
              (mFAdditi.prod_assoc_addequiv (p := p) G H K x)))) := by
  simpa using mFAdditi.mapadd_prodcomm_assohexarigh (p := p) G H K x

/-- Packaged linear hexagon coherence for moving a left factor past a binary product. -/
theorem mFAdditi.prodcomm_linequiv_assohexaleft [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    mFAdditi.prod_comm_linequiv (p := p) G (H × K) x =
      (mFAdditi.prod_assoc_linequiv (p := p) H K G).symm
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom)
          (mFAdditi.prod_assoc_linequiv (p := p) H G K
            (mFAdditi.mapLinear (p := p)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K))
              ((mFAdditi.prod_assoc_linequiv (p := p) G H K).symm x)))) := by
  simpa using mFAdditi.maplin_prodcomm_assohexaleft (p := p) G H K x

/-- Packaged linear hexagon coherence for moving a binary product past a right factor. -/
theorem mFAdditi.prodcomm_linequiv_assohexarigh [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.prod_comm_linequiv (p := p) (G × H) K x =
      mFAdditi.prod_assoc_linequiv (p := p) K G H
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H))
          ((mFAdditi.prod_assoc_linequiv (p := p) G K H).symm
            (mFAdditi.mapLinear (p := p)
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom)
              (mFAdditi.prod_assoc_linequiv (p := p) G H K x)))) := by
  simpa using mFAdditi.maplin_prodcomm_assohexarigh (p := p) G H K x


@[simp] theorem mFAdditi.prod_assocadd_equivapply
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.prod_assoc_addequiv (p := p) G H K x =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x := rfl

@[simp] theorem mFAdditi.prod_assocadd_equivmk
    (G H K : Type*) [Group G] [Group H] [Group K]
    (a : G) (b : H) (c : K) :
    mFAdditi.prod_assoc_addequiv (p := p) G H K
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × H) × K)) ((a, b), c))) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H × K)) (a, (b, c))) := rfl

@[simp] theorem mFAdditi.prodassoc_addequiv_symmapply
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).symm x =
      mFAdditi.mapAdd (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x := rfl

@[simp] theorem mFAdditi.prodassoc_addequiv_symmmk
    (G H K : Type*) [Group G] [Group H] [Group K]
    (a : G) (b : H) (c : K) :
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H × K)) (a, (b, c)))) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × H) × K)) ((a, b), c)) := rfl

/-- First coordinate coherence between additive product splittings and associator. -/
theorem mFAdditi.prod_addequiv_assocfst
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodAddEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_addequiv (p := p) G H K x)).1 =
      (mFAdditi.prodAddEquiv (p := p) G H
        ((mFAdditi.prodAddEquiv (p := p) (G × H) K x).1)).1 := by
  simpa using mFAdditi.map_addfst_prodassoc (p := p) G H K x

/-- Middle coordinate coherence between additive product splittings and associator. -/
theorem mFAdditi.prod_addequiv_assocmid
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodAddEquiv (p := p) H K
      ((mFAdditi.prodAddEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_addequiv (p := p) G H K x)).2)).1 =
      (mFAdditi.prodAddEquiv (p := p) G H
        ((mFAdditi.prodAddEquiv (p := p) (G × H) K x).1)).2 := by
  simpa using mFAdditi.mapadd_fstsnd_prodassoc (p := p) G H K x

/-- Last coordinate coherence between additive product splittings and associator. -/
theorem mFAdditi.prod_addequiv_assocsnd
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodAddEquiv (p := p) H K
      ((mFAdditi.prodAddEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_addequiv (p := p) G H K x)).2)).2 =
      (mFAdditi.prodAddEquiv (p := p) (G × H) K x).2 := by
  simpa using mFAdditi.mapadd_sndsnd_prodassoc (p := p) G H K x


/-- First coordinate coherence for the inverse additive associator. -/
theorem mFAdditi.prodadd_equivassoc_symmfst
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodAddEquiv (p := p) G H
      ((mFAdditi.prodAddEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_addequiv (p := p) G H K).symm x)).1)).1 =
      (mFAdditi.prodAddEquiv (p := p) G (H × K) x).1 := by
  simpa using mFAdditi.mapadd_fstfst_prodassocsymm (p := p) G H K x

/-- Middle coordinate coherence for the inverse additive associator. -/
theorem mFAdditi.prodadd_equivassoc_symmmid
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodAddEquiv (p := p) G H
      ((mFAdditi.prodAddEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_addequiv (p := p) G H K).symm x)).1)).2 =
      (mFAdditi.prodAddEquiv (p := p) H K
        ((mFAdditi.prodAddEquiv (p := p) G (H × K) x).2)).1 := by
  simpa using mFAdditi.mapadd_sndfst_prodassocsymm (p := p) G H K x

/-- Last coordinate coherence for the inverse additive associator. -/
theorem mFAdditi.prodadd_equivassoc_symmsnd
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodAddEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_addequiv (p := p) G H K).symm x)).2 =
      (mFAdditi.prodAddEquiv (p := p) H K
        ((mFAdditi.prodAddEquiv (p := p) G (H × K) x).2)).2 := by
  simpa using mFAdditi.mapadd_sndprod_assocsymm (p := p) G H K x


@[simp] theorem mFAdditi.prod_assoclin_equivapply [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    mFAdditi.prod_assoc_linequiv (p := p) G H K x =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom x := rfl

@[simp] theorem mFAdditi.prod_assoclin_equivmk [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (a : G) (b : H) (c : K) :
    mFAdditi.prod_assoc_linequiv (p := p) G H K
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × H) × K)) ((a, b), c))) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H × K)) (a, (b, c))) := rfl
/-- First coordinate coherence between linear product splittings and associator. -/
theorem mFAdditi.prod_linequiv_assocfst [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodLinearEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_linequiv (p := p) G H K x)).1 =
      (mFAdditi.prodLinearEquiv (p := p) G H
        ((mFAdditi.prodLinearEquiv (p := p) (G × H) K x).1)).1 := by
  simpa using mFAdditi.map_linfst_prodassoc (p := p) G H K x

/-- Middle coordinate coherence between linear product splittings and associator. -/
theorem mFAdditi.prod_linequiv_assocmid [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodLinearEquiv (p := p) H K
      ((mFAdditi.prodLinearEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_linequiv (p := p) G H K x)).2)).1 =
      (mFAdditi.prodLinearEquiv (p := p) G H
        ((mFAdditi.prodLinearEquiv (p := p) (G × H) K x).1)).2 := by
  simpa using mFAdditi.maplin_fstsnd_prodassoc (p := p) G H K x

/-- Last coordinate coherence between linear product splittings and associator. -/
theorem mFAdditi.prod_linequiv_assocsnd [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p ((G × H) × K)) :
    (mFAdditi.prodLinearEquiv (p := p) H K
      ((mFAdditi.prodLinearEquiv (p := p) G (H × K)
        (mFAdditi.prod_assoc_linequiv (p := p) G H K x)).2)).2 =
      (mFAdditi.prodLinearEquiv (p := p) (G × H) K x).2 := by
  simpa using mFAdditi.maplin_sndsnd_prodassoc (p := p) G H K x


/-- First coordinate coherence for the inverse linear associator. -/
theorem mFAdditi.prodlin_equivassoc_symmfst [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodLinearEquiv (p := p) G H
      ((mFAdditi.prodLinearEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_linequiv (p := p) G H K).symm x)).1)).1 =
      (mFAdditi.prodLinearEquiv (p := p) G (H × K) x).1 := by
  simpa using mFAdditi.maplin_fstfst_prodassocsymm (p := p) G H K x

/-- Middle coordinate coherence for the inverse linear associator. -/
theorem mFAdditi.prodlin_equivassoc_symmmid [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodLinearEquiv (p := p) G H
      ((mFAdditi.prodLinearEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_linequiv (p := p) G H K).symm x)).1)).2 =
      (mFAdditi.prodLinearEquiv (p := p) H K
        ((mFAdditi.prodLinearEquiv (p := p) G (H × K) x).2)).1 := by
  simpa using mFAdditi.maplin_sndfst_prodassocsymm (p := p) G H K x

/-- Last coordinate coherence for the inverse linear associator. -/
theorem mFAdditi.prodlin_equivassoc_symmsnd [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prodLinearEquiv (p := p) (G × H) K
        ((mFAdditi.prod_assoc_linequiv (p := p) G H K).symm x)).2 =
      (mFAdditi.prodLinearEquiv (p := p) H K
        ((mFAdditi.prodLinearEquiv (p := p) G (H × K) x).2)).2 := by
  simpa using mFAdditi.maplin_sndprod_assocsymm (p := p) G H K x


@[simp] theorem mFAdditi.prodassoc_linequiv_symmapply [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (x : mFAdditi p (G × H × K)) :
    (mFAdditi.prod_assoc_linequiv (p := p) G H K).symm x =
      mFAdditi.mapLinear (p := p)
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom x := rfl

@[simp] theorem mFAdditi.prodassoc_linequiv_symmmk [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    (a : G) (b : H) (c : K) :
    (mFAdditi.prod_assoc_linequiv (p := p) G H K).symm
        (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H × K)) (a, (b, c)))) =
      Additive.ofMul (QuotientGroup.mk' (modPFrattini p ((G × H) × K)) ((a, b), c)) := rfl

/-- Packaged additive triangle coherence for the associator with a trivial middle
factor.  This is the equivalence-valued form of
`mapadd_prodassoc_trivialtriangle`. -/
theorem mFAdditi.prodassoc_addequiv_trivialtriangle
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_addequiv (p := p) G E H x) := by
  simpa using
    mFAdditi.mapadd_prodassoc_trivialtriangle (p := p) G E H x

/-- Packaged inverse additive triangle coherence for the associator with a
trivial middle factor. -/
theorem mFAdditi.prodassoc_addequiv_symmtrivtria
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × E × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
        ((mFAdditi.prod_assoc_addequiv (p := p) G E H).symm x) := by
  simpa using
    mFAdditi.mapadd_prodassoc_symmtrivtria (p := p) G E H x

/-- Packaged linear triangle coherence for the associator with a trivial middle
factor. -/
theorem mFAdditi.prodassoc_linequiv_trivialtriangle [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_linequiv (p := p) G E H x) := by
  simpa using
    mFAdditi.maplin_prodassoc_trivialtriangle (p := p) G E H x

/-- Packaged inverse linear triangle coherence for the associator with a trivial
middle factor. -/
theorem mFAdditi.prodassoc_linequiv_symmtrivtria [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × E × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H))
        ((mFAdditi.prod_assoc_linequiv (p := p) G E H).symm x) := by
  simpa using
    mFAdditi.maplin_prodassoc_symmtrivtria (p := p) G E H x

/-- Additive product coordinates for deleting a trivial middle factor before
reassociating. -/
theorem mFAdditi.prodadd_equivdelete_middleleft
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodAddEquiv (p := p) G H
      (mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x) =
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E
        ((mFAdditi.prodAddEquiv (p := p) (G × E) H x).1),
      (mFAdditi.prodAddEquiv (p := p) (G × E) H x).2) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  rfl

/-- Additive product coordinates for deleting a trivial middle factor after
reassociating. -/
theorem mFAdditi.prodadd_equivdelete_middleright
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodAddEquiv (p := p) G H
      (mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_addequiv (p := p) G E H x)) =
    ((mFAdditi.prodAddEquiv (p := p) G (E × H)
        (mFAdditi.prod_assoc_addequiv (p := p) G E H x)).1,
      mFAdditi.prod_lefttrivial_addequiv (p := p) E H
        ((mFAdditi.prodAddEquiv (p := p) G (E × H)
          (mFAdditi.prod_assoc_addequiv (p := p) G E H x)).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  rfl

/-- Linear product coordinates for deleting a trivial middle factor before
reassociating. -/
theorem mFAdditi.prodlin_equivdelete_middleleft [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodLinearEquiv (p := p) G H
      (mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.fst G E) (MonoidHom.id H)) x) =
    (mFAdditi.prod_righttrivial_linequiv (p := p) G E
        ((mFAdditi.prodLinearEquiv (p := p) (G × E) H x).1),
      (mFAdditi.prodLinearEquiv (p := p) (G × E) H x).2) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  rfl

/-- Linear product coordinates for deleting a trivial middle factor after
reassociating. -/
theorem mFAdditi.prodlin_equivdelete_middleright [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodLinearEquiv (p := p) G H
      (mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_linequiv (p := p) G E H x)) =
    ((mFAdditi.prodLinearEquiv (p := p) G (E × H)
        (mFAdditi.prod_assoc_linequiv (p := p) G E H x)).1,
      mFAdditi.prod_lefttrivial_linequiv (p := p) E H
        ((mFAdditi.prodLinearEquiv (p := p) G (E × H)
          (mFAdditi.prod_assoc_linequiv (p := p) G E H x)).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨ge, h⟩
  rcases ge with ⟨g, e⟩
  rfl

/-- Additive middle deletion agrees with reassociating and deleting the left
factor of `E × H`. -/
theorem mFAdditi.prodmiddle_trivialadd_equivassoc
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prod_middletrivial_addequiv (p := p) G E H x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_addequiv (p := p) G E H x) := by
  simpa using
    mFAdditi.prodassoc_addequiv_trivialtriangle (p := p) G E H x

/-- Inverse additive middle insertion via right insertion followed by inverse
associator. -/
theorem mFAdditi.prodmiddle_trivialadd_equivsymmassoc
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prod_middletrivial_addequiv (p := p) G E H).symm x =
      (mFAdditi.prod_assoc_addequiv (p := p) G E H).symm
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Linear middle deletion agrees with reassociating and deleting the left factor
of `E × H`. -/
theorem mFAdditi.prodmiddle_triviallin_equivassoc [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prod_middletrivial_linequiv (p := p) G E H x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
        (mFAdditi.prod_assoc_linequiv (p := p) G E H x) := by
  simpa using
    mFAdditi.prodassoc_linequiv_trivialtriangle (p := p) G E H x

/-- Inverse linear middle insertion via right insertion followed by inverse
associator. -/
theorem mFAdditi.prodmiddle_triviallin_equivsymmassoc [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prod_middletrivial_linequiv (p := p) G E H).symm x =
      (mFAdditi.prod_assoc_linequiv (p := p) G E H).symm
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl


/-- Additive equivalence deleting a trivial left factor inside a right-nested
product `G × (E × H)`. -/
noncomputable def mFAdditi.prodnested_lefttrivial_addequiv
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E] :
    mFAdditi p (G × (E × H)) ≃+
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
  invFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, eh⟩
    rcases eh with ⟨e, h⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prodnested_lefttrivial_addequivapply
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x := rfl

@[simp] theorem mFAdditi.prodnested_lefttrivialadd_equivsymmapply
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H)) x := rfl

@[simp] theorem mFAdditi.prodnested_lefttrivial_addequivmk
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (e : E) (h : H) :
    mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (E × H))) (g, (e, h)))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodnested_lefttrivialadd_equivsymmmk
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (E × H))) (g, (1, h))) := rfl

/-- The additive nested-left trivial equivalence is the reassociated form of the
middle-trivial equivalence. -/
theorem mFAdditi.prodnested_lefttrivial_addequivassoc
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H
        (mFAdditi.prod_assoc_addequiv (p := p) G E H x) =
      mFAdditi.prod_middletrivial_addequiv (p := p) G E H x := by
  symm
  exact mFAdditi.prodmiddle_trivialadd_equivassoc (p := p) G E H x

/-- Inverse nested-left insertion is middle insertion followed by reassociation. -/
theorem mFAdditi.prodnested_lefttrivialadd_equivsymmassoc
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm x =
      mFAdditi.prod_assoc_addequiv (p := p) G E H
        ((mFAdditi.prod_middletrivial_addequiv (p := p) G E H).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Linear equivalence deleting a trivial left factor inside a right-nested
product `G × (E × H)`. -/
noncomputable def mFAdditi.prodnested_lefttrivial_linequiv [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E] :
    mFAdditi p (G × (E × H)) ≃ₗ[ZMod p]
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H))
  invFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, eh⟩
    rcases eh with ⟨e, h⟩
    have he : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prodnested_lefttrivial_linequivapply [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.snd E H)) x := rfl

@[simp] theorem mFAdditi.prodnested_lefttriviallin_equivsymmapply
    [Fact p.Prime] (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inr E H)) x := rfl

@[simp] theorem mFAdditi.prodnested_lefttrivial_linequivmk [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (e : E) (h : H) :
    mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (E × H))) (g, (e, h)))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodnested_lefttriviallin_equivsymmmk
    [Fact p.Prime] (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (E × H))) (g, (1, h))) := rfl

/-- The linear nested-left trivial equivalence is the reassociated form of the
middle-trivial equivalence. -/
theorem mFAdditi.prodnested_lefttrivial_linequivassoc [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p ((G × E) × H)) :
    mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H
        (mFAdditi.prod_assoc_linequiv (p := p) G E H x) =
      mFAdditi.prod_middletrivial_linequiv (p := p) G E H x := by
  symm
  exact mFAdditi.prodmiddle_triviallin_equivassoc (p := p) G E H x

/-- Inverse linear nested-left insertion is middle insertion followed by reassociation. -/
theorem mFAdditi.prodnested_lefttriviallin_equivsymmassoc [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm x =
      mFAdditi.prod_assoc_linequiv (p := p) G E H
        ((mFAdditi.prod_middletrivial_linequiv (p := p) G E H).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Naturality of the additive nested-left trivial equivalence. -/
theorem mFAdditi.prodnested_lefttrivial_addequivnatural
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × (E₁ × H₁))) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G₁ E₁ H₁ x) =
      mFAdditi.prodnested_lefttrivial_addequiv (p := p) G₂ E₂ H₂
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap e h)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, ek⟩
  rcases ek with ⟨u, k⟩
  rfl

/-- Naturality of the inverse additive nested-left trivial equivalence. -/
theorem mFAdditi.prodnested_lefttrivialadd_equisymmnatu
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap f (MonoidHom.prodMap e h))
        ((mFAdditi.prodnested_lefttrivial_addequiv (p := p) G₁ E₁ H₁).symm x) =
      (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G₂ E₂ H₂).symm
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, k⟩
  change Additive.ofMul (mFQuot.mk p (G₂ × (E₂ × H₂))
      (f g, (e 1, h k))) =
    Additive.ofMul (mFQuot.mk p (G₂ × (E₂ × H₂))
      (f g, (1, h k)))
  rw [map_one]

/-- Naturality of the linear nested-left trivial equivalence. -/
theorem mFAdditi.prodnested_lefttrivial_linequivnatural [Fact p.Prime]
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × (E₁ × H₁))) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G₁ E₁ H₁ x) =
      mFAdditi.prodnested_lefttrivial_linequiv (p := p) G₂ E₂ H₂
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap e h)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, ek⟩
  rcases ek with ⟨u, k⟩
  rfl

/-- Naturality of the inverse linear nested-left trivial equivalence. -/
theorem mFAdditi.prodnested_lefttriviallin_equisymmnatu
    [Fact p.Prime]
    {G₁ G₂ E₁ E₂ H₁ H₂ : Type*}
    [Group G₁] [Group G₂] [Group E₁] [Group E₂] [Group H₁] [Group H₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (e : E₁ →* E₂) (h : H₁ →* H₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap f (MonoidHom.prodMap e h))
        ((mFAdditi.prodnested_lefttrivial_linequiv (p := p) G₁ E₁ H₁).symm x) =
      (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G₂ E₂ H₂).symm
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, k⟩
  change Additive.ofMul (mFQuot.mk p (G₂ × (E₂ × H₂))
      (f g, (e 1, h k))) =
    Additive.ofMul (mFQuot.mk p (G₂ × (E₂ × H₂))
      (f g, (1, h k)))
  rw [map_one]

/-- Additive equivalence deleting a trivial right factor inside a right-nested
product `G × (H × E)`. -/
noncomputable def mFAdditi.prodnested_righttrivial_addequiv
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E] :
    mFAdditi p (G × (H × E)) ≃+
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.fst H E))
  invFun := mFAdditi.mapAdd (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inl H E))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, he⟩
    rcases he with ⟨h, e⟩
    have heq : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y }

@[simp] theorem mFAdditi.prodnested_righttrivial_addequivapply
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.fst H E)) x := rfl

@[simp] theorem mFAdditi.prodnested_righttrivialadd_equivsymmapply
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm x =
      mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inl H E)) x := rfl

@[simp] theorem mFAdditi.prodnested_righttrivial_addequivmk
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (g : G) (h : H) (e : E) :
    mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (H × E))) (g, (h, e)))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodnested_righttrivialadd_equivsymmmk
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (H × E))) (g, (h, 1))) := rfl

/-- The additive nested-right trivial equivalence is inverse reassociation followed
by the right-trivial equivalence. -/
theorem mFAdditi.prodnested_righttrivialadd_equivassocsymm
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E x =
      mFAdditi.prod_righttrivial_addequiv (p := p) (G × H) E
        ((mFAdditi.prod_assoc_addequiv (p := p) G H E).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl

/-- Inverse nested-right insertion is right insertion followed by reassociation. -/
theorem mFAdditi.prodnested_righttrivialadd_equivsymmassoc
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm x =
      mFAdditi.prod_assoc_addequiv (p := p) G H E
        ((mFAdditi.prod_righttrivial_addequiv (p := p) (G × H) E).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Naturality of the additive nested-right trivial equivalence. -/
theorem mFAdditi.prodnested_righttrivial_addequivnatural
    {G₁ G₂ H₁ H₂ E₁ E₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (h : H₁ →* H₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × (H₁ × E₁))) :
    mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prodnested_righttrivial_addequiv (p := p) G₁ H₁ E₁ x) =
      mFAdditi.prodnested_righttrivial_addequiv (p := p) G₂ H₂ E₂
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap h e)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, hk⟩
  rcases hk with ⟨u, k⟩
  rfl

/-- Naturality of the inverse additive nested-right trivial equivalence. -/
theorem mFAdditi.prodnested_righttrivialadd_equisymmnatu
    {G₁ G₂ H₁ H₂ E₁ E₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (h : H₁ →* H₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap f (MonoidHom.prodMap h e))
        ((mFAdditi.prodnested_righttrivial_addequiv (p := p) G₁ H₁ E₁).symm x) =
      (mFAdditi.prodnested_righttrivial_addequiv (p := p) G₂ H₂ E₂).symm
        (mFAdditi.mapAdd (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, u⟩
  change Additive.ofMul (mFQuot.mk p (G₂ × (H₂ × E₂))
      (f g, (h u, e 1))) =
    Additive.ofMul (mFQuot.mk p (G₂ × (H₂ × E₂))
      (f g, (h u, 1)))
  rw [map_one]

/-- Linear equivalence deleting a trivial right factor inside a right-nested
product `G × (H × E)`. -/
noncomputable def mFAdditi.prodnested_righttrivial_linequiv [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E] :
    mFAdditi p (G × (H × E)) ≃ₗ[ZMod p]
      mFAdditi p (G × H) :=
{ toFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.fst H E))
  invFun := mFAdditi.mapLinear (p := p)
    (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inl H E))
  left_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, he⟩
    rcases he with ⟨h, e⟩
    have heq : e = 1 := Subsingleton.elim e 1
    subst e
    rfl
  right_inv := by
    intro x
    cases x using Additive.rec
    rename_i q
    refine QuotientGroup.induction_on q ?_
    intro a
    rcases a with ⟨g, h⟩
    rfl
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact map_smul _ c x }

@[simp] theorem mFAdditi.prodnested_righttrivial_linequivapply [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.fst H E)) x := rfl

@[simp] theorem mFAdditi.prodnested_righttriviallin_equivsymmapply [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm x =
      mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G) (MonoidHom.inl H E)) x := rfl

@[simp] theorem mFAdditi.prodnested_righttrivial_linequivmk [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (g : G) (h : H) (e : E) :
    mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (H × E))) (g, (h, e)))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h)) := rfl

@[simp] theorem mFAdditi.prodnested_righttriviallin_equivsymmmk [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (g : G) (h : H) :
    (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm
      (Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × H)) (g, h))) =
    Additive.ofMul (QuotientGroup.mk' (modPFrattini p (G × (H × E))) (g, (h, 1))) := rfl

/-- The linear nested-right trivial equivalence is inverse reassociation followed
by the right-trivial equivalence. -/
theorem mFAdditi.prodnested_righttriviallin_equivassocsymm [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E x =
      mFAdditi.prod_righttrivial_linequiv (p := p) (G × H) E
        ((mFAdditi.prod_assoc_linequiv (p := p) G H E).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl

/-- Inverse linear nested-right insertion is right insertion followed by reassociation. -/
theorem mFAdditi.prodnested_righttriviallin_equivsymmassoc [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm x =
      mFAdditi.prod_assoc_linequiv (p := p) G H E
        ((mFAdditi.prod_righttrivial_linequiv (p := p) (G × H) E).symm x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Naturality of the linear nested-right trivial equivalence. -/
theorem mFAdditi.prodnested_righttrivial_linequivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ E₁ E₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (h : H₁ →* H₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × (H₁ × E₁))) :
    mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h)
        (mFAdditi.prodnested_righttrivial_linequiv (p := p) G₁ H₁ E₁ x) =
      mFAdditi.prodnested_righttrivial_linequiv (p := p) G₂ H₂ E₂
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap f (MonoidHom.prodMap h e)) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, hk⟩
  rcases hk with ⟨u, k⟩
  rfl

/-- Naturality of the inverse linear nested-right trivial equivalence. -/
theorem mFAdditi.prodnested_righttriviallin_equisymmnatu [Fact p.Prime]
    {G₁ G₂ H₁ H₂ E₁ E₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group E₁] [Group E₂]
    [Subsingleton E₁] [Subsingleton E₂]
    (f : G₁ →* G₂) (h : H₁ →* H₂) (e : E₁ →* E₂)
    (x : mFAdditi p (G₁ × H₁)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap f (MonoidHom.prodMap h e))
        ((mFAdditi.prodnested_righttrivial_linequiv (p := p) G₁ H₁ E₁).symm x) =
      (mFAdditi.prodnested_righttrivial_linequiv (p := p) G₂ H₂ E₂).symm
        (mFAdditi.mapLinear (p := p) (MonoidHom.prodMap f h) x) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, u⟩
  change Additive.ofMul (mFQuot.mk p (G₂ × (H₂ × E₂))
      (f g, (h u, e 1))) =
    Additive.ofMul (mFQuot.mk p (G₂ × (H₂ × E₂))
      (f g, (h u, 1)))
  rw [map_one]



/-- Additive product coordinates for deleting a trivial left factor inside a
right-nested product. -/
theorem mFAdditi.prodadd_equivnested_lefttrivial
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodAddEquiv (p := p) G H
        (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H x) =
      ((mFAdditi.prodAddEquiv (p := p) G (E × H) x).1,
        mFAdditi.prod_lefttrivial_addequiv (p := p) E H
          ((mFAdditi.prodAddEquiv (p := p) G (E × H) x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  rfl

/-- Linear product coordinates for deleting a trivial left factor inside a
right-nested product. -/
theorem mFAdditi.prodlin_equivnested_lefttrivial [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodLinearEquiv (p := p) G H
        (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H x) =
      ((mFAdditi.prodLinearEquiv (p := p) G (E × H) x).1,
        mFAdditi.prod_lefttrivial_linequiv (p := p) E H
          ((mFAdditi.prodLinearEquiv (p := p) G (E × H) x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  rfl

/-- Additive product coordinates for deleting a trivial right factor inside a
right-nested product. -/
theorem mFAdditi.prodadd_equivnested_righttrivial
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodAddEquiv (p := p) G H
        (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E x) =
      ((mFAdditi.prodAddEquiv (p := p) G (H × E) x).1,
        mFAdditi.prod_righttrivial_addequiv (p := p) H E
          ((mFAdditi.prodAddEquiv (p := p) G (H × E) x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl

/-- Linear product coordinates for deleting a trivial right factor inside a
right-nested product. -/
theorem mFAdditi.prodlin_equivnested_righttrivial [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodLinearEquiv (p := p) G H
        (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E x) =
      ((mFAdditi.prodLinearEquiv (p := p) G (H × E) x).1,
        mFAdditi.prod_righttrivial_linequiv (p := p) H E
          ((mFAdditi.prodLinearEquiv (p := p) G (H × E) x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl


/-- Additive product coordinates for inserting a trivial left factor inside a
right-nested product. -/
theorem mFAdditi.prodadd_equivnested_lefttrivialsymm
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodAddEquiv (p := p) G (E × H)
        ((mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm x) =
      ((mFAdditi.prodAddEquiv (p := p) G H x).1,
        (mFAdditi.prod_lefttrivial_addequiv (p := p) E H).symm
          ((mFAdditi.prodAddEquiv (p := p) G H x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Linear product coordinates for inserting a trivial left factor inside a
right-nested product. -/
theorem mFAdditi.prodlin_equivnested_lefttrivialsymm [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodLinearEquiv (p := p) G (E × H)
        ((mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm x) =
      ((mFAdditi.prodLinearEquiv (p := p) G H x).1,
        (mFAdditi.prod_lefttrivial_linequiv (p := p) E H).symm
          ((mFAdditi.prodLinearEquiv (p := p) G H x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Additive product coordinates for inserting a trivial right factor inside a
right-nested product. -/
theorem mFAdditi.prodadd_equivnested_rightrivsymm
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodAddEquiv (p := p) G (H × E)
        ((mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm x) =
      ((mFAdditi.prodAddEquiv (p := p) G H x).1,
        (mFAdditi.prod_righttrivial_addequiv (p := p) H E).symm
          ((mFAdditi.prodAddEquiv (p := p) G H x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Linear product coordinates for inserting a trivial right factor inside a
right-nested product. -/
theorem mFAdditi.prodlin_equivnested_rightrivsymm [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.prodLinearEquiv (p := p) G (H × E)
        ((mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm x) =
      ((mFAdditi.prodLinearEquiv (p := p) G H x).1,
        (mFAdditi.prod_righttrivial_linequiv (p := p) H E).symm
          ((mFAdditi.prodLinearEquiv (p := p) G H x).2)) := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl


/-- Swapping the inner factors turns additive nested-left deletion into nested-right deletion. -/
theorem mFAdditi.prodnested_trivialadd_equivinnerswap
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := E) (N := H)).toMonoidHom) x) =
      mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  rfl

/-- Swapping the inner factors turns linear nested-left deletion into nested-right deletion. -/
theorem mFAdditi.prodnested_triviallin_equivinnerswap [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × (E × H))) :
    mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := E) (N := H)).toMonoidHom) x) =
      mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, eh⟩
  rcases eh with ⟨e, h⟩
  rfl


/-- Inner swap identifies inverse additive nested-left and nested-right insertions. -/
theorem mFAdditi.prodnested_trivialaddequiv_symminnerswap
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := E) (N := H)).toMonoidHom)
        ((mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm x) =
      (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Inner swap identifies inverse linear nested-left and nested-right insertions. -/
theorem mFAdditi.prodnested_triviallinequiv_symminnerswap [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := E) (N := H)).toMonoidHom)
        ((mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm x) =
      (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl


/-- Reverse inner-swap form of additive nested-left/right deletion coherence. -/
theorem mFAdditi.prodnested_trivialaddequiv_innerswaprev
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H
        (mFAdditi.mapAdd (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := H) (N := E)).toMonoidHom) x) =
      mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl

/-- Reverse inner-swap form of linear nested-left/right deletion coherence. -/
theorem mFAdditi.prodnested_triviallinequiv_innerswaprev [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × (H × E))) :
    mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H
        (mFAdditi.mapLinear (p := p)
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := H) (N := E)).toMonoidHom) x) =
      mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, he⟩
  rcases he with ⟨h, e⟩
  rfl


/-- Reverse inner swap identifies inverse additive nested-right and nested-left insertions. -/
theorem mFAdditi.prodnesttriv_addequivsymm_innerswaprev
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapAdd (p := p)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := H) (N := E)).toMonoidHom)
        ((mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm x) =
      (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl

/-- Reverse inner swap identifies inverse linear nested-right and nested-left insertions. -/
theorem mFAdditi.prodnesttriv_linequivsymm_innerswaprev [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    (x : mFAdditi p (G × H)) :
    mFAdditi.mapLinear (p := p)
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := H) (N := E)).toMonoidHom)
        ((mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm x) =
      (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm x := by
  cases x using Additive.rec
  rename_i q
  refine QuotientGroup.induction_on q ?_
  intro a
  rcases a with ⟨g, h⟩
  rfl


/-- Finite-dimensionality is unchanged by adjoining a trivial right factor. -/
theorem module_additive_trivial [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Module.Finite (ZMod p) (mFAdditi p (G × E)) := by
  exact Module.Finite.equiv
    (mFAdditi.prod_righttrivial_linequiv (p := p) G E).symm

/-- Finite-dimensionality is unchanged by adjoining a trivial left factor. -/
theorem module_mod_trivial [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Module.Finite (ZMod p) (mFAdditi p (E × G)) := by
  exact Module.Finite.equiv
    (mFAdditi.prod_lefttrivial_linequiv (p := p) E G).symm

/-- Finrank is unchanged by adjoining a trivial right factor. -/
theorem finrank_mod_trivial [Fact p.Prime]
    (G E : Type*) [Group G] [Group E] [Subsingleton E] :
    Module.finrank (ZMod p) (mFAdditi p (G × E)) =
      Module.finrank (ZMod p) (mFAdditi p G) := by
  exact (mFAdditi.prod_righttrivial_linequiv (p := p) G E).finrank_eq

/-- Finrank is unchanged by adjoining a trivial left factor. -/
theorem finrank_p_trivial [Fact p.Prime]
    (E G : Type*) [Group E] [Group G] [Subsingleton E] :
    Module.finrank (ZMod p) (mFAdditi p (E × G)) =
      Module.finrank (ZMod p) (mFAdditi p G) := by
  exact (mFAdditi.prod_lefttrivial_linequiv (p := p) E G).finrank_eq


/-- Finite-dimensionality is unchanged by inserting a trivial left factor inside
a right-nested product. -/
theorem module_frattini_trivial [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p (G × H))] :
    Module.Finite (ZMod p) (mFAdditi p (G × (E × H))) := by
  exact Module.Finite.equiv
    (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).symm

/-- Finite-dimensionality is unchanged by inserting a trivial right factor inside
a right-nested product. -/
theorem module_nested_trivial [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p (G × H))] :
    Module.Finite (ZMod p) (mFAdditi p (G × (H × E))) := by
  exact Module.Finite.equiv
    (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).symm

/-- Finrank is unchanged by deleting a trivial left factor inside a right-nested product. -/
theorem finrank_additive_trivial [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E] :
    Module.finrank (ZMod p) (mFAdditi p (G × (E × H))) =
      Module.finrank (ZMod p) (mFAdditi p (G × H)) := by
  exact (mFAdditi.prodnested_lefttrivial_linequiv (p := p) G E H).finrank_eq

/-- Finrank is unchanged by deleting a trivial right factor inside a right-nested product. -/
theorem finrank_frattini_trivial [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E] :
    Module.finrank (ZMod p) (mFAdditi p (G × (H × E))) =
      Module.finrank (ZMod p) (mFAdditi p (G × H)) := by
  exact (mFAdditi.prodnested_righttrivial_linequiv (p := p) G H E).finrank_eq




/-- A subsingleton group has zero-dimensional mod-`p` Frattini quotient. -/
theorem finrank_additive_subsingleton [Fact p.Prime]
    (E : Type*) [Group E] [Subsingleton E] :
    Module.finrank (ZMod p) (mFAdditi p E) = 0 := by
  exact Module.finrank_zero_of_subsingleton

/-- Finite-dimensionality transports across swapping product factors. -/
theorem module_frattini_comm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    [Module.Finite (ZMod p) (mFAdditi p (G × H))] :
    Module.Finite (ZMod p) (mFAdditi p (H × G)) := by
  exact Module.Finite.equiv (mFAdditi.prod_comm_linequiv (p := p) G H)

/-- Finite-dimensionality transports across reassociating product factors. -/
theorem module_frattini_assoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p ((G × H) × K))] :
    Module.Finite (ZMod p) (mFAdditi p (G × (H × K))) := by
  exact Module.Finite.equiv (mFAdditi.prod_assoc_linequiv (p := p) G H K)

/-- Finite-dimensionality transports across inverse reassociation. -/
theorem module_assoc_symm [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p (G × (H × K)))] :
    Module.Finite (ZMod p) (mFAdditi p ((G × H) × K)) := by
  exact Module.Finite.equiv (mFAdditi.prod_assoc_linequiv (p := p) G H K).symm

/-- Finrank is invariant under swapping product factors. -/
theorem finrank_frattini_comm [Fact p.Prime]
    (G H : Type*) [Group G] [Group H] :
    Module.finrank (ZMod p) (mFAdditi p (G × H)) =
      Module.finrank (ZMod p) (mFAdditi p (H × G)) := by
  exact (mFAdditi.prod_comm_linequiv (p := p) G H).finrank_eq

/-- Finrank is invariant under reassociating three product factors. -/
theorem finrank_frattini_assoc [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K] :
    Module.finrank (ZMod p) (mFAdditi p ((G × H) × K)) =
      Module.finrank (ZMod p) (mFAdditi p (G × (H × K))) := by
  exact (mFAdditi.prod_assoc_linequiv (p := p) G H K).finrank_eq

/-- Finite-dimensionality of mod-`p` Frattini quotients is preserved by binary
products when both factors are finite-dimensional. -/
theorem module_mod_prod [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Module.Finite (ZMod p) (mFAdditi p (G × H)) := by
  exact Module.Finite.equiv (mFAdditi.prodLinearEquiv (p := p) G H).symm

/-- Finite `ZMod p`-rank is additive under direct products of mod-`p` Frattini
quotients. -/
theorem finrank_frattini_additive [Fact p.Prime]
    (G H : Type*) [Group G] [Group H]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Module.finrank (ZMod p) (mFAdditi p (G × H)) =
      Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) := by
  let e := mFAdditi.prodLinearEquiv (p := p) G H
  haveI : Module.Finite (ZMod p) (mFAdditi p (G × H)) :=
    Module.Finite.equiv e.symm
  calc
    Module.finrank (ZMod p) (mFAdditi p (G × H)) =
        Module.finrank (ZMod p)
          (mFAdditi p G × mFAdditi p H) := e.finrank_eq
    _ = Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) := by
          rw [Module.finrank_prod]


/-- Finrank of a right-nested product with a trivial middle factor is the sum
of the nontrivial factors. -/
theorem finrank_trivial_sum [Fact p.Prime]
    (G E H : Type*) [Group G] [Group E] [Group H] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Module.finrank (ZMod p) (mFAdditi p (G × (E × H))) =
      Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) := by
  calc
    Module.finrank (ZMod p) (mFAdditi p (G × (E × H))) =
        Module.finrank (ZMod p) (mFAdditi p (G × H)) :=
          finrank_additive_trivial (p := p) G E H
    _ = Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) :=
          finrank_frattini_additive (p := p) G H

/-- Finrank of a right-nested product with a trivial right factor is the sum
of the nontrivial factors. -/
theorem finrank_nested_trivial [Fact p.Prime]
    (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Module.finrank (ZMod p) (mFAdditi p (G × (H × E))) =
      Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) := by
  calc
    Module.finrank (ZMod p) (mFAdditi p (G × (H × E))) =
        Module.finrank (ZMod p) (mFAdditi p (G × H)) :=
          finrank_frattini_trivial (p := p) G H E
    _ = Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H) :=
          finrank_frattini_additive (p := p) G H

/-- Finite-dimensionality for a left-associated triple product. -/
theorem module_additive_prod [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)]
    [Module.Finite (ZMod p) (mFAdditi p K)] :
    Module.Finite (ZMod p) (mFAdditi p ((G × H) × K)) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (G × H)) :=
    module_mod_prod (p := p) G H
  exact module_mod_prod (p := p) (G × H) K

/-- Finite-dimensionality for a right-associated triple product. -/
theorem module_frattini_nested [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)]
    [Module.Finite (ZMod p) (mFAdditi p K)] :
    Module.Finite (ZMod p) (mFAdditi p (G × (H × K))) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (H × K)) :=
    module_mod_prod (p := p) H K
  exact module_mod_prod (p := p) G (H × K)

/-- Finrank of a left-associated triple product is the sum of the three factors. -/
theorem finrank_additive_prod [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)]
    [Module.Finite (ZMod p) (mFAdditi p K)] :
    Module.finrank (ZMod p) (mFAdditi p ((G × H) × K)) =
      (Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H)) +
        Module.finrank (ZMod p) (mFAdditi p K) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (G × H)) :=
    module_mod_prod (p := p) G H
  calc
    Module.finrank (ZMod p) (mFAdditi p ((G × H) × K)) =
        Module.finrank (ZMod p) (mFAdditi p (G × H)) +
          Module.finrank (ZMod p) (mFAdditi p K) :=
            finrank_frattini_additive (p := p) (G × H) K
    _ = (Module.finrank (ZMod p) (mFAdditi p G) +
          Module.finrank (ZMod p) (mFAdditi p H)) +
          Module.finrank (ZMod p) (mFAdditi p K) := by
            rw [finrank_frattini_additive (p := p) G H]

/-- Finrank of a right-associated triple product is the sum of the three factors. -/
theorem finrank_frattini_nested [Fact p.Prime]
    (G H K : Type*) [Group G] [Group H] [Group K]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)]
    [Module.Finite (ZMod p) (mFAdditi p K)] :
    Module.finrank (ZMod p) (mFAdditi p (G × (H × K))) =
      Module.finrank (ZMod p) (mFAdditi p G) +
        (Module.finrank (ZMod p) (mFAdditi p H) +
          Module.finrank (ZMod p) (mFAdditi p K)) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (H × K)) :=
    module_mod_prod (p := p) H K
  calc
    Module.finrank (ZMod p) (mFAdditi p (G × (H × K))) =
        Module.finrank (ZMod p) (mFAdditi p G) +
          Module.finrank (ZMod p) (mFAdditi p (H × K)) :=
            finrank_frattini_additive (p := p) G (H × K)
    _ = Module.finrank (ZMod p) (mFAdditi p G) +
        (Module.finrank (ZMod p) (mFAdditi p H) +
          Module.finrank (ZMod p) (mFAdditi p K)) := by
            rw [finrank_frattini_additive (p := p) H K]

end Submission

namespace Submission

variable (p : ℕ) {G H : Type*} [Group G] [Group H]


/-- Finite-dimensionality transports forward along a surjection with Frattini-contained kernel. -/
theorem module_frattini_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Module.Finite (ZMod p) (mFAdditi p H) := by
  exact Module.Finite.equiv
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker)

/-- Finite-dimensionality transports backward along a surjection with Frattini-contained kernel. -/
theorem module_frattini_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Module.Finite (ZMod p) (mFAdditi p G) := by
  exact Module.Finite.equiv
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).symm

/-- Finrank is preserved by a surjection with Frattini-contained kernel. -/
theorem finrank_additive_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    Module.finrank (ZMod p) (mFAdditi p G) =
      Module.finrank (ZMod p) (mFAdditi p H) := by
  exact (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).finrank_eq

/-- The linear Frattini map attached to a suitable surjection has trivial kernel. -/
theorem mFAdditi.maplin_kereqbot_surjkerle
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    LinearMap.ker (mFAdditi.mapLinear (p := p) f) = ⊥ := by
  rw [← mFAdditi.linequiv_surjker_lelinmap
    (p := p) f hs hker]
  exact LinearMap.ker_eq_bot_of_injective
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).injective

/-- The linear Frattini map attached to a suitable surjection has full range. -/
theorem mFAdditi.maplin_rangeeqtop_surjkerle
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    LinearMap.range (mFAdditi.mapLinear (p := p) f) = ⊤ := by
  rw [← mFAdditi.linequiv_surjker_lelinmap
    (p := p) f hs hker]
  exact LinearMap.range_eq_top_of_surjective _
    (mFAdditi.lin_equivsurj_kerle (p := p) f hs hker).surjective

end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H]

/-- Additive type-synonym version of multiplicativity of `Nat.card` for Frattini quotients. -/
theorem mod_frattini_additive :
    Nat.card (mFAdditi p (G × H)) =
      Nat.card (mFAdditi p G) * Nat.card (mFAdditi p H) := by
  calc
    Nat.card (mFAdditi p (G × H)) =
        Nat.card (mFAdditi p G × mFAdditi p H) :=
      Nat.card_congr (mFAdditi.prodAddEquiv (p := p) G H).toEquiv
    _ = _ := Nat.card_prod _ _

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (E : Type*) [Group E] [Subsingleton E]

/-- Canonical fintype structure on the Frattini quotient of a subsingleton group. -/
@[reducible] noncomputable def fintype_p_subsingleton :
    Fintype (mFQuot p E) :=
  Fintype.ofSubsingleton (1 : mFQuot p E)

/-- Canonical fintype structure on the additive Frattini quotient of a subsingleton group. -/
@[reducible] noncomputable def fintype_mod_subsingleton :
    Fintype (mFAdditi p E) :=
  Fintype.ofSubsingleton (0 : mFAdditi p E)

/-- The canonical fintype on a subsingleton multiplicative quotient has cardinality one. -/
theorem fintype_frattini_subsingleton :
    @Fintype.card (mFQuot p E)
        (fintype_p_subsingleton p E) = 1 := by
  exact Fintype.card_ofSubsingleton (1 : mFQuot p E)

/-- The canonical fintype on a subsingleton additive quotient has cardinality one. -/
theorem fintype_additive_subsingleton :
    @Fintype.card (mFAdditi p E)
        (fintype_mod_subsingleton p E) = 1 := by
  exact Fintype.card_ofSubsingleton (0 : mFAdditi p E)

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K]

/-- Transport a fintype structure across the product-commuting equivalence (multiplicative
Frattini quotient).  This is useful when the product quotient is already known finite without
choosing fintypes on the two factors separately. -/
@[reducible] noncomputable def frattini_prod_comm
    [Fintype (mFQuot p (G × H))] :
    Fintype (mFQuot p (H × G)) := by
  exact Fintype.ofEquiv (mFQuot p (G × H))
    (mFQuot.prodCommEquiv (p := p) G H).toEquiv

/-- Transport a fintype structure across the product-commuting equivalence (additive
Frattini quotient). -/
@[reducible] noncomputable def mod_frattini_comm
    [Fintype (mFAdditi p (G × H))] :
    Fintype (mFAdditi p (H × G)) := by
  exact Fintype.ofEquiv (mFAdditi p (G × H))
    (mFAdditi.prod_comm_addequiv (p := p) G H).toEquiv

/-- Transport a fintype structure across reassociation (multiplicative quotient). -/
@[reducible] noncomputable def frattini_prod_assoc
    [Fintype (mFQuot p ((G × H) × K))] :
    Fintype (mFQuot p (G × (H × K))) := by
  exact Fintype.ofEquiv (mFQuot p ((G × H) × K))
    (mFQuot.prodAssocEquiv (p := p) G H K).toEquiv

/-- Transport a fintype structure across reassociation (additive quotient). -/
@[reducible] noncomputable def mod_frattini_assoc
    [Fintype (mFAdditi p ((G × H) × K))] :
    Fintype (mFAdditi p (G × (H × K))) := by
  exact Fintype.ofEquiv (mFAdditi p ((G × H) × K))
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).toEquiv

/-- Cardinality is preserved by the transported product-commuting multiplicative fintype. -/
theorem p_frattini_comm
    [Fintype (mFQuot p (G × H))] :
    @Fintype.card (mFQuot p (H × G))
        (frattini_prod_comm p G H) =
      Fintype.card (mFQuot p (G × H)) := by
  letI : Fintype (mFQuot p (H × G)) :=
    frattini_prod_comm p G H
  exact (Fintype.card_congr
    (mFQuot.prodCommEquiv (p := p) G H).toEquiv).symm

/-- Cardinality is preserved by the transported product-commuting additive fintype. -/
theorem fintype_p_comm
    [Fintype (mFAdditi p (G × H))] :
    @Fintype.card (mFAdditi p (H × G))
        (mod_frattini_comm p G H) =
      Fintype.card (mFAdditi p (G × H)) := by
  letI : Fintype (mFAdditi p (H × G)) :=
    mod_frattini_comm p G H
  exact (Fintype.card_congr
    (mFAdditi.prod_comm_addequiv (p := p) G H).toEquiv).symm

/-- Cardinality is preserved by the transported reassociation multiplicative fintype. -/
theorem p_frattini_assoc
    [Fintype (mFQuot p ((G × H) × K))] :
    @Fintype.card (mFQuot p (G × (H × K)))
        (frattini_prod_assoc p G H K) =
      Fintype.card (mFQuot p ((G × H) × K)) := by
  letI : Fintype (mFQuot p (G × (H × K))) :=
    frattini_prod_assoc p G H K
  exact (Fintype.card_congr
    (mFQuot.prodAssocEquiv (p := p) G H K).toEquiv).symm

/-- Cardinality is preserved by the transported reassociation additive fintype. -/
theorem fintype_p_assoc
    [Fintype (mFAdditi p ((G × H) × K))] :
    @Fintype.card (mFAdditi p (G × (H × K)))
        (mod_frattini_assoc p G H K) =
      Fintype.card (mFAdditi p ((G × H) × K)) := by
  letI : Fintype (mFAdditi p (G × (H × K))) :=
    mod_frattini_assoc p G H K
  exact (Fintype.card_congr
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).toEquiv).symm

/-- Transport a fintype structure backward across product commutation (multiplicative quotient). -/
@[reducible] noncomputable def fintype_mod_comm
    [Fintype (mFQuot p (H × G))] :
    Fintype (mFQuot p (G × H)) := by
  exact Fintype.ofEquiv (mFQuot p (H × G))
    (mFQuot.prodCommEquiv (p := p) G H).symm.toEquiv

/-- Transport a fintype structure backward across product commutation (additive quotient). -/
@[reducible] noncomputable def frattini_comm_symm
    [Fintype (mFAdditi p (H × G))] :
    Fintype (mFAdditi p (G × H)) := by
  exact Fintype.ofEquiv (mFAdditi p (H × G))
    (mFAdditi.prod_comm_addequiv (p := p) G H).symm.toEquiv

/-- Transport a fintype structure backward across reassociation (multiplicative quotient). -/
@[reducible] noncomputable def fintype_mod_assoc
    [Fintype (mFQuot p (G × (H × K)))] :
    Fintype (mFQuot p ((G × H) × K)) := by
  exact Fintype.ofEquiv (mFQuot p (G × (H × K)))
    (mFQuot.prodAssocEquiv (p := p) G H K).symm.toEquiv

/-- Transport a fintype structure backward across reassociation (additive quotient). -/
@[reducible] noncomputable def frattini_assoc_symm
    [Fintype (mFAdditi p (G × (H × K)))] :
    Fintype (mFAdditi p ((G × H) × K)) := by
  exact Fintype.ofEquiv (mFAdditi p (G × (H × K)))
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).symm.toEquiv

/-- Cardinality for backward transported product-commuting multiplicative fintypes. -/
theorem fintype_frattini_comm
    [Fintype (mFQuot p (H × G))] :
    @Fintype.card (mFQuot p (G × H))
        (fintype_mod_comm p G H) =
      Fintype.card (mFQuot p (H × G)) := by
  letI : Fintype (mFQuot p (G × H)) :=
    fintype_mod_comm p G H
  exact Fintype.card_congr
    (mFQuot.prodCommEquiv (p := p) G H).toEquiv

/-- Cardinality for backward transported product-commuting additive fintypes. -/
theorem fintype_comm_symm
    [Fintype (mFAdditi p (H × G))] :
    @Fintype.card (mFAdditi p (G × H))
        (frattini_comm_symm p G H) =
      Fintype.card (mFAdditi p (H × G)) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    frattini_comm_symm p G H
  exact Fintype.card_congr
    (mFAdditi.prod_comm_addequiv (p := p) G H).toEquiv

/-- Cardinality for backward transported reassociation multiplicative fintypes. -/
theorem fintype_frattini_assoc
    [Fintype (mFQuot p (G × (H × K)))] :
    @Fintype.card (mFQuot p ((G × H) × K))
        (fintype_mod_assoc p G H K) =
      Fintype.card (mFQuot p (G × (H × K))) := by
  letI : Fintype (mFQuot p ((G × H) × K)) :=
    fintype_mod_assoc p G H K
  exact Fintype.card_congr
    (mFQuot.prodAssocEquiv (p := p) G H K).toEquiv

/-- Cardinality for backward transported reassociation additive fintypes. -/
theorem fintype_assoc_symm
    [Fintype (mFAdditi p (G × (H × K)))] :
    @Fintype.card (mFAdditi p ((G × H) × K))
        (frattini_assoc_symm p G H K) =
      Fintype.card (mFAdditi p (G × (H × K))) := by
  letI : Fintype (mFAdditi p ((G × H) × K)) :=
    frattini_assoc_symm p G H K
  exact Fintype.card_congr
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).toEquiv


variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- `Nat.card` is preserved by a surjection whose kernel lies in the mod-`p` Frattini subgroup. -/
theorem nat_frattini_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    Nat.card (mFQuot p G) = Nat.card (mFQuot p H) := by
  exact Nat.card_congr
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv

/-- Additive version of `Nat.card` preservation for Frattini-contained-kernel surjections. -/
theorem frattini_additive_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G) :
    Nat.card (mFAdditi p G) = Nat.card (mFAdditi p H) := by
  exact Nat.card_congr
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- Finiteness of multiplicative Frattini quotients transports forward along a suitable
surjection. -/
theorem frattini_surjective_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Finite (mFQuot p G)] : Finite (mFQuot p H) := by
  exact Finite.of_equiv (mFQuot p G)
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv

/-- Finiteness of multiplicative Frattini quotients transports backward along a suitable
surjection. -/
theorem frattini_surjective_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Finite (mFQuot p H)] : Finite (mFQuot p G) := by
  exact Finite.of_equiv (mFQuot p H)
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv.symm

/-- Finiteness of additive Frattini quotients transports forward along a suitable surjection. -/
theorem additive_surjective_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Finite (mFAdditi p G)] : Finite (mFAdditi p H) := by
  exact Finite.of_equiv (mFAdditi p G)
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv

/-- Finiteness of additive Frattini quotients transports backward along a suitable surjection. -/
theorem frattini_additive_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Finite (mFAdditi p H)] : Finite (mFAdditi p G) := by
  exact Finite.of_equiv (mFAdditi p H)
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv.symm

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} (G H : Type*) [Group G] [Group H]

/-- If the Frattini quotient of a product is finite-dimensional, then so is its left factor. -/
theorem module_frattini_prod [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p (G × H))] :
    Module.Finite (ZMod p) (mFAdditi p G) := by
  let e := mFAdditi.prodLinearEquiv (p := p) G H
  haveI : Module.Finite (ZMod p)
      (mFAdditi p G × mFAdditi p H) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.fst (ZMod p) (mFAdditi p G) (mFAdditi p H))
    (by
      intro x
      exact ⟨(x, 0), rfl⟩)

/-- If the Frattini quotient of a product is finite-dimensional, then so is its right factor. -/
theorem module_frattini_additive [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p (G × H))] :
    Module.Finite (ZMod p) (mFAdditi p H) := by
  let e := mFAdditi.prodLinearEquiv (p := p) G H
  haveI : Module.Finite (ZMod p)
      (mFAdditi p G × mFAdditi p H) :=
    Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.snd (ZMod p) (mFAdditi p G) (mFAdditi p H))
    (by
      intro y
      exact ⟨(0, y), rfl⟩)

/-- `Nat.card` of a finite-dimensional additive Frattini quotient, in finrank form. -/
theorem p_frattini_finrank [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Nat.card (mFAdditi p G) =
      p ^ Module.finrank (ZMod p) (mFAdditi p G) := by
  simpa using
    (Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := mFAdditi p G))

/-- `Nat.card` of a finite-dimensional multiplicative Frattini quotient, in finrank form. -/
theorem mod_frattini_finrank [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Nat.card (mFQuot p G) =
      p ^ Module.finrank (ZMod p) (mFAdditi p G) := by
  calc
    Nat.card (mFQuot p G) = Nat.card (mFAdditi p G) :=
      Nat.card_congr Additive.ofMul
    _ = _ := p_frattini_finrank (p := p) G

/-- Product finite-dimensionality is equivalent to finite-dimensionality of both factors,
packaged as a constructor for the reverse direction. -/
theorem module_additive_components [Fact p.Prime] :
    (Module.Finite (ZMod p) (mFAdditi p (G × H))) ↔
      (Module.Finite (ZMod p) (mFAdditi p G) ∧
        Module.Finite (ZMod p) (mFAdditi p H)) := by
  constructor
  · intro h
    letI := h
    exact ⟨module_frattini_prod (p := p) G H,
      module_frattini_additive (p := p) G H⟩
  · intro h
    letI := h.1
    letI := h.2
    exact module_mod_prod (p := p) G H

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} (G H : Type*) [Group G] [Group H]

/-- Cardinality of a finite-dimensional additive Frattini quotient of a product,
in summed-rank form. -/
theorem frattini_additive_finrank [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Nat.card (mFAdditi p (G × H)) =
      p ^ (Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H)) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (G × H)) :=
    module_mod_prod (p := p) G H
  rw [p_frattini_finrank (p := p) (G × H),
    finrank_frattini_additive (p := p) G H]

/-- Cardinality of a finite-dimensional multiplicative Frattini quotient of a product,
in summed-rank form. -/
theorem nat_frattini_finrank [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)]
    [Module.Finite (ZMod p) (mFAdditi p H)] :
    Nat.card (mFQuot p (G × H)) =
      p ^ (Module.finrank (ZMod p) (mFAdditi p G) +
        Module.finrank (ZMod p) (mFAdditi p H)) := by
  haveI : Module.Finite (ZMod p) (mFAdditi p (G × H)) :=
    module_mod_prod (p := p) G H
  rw [mod_frattini_finrank (p := p) (G × H),
    finrank_frattini_additive (p := p) G H]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H]

/-- Finiteness of multiplicative Frattini quotients is preserved by products. -/
theorem finite_frattini_prod
    [Finite (mFQuot p G)] [Finite (mFQuot p H)] :
    Finite (mFQuot p (G × H)) := by
  haveI : Finite (mFQuot p G × mFQuot p H) := inferInstance
  exact Finite.of_equiv _ (mFQuot.prodEquiv p G H).symm.toEquiv

/-- Finiteness of the product quotient implies finiteness of the left quotient. -/
theorem mod_frattini_prod
    [Finite (mFQuot p (G × H))] :
    Finite (mFQuot p G) := by
  haveI : Finite (mFQuot p G × mFQuot p H) :=
    Finite.of_equiv _ (mFQuot.prodEquiv p G H).toEquiv
  exact Finite.of_surjective
    (fun z : mFQuot p G × mFQuot p H => z.1)
    (by
      intro x
      exact ⟨(x, 1), rfl⟩)

/-- Finiteness of the product quotient implies finiteness of the right quotient. -/
theorem p_frattini_prod
    [Finite (mFQuot p (G × H))] :
    Finite (mFQuot p H) := by
  haveI : Finite (mFQuot p G × mFQuot p H) :=
    Finite.of_equiv _ (mFQuot.prodEquiv p G H).toEquiv
  exact Finite.of_surjective
    (fun z : mFQuot p G × mFQuot p H => z.2)
    (by
      intro y
      exact ⟨(1, y), rfl⟩)

/-- Finiteness of additive Frattini quotients is preserved by products. -/
theorem p_additive_prod
    [Finite (mFAdditi p G)] [Finite (mFAdditi p H)] :
    Finite (mFAdditi p (G × H)) := by
  haveI : Finite (mFAdditi p G × mFAdditi p H) := inferInstance
  exact Finite.of_equiv _ (mFAdditi.prodAddEquiv (p := p) G H).symm.toEquiv

/-- Finiteness of an additive product quotient implies finiteness of the left quotient. -/
theorem p_frattini_additive
    [Finite (mFAdditi p (G × H))] :
    Finite (mFAdditi p G) := by
  haveI : Finite (mFAdditi p G × mFAdditi p H) :=
    Finite.of_equiv _ (mFAdditi.prodAddEquiv (p := p) G H).toEquiv
  exact Finite.of_surjective
    (fun z : mFAdditi p G × mFAdditi p H => z.1)
    (by
      intro x
      exact ⟨(x, 0), rfl⟩)

/-- Finiteness of an additive product quotient implies finiteness of the right quotient. -/
theorem frattini_additive_prod
    [Finite (mFAdditi p (G × H))] :
    Finite (mFAdditi p H) := by
  haveI : Finite (mFAdditi p G × mFAdditi p H) :=
    Finite.of_equiv _ (mFAdditi.prodAddEquiv (p := p) G H).toEquiv
  exact Finite.of_surjective
    (fun z : mFAdditi p G × mFAdditi p H => z.2)
    (by
      intro y
      exact ⟨(0, y), rfl⟩)

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H]

/-- A product multiplicative Frattini quotient is finite iff both factor quotients are finite. -/
theorem mod_p_prod :
    Finite (mFQuot p (G × H)) ↔
      Finite (mFQuot p G) ∧ Finite (mFQuot p H) := by
  constructor
  · intro h
    letI := h
    exact ⟨mod_frattini_prod p G H,
      p_frattini_prod p G H⟩
  · intro h
    letI := h.1
    letI := h.2
    exact finite_frattini_prod p G H

/-- A product additive Frattini quotient is finite iff both factor quotients are finite. -/
theorem mod_additive_prod :
    Finite (mFAdditi p (G × H)) ↔
      Finite (mFAdditi p G) ∧ Finite (mFAdditi p H) := by
  constructor
  · intro h
    letI := h
    exact ⟨p_frattini_additive p G H,
      frattini_additive_prod p G H⟩
  · intro h
    letI := h.1
    letI := h.2
    exact p_additive_prod p G H

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K]

/-- `Nat.card` multiplicativity for a left-associated triple product of Frattini quotients. -/
theorem nat_frattini_prod :
    Nat.card (mFQuot p ((G × H) × K)) =
      Nat.card (mFQuot p G) * Nat.card (mFQuot p H) *
        Nat.card (mFQuot p K) := by
  rw [nat_mod_prod (p := p) (G × H) K,
    nat_mod_prod (p := p) G H]

/-- `Nat.card` multiplicativity for a right-associated triple product of Frattini quotients. -/
theorem nat_frattini_nested :
    Nat.card (mFQuot p (G × (H × K))) =
      Nat.card (mFQuot p G) *
        (Nat.card (mFQuot p H) * Nat.card (mFQuot p K)) := by
  rw [nat_mod_prod (p := p) G (H × K),
    nat_mod_prod (p := p) H K]

/-- Additive `Nat.card` multiplicativity for a left-associated triple product. -/
theorem nat_frattini_additive :
    Nat.card (mFAdditi p ((G × H) × K)) =
      Nat.card (mFAdditi p G) * Nat.card (mFAdditi p H) *
        Nat.card (mFAdditi p K) := by
  rw [mod_frattini_additive (p := p) (G × H) K,
    mod_frattini_additive (p := p) G H]

/-- Additive `Nat.card` multiplicativity for a right-associated triple product. -/
theorem frattini_additive_nested :
    Nat.card (mFAdditi p (G × (H × K))) =
      Nat.card (mFAdditi p G) *
        (Nat.card (mFAdditi p H) * Nat.card (mFAdditi p K)) := by
  rw [mod_frattini_additive (p := p) G (H × K),
    mod_frattini_additive (p := p) H K]

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} (G : Type*) [Group G]

/-- A finite-dimensional additive Frattini quotient over `ZMod p` is finite as a type. -/
theorem frattini_additive_module [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Finite (mFAdditi p G) := by
  have hcard := p_frattini_finrank (p := p) G
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpos : 0 < Nat.card (mFAdditi p G) := by
    rw [hcard]
    exact pow_pos hp _
  exact (Nat.card_pos_iff.mp hpos).2

/-- A finite-dimensional Frattini quotient is finite in multiplicative form as well. -/
theorem p_frattini_module [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Finite (mFQuot p G) := by
  haveI : Finite (mFAdditi p G) :=
    frattini_additive_module (p := p) G
  exact Finite.of_equiv (mFAdditi p G) Additive.ofMul.symm

/-- A canonical fintype structure obtained from finite-dimensionality of the additive quotient. -/
@[reducible] noncomputable def fintype_p_module [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Fintype (mFAdditi p G) := by
  classical
  haveI : Finite (mFAdditi p G) :=
    frattini_additive_module (p := p) G
  exact Fintype.ofFinite _

/-- A canonical fintype structure on the multiplicative quotient from finite-dimensionality. -/
@[reducible] noncomputable def fintype_module_finite [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    Fintype (mFQuot p G) := by
  classical
  haveI : Finite (mFQuot p G) :=
    p_frattini_module (p := p) G
  exact Fintype.ofFinite _

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} (G : Type*) [Group G]

/-- `Fintype.card` form of the finite-dimensional additive Frattini quotient cardinality,
using the canonical fintype structure from `fintype_p_module`. -/
theorem fintype_frattini_module [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    @Fintype.card (mFAdditi p G)
        (fintype_p_module (p := p) G) =
      p ^ Module.finrank (ZMod p) (mFAdditi p G) := by
  have h := p_frattini_finrank (p := p) G
  rw [@Nat.card_eq_fintype_card (mFAdditi p G)
    (fintype_p_module (p := p) G)] at h
  exact h

/-- `Fintype.card` form for the multiplicative Frattini quotient, using the canonical
fintype structure from finite-dimensionality. -/
theorem fintype_mod_module [Fact p.Prime]
    [Module.Finite (ZMod p) (mFAdditi p G)] :
    @Fintype.card (mFQuot p G)
        (fintype_module_finite (p := p) G) =
      p ^ Module.finrank (ZMod p) (mFAdditi p G) := by
  have h := mod_frattini_finrank (p := p) G
  rw [@Nat.card_eq_fintype_card (mFQuot p G)
    (fintype_module_finite (p := p) G)] at h
  exact h

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} (G H K : Type*) [Group G] [Group H] [Group K]

/-- Finite-dimensionality criterion for a left-associated triple product. -/
theorem module_frattini_components [Fact p.Prime] :
    Module.Finite (ZMod p) (mFAdditi p ((G × H) × K)) ↔
      Module.Finite (ZMod p) (mFAdditi p G) ∧
        Module.Finite (ZMod p) (mFAdditi p H) ∧
          Module.Finite (ZMod p) (mFAdditi p K) := by
  rw [module_additive_components (p := p) (G × H) K,
    module_additive_components (p := p) G H]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Finite-dimensionality criterion for a right-associated triple product. -/
theorem module_nested_components [Fact p.Prime] :
    Module.Finite (ZMod p) (mFAdditi p (G × (H × K))) ↔
      Module.Finite (ZMod p) (mFAdditi p G) ∧
        Module.Finite (ZMod p) (mFAdditi p H) ∧
          Module.Finite (ZMod p) (mFAdditi p K) := by
  rw [module_additive_components (p := p) G (H × K),
    module_additive_components (p := p) H K]

/-- Finiteness criterion for a left-associated triple multiplicative quotient. -/
theorem p_frattini_components :
    Finite (mFQuot p ((G × H) × K)) ↔
      Finite (mFQuot p G) ∧ Finite (mFQuot p H) ∧
        Finite (mFQuot p K) := by
  rw [mod_p_prod p (G × H) K,
    mod_p_prod p G H]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Finiteness criterion for a right-associated triple multiplicative quotient. -/
theorem mod_nested_components :
    Finite (mFQuot p (G × (H × K))) ↔
      Finite (mFQuot p G) ∧ Finite (mFQuot p H) ∧
        Finite (mFQuot p K) := by
  rw [mod_p_prod p G (H × K),
    mod_p_prod p H K]

/-- Finiteness criterion for a left-associated triple additive quotient. -/
theorem frattini_additive_components :
    Finite (mFAdditi p ((G × H) × K)) ↔
      Finite (mFAdditi p G) ∧ Finite (mFAdditi p H) ∧
        Finite (mFAdditi p K) := by
  rw [mod_additive_prod p (G × H) K,
    mod_additive_prod p G H]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Finiteness criterion for a right-associated triple additive quotient. -/
theorem frattini_nested_components :
    Finite (mFAdditi p (G × (H × K))) ↔
      Finite (mFAdditi p G) ∧ Finite (mFAdditi p H) ∧
        Finite (mFAdditi p K) := by
  rw [mod_additive_prod p G (H × K),
    mod_additive_prod p H K]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K]

/-- `Nat.card` is invariant under swapping product factors in multiplicative Frattini quotients. -/
theorem nat_frattini_comm :
    Nat.card (mFQuot p (G × H)) =
      Nat.card (mFQuot p (H × G)) := by
  exact Nat.card_congr (mFQuot.prodCommEquiv (p := p) G H).toEquiv

/-- `Nat.card` is invariant under reassociating triple products in multiplicative quotients. -/
theorem nat_frattini_assoc :
    Nat.card (mFQuot p ((G × H) × K)) =
      Nat.card (mFQuot p (G × (H × K))) := by
  exact Nat.card_congr (mFQuot.prodAssocEquiv (p := p) G H K).toEquiv

/-- `Nat.card` is invariant under swapping product factors in additive Frattini quotients. -/
theorem frattini_additive_comm :
    Nat.card (mFAdditi p (G × H)) =
      Nat.card (mFAdditi p (H × G)) := by
  exact Nat.card_congr (mFAdditi.prod_comm_addequiv (p := p) G H).toEquiv

/-- `Nat.card` is invariant under reassociating triple products in additive quotients. -/
theorem frattini_additive_assoc :
    Nat.card (mFAdditi p ((G × H) × K)) =
      Nat.card (mFAdditi p (G × (H × K))) := by
  exact Nat.card_congr (mFAdditi.prod_assoc_addequiv (p := p) G H K).toEquiv

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K]

/-- Finiteness transports across swapping product factors (multiplicative quotient). -/
theorem mod_p_comm
    [Finite (mFQuot p (G × H))] :
    Finite (mFQuot p (H × G)) := by
  exact Finite.of_equiv (mFQuot p (G × H))
    (mFQuot.prodCommEquiv (p := p) G H).toEquiv

/-- Finiteness transports across reassociation (multiplicative quotient). -/
theorem mod_p_assoc
    [Finite (mFQuot p ((G × H) × K))] :
    Finite (mFQuot p (G × (H × K))) := by
  exact Finite.of_equiv (mFQuot p ((G × H) × K))
    (mFQuot.prodAssocEquiv (p := p) G H K).toEquiv

/-- Finiteness transports across inverse reassociation (multiplicative quotient). -/
theorem mod_assoc_symm
    [Finite (mFQuot p (G × (H × K)))] :
    Finite (mFQuot p ((G × H) × K)) := by
  exact Finite.of_equiv (mFQuot p (G × (H × K)))
    (mFQuot.prodAssocEquiv (p := p) G H K).symm.toEquiv

/-- Finiteness transports across swapping product factors (additive quotient). -/
theorem mod_additive_comm
    [Finite (mFAdditi p (G × H))] :
    Finite (mFAdditi p (H × G)) := by
  exact Finite.of_equiv (mFAdditi p (G × H))
    (mFAdditi.prod_comm_addequiv (p := p) G H).toEquiv

/-- Finiteness transports across reassociation (additive quotient). -/
theorem mod_additive_assoc
    [Finite (mFAdditi p ((G × H) × K))] :
    Finite (mFAdditi p (G × (H × K))) := by
  exact Finite.of_equiv (mFAdditi p ((G × H) × K))
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).toEquiv

/-- Finiteness transports across inverse reassociation (additive quotient). -/
theorem additive_assoc_symm
    [Finite (mFAdditi p (G × (H × K)))] :
    Finite (mFAdditi p ((G × H) × K)) := by
  exact Finite.of_equiv (mFAdditi p (G × (H × K)))
    (mFAdditi.prod_assoc_addequiv (p := p) G H K).symm.toEquiv

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- Canonical fintype structure transported forward along a Frattini-isomorphism-inducing
surjection (multiplicative quotient). -/
@[reducible] noncomputable def fintype_mod_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFQuot p G)] : Fintype (mFQuot p H) := by
  exact Fintype.ofEquiv (mFQuot p G)
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv

/-- Canonical fintype structure transported forward along a Frattini-isomorphism-inducing
surjection (additive quotient). -/
@[reducible] noncomputable def fintype_additive_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFAdditi p G)] : Fintype (mFAdditi p H) := by
  exact Fintype.ofEquiv (mFAdditi p G)
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv

/-- `Fintype.card` is preserved by the canonical transported multiplicative fintype. -/
theorem fintype_surjective_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFQuot p G)] :
    @Fintype.card (mFQuot p H)
        (fintype_mod_ker (p := p) f hs hker) =
      Fintype.card (mFQuot p G) := by
  letI : Fintype (mFQuot p H) :=
    fintype_mod_ker (p := p) f hs hker
  exact (Fintype.card_congr
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv).symm

/-- `Fintype.card` is preserved by the canonical transported additive fintype. -/
theorem fintype_frattini_ker
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFAdditi p G)] :
    @Fintype.card (mFAdditi p H)
        (fintype_additive_ker (p := p) f hs hker) =
      Fintype.card (mFAdditi p G) := by
  letI : Fintype (mFAdditi p H) :=
    fintype_additive_ker (p := p) f hs hker
  exact (Fintype.card_congr
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv).symm

end
end Submission

namespace Submission

noncomputable section

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- Canonical fintype structure transported backward along a Frattini-isomorphism-inducing
surjection (multiplicative quotient). -/
@[reducible] noncomputable def fintype_mod_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFQuot p H)] : Fintype (mFQuot p G) := by
  exact Fintype.ofEquiv (mFQuot p H)
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).symm.toEquiv

/-- Canonical fintype structure transported backward along a Frattini-isomorphism-inducing
surjection (additive quotient). -/
@[reducible] noncomputable def fintype_additive_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFAdditi p H)] : Fintype (mFAdditi p G) := by
  exact Fintype.ofEquiv (mFAdditi p H)
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).symm.toEquiv

/-- Backward transported multiplicative fintype has the same cardinality as the target. -/
theorem fintype_surjective_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFQuot p H)] :
    @Fintype.card (mFQuot p G)
        (fintype_mod_symm (p := p) f hs hker) =
      Fintype.card (mFQuot p H) := by
  letI : Fintype (mFQuot p G) :=
    fintype_mod_symm (p := p) f hs hker
  exact Fintype.card_congr
    (mFQuot.equiv_surj_kerle (p := p) f hs hker).toEquiv

/-- Backward transported additive fintype has the same cardinality as the target. -/
theorem fintype_frattini_symm
    (f : G →* H) (hs : Function.Surjective f) (hker : f.ker ≤ modPFrattini p G)
    [Fintype (mFAdditi p H)] :
    @Fintype.card (mFAdditi p G)
        (fintype_additive_symm (p := p) f hs hker) =
      Fintype.card (mFAdditi p H) := by
  letI : Fintype (mFAdditi p G) :=
    fintype_additive_symm (p := p) f hs hker
  exact Fintype.card_congr
    (mFAdditi.add_equivsurj_kerle (p := p) f hs hker).toEquiv

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H : Type*) [Group G] [Group H]

/-- Canonical fintype structure on a product multiplicative Frattini quotient from
factor fintypes. -/
@[reducible] noncomputable def fintype_mod_quotient
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)] :
    Fintype (mFQuot p (G × H)) := by
  exact Fintype.ofEquiv (mFQuot p G × mFQuot p H)
    (mFQuot.prodEquiv p G H).symm.toEquiv

/-- Canonical fintype structure on a product additive Frattini quotient from factor fintypes. -/
@[reducible] noncomputable def fintype_p_additive
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)] :
    Fintype (mFAdditi p (G × H)) := by
  exact Fintype.ofEquiv (mFAdditi p G × mFAdditi p H)
    (mFAdditi.prodAddEquiv (p := p) G H).symm.toEquiv

/-- `Fintype.card` multiplicativity for the canonical product multiplicative fintype. -/
theorem fintype_card_mod
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)] :
    @Fintype.card (mFQuot p (G × H))
        (fintype_mod_quotient p G H) =
      Fintype.card (mFQuot p G) *
        Fintype.card (mFQuot p H) := by
  letI : Fintype (mFQuot p (G × H)) :=
    fintype_mod_quotient p G H
  rw [Fintype.card_congr (mFQuot.prodEquiv p G H).toEquiv]
  exact Fintype.card_prod _ _

/-- `Fintype.card` multiplicativity for the canonical product additive fintype. -/
theorem fintype_card_frattini
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)] :
    @Fintype.card (mFAdditi p (G × H))
        (fintype_p_additive p G H) =
      Fintype.card (mFAdditi p G) *
        Fintype.card (mFAdditi p H) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    fintype_p_additive p G H
  rw [Fintype.card_congr (mFAdditi.prodAddEquiv (p := p) G H).toEquiv]
  exact Fintype.card_prod _ _

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H K : Type*) [Group G] [Group H] [Group K]

/-- Canonical fintype on a left-associated triple multiplicative Frattini quotient. -/
@[reducible] noncomputable def fintype_frattini_quotient
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)]
    [Fintype (mFQuot p K)] :
    Fintype (mFQuot p ((G × H) × K)) := by
  letI : Fintype (mFQuot p (G × H)) :=
    fintype_mod_quotient p G H
  exact fintype_mod_quotient p (G × H) K

/-- Canonical fintype on a right-associated triple multiplicative Frattini quotient. -/
@[reducible] noncomputable def mod_frattini_nested
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)]
    [Fintype (mFQuot p K)] :
    Fintype (mFQuot p (G × (H × K))) := by
  letI : Fintype (mFQuot p (H × K)) :=
    fintype_mod_quotient p H K
  exact fintype_mod_quotient p G (H × K)

/-- Canonical fintype on a left-associated triple additive Frattini quotient. -/
@[reducible] noncomputable def fintype_p_prod
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)]
    [Fintype (mFAdditi p K)] :
    Fintype (mFAdditi p ((G × H) × K)) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    fintype_p_additive p G H
  exact fintype_p_additive p (G × H) K

/-- Canonical fintype on a right-associated triple additive Frattini quotient. -/
@[reducible] noncomputable def p_frattini_nested
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)]
    [Fintype (mFAdditi p K)] :
    Fintype (mFAdditi p (G × (H × K))) := by
  letI : Fintype (mFAdditi p (H × K)) :=
    fintype_p_additive p H K
  exact fintype_p_additive p G (H × K)

/-- Cardinality of the canonical left-associated triple multiplicative fintype. -/
theorem fintype_mod_prod
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)]
    [Fintype (mFQuot p K)] :
    @Fintype.card (mFQuot p ((G × H) × K))
        (fintype_frattini_quotient p G H K) =
      Fintype.card (mFQuot p G) *
        Fintype.card (mFQuot p H) *
          Fintype.card (mFQuot p K) := by
  letI : Fintype (mFQuot p (G × H)) :=
    fintype_mod_quotient p G H
  letI : Fintype (mFQuot p ((G × H) × K)) :=
    fintype_frattini_quotient p G H K
  rw [fintype_card_mod (p := p) (G × H) K,
    fintype_card_mod (p := p) G H]

/-- Cardinality of the canonical right-associated triple multiplicative fintype. -/
theorem fintype_p_nested
    [Fintype (mFQuot p G)] [Fintype (mFQuot p H)]
    [Fintype (mFQuot p K)] :
    @Fintype.card (mFQuot p (G × (H × K)))
        (mod_frattini_nested p G H K) =
      Fintype.card (mFQuot p G) *
        (Fintype.card (mFQuot p H) *
          Fintype.card (mFQuot p K)) := by
  letI : Fintype (mFQuot p (H × K)) :=
    fintype_mod_quotient p H K
  letI : Fintype (mFQuot p (G × (H × K))) :=
    mod_frattini_nested p G H K
  rw [fintype_card_mod (p := p) G (H × K),
    fintype_card_mod (p := p) H K]

/-- Cardinality of the canonical left-associated triple additive fintype. -/
theorem fintype_frattini_prod
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)]
    [Fintype (mFAdditi p K)] :
    @Fintype.card (mFAdditi p ((G × H) × K))
        (fintype_p_prod p G H K) =
      Fintype.card (mFAdditi p G) *
        Fintype.card (mFAdditi p H) *
          Fintype.card (mFAdditi p K) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    fintype_p_additive p G H
  letI : Fintype (mFAdditi p ((G × H) × K)) :=
    fintype_p_prod p G H K
  rw [fintype_card_frattini (p := p) (G × H) K,
    fintype_card_frattini (p := p) G H]

/-- Cardinality of the canonical right-associated triple additive fintype. -/
theorem fintype_mod_nested
    [Fintype (mFAdditi p G)] [Fintype (mFAdditi p H)]
    [Fintype (mFAdditi p K)] :
    @Fintype.card (mFAdditi p (G × (H × K)))
        (p_frattini_nested p G H K) =
      Fintype.card (mFAdditi p G) *
        (Fintype.card (mFAdditi p H) *
          Fintype.card (mFAdditi p K)) := by
  letI : Fintype (mFAdditi p (H × K)) :=
    fintype_p_additive p H K
  letI : Fintype (mFAdditi p (G × (H × K))) :=
    p_frattini_nested p G H K
  rw [fintype_card_frattini (p := p) G (H × K),
    fintype_card_frattini (p := p) H K]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G E : Type*) [Group G] [Group E] [Subsingleton E]

/-- Canonical fintype on a product with a trivial right factor, transported from the
multiplicative Frattini quotient of the nontrivial factor. -/
@[reducible] noncomputable def fintype_p_frattini
    [Fintype (mFQuot p G)] :
    Fintype (mFQuot p (G × E)) := by
  exact Fintype.ofEquiv (mFQuot p G)
    (mFQuot.prod_right_trivialequiv (p := p) G E).symm.toEquiv

/-- Canonical fintype on a product with a trivial left factor, transported from the
multiplicative Frattini quotient of the nontrivial factor. -/
@[reducible] noncomputable def fintype_mod_p
    [Fintype (mFQuot p G)] :
    Fintype (mFQuot p (E × G)) := by
  exact Fintype.ofEquiv (mFQuot p G)
    (mFQuot.prod_left_trivialequiv (p := p) E G).symm.toEquiv

/-- Canonical fintype on an additive product quotient with a trivial right factor. -/
@[reducible] noncomputable def mod_p_trivial
    [Fintype (mFAdditi p G)] :
    Fintype (mFAdditi p (G × E)) := by
  exact Fintype.ofEquiv (mFAdditi p G)
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).symm.toEquiv

/-- Canonical fintype on an additive product quotient with a trivial left factor. -/
@[reducible] noncomputable def frattini_left_trivial
    [Fintype (mFAdditi p G)] :
    Fintype (mFAdditi p (E × G)) := by
  exact Fintype.ofEquiv (mFAdditi p G)
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).symm.toEquiv

/-- Cardinality of the canonical right-trivial product multiplicative fintype. -/
theorem card_frattini_trivial
    [Fintype (mFQuot p G)] :
    @Fintype.card (mFQuot p (G × E))
        (fintype_p_frattini p G E) =
      Fintype.card (mFQuot p G) := by
  letI : Fintype (mFQuot p (G × E)) :=
    fintype_p_frattini p G E
  exact Fintype.card_congr
    (mFQuot.prod_right_trivialequiv (p := p) G E).toEquiv

/-- Cardinality of the canonical left-trivial product multiplicative fintype. -/
theorem frattini_prod_trivial
    [Fintype (mFQuot p G)] :
    @Fintype.card (mFQuot p (E × G))
        (fintype_mod_p p G E) =
      Fintype.card (mFQuot p G) := by
  letI : Fintype (mFQuot p (E × G)) :=
    fintype_mod_p p G E
  exact Fintype.card_congr
    (mFQuot.prod_left_trivialequiv (p := p) E G).toEquiv

/-- Cardinality of the canonical right-trivial product additive fintype. -/
theorem mod_additive_trivial
    [Fintype (mFAdditi p G)] :
    @Fintype.card (mFAdditi p (G × E))
        (mod_p_trivial p G E) =
      Fintype.card (mFAdditi p G) := by
  letI : Fintype (mFAdditi p (G × E)) :=
    mod_p_trivial p G E
  exact Fintype.card_congr
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).toEquiv

/-- Cardinality of the canonical left-trivial product additive fintype. -/
theorem p_additive_trivial
    [Fintype (mFAdditi p G)] :
    @Fintype.card (mFAdditi p (E × G))
        (frattini_left_trivial p G E) =
      Fintype.card (mFAdditi p G) := by
  letI : Fintype (mFAdditi p (E × G)) :=
    frattini_left_trivial p G E
  exact Fintype.card_congr
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).toEquiv

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G E : Type*) [Group G] [Group E] [Subsingleton E]

/-- Transport a fintype from a right-trivial product quotient back to the nontrivial factor. -/
@[reducible] noncomputable def fintype_mod_frattini
    [Fintype (mFQuot p (G × E))] :
    Fintype (mFQuot p G) := by
  exact Fintype.ofEquiv (mFQuot p (G × E))
    (mFQuot.prod_right_trivialequiv (p := p) G E).toEquiv

/-- Transport a fintype from a left-trivial product quotient back to the nontrivial factor. -/
@[reducible] noncomputable def fintype_quotient_trivial
    [Fintype (mFQuot p (E × G))] :
    Fintype (mFQuot p G) := by
  exact Fintype.ofEquiv (mFQuot p (E × G))
    (mFQuot.prod_left_trivialequiv (p := p) E G).toEquiv

/-- Transport a fintype from an additive right-trivial product quotient back to the factor. -/
@[reducible] noncomputable def additive_prod_trivial
    [Fintype (mFAdditi p (G × E))] :
    Fintype (mFAdditi p G) := by
  exact Fintype.ofEquiv (mFAdditi p (G × E))
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).toEquiv

/-- Transport a fintype from an additive left-trivial product quotient back to the factor. -/
@[reducible] noncomputable def fintype_mod_additive
    [Fintype (mFAdditi p (E × G))] :
    Fintype (mFAdditi p G) := by
  exact Fintype.ofEquiv (mFAdditi p (E × G))
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).toEquiv

/-- Cardinality for the factor fintype transported from a right-trivial product. -/
theorem p_frattini_trivial
    [Fintype (mFQuot p (G × E))] :
    @Fintype.card (mFQuot p G)
        (fintype_mod_frattini p G E) =
      Fintype.card (mFQuot p (G × E)) := by
  letI : Fintype (mFQuot p G) :=
    fintype_mod_frattini p G E
  exact (Fintype.card_congr
    (mFQuot.prod_right_trivialequiv (p := p) G E).toEquiv).symm

/-- Cardinality for the factor fintype transported from a left-trivial product. -/
theorem mod_frattini_trivial
    [Fintype (mFQuot p (E × G))] :
    @Fintype.card (mFQuot p G)
        (fintype_quotient_trivial p G E) =
      Fintype.card (mFQuot p (E × G)) := by
  letI : Fintype (mFQuot p G) :=
    fintype_quotient_trivial p G E
  exact (Fintype.card_congr
    (mFQuot.prod_left_trivialequiv (p := p) E G).toEquiv).symm

/-- Cardinality for the additive factor fintype transported from a right-trivial product. -/
theorem frattini_additive_trivial
    [Fintype (mFAdditi p (G × E))] :
    @Fintype.card (mFAdditi p G)
        (additive_prod_trivial p G E) =
      Fintype.card (mFAdditi p (G × E)) := by
  letI : Fintype (mFAdditi p G) :=
    additive_prod_trivial p G E
  exact (Fintype.card_congr
    (mFAdditi.prod_righttrivial_addequiv (p := p) G E).toEquiv).symm

/-- Cardinality for the additive factor fintype transported from a left-trivial product. -/
theorem fintype_frattini_additive
    [Fintype (mFAdditi p (E × G))] :
    @Fintype.card (mFAdditi p G)
        (fintype_mod_additive p G E) =
      Fintype.card (mFAdditi p (E × G)) := by
  letI : Fintype (mFAdditi p G) :=
    fintype_mod_additive p G E
  exact (Fintype.card_congr
    (mFAdditi.prod_lefttrivial_addequiv (p := p) E G).toEquiv).symm

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]

/-- Canonical fintype on a nested product with a trivial middle factor. -/
@[reducible] noncomputable def prod_nested_trivial
    [Fintype (mFQuot p (G × H))] :
    Fintype (mFQuot p (G × (E × H))) := by
  exact Fintype.ofEquiv (mFQuot p (G × H))
    (mFQuot.prod_nestedleft_trivialequiv (p := p) G E H).symm.toEquiv

/-- Canonical fintype on a nested product with a trivial rightmost factor. -/
@[reducible] noncomputable def p_nested_trivial
    [Fintype (mFQuot p (G × H))] :
    Fintype (mFQuot p (G × (H × E))) := by
  exact Fintype.ofEquiv (mFQuot p (G × H))
    (mFQuot.prod_nestedright_trivialequiv (p := p) G H E).symm.toEquiv

/-- Additive canonical fintype on a nested product with a trivial middle factor. -/
@[reducible] noncomputable def fintype_additive_nested
    [Fintype (mFAdditi p (G × H))] :
    Fintype (mFAdditi p (G × (E × H))) := by
  exact Fintype.ofEquiv (mFAdditi p (G × H))
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).symm.toEquiv

/-- Additive canonical fintype on a nested product with a trivial rightmost factor. -/
@[reducible] noncomputable def fintype_frattini_nested
    [Fintype (mFAdditi p (G × H))] :
    Fintype (mFAdditi p (G × (H × E))) := by
  exact Fintype.ofEquiv (mFAdditi p (G × H))
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).symm.toEquiv

/-- Cardinality of the canonical nested-left-trivial multiplicative fintype. -/
theorem frattini_nested_trivial
    [Fintype (mFQuot p (G × H))] :
    @Fintype.card (mFQuot p (G × (E × H)))
        (prod_nested_trivial p G H E) =
      Fintype.card (mFQuot p (G × H)) := by
  letI : Fintype (mFQuot p (G × (E × H))) :=
    prod_nested_trivial p G H E
  exact Fintype.card_congr
    (mFQuot.prod_nestedleft_trivialequiv (p := p) G E H).toEquiv

/-- Cardinality of the canonical nested-right-trivial multiplicative fintype. -/
theorem fintype_p_trivial
    [Fintype (mFQuot p (G × H))] :
    @Fintype.card (mFQuot p (G × (H × E)))
        (p_nested_trivial p G H E) =
      Fintype.card (mFQuot p (G × H)) := by
  letI : Fintype (mFQuot p (G × (H × E))) :=
    p_nested_trivial p G H E
  exact Fintype.card_congr
    (mFQuot.prod_nestedright_trivialequiv (p := p) G H E).toEquiv

/-- Cardinality of the canonical nested-left-trivial additive fintype. -/
theorem fintype_prod_trivial
    [Fintype (mFAdditi p (G × H))] :
    @Fintype.card (mFAdditi p (G × (E × H)))
        (fintype_additive_nested p G H E) =
      Fintype.card (mFAdditi p (G × H)) := by
  letI : Fintype (mFAdditi p (G × (E × H))) :=
    fintype_additive_nested p G H E
  exact Fintype.card_congr
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).toEquiv

/-- Cardinality of the canonical nested-right-trivial additive fintype. -/
theorem fintype_card_trivial
    [Fintype (mFAdditi p (G × H))] :
    @Fintype.card (mFAdditi p (G × (H × E)))
        (fintype_frattini_nested p G H E) =
      Fintype.card (mFAdditi p (G × H)) := by
  letI : Fintype (mFAdditi p (G × (H × E))) :=
    fintype_frattini_nested p G H E
  exact Fintype.card_congr
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).toEquiv

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (G H E : Type*) [Group G] [Group H] [Group E] [Subsingleton E]

/-- Transport a fintype from a nested-left-trivial product back to the shortened product. -/
@[reducible] noncomputable def mod_nested_trivial
    [Fintype (mFQuot p (G × (E × H)))] :
    Fintype (mFQuot p (G × H)) := by
  exact Fintype.ofEquiv (mFQuot p (G × (E × H)))
    (mFQuot.prod_nestedleft_trivialequiv (p := p) G E H).toEquiv

/-- Transport a fintype from a nested-right-trivial product back to the shortened product. -/
@[reducible] noncomputable def fintype_right_trivial
    [Fintype (mFQuot p (G × (H × E)))] :
    Fintype (mFQuot p (G × H)) := by
  exact Fintype.ofEquiv (mFQuot p (G × (H × E)))
    (mFQuot.prod_nestedright_trivialequiv (p := p) G H E).toEquiv

/-- Additive transport from a nested-left-trivial product back to the shortened product. -/
@[reducible] noncomputable def fintype_left_trivial
    [Fintype (mFAdditi p (G × (E × H)))] :
    Fintype (mFAdditi p (G × H)) := by
  exact Fintype.ofEquiv (mFAdditi p (G × (E × H)))
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).toEquiv

/-- Additive transport from a nested-right-trivial product back to the shortened product. -/
@[reducible] noncomputable def additive_nested_trivial
    [Fintype (mFAdditi p (G × (H × E)))] :
    Fintype (mFAdditi p (G × H)) := by
  exact Fintype.ofEquiv (mFAdditi p (G × (H × E)))
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).toEquiv

/-- Cardinality for shortening a nested-left-trivial multiplicative product. -/
theorem fintype_mod_trivial
    [Fintype (mFQuot p (G × (E × H)))] :
    @Fintype.card (mFQuot p (G × H))
        (mod_nested_trivial p G H E) =
      Fintype.card (mFQuot p (G × (E × H))) := by
  letI : Fintype (mFQuot p (G × H)) :=
    mod_nested_trivial p G H E
  exact (Fintype.card_congr
    (mFQuot.prod_nestedleft_trivialequiv (p := p) G E H).toEquiv).symm

/-- Cardinality for shortening a nested-right-trivial multiplicative product. -/
theorem fintype_frattini_trivial
    [Fintype (mFQuot p (G × (H × E)))] :
    @Fintype.card (mFQuot p (G × H))
        (fintype_right_trivial p G H E) =
      Fintype.card (mFQuot p (G × (H × E))) := by
  letI : Fintype (mFQuot p (G × H)) :=
    fintype_right_trivial p G H E
  exact (Fintype.card_congr
    (mFQuot.prod_nestedright_trivialequiv (p := p) G H E).toEquiv).symm

/-- Cardinality for shortening a nested-left-trivial additive product. -/
theorem fintype_additive_trivial
    [Fintype (mFAdditi p (G × (E × H)))] :
    @Fintype.card (mFAdditi p (G × H))
        (fintype_left_trivial p G H E) =
      Fintype.card (mFAdditi p (G × (E × H))) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    fintype_left_trivial p G H E
  exact (Fintype.card_congr
    (mFAdditi.prodnested_lefttrivial_addequiv (p := p) G E H).toEquiv).symm

/-- Cardinality for shortening a nested-right-trivial additive product. -/
theorem fintype_nested_trivial
    [Fintype (mFAdditi p (G × (H × E)))] :
    @Fintype.card (mFAdditi p (G × H))
        (additive_nested_trivial p G H E) =
      Fintype.card (mFAdditi p (G × (H × E))) := by
  letI : Fintype (mFAdditi p (G × H)) :=
    additive_nested_trivial p G H E
  exact (Fintype.card_congr
    (mFAdditi.prodnested_righttrivial_addequiv (p := p) G H E).toEquiv).symm

end
end Submission
