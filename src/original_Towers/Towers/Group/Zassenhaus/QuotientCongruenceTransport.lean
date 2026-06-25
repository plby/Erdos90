import Towers.Group.Zassenhaus.Core

open scoped commutatorElement

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Congruence followed by its inverse is identity on Zassenhaus quotient homs. -/
theorem zQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zQuot.congr p G e n).symm.toMonoidHom).comp
      (zQuot.congr p G e n).toMonoidHom =
    MonoidHom.id (zQuot p G n) := by
  ext x
  change (zQuot.congr p G e n).symm
      ((zQuot.congr p G e n) x) = x
  exact (zQuot.congr p G e n).left_inv x

/-- Inverse congruence followed by congruence is identity on Zassenhaus quotient homs. -/
theorem zQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zQuot.congr p G e n).toMonoidHom.comp
      ((zQuot.congr p G e n).symm.toMonoidHom) =
    MonoidHom.id (zQuot p H n) := by
  ext x
  change (zQuot.congr p G e n)
      ((zQuot.congr p G e n).symm x) = x
  exact (zQuot.congr p G e n).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Congruence followed by its inverse is identity on Zassenhaus consecutive quotient homs. -/
theorem zNQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zNQuot.congr p G e n).symm.toMonoidHom).comp
      (zNQuot.congr p G e n).toMonoidHom =
    MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n) := by
  ext x
  change (zNQuot.congr p G e n).symm
      ((zNQuot.congr p G e n) x) = x
  exact (zNQuot.congr p G e n).left_inv x

/-- Inverse congruence followed by congruence is identity on Zassenhaus consecutive
quotient homs. -/
theorem zNQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNQuot.congr p G e n).toMonoidHom.comp
      ((zNQuot.congr p G e n).symm.toMonoidHom) =
    MonoidHom.id (zSubgro p H n ⧸ zNTerm p H n) := by
  ext x
  change (zNQuot.congr p G e n)
      ((zNQuot.congr p G e n).symm x) = x
  exact (zNQuot.congr p G e n).right_inv x

/-- Congruence followed by its inverse is identity on Zassenhaus layer-kernel homs. -/
theorem zLKern.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zLKern.congr p G e n).symm.toMonoidHom).comp
      (zLKern.congr p G e n).toMonoidHom =
    MonoidHom.id (zLKern p G n) := by
  ext x
  exact congrArg Subtype.val
    ((zLKern.congr p G e n).left_inv x)

/-- Inverse congruence followed by congruence is identity on Zassenhaus layer-kernel homs. -/
theorem zLKern.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zLKern.congr p G e n).toMonoidHom.comp
      ((zLKern.congr p G e n).symm.toMonoidHom) =
    MonoidHom.id (zLKern p H n) := by
  ext x
  exact congrArg Subtype.val
    ((zLKern.congr p G e n).right_inv x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- A prime consecutive-quotient linear congruence followed by its inverse is identity. -/
theorem zNQuot.congrlin_symmcomp_linmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zNQuot.congrLinear p G e n).symm.toLinearMap).comp
      (zNQuot.congrLinear p G e n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- The inverse prime consecutive-quotient linear congruence followed by congruence is identity. -/
theorem zNQuot.congrlin_compsymm_linmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNQuot.congrLinear p G e n).toLinearMap.comp
      ((zNQuot.congrLinear p G e n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

/-- A prime layer-kernel linear automorphism followed by its inverse is identity. -/
theorem zLKern.congrlin_symmcomp_linmap
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    ((zLKern.congrLinear p G e n).symm.toLinearMap).comp
      (zLKern.congrLinear p G e n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- The inverse prime layer-kernel linear automorphism followed by automorphism is identity. -/
theorem zLKern.congrlin_compsymm_linmap
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    (zLKern.congrLinear p G e n).toLinearMap.comp
      ((zLKern.congrLinear p G e n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Composition of Zassenhaus quotient congruence homs is congruence for the composite. -/
theorem zQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zQuot.congr p H f n).toMonoidHom.comp
      (zQuot.congr p G e n).toMonoidHom =
    (zQuot.congr p G (e.trans f) n).toMonoidHom := by
  ext x
  change ((zQuot.congr p G e n).trans
      (zQuot.congr p H f n)) x =
    (zQuot.congr p G (e.trans f) n) x
  exact congrArg
    (fun E : zQuot p G n ≃* zQuot p K n => E x)
    (zQuot.congr_trans (p := p) (G := G) e f n)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Composition of consecutive Zassenhaus quotient congruence homs is congruence for
the composite. -/
theorem zNQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zNQuot.congr p H f n).toMonoidHom.comp
      (zNQuot.congr p G e n).toMonoidHom =
    (zNQuot.congr p G (e.trans f) n).toMonoidHom := by
  ext x
  change ((zNQuot.congr p G e n).trans
      (zNQuot.congr p H f n)) x =
    (zNQuot.congr p G (e.trans f) n) x
  exact congrArg
    (fun E : (zSubgro p G n ⧸ zNTerm p G n) ≃*
        (zSubgro p K n ⧸ zNTerm p K n) => E x)
    (zNQuot.congr_trans (p := p) (G := G) e f n)

/-- Composition of Zassenhaus layer-kernel congruence homs is congruence for the composite. -/
theorem zLKern.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zLKern.congr p H f n).toMonoidHom.comp
      (zLKern.congr p G e n).toMonoidHom =
    (zLKern.congr p G (e.trans f) n).toMonoidHom := by
  ext x
  exact congrArg Subtype.val <| congrArg
    (fun E : zLKern p G n ≃* zLKern p K n => E x)
    (zLKern.congr_trans (p := p) (G := G) e f n)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The identity equivalence induces the identity hom on Zassenhaus quotients. -/
theorem zQuot.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zQuot.congr p G (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (zQuot p G n) := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The identity equivalence induces the identity hom on consecutive Zassenhaus quotients. -/
theorem zNQuot.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zNQuot.congr p G (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n) := by
  ext x
  simp

/-- The identity equivalence induces the identity hom on Zassenhaus layer kernels. -/
theorem zLKern.congr_refl_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zLKern.congr p G (MulEquiv.refl G) n).toMonoidHom =
    MonoidHom.id (zLKern p G n) := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The identity equivalence induces the identity linear map on prime consecutive quotients. -/
theorem zNQuot.congr_linrefl_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    (zNQuot.congrLinear p G (MulEquiv.refl G) n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The identity automorphism induces the identity linear map on prime layer kernels. -/
theorem zLKern.congr_linrefl_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    (zLKern.congrLinear p G (MulEquiv.refl G) n).toLinearMap =
    LinearMap.id := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.congrLinear, zLKern.mapLinear,
        zLKern.mapAdd]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Composition of prime consecutive-quotient linear congruences is the composite congruence. -/
theorem zNQuot.congr_lintrans_linmap
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zNQuot.congrLinear p H f n).toLinearMap.comp
      (zNQuot.congrLinear p G e n).toLinearMap =
    (zNQuot.congrLinear p G (e.trans f) n).toLinearMap := by
  ext x
  cases x with
  | ofMul q =>
      simp [LinearMap.comp_apply, zNQuot.congrLinear,
        zNQuot.mapLinear]

/-- Composition of prime layer-kernel linear automorphisms is the composite automorphism. -/
theorem zLKern.congr_lintrans_linmap
    [Fact p.Prime] (G : Type*) [Group G] (e f : MulAut G) (n : ℕ) :
    (zLKern.congrLinear p G f n).toLinearMap.comp
      (zLKern.congrLinear p G e n).toLinearMap =
    (zLKern.congrLinear p G (e.trans f) n).toLinearMap := by
  ext x
  cases x with
  | ofMul y =>
      simp [LinearMap.comp_apply, zLKern.congrLinear,
        zLKern.mapLinear, zLKern.mapAdd]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Term-quotient congruence followed by its inverse is identity. -/
theorem zTQuot.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((zTQuot.congr p G e hmn).symm.toMonoidHom).comp
      (zTQuot.congr p G e hmn).toMonoidHom =
    MonoidHom.id (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  ext x
  change (zTQuot.congr p G e hmn).symm
      ((zTQuot.congr p G e hmn) x) = x
  exact (zTQuot.congr p G e hmn).left_inv x

/-- Inverse term-quotient congruence followed by congruence is identity. -/
theorem zTQuot.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p G e hmn).toMonoidHom.comp
      ((zTQuot.congr p G e hmn).symm.toMonoidHom) =
    MonoidHom.id (zSubgro p H m ⧸ zTSubgro p H hmn) := by
  ext x
  change (zTQuot.congr p G e hmn)
      ((zTQuot.congr p G e hmn).symm x) = x
  exact (zTQuot.congr p G e hmn).right_inv x

/-- Transition-kernel congruence followed by its inverse is identity. -/
theorem zTKern.congr_symmcomp_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((zTKern.congr p G e hmn).symm.toMonoidHom).comp
      (zTKern.congr p G e hmn).toMonoidHom =
    MonoidHom.id (MonoidHom.ker (zassenhaus p G hmn)) := by
  ext x
  exact congrArg Subtype.val
    ((zTKern.congr p G e hmn).left_inv x)

/-- Inverse transition-kernel congruence followed by congruence is identity. -/
theorem zTKern.congr_compsymm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p G e hmn).toMonoidHom.comp
      ((zTKern.congr p G e hmn).symm.toMonoidHom) =
    MonoidHom.id (MonoidHom.ker (zassenhaus p H hmn)) := by
  ext x
  exact congrArg Subtype.val
    ((zTKern.congr p G e hmn).right_inv x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Identity equivalence induces identity on arbitrary Zassenhaus term quotients. -/
theorem zTQuot.congr_refl_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p G (MulEquiv.refl G) hmn).toMonoidHom =
    MonoidHom.id (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  ext x
  simp

/-- Identity equivalence induces identity on arbitrary Zassenhaus transition kernels. -/
theorem zTKern.congr_refl_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p G (MulEquiv.refl G) hmn).toMonoidHom =
    MonoidHom.id (MonoidHom.ker (zassenhaus p G hmn)) := by
  ext x
  simp

/-- Composition of term-quotient congruence homs is congruence for the composite. -/
theorem zTQuot.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p H f hmn).toMonoidHom.comp
      (zTQuot.congr p G e hmn).toMonoidHom =
    (zTQuot.congr p G (e.trans f) hmn).toMonoidHom := by
  ext x
  change ((zTQuot.congr p G e hmn).trans
      (zTQuot.congr p H f hmn)) x =
    (zTQuot.congr p G (e.trans f) hmn) x
  exact congrArg
    (fun E : (zSubgro p G m ⧸ zTSubgro p G hmn) ≃*
        (zSubgro p K m ⧸ zTSubgro p K hmn) => E x)
    (zTQuot.congr_trans (p := p) (G := G) e f hmn)

/-- Composition of transition-kernel congruence homs is congruence for the composite. -/
theorem zTKern.congr_trans_monoidhom
    (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p H f hmn).toMonoidHom.comp
      (zTKern.congr p G e hmn).toMonoidHom =
    (zTKern.congr p G (e.trans f) hmn).toMonoidHom := by
  ext x
  exact congrArg Subtype.val <| congrArg
    (fun E : MonoidHom.ker (zassenhaus p G hmn) ≃*
        MonoidHom.ker (zassenhaus p K hmn) => E x)
    (zTKern.congr_trans (p := p) (G := G) e f hmn)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The inverse Zassenhaus quotient congruence hom is the congruence hom
for the inverse isomorphism. -/
theorem zQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zQuot.congr p G e n).symm.toMonoidHom) =
      (zQuot.congr p H e.symm n).toMonoidHom := by
  rw [zQuot.congr_symm]

/-- The inverse consecutive Zassenhaus quotient congruence hom is induced by
the inverse isomorphism. -/
theorem zNQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zNQuot.congr p G e n).symm.toMonoidHom) =
      (zNQuot.congr p H e.symm n).toMonoidHom := by
  rw [zNQuot.congr_symm]

/-- The inverse Zassenhaus layer-kernel congruence hom is induced by
the inverse isomorphism. -/
theorem zLKern.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zLKern.congr p G e n).symm.toMonoidHom) =
      (zLKern.congr p H e.symm n).toMonoidHom := by
  rw [zLKern.congr_symm]

/-- The inverse arbitrary-term Zassenhaus quotient congruence hom is induced by
the inverse isomorphism. -/
theorem zTQuot.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((zTQuot.congr p G e hmn).symm.toMonoidHom) =
      (zTQuot.congr p H e.symm hmn).toMonoidHom := by
  rw [zTQuot.congr_symm]

/-- The inverse Zassenhaus transition-kernel congruence hom is induced by
the inverse isomorphism. -/
theorem zTKern.congr_symm_monoidhom
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    ((zTKern.congr p G e hmn).symm.toMonoidHom) =
      (zTKern.congr p H e.symm hmn).toMonoidHom := by
  rw [zTKern.congr_symm]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The inverse prime consecutive-quotient congruence linear map is induced by
the inverse isomorphism. -/
theorem zNQuot.congr_linsymm_linmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    ((zNQuot.congrLinear p G e n).symm.toLinearMap) =
      (zNQuot.congrLinear p H e.symm n).toLinearMap := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.congrLinear, zNQuot.mapLinear]

/-- The inverse prime layer-kernel congruence linear map is induced by
the inverse automorphism. -/
theorem zLKern.congr_linsymm_linmap
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    ((zLKern.congrLinear p G e n).symm.toLinearMap) =
      (zLKern.congrLinear p G e.symm n).toLinearMap := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.congrLinear, zLKern.mapLinear,
        zLKern.mapAdd]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Identity isomorphism induces the identity prime-linear equivalence on consecutive quotients. -/
@[simp] theorem zNQuot.congrLinear_refl
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    zNQuot.congrLinear p G (MulEquiv.refl G) n =
      LinearEquiv.refl (ZMod p)
        (Additive (zSubgro p G n ⧸ zNTerm p G n)) := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.congrLinear, zNQuot.mapLinear]

/-- Identity automorphism induces the identity prime-linear equivalence on layer kernels. -/
@[simp] theorem zLKern.congrLinear_refl
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    zLKern.congrLinear p G (MulEquiv.refl G) n =
      LinearEquiv.refl (ZMod p) (Additive (zLKern p G n)) := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.congrLinear, zLKern.mapLinear,
        zLKern.mapAdd]

/-- Composition of prime-linear consecutive quotient congruences is the composite congruence. -/
@[simp] theorem zNQuot.congrLinear_trans
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zNQuot.congrLinear p G e n).trans
      (zNQuot.congrLinear p H f n) =
    zNQuot.congrLinear p G (e.trans f) n := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.congrLinear, zNQuot.mapLinear]

/-- Composition of prime-linear layer-kernel automorphism congruences is composite. -/
@[simp] theorem zLKern.congrLinear_trans
    [Fact p.Prime] (G : Type*) [Group G] (e f : MulAut G) (n : ℕ) :
    (zLKern.congrLinear p G e n).trans
      (zLKern.congrLinear p G f n) =
    zLKern.congrLinear p G (e.trans f) n := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.congrLinear, zLKern.mapLinear,
        zLKern.mapAdd]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The inverse prime-linear consecutive quotient equivalence is induced by
the inverse isomorphism. -/
@[simp] theorem zNQuot.congrLinear_symm
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNQuot.congrLinear p G e n).symm =
      zNQuot.congrLinear p H e.symm n := by
  ext x
  cases x with
  | ofMul q =>
      simp [zNQuot.congrLinear, zNQuot.mapLinear]

/-- The inverse prime-linear layer-kernel equivalence is induced by the inverse automorphism. -/
@[simp] theorem zLKern.congrLinear_symm
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    (zLKern.congrLinear p G e n).symm =
      zLKern.congrLinear p G e.symm n := by
  ext x
  cases x with
  | ofMul y =>
      simp [zLKern.congrLinear, zLKern.mapLinear,
        zLKern.mapAdd]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise form of the automorphism action on the first Zassenhaus additive quotient. -/
@[simp] theorem zTAdditi.lin_aut_mapapply
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G e x =
      zTAdditi.congrLinear p G e x := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The first-layer linear equivalence intertwines the automorphism actions on the
Zassenhaus layer kernel and on `G/Z₂`. -/
theorem linear_congr_naturality
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) :
    (zassenhausLinearEquiv p G).toLinearMap.comp
        (zLKern.congrLinear p G e 1).toLinearMap =
      (zTAdditi.congrLinear p G e).toLinearMap.comp
        (zassenhausLinearEquiv p G).toLinearMap := by
  simpa [zLKern.congrLinear, zTAdditi.congrLinear]
    using (zassenhaus_linear_naturality (p := p) (G := G)
      (φ := e.toMonoidHom))

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise intertwining form for the first Zassenhaus layer equivalence and automorphisms. -/
@[simp] theorem zassenhaus_linear_congr
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G)
    (x : Additive (zLKern p G 1)) :
    zassenhausLinearEquiv p G
        (zLKern.congrLinear p G e 1 x) =
      zTAdditi.congrLinear p G e
        (zassenhausLinearEquiv p G x) := by
  have h := congrArg (fun f => f x)
    (linear_congr_naturality (p := p) G e)
  simpa [LinearMap.comp_apply] using h

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Equivalence-level intertwining of first Zassenhaus layer and quotient automorphism actions. -/
theorem linear_congr_trans
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) :
    (zLKern.congrLinear p G e 1).trans
        (zassenhausLinearEquiv p G) =
      (zassenhausLinearEquiv p G).trans
        (zTAdditi.congrLinear p G e) := by
  ext x
  exact zassenhaus_linear_congr (p := p) G e x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The first Zassenhaus quotient automorphism action sends the identity
automorphism to identity. -/
@[simp] theorem zTAdditi.lin_aut_mapone
    (G : Type*) [Group G] :
    zTAdditi.linearAutMap p G 1 = 1 :=
  map_one (zTAdditi.linearAutMap p G)

/-- The first Zassenhaus quotient automorphism action preserves multiplication. -/
@[simp] theorem zTAdditi.lin_aut_mapmul
    (G : Type*) [Group G] (e f : MulAut G) :
    zTAdditi.linearAutMap p G (e * f) =
      zTAdditi.linearAutMap p G e *
        zTAdditi.linearAutMap p G f :=
  map_mul (zTAdditi.linearAutMap p G) e f

/-- Pointwise multiplication law for the first Zassenhaus quotient automorphism action. -/
@[simp] theorem zTAdditi.lin_autmap_mulapply
    (G : Type*) [Group G] (e f : MulAut G) (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G (e * f) x =
      zTAdditi.linearAutMap p G e
        (zTAdditi.linearAutMap p G f x) := by
  simp [zTAdditi.lin_aut_mapmul]

/-- Pointwise identity law for the first Zassenhaus quotient automorphism action. -/
@[simp] theorem zTAdditi.lin_autmap_oneapply
    (G : Type*) [Group G] (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G 1 x = x := by
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse law for the first Zassenhaus quotient automorphism action. -/
@[simp] theorem zTAdditi.lin_aut_mapinv
    (G : Type*) [Group G] (e : MulAut G) :
    zTAdditi.linearAutMap p G e⁻¹ =
      (zTAdditi.linearAutMap p G e)⁻¹ :=
  map_inv (zTAdditi.linearAutMap p G) e

/-- Pointwise inverse cancellation for the first Zassenhaus quotient action. -/
@[simp] theorem zTAdditi.linaut_mapinv_applyself
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G e⁻¹
        (zTAdditi.linearAutMap p G e x) = x := by
  simpa [zTAdditi.lin_aut_mapinv]
    using LinearEquiv.left_inv (zTAdditi.linearAutMap p G e) x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Right inverse cancellation for the first Zassenhaus quotient action. -/
@[simp] theorem zTAdditi.linaut_mapapply_invself
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G e
        (zTAdditi.linearAutMap p G e⁻¹ x) = x := by
  rw [zTAdditi.lin_aut_mapinv]
  exact LinearEquiv.right_inv (zTAdditi.linearAutMap p G e) x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Applying a prime-linear consecutive quotient congruence and then its inverse cancels. -/
@[simp] theorem zNQuot.congr_linsymm_applyself
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p H e.symm n
        (zNQuot.congrLinear p G e n x) = x := by
  simpa [zNQuot.congrLinear_symm]
    using LinearEquiv.left_inv (zNQuot.congrLinear p G e n) x

/-- Applying the inverse prime-linear consecutive quotient congruence and then
the original cancels. -/
@[simp] theorem zNQuot.congr_linapply_symmself
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : Additive (zSubgro p H n ⧸ zNTerm p H n)) :
    zNQuot.congrLinear p G e n
        (zNQuot.congrLinear p H e.symm n x) = x := by
  simpa [zNQuot.congrLinear_symm]
    using LinearEquiv.right_inv (zNQuot.congrLinear p G e n) x

/-- Applying a prime-linear layer automorphism and then its inverse cancels. -/
@[simp] theorem zLKern.congr_linsymm_applyself
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G e.symm n
        (zLKern.congrLinear p G e n x) = x := by
  simpa [zLKern.congrLinear_symm]
    using LinearEquiv.left_inv (zLKern.congrLinear p G e n) x

/-- Applying the inverse prime-linear layer automorphism and then the original cancels. -/
@[simp] theorem zLKern.congr_linapply_symmself
    [Fact p.Prime] (G : Type*) [Group G] (e : MulAut G) (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G e n
        (zLKern.congrLinear p G e.symm n x) = x := by
  simpa [zLKern.congrLinear_symm]
    using LinearEquiv.right_inv (zLKern.congrLinear p G e n) x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Applying a Zassenhaus quotient congruence and then its inverse cancels. -/
@[simp] theorem zQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zQuot p G n) :
    zQuot.congr p H e.symm n
        (zQuot.congr p G e n x) = x := by
  rw [← zQuot.congr_symm (p := p) (G := G) e n]
  exact (zQuot.congr p G e n).left_inv x

/-- Applying the inverse Zassenhaus quotient congruence and then the original cancels. -/
@[simp] theorem zQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zQuot p H n) :
    zQuot.congr p G e n
        (zQuot.congr p H e.symm n x) = x := by
  rw [← zQuot.congr_symm (p := p) (G := G) e n]
  exact (zQuot.congr p G e n).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Consecutive Zassenhaus quotient congruence followed by its inverse cancels. -/
@[simp] theorem zNQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.congr p H e.symm n
        (zNQuot.congr p G e n x) = x := by
  rw [← zNQuot.congr_symm (p := p) (G := G) e n]
  exact (zNQuot.congr p G e n).left_inv x

/-- Inverse consecutive Zassenhaus quotient congruence followed by the original cancels. -/
@[simp] theorem zNQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.congr p G e n
        (zNQuot.congr p H e.symm n x) = x := by
  rw [← zNQuot.congr_symm (p := p) (G := G) e n]
  exact (zNQuot.congr p G e n).right_inv x

/-- Zassenhaus layer-kernel congruence followed by its inverse cancels. -/
@[simp] theorem zLKern.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zLKern p G n) :
    zLKern.congr p H e.symm n
        (zLKern.congr p G e n x) = x := by
  rw [← zLKern.congr_symm (p := p) (G := G) e n]
  exact (zLKern.congr p G e n).left_inv x

/-- Inverse Zassenhaus layer-kernel congruence followed by the original cancels. -/
@[simp] theorem zLKern.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zLKern p H n) :
    zLKern.congr p G e n
        (zLKern.congr p H e.symm n x) = x := by
  rw [← zLKern.congr_symm (p := p) (G := G) e n]
  exact (zLKern.congr p G e n).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Zassenhaus term-quotient congruence followed by its inverse cancels. -/
@[simp] theorem zTQuot.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTQuot.congr p H e.symm hmn
        (zTQuot.congr p G e hmn x) = x := by
  rw [← zTQuot.congr_symm (p := p) (G := G) e hmn]
  exact (zTQuot.congr p G e hmn).left_inv x

/-- Inverse Zassenhaus term-quotient congruence followed by the original cancels. -/
@[simp] theorem zTQuot.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zTQuot.congr p G e hmn
        (zTQuot.congr p H e.symm hmn x) = x := by
  rw [← zTQuot.congr_symm (p := p) (G := G) e hmn]
  exact (zTQuot.congr p G e hmn).right_inv x

/-- Zassenhaus transition-kernel congruence followed by its inverse cancels. -/
@[simp] theorem zTKern.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.congr p H e.symm hmn
        (zTKern.congr p G e hmn x) = x := by
  rw [← zTKern.congr_symm (p := p) (G := G) e hmn]
  exact (zTKern.congr p G e hmn).left_inv x

/-- Inverse Zassenhaus transition-kernel congruence followed by the original cancels. -/
@[simp] theorem zTKern.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p H hmn)) :
    zTKern.congr p G e hmn
        (zTKern.congr p H e.symm hmn x) = x := by
  rw [← zTKern.congr_symm (p := p) (G := G) e hmn]
  exact (zTKern.congr p G e hmn).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Zassenhaus subgroup congruence followed by its inverse cancels. -/
@[simp] theorem zSubgro.congr_symm_applyself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zSubgro p G n) :
    zSubgro.congr p H e.symm n
        (zSubgro.congr p G e n x) = x := by
  rw [← zSubgro.congr_symm (p := p) (G := G) e n]
  exact (zSubgro.congr p G e n).left_inv x

/-- Inverse Zassenhaus subgroup congruence followed by the original cancels. -/
@[simp] theorem zSubgro.congr_apply_symmself
    (G H : Type*) [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zSubgro p H n) :
    zSubgro.congr p G e n
        (zSubgro.congr p H e.symm n x) = x := by
  rw [← zSubgro.congr_symm (p := p) (G := G) e n]
  exact (zSubgro.congr p G e n).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise composition law for Zassenhaus subgroup congruences. -/
@[simp] theorem zSubgro.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : zSubgro p A n) :
    zSubgro.congr p B f n (zSubgro.congr p A e n x) =
      zSubgro.congr p A (e.trans f) n x := by
  change ((zSubgro.congr p A e n).trans
      (zSubgro.congr p B f n)) x = _
  rw [zSubgro.congr_trans]

/-- Identity Zassenhaus subgroup congruence acts pointwise as the identity. -/
@[simp] theorem zSubgro.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : zSubgro p A n) :
    zSubgro.congr p A (MulEquiv.refl A) n x = x := by
  rw [zSubgro.congr_refl]
  rfl

/-- Pointwise composition law for ordinary Zassenhaus quotient congruences. -/
@[simp] theorem zQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : zQuot p A n) :
    zQuot.congr p B f n (zQuot.congr p A e n x) =
      zQuot.congr p A (e.trans f) n x := by
  change ((zQuot.congr p A e n).trans
      (zQuot.congr p B f n)) x = _
  rw [zQuot.congr_trans]

/-- Identity ordinary Zassenhaus quotient congruence acts pointwise as the identity. -/
@[simp] theorem zQuot.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : zQuot p A n) :
    zQuot.congr p A (MulEquiv.refl A) n x = x := by
  rw [zQuot.congr_refl]
  rfl

/-- Pointwise composition law for consecutive Zassenhaus quotient congruences. -/
@[simp] theorem zNQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ)
    (x : zSubgro p A n ⧸ zNTerm p A n) :
    zNQuot.congr p B f n
        (zNQuot.congr p A e n x) =
      zNQuot.congr p A (e.trans f) n x := by
  change ((zNQuot.congr p A e n).trans
      (zNQuot.congr p B f n)) x = _
  rw [zNQuot.congr_trans]

/-- Identity consecutive Zassenhaus quotient congruence acts pointwise as the identity. -/
@[simp] theorem zNQuot.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ)
    (x : zSubgro p A n ⧸ zNTerm p A n) :
    zNQuot.congr p A (MulEquiv.refl A) n x = x := by
  rw [zNQuot.congr_refl]
  rfl

/-- Pointwise composition law for Zassenhaus layer-kernel congruences. -/
@[simp] theorem zLKern.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ) (x : zLKern p A n) :
    zLKern.congr p B f n (zLKern.congr p A e n x) =
      zLKern.congr p A (e.trans f) n x := by
  change ((zLKern.congr p A e n).trans
      (zLKern.congr p B f n)) x = _
  rw [zLKern.congr_trans]

/-- Identity Zassenhaus layer-kernel congruence acts pointwise as the identity. -/
@[simp] theorem zLKern.congr_refl_apply
    {A : Type*} [Group A] (n : ℕ) (x : zLKern p A n) :
    zLKern.congr p A (MulEquiv.refl A) n x = x := by
  rw [zLKern.congr_refl]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise composition law for arbitrary Zassenhaus term-quotient congruences. -/
@[simp] theorem zTQuot.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p A m ⧸ zTSubgro p A hmn) :
    zTQuot.congr p B f hmn
        (zTQuot.congr p A e hmn x) =
      zTQuot.congr p A (e.trans f) hmn x := by
  change ((zTQuot.congr p A e hmn).trans
      (zTQuot.congr p B f hmn)) x = _
  rw [zTQuot.congr_trans]

/-- Identity arbitrary Zassenhaus term-quotient congruence acts pointwise as identity. -/
@[simp] theorem zTQuot.congr_refl_apply
    {A : Type*} [Group A] {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p A m ⧸ zTSubgro p A hmn) :
    zTQuot.congr p A (MulEquiv.refl A) hmn x = x := by
  rw [zTQuot.congr_refl]
  rfl

/-- Pointwise composition law for Zassenhaus transition-kernel congruences. -/
@[simp] theorem zTKern.congr_trans_apply
    {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p A hmn)) :
    zTKern.congr p B f hmn
        (zTKern.congr p A e hmn x) =
      zTKern.congr p A (e.trans f) hmn x := by
  change ((zTKern.congr p A e hmn).trans
      (zTKern.congr p B f hmn)) x = _
  rw [zTKern.congr_trans]

/-- Identity Zassenhaus transition-kernel congruence acts pointwise as identity. -/
@[simp] theorem zTKern.congr_refl_apply
    {A : Type*} [Group A] {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p A hmn)) :
    zTKern.congr p A (MulEquiv.refl A) hmn x = x := by
  rw [zTKern.congr_refl]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise composition law for prime-linear consecutive Zassenhaus congruences. -/
@[simp] theorem zNQuot.congr_lin_transapply
    [Fact p.Prime] {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) (n : ℕ)
    (x : Additive (zSubgro p A n ⧸ zNTerm p A n)) :
    zNQuot.congrLinear p B f n
        (zNQuot.congrLinear p A e n x) =
      zNQuot.congrLinear p A (e.trans f) n x := by
  change ((zNQuot.congrLinear p A e n).trans
      (zNQuot.congrLinear p B f n)) x = _
  rw [zNQuot.congrLinear_trans]

/-- Identity prime-linear consecutive Zassenhaus congruence acts pointwise as identity. -/
@[simp] theorem zNQuot.congr_lin_reflapply
    [Fact p.Prime] {A : Type*} [Group A] (n : ℕ)
    (x : Additive (zSubgro p A n ⧸ zNTerm p A n)) :
    zNQuot.congrLinear p A (MulEquiv.refl A) n x = x := by
  rw [zNQuot.congrLinear_refl]
  rfl

/-- Pointwise composition law for prime-linear Zassenhaus layer automorphisms. -/
@[simp] theorem zLKern.congr_lin_transapply
    [Fact p.Prime] (G : Type*) [Group G] (e f : MulAut G) (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G f n
        (zLKern.congrLinear p G e n x) =
      zLKern.congrLinear p G (e.trans f) n x := by
  change ((zLKern.congrLinear p G e n).trans
      (zLKern.congrLinear p G f n)) x = _
  rw [zLKern.congrLinear_trans]

/-- Identity prime-linear Zassenhaus layer automorphism acts pointwise as identity. -/
@[simp] theorem zLKern.congr_lin_reflapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G (MulEquiv.refl G) n x = x := by
  rw [zLKern.congrLinear_refl]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism action on Zassenhaus quotients sends identity to identity. -/
@[simp] theorem zQuot.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    zQuot.mulAutMap p G n 1 = 1 :=
  map_one (zQuot.mulAutMap p G n)

/-- Automorphism action on Zassenhaus quotients preserves multiplication. -/
@[simp] theorem zQuot.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    zQuot.mulAutMap p G n (e * f) =
      zQuot.mulAutMap p G n e * zQuot.mulAutMap p G n f :=
  map_mul (zQuot.mulAutMap p G n) e f

/-- Pointwise multiplication law for the automorphism action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) (x : zQuot p G n) :
    zQuot.mulAutMap p G n (e * f) x =
      zQuot.mulAutMap p G n e (zQuot.mulAutMap p G n f x) := by
  simp [zQuot.mul_aut_mapmul]

/-- Pointwise identity law for the automorphism action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ) (x : zQuot p G n) :
    zQuot.mulAutMap p G n 1 x = x := by
  simp

/-- Automorphism action on consecutive Zassenhaus quotients sends identity to identity. -/
@[simp] theorem zNQuot.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    zNQuot.mulAutMap p G n 1 = 1 :=
  map_one (zNQuot.mulAutMap p G n)

/-- Automorphism action on consecutive Zassenhaus quotients preserves multiplication. -/
@[simp] theorem zNQuot.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    zNQuot.mulAutMap p G n (e * f) =
      zNQuot.mulAutMap p G n e *
        zNQuot.mulAutMap p G n f :=
  map_mul (zNQuot.mulAutMap p G n) e f

/-- Pointwise multiplication law for consecutive Zassenhaus quotient automorphism action. -/
@[simp] theorem zNQuot.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.mulAutMap p G n (e * f) x =
      zNQuot.mulAutMap p G n e
        (zNQuot.mulAutMap p G n f x) := by
  simp [zNQuot.mul_aut_mapmul]

/-- Pointwise identity law for consecutive Zassenhaus quotient automorphism action. -/
@[simp] theorem zNQuot.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.mulAutMap p G n 1 x = x := by
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism action on Zassenhaus layer kernels sends identity to identity. -/
@[simp] theorem zLKern.mul_aut_mapone
    (G : Type*) [Group G] (n : ℕ) :
    zLKern.mulAutMap p G n 1 = 1 :=
  map_one (zLKern.mulAutMap p G n)

/-- Automorphism action on Zassenhaus layer kernels preserves multiplication. -/
@[simp] theorem zLKern.mul_aut_mapmul
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    zLKern.mulAutMap p G n (e * f) =
      zLKern.mulAutMap p G n e *
        zLKern.mulAutMap p G n f :=
  map_mul (zLKern.mulAutMap p G n) e f

/-- Pointwise multiplication law for Zassenhaus layer-kernel automorphism action. -/
@[simp] theorem zLKern.mul_autmap_mulapply
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : zLKern p G n) :
    zLKern.mulAutMap p G n (e * f) x =
      zLKern.mulAutMap p G n e
        (zLKern.mulAutMap p G n f x) := by
  simp [zLKern.mul_aut_mapmul]

/-- Pointwise identity law for Zassenhaus layer-kernel automorphism action. -/
@[simp] theorem zLKern.mul_autmap_oneapply
    (G : Type*) [Group G] (n : ℕ) (x : zLKern p G n) :
    zLKern.mulAutMap p G n 1 x = x := by
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism action on arbitrary Zassenhaus term quotients sends identity to identity. -/
@[simp] theorem zTQuot.mul_aut_mapone
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    zTQuot.mulAutMap p G hmn 1 = 1 :=
  map_one (zTQuot.mulAutMap p G hmn)

/-- Automorphism action on arbitrary Zassenhaus term quotients preserves multiplication. -/
@[simp] theorem zTQuot.mul_aut_mapmul
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    zTQuot.mulAutMap p G hmn (e * f) =
      zTQuot.mulAutMap p G hmn e *
        zTQuot.mulAutMap p G hmn f :=
  map_mul (zTQuot.mulAutMap p G hmn) e f

/-- Pointwise multiplication law for arbitrary Zassenhaus term quotient actions. -/
@[simp] theorem zTQuot.mul_autmap_mulapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTQuot.mulAutMap p G hmn (e * f) x =
      zTQuot.mulAutMap p G hmn e
        (zTQuot.mulAutMap p G hmn f x) := by
  simp [zTQuot.mul_aut_mapmul]

/-- Pointwise identity law for arbitrary Zassenhaus term quotient actions. -/
@[simp] theorem zTQuot.mul_autmap_oneapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTQuot.mulAutMap p G hmn 1 x = x := by
  simp

/-- Automorphism action on Zassenhaus transition kernels sends identity to identity. -/
@[simp] theorem zTKern.mul_aut_mapone
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    zTKern.mulAutMap p G hmn 1 = 1 :=
  map_one (zTKern.mulAutMap p G hmn)

/-- Automorphism action on Zassenhaus transition kernels preserves multiplication. -/
@[simp] theorem zTKern.mul_aut_mapmul
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    zTKern.mulAutMap p G hmn (e * f) =
      zTKern.mulAutMap p G hmn e *
        zTKern.mulAutMap p G hmn f :=
  map_mul (zTKern.mulAutMap p G hmn) e f

/-- Pointwise multiplication law for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mul_autmap_mulapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.mulAutMap p G hmn (e * f) x =
      zTKern.mulAutMap p G hmn e
        (zTKern.mulAutMap p G hmn f x) := by
  simp [zTKern.mul_aut_mapmul]

/-- Pointwise identity law for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mul_autmap_oneapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.mulAutMap p G hmn 1 x = x := by
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse law for automorphism action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zQuot.mulAutMap p G n e⁻¹ =
      (zQuot.mulAutMap p G n e)⁻¹ :=
  map_inv (zQuot.mulAutMap p G n) e

/-- Left inverse cancellation for automorphism action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zQuot p G n) :
    zQuot.mulAutMap p G n e⁻¹ (zQuot.mulAutMap p G n e x) = x := by
  simp [zQuot.mul_aut_mapinv]

/-- Right inverse cancellation for automorphism action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zQuot p G n) :
    zQuot.mulAutMap p G n e (zQuot.mulAutMap p G n e⁻¹ x) = x := by
  rw [zQuot.mul_aut_mapinv]
  exact (zQuot.mulAutMap p G n e).right_inv x

/-- Inverse law for automorphism action on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zNQuot.mulAutMap p G n e⁻¹ =
      (zNQuot.mulAutMap p G n e)⁻¹ :=
  map_inv (zNQuot.mulAutMap p G n) e

/-- Left inverse cancellation for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.mulAutMap p G n e⁻¹
        (zNQuot.mulAutMap p G n e x) = x := by
  simp [zNQuot.mul_aut_mapinv]

/-- Right inverse cancellation for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.mulAutMap p G n e
        (zNQuot.mulAutMap p G n e⁻¹ x) = x := by
  rw [zNQuot.mul_aut_mapinv]
  exact (zNQuot.mulAutMap p G n e).right_inv x

/-- Inverse law for automorphism action on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mul_aut_mapinv
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zLKern.mulAutMap p G n e⁻¹ =
      (zLKern.mulAutMap p G n e)⁻¹ :=
  map_inv (zLKern.mulAutMap p G n) e

/-- Left inverse cancellation for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapinv_applyself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zLKern p G n) :
    zLKern.mulAutMap p G n e⁻¹
        (zLKern.mulAutMap p G n e x) = x := by
  simpa [zLKern.mul_aut_mapinv]
    using (zLKern.mulAutMap p G n e).left_inv x

/-- Right inverse cancellation for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapapply_invself
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zLKern p G n) :
    zLKern.mulAutMap p G n e
        (zLKern.mulAutMap p G n e⁻¹ x) = x := by
  rw [zLKern.mul_aut_mapinv]
  exact (zLKern.mulAutMap p G n e).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse law for automorphism action on arbitrary Zassenhaus term quotients. -/
@[simp] theorem zTQuot.mul_aut_mapinv
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTQuot.mulAutMap p G hmn e⁻¹ =
      (zTQuot.mulAutMap p G hmn e)⁻¹ :=
  map_inv (zTQuot.mulAutMap p G hmn) e

/-- Left inverse cancellation for arbitrary Zassenhaus term quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapinv_applyself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTQuot.mulAutMap p G hmn e⁻¹
        (zTQuot.mulAutMap p G hmn e x) = x := by
  simpa [zTQuot.mul_aut_mapinv]
    using (zTQuot.mulAutMap p G hmn e).left_inv x

/-- Right inverse cancellation for arbitrary Zassenhaus term quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapapply_invself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zTQuot.mulAutMap p G hmn e
        (zTQuot.mulAutMap p G hmn e⁻¹ x) = x := by
  rw [zTQuot.mul_aut_mapinv]
  exact (zTQuot.mulAutMap p G hmn e).right_inv x

/-- Inverse law for automorphism action on Zassenhaus transition kernels. -/
@[simp] theorem zTKern.mul_aut_mapinv
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTKern.mulAutMap p G hmn e⁻¹ =
      (zTKern.mulAutMap p G hmn e)⁻¹ :=
  map_inv (zTKern.mulAutMap p G hmn) e

/-- Left inverse cancellation for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapinv_applyself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.mulAutMap p G hmn e⁻¹
        (zTKern.mulAutMap p G hmn e x) = x := by
  simpa [zTKern.mul_aut_mapinv]
    using (zTKern.mulAutMap p G hmn e).left_inv x

/-- Right inverse cancellation for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapapply_invself
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    zTKern.mulAutMap p G hmn e
        (zTKern.mulAutMap p G hmn e⁻¹ x) = x := by
  rw [zTKern.mul_aut_mapinv]
  exact (zTKern.mulAutMap p G hmn e).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Unfold the automorphism action on an ordinary Zassenhaus quotient. -/
@[simp] theorem zQuot.mul_aut_mapapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zQuot p G n) :
    zQuot.mulAutMap p G n e x =
      zQuot.congr p G e n x := rfl

/-- Unfold the automorphism action on a consecutive Zassenhaus quotient. -/
@[simp] theorem zNQuot.mul_aut_mapapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.mulAutMap p G n e x =
      zNQuot.congr p G e n x := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Symmetric orientation of the inverse action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zQuot.mulAutMap p G n e).symm =
      zQuot.mulAutMap p G n e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.mulAutMap p G n e).symm =
      zNQuot.mulAutMap p G n e⁻¹ := by
  rfl

/-- Symmetric orientation of the inverse action on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mul_aut_mapsymm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.mulAutMap p G n e).symm =
      zLKern.mulAutMap p G n e⁻¹ := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Symmetric orientation of the inverse action on arbitrary Zassenhaus term quotients. -/
@[simp] theorem zTQuot.mul_aut_mapsymm
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTQuot.mulAutMap p G hmn e).symm =
      zTQuot.mulAutMap p G hmn e⁻¹ := rfl

/-- Symmetric orientation of the inverse action on Zassenhaus transition kernels. -/
@[simp] theorem zTKern.mul_aut_mapsymm
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTKern.mulAutMap p G hmn e).symm =
      zTKern.mulAutMap p G hmn e⁻¹ := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise form of the symmetric inverse action on Zassenhaus quotients. -/
@[simp] theorem zQuot.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zQuot p G n) :
    (zQuot.mulAutMap p G n e).symm x =
      zQuot.mulAutMap p G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.mulAutMap p G n e).symm x =
      zNQuot.mulAutMap p G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mul_autmap_symmapply
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (x : zLKern p G n) :
    (zLKern.mulAutMap p G n e).symm x =
      zLKern.mulAutMap p G n e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on arbitrary Zassenhaus term quotients. -/
@[simp] theorem zTQuot.mul_autmap_symmapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (zTQuot.mulAutMap p G hmn e).symm x =
      zTQuot.mulAutMap p G hmn e⁻¹ x := rfl

/-- Pointwise form of the symmetric inverse action on Zassenhaus transition kernels. -/
@[simp] theorem zTKern.mul_autmap_symmapply
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (zTKern.mulAutMap p G hmn e).symm x =
      zTKern.mulAutMap p G hmn e⁻¹ x := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Coercion of the automorphism action on Zassenhaus quotients to its underlying map. -/
@[simp] theorem zQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zQuot.mulAutMap p G n e).toMonoidHom =
      zQuot.map p G e.toMonoidHom n := rfl

/-- Coercion of the automorphism action on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.mulAutMap p G n e).toMonoidHom =
      zNQuot.map p G e.toMonoidHom n := rfl

/-- Coercion of the automorphism action on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mul_autmap_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.mulAutMap p G n e).toMonoidHom =
      zLKern.map p G e.toMonoidHom n := rfl

/-- Coercion of a term-quotient congruence to its underlying homomorphism. -/
@[simp] theorem zTQuot.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.congr p G e hmn).toMonoidHom =
      zassenhausTerm p G e.toMonoidHom hmn := rfl

/-- Coercion of the automorphism action on arbitrary Zassenhaus term quotients. -/
@[simp] theorem zTQuot.mul_autmap_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTQuot.mulAutMap p G hmn e).toMonoidHom =
      zassenhausTerm p G e.toMonoidHom hmn := rfl

/-- Coercion of a transition-kernel congruence to its underlying homomorphism. -/
@[simp] theorem zTKern.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.congr p G e hmn).toMonoidHom =
      transitionKernel p G e.toMonoidHom hmn := rfl

/-- Coercion of the automorphism action on Zassenhaus transition kernels. -/
@[simp] theorem zTKern.mul_autmap_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTKern.mulAutMap p G hmn e).toMonoidHom =
      transitionKernel p G e.toMonoidHom hmn := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level left inverse for Zassenhaus quotient automorphism actions. -/
@[simp] theorem zQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zQuot.mulAutMap p G n e⁻¹).toMonoidHom).comp
        (zQuot.mulAutMap p G n e).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level right inverse for Zassenhaus quotient automorphism actions. -/
@[simp] theorem zQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zQuot.mulAutMap p G n e).toMonoidHom).comp
        (zQuot.mulAutMap p G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level left inverse for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zNQuot.mulAutMap p G n e⁻¹).toMonoidHom).comp
        (zNQuot.mulAutMap p G n e).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level right inverse for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zNQuot.mulAutMap p G n e).toMonoidHom).comp
        (zNQuot.mulAutMap p G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level left inverse for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zLKern.mulAutMap p G n e⁻¹).toMonoidHom).comp
        (zLKern.mulAutMap p G n e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, zLKern.mul_aut_mapsymm]
    using (zLKern.mulAutMap p G n e).left_inv x

/-- Hom-level right inverse for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    ((zLKern.mulAutMap p G n e).toMonoidHom).comp
        (zLKern.mulAutMap p G n e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level left inverse for arbitrary Zassenhaus term-quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((zTQuot.mulAutMap p G hmn e⁻¹).toMonoidHom).comp
        (zTQuot.mulAutMap p G hmn e).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level right inverse for arbitrary Zassenhaus term-quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((zTQuot.mulAutMap p G hmn e).toMonoidHom).comp
        (zTQuot.mulAutMap p G hmn e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level left inverse for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapinv_compmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((zTKern.mulAutMap p G hmn e⁻¹).toMonoidHom).comp
        (zTKern.mulAutMap p G hmn e).toMonoidHom = MonoidHom.id _ := by
  ext x
  simpa [MonoidHom.comp_apply, zTKern.mul_aut_mapsymm]
    using (zTKern.mulAutMap p G hmn e).left_inv x

/-- Hom-level right inverse for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapcomp_invmonoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((zTKern.mulAutMap p G hmn e).toMonoidHom).comp
        (zTKern.mulAutMap p G hmn e⁻¹).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level identity for Zassenhaus quotient automorphism actions. -/
@[simp] theorem zQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zQuot.mulAutMap p G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for Zassenhaus quotient automorphism actions. -/
@[simp] theorem zQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((zQuot.mulAutMap p G n e).toMonoidHom).comp
        (zQuot.mulAutMap p G n f).toMonoidHom =
      (zQuot.mulAutMap p G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zNQuot.mulAutMap p G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((zNQuot.mulAutMap p G n e).toMonoidHom).comp
        (zNQuot.mulAutMap p G n f).toMonoidHom =
      (zNQuot.mulAutMap p G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapone_monoidhom
    (G : Type*) [Group G] (n : ℕ) :
    (zLKern.mulAutMap p G n 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    ((zLKern.mulAutMap p G n e).toMonoidHom).comp
        (zLKern.mulAutMap p G n f).toMonoidHom =
      (zLKern.mulAutMap p G n (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for arbitrary Zassenhaus term-quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapone_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (zTQuot.mulAutMap p G hmn 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for arbitrary Zassenhaus term-quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    ((zTQuot.mulAutMap p G hmn e).toMonoidHom).comp
        (zTQuot.mulAutMap p G hmn f).toMonoidHom =
      (zTQuot.mulAutMap p G hmn (e * f)).toMonoidHom := by
  ext x; simp

/-- Hom-level identity for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapone_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    (zTKern.mulAutMap p G hmn 1).toMonoidHom = MonoidHom.id _ := by
  ext x; simp

/-- Hom-level composition for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapcomp_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    ((zTKern.mulAutMap p G hmn e).toMonoidHom).comp
        (zTKern.mulAutMap p G hmn f).toMonoidHom =
      (zTKern.mulAutMap p G hmn (e * f)).toMonoidHom := by
  ext x; simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Symmetric orientation for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.lin_aut_mapsymm
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.linearAutMap p G e).symm =
      zTAdditi.linearAutMap p G e⁻¹ := rfl

/-- Pointwise symmetric orientation for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.lin_autmap_symmapply
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    (zTAdditi.linearAutMap p G e).symm x =
      zTAdditi.linearAutMap p G e⁻¹ x := rfl

/-- Underlying linear map of the first Zassenhaus additive automorphism action. -/
@[simp] theorem zTAdditi.lin_autmap_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.linearAutMap p G e).toLinearMap =
      zTAdditi.mapLinear p G e.toMonoidHom := rfl

/-- Hom-level identity for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.linaut_mapone_linmap
    (G : Type*) [Group G] :
    (zTAdditi.linearAutMap p G 1).toLinearMap = LinearMap.id := by
  ext x; simp

/-- Hom-level composition for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.linaut_mapcomp_linmap
    (G : Type*) [Group G] (e f : MulAut G) :
    (zTAdditi.linearAutMap p G e).toLinearMap.comp
        (zTAdditi.linearAutMap p G f).toLinearMap =
      (zTAdditi.linearAutMap p G (e * f)).toLinearMap := by
  ext x; simp

/-- Left inverse at the underlying-linear-map level for the first Zassenhaus action. -/
@[simp] theorem zTAdditi.linaut_mapinv_complinmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.linearAutMap p G e⁻¹).toLinearMap.comp
        (zTAdditi.linearAutMap p G e).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, zTAdditi.lin_aut_mapsymm]
    using (zTAdditi.linearAutMap p G e).left_inv x

/-- Right inverse at the underlying-linear-map level for the first Zassenhaus action. -/
@[simp] theorem zTAdditi.linaut_mapcomp_invlinmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.linearAutMap p G e).toLinearMap.comp
        (zTAdditi.linearAutMap p G e⁻¹).toLinearMap = LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply, zTAdditi.lin_aut_mapsymm]
    using (zTAdditi.linearAutMap p G e).right_inv x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Symmetric orientation for the defining linear equivalence on the first Zassenhaus quotient. -/
@[simp] theorem zTAdditi.congrLinear_symm
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.congrLinear p G e).symm =
      zTAdditi.congrLinear p G e.symm := rfl

/-- Pointwise symmetric orientation for the defining linear equivalence on the first
Zassenhaus quotient. -/
@[simp] theorem zTAdditi.congr_lin_symmapply
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    (zTAdditi.congrLinear p G e).symm x =
      zTAdditi.congrLinear p G e.symm x := rfl

/-- Underlying-map form of the symmetric orientation for the first Zassenhaus quotient. -/
@[simp] theorem zTAdditi.congr_linsymm_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.congrLinear p G e).symm.toLinearMap =
      (zTAdditi.congrLinear p G e.symm).toLinearMap := by
  rw [zTAdditi.congrLinear_symm]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Hom-level identity for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congr_linone_linmap
    (G : Type*) [Group G] :
    (zTAdditi.congrLinear p G 1).toLinearMap = LinearMap.id := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.linaut_mapone_linmap (p := p) G)

/-- Hom-level composition for the defining first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congr_lincomp_linmap
    (G : Type*) [Group G] (e f : MulAut G) :
    (zTAdditi.congrLinear p G e).toLinearMap.comp
        (zTAdditi.congrLinear p G f).toLinearMap =
      (zTAdditi.congrLinear p G (e * f)).toLinearMap := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.linaut_mapcomp_linmap (p := p) G e f)

/-- Left inverse at the underlying-linear-map level for first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congrlin_invcomp_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.congrLinear p G e⁻¹).toLinearMap.comp
        (zTAdditi.congrLinear p G e).toLinearMap = LinearMap.id := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.linaut_mapinv_complinmap (p := p) G e)

/-- Right inverse at the underlying-linear-map level for first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congrlin_compinv_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.congrLinear p G e).toLinearMap.comp
        (zTAdditi.congrLinear p G e⁻¹).toLinearMap = LinearMap.id := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.linaut_mapcomp_invlinmap (p := p) G e)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Equivalence-level identity for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congrLinear_one
    (G : Type*) [Group G] :
    zTAdditi.congrLinear p G 1 = 1 := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.lin_aut_mapone (p := p) G)

/-- Equivalence-level multiplication law for the defining first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congrLinear_mul
    (G : Type*) [Group G] (e f : MulAut G) :
    zTAdditi.congrLinear p G (e * f) =
      zTAdditi.congrLinear p G e *
        zTAdditi.congrLinear p G f := by
  simpa [zTAdditi.linearAutMap] using
    (zTAdditi.lin_aut_mapmul (p := p) G e f)

/-- Pointwise identity law for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congr_lin_oneapply
    (G : Type*) [Group G] (x : zTAdditi p G) :
    zTAdditi.congrLinear p G 1 x = x := by
  simp

/-- Pointwise multiplication law for the defining first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congr_lin_mulapply
    (G : Type*) [Group G] (e f : MulAut G) (x : zTAdditi p G) :
    zTAdditi.congrLinear p G (e * f) x =
      zTAdditi.congrLinear p G e
        (zTAdditi.congrLinear p G f x) := by
  exact
    (zTAdditi.lin_autmap_mulapply (p := p) G e f x)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- MulAut-notation identity law for prime-linear consecutive Zassenhaus congruences. -/
@[simp] theorem zNQuot.congrLinear_one
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    zNQuot.congrLinear p G (1 : MulAut G) n = 1 := by
  change zNQuot.congrLinear p G (MulEquiv.refl G) n =
    LinearEquiv.refl (ZMod p)
      (Additive (zSubgro p G n ⧸ zNTerm p G n))
  exact zNQuot.congrLinear_refl (p := p) G n

/-- MulAut-notation identity law for prime-linear Zassenhaus layer congruences. -/
@[simp] theorem zLKern.congrLinear_one
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    zLKern.congrLinear p G (1 : MulAut G) n = 1 := by
  change zLKern.congrLinear p G (MulEquiv.refl G) n =
    LinearEquiv.refl (ZMod p) (Additive (zLKern p G n))
  exact zLKern.congrLinear_refl (p := p) G n

/-- MulAut-notation multiplication law for prime-linear consecutive Zassenhaus congruences. -/
@[simp] theorem zNQuot.congrLinear_mul
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    zNQuot.congrLinear p G (e * f) n =
      (zNQuot.congrLinear p G f n).trans
        (zNQuot.congrLinear p G e n) := by
  rw [show (e * f : MulAut G) = f.trans e by rfl]
  symm
  exact zNQuot.congrLinear_trans (p := p) G G G f e n

/-- MulAut-notation multiplication law for prime-linear Zassenhaus layer congruences. -/
@[simp] theorem zLKern.congrLinear_mul
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    zLKern.congrLinear p G (e * f) n =
      (zLKern.congrLinear p G f n).trans
        (zLKern.congrLinear p G e n) := by
  rw [show (e * f : MulAut G) = f.trans e by rfl]
  symm
  exact zLKern.congrLinear_trans (p := p) G f e n

/-- Pointwise MulAut-notation identity law for consecutive Zassenhaus congruences. -/
@[simp] theorem zNQuot.congr_lin_oneapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G (1 : MulAut G) n x = x := by
  rw [zNQuot.congrLinear_one]
  rfl

/-- Pointwise MulAut-notation identity law for Zassenhaus layer congruences. -/
@[simp] theorem zLKern.congr_lin_oneapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G (1 : MulAut G) n x = x := by
  rw [zLKern.congrLinear_one]
  rfl

/-- Pointwise MulAut-notation multiplication law for consecutive Zassenhaus congruences. -/
@[simp] theorem zNQuot.congr_lin_mulapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G (e * f) n x =
      zNQuot.congrLinear p G e n
        (zNQuot.congrLinear p G f n x) := by
  rw [show (e * f : MulAut G) = f.trans e by rfl]
  rw [← zNQuot.congrLinear_trans (p := p) G G G f e n]
  rfl

/-- Pointwise MulAut-notation multiplication law for Zassenhaus layer congruences. -/
@[simp] theorem zLKern.congr_lin_mulapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G (e * f) n x =
      zLKern.congrLinear p G e n
        (zLKern.congrLinear p G f n x) := by
  rw [show (e * f : MulAut G) = f.trans e by rfl]
  rw [← zLKern.congrLinear_trans (p := p) G f e n]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Hom-level identity law for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congr_linone_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    (zNQuot.congrLinear p G (1 : MulAut G) n).toLinearMap =
      LinearMap.id := by
  ext x
  exact zNQuot.congr_lin_oneapply (p := p) G n x

/-- Hom-level identity law for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congr_linone_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) :
    (zLKern.congrLinear p G (1 : MulAut G) n).toLinearMap =
      LinearMap.id := by
  ext x
  exact congrArg Subtype.val (congrArg Additive.toMul
    (zLKern.congr_lin_oneapply (p := p) G n x))

/-- Hom-level multiplication law for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congr_linmul_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    (zNQuot.congrLinear p G e n).toLinearMap.comp
        (zNQuot.congrLinear p G f n).toLinearMap =
      (zNQuot.congrLinear p G (e * f) n).toLinearMap := by
  ext x
  exact congrArg Additive.toMul
    (zNQuot.congr_lin_mulapply (p := p) G n e f x).symm

/-- Hom-level multiplication law for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congr_linmul_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e f : MulAut G) :
    (zLKern.congrLinear p G e n).toLinearMap.comp
        (zLKern.congrLinear p G f n).toLinearMap =
      (zLKern.congrLinear p G (e * f) n).toLinearMap := by
  ext x
  exact congrArg Subtype.val (congrArg Additive.toMul
    (zLKern.congr_lin_mulapply (p := p) G n e f x).symm)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Inverse orientation for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congrLinear_inv
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zNQuot.congrLinear p G e⁻¹ n =
      (zNQuot.congrLinear p G e n).symm := by
  rw [zNQuot.congrLinear_symm]
  rfl

/-- Inverse orientation for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congrLinear_inv
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zLKern.congrLinear p G e⁻¹ n =
      (zLKern.congrLinear p G e n).symm := by
  rw [zLKern.congrLinear_symm]
  rfl

/-- Left inverse at the hom level for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congrlin_invcomp_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.congrLinear p G e⁻¹ n).toLinearMap.comp
        (zNQuot.congrLinear p G e n).toLinearMap = LinearMap.id := by
  rw [show (e⁻¹ : MulAut G) = e.symm by rfl]
  rw [← zNQuot.congr_linsymm_linmap (p := p) G G e n]
  exact zNQuot.congrlin_symmcomp_linmap (p := p) G G e n

/-- Right inverse at the hom level for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congrlin_compinv_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.congrLinear p G e n).toLinearMap.comp
        (zNQuot.congrLinear p G e⁻¹ n).toLinearMap = LinearMap.id := by
  rw [show (e⁻¹ : MulAut G) = e.symm by rfl]
  rw [← zNQuot.congr_linsymm_linmap (p := p) G G e n]
  exact zNQuot.congrlin_compsymm_linmap (p := p) G G e n

/-- Left inverse at the hom level for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congrlin_invcomp_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.congrLinear p G e⁻¹ n).toLinearMap.comp
        (zLKern.congrLinear p G e n).toLinearMap = LinearMap.id := by
  rw [show (e⁻¹ : MulAut G) = e.symm by rfl]
  rw [← zLKern.congr_linsymm_linmap (p := p) G e n]
  exact zLKern.congrlin_symmcomp_linmap (p := p) G e n

/-- Right inverse at the hom level for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congrlin_compinv_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.congrLinear p G e n).toLinearMap.comp
        (zLKern.congrLinear p G e⁻¹ n).toLinearMap = LinearMap.id := by
  rw [show (e⁻¹ : MulAut G) = e.symm by rfl]
  rw [← zLKern.congr_linsymm_linmap (p := p) G e n]
  exact zLKern.congrlin_compsymm_linmap (p := p) G e n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Left cancellation for inverse first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congr_lininv_applyself
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.congrLinear p G e⁻¹
        (zTAdditi.congrLinear p G e x) = x := by
  simpa [zTAdditi.congrLinear_symm] using
    (zTAdditi.congrLinear p G e).left_inv x

/-- Right cancellation for inverse first Zassenhaus quotient congruences. -/
@[simp] theorem zTAdditi.congr_linapply_invself
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.congrLinear p G e
        (zTAdditi.congrLinear p G e⁻¹ x) = x := by
  simpa [zTAdditi.congrLinear_symm] using
    (zTAdditi.congrLinear p G e).right_inv x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Left cancellation for inverse consecutive Zassenhaus linear congruences in MulAut notation. -/
@[simp] theorem zNQuot.congr_lininv_applyself
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G e⁻¹ n
        (zNQuot.congrLinear p G e n x) = x := by
  simpa using zNQuot.congr_linsymm_applyself (p := p) G G e n x

/-- Right cancellation for inverse consecutive Zassenhaus linear congruences in MulAut notation. -/
@[simp] theorem zNQuot.congr_linapply_invself
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G e n
        (zNQuot.congrLinear p G e⁻¹ n x) = x := by
  simpa using zNQuot.congr_linapply_symmself (p := p) G G e n x

/-- Left cancellation for inverse Zassenhaus layer linear congruences in MulAut notation. -/
@[simp] theorem zLKern.congr_lininv_applyself
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G e⁻¹ n
        (zLKern.congrLinear p G e n x) = x := by
  exact zLKern.congr_linsymm_applyself (p := p) G e n x

/-- Right cancellation for inverse Zassenhaus layer linear congruences in MulAut notation. -/
@[simp] theorem zLKern.congr_linapply_invself
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G e n
        (zLKern.congrLinear p G e⁻¹ n x) = x := by
  exact zLKern.congr_linapply_symmself (p := p) G e n x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Inverse orientation for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congrLinear_inv
    (G : Type*) [Group G] (e : MulAut G) :
    zTAdditi.congrLinear p G e⁻¹ =
      (zTAdditi.congrLinear p G e).symm := by
  rw [zTAdditi.congrLinear_symm]
  rfl

/-- Underlying-map inverse orientation for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congr_lininv_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.congrLinear p G e⁻¹).toLinearMap =
      (zTAdditi.congrLinear p G e).symm.toLinearMap := by
  rw [zTAdditi.congrLinear_inv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Underlying-map inverse orientation for MulAut-notation consecutive Zassenhaus
linear congruences. -/
@[simp] theorem zNQuot.congr_lininv_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.congrLinear p G e⁻¹ n).toLinearMap =
      (zNQuot.congrLinear p G e n).symm.toLinearMap := by
  rw [zNQuot.congrLinear_inv]

/-- Underlying-map inverse orientation for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congr_lininv_linmap
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.congrLinear p G e⁻¹ n).toLinearMap =
      (zLKern.congrLinear p G e n).symm.toLinearMap := by
  rw [zLKern.congrLinear_inv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Pointwise inverse orientation for the defining first Zassenhaus quotient congruence. -/
@[simp] theorem zTAdditi.congr_lin_invapply
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.congrLinear p G e⁻¹ x =
      (zTAdditi.congrLinear p G e).symm x := by
  rw [zTAdditi.congrLinear_inv]

/-- Pointwise inverse orientation for MulAut-notation consecutive Zassenhaus linear congruences. -/
@[simp] theorem zNQuot.congr_lin_invapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.congrLinear p G e⁻¹ n x =
      (zNQuot.congrLinear p G e n).symm x := by
  rw [zNQuot.congrLinear_inv]

/-- Pointwise inverse orientation for MulAut-notation Zassenhaus layer linear congruences. -/
@[simp] theorem zLKern.congr_lin_invapply
    [Fact p.Prime] (G : Type*) [Group G] (n : ℕ) (e : MulAut G)
    (x : Additive (zLKern p G n)) :
    zLKern.congrLinear p G e⁻¹ n x =
      (zLKern.congrLinear p G e n).symm x := by
  rw [zLKern.congrLinear_inv]

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Underlying-map inverse orientation for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.linaut_mapinv_linmap
    (G : Type*) [Group G] (e : MulAut G) :
    (zTAdditi.linearAutMap p G e⁻¹).toLinearMap =
      (zTAdditi.linearAutMap p G e).symm.toLinearMap := by
  rw [zTAdditi.lin_aut_mapinv]
  rfl

/-- Pointwise inverse orientation for the first Zassenhaus additive linear action. -/
@[simp] theorem zTAdditi.lin_autmap_invapply
    (G : Type*) [Group G] (e : MulAut G) (x : zTAdditi p G) :
    zTAdditi.linearAutMap p G e⁻¹ x =
      (zTAdditi.linearAutMap p G e).symm x := by
  rw [zTAdditi.lin_aut_mapinv]
  rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse orientation for Zassenhaus quotient automorphism actions. -/
@[simp] theorem zQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zQuot.mulAutMap p G n e⁻¹).toMonoidHom =
      (zQuot.mulAutMap p G n e).symm.toMonoidHom := by
  rw [zQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for consecutive Zassenhaus quotient actions. -/
@[simp] theorem zNQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zNQuot.mulAutMap p G n e⁻¹).toMonoidHom =
      (zNQuot.mulAutMap p G n e).symm.toMonoidHom := by
  rw [zNQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for Zassenhaus layer-kernel actions. -/
@[simp] theorem zLKern.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zLKern.mulAutMap p G n e⁻¹).toMonoidHom =
      (zLKern.mulAutMap p G n e).symm.toMonoidHom := by
  rw [zLKern.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for arbitrary Zassenhaus term-quotient actions. -/
@[simp] theorem zTQuot.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTQuot.mulAutMap p G hmn e⁻¹).toMonoidHom =
      (zTQuot.mulAutMap p G hmn e).symm.toMonoidHom := by
  rw [zTQuot.mul_aut_mapinv]
  rfl

/-- Hom-level inverse orientation for Zassenhaus transition-kernel actions. -/
@[simp] theorem zTKern.mulaut_mapinv_monoidhom
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTKern.mulAutMap p G hmn e⁻¹).toMonoidHom =
      (zTKern.mulAutMap p G hmn e).symm.toMonoidHom := by
  rw [zTKern.mul_aut_mapinv]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism actions on Zassenhaus quotients are the corresponding congruences. -/
@[simp] theorem zQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zQuot.mulAutMap p G n e = zQuot.congr p G e n := rfl

/-- Automorphism actions on consecutive Zassenhaus quotients are the corresponding congruences. -/
@[simp] theorem zNQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zNQuot.mulAutMap p G n e =
      zNQuot.congr p G e n := rfl

/-- Automorphism actions on Zassenhaus layer kernels are the corresponding congruences. -/
@[simp] theorem zLKern.mul_autmap_eqcongr
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    zLKern.mulAutMap p G n e =
      zLKern.congr p G e n := rfl

/-- Automorphism actions on Zassenhaus term quotients are the corresponding congruences. -/
@[simp] theorem zTQuot.mul_autmap_eqcongr
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTQuot.mulAutMap p G hmn e =
      zTQuot.congr p G e hmn := rfl

/-- Automorphism actions on Zassenhaus transition kernels are the corresponding congruences. -/
@[simp] theorem zTKern.mul_autmap_eqcongr
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTKern.mulAutMap p G hmn e =
      zTKern.congr p G e hmn := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- The first Zassenhaus additive linear automorphism action is its defining congruence. -/
@[simp] theorem zTAdditi.linaut_mapeq_congrlin
    (G : Type*) [Group G] (e : MulAut G) :
    zTAdditi.linearAutMap p G e =
      zTAdditi.congrLinear p G e := rfl

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- A group automorphism maps each Zassenhaus subgroup onto itself. -/
@[simp] theorem zassenhaus_mul_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zSubgro p G n).map e.toMonoidHom = zSubgro p G n := by
  simpa using (zassenhaus_equiv (p := p) (G := G) e n)

/-- A group automorphism pulls each Zassenhaus subgroup back to itself. -/
@[simp] theorem zassenhaus_comap_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) :
    (zSubgro p G n).comap e.toMonoidHom = zSubgro p G n := by
  simpa using (zassenhaus_comap_equiv (p := p) (G := G) e n)

/-- Pointwise invariance of Zassenhaus-subgroup membership under automorphisms. -/
theorem zassenhaus_subgroup_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    e g ∈ zSubgro p G n ↔ g ∈ zSubgro p G n := by
  simpa using (zassenhaus_subgroup_equiv (p := p) (G := G) e n g)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Zassenhaus depth is invariant under automorphisms, in predicate form. -/
theorem depth_least_aut
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    zassenhausDepthLeast p G (e g) n ↔ zassenhausDepthLeast p G g n := by
  exact zassenhaus_subgroup_aut (p := p) G n e g

/-- Symmetric automorphism-invariance form for Zassenhaus depth. -/
theorem least_aut_symm
    (G : Type*) [Group G] (n : ℕ) (e : MulAut G) (g : G) :
    zassenhausDepthLeast p G (e.symm g) n ↔ zassenhausDepthLeast p G g n := by
  simpa using (depth_least_aut (p := p) G n e.symm g)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Equivalences of groups carry the next Zassenhaus term inside a term onto the next term. -/
theorem next_term_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zNTerm p G n).map
        (zSubgro.congr p G e n).toMonoidHom =
      zNTerm p H n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ zSubgro p G (n + 1) :=
      (zassenhaus_next_term (p := p) (G := G) n x).1 hx
    change (((zSubgro.congr p G e n) x : zSubgro p H n) : H) ∈
      zSubgro p H (n + 1)
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e (n + 1) (x : G)).2 hx'
    simpa using h
  · intro hy
    refine ⟨(zSubgro.congr p H e.symm n) y, ?_, ?_⟩
    · have hy' : (y : H) ∈ zSubgro p H (n + 1) :=
        (zassenhaus_next_term (p := p) (G := H) n y).1 hy
      change (((zSubgro.congr p H e.symm n) y : zSubgro p G n) : G) ∈
        zSubgro p G (n + 1)
      have h := (zassenhaus_equiv_symm (p := p) (G := G) e (n + 1) (y : H)).2 hy'
      simpa using h
    · ext
      simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Equivalences of groups pull the next Zassenhaus term inside a term back to the next term. -/
theorem next_comap_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zNTerm p H n).comap
        (zSubgro.congr p G e n).toMonoidHom =
      zNTerm p G n := by
  ext x
  constructor
  · intro hx
    have hx' : (((zSubgro.congr p G e n) x :
          zSubgro p H n) : H) ∈ zSubgro p H (n + 1) :=
      (zassenhaus_next_term (p := p) (G := H) n _).1 hx
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e
      (n + 1) (x : G)).1 (by simpa using hx')
    exact (zassenhaus_next_term (p := p) (G := G) n x).2 h
  · intro hx
    have hx' : (x : G) ∈ zSubgro p G (n + 1) :=
      (zassenhaus_next_term (p := p) (G := G) n x).1 hx
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e
      (n + 1) (x : G)).2 hx'
    exact (zassenhaus_next_term (p := p) (G := H) n _).2 (by simpa using h)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The restriction of a group equivalence to the embedded next Zassenhaus terms. -/
noncomputable def zNTerm.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    zNTerm p G n ≃* zNTerm p H n :=
  ((zSubgro.congr p G e n).subgroupMap
      (zNTerm p G n)).trans
    (MulEquiv.subgroupCongr (next_term_congr (p := p) e n))

/-- Coercion formula for the restricted equivalence on embedded next Zassenhaus terms. -/
@[simp] theorem zNTerm.congr_apply_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) (x : zNTerm p G n) :
    (((zNTerm.congr (p := p) e n x :
        zNTerm p H n) : zSubgro p H n) : H) =
      e ((x : zSubgro p G n) : G) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse orientation for restricted equivalences on embedded next Zassenhaus terms. -/
@[simp] theorem zNTerm.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) :
    (zNTerm.congr (p := p) e n).symm =
      zNTerm.congr (p := p) e.symm n := by
  ext y
  change e.symm ((y : zSubgro p H n) : H) =
    e.symm ((y : zSubgro p H n) : H)
  rfl

/-- Identity law for restricted equivalences on embedded next Zassenhaus terms. -/
@[simp] theorem zNTerm.congr_refl {G : Type*} [Group G] (n : ℕ) :
    zNTerm.congr (p := p) (MulEquiv.refl G) n =
      MulEquiv.refl (zNTerm p G n) := by
  ext x
  rfl

/-- Composition law for restricted equivalences on embedded next Zassenhaus terms. -/
@[simp] theorem zNTerm.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K) (n : ℕ) :
    (zNTerm.congr (p := p) e n).trans
        (zNTerm.congr (p := p) f n) =
      zNTerm.congr (p := p) (e.trans f) n := by
  ext x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Left inverse cancellation for restricted Zassenhaus next-term congruences. -/
@[simp] theorem zNTerm.congr_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zNTerm p G n) :
    zNTerm.congr (p := p) e.symm n
        (zNTerm.congr (p := p) e n x) = x := by
  rw [← zNTerm.congr_symm (p := p) e n]
  exact (zNTerm.congr (p := p) e n).left_inv x

/-- Right inverse cancellation for restricted Zassenhaus next-term congruences. -/
@[simp] theorem zNTerm.congr_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (y : zNTerm p H n) :
    zNTerm.congr (p := p) e n
        (zNTerm.congr (p := p) e.symm n y) = y := by
  rw [← zNTerm.congr_symm (p := p) e n]
  exact (zNTerm.congr (p := p) e n).right_inv y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Parent-term coercion of the restricted Zassenhaus next-term congruence. -/
@[simp] theorem zNTerm.congr_apply_parent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (x : zNTerm p G n) :
    ((zNTerm.congr (p := p) e n x :
        zNTerm p H n) : zSubgro p H n) =
      zSubgro.congr p G e n (x : zSubgro p G n) := by
  rfl

/-- Coercion formula for the inverse restricted Zassenhaus next-term congruence. -/
@[simp] theorem zNTerm.congr_symm_applycoe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) (n : ℕ)
    (y : zNTerm p H n) :
    ((((zNTerm.congr (p := p) e n).symm y :
        zNTerm p G n) : zSubgro p G n) : G) =
      e.symm ((y : zSubgro p H n) : H) := by
  rw [zNTerm.congr_symm]
  exact zNTerm.congr_apply_coe (p := p) e.symm n y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Equivalences carry embedded arbitrary Zassenhaus terms onto embedded arbitrary terms. -/
theorem zassenhaus_term_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro p G hmn).map
        (zSubgro.congr p G e m).toMonoidHom =
      zTSubgro p H hmn := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ zSubgro p G n :=
      (zassenhaus_term (p := p) (G := G) hmn x).1 hx
    change (((zSubgro.congr p G e m) x :
        zSubgro p H m) : H) ∈ zSubgro p H n
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e n (x : G)).2 hx'
    simpa using h
  · intro hy
    refine ⟨(zSubgro.congr p H e.symm m) y, ?_, ?_⟩
    · have hy' : (y : H) ∈ zSubgro p H n :=
        (zassenhaus_term (p := p) (G := H) hmn y).1 hy
      change (((zSubgro.congr p H e.symm m) y :
          zSubgro p G m) : G) ∈ zSubgro p G n
      have h := (zassenhaus_equiv_symm (p := p) (G := G) e n (y : H)).2 hy'
      simpa using h
    · ext
      simp

/-- Equivalences pull embedded arbitrary Zassenhaus terms back to embedded arbitrary terms. -/
theorem term_comap_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro p H hmn).comap
        (zSubgro.congr p G e m).toMonoidHom =
      zTSubgro p G hmn := by
  ext x
  constructor
  · intro hx
    have hx' : (((zSubgro.congr p G e m) x :
        zSubgro p H m) : H) ∈ zSubgro p H n :=
      (zassenhaus_term (p := p) (G := H) hmn
        ((zSubgro.congr p G e m) x)).1 hx
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e n (x : G)).1
      (by simpa using hx')
    exact (zassenhaus_term (p := p) (G := G) hmn x).2 h
  · intro hx
    have hx' : (x : G) ∈ zSubgro p G n :=
      (zassenhaus_term (p := p) (G := G) hmn x).1 hx
    have h := (zassenhaus_subgroup_equiv (p := p) (G := G) e n (x : G)).2 hx'
    exact (zassenhaus_term (p := p) (G := H) hmn
        ((zSubgro.congr p G e m) x)).2 (by simpa using h)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The restriction of a group equivalence to arbitrary embedded Zassenhaus terms. -/
noncomputable def zTSubgro.congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro p G hmn ≃* zTSubgro p H hmn :=
  ((zSubgro.congr p G e m).subgroupMap
      (zTSubgro p G hmn)).trans
    (MulEquiv.subgroupCongr (zassenhaus_term_congr (p := p) e hmn))

/-- Parent-term coercion of the restricted congruence on arbitrary Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_apply_parent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    ((zTSubgro.congr (p := p) e hmn x :
        zTSubgro p H hmn) : zSubgro p H m) =
      zSubgro.congr p G e m (x : zSubgro p G m) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse orientation for restricted equivalences on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e hmn).symm =
      zTSubgro.congr (p := p) e.symm hmn := by
  ext y
  change e.symm (((y : zTSubgro p H hmn) :
      zSubgro p H m) : H) =
    e.symm (((y : zTSubgro p H hmn) :
      zSubgro p H m) : H)
  rfl

/-- Identity law for restricted equivalences on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.congr (p := p) (MulEquiv.refl G) hmn =
      MulEquiv.refl (zTSubgro p G hmn) := by
  ext x
  rfl

/-- Composition law for restricted equivalences on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_trans {G H K : Type*}
    [Group G] [Group H] [Group K] (e : G ≃* H) (f : H ≃* K)
    {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e hmn).trans
        (zTSubgro.congr (p := p) f hmn) =
      zTSubgro.congr (p := p) (e.trans f) hmn := by
  ext x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Left inverse cancellation for restricted arbitrary Zassenhaus-term congruences. -/
@[simp] theorem zTSubgro.congr_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    zTSubgro.congr (p := p) e.symm hmn
        (zTSubgro.congr (p := p) e hmn x) = x := by
  rw [← zTSubgro.congr_symm (p := p) e hmn]
  exact (zTSubgro.congr (p := p) e hmn).left_inv x

/-- Right inverse cancellation for restricted arbitrary Zassenhaus-term congruences. -/
@[simp] theorem zTSubgro.congr_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn) :
    zTSubgro.congr (p := p) e hmn
        (zTSubgro.congr (p := p) e.symm hmn y) = y := by
  rw [← zTSubgro.congr_symm (p := p) e hmn]
  exact (zTSubgro.congr (p := p) e hmn).right_inv y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Underlying-group coercion of the restricted congruence on arbitrary Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_apply_coe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    (((zTSubgro.congr (p := p) e hmn x :
        zTSubgro p H hmn) : zSubgro p H m) : H) =
      e ((x : zSubgro p G m) : G) := by
  rfl

/-- Parent-term coercion of the inverse restricted congruence on arbitrary Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_symm_applyparent {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn) :
    (((zTSubgro.congr (p := p) e hmn).symm y :
        zTSubgro p G hmn) : zSubgro p G m) =
      zSubgro.congr p H e.symm m (y : zSubgro p H m) := by
  rw [zTSubgro.congr_symm]
  exact zTSubgro.congr_apply_parent (p := p) e.symm hmn y

/-- Underlying-group coercion of the inverse restricted congruence on arbitrary Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_symm_applycoe {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn) :
    ((((zTSubgro.congr (p := p) e hmn).symm y :
        zTSubgro p G hmn) : zSubgro p G m) : G) =
      e.symm ((y : zSubgro p H m) : H) := by
  rw [zTSubgro.congr_symm]
  exact zTSubgro.congr_apply_coe (p := p) e.symm hmn y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphisms of `G` act on arbitrary embedded Zassenhaus terms. -/
noncomputable def zTSubgro.mulAutMap (G : Type*) [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    MulAut G →* MulAut (zTSubgro p G hmn) where
  toFun e := zTSubgro.congr (p := p) e hmn
  map_one' := by
    ext x
    rfl
  map_mul' e f := by
    ext x
    rfl

@[simp] theorem zTSubgro.mul_aut_mapapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zTSubgro p G hmn) :
    zTSubgro.mulAutMap (p := p) G hmn e x =
      zTSubgro.congr (p := p) e hmn x := rfl

@[simp] theorem zTSubgro.mul_aut_mapone {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.mulAutMap (p := p) G hmn 1 = 1 :=
  map_one (zTSubgro.mulAutMap (p := p) G hmn)

@[simp] theorem zTSubgro.mul_aut_mapmul {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G) :
    zTSubgro.mulAutMap (p := p) G hmn (e * f) =
      zTSubgro.mulAutMap (p := p) G hmn e *
        zTSubgro.mulAutMap (p := p) G hmn f :=
  map_mul (zTSubgro.mulAutMap (p := p) G hmn) e f

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem zTSubgro.mul_aut_mapinv {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTSubgro.mulAutMap (p := p) G hmn e⁻¹ =
      (zTSubgro.mulAutMap (p := p) G hmn e)⁻¹ :=
  map_inv (zTSubgro.mulAutMap (p := p) G hmn) e

@[simp] theorem zTSubgro.mul_autmap_mulapply {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e f : MulAut G)
    (x : zTSubgro p G hmn) :
    zTSubgro.mulAutMap (p := p) G hmn (e * f) x =
      zTSubgro.mulAutMap (p := p) G hmn e
        (zTSubgro.mulAutMap (p := p) G hmn f x) := by
  simp [zTSubgro.mul_aut_mapmul]

@[simp] theorem zTSubgro.mulaut_mapinv_applyself {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zTSubgro p G hmn) :
    zTSubgro.mulAutMap (p := p) G hmn e⁻¹
        (zTSubgro.mulAutMap (p := p) G hmn e x) = x := by
  change zTSubgro.congr (p := p) e.symm hmn
      (zTSubgro.congr (p := p) e hmn x) = x
  exact zTSubgro.congr_symm_applyself (p := p) e hmn x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism actions on arbitrary embedded Zassenhaus terms are congruences. -/
@[simp] theorem zTSubgro.mul_autmap_eqcongr {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    zTSubgro.mulAutMap (p := p) G hmn e =
      zTSubgro.congr (p := p) e hmn := rfl

/-- Parent-term formula for the automorphism action on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.mul_autmap_applyparent {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zTSubgro p G hmn) :
    ((zTSubgro.mulAutMap (p := p) G hmn e x :
        zTSubgro p G hmn) : zSubgro p G m) =
      zSubgro.congr p G e m (x : zSubgro p G m) := by
  rfl

/-- Underlying-group formula for the automorphism action on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.mul_autmap_applycoe {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zTSubgro p G hmn) :
    (((zTSubgro.mulAutMap (p := p) G hmn e x :
        zTSubgro p G hmn) : zSubgro p G m) : G) =
      e ((x : zSubgro p G m) : G) := by
  rfl

/-- Right inverse cancellation for automorphism actions on arbitrary Zassenhaus terms. -/
@[simp] theorem zTSubgro.mulaut_mapapply_invself {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G)
    (x : zTSubgro p G hmn) :
    zTSubgro.mulAutMap (p := p) G hmn e
        (zTSubgro.mulAutMap (p := p) G hmn e⁻¹ x) = x := by
  change zTSubgro.congr (p := p) e hmn
      (zTSubgro.congr (p := p) e.symm hmn x) = x
  exact zTSubgro.congr_apply_symmself (p := p) e hmn x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Inverse-application criterion for restricted congruences on arbitrary Zassenhaus terms. -/
theorem zTSubgro.congr_symm_applyeq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn)
    (x : zTSubgro p G hmn) :
    (zTSubgro.congr (p := p) e hmn).symm y = x ↔
      y = zTSubgro.congr (p := p) e hmn x := by
  rw [MulEquiv.symm_apply_eq]

/-- Forward-application criterion for restricted congruences on arbitrary Zassenhaus terms. -/
theorem zTSubgro.congr_apply_eqiff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn)
    (y : zTSubgro p H hmn) :
    zTSubgro.congr (p := p) e hmn x = y ↔
      x = zTSubgro.congr (p := p) e.symm hmn y := by
  rw [← zTSubgro.congr_symm (p := p) e hmn]
  exact (zTSubgro.congr (p := p) e hmn).apply_eq_iff_eq_symm_apply

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level form of the arbitrary Zassenhaus-term automorphism action. -/
@[simp] theorem zTSubgro.mul_autmap_monoidhom {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTSubgro.mulAutMap (p := p) G hmn e).toMonoidHom =
      (zTSubgro.congr (p := p) e hmn).toMonoidHom := rfl

/-- Hom-level form of the inverse arbitrary Zassenhaus-term automorphism action. -/
@[simp] theorem zTSubgro.mulaut_mapsymm_monoidhom {G : Type*}
    [Group G] {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    ((zTSubgro.mulAutMap (p := p) G hmn e).symm).toMonoidHom =
      (zTSubgro.congr (p := p) e.symm hmn).toMonoidHom := by
  rw [← zTSubgro.congr_symm (p := p) e hmn]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Restricted arbitrary-term congruences commute with inclusion into the parent term. -/
theorem zTSubgro.subtype_comp_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro p H hmn).subtype.comp
        (zTSubgro.congr (p := p) e hmn).toMonoidHom =
      (zSubgro.congr p G e m).toMonoidHom.comp
        (zTSubgro p G hmn).subtype := by
  ext x
  rfl

/-- Pointwise inclusion-square form for arbitrary Zassenhaus-term congruences. -/
@[simp] theorem zTSubgro.subtype_congr_apply {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    (zTSubgro p H hmn).subtype
        (zTSubgro.congr (p := p) e hmn x) =
      zSubgro.congr p G e m
        ((zTSubgro p G hmn).subtype x) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Arbitrary Zassenhaus-term actions commute with inclusion into the parent term. -/
theorem zTSubgro.subtype_compmul_autmap {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) (e : MulAut G) :
    (zTSubgro p G hmn).subtype.comp
        (zTSubgro.mulAutMap (p := p) G hmn e).toMonoidHom =
      (zSubgro.congr p G e m).toMonoidHom.comp
        (zTSubgro p G hmn).subtype := by
  ext x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Deeper embedded Zassenhaus terms are contained in intermediate embedded terms. -/
theorem term_subgroup {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro p G (Nat.le_trans hmn hnk) ≤
      zTSubgro p G hmn := by
  intro x hx
  rw [zassenhaus_term] at hx ⊢
  exact zassenhausSubgroup_antitone p G hnk hx

/-- Inclusion of a deeper embedded Zassenhaus term into an intermediate one. -/
def zTSubgro.inclusion {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro p G (Nat.le_trans hmn hnk) →*
      zTSubgro p G hmn :=
  Subgroup.inclusion (term_subgroup (p := p) hmn hnk)

@[simp] theorem zTSubgro.inclusion_apply {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G (Nat.le_trans hmn hnk)) :
    (zTSubgro.inclusion (p := p) hmn hnk x :
        zSubgro p G m) = x := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Nested inclusion maps for embedded Zassenhaus terms compose as expected. -/
@[simp] theorem zTSubgro.inclusion_comp {G : Type*} [Group G]
    {m n k l : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (hkl : k ≤ l) :
    (zTSubgro.inclusion (p := p) (G := G) hmn hnk).comp
        (zTSubgro.inclusion (p := p) (G := G)
          (Nat.le_trans hmn hnk) hkl) =
      zTSubgro.inclusion (p := p) (G := G) hmn
        (Nat.le_trans hnk hkl) := by
  ext x
  rfl

/-- The reflexive inclusion of an embedded Zassenhaus term is the identity. -/
@[simp] theorem zTSubgro.inclusion_refl {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.inclusion (p := p) (G := G) hmn (Nat.le_refl n) =
      MonoidHom.id (zTSubgro p G hmn) := by
  ext x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Restricted congruences are natural for inclusions between nested Zassenhaus terms. -/
theorem zTSubgro.inclusion_comp_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion (p := p) (G := H) hmn hnk).comp
        (zTSubgro.congr (p := p) e (Nat.le_trans hmn hnk)).toMonoidHom =
      (zTSubgro.congr (p := p) e hmn).toMonoidHom.comp
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk) := by
  ext x
  rfl

/-- Pointwise naturality for nested Zassenhaus-term inclusions and congruences. -/
@[simp] theorem zTSubgro.inclusion_congr_apply {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G (Nat.le_trans hmn hnk)) :
    zTSubgro.inclusion (p := p) (G := H) hmn hnk
        (zTSubgro.congr (p := p) e (Nat.le_trans hmn hnk) x) =
      zTSubgro.congr (p := p) e hmn
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk x) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism actions are natural for inclusions between nested Zassenhaus terms. -/
theorem zTSubgro.inclusion_compmul_autmap {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G) :
    (zTSubgro.inclusion (p := p) (G := G) hmn hnk).comp
        (zTSubgro.mulAutMap (p := p) G (Nat.le_trans hmn hnk) e).toMonoidHom =
      (zTSubgro.mulAutMap (p := p) G hmn e).toMonoidHom.comp
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk) := by
  ext x
  rfl

/-- Pointwise naturality of automorphism actions for nested Zassenhaus-term inclusions. -/
@[simp] theorem zTSubgro.inclusion_mulaut_mapapply {G : Type*}
    [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G)
    (x : zTSubgro p G (Nat.le_trans hmn hnk)) :
    zTSubgro.inclusion (p := p) (G := G) hmn hnk
        (zTSubgro.mulAutMap (p := p) G (Nat.le_trans hmn hnk) e x) =
      zTSubgro.mulAutMap (p := p) G hmn e
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk x) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Canonical inclusions between nested Zassenhaus terms are injective. -/
theorem zTSubgro.inclusion_injective {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective (zTSubgro.inclusion (p := p) (G := G) hmn hnk) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : zTSubgro p G hmn =>
      (z : zSubgro p G m)) hxy

/-- Equality can be checked after the canonical inclusion between nested Zassenhaus terms. -/
@[simp] theorem zTSubgro.inclusion_apply_eqiff {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : zTSubgro p G (Nat.le_trans hmn hnk)) :
    zTSubgro.inclusion (p := p) (G := G) hmn hnk x =
        zTSubgro.inclusion (p := p) (G := G) hmn hnk y ↔ x = y := by
  constructor
  · intro h
    exact zTSubgro.inclusion_injective (p := p) (G := G) hmn hnk h
  · intro h
    simp [h]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Range criterion for the canonical inclusion between nested Zassenhaus terms. -/
theorem zTSubgro.mem_range_inclusioniff {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : zTSubgro p G hmn) :
    y ∈ (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range ↔
      ((y : zSubgro p G m) : G) ∈ zSubgro p G k := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (zassenhaus_term (p := p) (G := G) (Nat.le_trans hmn hnk)
      (x : zSubgro p G m)).1 x.property
  · intro hy
    let x : zTSubgro p G (Nat.le_trans hmn hnk) :=
      ⟨(y : zSubgro p G m),
        (zassenhaus_term (p := p) (G := G) (Nat.le_trans hmn hnk)
          (y : zSubgro p G m)).2 hy⟩
    refine ⟨x, ?_⟩
    ext
    rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Restricted congruences carry the range of a nested Zassenhaus-term inclusion to the
corresponding range after transport. -/
theorem zTSubgro.map_range_inclusioncongr {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    ((zTSubgro.inclusion (p := p) (G := G) hmn hnk).range).map
        (zTSubgro.congr (p := p) e hmn).toMonoidHom =
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz⟩
    refine ⟨zTSubgro.congr (p := p) e (Nat.le_trans hmn hnk) z, ?_⟩
    rw [← hz]
    exact (zTSubgro.inclusion_congr_apply (p := p) e hmn hnk z).symm
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨zTSubgro.inclusion (p := p) (G := G) hmn hnk
        (zTSubgro.congr (p := p) e.symm (Nat.le_trans hmn hnk) z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · rw [zTSubgro.inclusion_congr_apply (p := p) e.symm hmn hnk]
      rw [← hz]
      simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Automorphism actions preserve the range of a nested Zassenhaus-term inclusion. -/
theorem zTSubgro.maprange_inclusionmul_autmap {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (e : MulAut G) :
    ((zTSubgro.inclusion (p := p) (G := G) hmn hnk).range).map
        (zTSubgro.mulAutMap (p := p) G hmn e).toMonoidHom =
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range := by
  simpa using
    (zTSubgro.map_range_inclusioncongr (p := p) (G := G) (H := G)
      (e := e) hmn hnk)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The range of a nested Zassenhaus-term inclusion is normal in the intermediate term. -/
theorem zTSubgro.inclusion_range_normal {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range.Normal := by
  constructor
  intro x hx y
  rw [zTSubgro.mem_range_inclusioniff (p := p) hmn hnk] at hx ⊢
  change ((y : zSubgro p G m) : G) * ((x : zSubgro p G m) : G) *
      ((y : zSubgro p G m) : G)⁻¹ ∈ zSubgro p G k
  exact (zassenhausSubgroup_normal p G k).conj_mem
    ((x : zSubgro p G m) : G) hx ((y : zSubgro p G m) : G)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- The range of a nested Zassenhaus-term inclusion is available as a normal subgroup instance. -/
instance zTSubgro.inclusion_range_normalinst {G : Type*} [Group G]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range.Normal :=
  zTSubgro.inclusion_range_normal (p := p) (G := G) hmn hnk

/-- A homomorphism induces a map on quotients by ranges of nested Zassenhaus-term inclusions. -/
noncomputable def zTSubgro.inclusion_range_quotmap {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro p G hmn ⧸
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) →*
      (zTSubgro p H hmn ⧸
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :=
  DFilt.tSOf.inclusion_range_quotmap
    (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn hnk

@[simp] theorem zTSubgro.inclusion_rangequot_mapmk {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G hmn) :
    zTSubgro.inclusion_range_quotmap φ hmn hnk
        (QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range
        (DFilt.tSOf.map
          (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn x) := rfl

/-- A group isomorphism induces an equivalence on quotients by ranges of nested
Zassenhaus-term inclusions. -/
noncomputable def zTSubgro.inclusion_range_quotcongr {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro p G hmn ⧸
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) ≃*
      (zTSubgro p H hmn ⧸
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :=
  DFilt.tSOf.inclusionrange_quotequiv_mulequiv e
    (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
    (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn hnk

@[simp] theorem zTSubgro.inclusion_rangequot_congrmk {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G hmn) :
    zTSubgro.inclusion_range_quotcongr e hmn hnk
        (QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range
        (DFilt.tSOf.map
          (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom) hmn x) := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem zTSubgro.inclus_quotc_symmm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) (y : zTSubgro p H hmn) :
    (zTSubgro.inclusion_range_quotcongr e hmn hnk).symm
        (QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range y) =
      QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range
        (DFilt.tSOf.map
          (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn y) := rfl

@[simp] theorem zTSubgro.inclus_quotc_monoi
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).toMonoidHom =
      zTSubgro.inclusion_range_quotmap e.toMonoidHom hmn hnk := rfl

@[simp] theorem zTSubgro.inclus_quotc_symmb
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm.toMonoidHom =
      zTSubgro.inclusion_range_quotmap e.symm.toMonoidHom hmn hnk := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem zTSubgro.inclusion_rangequot_mapid {G : Type*}
    [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro.inclusion_range_quotmap (p := p) (MonoidHom.id G) hmn hnk =
      MonoidHom.id
        (zTSubgro p G hmn ⧸
          (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zTSubgro.inclusion_rangequot_mapcomp {G H L : Type*}
    [Group G] [Group H] [Group L] (φ : G →* H) (ψ : H →* L)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro.inclusion_range_quotmap (p := p) (ψ.comp φ) hmn hnk =
      (zTSubgro.inclusion_range_quotmap (p := p) ψ hmn hnk).comp
        (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem zTSubgro.inclusion_rangequot_congrrefl
    {G : Type*} [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro.inclusion_range_quotcongr (p := p) (MulEquiv.refl G) hmn hnk =
      MulEquiv.refl
        (zTSubgro p G hmn ⧸
          (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zTSubgro.inclusion_rangequot_congrsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm =
      zTSubgro.inclusion_range_quotcongr (p := p) e.symm hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro y
  rfl

@[simp] theorem zTSubgro.inclusion_rangequot_congrtrans
    {G H L : Type*} [Group G] [Group H] [Group L] (e : G ≃* H) (f : H ≃* L)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).trans
        (zTSubgro.inclusion_range_quotcongr (p := p) f hmn hnk) =
      zTSubgro.inclusion_range_quotcongr (p := p) (e.trans f) hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem zTSubgro.inclus_quotc_symma
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : zTSubgro p G hmn ⧸
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm
        (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk q) = q :=
  (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).left_inv q

@[simp] theorem zTSubgro.inclus_quotc_apply
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : zTSubgro p H hmn ⧸
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :
    zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk
        ((zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm q) = q :=
  (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).right_inv q

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem zTSubgro.inclus_quotm_symmc
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotmap (p := p) e.symm.toMonoidHom hmn hnk).comp
        (zTSubgro.inclusion_range_quotmap (p := p) e.toMonoidHom hmn hnk) =
      MonoidHom.id
        (zTSubgro p G hmn ⧸
          (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_symmc
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn hnk

@[simp] theorem zTSubgro.inclus_quotm_comps
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotmap (p := p) e.toMonoidHom hmn hnk).comp
        (zTSubgro.inclusion_range_quotmap (p := p) e.symm.toMonoidHom hmn hnk) =
      MonoidHom.id
        (zTSubgro p H hmn ⧸
          (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_comps
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn hnk

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse composition for arbitrary embedded Zassenhaus-term congruences. -/
@[simp] theorem zTSubgro.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e.symm hmn).toMonoidHom.comp
        (zTSubgro.congr (p := p) e hmn).toMonoidHom =
      MonoidHom.id (zTSubgro p G hmn) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e hmn).toMonoidHom.comp
        (zTSubgro.congr (p := p) e.symm hmn).toMonoidHom =
      MonoidHom.id (zTSubgro p H hmn) := by
  ext y
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse composition for Zassenhaus nested-range quotient congruences. -/
@[simp] theorem zTSubgro.inclus_quotc_homsy
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm.toMonoidHom.comp
        (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).toMonoidHom =
      MonoidHom.id
        (zTSubgro p G hmn ⧸
          (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) := by
  simpa using zTSubgro.inclus_quotm_symmc (p := p) e hmn hnk

/-- Hom-level inverse composition in the other order for Zassenhaus nested-range congruences. -/
@[simp] theorem zTSubgro.inclus_quotc_homco
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).toMonoidHom.comp
        (zTSubgro.inclusion_range_quotcongr (p := p) e hmn hnk).symm.toMonoidHom =
      MonoidHom.id
        (zTSubgro p H hmn ⧸
          (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) := by
  simpa using zTSubgro.inclus_quotm_comps (p := p) e hmn hnk

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse composition for embedded next Zassenhaus-term congruences. -/
@[simp] theorem zNTerm.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNTerm.congr (p := p) e.symm n).toMonoidHom.comp
        (zNTerm.congr (p := p) e n).toMonoidHom =
      MonoidHom.id (zNTerm p G n) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for embedded next Zassenhaus terms. -/
@[simp] theorem zNTerm.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNTerm.congr (p := p) e n).toMonoidHom.comp
        (zNTerm.congr (p := p) e.symm n).toMonoidHom =
      MonoidHom.id (zNTerm p H n) := by
  ext y
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse composition for Zassenhaus subgroup congruences. -/
@[simp] theorem zSubgro.congr_monoidhom_symmcomp
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zSubgro.congr p H e.symm n).toMonoidHom.comp
        (zSubgro.congr p G e n).toMonoidHom =
      MonoidHom.id (zSubgro p G n) := by
  ext x
  simp

/-- Hom-level inverse composition in the other order for Zassenhaus subgroup congruences. -/
@[simp] theorem zSubgro.congr_monoidhom_compsymm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zSubgro.congr p G e n).toMonoidHom.comp
        (zSubgro.congr p H e.symm n).toMonoidHom =
      MonoidHom.id (zSubgro p H n) := by
  ext y
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level inverse orientation for Zassenhaus subgroup congruences. -/
@[simp] theorem zSubgro.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zSubgro.congr p G e n).symm.toMonoidHom =
      (zSubgro.congr p H e.symm n).toMonoidHom := by
  rw [zSubgro.congr_symm]

/-- Hom-level inverse orientation for embedded next Zassenhaus-term congruences. -/
@[simp] theorem zNTerm.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    (zNTerm.congr (p := p) e n).symm.toMonoidHom =
      (zNTerm.congr (p := p) e.symm n).toMonoidHom := by
  rw [zNTerm.congr_symm]

/-- Hom-level inverse orientation for arbitrary embedded Zassenhaus-term congruences. -/
@[simp] theorem zTSubgro.congr_symm_monoidhom
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e hmn).symm.toMonoidHom =
      (zTSubgro.congr (p := p) e.symm hmn).toMonoidHom := by
  rw [zTSubgro.congr_symm]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise cancellation for inverse maps on arbitrary Zassenhaus-term quotients. -/
@[simp] theorem zassenhaus_symm_self
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p H e.symm.toMonoidHom hmn
        (zassenhausTerm p G e.toMonoidHom hmn q) = q := by
  simpa [zassenhausTerm] using
    DFilt.quotient_symm_self
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn q

/-- Pointwise cancellation in the other order for arbitrary Zassenhaus-term quotient maps. -/
@[simp] theorem term_symm_self
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (q : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G e.toMonoidHom hmn
        (zassenhausTerm p H e.symm.toMonoidHom hmn q) = q := by
  simpa [zassenhausTerm] using
    DFilt.term_quotient_self
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn q

/-- Pointwise cancellation for inverse maps on Zassenhaus nested-range quotients. -/
@[simp] theorem zTSubgro.inclus_quotm_symma
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : zTSubgro p G hmn ⧸
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap (p := p) e.symm.toMonoidHom hmn hnk
        (zTSubgro.inclusion_range_quotmap (p := p) e.toMonoidHom
          hmn hnk q) = q := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_symma
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn hnk q

/-- Pointwise cancellation in the other order for Zassenhaus nested-range quotient maps. -/
@[simp] theorem zTSubgro.inclus_quotm_apply
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k)
    (q : zTSubgro p H hmn ⧸
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap (p := p) e.toMonoidHom hmn hnk
        (zTSubgro.inclusion_range_quotmap (p := p) e.symm.toMonoidHom
          hmn hnk q) = q := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_apply
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn hnk q

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- A homomorphism restricts to arbitrary embedded Zassenhaus terms. -/
noncomputable def zTSubgro.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro p G hmn →* zTSubgro p H hmn :=
  DFilt.tSOf.map
    (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn

/-- Coercion formula for maps on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.map_coe {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    (((zTSubgro.map (p := p) φ hmn x :
        zTSubgro p H hmn) : zSubgro p H m) : H) =
      φ (((x : zTSubgro p G hmn) : zSubgro p G m) : G) := by
  rfl

/-- Identity law for maps on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.map_id {G : Type*} [Group G]
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.map (p := p) (MonoidHom.id G) hmn =
      MonoidHom.id (zTSubgro p G hmn) := by
  ext x
  rfl

/-- Composition law for maps on arbitrary embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.map_comp {G H K : Type*}
    [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K)
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.map (p := p) (ψ.comp φ) hmn =
      (zTSubgro.map (p := p) ψ hmn).comp
        (zTSubgro.map (p := p) φ hmn) := by
  ext x
  rfl

/-- The restricted congruence has the same underlying hom as the restricted map. -/
@[simp] theorem zTSubgro.congr_monoid_hom {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.congr (p := p) e hmn).toMonoidHom =
      zTSubgro.map (p := p) e.toMonoidHom hmn := by
  ext x
  simp [zTSubgro.map_coe, zTSubgro.congr_apply_parent]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Pointwise cancellation for inverse restricted maps on embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.map_symm_applyself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    zTSubgro.map (p := p) e.symm.toMonoidHom hmn
        (zTSubgro.map (p := p) e.toMonoidHom hmn x) = x := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_symm_applyself
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn x

/-- Pointwise cancellation in the other order for restricted maps on embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.map_apply_symmself {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn) :
    zTSubgro.map (p := p) e.toMonoidHom hmn
        (zTSubgro.map (p := p) e.symm.toMonoidHom hmn y) = y := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_apply_symmself
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) e
      (zassenhausFiltration_preserves (p := p) (G := G) e.toMonoidHom)
      (zassenhausFiltration_preserves (p := p) (G := H) e.symm.toMonoidHom) hmn y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Restricted maps commute with nested inclusions of embedded Zassenhaus terms. -/
theorem zTSubgro.inclusion_comp_map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion (p := p) (G := H) hmn hnk).comp
        (zTSubgro.map (p := p) φ (Nat.le_trans hmn hnk)) =
      (zTSubgro.map (p := p) φ hmn).comp
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk) := by
  simpa [zTSubgro.map, zTSubgro.inclusion] using
    DFilt.tSOf.inclusion_comp_map
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H)
      (zassenhausFiltration_preserves (p := p) (G := G) φ) hmn hnk

/-- Pointwise naturality of restricted maps with nested Zassenhaus-term inclusions. -/
@[simp] theorem zTSubgro.inclusion_map_apply {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G (Nat.le_trans hmn hnk)) :
    zTSubgro.inclusion (p := p) (G := H) hmn hnk
        (zTSubgro.map (p := p) φ (Nat.le_trans hmn hnk) x) =
      zTSubgro.map (p := p) φ hmn
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk x) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- A restricted Zassenhaus-term map sends nested-inclusion ranges into target ranges. -/
theorem zTSubgro.map_range_inclusionle {G H : Type*}
    [Group G] [Group H] (φ : G →* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((zTSubgro.inclusion (p := p) (G := G) hmn hnk).range).map
        (zTSubgro.map (p := p) φ hmn) ≤
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨z, hz⟩
  refine ⟨zTSubgro.map (p := p) φ (Nat.le_trans hmn hnk) z, ?_⟩
  rw [← hz]
  exact (zTSubgro.inclusion_map_apply (p := p) φ hmn hnk z).symm

/-- An equivalence carries nested-inclusion ranges of Zassenhaus terms onto target ranges. -/
theorem zTSubgro.map_rangeinclusion_eqequiv {G H : Type*}
    [Group G] [Group H] (e : G ≃* H) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((zTSubgro.inclusion (p := p) (G := G) hmn hnk).range).map
        (zTSubgro.map (p := p) e.toMonoidHom hmn) =
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range := by
  apply le_antisymm
  · exact zTSubgro.map_range_inclusionle (p := p) e.toMonoidHom hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    refine ⟨zTSubgro.inclusion (p := p) (G := G) hmn hnk
        (zTSubgro.map (p := p) e.symm.toMonoidHom (Nat.le_trans hmn hnk) z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · rw [zTSubgro.inclusion_map_apply (p := p) e.symm.toMonoidHom hmn hnk z]
      exact zTSubgro.map_apply_symmself (p := p) e hmn
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk z)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Restricted maps on embedded Zassenhaus terms are injective for injective ambient maps. -/
theorem zTSubgro.map_injective {G H : Type*} [Group G] [Group H]
    {φ : G →* H} (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (zTSubgro.map (p := p) φ hmn) := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_injective
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H)
      (zassenhausFiltration_preserves (p := p) (G := G) φ) hinj hmn

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Kernel form of injectivity for restricted Zassenhaus-term maps. -/
@[simp] theorem zTSubgro.map_kereq_botinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H} (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.map (p := p) φ hmn).ker = ⊥ := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_kereq_botinj
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H)
      (zassenhausFiltration_preserves (p := p) (G := G) φ) hinj hmn

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Surjectivity of restricted maps on embedded Zassenhaus terms under termwise-onto hypotheses. -/
theorem zTSubgro.map_surj_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (zTSubgro.map (p := p) φ hmn) := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_surjective honto hmn

/-- Range form of surjectivity for restricted maps on embedded Zassenhaus terms. -/
@[simp] theorem zTSubgro.maprange_eqtop_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.map (p := p) φ hmn).range = ⊤ := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.maprange_eqtop_mapsonto honto hmn

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Bijectivity of restricted Zassenhaus-term maps under termwise-onto and injective hypotheses. -/
theorem zTSubgro.map_bijmaps_ontoinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (zTSubgro.map (p := p) φ hmn) := by
  simpa [zTSubgro.map] using
    DFilt.tSOf.map_bijmaps_ontoinj honto hinj hmn

/-- Equivalence on embedded Zassenhaus terms induced by a termwise-onto injective map. -/
noncomputable def zTSubgro.equiv_maps_ontoinj {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro p G hmn ≃* zTSubgro p H hmn :=
  DFilt.tSOf.equiv_maps_ontoinj honto hinj hmn

@[simp] theorem zTSubgro.equivmaps_ontoinj_monoidhom {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).toMonoidHom =
      zTSubgro.map (p := p) φ hmn := by
  rfl

@[simp] theorem zTSubgro.equiv_mapsonto_injapply {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro p G hmn) :
    zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn x =
      zTSubgro.map (p := p) φ hmn x := rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Left inverse cancellation for onto-injective embedded Zassenhaus-term equivalences. -/
@[simp] theorem zTSubgro.equivm_ontoi_symma {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (x : zTSubgro p G hmn) :
    (zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).symm
        (zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn x) = x := by
  exact DFilt.tSOf.equivm_ontoi_symma
    honto hinj hmn x

/-- Right inverse cancellation for onto-injective embedded Zassenhaus-term equivalences. -/
@[simp] theorem zTSubgro.equivm_ontoi_apply {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (y : zTSubgro p H hmn) :
    zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn
        ((zTSubgro.equiv_maps_ontoinj (p := p)
          honto hinj hmn).symm y) = y := by
  exact DFilt.tSOf.equivm_ontoi_apply
    honto hinj hmn y

/-- The inverse Zassenhaus embedded-term equivalence chooses an ambient preimage. -/
theorem zTSubgro.equivmaps_ontoinj_symmapplycoe {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (y : zTSubgro p H hmn) :
    φ ((((zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).symm y :
        zTSubgro p G hmn) : zSubgro p G m) : G) =
      ((y : zSubgro p H m) : H) := by
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplycoe
    honto hinj hmn y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Surjectivity on nested-inclusion-range quotients of Zassenhaus terms under
termwise onto maps. -/
theorem zTSubgro.inclus_quotm_surjm {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Surjective
      (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk) := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_surjm
      honto hmn hnk

/-- Range-top form for nested-inclusion-range quotient maps of Zassenhaus terms. -/
@[simp] theorem
    zTSubgro.inclrangquot_maprangeeq_topmapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk).range =
      ⊤ := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclrangquot_maprangeeq_topmapsonto
      honto hmn hnk

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Symmetric inverse-characterization for onto-injective embedded Zassenhaus-term equivalences. -/
theorem zTSubgro.equivmaps_ontoinj_symmapplyeq {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro p H hmn)
    (x : zTSubgro p G hmn) :
    (zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).symm y = x ↔
      y = zTSubgro.map (p := p) φ hmn x := by
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplyeq
    honto hinj hmn y x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Termwise-onto maps carry nested-inclusion ranges of Zassenhaus terms onto target ranges. -/
theorem zTSubgro.maprange_inclusioneq_mapsonto {G H : Type*}
    [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((zTSubgro.inclusion (p := p) (G := G) hmn hnk).range).map
        (zTSubgro.map (p := p) φ hmn) =
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range := by
  apply le_antisymm
  · exact zTSubgro.map_range_inclusionle (p := p) φ hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    rcases zTSubgro.map_surj_mapsonto (p := p) honto
        (Nat.le_trans hmn hnk) z with ⟨w, hw⟩
    refine ⟨zTSubgro.inclusion (p := p) (G := G) hmn hnk w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · rw [← zTSubgro.inclusion_map_apply (p := p) φ hmn hnk w]
      exact congrArg (zTSubgro.inclusion (p := p) (G := H) hmn hnk) hw

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Onto-injective maps induce equivalences on quotients by nested Zassenhaus-term ranges. -/
noncomputable def zTSubgro.inclus_quote_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro p G hmn ⧸
        (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) ≃*
      (zTSubgro p H hmn ⧸
        (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) := by
  let e := zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn
  refine QuotientGroup.congr
    (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range
    (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range e ?_
  dsimp [e]
  simpa [zTSubgro.equivmaps_ontoinj_monoidhom] using
    zTSubgro.maprange_inclusioneq_mapsonto (p := p) honto hmn hnk

@[simp] theorem zTSubgro.inclus_quote_ontoi
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro p G hmn) :
    zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk
        (QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range x) =
      QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range
        (zTSubgro.map (p := p) φ hmn x) := by
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

@[simp] theorem
    zTSubgro.inclra_equiv_injmo
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).toMonoidHom =
      zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Bijectivity form for nested-range quotient maps of Zassenhaus terms. -/
theorem zTSubgro.inclus_quotm_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Bijective
      (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk) := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_mapso
      honto hinj hmn hnk

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Inverse representative formula for nested-range quotient equivalences of Zassenhaus terms. -/
@[simp] theorem zTSubgro.inclra_equiv_injsa
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : zTSubgro (p := p) (G := H) hmn) :
    (zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).symm
      (QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range y) =
    QuotientGroup.mk' (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range
      ((zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).symm y) := by
  simpa [zTSubgro.inclus_quote_mapso,
    zTSubgro.equiv_maps_ontoinj,
    zTSubgro.inclusion] using
    DFilt.tSOf.inclra_equiv_injsa
      (F := zassenhausFiltration p G) (E := zassenhausFiltration p H) honto hinj hmn hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Injectivity form for nested-range quotient maps of Zassenhaus terms. -/
theorem zTSubgro.inclus_quotm_mapsa
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective
      (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk) := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    DFilt.tSOf.inclus_quotm_mapsa
      honto hinj hmn hnk

/-- Kernel form for nested-range quotient maps of Zassenhaus terms. -/
@[simp] theorem zTSubgro.inclus_quotm_kereq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk).ker = ⊥ := by
  exact (MonoidHom.ker_eq_bot_iff _).2
    (zTSubgro.inclus_quotm_mapsa
      (p := p) honto hinj hmn hnk)

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Equality reflection for nested-range quotient maps of Zassenhaus terms. -/
theorem zTSubgro.inclus_quotm_eqapp
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : zTSubgro (p := p) (G := G) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk x =
        zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk y ↔ x = y := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    tSOf.inclra_mapap_iffma
      honto hinj hmn hnk x y

/-- One-reflection form for nested-range quotient maps of Zassenhaus terms. -/
@[simp] theorem zTSubgro.inclus_quotm_eqone
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro (p := p) (G := G) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk x = 1 ↔ x = 1 := by
  simpa [zTSubgro.inclusion_range_quotmap] using
    tSOf.inclrangquot_mapapplyeqone_iffmapsontoinj
      honto hinj hmn hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Inverse-after-map cancellation for onto-injective Zassenhaus embedded-term equivalences. -/
@[simp] theorem zTSubgro.equivsymm_applymap_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro (p := p) (G := G) hmn) :
    (zTSubgro.equiv_maps_ontoinj (p := p) honto hinj hmn).symm
        (zTSubgro.map (p := p) φ hmn x) = x := by
  change (DFilt.tSOf.equiv_maps_ontoinj
      honto hinj hmn).symm
      (DFilt.tSOf.map
        (DFilt.MapsOnto.preserves honto) hmn x) = x
  exact DFilt.tSOf.equivmaps_ontoinj_symmapplymap
    honto hinj hmn x

/-- Map-after-inverse cancellation for onto-injective Zassenhaus embedded-term equivalences. -/
@[simp] theorem zTSubgro.mapapply_equivsymm_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (y : zTSubgro (p := p) (G := H) hmn) :
    zTSubgro.map (p := p) φ hmn
        ((zTSubgro.equiv_maps_ontoinj
          (p := p) honto hinj hmn).symm y) = y := by
  change DFilt.tSOf.map
      (DFilt.MapsOnto.preserves honto) hmn
      ((DFilt.tSOf.equiv_maps_ontoinj
        honto hinj hmn).symm y) = y
  exact DFilt.tSOf.mapapply_equivmaps_ontoinjsymm
    honto hinj hmn y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Inverse-after-map cancellation for onto-injective Zassenhaus nested-range quotients. -/
@[simp] theorem zTSubgro.rangequot_equivsymm_applymap
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro (p := p) (G := G) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    (zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).symm
      (zTSubgro.inclusion_range_quotmap
        (p := p) φ hmn hnk x) = x := by
  change (tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm
    (tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk x) = x
  exact tSOf.inclra_equiv_injsy
    honto hinj hmn hnk x

/-- Map-after-inverse cancellation for onto-injective Zassenhaus nested-range quotients. -/
@[simp] theorem zTSubgro.rangequot_mapapply_equivsymm
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : zTSubgro (p := p) (G := H) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap
        (p := p) φ hmn hnk
      ((zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).symm y) = y := by
  change tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk
      ((tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm y) = y
  exact tSOf.inclra_mapap_mapso
    honto hinj hmn hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Inverse-characterization for onto-injective Zassenhaus nested-range quotient equivalences. -/
theorem zTSubgro.rangequot_equivsymm_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : zTSubgro (p := p) (G := H) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range)
    (x : zTSubgro (p := p) (G := G) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) :
    (zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).symm y = x ↔
      y = zTSubgro.inclusion_range_quotmap
        (p := p) φ hmn hnk x := by
  change (tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm y = x ↔
    y = tSOf.inclusion_range_quotmap
      (DFilt.MapsOnto.preserves honto) hmn hnk x
  exact tSOf.inclrangquot_equivmapsonto_injsymmapplyeq
    honto hinj hmn hnk y x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for onto-injective Zassenhaus embedded-term equivalences. -/
theorem zTSubgro.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ)
    (hψ : DFilt.MapsOnto (zassenhausFiltration p H)
      (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.equiv_maps_ontoinj (p := p)
        (DFilt.MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (zTSubgro.equiv_maps_ontoinj (p := p)
        hφ hinjφ hmn).trans
        (zTSubgro.equiv_maps_ontoinj (p := p)
          hψ hinjψ hmn) := by
  change tSOf.equiv_maps_ontoinj
      (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (tSOf.equiv_maps_ontoinj hφ hinjφ hmn).trans
      (tSOf.equiv_maps_ontoinj hψ hinjψ hmn)
  exact tSOf.equiv_mapsonto_injcomp hφ hψ hinjφ hinjψ hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for onto-injective Zassenhaus nested-range quotient equivalences. -/
theorem zTSubgro.range_quot_equivcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ)
    (hψ : DFilt.MapsOnto (zassenhausFiltration p H)
      (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro.inclus_quote_mapso
        (p := p) (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn hnk =
      (zTSubgro.inclus_quote_mapso
        (p := p) hφ hinjφ hmn hnk).trans
        (zTSubgro.inclus_quote_mapso
          (p := p) hψ hinjψ hmn hnk) := by
  change tSOf.inclus_quote_mapso
      (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn hnk =
    (tSOf.inclus_quote_mapso
      hφ hinjφ hmn hnk).trans
      (tSOf.inclus_quote_mapso
        hψ hinjψ hmn hnk)
  exact tSOf.inclusionrange_quotequivmaps_ontoinjcomp
    hφ hψ hinjφ hinjψ hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Identity law for onto-injective Zassenhaus embedded-term equivalences. -/
@[simp] theorem zTSubgro.equiv_mapsonto_injid
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    zTSubgro.equiv_maps_ontoinj (p := p)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
      MulEquiv.refl (zTSubgro (p := p) (G := G) hmn) := by
  change tSOf.equiv_maps_ontoinj
      (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
    MulEquiv.refl (tSOf (zassenhausFiltration p G) hmn)
  exact tSOf.equiv_mapsonto_injid (zassenhausFiltration p G) hmn

/-- Identity law for onto-injective Zassenhaus nested-range quotient equivalences. -/
@[simp] theorem zTSubgro.range_quot_equivid
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    zTSubgro.inclus_quote_mapso (p := p)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn hnk =
      MulEquiv.refl
        (zTSubgro (p := p) (G := G) hmn ⧸
          (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range) := by
  change tSOf.inclus_quote_mapso
      (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn hnk =
    MulEquiv.refl (tSOf (zassenhausFiltration p G) hmn ⧸
      (tSOf.inclusion (F := zassenhausFiltration p G) hmn hnk).range)
  exact tSOf.inclusionrange_quotequivmaps_ontoinjid
    (zassenhausFiltration p G) hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for onto-injective Zassenhaus embedded-term equivalences. -/
theorem zTSubgro.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro (p := p) (G := G) hmn)
    (y : zTSubgro (p := p) (G := H) hmn) :
    zTSubgro.map (p := p) φ hmn x = y ↔
      x = (zTSubgro.equiv_maps_ontoinj
        (p := p) honto hinj hmn).symm y := by
  change tSOf.map (MapsOnto.preserves honto) hmn x = y ↔
    x = (tSOf.equiv_maps_ontoinj honto hinj hmn).symm y
  exact tSOf.equivmaps_ontoinj_applyeq honto hinj hmn x y

/-- Forward-image characterization for Zassenhaus nested-range quotient equivalences. -/
theorem zTSubgro.range_quotequiv_applyeq
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : zTSubgro (p := p) (G := G) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := G) hmn hnk).range)
    (y : zTSubgro (p := p) (G := H) hmn ⧸
      (zTSubgro.inclusion (p := p) (G := H) hmn hnk).range) :
    zTSubgro.inclusion_range_quotmap (p := p) φ hmn hnk x = y ↔
      x = (zTSubgro.inclus_quote_mapso
        (p := p) honto hinj hmn hnk).symm y := by
  change tSOf.inclusion_range_quotmap
      (MapsOnto.preserves honto) hmn hnk x = y ↔
    x = (tSOf.inclus_quote_mapso
      honto hinj hmn hnk).symm y
  exact tSOf.inclrangquot_equivmapsonto_injapplyeq
    honto hinj hmn hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Injectivity of Zassenhaus embedded-term maps under termwise-onto injective maps. -/
theorem zTSubgro.map_injmaps_ontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (zTSubgro.map (p := p) φ hmn) := by
  change Function.Injective (tSOf.map (MapsOnto.preserves honto) hmn)
  exact tSOf.map_injmaps_ontoinj honto hinj hmn

/-- Equality reflection for Zassenhaus embedded-term maps under termwise-onto injective maps. -/
theorem zTSubgro.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x y : zTSubgro (p := p) (G := G) hmn) :
    zTSubgro.map (p := p) φ hmn x =
        zTSubgro.map (p := p) φ hmn y ↔ x = y := by
  change tSOf.map (MapsOnto.preserves honto) hmn x =
      tSOf.map (MapsOnto.preserves honto) hmn y ↔ x = y
  exact tSOf.mapapp_eqapp_mapso
    honto hinj hmn x y

/-- One-reflection form for Zassenhaus embedded-term maps under termwise-onto injective maps. -/
@[simp] theorem zTSubgro.mapapply_eqoneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : zTSubgro (p := p) (G := G) hmn) :
    zTSubgro.map (p := p) φ hmn x = 1 ↔ x = 1 := by
  change tSOf.map (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact tSOf.mapapply_eqoneiff_mapsontoinj
    honto hinj hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}

/-- Forward-image characterization for onto-injective Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : DFilt.MapsOnto (zassenhausFiltration p G)
      (zassenhausFiltration p H) φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : zQuot p G n) (y : zQuot p H n) :
    zQuot.map p G φ n x = y ↔
      x = (zQuot.equiv_maps_ontoinj p G φ honto hinj n).symm y := by
  change DFilt.quotientMap (DFilt.MapsOnto.preserves honto) n x = y ↔
    x = (DFilt.quotientOntoInjective honto hinj n).symm y
  exact DFilt.onto_injective
    honto hinj n x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Identity law for onto-injective Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    zQuot.equiv_maps_ontoinj p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) n =
      MulEquiv.refl (zQuot p G n) := by
  change quotientOntoInjective
      (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) n =
    MulEquiv.refl (G ⧸ (zassenhausFiltration p G) n)
  exact quotient_injective_id (zassenhausFiltration p G) n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for onto-injective Zassenhaus quotient equivalences. -/
theorem zQuot.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    zQuot.equiv_maps_ontoinj p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (zQuot.equiv_maps_ontoinj p G φ hφ hinjφ n).trans
        (zQuot.equiv_maps_ontoinj p H ψ hψ hinjψ n) := by
  change quotientOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (quotientOntoInjective hφ hinjφ n).trans
      (quotientOntoInjective hψ hinjψ n)
  exact quotient_injective_comp hφ hψ hinjφ hinjψ n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for Zassenhaus term-quotient equivalences. -/
theorem zassenhaus_maps_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G φ hmn x = y ↔
      x = (termOntoInjective
        p G φ honto hinj hmn).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsInjective honto hinj hmn).symm y
  exact term_injective honto hinj hmn x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Identity law for Zassenhaus term-quotient equivalences. -/
@[simp] theorem maps_injective_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    termOntoInjective p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
      MulEquiv.refl
        (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  change termMapsInjective
      (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
    MulEquiv.refl ((zassenhausFiltration p G) m ⧸
      tSOf (zassenhausFiltration p G) hmn)
  exact term_injective_id (zassenhausFiltration p G) hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for Zassenhaus term-quotient equivalences. -/
theorem maps_injective_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    termOntoInjective p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (termOntoInjective p G φ hφ hinjφ hmn).trans
        (termOntoInjective p H ψ hψ hinjψ hmn) := by
  change termMapsInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (termMapsInjective hφ hinjφ hmn).trans
      (termMapsInjective hψ hinjψ hmn)
  exact term_equiv_comp hφ hψ hinjφ hinjψ hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for Zassenhaus transition-kernel equivalences. -/
theorem zassenhaus_onto_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn))
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn x = y ↔
      x = (mapsOntoInjective
        p G φ honto hinj hmn).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionOntoInjective honto hinj hmn).symm y
  exact transition_injective honto hinj hmn x y

/-- Inverse-after-map cancellation for onto-injective Zassenhaus transition kernels. -/
@[simp] theorem onto_injective_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (mapsOntoInjective
        p G φ honto hinj hmn).symm
      (transitionKernel p G φ hmn x) = x := by
  change (transitionOntoInjective honto hinj hmn).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact equiv_injective_symm honto hinj hmn x

/-- Map-after-inverse cancellation for onto-injective Zassenhaus transition kernels. -/
@[simp] theorem maps_injective_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn
        ((mapsOntoInjective
          p G φ honto hinj hmn).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionOntoInjective honto hinj hmn).symm y) = y
  exact transition_equiv_injective honto hinj hmn y

/-- Onto-injective Zassenhaus transition-kernel maps reflect equality. -/
theorem transition_onto_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x y : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x =
        transitionKernel p G φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_kernel_injective
    honto hinj hmn x y

/-- Onto-injective Zassenhaus transition-kernel maps reflect the identity. -/
theorem zassenhaus_transition_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_one_injective honto hinj hmn x

/-- Identity law for Zassenhaus transition-kernel equivalences. -/
@[simp] theorem onto_injective_id
    (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    mapsOntoInjective p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
      MulEquiv.refl (MonoidHom.ker (zassenhaus p G hmn)) := by
  change transitionOntoInjective
      (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) hmn =
    MulEquiv.refl (MonoidHom.ker (quotientTransition (zassenhausFiltration p G) hmn))
  exact transition_injective_id (zassenhausFiltration p G) hmn

/-- Composition law for Zassenhaus transition-kernel equivalences. -/
theorem onto_injective_comp
    {G H K : Type*} [Group G] [Group H] [Group K] {p : ℕ}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    mapsOntoInjective p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (mapsOntoInjective
        p G φ hφ hinjφ hmn).trans
        (mapsOntoInjective
          p H ψ hψ hinjψ hmn) := by
  change transitionOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
    (transitionOntoInjective hφ hinjφ hmn).trans
      (transitionOntoInjective hψ hinjψ hmn)
  exact transition_injective_comp hφ hψ hinjφ hinjψ hmn

/-- Forward-image characterization for small-kernel Zassenhaus transition equivalences. -/
theorem equiv_maps_ker
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : MonoidHom.ker (zassenhaus p G hmn))
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn x = y ↔
      x = (transitionMapsKer
        p G φ honto hmn hker).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionMapsOnto honto hmn hker).symm y
  exact transition_kernel_equiv honto hmn hker x y

/-- Forward-image characterization for monotone small-kernel Zassenhaus transition equivalences. -/
theorem zassenhaus_transition_onto
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn))
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn x = y ↔
      x = (mapsOntoKer
        p G φ honto hmn hker hnk).symm y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = y ↔
    x = (transitionOntoKer honto hmn hker hnk).symm y
  exact transition_equiv_ker honto hmn hker hnk x y

/-- Inverse-after-map cancellation for small-kernel Zassenhaus transition equivalences. -/
@[simp] theorem kernel_maps_symm
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (transitionMapsKer
        p G φ honto hmn hker).symm
      (transitionKernel p G φ hmn x) = x := by
  change (transitionMapsOnto honto hmn hker).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact transition_kernel_onto honto hmn hker x

/-- Map-after-inverse cancellation for small-kernel Zassenhaus transition equivalences. -/
@[simp] theorem zassenhaus_transition_maps
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn
        ((transitionMapsKer
          p G φ honto hmn hker).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionMapsOnto honto hmn hker).symm y) = y
  exact transition_equiv_maps honto hmn hker y

/-- Inverse-after-map cancellation for monotone small-kernel Zassenhaus transition equivalences. -/
@[simp] theorem zassenhaus_transition_symm
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    (mapsOntoKer
        p G φ honto hmn hker hnk).symm
      (transitionKernel p G φ hmn x) = x := by
  change (transitionOntoKer honto hmn hker hnk).symm
      (transitionKernelMap (MapsOnto.preserves honto) hmn x) = x
  exact transition_kernel_symm honto hmn hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel Zassenhaus transition equivalences. -/
@[simp] theorem zassenhaus_onto_symm
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (y : MonoidHom.ker (zassenhaus p H hmn)) :
    transitionKernel p G φ hmn
        ((mapsOntoKer
          p G φ honto hmn hker hnk).symm y) = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn
      ((transitionOntoKer honto hmn hker hnk).symm y) = y
  exact transition_equiv_symm honto hmn hker hnk y

/-- Small-kernel Zassenhaus transition maps reflect equality. -/
theorem zassenhaus_transition_ker
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x y : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x =
        transitionKernel p G φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_kernel_maps
    honto hmn hker x y

/-- Small-kernel Zassenhaus transition maps reflect the identity. -/
theorem kernel_onto_ker
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_one_ker honto hmn hker x

/-- Monotone small-kernel Zassenhaus transition maps reflect equality. -/
theorem transition_onto_ker
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x y : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x =
        transitionKernel p G φ hmn y ↔ x = y := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x =
      transitionKernelMap (MapsOnto.preserves honto) hmn y ↔ x = y
  exact transition_maps_onto
    honto hmn hker hnk x y

/-- Monotone small-kernel Zassenhaus transition maps reflect the identity. -/
theorem transition_maps_ker
    {G H : Type*} [Group G] [Group H] {p : ℕ} (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    transitionKernel p G φ hmn x = 1 ↔ x = 1 := by
  change transitionKernelMap (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact transition_kernel_ker
    honto hmn hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for small-kernel Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G n)
    (x : zQuot p G n) (y : zQuot p H n) :
    zQuot.map p G φ n x = y ↔
      x = (zQuot.equiv_mapsonto_kerle
        p G φ honto hker).symm y := by
  change quotientMap (MapsOnto.preserves honto) n x = y ↔
    x = (quotientMapsKer honto hker).symm y
  exact maps_ker honto hker x y

/-- Forward-image characterization for monotone small-kernel Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (x : zQuot p G m) (y : zQuot p H m) :
    zQuot.map p G φ m x = y ↔
      x = (zQuot.equivmaps_ontoker_lele
        p G φ honto hker hmn).symm y := by
  change quotientMap (MapsOnto.preserves honto) m x = y ↔
    x = (quotientOntoKer honto hker hmn).symm y
  exact equiv_onto_ker honto hker hmn x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for small-kernel Zassenhaus term-quotient equivalences. -/
theorem equiv_maps_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G φ hmn x = y ↔
      x = (zassenhausOntoKer
        p G φ honto hmn hker).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsOnto honto hmn hker).symm y
  exact term_quotient_equiv honto hmn hker x y

/-- Forward-image characterization for monotone small-kernel Zassenhaus term quotients. -/
theorem zassenhaus_term_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G φ hmn x = y ↔
      x = (termOntoKer
        p G φ honto hmn hker hnk).symm y := by
  change termQuotient (MapsOnto.preserves honto) hmn x = y ↔
    x = (termMapsKer honto hmn hker hnk).symm y
  exact term_equiv_ker honto hmn hker hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Small-kernel Zassenhaus quotient maps reflect equality. -/
theorem zQuot.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G n)
    (x y : zQuot p G n) :
    zQuot.map p G φ n x =
        zQuot.map p G φ n y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) n x =
      quotientMap (MapsOnto.preserves honto) n y ↔ x = y
  exact quotient_maps_onto honto hker x y

/-- Small-kernel Zassenhaus quotient maps reflect the identity. -/
theorem zQuot.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G n)
    (x : zQuot p G n) :
    zQuot.map p G φ n x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_onto_ker honto hker x

/-- Monotone small-kernel Zassenhaus quotient maps reflect equality. -/
theorem zQuot.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (x y : zQuot p G m) :
    zQuot.map p G φ m x =
        zQuot.map p G φ m y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) m x =
      quotientMap (MapsOnto.preserves honto) m y ↔ x = y
  exact quotient_onto_ker
    honto hker hmn x y

/-- Monotone small-kernel Zassenhaus quotient maps reflect the identity. -/
theorem zQuot.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (x : zQuot p G m) :
    zQuot.map p G φ m x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) m x = 1 ↔ x = 1
  exact quotient_maps_ker honto hker hmn x

/-- Small-kernel Zassenhaus term-quotient maps reflect equality. -/
theorem zassenhaus_onto_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x y : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x =
        zassenhausTerm p G φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_quotient_ker
    honto hmn hker x y

/-- Small-kernel Zassenhaus term-quotient maps reflect the identity. -/
theorem zassenhaus_maps_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_one_ker honto hmn hker x

/-- Monotone small-kernel Zassenhaus term-quotient maps reflect equality. -/
theorem maps_onto_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x y : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x =
        zassenhausTerm p G φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_maps_ker
    honto hmn hker hnk x y

/-- Monotone small-kernel Zassenhaus term-quotient maps reflect the identity. -/
theorem term_onto_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_maps_onto
    honto hmn hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Identity law for small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    zQuot.equiv_mapsonto_kerle p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G))
        (id_ker_le (zassenhausFiltration p G) n) =
      MulEquiv.refl (zQuot p G n) := by
  change quotientMapsKer (mapsOnto_id (zassenhausFiltration p G))
      (id_ker_le (zassenhausFiltration p G) n) = _
  exact quotient_onto_id (zassenhausFiltration p G) n

/-- Identity law for monotone small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.equivmaps_ontoker_leleid
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    zQuot.equivmaps_ontoker_lele p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G))
        (id_ker_le (zassenhausFiltration p G) n) hmn =
      MulEquiv.refl (zQuot p G m) := by
  change quotientOntoKer
      (mapsOnto_id (zassenhausFiltration p G))
      (id_ker_le (zassenhausFiltration p G) n) hmn = _
  exact maps_ker_id (zassenhausFiltration p G) hmn

/-- Identity law for small-kernel Zassenhaus term-quotient equivalences. -/
@[simp] theorem term_maps_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    zassenhausOntoKer p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) hmn
        (id_ker_le (zassenhausFiltration p G) n) =
      MulEquiv.refl (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  change termMapsOnto
      (mapsOnto_id (zassenhausFiltration p G)) hmn
      (id_ker_le (zassenhausFiltration p G) n) = _
  exact term_ker_id (zassenhausFiltration p G) hmn

/-- Identity law for monotone small-kernel Zassenhaus term-quotient equivalences. -/
@[simp] theorem onto_ker_id
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    termOntoKer p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) hmn
        (id_ker_le (zassenhausFiltration p G) k) hnk =
      MulEquiv.refl (zSubgro p G m ⧸ zTSubgro p G hmn) := by
  change termMapsKer
      (mapsOnto_id (zassenhausFiltration p G)) hmn
      (id_ker_le (zassenhausFiltration p G) k) hnk = _
  exact term_onto_id (zassenhausFiltration p G) hmn hnk

/-- Identity law for small-kernel Zassenhaus transition-kernel equivalences. -/
@[simp] theorem transition_maps_id
    (G : Type*) [Group G] {m n : ℕ} (hmn : m ≤ n) :
    transitionMapsKer p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) hmn
        (id_ker_le (zassenhausFiltration p G) n) =
      MulEquiv.refl (MonoidHom.ker (zassenhaus p G hmn)) := by
  change transitionMapsOnto
      (mapsOnto_id (zassenhausFiltration p G)) hmn
      (id_ker_le (zassenhausFiltration p G) n) = _
  exact transition_ker_id (zassenhausFiltration p G) hmn

/-- Identity law for monotone small-kernel Zassenhaus transition-kernel equivalences. -/
@[simp] theorem maps_onto_id
    (G : Type*) [Group G] {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    mapsOntoKer p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) hmn
        (id_ker_le (zassenhausFiltration p G) k) hnk =
      MulEquiv.refl (MonoidHom.ker (zassenhaus p G hmn)) := by
  change transitionOntoKer
      (mapsOnto_id (zassenhausFiltration p G)) hmn
      (id_ker_le (zassenhausFiltration p G) k) hnk = _
  exact transition_onto_id (zassenhausFiltration p G) hmn hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Inverse-after-map cancellation for small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G n)
    (x : zQuot p G n) :
    (zQuot.equiv_mapsonto_kerle p G φ honto hker).symm
        (zQuot.map p G φ n x) = x := by
  change (quotientMapsKer honto hker).symm
      (quotientMap (MapsOnto.preserves honto) n x) = x
  exact quotient_equiv_symm honto hker x

/-- Map-after-inverse cancellation for small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G n)
    (y : zQuot p H n) :
    zQuot.map p G φ n
        ((zQuot.equiv_mapsonto_kerle p G φ honto hker).symm y) = y := by
  change quotientMap (MapsOnto.preserves honto) n
      ((quotientMapsKer honto hker).symm y) = y
  exact quotient_equiv_onto honto hker y

/-- Inverse-after-map cancellation for monotone small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (x : zQuot p G m) :
    (zQuot.equivmaps_ontoker_lele p G φ honto hker hmn).symm
        (zQuot.map p G φ m x) = x := by
  change (quotientOntoKer honto hker hmn).symm
      (quotientMap (MapsOnto.preserves honto) m x) = x
  exact quotient_onto_symm honto hker hmn x

/-- Map-after-inverse cancellation for monotone small-kernel Zassenhaus quotient equivalences. -/
@[simp] theorem zQuot.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hker : φ.ker ≤ zSubgro p G n) (hmn : m ≤ n)
    (y : zQuot p H m) :
    zQuot.map p G φ m
        ((zQuot.equivmaps_ontoker_lele
          p G φ honto hker hmn).symm y) = y := by
  change quotientMap (MapsOnto.preserves honto) m
      ((quotientOntoKer honto hker hmn).symm y) = y
  exact equiv_ker_symm honto hker hmn y

/-- Inverse-after-map cancellation for small-kernel Zassenhaus term-quotient equivalences. -/
@[simp] theorem zassenhaus_term_onto
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (zassenhausOntoKer p G φ honto hmn hker).symm
        (zassenhausTerm p G φ hmn x) = x := by
  change (termMapsOnto honto hmn hker).symm
      (termQuotient (MapsOnto.preserves honto) hmn x) = x
  exact term_quotient_onto honto hmn hker x

/-- Map-after-inverse cancellation for small-kernel Zassenhaus term-quotient equivalences. -/
@[simp] theorem zassenhaus_term_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n : ℕ} (hmn : m ≤ n) (hker : φ.ker ≤ zSubgro p G n)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G φ hmn
        ((zassenhausOntoKer p G φ honto hmn hker).symm y) = y := by
  change termQuotient (MapsOnto.preserves honto) hmn
      ((termMapsOnto honto hmn hker).symm y) = y
  exact term_quotient_maps honto hmn hker y

/-- Inverse-after-map cancellation for monotone small-kernel Zassenhaus term quotients. -/
@[simp] theorem zassenhaus_ker_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    (termOntoKer
        p G φ honto hmn hker hnk).symm
      (zassenhausTerm p G φ hmn x) = x := by
  change (termMapsKer honto hmn hker hnk).symm
      (termQuotient (MapsOnto.preserves honto) hmn x) = x
  exact term_quotient_symm honto hmn hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel Zassenhaus term quotients. -/
@[simp] theorem onto_ker_symm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hker : φ.ker ≤ zSubgro p G k) (hnk : n ≤ k)
    (y : zSubgro p H m ⧸ zTSubgro p H hmn) :
    zassenhausTerm p G φ hmn
        ((termOntoKer
          p G φ honto hmn hker hnk).symm y) = y := by
  change termQuotient (MapsOnto.preserves honto) hmn
      ((termMapsKer honto hmn hker hnk).symm y) = y
  exact term_equiv_symm honto hmn hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Onto-injective Zassenhaus quotient maps reflect equality. -/
theorem zQuot.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x y : zQuot p G n) :
    zQuot.map p G φ n x =
        zQuot.map p G φ n y ↔ x = y := by
  change quotientMap (MapsOnto.preserves honto) n x =
      quotientMap (MapsOnto.preserves honto) n y ↔ x = y
  exact quotient_onto_injective honto hinj n x y

/-- Onto-injective Zassenhaus quotient maps reflect the identity. -/
theorem zQuot.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : zQuot p G n) :
    zQuot.map p G φ n x = 1 ↔ x = 1 := by
  change quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_onto_injective honto hinj n x

/-- Onto-injective Zassenhaus term-quotient maps reflect equality. -/
theorem maps_onto_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x y : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x =
        zassenhausTerm p G φ hmn y ↔ x = y := by
  change termQuotient (MapsOnto.preserves honto) hmn x =
      termQuotient (MapsOnto.preserves honto) hmn y ↔ x = y
  exact term_maps_injective
    honto hinj hmn x y

/-- Onto-injective Zassenhaus term-quotient maps reflect the identity. -/
theorem term_onto_injective
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    zassenhausTerm p G φ hmn x = 1 ↔ x = 1 := by
  change termQuotient (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1
  exact term_quotient_injective honto hinj hmn x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Forward-image characterization for onto-injective consecutive Zassenhaus
quotient equivalences. -/
theorem zNQuot.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n x = y ↔
      x = (zNQuot.equiv_maps_ontoinj
        p G φ honto hinj n).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoInjective honto hinj n).symm y
  exact next_equiv_injective honto hinj n x y

/-- Forward-image characterization for small-kernel consecutive Zassenhaus quotient equivalences. -/
theorem zNQuot.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zSubgro p G n ⧸ zNTerm p G n)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n x = y ↔
      x = (zNQuot.equiv_mapsonto_kerle
        p G φ honto n hker).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextMapsKer honto n hker).symm y
  exact next_equiv_maps honto n hker x y

/-- Forward-image characterization for monotone small-kernel consecutive Zassenhaus
quotient equivalences. -/
theorem zNQuot.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n x = y ↔
      x = (zNQuot.equivmaps_ontoker_lele
        p G φ honto n hker hnk).symm y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoKer honto n hker hnk).symm y
  exact next_term_onto honto n hker hnk x y

/-- Forward-image characterization for onto-injective Zassenhaus layer equivalences. -/
theorem zLKern.equivmaps_ontoinj_applyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : zLKern p G n) (y : zLKern p H n) :
    zLKern.map p G φ n x = y ↔
      x = (zLKern.equiv_maps_ontoinj
        p G φ honto hinj n).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoInjective honto hinj n).symm y
  exact layer_injective honto hinj n x y

/-- Forward-image characterization for small-kernel Zassenhaus layer equivalences. -/
theorem zLKern.equivmaps_ontoker_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zLKern p G n) (y : zLKern p H n) :
    zLKern.map p G φ n x = y ↔
      x = (zLKern.equiv_mapsonto_kerle
        p G φ honto n hker).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerMapsKer honto n hker).symm y
  exact layer_onto honto n hker x y

/-- Forward-image characterization for monotone small-kernel Zassenhaus layer equivalences. -/
theorem zLKern.equivmaps_ontokerle_leapplyeq
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (x : zLKern p G n) (y : zLKern p H n) :
    zLKern.map p G φ n x = y ↔
      x = (zLKern.equivmaps_ontoker_lele
        p G φ honto n hker hnk).symm y := by
  change layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoKer honto n hker hnk).symm y
  exact layer_equiv_ker honto n hker hnk x y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Onto-injective consecutive Zassenhaus quotient maps reflect equality. -/
theorem zNQuot.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x y : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x =
        zNQuot.map p G φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_onto_injective
    honto hinj n x y

/-- Onto-injective consecutive Zassenhaus quotient maps reflect the identity. -/
theorem zNQuot.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_quotient_injective honto hinj n x

/-- Small-kernel consecutive Zassenhaus quotient maps reflect equality. -/
theorem zNQuot.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x y : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x =
        zNQuot.map p G φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_term_ker honto hker x y

/-- Small-kernel consecutive Zassenhaus quotient maps reflect the identity. -/
theorem zNQuot.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_quotient_ker honto hker x

/-- Monotone small-kernel consecutive Zassenhaus quotient maps reflect equality. -/
theorem zNQuot.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (x y : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x =
        zNQuot.map p G φ n y ↔ x = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n x =
      nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y
  exact next_onto_ker
    honto n hker hnk x y

/-- Monotone small-kernel consecutive Zassenhaus quotient maps reflect the identity. -/
theorem zNQuot.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p G φ n x = 1 ↔ x = 1 := by
  change nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact next_maps_ker
    honto n hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Onto-injective Zassenhaus layer maps reflect equality. -/
theorem zLKern.mapapp_eqapp_mapso
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x y : zLKern p G n) :
    zLKern.map p G φ n x =
        zLKern.map p G φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact layer_onto_injective honto hinj n x y

/-- Onto-injective Zassenhaus layer maps reflect the identity. -/
theorem zLKern.mapeq_oneiff_mapsontoinj
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : zLKern p G n) :
    zLKern.map p G φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_maps_injective honto hinj n x

/-- Small-kernel Zassenhaus layer maps reflect equality. -/
theorem zLKern.mapapp_apply_ontok
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x y : zLKern p G n) :
    zLKern.map p G φ n x =
        zLKern.map p G φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact onto_ker honto hker x y

/-- Small-kernel Zassenhaus layer maps reflect the identity. -/
theorem zLKern.mapeq_oneiffmaps_ontokerle
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    {n : ℕ} (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zLKern p G n) :
    zLKern.map p G φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact one_maps_ker honto hker x

/-- Monotone small-kernel Zassenhaus layer maps reflect equality. -/
theorem zLKern.mapapp_apply_ontoa
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k) (x y : zLKern p G n) :
    zLKern.map p G φ n x =
        zLKern.map p G φ n y ↔ x = y := by
  change layerMap (MapsOnto.preserves honto) n x =
      layerMap (MapsOnto.preserves honto) n y ↔ x = y
  exact layer_onto_ker honto n hker hnk x y

/-- Monotone small-kernel Zassenhaus layer maps reflect the identity. -/
theorem zLKern.mapeqone_iffmapsonto_kerlele
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k) (x : zLKern p G n) :
    zLKern.map p G φ n x = 1 ↔ x = 1 := by
  change layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1
  exact layer_maps_ker honto n hker hnk x

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Identity law for onto-injective Zassenhaus consecutive-quotient equivalences. -/
@[simp] theorem zNQuot.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    zNQuot.equiv_maps_ontoinj p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) n =
      MulEquiv.refl (zSubgro p G n ⧸ zNTerm p G n) := by
  exact next_injective_id (zassenhausFiltration p G) n

/-- Identity law for small-kernel Zassenhaus consecutive-quotient equivalences. -/
@[simp] theorem zNQuot.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    zNQuot.equiv_mapsonto_kerle p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) n
        (id_ker_le (zassenhausFiltration p G) (n + 1)) =
      MulEquiv.refl (zSubgro p G n ⧸ zNTerm p G n) := by
  exact next_maps_id (zassenhausFiltration p G) n

/-- Identity law for monotone small-kernel Zassenhaus consecutive-quotient equivalences. -/
@[simp] theorem zNQuot.equivmaps_ontoker_leleid
    (G : Type*) [Group G] (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    zNQuot.equivmaps_ontoker_lele p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) n
        (id_ker_le (zassenhausFiltration p G) k) hnk =
      MulEquiv.refl (zSubgro p G n ⧸ zNTerm p G n) := by
  exact next_onto_id (zassenhausFiltration p G) n hnk

/-- Identity law for onto-injective Zassenhaus layer equivalences. -/
@[simp] theorem zLKern.equiv_mapsonto_injid
    (G : Type*) [Group G] (n : ℕ) :
    zLKern.equiv_maps_ontoinj p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) (fun _ _ h => h) n =
      MulEquiv.refl (zLKern p G n) := by
  exact layer_injective_id (zassenhausFiltration p G) n

/-- Identity law for small-kernel Zassenhaus layer equivalences. -/
@[simp] theorem zLKern.equivmaps_ontoker_leid
    (G : Type*) [Group G] (n : ℕ) :
    zLKern.equiv_mapsonto_kerle p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) n
        (id_ker_le (zassenhausFiltration p G) (n + 1)) =
      MulEquiv.refl (zLKern p G n) := by
  exact layer_maps_id (zassenhausFiltration p G) n

/-- Identity law for monotone small-kernel Zassenhaus layer equivalences. -/
@[simp] theorem zLKern.equivmaps_ontoker_leleid
    (G : Type*) [Group G] (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    zLKern.equivmaps_ontoker_lele p G (MonoidHom.id G)
        (mapsOnto_id (zassenhausFiltration p G)) n
        (id_ker_le (zassenhausFiltration p G) k) hnk =
      MulEquiv.refl (zLKern p G n) := by
  exact layer_onto_id (zassenhausFiltration p G) n hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for onto-injective Zassenhaus consecutive quotient equivalences. -/
theorem zNQuot.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    zNQuot.equiv_maps_ontoinj p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (zNQuot.equiv_maps_ontoinj p G φ hφ hinjφ n).trans
        (zNQuot.equiv_maps_ontoinj p H ψ hψ hinjψ n) := by
  change nextOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (nextOntoInjective hφ hinjφ n).trans
      (nextOntoInjective hψ hinjψ n)
  exact next_injective_comp hφ hψ hinjφ hinjψ n

/-- Composition law for onto-injective Zassenhaus layer-kernel equivalences. -/
theorem zLKern.equiv_mapsonto_injcomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    zLKern.equiv_maps_ontoinj p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (zLKern.equiv_maps_ontoinj p G φ hφ hinjφ n).trans
        (zLKern.equiv_maps_ontoinj p H ψ hψ hinjψ n) := by
  change layerOntoInjective (MapsOnto.comp hφ hψ)
      (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
    (layerOntoInjective hφ hinjφ n).trans
      (layerOntoInjective hψ hinjψ n)
  exact layer_injective_comp hφ hψ hinjφ hinjψ n

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Inverse-after-map cancellation for onto-injective Zassenhaus next quotients. -/
@[simp] theorem zNQuot.equivmaps_ontoinj_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equiv_maps_ontoinj p G φ honto hinj n).symm
      (zNQuot.map p G φ n x) = x := by
  change (nextOntoInjective honto hinj n).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_injective_symm honto hinj n x

/-- Map-after-inverse cancellation for onto-injective Zassenhaus next quotients. -/
@[simp] theorem zNQuot.mapapply_equivmaps_ontoinjsymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n
        ((zNQuot.equiv_maps_ontoinj p G φ honto hinj n).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextOntoInjective honto hinj n).symm y) = y
  exact next_maps_injective honto hinj n y

/-- Inverse-after-map cancellation for small-kernel Zassenhaus next quotients. -/
@[simp] theorem zNQuot.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equiv_mapsonto_kerle p G φ honto n hker).symm
      (zNQuot.map p G φ n x) = x := by
  change (nextMapsKer honto n hker).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_term_maps honto n hker x

/-- Map-after-inverse cancellation for small-kernel Zassenhaus next quotients. -/
@[simp] theorem zNQuot.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n
        ((zNQuot.equiv_mapsonto_kerle p G φ honto n hker).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextMapsKer honto n hker).symm y) = y
  exact next_quotient_symm honto n hker y

/-- Inverse-after-map cancellation for monotone small-kernel Zassenhaus next quotients. -/
@[simp] theorem zNQuot.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.equivmaps_ontoker_lele p G φ honto n hker hnk).symm
      (zNQuot.map p G φ n x) = x := by
  change (nextOntoKer honto n hker hnk).symm
      (nextTermQuotient (MapsOnto.preserves honto) n x) = x
  exact next_ker_symm
    honto n hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel Zassenhaus next quotients. -/
@[simp] theorem zNQuot.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G φ n
        ((zNQuot.equivmaps_ontoker_lele
          p G φ honto n hker hnk).symm y) = y := by
  change nextTermQuotient (MapsOnto.preserves honto) n
      ((nextOntoKer honto n hker hnk).symm y) = y
  exact next_term_symm
    honto n hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Inverse-after-map cancellation for onto-injective Zassenhaus layer kernels. -/
@[simp] theorem zLKern.equivmaps_ontoinj_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : zLKern p G n) :
    (zLKern.equiv_maps_ontoinj p G φ honto hinj n).symm
      (zLKern.map p G φ n x) = x := by
  change (layerOntoInjective honto hinj n).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_maps_injective honto hinj n x

/-- Map-after-inverse cancellation for onto-injective Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mapapply_equivmaps_ontoinjsymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hinj : Function.Injective φ) (n : ℕ) (y : zLKern p H n) :
    zLKern.map p G φ n
        ((zLKern.equiv_maps_ontoinj p G φ honto hinj n).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerOntoInjective honto hinj n).symm y) = y
  exact layer_injective_symm honto hinj n y

/-- Inverse-after-map cancellation for small-kernel Zassenhaus layer kernels. -/
@[simp] theorem zLKern.equivmaps_ontokerle_symmapplymap
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (x : zLKern p G n) :
    (zLKern.equiv_mapsonto_kerle p G φ honto n hker).symm
      (zLKern.map p G φ n x) = x := by
  change (layerMapsKer honto n hker).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_equiv_onto honto n hker x

/-- Map-after-inverse cancellation for small-kernel Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mapapply_equivmapsonto_kerlesymm
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) (hker : φ.ker ≤ zSubgro p G (n + 1))
    (y : zLKern p H n) :
    zLKern.map p G φ n
        ((zLKern.equiv_mapsonto_kerle p G φ honto n hker).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerMapsKer honto n hker).symm y) = y
  exact layer_equiv_maps honto n hker y

/-- Inverse-after-map cancellation for monotone small-kernel Zassenhaus layer kernels. -/
@[simp] theorem zLKern.equivm_kerle_symmb
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k) (x : zLKern p G n) :
    (zLKern.equivmaps_ontoker_lele p G φ honto n hker hnk).symm
      (zLKern.map p G φ n x) = x := by
  change (layerOntoKer honto n hker hnk).symm
      (layerMap (MapsOnto.preserves honto) n x) = x
  exact layer_maps_onto honto n hker hnk x

/-- Map-after-inverse cancellation for monotone small-kernel Zassenhaus layer kernels. -/
@[simp] theorem zLKern.mapapp_mapso_leles
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (honto : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (n : ℕ) {k : ℕ} (hker : φ.ker ≤ zSubgro p G k)
    (hnk : n + 1 ≤ k) (y : zLKern p H n) :
    zLKern.map p G φ n
        ((zLKern.equivmaps_ontoker_lele p G φ honto n hker hnk).symm y) = y := by
  change layerMap (MapsOnto.preserves honto) n
      ((layerOntoKer honto n hker hnk).symm y) = y
  exact layer_ker_symm honto n hker hnk y

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for small-kernel Zassenhaus consecutive quotient equivalences. -/
theorem zNQuot.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) (hkφ : φ.ker ≤ zSubgro p G (n + 1))
    (hkψ : ψ.ker ≤ zSubgro p H (n + 1)) :
    zNQuot.equiv_mapsonto_kerle p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (zNQuot.equiv_mapsonto_kerle p G φ hφ n hkφ).trans
        (zNQuot.equiv_mapsonto_kerle p H ψ hψ n hkψ) := by
  change nextMapsKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (nextMapsKer hφ n hkφ).trans
      (nextMapsKer hψ n hkψ)
  exact next_term_comp hφ hψ n hkφ hkψ

/-- Composition law for small-kernel Zassenhaus layer-kernel equivalences. -/
theorem zLKern.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) (hkφ : φ.ker ≤ zSubgro p G (n + 1))
    (hkψ : ψ.ker ≤ zSubgro p H (n + 1)) :
    zLKern.equiv_mapsonto_kerle p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (zLKern.equiv_mapsonto_kerle p G φ hφ n hkφ).trans
        (zLKern.equiv_mapsonto_kerle p H ψ hψ n hkψ) := by
  change layerMapsKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (layerMapsKer hφ n hkφ).trans
      (layerMapsKer hψ n hkψ)
  exact equiv_maps_comp hφ hψ n hkφ hkψ

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for monotone small-kernel Zassenhaus next equivalences at a common depth. -/
theorem zNQuot.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hnk : n + 1 ≤ k) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (zNQuot.equivmaps_ontoker_lele
        p G φ hφ n hkφ hnk).trans
        (zNQuot.equivmaps_ontoker_lele
          p H ψ hψ n hkψ hnk) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (nextOntoKer hφ n hkφ hnk).trans
      (nextOntoKer hψ n hkψ hnk)
  exact next_same_level
    hφ hψ n hkφ hkψ hnk

/-- Composition law for monotone small-kernel Zassenhaus layer equivalences at a common depth. -/
theorem zLKern.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hnk : n + 1 ≤ k) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (zLKern.equivmaps_ontoker_lele
        p G φ hφ n hkφ hnk).trans
        (zLKern.equivmaps_ontoker_lele
          p H ψ hψ n hkψ hnk) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (layerOntoKer hφ n hkφ hnk).trans
      (layerOntoKer hψ n hkψ hnk)
  exact layer_same_level hφ hψ n hkφ hkψ hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Composition law for small-kernel Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontoker_lecomp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {n : ℕ} (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H n) :
    zQuot.equiv_mapsonto_kerle p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (zQuot.equiv_mapsonto_kerle p G φ hφ hkφ).trans
        (zQuot.equiv_mapsonto_kerle p H ψ hψ hkψ) := by
  change quotientMapsKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (quotientMapsKer hφ hkφ).trans
      (quotientMapsKer hψ hkψ)
  exact quotient_ker_comp hφ hψ hkφ hkψ

/-- Composition law for small-kernel Zassenhaus term-quotient equivalences. -/
theorem zassenhaus_onto_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H n) :
    zassenhausOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (zassenhausOntoKer p G φ hφ hmn hkφ).trans
        (zassenhausOntoKer p H ψ hψ hmn hkψ) := by
  change termMapsOnto (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (termMapsOnto hφ hmn hkφ).trans
      (termMapsOnto hψ hmn hkψ)
  exact term_quotient_comp hφ hψ hmn hkφ hkψ

/-- Composition law for small-kernel Zassenhaus transition-kernel equivalences. -/
theorem zassenhaus_transition_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H n) :
    transitionMapsKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (transitionMapsKer p G φ hφ hmn hkφ).trans
        (transitionMapsKer p H ψ hψ hmn hkψ) := by
  change transitionMapsOnto (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
    (transitionMapsOnto hφ hmn hkφ).trans
      (transitionMapsOnto hψ hmn hkψ)
  exact transition_equiv_comp hφ hψ hmn hkφ hkψ

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Common-depth monotone composition law for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_comps
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m k : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hmk : m ≤ k) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hmk =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ hmk).trans
        (zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ hmk) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hmk =
    (quotientOntoKer hφ hkφ hmk).trans
      (quotientOntoKer hψ hkψ hmk)
  exact ker_same_level hφ hψ hkφ hkψ hmk

/-- Common-depth monotone composition law for Zassenhaus term-quotient equivalences. -/
theorem onto_same_level
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hnk : n ≤ k) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (termOntoKer
        p G φ hφ hmn hkφ hnk).trans
        (termOntoKer
          p H ψ hψ hmn hkψ hnk) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (termMapsKer hφ hmn hkφ hnk).trans
      (termMapsKer hψ hmn hkψ hnk)
  exact term_same_level
    hφ hψ hmn hkφ hkψ hnk

/-- Common-depth monotone composition law for Zassenhaus transition-kernel equivalences. -/
theorem comp_same_level
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hnk : n ≤ k) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (mapsOntoKer
        p G φ hφ hmn hkφ hnk).trans
        (mapsOntoKer
          p H ψ hψ hmn hkψ hnk) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
    (transitionOntoKer hφ hmn hkφ hnk).trans
      (transitionOntoKer hψ hmn hkψ hnk)
  exact transition_same_level
    hφ hψ hmn hkφ hkψ hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Heterogeneous-depth composition law for monotone Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk =
      (zQuot.equivmaps_ontoker_lele
        p G φ hφ hkφ (le_trans hmk hka)).trans
        (zQuot.equivmaps_ontoker_lele
          p H ψ hψ hkψ (le_trans hmk hkb)) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk =
    (quotientOntoKer hφ hkφ (le_trans hmk hka)).trans
      (quotientOntoKer hψ hkψ (le_trans hmk hkb))
  exact quotient_maps_comp hφ hψ hkφ hkψ hka hkb hmk

/-- Heterogeneous-depth composition law for monotone Zassenhaus term-quotient equivalences. -/
theorem maps_ker_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (termOntoKer
        p G φ hφ hmn hkφ (le_trans hnk hka)).trans
        (termOntoKer
          p H ψ hψ hmn hkψ (le_trans hnk hkb)) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (termMapsKer hφ hmn hkφ (le_trans hnk hka)).trans
      (termMapsKer hψ hmn hkψ (le_trans hnk hkb))
  exact term_ker_comp hφ hψ hmn hkφ hkψ hka hkb hnk

/-- Heterogeneous-depth composition law for monotone Zassenhaus transition-kernel equivalences. -/
theorem transition_maps_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (mapsOntoKer
        p G φ hφ hmn hkφ (le_trans hnk hka)).trans
        (mapsOntoKer
          p H ψ hψ hmn hkψ (le_trans hnk hkb)) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).trans
      (transitionOntoKer hψ hmn hkψ (le_trans hnk hkb))
  exact transition_kernel_comp hφ hψ hmn hkφ hkψ hka hkb hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Heterogeneous-depth composition law for monotone Zassenhaus next-quotient equivalences. -/
theorem zNQuot.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (zNQuot.equivmaps_ontoker_lele
        p G φ hφ n hkφ (le_trans hnk hka)).trans
        (zNQuot.equivmaps_ontoker_lele
          p H ψ hψ n hkψ (le_trans hnk hkb)) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
      (nextOntoKer hψ n hkψ (le_trans hnk hkb))
  exact next_ker_comp hφ hψ n hkφ hkψ hka hkb hnk

/-- Heterogeneous-depth composition law for monotone Zassenhaus layer-kernel equivalences. -/
theorem zLKern.equivmaps_ontokerle_lecomple
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (zLKern.equivmaps_ontoker_lele
        p G φ hφ n hkφ (le_trans hnk hka)).trans
        (zLKern.equivmaps_ontoker_lele
          p H ψ hψ n hkψ (le_trans hnk hkb)) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
    (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
      (layerOntoKer hψ n hkψ (le_trans hnk hkb))
  exact layer_ker_comp hφ hψ n hkφ hkψ hka hkb hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Minimum-depth composition law for monotone Zassenhaus quotient equivalences. -/
theorem zQuot.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hm : m ≤ min a b) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).trans
        (zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
          (le_trans hm (Nat.min_le_right a b))) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm =
    (quotientOntoKer hφ hkφ
      (le_trans hm (Nat.min_le_left a b))).trans
      (quotientOntoKer hψ hkψ
        (le_trans hm (Nat.min_le_right a b)))
  exact onto_ker_min hφ hψ hkφ hkψ hm

/-- Minimum-depth composition law for monotone Zassenhaus term-quotient equivalences. -/
theorem ker_comp_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (termOntoKer p G φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (termOntoKer p H ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (termMapsKer hφ hmn hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (termMapsKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact term_onto_min hφ hψ hmn hkφ hkψ hn

/-- Minimum-depth composition law for monotone Zassenhaus transition-kernel equivalences. -/
theorem maps_comp_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (mapsOntoKer p G φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (mapsOntoKer p H ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (transitionOntoKer hφ hmn hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (transitionOntoKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact transition_maps_min hφ hψ hmn hkφ hkψ hn

/-- Minimum-depth composition law for monotone Zassenhaus next-quotient equivalences. -/
theorem zNQuot.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (nextOntoKer hφ n hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (nextOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact next_onto_min hφ hψ n hkφ hkψ hn

/-- Minimum-depth composition law for monotone Zassenhaus layer-kernel equivalences. -/
theorem zLKern.equivmaps_ontokerle_lecompmin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).trans
        (zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
      (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
    (layerOntoKer hφ n hkφ
      (le_trans hn (Nat.min_le_left a b))).trans
      (layerOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b)))
  exact layer_onto_min hφ hψ n hkφ hkψ hn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise minimum-depth composition formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hm : m ≤ min a b)
    (x : zQuot p G m) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm x =
      zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
        (le_trans hm (Nat.min_le_right a b))
        (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
          (le_trans hm (Nat.min_le_left a b)) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm x =
      quotientOntoKer hψ hkψ
        (le_trans hm (Nat.min_le_right a b))
        (quotientOntoKer hφ hkφ
          (le_trans hm (Nat.min_le_left a b)) x)
  exact maps_onto_min hφ hψ hkφ hkψ hm x

/-- Inverse pointwise minimum-depth composition formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hm : m ≤ min a b)
    (z : zQuot p K m) :
    (zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm).symm z =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).symm
        ((zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
          (le_trans hm (Nat.min_le_right a b))).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm).symm z =
      (quotientOntoKer hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).symm
        ((quotientOntoKer hψ hkψ
          (le_trans hm (Nat.min_le_right a b))).symm z)
  exact maps_min_symm hφ hψ hkφ hkψ hm z

/-- Pointwise minimum-depth composition formula for Zassenhaus term quotients. -/
theorem onto_comp_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      termOntoKer p H ψ hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (termOntoKer p G φ hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      termMapsKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (termMapsKer hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact term_comp_min hφ hψ hmn hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for Zassenhaus term quotients. -/
theorem onto_min_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b)
    (z : zSubgro p K m ⧸ zTSubgro p K hmn) :
    (termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (termOntoKer p G φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((termOntoKer p H ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (termMapsKer hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((termMapsKer hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact term_min_symm hφ hψ hmn hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise minimum-depth composition formula for Zassenhaus transition kernels. -/
theorem transition_comp_min
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      mapsOntoKer p H ψ hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (mapsOntoKer p G φ hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      transitionOntoKer hψ hmn hkψ
        (le_trans hn (Nat.min_le_right a b))
        (transitionOntoKer hφ hmn hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact transition_onto_min hφ hψ hmn hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for Zassenhaus transition kernels. -/
theorem comp_min_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n ≤ min a b)
    (z : MonoidHom.ker (zassenhaus p K hmn)) :
    (mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (mapsOntoKer p G φ hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((mapsOntoKer p H ψ hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (transitionOntoKer hφ hmn hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((transitionOntoKer hψ hmn hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact transition_min_symm hφ hψ hmn hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise minimum-depth composition formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      nextOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (nextOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact next_comp_min hφ hψ n hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b)
    (z : zSubgro p K n ⧸ zNTerm p K n) :
    (zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (nextOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((nextOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact next_min_symm hφ hψ n hkφ hkψ hn z

/-- Pointwise minimum-depth composition formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_compm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b)
    (x : zLKern p G n) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      layerOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (layerOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x)
  exact layer_comp_min hφ hψ n hkφ hkψ hn x

/-- Inverse pointwise minimum-depth composition formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_commi
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hn : n + 1 ≤ min a b)
    (z : zLKern p K n) :
    (zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (layerOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((layerOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z)
  exact layer_min_symm hφ hψ n hkφ hkψ hn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise heterogeneous-depth composition formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k)
    (x : zQuot p G m) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk x =
      zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
        (le_trans hmk hkb)
        (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
          (le_trans hmk hka) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk x =
      quotientOntoKer hψ hkψ (le_trans hmk hkb)
        (quotientOntoKer hφ hkφ (le_trans hmk hka) x)
  exact quotient_onto_comp hφ hψ hkφ hkψ hka hkb hmk x

/-- Inverse pointwise heterogeneous-depth composition formula for Zassenhaus
quotient equivalences. -/
theorem zQuot.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k)
    (z : zQuot p K m) :
    (zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk).symm z =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
        (le_trans hmk hka)).symm
        ((zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
          (le_trans hmk hkb)).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmk hka)).symm
        ((quotientOntoKer hψ hkψ (le_trans hmk hkb)).symm z)
  exact maps_ker_symm hφ hψ hkφ hkψ hka hkb hmk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise heterogeneous-depth composition formula for Zassenhaus term quotients. -/
theorem onto_ker_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      termOntoKer p H ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (termOntoKer p G φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      termMapsKer hψ hmn hkψ (le_trans hnk hkb)
        (termMapsKer hφ hmn hkφ (le_trans hnk hka) x)
  exact term_onto_comp hφ hψ hmn hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for Zassenhaus term quotients. -/
theorem term_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : zSubgro p K m ⧸ zTSubgro p K hmn) :
    (termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (termOntoKer p G φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((termOntoKer p H ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (termMapsKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact term_ker_symm hφ hψ hmn hkφ hkψ hka hkb hnk z

/-- Pointwise heterogeneous-depth composition formula for Zassenhaus transition kernels. -/
theorem maps_onto_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      mapsOntoKer p H ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (mapsOntoKer p G φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ hmn hkφ (le_trans hnk hka) x)
  exact transition_ker_comp hφ hψ hmn hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for Zassenhaus transition kernels. -/
theorem ker_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k a b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (zassenhaus p K hmn)) :
    (mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (mapsOntoKer p G φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((mapsOntoKer p H ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact transition_ker_symm hφ hψ hmn
    hkφ hkψ hka hkb hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise heterogeneous-depth composition formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hnk hkb)
        (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact next_onto_comp hφ hψ n hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for consecutive
Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : zSubgro p K n ⧸ zNTerm p K n) :
    (zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact next_maps_symm hφ hψ n
    hkφ hkψ hka hkb hnk z

/-- Pointwise heterogeneous-depth composition formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_compl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : zLKern p G n) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hnk hkb)
        (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact layer_onto_comp hφ hψ n hkφ hkψ hka hkb hnk x

/-- Inverse pointwise heterogeneous-depth composition formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_compb
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k a b : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : zLKern p K n) :
    (zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact layer_maps_symm hφ hψ n hkφ hkψ hka hkb hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}
open DFilt

/-- Zassenhaus-filtration same-depth composite-kernel containment. -/
theorem zMOnto.comp_kerle_samelevel
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {n : ℕ}
    (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H n) :
    (ψ.comp φ).ker ≤ zSubgro p G n := by
  exact MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ

/-- Zassenhaus-filtration one-sided composite-kernel containment (left depth fixed). -/
theorem zMOnto.comp_kerle_leftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {n b : ℕ}
    (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hnb : n ≤ b) :
    (ψ.comp φ).ker ≤ zSubgro p G n := by
  exact MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb

/-- Zassenhaus-filtration one-sided composite-kernel containment (right depth fixed). -/
theorem zMOnto.comp_kerle_rightle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {a n : ℕ}
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H n) (hna : n ≤ a) :
    (ψ.comp φ).ker ≤ zSubgro p G n := by
  exact MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna

/-- Zassenhaus-filtration successor-depth composite-kernel containment. -/
theorem zMOnto.comp_ker_lesucc
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {n : ℕ}
    (hkφ : φ.ker ≤ zSubgro p G (n + 1))
    (hkψ : ψ.ker ≤ zSubgro p H (n + 1)) :
    (ψ.comp φ).ker ≤ zSubgro p G n := by
  exact MapsOnto.comp_ker_lesucc hφ hψ hkφ hkψ

/-- Zassenhaus-filtration minimum-depth composite-kernel containment. -/
theorem zMOnto.comp_ker_lemin
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {a b : ℕ}
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H b) :
    (ψ.comp φ).ker ≤ zSubgro p G (min a b) := by
  exact MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- One-sided (left-depth) composition law for Zassenhaus quotient equivalences. -/
theorem zQuot.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hnb : n ≤ b) (hmn : m ≤ n) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ hmn).trans
        (zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
          (le_trans hmn hnb)) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn =
      (quotientOntoKer hφ hkφ hmn).trans
        (quotientOntoKer hψ hkψ (le_trans hmn hnb))
  exact onto_ker_left hφ hψ hkφ hkψ hnb hmn

/-- One-sided (right-depth) composition law for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H n) (hna : n ≤ a) (hmn : m ≤ n) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
        (le_trans hmn hna)).trans
        (zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ hmn) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).trans
        (quotientOntoKer hψ hkψ hmn)
  exact onto_ker_right hφ hψ hkφ hkψ hna hmn

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- One-sided (left-depth) composition law for Zassenhaus term quotients. -/
theorem ker_comp_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (termOntoKer p G φ hφ h hkφ hnk).trans
        (termOntoKer p H ψ hψ h hkψ
          (le_trans hnk hkb)) := by
  change termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (termMapsKer hφ h hkφ hnk).trans
        (termMapsKer hψ h hkψ (le_trans hnk hkb))
  exact term_onto_left hφ hψ h hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for Zassenhaus term quotients. -/
theorem ker_comp_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (termOntoKer p G φ hφ h hkφ
        (le_trans hnk hka)).trans
        (termOntoKer p H ψ hψ h hkψ hnk) := by
  change termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).trans
        (termMapsKer hψ h hkψ hnk)
  exact term_maps_comp hφ hψ h hkφ hkψ hka hnk

/-- One-sided (left-depth) composition law for Zassenhaus transition kernels. -/
theorem maps_comp_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (mapsOntoKer p G φ hφ h hkφ hnk).trans
        (mapsOntoKer p H ψ hψ h hkψ
          (le_trans hnk hkb)) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (transitionOntoKer hφ h hkφ hnk).trans
        (transitionOntoKer hψ h hkψ (le_trans hnk hkb))
  exact transition_maps_left hφ hψ h hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for Zassenhaus transition kernels. -/
theorem maps_comp_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (mapsOntoKer p G φ hφ h hkφ
        (le_trans hnk hka)).trans
        (mapsOntoKer p H ψ hψ h hkψ hnk) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).trans
        (transitionOntoKer hψ h hkψ hnk)
  exact transition_onto_right hφ hψ h hkφ hkψ hka hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- One-sided (left-depth) composition law for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ hnk).trans
        (zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (nextOntoKer hφ n hkφ hnk).trans
        (nextOntoKer hψ n hkψ (le_trans hnk hkb))
  exact next_onto_left hφ hψ n hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).trans
        (zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (nextOntoKer hψ n hkψ hnk)
  exact next_maps_comp hφ hψ n hkφ hkψ hka hnk

/-- One-sided (left-depth) composition law for Zassenhaus layer kernels. -/
theorem zLKern.equivmapsonto_kerlele_compleftle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ hnk).trans
        (zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (layerOntoKer hφ n hkφ hnk).trans
        (layerOntoKer hψ n hkψ (le_trans hnk hkb))
  exact layer_onto_left hφ hψ n hkφ hkψ hkb hnk

/-- One-sided (right-depth) composition law for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_compr
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).trans
        (zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (layerOntoKer hψ n hkψ hnk)
  exact layer_maps_comp hφ hψ n hkφ hkψ hka hnk

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise left-depth one-sided composition formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hnb : n ≤ b) (hmn : m ≤ n)
    (x : zQuot p G m) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn x =
      zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
        (le_trans hmn hnb)
        (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ hmn x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn x =
      quotientOntoKer hψ hkψ (le_trans hmn hnb)
        (quotientOntoKer hφ hkφ hmn x)
  exact maps_onto_left hφ hψ hkφ hkψ hnb hmn x

/-- Pointwise right-depth one-sided composition formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H n) (hna : n ≤ a) (hmn : m ≤ n)
    (x : zQuot p G m) :
    zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn x =
      zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ hmn
        (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
          (le_trans hmn hna) x) := by
  change quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn x =
      quotientOntoKer hψ hkψ hmn
        (quotientOntoKer hφ hkφ (le_trans hmn hna) x)
  exact maps_onto_right hφ hψ hkφ hkψ hna hmn x

/-- Inverse pointwise left-depth one-sided formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n b : ℕ} (hkφ : φ.ker ≤ zSubgro p G n)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hnb : n ≤ b) (hmn : m ≤ n)
    (z : zQuot p K m) :
    (zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn).symm z =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ hmn).symm
        ((zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ
          (le_trans hmn hnb)).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn).symm z =
      (quotientOntoKer hφ hkφ hmn).symm
        ((quotientOntoKer hψ hkψ (le_trans hmn hnb)).symm z)
  exact comp_left_symm hφ hψ hkφ hkψ hnb hmn z

/-- Inverse pointwise right-depth one-sided formula for Zassenhaus quotient equivalences. -/
theorem zQuot.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m a n : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H n) (hna : n ≤ a) (hmn : m ≤ n)
    (z : zQuot p K m) :
    (zQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn).symm z =
      (zQuot.equivmaps_ontoker_lele p G φ hφ hkφ
        (le_trans hmn hna)).symm
        ((zQuot.equivmaps_ontoker_lele p H ψ hψ hkψ hmn).symm z) := by
  change (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).symm
        ((quotientOntoKer hψ hkψ hmn).symm z)
  exact comp_right_symm hφ hψ hkφ hkψ hna hmn z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise left-depth one-sided formula for Zassenhaus term quotients. -/
theorem onto_comp_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      termOntoKer p H ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (termOntoKer p G φ hφ hmn hkφ hnk x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      termMapsKer hψ hmn hkψ (le_trans hnk hkb)
        (termMapsKer hφ hmn hkφ hnk x)
  exact term_comp_left hφ hψ hmn hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for Zassenhaus term quotients. -/
theorem onto_comp_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : zSubgro p G m ⧸ zTSubgro p G hmn) :
    termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      termOntoKer p H ψ hψ hmn hkψ hnk
        (termOntoKer p G φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      termMapsKer hψ hmn hkψ hnk
        (termMapsKer hφ hmn hkφ (le_trans hnk hka) x)
  exact term_comp_right hφ hψ hmn hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for Zassenhaus term quotients. -/
theorem maps_onto_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : zSubgro p K m ⧸ zTSubgro p K hmn) :
    (termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (termOntoKer p G φ hφ hmn hkφ hnk).symm
        ((termOntoKer p H ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (termMapsKer hφ hmn hkφ hnk).symm
        ((termMapsKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact term_maps_symm hφ hψ hmn
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for Zassenhaus term quotients. -/
theorem maps_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : zSubgro p K m ⧸ zTSubgro p K hmn) :
    (termOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (termOntoKer p G φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((termOntoKer p H ψ hψ hmn hkψ hnk).symm z) := by
  change (termMapsKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (termMapsKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ hmn hkψ hnk).symm z)
  exact term_onto_symm hφ hψ hmn
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers


namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise left-depth one-sided formula for Zassenhaus transition kernels. -/
theorem transition_comp_left
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      mapsOntoKer p H ψ hψ hmn hkψ
        (le_trans hnk hkb)
        (mapsOntoKer p G φ hφ hmn hkφ hnk x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ hmn hkφ hnk x)
  exact transition_onto_left hφ hψ hmn hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for Zassenhaus transition kernels. -/
theorem transition_comp_right
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : MonoidHom.ker (zassenhaus p G hmn)) :
    mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      mapsOntoKer p H ψ hψ hmn hkψ hnk
        (mapsOntoKer p G φ hφ hmn hkφ
          (le_trans hnk hka) x) := by
  change transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      transitionOntoKer hψ hmn hkψ hnk
        (transitionOntoKer hφ hmn hkφ (le_trans hnk hka) x)
  exact transition_onto_comp hφ hψ hmn
    hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for Zassenhaus transition kernels. -/
theorem onto_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n k b : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (zassenhaus p K hmn)) :
    (mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (mapsOntoKer p G φ hφ hmn hkφ hnk).symm
        ((mapsOntoKer p H ψ hψ hmn hkψ
          (le_trans hnk hkb)).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ hnk).symm
        ((transitionOntoKer hψ hmn hkψ (le_trans hnk hkb)).symm z)
  exact transition_maps_symm hφ hψ hmn
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for Zassenhaus transition kernels. -/
theorem transition_comp_symm
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    {m n a k : ℕ} (hmn : m ≤ n)
    (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : MonoidHom.ker (zassenhaus p K hmn)) :
    (mapsOntoKer p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (mapsOntoKer p G φ hφ hmn hkφ
        (le_trans hnk hka)).symm
        ((mapsOntoKer p H ψ hψ hmn hkψ hnk).symm z) := by
  change (transitionOntoKer (MapsOnto.comp hφ hψ) hmn
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (transitionOntoKer hφ hmn hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ hmn hkψ hnk).symm z)
  exact transition_onto_symm hφ hψ hmn
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise left-depth one-sided formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hnk hkb)
        (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ hnk x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ hnk x)
  exact next_comp_left hφ hψ n hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk
        (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      nextOntoKer hψ n hkψ hnk
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact next_comp_right hφ hψ n hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : zSubgro p K n ⧸ zNTerm p K n) :
    (zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ hnk).symm
        ((zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ hnk).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact next_onto_symm hφ hψ n
    hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for consecutive Zassenhaus quotients. -/
theorem zNQuot.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : zSubgro p K n ⧸ zNTerm p K n) :
    (zNQuot.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (zNQuot.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((zNQuot.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk).symm z) := by
  change (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ hnk).symm z)
  exact next_comp_symm hφ hψ n
    hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

noncomputable section
variable {p : ℕ}
open DFilt

/-- Pointwise left-depth one-sided formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_compa
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : zLKern p G n) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
        (le_trans hnk hkb)
        (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ hnk x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ hnk x)
  exact layer_comp_left hφ hψ n hkφ hkψ hkb hnk x

/-- Pointwise right-depth one-sided formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_comri
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : zLKern p G n) :
    zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk
        (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
          (le_trans hnk hka) x) := by
  change layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      layerOntoKer hψ n hkψ hnk
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x)
  exact layer_comp_right hφ hψ n hkφ hkψ hka hnk x

/-- Inverse pointwise left-depth one-sided formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_leftl
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {k b : ℕ} (hkφ : φ.ker ≤ zSubgro p G k)
    (hkψ : ψ.ker ≤ zSubgro p H b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : zLKern p K n) :
    (zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ hnk).symm
        ((zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ
          (le_trans hnk hkb)).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ hnk).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z)
  exact layer_onto_symm hφ hψ n hkφ hkψ hkb hnk z

/-- Inverse pointwise right-depth one-sided formula for Zassenhaus layer kernels. -/
theorem zLKern.equivm_kerle_rigle
    {G H K : Type*} [Group G] [Group H] [Group K]
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto (zassenhausFiltration p G) (zassenhausFiltration p H) φ)
    (hψ : MapsOnto (zassenhausFiltration p H) (zassenhausFiltration p K) ψ)
    (n : ℕ) {a k : ℕ} (hkφ : φ.ker ≤ zSubgro p G a)
    (hkψ : ψ.ker ≤ zSubgro p H k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : zLKern p K n) :
    (zLKern.equivmaps_ontoker_lele p G (ψ.comp φ)
        (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (zLKern.equivmaps_ontoker_lele p G φ hφ n hkφ
        (le_trans hnk hka)).symm
        ((zLKern.equivmaps_ontoker_lele p H ψ hψ n hkψ hnk).symm z) := by
  change (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ hnk).symm z)
  exact layer_comp_symm hφ hψ n hkφ hkψ hka hnk z

end
end GroupAlgebra
end Towers
