import Towers.Group.Presentation
import Towers.Group.Zassenhaus.Core

/-!
# Presentations with Zassenhaus depth bookkeeping

This module contains only bookkeeping: a presentation together with lower bounds for
the Zassenhaus depth of each relator in the ambient free group.  No Fox calculus or
minimality theorem is used here; those later layers can consume this small interface.
-/

namespace Towers

universe u

open GroupAlgebra

namespace Presentation

variable (p : ℕ) (P : Presentation.{u})

/-- The image in a presented group of the ambient free-group Zassenhaus term. -/
def zassenhausImage (n : ℕ) : Subgroup P.Group :=
  (GroupAlgebra.zSubgro p P.Free n).map P.quotientMap

instance zassenhausImage_normal (n : ℕ) : (zassenhausImage p P n).Normal := by
  classical
  dsimp [zassenhausImage]
  haveI : (GroupAlgebra.zSubgro p P.Free n).Normal :=
    GroupAlgebra.zassenhausSubgroup_normal p P.Free n
  exact (show (GroupAlgebra.zSubgro p P.Free n).Normal from inferInstance).map
    P.quotientMap P.quotientMap_surjective

/-- A word in a free Zassenhaus term maps into the corresponding presented-group image. -/
theorem zassenhaus_image {n : ℕ} {w : P.Free}
    (hw : w ∈ GroupAlgebra.zSubgro p P.Free n) :
    P.quotientMap w ∈ zassenhausImage p P n :=
  Subgroup.mem_map.mpr ⟨w, hw, rfl⟩

/-- Zassenhaus images are antitone in the index. -/
theorem zassenhausImage_antitone : Antitone (zassenhausImage p P) := by
  intro m n hmn y hy
  rcases Subgroup.mem_map.mp hy with ⟨w, hw, rfl⟩
  exact zassenhaus_image p P
    (GroupAlgebra.zassenhausSubgroup_antitone p P.Free hmn hw)

@[simp] theorem zassenhaus_image_top : zassenhausImage p P 1 = ⊤ := by
  dsimp [zassenhausImage]
  rw [GroupAlgebra.zassenhaus_one_top]
  exact Subgroup.map_top_of_surjective P.quotientMap P.quotientMap_surjective

/-- The images of the free Zassenhaus filtration inside a presented group form a
descending filtration. -/
def zassenhausImageFiltration : DFilt P.Group where
  term := zassenhausImage p P
  antitone' := zassenhausImage_antitone p P
  normal' := fun n => zassenhausImage_normal p P n
  one_eq_top' := zassenhaus_image_top p P

@[simp] theorem image_filtration_term (n : ℕ) :
    (zassenhausImageFiltration p P) n = zassenhausImage p P n := rfl

variable {P Q : Presentation.{u}}

/-- Presentation morphisms carry presented Zassenhaus images into presented
Zassenhaus images.  This is the quotient-level form of functoriality of the
ambient free-group Zassenhaus filtration. -/
theorem Hom.map_zass_imagele (f : Hom P Q) (n : ℕ) :
    (zassenhausImage p P n).map f.toGroupHom ≤ zassenhausImage p Q n := by
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  rcases Subgroup.mem_map.mp hx with ⟨w, hw, rfl⟩
  rw [Hom.group_quotient]
  exact zassenhaus_image p Q
    (GroupAlgebra.zassenhaus_subgroup_comap p P.Free f.freeMap n hw)

/-- Pointwise form of `Hom.map_zass_imagele`. -/
theorem Hom.apply_mem_zassimage (f : Hom P Q) {n : ℕ} {x : P.Group}
    (hx : x ∈ zassenhausImage p P n) :
    f.toGroupHom x ∈ zassenhausImage p Q n := by
  exact f.map_zass_imagele (p := p) n (Subgroup.mem_map_of_mem _ hx)

/-- Presentation morphisms preserve the presented Zassenhaus-image filtrations. -/
theorem Hom.preserves_zass_imagefilt (f : Hom P Q) :
    DFilt.Preserves (zassenhausImageFiltration p P)
      (zassenhausImageFiltration p Q) f.toGroupHom := by
  intro n
  exact f.map_zass_imagele (p := p) n

/-- If presentation morphisms are inverse on the nose, the forward morphism maps
presented Zassenhaus images onto presented Zassenhaus images. -/
theorem Hom.mapzass_imageeq_rightinv
    (f : Hom P Q) (g : Hom Q P)
    (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (zassenhausImage p P n).map f.toGroupHom = zassenhausImage p Q n := by
  apply le_antisymm
  · exact f.map_zass_imagele (p := p) n
  · intro y hy
    have hgy : g.toGroupHom y ∈ zassenhausImage p P n :=
      g.apply_mem_zassimage (p := p) hy
    refine Subgroup.mem_map.mpr ⟨g.toGroupHom y, hgy, ?_⟩
    have hcomp : (f.toGroupHom.comp g.toGroupHom) = MonoidHom.id Q.Group := by
      simpa using congrArg Hom.toGroupHom hright
    exact congrArg (fun φ : Q.Group →* Q.Group => φ y) hcomp

/-- Inverse presentation morphisms are termwise onto for presented Zassenhaus-image filtrations. -/
theorem Hom.mapsonto_zassimage_filtrightinv
    (f : Hom P Q) (g : Hom Q P)
    (hright : f.comp g = Hom.id Q) :
    DFilt.MapsOnto (zassenhausImageFiltration p P)
      (zassenhausImageFiltration p Q) f.toGroupHom := by
  intro n
  exact f.mapzass_imageeq_rightinv (p := p) g hright n

/-- The map induced by a presentation morphism on quotients by presented
Zassenhaus images. -/
noncomputable def Hom.zass_image_quotmap (f : Hom P Q) (n : ℕ) :
    (P.Group ⧸ zassenhausImage p P n) →* (Q.Group ⧸ zassenhausImage p Q n) :=
  QuotientGroup.map (zassenhausImage p P n) (zassenhausImage p Q n) f.toGroupHom (by
    intro x hx
    exact f.apply_mem_zassimage (p := p) hx)

@[simp] theorem Hom.zass_imagequot_mapmk (f : Hom P Q) (n : ℕ)
    (x : P.Group) :
    f.zass_image_quotmap (p := p) n
        (QuotientGroup.mk' (zassenhausImage p P n) x) =
      QuotientGroup.mk' (zassenhausImage p Q n) (f.toGroupHom x) := rfl

/-- The bespoke quotient map agrees with the generic filtration quotient map for
presented Zassenhaus-image filtrations. -/
theorem Hom.zassimage_quotmapeq_filtquotmap (f : Hom P Q)
    (n : ℕ) :
    f.zass_image_quotmap (p := p) n =
      DFilt.quotientMap
        (f.preserves_zass_imagefilt (p := p)) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem Hom.zass_imagequot_mapid (P : Presentation.{u}) (n : ℕ) :
    (Hom.id P).zass_image_quotmap (p := p) n =
      MonoidHom.id (P.Group ⧸ zassenhausImage p P n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  change QuotientGroup.mk' (zassenhausImage p P n) ((Hom.id P).toGroupHom x) =
    QuotientGroup.mk' (zassenhausImage p P n) x
  simp

variable {R : Presentation.{u}}

@[simp] theorem Hom.zass_imagequot_mapcomp (g : Hom Q R) (f : Hom P Q)
    (n : ℕ) :
    (g.comp f).zass_image_quotmap (p := p) n =
      (g.zass_image_quotmap (p := p) n).comp
        (f.zass_image_quotmap (p := p) n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  change QuotientGroup.mk' (zassenhausImage p R n) ((g.comp f).toGroupHom x) =
    QuotientGroup.mk' (zassenhausImage p R n) (g.toGroupHom (f.toGroupHom x))
  simp [Hom.comp_group_hom, MonoidHom.comp_apply]


/-- Mutually inverse presentation morphisms induce equivalences on presented-image
Zassenhaus quotients. -/
noncomputable def Hom.zass_imagequot_equivinv (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (P.Group ⧸ zassenhausImage p P n) ≃* (Q.Group ⧸ zassenhausImage p Q n) where
  toFun := f.zass_image_quotmap (p := p) n
  invFun := g.zass_image_quotmap (p := p) n
  left_inv := by
    intro x
    have hcomp := DFunLike.congr_fun
      (Hom.zass_imagequot_mapcomp (p := p) g f n) x
    rw [hleft] at hcomp
    simpa using hcomp.symm
  right_inv := by
    intro x
    have hcomp := DFunLike.congr_fun
      (Hom.zass_imagequot_mapcomp (p := p) f g n) x
    rw [hright] at hcomp
    simpa using hcomp.symm
  map_mul' := (f.zass_image_quotmap (p := p) n).map_mul

@[simp] theorem Hom.zassimage_quotequiv_invapply (f : Hom P Q)
    (g : Hom Q P) (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q)
    (n : ℕ) (x : P.Group ⧸ zassenhausImage p P n) :
    f.zass_imagequot_equivinv (p := p) g hleft hright n x =
      f.zass_image_quotmap (p := p) n x := rfl

@[simp] theorem Hom.zassimage_quotequiv_invmonoidhom
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (f.zass_imagequot_equivinv (p := p) g hleft hright n).toMonoidHom =
      f.zass_image_quotmap (p := p) n := rfl

@[simp] theorem Hom.zassimage_quotequivinv_symmapplymap
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (x : P.Group ⧸ zassenhausImage p P n) :
    (f.zass_imagequot_equivinv (p := p) g hleft hright n).symm
        (f.zass_image_quotmap (p := p) n x) = x := by
  exact (f.zass_imagequot_equivinv (p := p) g hleft hright n).left_inv x

@[simp] theorem Hom.zassimage_quotmapapply_equivinvsymm
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (y : Q.Group ⧸ zassenhausImage p Q n) :
    f.zass_image_quotmap (p := p) n
        ((f.zass_imagequot_equivinv (p := p) g hleft hright n).symm y) = y := by
  change f.zass_imagequot_equivinv (p := p) g hleft hright n
      ((f.zass_imagequot_equivinv (p := p) g hleft hright n).symm y) = y
  exact (f.zass_imagequot_equivinv (p := p) g hleft hright n).right_inv y

/-- Equality to the quotient map induced by inverse presentation morphisms, rewritten
through the inverse equivalence. -/
theorem Hom.zassim_mapeq_eqeqa
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (x : P.Group ⧸ zassenhausImage p P n)
    (y : Q.Group ⧸ zassenhausImage p Q n) :
    f.zass_image_quotmap (p := p) n x = y ↔
      x = (f.zass_imagequot_equivinv (p := p) g hleft hright n).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (f.zassimage_quotequivinv_symmapplymap
      (p := p) g hleft hright n x).symm
  · intro h
    rw [h]
    exact f.zassimage_quotmapapply_equivinvsymm
      (p := p) g hleft hright n y


/-- Surjectivity descends to quotients by presented Zassenhaus images. -/
theorem Hom.zass_imagequot_mapsurj (f : Hom P Q) (n : ℕ)
    (hf : Function.Surjective f.toGroupHom) :
    Function.Surjective (f.zass_image_quotmap (p := p) n) := by
  intro y
  refine QuotientGroup.induction_on y ?_
  intro q
  rcases hf q with ⟨x, rfl⟩
  refine ⟨QuotientGroup.mk' (zassenhausImage p P n) x, ?_⟩
  rfl

/-- A right inverse presentation morphism gives surjectivity on presented-image quotients. -/
theorem Hom.zassimage_quotmap_surjrightinv
    (f : Hom P Q) (g : Hom Q P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    Function.Surjective (f.zass_image_quotmap (p := p) n) := by
  apply f.zass_imagequot_mapsurj (p := p) n
  intro y
  refine ⟨g.toGroupHom y, ?_⟩
  have hcomp : f.toGroupHom.comp g.toGroupHom = MonoidHom.id Q.Group := by
    simpa using congrArg Hom.toGroupHom hright
  exact congrArg (fun φ : Q.Group →* Q.Group => φ y) hcomp

/-- Range form for quotient maps with a right inverse. -/
theorem Hom.zassim_mapra_topra
    (f : Hom P Q) (g : Hom Q P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (f.zass_image_quotmap (p := p) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (f.zassimage_quotmap_surjrightinv (p := p) g hright n)

/-- Range form of quotient-map surjectivity for presented Zassenhaus images. -/
theorem Hom.zassimage_quotmap_rangeeqtop (f : Hom P Q) (n : ℕ)
    (hf : Function.Surjective f.toGroupHom) :
    (f.zass_image_quotmap (p := p) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (f.zass_imagequot_mapsurj (p := p) n hf)

/-- If the kernel is contained in the source Zassenhaus image and the source image
maps onto the target image, then the full preimage of the target image is the
source image (only the containment needed for quotient injectivity is stated). -/
theorem Hom.comapzass_imageleker_lemapeq (f : Hom P Q) (n : ℕ)
    (hker : MonoidHom.ker f.toGroupHom ≤ zassenhausImage p P n)
    (hmap : (zassenhausImage p P n).map f.toGroupHom = zassenhausImage p Q n) :
    (zassenhausImage p Q n).comap f.toGroupHom ≤ zassenhausImage p P n := by
  intro x hx
  have hxmap : f.toGroupHom x ∈ (zassenhausImage p P n).map f.toGroupHom := by
    simpa [hmap] using hx
  rcases Subgroup.mem_map.mp hxmap with ⟨a, ha, hfa⟩
  have hk : x * a⁻¹ ∈ MonoidHom.ker f.toGroupHom := by
    change f.toGroupHom (x * a⁻¹) = 1
    rw [map_mul, map_inv, hfa]
    simp
  have hxa : x * a⁻¹ ∈ zassenhausImage p P n := hker hk
  have hprod : (x * a⁻¹) * a ∈ zassenhausImage p P n :=
    (zassenhausImage p P n).mul_mem hxa ha
  simpa [mul_assoc] using hprod

theorem Hom.zassimage_quotmap_injcomaple (f : Hom P Q) (n : ℕ)
    (hpre : (zassenhausImage p Q n).comap f.toGroupHom ≤ zassenhausImage p P n) :
    Function.Injective (f.zass_image_quotmap (p := p) n) := by
  intro a b hab
  revert b
  refine QuotientGroup.induction_on a ?_
  intro x b
  refine QuotientGroup.induction_on b ?_
  intro y hxy
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply hpre
  have hb : f.toGroupHom x / f.toGroupHom y ∈ zassenhausImage p Q n := by
    apply (QuotientGroup.eq_iff_div_mem).mp
    simpa [Hom.zass_imagequot_mapmk] using hxy
  simpa using hb


/-- Surjectivity plus a preimage criterion gives bijectivity on presented-image quotients. -/
theorem Hom.zassimage_quotmapbij_surjcomaple
    (f : Hom P Q) (n : ℕ) (hf : Function.Surjective f.toGroupHom)
    (hpre : (zassenhausImage p Q n).comap f.toGroupHom ≤ zassenhausImage p P n) :
    Function.Bijective (f.zass_image_quotmap (p := p) n) :=
  ⟨f.zassimage_quotmap_injcomaple (p := p) n hpre,
    f.zass_imagequot_mapsurj (p := p) n hf⟩

/-- Right-inverse variant of quotient bijectivity under a preimage criterion. -/
theorem Hom.zassim_mapbi_invco
    (f : Hom P Q) (g : Hom Q P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (hpre : (zassenhausImage p Q n).comap f.toGroupHom ≤ zassenhausImage p P n) :
    Function.Bijective (f.zass_image_quotmap (p := p) n) :=
  ⟨f.zassimage_quotmap_injcomaple (p := p) n hpre,
    f.zassimage_quotmap_surjrightinv (p := p) g hright n⟩

/-- Package a bijective presented-image quotient map as a multiplicative equivalence. -/
noncomputable def Hom.zass_imagequot_equivbij (f : Hom P Q) (n : ℕ)
    (hb : Function.Bijective (f.zass_image_quotmap (p := p) n)) :
    (P.Group ⧸ zassenhausImage p P n) ≃* (Q.Group ⧸ zassenhausImage p Q n) :=
  MulEquiv.ofBijective (f.zass_image_quotmap (p := p) n) hb

@[simp] theorem Hom.zassimage_quotequiv_bijapply (f : Hom P Q)
    (n : ℕ) (hb) (x : P.Group ⧸ zassenhausImage p P n) :
    f.zass_imagequot_equivbij (p := p) n hb x =
      f.zass_image_quotmap (p := p) n x := rfl


@[simp] theorem Hom.zassimage_quotequiv_bijmonoidhom (f : Hom P Q)
    (n : ℕ) (hb : Function.Bijective (f.zass_image_quotmap (p := p) n)) :
    (f.zass_imagequot_equivbij (p := p) n hb).toMonoidHom =
      f.zass_image_quotmap (p := p) n := rfl

@[simp] theorem Hom.zassimage_quotequivbij_symmapplyeq
    (f : Hom P Q) (n : ℕ)
    (hb : Function.Bijective (f.zass_image_quotmap (p := p) n))
    (y : Q.Group ⧸ zassenhausImage p Q n)
    (x : P.Group ⧸ zassenhausImage p P n) :
    (f.zass_imagequot_equivbij (p := p) n hb).symm y = x ↔
      y = f.zass_image_quotmap (p := p) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-! #### Layer maps for presented Zassenhaus images -/

/-- The map induced by a presentation morphism on consecutive presented-image
Zassenhaus layer kernels. -/
noncomputable def Hom.zass_image_layermap (f : Hom P Q) (n : ℕ) :
    DFilt.lKern (zassenhausImageFiltration p P) n →*
      DFilt.lKern (zassenhausImageFiltration p Q) n :=
  DFilt.layerMap (f.preserves_zass_imagefilt (p := p)) n

@[simp] theorem Hom.zass_imagelayer_mapcoe (f : Hom P Q) (n : ℕ)
    (x : DFilt.lKern (zassenhausImageFiltration p P) n) :
    (f.zass_image_layermap (p := p) n x).1 =
      f.zass_image_quotmap (p := p) (n + 1) x.1 := by
  rfl

@[simp] theorem Hom.zass_imagelayer_mapid (P : Presentation.{u}) (n : ℕ) :
    (Hom.id P).zass_image_layermap (p := p) n =
      MonoidHom.id (DFilt.lKern (zassenhausImageFiltration p P) n) := by
  dsimp [Hom.zass_image_layermap]
  simp [DFilt.layerMap_id]

@[simp] theorem Hom.zass_imagelayer_mapcomp (g : Hom Q R) (f : Hom P Q)
    (n : ℕ) :
    (g.comp f).zass_image_layermap (p := p) n =
      (g.zass_image_layermap (p := p) n).comp
        (f.zass_image_layermap (p := p) n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change ((g.comp f).zass_image_layermap (p := p) n x).1 =
    (g.zass_image_layermap (p := p) n
      (f.zass_image_layermap (p := p) n x)).1
  simp only [Hom.zass_imagelayer_mapcoe]
  have h := DFunLike.congr_fun
    (Hom.zass_imagequot_mapcomp (p := p) g f (n + 1)) x.1
  simpa only [MonoidHom.comp_apply] using h


/-- Mutually inverse presentation morphisms induce equivalences on presented-image
Zassenhaus layer kernels. -/
noncomputable def Hom.zass_imagelayer_equivinv (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    DFilt.lKern (zassenhausImageFiltration p P) n ≃*
      DFilt.lKern (zassenhausImageFiltration p Q) n where
  toFun := f.zass_image_layermap (p := p) n
  invFun := g.zass_image_layermap (p := p) n
  left_inv := by
    intro x
    have hcomp := DFunLike.congr_fun
      (Hom.zass_imagelayer_mapcomp (p := p) g f n) x
    rw [hleft] at hcomp
    simpa using hcomp.symm
  right_inv := by
    intro x
    have hcomp := DFunLike.congr_fun
      (Hom.zass_imagelayer_mapcomp (p := p) f g n) x
    rw [hright] at hcomp
    simpa using hcomp.symm
  map_mul' := (f.zass_image_layermap (p := p) n).map_mul

@[simp] theorem Hom.zassimage_layerequiv_invapply (f : Hom P Q)
    (g : Hom Q P) (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q)
    (n : ℕ) (x : DFilt.lKern (zassenhausImageFiltration p P) n) :
    f.zass_imagelayer_equivinv (p := p) g hleft hright n x =
      f.zass_image_layermap (p := p) n x := rfl

@[simp] theorem Hom.zassimage_layerequiv_invmonoidhom
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (f.zass_imagelayer_equivinv (p := p) g hleft hright n).toMonoidHom =
      f.zass_image_layermap (p := p) n := rfl

@[simp] theorem Hom.zassim_layer_symma
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (x : DFilt.lKern (zassenhausImageFiltration p P) n) :
    (f.zass_imagelayer_equivinv (p := p) g hleft hright n).symm
        (f.zass_image_layermap (p := p) n x) = x := by
  exact (f.zass_imagelayer_equivinv (p := p) g hleft hright n).left_inv x

@[simp] theorem Hom.zassim_layer_equiv
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (y : DFilt.lKern (zassenhausImageFiltration p Q) n) :
    f.zass_image_layermap (p := p) n
        ((f.zass_imagelayer_equivinv (p := p) g hleft hright n).symm y) = y := by
  change f.zass_imagelayer_equivinv (p := p) g hleft hright n
      ((f.zass_imagelayer_equivinv (p := p) g hleft hright n).symm y) = y
  exact (f.zass_imagelayer_equivinv (p := p) g hleft hright n).right_inv y

/-- Equality to the layer map induced by inverse presentation morphisms, rewritten through
 the inverse equivalence. -/
theorem Hom.zassim_mapeq_eqequ
    (f : Hom P Q) (g : Hom Q P)
    (hleft : g.comp f = Hom.id P) (hright : f.comp g = Hom.id Q) (n : ℕ)
    (x : DFilt.lKern (zassenhausImageFiltration p P) n)
    (y : DFilt.lKern (zassenhausImageFiltration p Q) n) :
    f.zass_image_layermap (p := p) n x = y ↔
      x = (f.zass_imagelayer_equivinv (p := p) g hleft hright n).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (f.zassim_layer_symma
      (p := p) g hleft hright n x).symm
  · intro h
    rw [h]
    exact f.zassim_layer_equiv
      (p := p) g hleft hright n y

/-- A preimage criterion for injectivity on presented-image layer kernels. -/
theorem Hom.zassimage_layermap_injcomaple (f : Hom P Q) {n : ℕ}
    (hpre : (zassenhausImage p Q (n + 1)).comap f.toGroupHom ≤
      zassenhausImage p P (n + 1)) :
    Function.Injective (f.zass_image_layermap (p := p) n) := by
  dsimp [Hom.zass_image_layermap]
  exact DFilt.layer_injective_comap
    (f.preserves_zass_imagefilt (p := p)) hpre


/-- Termwise onto morphisms are surjective on presented-image layer kernels. -/
theorem Hom.zassimage_layermap_surjmapsonto (f : Hom P Q)
    (honto : DFilt.MapsOnto (zassenhausImageFiltration p P)
      (zassenhausImageFiltration p Q) f.toGroupHom) (n : ℕ) :
    Function.Surjective (f.zass_image_layermap (p := p) n) := by
  dsimp [Hom.zass_image_layermap]
  simpa using DFilt.layer_surjective_onto honto n

/-- A right inverse presentation morphism gives surjectivity on presented-image layers. -/
theorem Hom.zassimage_layermap_surjrightinv
    (f : Hom P Q) (g : Hom Q P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    Function.Surjective (f.zass_image_layermap (p := p) n) :=
  f.zassimage_layermap_surjmapsonto (p := p)
    (f.mapsonto_zassimage_filtrightinv (p := p) g hright) n

/-- Range form for layer maps with a right inverse. -/
theorem Hom.zassim_mapra_topri
    (f : Hom P Q) (g : Hom Q P) (hright : f.comp g = Hom.id Q) (n : ℕ) :
    (f.zass_image_layermap (p := p) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (f.zassimage_layermap_surjrightinv (p := p) g hright n)

/-- Range form of layer-map surjectivity for presented Zassenhaus images. -/
theorem Hom.zassim_mapra_topma (f : Hom P Q)
    (honto : DFilt.MapsOnto (zassenhausImageFiltration p P)
      (zassenhausImageFiltration p Q) f.toGroupHom) (n : ℕ) :
    (f.zass_image_layermap (p := p) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (f.zassimage_layermap_surjmapsonto (p := p) honto n)

/-- Termwise onto plus a next-term preimage criterion gives bijectivity on layers. -/
theorem Hom.zassim_mapbi_ontoc (f : Hom P Q)
    (honto : DFilt.MapsOnto (zassenhausImageFiltration p P)
      (zassenhausImageFiltration p Q) f.toGroupHom) {n : ℕ}
    (hpre : (zassenhausImage p Q (n + 1)).comap f.toGroupHom ≤
      zassenhausImage p P (n + 1)) :
    Function.Bijective (f.zass_image_layermap (p := p) n) := by
  dsimp [Hom.zass_image_layermap]
  exact DFilt.bijective_maps_comap honto hpre


/-- Package a bijective presented-image layer map as a multiplicative equivalence. -/
noncomputable def Hom.zass_imagelayer_equivbij (f : Hom P Q) (n : ℕ)
    (hb : Function.Bijective (f.zass_image_layermap (p := p) n)) :
    DFilt.lKern (zassenhausImageFiltration p P) n ≃*
      DFilt.lKern (zassenhausImageFiltration p Q) n :=
  MulEquiv.ofBijective (f.zass_image_layermap (p := p) n) hb

@[simp] theorem Hom.zassimage_layerequiv_bijapply (f : Hom P Q)
    (n : ℕ) (hb)
    (x : DFilt.lKern (zassenhausImageFiltration p P) n) :
    f.zass_imagelayer_equivbij (p := p) n hb x =
      f.zass_image_layermap (p := p) n x := rfl


@[simp] theorem Hom.zassimage_layerequiv_bijmonoidhom (f : Hom P Q)
    (n : ℕ) (hb : Function.Bijective (f.zass_image_layermap (p := p) n)) :
    (f.zass_imagelayer_equivbij (p := p) n hb).toMonoidHom =
      f.zass_image_layermap (p := p) n := rfl

@[simp] theorem Hom.zassimage_layerequivbij_symmapplyeq
    (f : Hom P Q) (n : ℕ)
    (hb : Function.Bijective (f.zass_image_layermap (p := p) n))
    (y : DFilt.lKern (zassenhausImageFiltration p Q) n)
    (x : DFilt.lKern (zassenhausImageFiltration p P) n) :
    (f.zass_imagelayer_equivbij (p := p) n hb).symm y = x ↔
      y = f.zass_image_layermap (p := p) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

variable (P : Presentation.{u})

/-- The subtype of relators of a presentation. -/
abbrev Relator := { r : P.Free // r ∈ P.rels }

instance : Coe (Relator P) P.Free := ⟨Subtype.val⟩

/-- A Zassenhaus depth assignment for the relators of `P`.
`depth r = q` is interpreted as a certified lower bound: the relator lies in `D_q`.
Exactness of the depth is deliberately not part of this structure. -/
structure RDepths where
  depth : Relator P → ℕ
  mem_depth : ∀ r : Relator P,
    GroupAlgebra.zassenhausDepthLeast p P.Free (r : P.Free) (depth r)

namespace RDepths

variable {p P}

/-- Every presentation has the trivial depth assignment `1`, since `D₁ = ⊤`. -/
def trivial : RDepths p P where
  depth := fun _ => 1
  mem_depth := by
    intro r
    simp [GroupAlgebra.zassenhausDepthLeast]

/-- The relator certificate can be weakened to any smaller requested depth. -/
theorem mem_of_le (D : RDepths p P) (r : Relator P) {m : ℕ}
    (hm : m ≤ D.depth r) :
    GroupAlgebra.zassenhausDepthLeast p P.Free (r : P.Free) m := by
  exact GroupAlgebra.depth_least p P.Free hm (D.mem_depth r)

/-- Certified relator depth is stable under inversion. -/
theorem mem_inv (D : RDepths p P) (r : Relator P) :
    GroupAlgebra.zassenhausDepthLeast p P.Free ((r : P.Free)⁻¹) (D.depth r) :=
  GroupAlgebra.depth_least_inv p P.Free (D.mem_depth r)

/-- Certified relator depth is stable under conjugation in the free group. -/
theorem mem_conj (D : RDepths p P) (r : Relator P) (x : P.Free) :
    GroupAlgebra.zassenhausDepthLeast p P.Free (x * (r : P.Free) * x⁻¹) (D.depth r) :=
  GroupAlgebra.zassenhaus_least_conj p P.Free (D.mem_depth r)

/-- Products of two certified relators have any common lower depth bound. -/
theorem mul_common (D : RDepths p P) (r s : Relator P) {m : ℕ}
    (hr : m ≤ D.depth r) (hs : m ≤ D.depth s) :
    GroupAlgebra.zassenhausDepthLeast p P.Free ((r : P.Free) * (s : P.Free)) m := by
  change (r : P.Free) * (s : P.Free) ∈ GroupAlgebra.zSubgro p P.Free m
  exact (GroupAlgebra.zSubgro p P.Free m).mul_mem
    (D.mem_of_le r hr) (D.mem_of_le s hs)

/-- Products of conjugates of two certified relators have any common lower depth bound. -/
theorem conj_mul_common (D : RDepths p P) (r s : Relator P)
    (x y : P.Free) {m : ℕ} (hr : m ≤ D.depth r) (hs : m ≤ D.depth s) :
    GroupAlgebra.zassenhausDepthLeast p P.Free
      ((x * (r : P.Free) * x⁻¹) * (y * (s : P.Free) * y⁻¹)) m := by
  change _ ∈ GroupAlgebra.zSubgro p P.Free m
  exact (GroupAlgebra.zSubgro p P.Free m).mul_mem
    (GroupAlgebra.depth_least p P.Free hr (D.mem_conj r x))
    (GroupAlgebra.depth_least p P.Free hs (D.mem_conj s y))


/-- A product of a list of elements all lying in a fixed Zassenhaus term also lies in that term. -/
theorem list_prod_forall {n : ℕ} (L : List P.Free)
    (hL : ∀ x ∈ L, GroupAlgebra.zassenhausDepthLeast p P.Free x n) :
    GroupAlgebra.zassenhausDepthLeast p P.Free L.prod n := by
  change L.prod ∈ GroupAlgebra.zSubgro p P.Free n
  induction L with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.prod_cons]
      exact (GroupAlgebra.zSubgro p P.Free n).mul_mem
        (hL x (by simp))
        (ih (by
          intro y hy
          exact hL y (by simp [hy])))

/-- The product word formed from a list of conjugated relators. -/
def conjugateRelatorProduct (L : List (P.Free × Relator P)) : P.Free :=
  (L.map (fun xr => xr.1 * (xr.2 : P.Free) * xr.1⁻¹)).prod

@[simp] theorem conjugate_relator_nil :
    conjugateRelatorProduct (P := P) [] = (1 : P.Free) := by
  simp [conjugateRelatorProduct]

@[simp] theorem conjugate_relator_cons (x : P.Free × Relator P)
    (xs : List (P.Free × Relator P)) :
    conjugateRelatorProduct (P := P) (x :: xs) =
      (x.1 * (x.2 : P.Free) * x.1⁻¹) * conjugateRelatorProduct (P := P) xs := by
  simp [conjugateRelatorProduct]

@[simp] theorem conjugate_relator_append (xs ys : List (P.Free × Relator P)) :
    conjugateRelatorProduct (P := P) (xs ++ ys) =
      conjugateRelatorProduct (P := P) xs * conjugateRelatorProduct (P := P) ys := by
  simp [conjugateRelatorProduct, List.map_append, List.prod_append]

/-- A product of conjugated relators has any common certified lower depth bound. -/
theorem conjugate_relator_forall (D : RDepths p P)
    {n : ℕ} (L : List (P.Free × Relator P))
    (hL : ∀ xr ∈ L, n ≤ D.depth xr.2) :
    GroupAlgebra.zassenhausDepthLeast p P.Free (conjugateRelatorProduct (P := P) L) n := by
  unfold conjugateRelatorProduct
  apply list_prod_forall (p := p) (P := P)
  intro x hx
  rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
  exact GroupAlgebra.depth_least p P.Free (hL xr hxr)
    (D.mem_conj xr.2 xr.1)

/-- A signed conjugated relator datum: a conjugator, a relator, and whether to invert it. -/
structure SCRelato where
  conjugator : P.Free
  relator : Relator P
  inverse : Bool

/-- The group word represented by a signed conjugated relator datum. -/
def SCRelato.word (x : SCRelato (P := P)) : P.Free :=
  x.conjugator *
    (if x.inverse then (x.relator : P.Free)⁻¹ else (x.relator : P.Free)) *
    x.conjugator⁻¹

/-- Product word formed from signed conjugated relators. -/
def signedConjugateProduct (L : List (SCRelato (P := P))) : P.Free :=
  (L.map SCRelato.word).prod

@[simp] theorem SCRelato.word_mk_false (c : P.Free) (r : Relator P) :
    SCRelato.word (P := P) ⟨c, r, false⟩ = c * (r : P.Free) * c⁻¹ := by
  simp [SCRelato.word]

@[simp] theorem SCRelato.word_mk_true (c : P.Free) (r : Relator P) :
    SCRelato.word (P := P) ⟨c, r, true⟩ = c * (r : P.Free)⁻¹ * c⁻¹ := by
  simp [SCRelato.word]

@[simp] theorem signed_conjugate_nil :
    signedConjugateProduct (P := P) [] = (1 : P.Free) := by
  simp [signedConjugateProduct]

@[simp] theorem signed_conjugate_cons (x : SCRelato (P := P))
    (xs : List (SCRelato (P := P))) :
    signedConjugateProduct (P := P) (x :: xs) =
      x.word * signedConjugateProduct (P := P) xs := by
  simp [signedConjugateProduct]

@[simp] theorem signed_conjugate_append
    (xs ys : List (SCRelato (P := P))) :
    signedConjugateProduct (P := P) (xs ++ ys) =
      signedConjugateProduct (P := P) xs *
        signedConjugateProduct (P := P) ys := by
  simp [signedConjugateProduct, List.map_append, List.prod_append]

/-- A signed conjugated relator has the same certified depth as its relator. -/
theorem signed_conj_relator (D : RDepths p P)
    (x : SCRelato (P := P)) :
    GroupAlgebra.zassenhausDepthLeast p P.Free x.word (D.depth x.relator) := by
  unfold SCRelato.word
  by_cases hx : x.inverse
  · rw [if_pos hx]
    exact GroupAlgebra.zassenhaus_least_conj p P.Free (D.mem_inv x.relator)
  · rw [if_neg hx]
    exact D.mem_conj x.relator x.conjugator

/-- Products of signed conjugated relators have any common certified lower depth bound. -/
theorem signed_conjugate_forall (D : RDepths p P)
    {n : ℕ} (L : List (SCRelato (P := P)))
    (hL : ∀ x ∈ L, n ≤ D.depth x.relator) :
    GroupAlgebra.zassenhausDepthLeast p P.Free (signedConjugateProduct (P := P) L) n := by
  unfold signedConjugateProduct
  apply list_prod_forall (p := p) (P := P)
  intro w hw
  rcases List.mem_map.mp hw with ⟨x, hxL, rfl⟩
  exact GroupAlgebra.depth_least p P.Free (hL x hxL)
    (D.signed_conj_relator x)

/-- Predicate saying all relators have no degree-one part (depth at least two). -/
def degreeOneSilent (D : RDepths p P) : Prop :=
  ∀ r : Relator P, 2 ≤ D.depth r

/-- Degree-one silent relators give depth-two signed conjugate products. -/
theorem signed_conjugate_silent
    (D : RDepths p P) (hD : D.degreeOneSilent)
    (L : List (SCRelato (P := P))) :
    GroupAlgebra.zassenhausDepthLeast p P.Free
      (signedConjugateProduct (P := P) L) 2 :=
  D.signed_conjugate_forall L (fun x _ => hD x.relator)

/-- Relators whose certified lower-bound depth is active by degree `n`. -/
def activeAt (D : RDepths p P) (n : ℕ) : Set (Relator P) :=
  { r | D.depth r ≤ n }

@[simp] theorem mem_activeAt (D : RDepths p P) (r : Relator P) (n : ℕ) :
    r ∈ D.activeAt n ↔ D.depth r ≤ n := Iff.rfl

/-- The active-relator sets are monotone in the cutoff degree. -/
theorem activeAt_mono (D : RDepths p P) {m n : ℕ} (hmn : m ≤ n) :
    D.activeAt m ⊆ D.activeAt n := by
  intro r hr
  exact le_trans hr hmn

@[simp] theorem activeAt_zero (D : RDepths p P) :
    D.activeAt 0 = {r | D.depth r = 0} := by
  ext r
  simp [Presentation.RDepths.activeAt]


/-- Relators with certified depth exactly `n`.  These are the graded slices of the
active-relator filtration. -/
def exactAt (D : RDepths p P) (n : ℕ) : Set (Relator P) :=
  { r | D.depth r = n }

@[simp] theorem mem_exactAt (D : RDepths p P) (r : Relator P) (n : ℕ) :
    r ∈ D.exactAt n ↔ D.depth r = n := Iff.rfl

/-- Exact-depth relators are active at their depth. -/
theorem exact_active (D : RDepths p P) (n : ℕ) :
    D.exactAt n ⊆ D.activeAt n := by
  intro r hr
  exact le_of_eq hr

/-- Passing from cutoff `n` to `n+1` adds precisely the exact-depth `n+1` relators. -/
theorem succ_union_exact (D : RDepths p P) (n : ℕ) :
    D.activeAt (n + 1) = D.activeAt n ∪ D.exactAt (n + 1) := by
  ext r
  constructor
  · intro hr
    change D.depth r ≤ n + 1 at hr
    have hle_or : D.depth r ≤ n ∨ D.depth r = n + 1 := by omega
    rcases hle_or with hle | heq
    · exact Or.inl hle
    · exact Or.inr heq
  · intro hr
    rcases hr with hle | heq
    · exact Nat.le_trans hle (Nat.le_succ n)
    · exact le_of_eq heq

/-- The old active relators and the newly exact-depth relators are disjoint. -/
theorem disjoint_active_exact (D : RDepths p P) (n : ℕ) :
    Disjoint (D.activeAt n) (D.exactAt (n + 1)) := by
  rw [Set.disjoint_left]
  intro r hle heq
  change D.depth r ≤ n at hle
  change D.depth r = n + 1 at heq
  omega


/-- Exact-depth slices at distinct degrees are disjoint. -/
theorem disjoint_ne (D : RDepths p P) {m n : ℕ} (h : m ≠ n) :
    Disjoint (D.exactAt m) (D.exactAt n) := by
  rw [Set.disjoint_left]
  intro r hm hn
  change D.depth r = m at hm
  change D.depth r = n at hn
  exact h (hm.symm.trans hn)

/-- The active set up to `n` is the union of exact-depth slices of degree at most `n`. -/
theorem active_i_exact (D : RDepths p P) (n : ℕ) :
    D.activeAt n = ⋃ i : {i : ℕ // i ≤ n}, D.exactAt i.1 := by
  ext r
  constructor
  · intro hr
    change D.depth r ≤ n at hr
    refine Set.mem_iUnion.mpr ⟨⟨D.depth r, hr⟩, ?_⟩
    exact rfl
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
    change D.depth r = i.1 at hi
    change D.depth r ≤ n
    exact hi.le.trans i.2


/-- Splitting active relators at cutoff `n+1` into old active relators and the new
exact-depth slice. -/
noncomputable def activeSuccSum (D : RDepths p P) (n : ℕ) :
    {r : Relator P // r ∈ D.activeAt (n + 1)} ≃
      ({r : Relator P // r ∈ D.activeAt n} ⊕
        {r : Relator P // r ∈ D.exactAt (n + 1)}) where
  toFun r := by
    classical
    by_cases h : r.1 ∈ D.activeAt n
    · exact Sum.inl ⟨r.1, h⟩
    · refine Sum.inr ⟨r.1, ?_⟩
      have hs : D.depth r.1 ≤ n + 1 := r.2
      change D.depth r.1 = n + 1
      have hn : ¬ D.depth r.1 ≤ n := h
      omega
  invFun s := by
    rcases s with a | b
    · exact ⟨a.1, Nat.le_trans a.2 (Nat.le_succ n)⟩
    · exact ⟨b.1, le_of_eq b.2⟩
  left_inv := by
    intro r
    cases r with
    | mk rv rh =>
      simp only
      by_cases h : rv ∈ D.activeAt n
      · simp [h]
      · simp [h]
  right_inv := by
    intro s
    rcases s with a | b
    · cases a with
      | mk av ah =>
        simp [ah]
    · cases b with
      | mk bv bh =>
        have hnot : ¬ bv ∈ D.activeAt n := by
          intro hle
          change D.depth bv ≤ n at hle
          change D.depth bv = n + 1 at bh
          omega
        simp [hnot]

/-- Active relators up to `n` are equivalently a sigma-type of exact-depth
relators indexed by degrees `≤ n`. -/
noncomputable def activeSigmaExact (D : RDepths p P) (n : ℕ) :
    {r : Relator P // r ∈ D.activeAt n} ≃
      (Σ i : {i : ℕ // i ≤ n}, {r : Relator P // r ∈ D.exactAt i.1}) where
  toFun r :=
    ⟨⟨D.depth r.1, r.2⟩, ⟨r.1, rfl⟩⟩
  invFun s :=
    ⟨s.2.1, by
      change D.depth s.2.1 ≤ n
      exact le_trans (le_of_eq s.2.2) s.1.2⟩
  left_inv := by
    intro r
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    cases s with
    | mk i r =>
      cases i with
      | mk i hi =>
        cases r with
        | mk rv hr =>
          change D.depth rv = i at hr
          cases hr
          rfl

/-- Active relators up to `n`, indexed by a `Fin (n+1)` exact depth. -/
noncomputable def sigmaExactFin (D : RDepths p P) (n : ℕ) :
    {r : Relator P // r ∈ D.activeAt n} ≃
      (Σ i : Fin (n + 1), {r : Relator P // r ∈ D.exactAt i.1}) where
  toFun r :=
    ⟨⟨D.depth r.1, Nat.lt_succ_of_le r.2⟩, ⟨r.1, rfl⟩⟩
  invFun s :=
    ⟨s.2.1, by
      change D.depth s.2.1 ≤ n
      have hi : s.1.1 ≤ n := Nat.le_of_lt_succ s.1.2
      exact le_trans (le_of_eq s.2.2) hi⟩
  left_inv := by
    intro r
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    cases s with
    | mk i r =>
      cases i with
      | mk i hi =>
        cases r with
        | mk rv hr =>
          change D.depth rv = i at hr
          cases hr
          rfl

/-- Cardinal form of the decomposition of active relators into exact-depth slices. -/
theorem nat_exact_fin [Finite (Relator P)]
    (D : RDepths p P) (n : ℕ) :
    Nat.card {r : Relator P // r ∈ D.activeAt n} =
      ∑ i : Fin (n + 1), Nat.card {r : Relator P // r ∈ D.exactAt i.1} := by
  classical
  calc
    Nat.card {r : Relator P // r ∈ D.activeAt n} =
        Nat.card (Σ i : Fin (n + 1), {r : Relator P // r ∈ D.exactAt i.1}) :=
      Nat.card_congr (D.sigmaExactFin n)
    _ = _ := Nat.card_sigma

/-- Cardinal recurrence for active relators, split by the newly appearing exact-depth slice. -/
theorem nat_active_succ [Finite (Relator P)] (D : RDepths p P) (n : ℕ) :
    Nat.card {r : Relator P // r ∈ D.activeAt (n + 1)} =
      Nat.card {r : Relator P // r ∈ D.activeAt n} +
        Nat.card {r : Relator P // r ∈ D.exactAt (n + 1)} := by
  classical
  calc
    Nat.card {r : Relator P // r ∈ D.activeAt (n + 1)} =
        Nat.card (({r : Relator P // r ∈ D.activeAt n}) ⊕
          {r : Relator P // r ∈ D.exactAt (n + 1)}) :=
      Nat.card_congr (D.activeSuccSum n)
    _ = _ := Nat.card_sum


/-- If no relator is active by `n-1`, then every relator has depth at least `n`. -/
theorem forall_pred_empty (D : RDepths p P)
    {n : ℕ} (hn : 0 < n) (h : D.activeAt (n - 1) = ∅) :
    ∀ r : Relator P, n ≤ D.depth r := by
  intro r
  by_contra hr
  have hrle : D.depth r ≤ n - 1 := by omega
  have : r ∈ D.activeAt (n - 1) := hrle
  rw [h] at this
  exact this.elim



/-- If every relator has certified depth at least `n`, then the normal closure of the
relators is contained in the `n`th Zassenhaus term of the free group. -/
theorem normal_closure_forall {n : ℕ} (D : RDepths p P)
    (hD : ∀ r : Relator P, n ≤ D.depth r) :
    P.rNClos ≤ GroupAlgebra.zSubgro p P.Free n := by
  classical
  haveI : (GroupAlgebra.zSubgro p P.Free n).Normal :=
    GroupAlgebra.zassenhausSubgroup_normal p P.Free n
  apply Subgroup.normalClosure_le_normal
  intro x hx
  let r : Relator P := ⟨x, hx⟩
  exact D.mem_of_le r (hD r)

/-- Empty activity below `n` gives the usual normal-closure containment in `D_n`. -/
theorem active_pred_empty (D : RDepths p P)
    {n : ℕ} (hn : 0 < n) (h : D.activeAt (n - 1) = ∅) :
    P.rNClos ≤ GroupAlgebra.zSubgro p P.Free n :=
  D.normal_closure_forall
    (D.forall_pred_empty hn h)


/-- If relators have depth at least `n`, the presented group maps canonically to the
free group's `n`th Zassenhaus quotient.  This is the quotient map induced by
`F → F / D_n` because the relator normal closure lies in `D_n`. -/
noncomputable def quotientZassenhaus {n : ℕ} (D : RDepths p P)
    (hD : ∀ r : Relator P, n ≤ D.depth r) :
    P.Group →* P.Free ⧸ GroupAlgebra.zSubgro p P.Free n := by
  classical
  let N := GroupAlgebra.zSubgro p P.Free n
  refine QuotientGroup.lift P.rNClos (QuotientGroup.mk' N) ?_
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mpr
    ((D.normal_closure_forall hD) hx)


@[simp] theorem quotient_zassenhaus {n : ℕ}
    (D : RDepths p P) (hD : ∀ r : Relator P, n ≤ D.depth r) (x : P.Free) :
    D.quotientZassenhaus hD (P.quotientMap x) =
      QuotientGroup.mk' (GroupAlgebra.zSubgro p P.Free n) x := by
  dsimp [quotientZassenhaus, Presentation.quotientMap]
  change (QuotientGroup.lift P.rNClos
      (QuotientGroup.mk' (GroupAlgebra.zSubgro p P.Free n)) _)
      (QuotientGroup.mk x) = _
  rw [QuotientGroup.lift_mk']
  rfl

/-- The maps from a presentation to free Zassenhaus quotients commute with truncation
whenever the stronger depth bound is available. -/
theorem quotient_zassenhaus_transition {m n : ℕ}
    (D : RDepths p P) (hmn : m ≤ n)
    (hDn : ∀ r : Relator P, n ≤ D.depth r) :
    (GroupAlgebra.zassenhaus p P.Free hmn).comp
        (D.quotientZassenhaus hDn) =
      D.quotientZassenhaus (fun r => le_trans hmn (hDn r)) := by
  apply MonoidHom.ext
  intro q
  rcases P.quotientMap_surjective q with ⟨x, rfl⟩
  change GroupAlgebra.zassenhaus p P.Free hmn
      (D.quotientZassenhaus hDn (P.quotientMap x)) =
    D.quotientZassenhaus (fun r => le_trans hmn (hDn r)) (P.quotientMap x)
  rw [quotient_zassenhaus,
    quotient_zassenhaus]
  exact GroupAlgebra.zassenhaus_quotient_mk p P.Free hmn x

/-- Naturality of the canonical map from a presented group to a free Zassenhaus
quotient with respect to a morphism of presentations.  Both presentations only
need the same uniform lower depth bound on their relators. -/
theorem quotient_zassenhaus_naturality {Q : Presentation.{u}} {n : ℕ}
    (D₁ : RDepths p P) (D₂ : RDepths p Q)
    (f : Presentation.Hom P Q)
    (h₁ : ∀ r : Relator P, n ≤ D₁.depth r)
    (h₂ : ∀ r : Relator Q, n ≤ D₂.depth r) :
    (GroupAlgebra.zQuot.map p P.Free f.freeMap n).comp
        (D₁.quotientZassenhaus h₁) =
      (D₂.quotientZassenhaus h₂).comp f.toGroupHom := by
  apply MonoidHom.ext
  intro q
  rcases P.quotientMap_surjective q with ⟨x, rfl⟩
  change GroupAlgebra.zQuot.map p P.Free f.freeMap n
      (D₁.quotientZassenhaus h₁ (P.quotientMap x)) =
    D₂.quotientZassenhaus h₂
      (f.toGroupHom (P.quotientMap x))
  rw [quotient_zassenhaus,
    Presentation.Hom.group_quotient,
    quotient_zassenhaus]
  exact GroupAlgebra.zQuot.map_mk p P.Free f.freeMap n x


/-- The canonical map to the free Zassenhaus quotient is surjective. -/
theorem quotient_zassenhaus_surjective {n : ℕ}
    (D : RDepths p P) (hD : ∀ r : Relator P, n ≤ D.depth r) :
    Function.Surjective (D.quotientZassenhaus hD) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  refine ⟨P.quotientMap x, ?_⟩
  simp [quotient_zassenhaus]

/-- The kernel of the canonical map from a presented group to the free Zassenhaus
quotient is exactly the presented image of the free Zassenhaus term. -/
theorem ker_quotient_zassenhaus {n : ℕ}
    (D : RDepths p P) (hD : ∀ r : Relator P, n ≤ D.depth r) :
    MonoidHom.ker (D.quotientZassenhaus hD) = zassenhausImage p P n := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    rcases P.quotientMap_surjective x with ⟨w, rfl⟩
    have hmk : QuotientGroup.mk' (GroupAlgebra.zSubgro p P.Free n) w = 1 := by
      simpa [quotient_zassenhaus] using hx
    exact zassenhaus_image p P ((QuotientGroup.eq_one_iff w).mp hmk)
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨w, hw, rfl⟩
    change D.quotientZassenhaus hD (P.quotientMap w) = 1
    rw [quotient_zassenhaus]
    exact (QuotientGroup.eq_one_iff w).mpr hw

/-- The quotient of the presented group by the presented Zassenhaus image is
canonically equivalent to the ambient free Zassenhaus quotient, provided all
relators have depth at least `n`. -/
noncomputable def zassenhausImageFree {n : ℕ}
    (D : RDepths p P) (hD : ∀ r : Relator P, n ≤ D.depth r) :
    (P.Group ⧸ zassenhausImage p P n) ≃*
      (P.Free ⧸ GroupAlgebra.zSubgro p P.Free n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (D.ker_quotient_zassenhaus hD).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (D.quotientZassenhaus hD)
      (D.quotient_zassenhaus_surjective hD))

@[simp] theorem image_free_mk {n : ℕ}
    (D : RDepths p P) (hD : ∀ r : Relator P, n ≤ D.depth r)
    (x : P.Group) :
    D.zassenhausImageFree hD
        (QuotientGroup.mk' (zassenhausImage p P n) x) =
      D.quotientZassenhaus hD x := by
  rcases P.quotientMap_surjective x with ⟨w, rfl⟩
  dsimp [zassenhausImageFree, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]

/-- Kernel form of `normal_closure_forall`. -/
theorem quotient_ker_forall {n : ℕ} (D : RDepths p P)
    (hD : ∀ r : Relator P, n ≤ D.depth r) :
    MonoidHom.ker P.quotientMap ≤ GroupAlgebra.zSubgro p P.Free n := by
  intro x hx
  have hxrel : x ∈ P.rNClos := by
    exact P.quotient_one.mp (MonoidHom.mem_ker.mp hx)
  exact D.normal_closure_forall hD hxrel

/-- Uniform depth-two version for degree-one silent relator collections. -/
theorem normal_closure_silent (D : RDepths p P)
    (hD : D.degreeOneSilent) :
    P.rNClos ≤ GroupAlgebra.zSubgro p P.Free 2 :=
  D.normal_closure_forall hD

/-- If all relators are degree-one silent, each relator lies in `D₂`. -/
theorem two_degree_silent (D : RDepths p P)
    (hD : D.degreeOneSilent) (r : Relator P) :
    GroupAlgebra.zassenhausDepthLeast p P.Free (r : P.Free) 2 :=
  D.mem_of_le r (hD r)

end RDepths

end Presentation

/-- A presentation bundled with certified Zassenhaus lower bounds for its relators. -/
structure FPres (p : ℕ) where
  toPresentation : Presentation.{u}
  depths : toPresentation.RDepths p

namespace FPres

variable {p : ℕ} (FP : FPres.{u} p)

abbrev Gen : Type u := FP.toPresentation.Gen
abbrev Free : Type u := FP.toPresentation.Free
abbrev Group : Type u := FP.toPresentation.Group

/-- A morphism of filtered presentations is currently just a morphism of the
underlying presentations.  Depth hypotheses are supplied explicitly to the
Zassenhaus quotient lemmas below, which keeps this lightweight wrapper flexible. -/
abbrev Hom (FP FQ : FPres.{u} p) : Type u :=
  Presentation.Hom FP.toPresentation FQ.toPresentation

/-- The certified depth of a relator in a filtered presentation. -/
def relatorDepth (r : FP.toPresentation.Relator) : ℕ := FP.depths.depth r

@[simp] theorem relatorDepth_apply (r : FP.toPresentation.Relator) :
    FP.relatorDepth r = FP.depths.depth r := rfl

/-- Membership certificate at the bundled relator depth. -/
theorem relator_mem_depth (r : FP.toPresentation.Relator) :
    GroupAlgebra.zassenhausDepthLeast p FP.Free (r : FP.Free) (FP.relatorDepth r) := by
  simpa [relatorDepth] using FP.depths.mem_depth r

/-- A relator also lies in any smaller requested Zassenhaus depth. -/
theorem relator_of_le (r : FP.toPresentation.Relator) {n : ℕ}
    (hn : n ≤ FP.relatorDepth r) :
    GroupAlgebra.zassenhausDepthLeast p FP.Free (r : FP.Free) n := by
  exact FP.depths.mem_of_le r (by simpa [relatorDepth] using hn)

/-- Filtered-presentation-level spelling of degree-one silent relators. -/
def degreeOneSilent : Prop := FP.depths.degreeOneSilent

@[simp] theorem degree_one_silent :
    FP.degreeOneSilent ↔ ∀ r : FP.toPresentation.Relator, 2 ≤ FP.relatorDepth r := by
  rfl

/-- In a degree-one silent filtered presentation, every relator has certified depth at least two. -/
theorem two_relator_silent (h : FP.degreeOneSilent)
    (r : FP.toPresentation.Relator) : 2 ≤ FP.relatorDepth r := by
  exact h r

/-- Degree-one silence gives direct membership in the second Zassenhaus term. -/
theorem relator_degree_silent (h : FP.degreeOneSilent)
    (r : FP.toPresentation.Relator) :
    GroupAlgebra.zassenhausDepthLeast p FP.Free (r : FP.Free) 2 :=
  FP.relator_of_le r (FP.two_relator_silent h r)

/-- Canonical map from a filtered presentation to the free Zassenhaus quotient, under
a uniform relator-depth lower bound. -/
noncomputable def quotientZassenhaus {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    FP.Group →* FP.Free ⧸ GroupAlgebra.zSubgro p FP.Free n :=
  FP.depths.quotientZassenhaus hD

@[simp] theorem quotient_zassenhaus {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) (x : FP.Free) :
    FP.quotientZassenhaus hD (FP.toPresentation.quotientMap x) =
      QuotientGroup.mk' (GroupAlgebra.zSubgro p FP.Free n) x :=
  Presentation.RDepths.quotient_zassenhaus FP.depths hD x

/-- Kernel of the filtered-presentation map to a free Zassenhaus quotient. -/
theorem ker_quotient_zassenhaus {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    MonoidHom.ker (FP.quotientZassenhaus hD) =
      Presentation.zassenhausImage p FP.toPresentation n :=
  FP.depths.ker_quotient_zassenhaus hD

/-- Equivalence between quotienting the presented group by the presented image of
`D_n` and the free Zassenhaus quotient, under a uniform relator-depth bound. -/
noncomputable def zassenhausImageFree {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation n) ≃*
      (FP.Free ⧸ GroupAlgebra.zSubgro p FP.Free n) :=
  FP.depths.zassenhausImageFree hD

@[simp] theorem image_free_mk {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) (x : FP.Group) :
    FP.zassenhausImageFree hD
        (QuotientGroup.mk' (Presentation.zassenhausImage p FP.toPresentation n) x) =
      FP.quotientZassenhaus hD x :=
  FP.depths.image_free_mk hD x

/-- Filtered-presentation quotient maps commute with Zassenhaus truncation maps. -/
theorem quotient_zassenhaus_transition {m n : ℕ} (hmn : m ≤ n)
    (hDn : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    (GroupAlgebra.zassenhaus p FP.Free hmn).comp
        (FP.quotientZassenhaus hDn) =
      FP.quotientZassenhaus (fun r => le_trans hmn (hDn r)) :=
  Presentation.RDepths.quotient_zassenhaus_transition FP.depths hmn hDn

/-- Naturality of filtered-presentation maps to free Zassenhaus quotients. -/
theorem quotient_zassenhaus_naturality
    {FQ : FPres.{u} p} {n : ℕ} (f : Hom FP FQ)
    (hP : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r)
    (hQ : ∀ r : FQ.toPresentation.Relator, n ≤ FQ.depths.depth r) :
    (GroupAlgebra.zQuot.map p FP.Free f.freeMap n).comp
        (FP.quotientZassenhaus hP) =
      (FQ.quotientZassenhaus hQ).comp f.toGroupHom :=
  Presentation.RDepths.quotient_zassenhaus_naturality
    FP.depths FQ.depths f hP hQ


/-- The filtered-presentation map to the free Zassenhaus quotient is surjective. -/
theorem quotient_zassenhaus_surjective {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    Function.Surjective (FP.quotientZassenhaus hD) :=
  FP.depths.quotient_zassenhaus_surjective hD

/-- A filtered presentation whose relators all have depth at least `n` has quotient
kernel contained in the `n`th Zassenhaus term of the free group. -/
theorem quotient_ker_forall {n : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r) :
    MonoidHom.ker FP.toPresentation.quotientMap ≤
      GroupAlgebra.zSubgro p FP.Free n :=
  FP.depths.quotient_ker_forall hD

/-- Depth-two kernel containment for degree-one silent filtered presentations. -/
theorem ker_degree_silent
    (hD : FP.depths.degreeOneSilent) :
    MonoidHom.ker FP.toPresentation.quotientMap ≤
      GroupAlgebra.zSubgro p FP.Free 2 :=
  FP.quotient_ker_forall hD

/-- Same depth-two kernel containment, using the filtered-presentation-level predicate. -/
theorem quotient_ker_two (hD : FP.degreeOneSilent) :
    MonoidHom.ker FP.toPresentation.quotientMap ≤
      GroupAlgebra.zSubgro p FP.Free 2 :=
  FP.ker_degree_silent hD

/-- Relators whose certified depth is active by cutoff `n`, viewed as a subset of
the ambient free group.  If the same word has multiple membership proofs, proof
irrelevance makes the chosen depth propositionally the same. -/
def activeRelatorSet (FP : FPres.{u} p) (n : ℕ) : Set FP.Free :=
  {w | ∃ h : w ∈ FP.toPresentation.rels,
    FP.depths.depth ⟨w, h⟩ ≤ n}


/-- Free-word relators whose certified depth is exactly `n`. -/
def exactRelatorSet (FP : FPres.{u} p) (n : ℕ) : Set FP.Free :=
  {w | ∃ h : w ∈ FP.toPresentation.rels,
    FP.depths.depth ⟨w, h⟩ = n}

@[simp] theorem active_relator_set (FP : FPres.{u} p) (n : ℕ)
    (w : FP.Free) :
    w ∈ FP.activeRelatorSet n ↔ ∃ h : w ∈ FP.toPresentation.rels,
      FP.depths.depth ⟨w, h⟩ ≤ n := Iff.rfl

@[simp] theorem exact_relator_set (FP : FPres.{u} p) (n : ℕ)
    (w : FP.Free) :
    w ∈ FP.exactRelatorSet n ↔ ∃ h : w ∈ FP.toPresentation.rels,
      FP.depths.depth ⟨w, h⟩ = n := Iff.rfl

/-- Exact free-word relator sets are contained in the ambient relator set. -/
theorem exact_subset_rels (FP : FPres.{u} p) (n : ℕ) :
    FP.exactRelatorSet n ⊆ FP.toPresentation.rels := by
  intro w hw
  rcases hw with ⟨h, _⟩
  exact h

/-- Exact-depth relators are active at any later cutoff. -/
theorem exact_subset_active
    (FP : FPres.{u} p) {k n : ℕ} (hkn : k ≤ n) :
    FP.exactRelatorSet k ⊆ FP.activeRelatorSet n := by
  intro w hw
  rcases hw with ⟨h, hd⟩
  exact ⟨h, le_trans (le_of_eq hd) hkn⟩

/-- Exact-depth relators are active at their own cutoff. -/
theorem exact_subset_self
    (FP : FPres.{u} p) (n : ℕ) :
    FP.exactRelatorSet n ⊆ FP.activeRelatorSet n :=
  FP.exact_subset_active (le_rfl)

/-- Active relators remain ambient relators after increasing the cutoff. -/
theorem active_set_subset
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    FP.activeRelatorSet m ⊆ FP.activeRelatorSet n := by
  intro w hw
  rcases hw with ⟨h, hd⟩
  exact ⟨h, le_trans hd hmn⟩

/-- The active free-word set is the image of the subtype-level active relators. -/
theorem active_set_image (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet n =
      ((fun r : FP.toPresentation.Relator => (r : FP.Free)) '' FP.depths.activeAt n) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨h, hd⟩
    refine ⟨⟨w, h⟩, ?_, rfl⟩
    exact hd
  · intro hw
    rcases hw with ⟨r, hr, rfl⟩
    exact ⟨r.2, hr⟩


/-- The exact free-word set is the image of the subtype-level exact-depth slice. -/
theorem exact_set_image (FP : FPres.{u} p) (n : ℕ) :
    FP.exactRelatorSet n =
      ((fun r : FP.toPresentation.Relator => (r : FP.Free)) '' FP.depths.exactAt n) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨h, hd⟩
    refine ⟨⟨w, h⟩, ?_, rfl⟩
    exact hd
  · intro hw
    rcases hw with ⟨r, hr, rfl⟩
    exact ⟨r.2, hr⟩

/-- Increasing the active free-word cutoff adds exactly the next exact-depth words. -/
theorem active_union_exact
    (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet (n + 1) = FP.activeRelatorSet n ∪ FP.exactRelatorSet (n + 1) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨h, hd⟩
    have hcase : FP.depths.depth ⟨w, h⟩ ≤ n ∨
        FP.depths.depth ⟨w, h⟩ = n + 1 := by omega
    rcases hcase with hle | heq
    · exact Or.inl ⟨h, hle⟩
    · exact Or.inr ⟨h, heq⟩
  · intro hw
    rcases hw with ⟨h, hle⟩ | ⟨h, heq⟩
    · exact ⟨h, Nat.le_trans hle (Nat.le_succ n)⟩
    · exact ⟨h, le_of_eq heq⟩

/-- The new active free-word relators at successor cutoff are exactly the exact-depth slice. -/
theorem active_set_diff
    (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet (n + 1) \ FP.activeRelatorSet n =
      FP.exactRelatorSet (n + 1) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hact, hnot⟩
    rcases hact with ⟨h, hd⟩
    have hgt : n < FP.depths.depth ⟨w, h⟩ := by
      by_contra hleNot
      have hle : FP.depths.depth ⟨w, h⟩ ≤ n := Nat.le_of_not_gt hleNot
      exact hnot ⟨h, hle⟩
    have heq : FP.depths.depth ⟨w, h⟩ = n + 1 := by omega
    exact ⟨h, heq⟩
  · intro hw
    rcases hw with ⟨h, heq⟩
    constructor
    · exact ⟨h, le_of_eq heq⟩
    · intro hold
      rcases hold with ⟨h0, hd0⟩
      have hs : (⟨w, h0⟩ : FP.toPresentation.Relator) = ⟨w, h⟩ := by
        apply Subtype.ext
        rfl
      have hdepth : FP.depths.depth (⟨w, h0⟩ : FP.toPresentation.Relator) =
          FP.depths.depth (⟨w, h⟩ : FP.toPresentation.Relator) := congrArg FP.depths.depth hs
      omega

/-- The active free-word set up to `n` is the union of exact-depth free-word slices. -/
theorem i_union_exact
    (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet n = ⋃ i : {i : ℕ // i ≤ n}, FP.exactRelatorSet i.1 := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨h, hle⟩
    refine Set.mem_iUnion.mpr ⟨⟨FP.depths.depth ⟨w, h⟩, hle⟩, ?_⟩
    exact ⟨h, rfl⟩
  · intro hw
    rcases Set.mem_iUnion.mp hw with ⟨i, hi⟩
    rcases hi with ⟨h, hd⟩
    exact ⟨h, le_trans (le_of_eq hd) i.2⟩

/-- Between two cutoffs, the new free-word relators are the union of exact-depth
slices with indices in the half-open interval `(m,n]`. -/
theorem union_ioc_exact
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    FP.activeRelatorSet n =
      FP.activeRelatorSet m ∪
        ⋃ i : {i : ℕ // m < i ∧ i ≤ n}, FP.exactRelatorSet i.1 := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨h, hdle⟩
    by_cases hdm : FP.depths.depth ⟨w, h⟩ ≤ m
    · exact Or.inl ⟨h, hdm⟩
    · right
      have hgt : m < FP.depths.depth ⟨w, h⟩ := Nat.lt_of_not_ge hdm
      refine Set.mem_iUnion.mpr ⟨⟨FP.depths.depth ⟨w, h⟩, hgt, hdle⟩, ?_⟩
      exact ⟨h, rfl⟩
  · intro hw
    rcases hw with hw | hw
    · rcases hw with ⟨h, hd⟩
      exact ⟨h, le_trans hd hmn⟩
    · rcases Set.mem_iUnion.mp hw with ⟨i, hi⟩
      rcases hi with ⟨h, hd⟩
      exact ⟨h, le_trans (le_of_eq hd) i.2.2⟩

/-- The old active free-word relators and the newly exact-depth free words are disjoint.
Although `activeRelatorSet` forgets the subtype proof of being a relator, proof
irrelevance for the relator subtype lets us compare the two certified depths. -/
theorem disjoint_exact_succ
    (FP : FPres.{u} p) (n : ℕ) :
    Disjoint (FP.activeRelatorSet n) (FP.exactRelatorSet (n + 1)) := by
  rw [Set.disjoint_left]
  intro w hold hnew
  rcases hold with ⟨h₁, hle⟩
  rcases hnew with ⟨h₂, heq⟩
  have hs : (⟨w, h₁⟩ : FP.toPresentation.Relator) = ⟨w, h₂⟩ := by
    apply Subtype.ext
    rfl
  have hd : FP.depths.depth (⟨w, h₁⟩ : FP.toPresentation.Relator) =
      FP.depths.depth (⟨w, h₂⟩ : FP.toPresentation.Relator) := congrArg FP.depths.depth hs
  omega

/-- Exact free-word slices at distinct depths are disjoint. -/
theorem disjoint_exact_ne (FP : FPres.{u} p)
    {m n : ℕ} (h : m ≠ n) :
    Disjoint (FP.exactRelatorSet m) (FP.exactRelatorSet n) := by
  rw [Set.disjoint_left]
  intro w hm hn
  rcases hm with ⟨hmRel, hmDepth⟩
  rcases hn with ⟨hnRel, hnDepth⟩
  have hs : (⟨w, hmRel⟩ : FP.toPresentation.Relator) = ⟨w, hnRel⟩ := by
    apply Subtype.ext
    rfl
  have hd : FP.depths.depth (⟨w, hmRel⟩ : FP.toPresentation.Relator) =
      FP.depths.depth (⟨w, hnRel⟩ : FP.toPresentation.Relator) := congrArg FP.depths.depth hs
  apply h
  calc
    m = FP.depths.depth (⟨w, hmRel⟩ : FP.toPresentation.Relator) := hmDepth.symm
    _ = FP.depths.depth (⟨w, hnRel⟩ : FP.toPresentation.Relator) := hd
    _ = n := hnDepth

/-- Emptiness of active free-word relators is equivalent to emptiness of the
subtype-level active relator set. -/
theorem active_set_empty (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet n = ∅ ↔ FP.depths.activeAt n = ∅ := by
  constructor
  · intro h
    ext r
    constructor
    · intro hr
      have hw : (r : FP.Free) ∈ FP.activeRelatorSet n := ⟨r.2, hr⟩
      rw [h] at hw
      exact False.elim hw
    · intro hr
      exact False.elim hr
  · intro h
    ext w
    constructor
    · intro hw
      rcases hw with ⟨hr, hd⟩
      have hx : (⟨w, hr⟩ : FP.toPresentation.Relator) ∈ FP.depths.activeAt n := hd
      rw [h] at hx
      exact False.elim hx
    · intro hw
      exact False.elim hw

theorem active_subset_rels (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorSet n ⊆ FP.toPresentation.rels := by
  intro w hw
  rcases hw with ⟨h, _⟩
  exact h

/-- Active relator sets are monotone in the cutoff. -/
theorem active_set_mono (FP : FPres.{u} p) {m n : ℕ}
    (hmn : m ≤ n) : FP.activeRelatorSet m ⊆ FP.activeRelatorSet n := by
  intro w hw
  rcases hw with ⟨h, hd⟩
  exact ⟨h, le_trans hd hmn⟩

/-- The subpresentation containing only relators active by cutoff `n`. -/
def activePresentation (FP : FPres.{u} p) (n : ℕ) : Presentation.{u} :=
  FP.toPresentation.withRelators (FP.activeRelatorSet n)

/-- The subpresentation containing only relators of exact certified depth `n`. -/
def exactPresentation (FP : FPres.{u} p) (n : ℕ) : Presentation.{u} :=
  FP.toPresentation.withRelators (FP.exactRelatorSet n)

/-- Exact relators of the exact subpresentation are equivalent to subtype-level
exact-depth relators of the original filtered presentation. -/
noncomputable def exactRelatorEquiv (FP : FPres.{u} p) (n : ℕ) :
    (FP.exactPresentation n).Relator ≃
      {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt n} where
  toFun := fun r => ⟨⟨r.1, Classical.choose r.2⟩, Classical.choose_spec r.2⟩
  invFun := fun r => ⟨r.1.1, ⟨r.1.2, r.2⟩⟩
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro r
    cases r with
    | mk rr h =>
      cases rr
      rfl

@[simp] theorem exact_relator_val
    (FP : FPres.{u} p) (n : ℕ)
    (r : (FP.exactPresentation n).Relator) :
    ((FP.exactRelatorEquiv n r).1 : FP.Free) = r.1 := rfl

/-- Active relators of the active subpresentation are equivalent to subtype-level
active relators of the original filtered presentation. -/
noncomputable def activeRelatorEquiv (FP : FPres.{u} p) (n : ℕ) :
    (FP.activePresentation n).Relator ≃
      {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n} where
  toFun := fun r => ⟨⟨r.1, Classical.choose r.2⟩, Classical.choose_spec r.2⟩
  invFun := fun r => ⟨r.1.1, ⟨r.1.2, r.2⟩⟩
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro r
    cases r with
    | mk rr h =>
      cases rr
      rfl

@[simp] theorem active_relator_val
    (FP : FPres.{u} p) (n : ℕ)
    (r : (FP.activePresentation n).Relator) :
    ((FP.activeRelatorEquiv n r).1 : FP.Free) = r.1 := rfl

/-- Exact-depth subpresentations have finitely many relators whenever the original
presentation does. -/
noncomputable instance exactPresentationFintype
    (FP : FPres.{u} p) (n : ℕ)
    [Fintype FP.toPresentation.Relator] : Fintype (FP.exactPresentation n).Relator := by
  classical
  exact Fintype.ofEquiv
    {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt n}
    (FP.exactRelatorEquiv n).symm

/-- The number of exact-depth relators is bounded by the total number of relators. -/
theorem exact_presentation_relator
    (FP : FPres.{u} p) (n : ℕ)
    [Fintype FP.toPresentation.Relator] :
    Fintype.card (FP.exactPresentation n).Relator ≤
      Fintype.card FP.toPresentation.Relator := by
  classical
  calc
    Fintype.card (FP.exactPresentation n).Relator =
        Fintype.card {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt n} :=
      Fintype.card_congr (FP.exactRelatorEquiv n)
    _ ≤ Fintype.card FP.toPresentation.Relator :=
      Fintype.card_subtype_le
        (fun r : FP.toPresentation.Relator => r ∈ FP.depths.exactAt n)

/-- Active subpresentations have finitely many relators whenever the original
presentation does. -/
noncomputable instance activePresentationFintype
    (FP : FPres.{u} p) (n : ℕ)
    [Fintype FP.toPresentation.Relator] : Fintype (FP.activePresentation n).Relator := by
  classical
  exact Fintype.ofEquiv
    {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n}
    (FP.activeRelatorEquiv n).symm

/-- The number of active relators is bounded by the total number of relators. -/
theorem active_presentation_relator
    (FP : FPres.{u} p) (n : ℕ)
    [Fintype FP.toPresentation.Relator] :
    Fintype.card (FP.activePresentation n).Relator ≤
      Fintype.card FP.toPresentation.Relator := by
  classical
  calc
    Fintype.card (FP.activePresentation n).Relator =
        Fintype.card {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n} :=
      Fintype.card_congr (FP.activeRelatorEquiv n)
    _ ≤ Fintype.card FP.toPresentation.Relator :=
      Fintype.card_subtype_le
        (fun r : FP.toPresentation.Relator => r ∈ FP.depths.activeAt n)


/-- The number of active relators is monotone in the cutoff. -/
theorem active_presentation_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    [Fintype FP.toPresentation.Relator] :
    Fintype.card (FP.activePresentation m).Relator ≤
      Fintype.card (FP.activePresentation n).Relator := by
  classical
  let A := {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt m}
  let B := {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n}
  let f : A → B := fun r => ⟨r.1, FP.depths.activeAt_mono hmn r.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    cases a with
    | mk av ah =>
    cases b with
    | mk bv bh =>
    simp only at hab
    cases hab
    rfl
  calc
    Fintype.card (FP.activePresentation m).Relator = Fintype.card A :=
      Fintype.card_congr (FP.activeRelatorEquiv m)
    _ ≤ Fintype.card B := Fintype.card_le_of_injective f hf
    _ = Fintype.card (FP.activePresentation n).Relator :=
      (Fintype.card_congr (FP.activeRelatorEquiv n)).symm


/-- Relators appearing at cutoff `n+1` split into old active relators and the
new exact-depth slice. -/
noncomputable def activePresentationSum
    (FP : FPres.{u} p) (n : ℕ) :
    (FP.activePresentation (n + 1)).Relator ≃
      ((FP.activePresentation n).Relator ⊕ (FP.exactPresentation (n + 1)).Relator) :=
  (FP.activeRelatorEquiv (n + 1)).trans <|
    (FP.depths.activeSuccSum n).trans <|
      Equiv.sumCongr (FP.activeRelatorEquiv n).symm
        (FP.exactRelatorEquiv (n + 1)).symm

/-- Maximum certified relator depth for a finite-relator filtered presentation. -/
noncomputable def maxRelatorDepth (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] : ℕ :=
  Finset.univ.sup FP.depths.depth

/-- Every relator depth is bounded by `maxRelatorDepth`. -/
theorem depth_max_relator (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (r : FP.toPresentation.Relator) :
    FP.depths.depth r ≤ FP.maxRelatorDepth := by
  classical
  dsimp [maxRelatorDepth]
  exact Finset.le_sup (Finset.mem_univ r)

/-- If a degree-one-silent finite-relator presentation has a relator, its maximum depth is
at least two. -/
theorem max_relator_silent
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    [Nonempty FP.toPresentation.Relator] (h : FP.degreeOneSilent) :
    2 ≤ FP.maxRelatorDepth := by
  classical
  let r : FP.toPresentation.Relator := Classical.choice inferInstance
  exact le_trans (h r) (FP.depth_max_relator r)

/-- Conversely, a degree-one-silent presentation with maximum depth below two has no
bundled relators. -/
theorem empty_silent_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (h : FP.degreeOneSilent) (hm : FP.maxRelatorDepth < 2) :
    IsEmpty FP.toPresentation.Relator := by
  refine ⟨?_⟩
  intro r
  have h2 : 2 ≤ FP.maxRelatorDepth :=
    le_trans (h r) (FP.depth_max_relator r)
  omega

/-- Cardinal form of the preceding emptiness criterion. -/
theorem card_silent_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (h : FP.degreeOneSilent) (hm : FP.maxRelatorDepth < 2) :
    Fintype.card FP.toPresentation.Relator = 0 := by
  haveI : IsEmpty FP.toPresentation.Relator :=
    FP.empty_silent_max h hm
  simp

/-- `Nat.card` form of the degree-one-silent low-maximum-depth emptiness criterion. -/
theorem nat_silent_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (h : FP.degreeOneSilent) (hm : FP.maxRelatorDepth < 2) :
    Nat.card FP.toPresentation.Relator = 0 := by
  haveI : IsEmpty FP.toPresentation.Relator :=
    FP.empty_silent_max h hm
  simp

/-- Positive relator cardinality forces maximum depth at least two under degree-one silence. -/
theorem two_max_silent
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (h : FP.degreeOneSilent) (hc : 0 < Fintype.card FP.toPresentation.Relator) :
    2 ≤ FP.maxRelatorDepth := by
  classical
  haveI : Nonempty FP.toPresentation.Relator := Fintype.card_pos_iff.mp hc
  exact FP.max_relator_silent h

/-- `Nat.card` positive-cardinality version of the preceding lower bound. -/
theorem max_silent_pos
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (h : FP.degreeOneSilent) (hc : 0 < Nat.card FP.toPresentation.Relator) :
    2 ≤ FP.maxRelatorDepth := by
  classical
  rw [Nat.card_eq_fintype_card] at hc
  haveI : Nonempty FP.toPresentation.Relator := Fintype.card_pos_iff.mp hc
  exact FP.max_relator_silent h

/-- Above the maximum certified depth, there are no exact-depth free-word relators. -/
theorem exact_empty_max (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] {n : ℕ} (h : FP.maxRelatorDepth < n) :
    FP.exactRelatorSet n = ∅ := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hr, hd⟩
    have hle := FP.depth_max_relator (⟨w, hr⟩ : FP.toPresentation.Relator)
    omega
  · intro hw
    exact False.elim hw

/-- At the maximum certified depth, all relators are active. -/
theorem active_max_rels
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.activeRelatorSet FP.maxRelatorDepth = FP.toPresentation.rels := by
  ext w
  constructor
  · intro hw
    exact FP.active_subset_rels _ hw
  · intro hw
    exact ⟨hw, FP.depth_max_relator (⟨w, hw⟩ : FP.toPresentation.Relator)⟩

/-- Beyond the maximum certified depth, all relators remain active. -/
theorem active_rels_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {n : ℕ} (hn : FP.maxRelatorDepth ≤ n) :
    FP.activeRelatorSet n = FP.toPresentation.rels := by
  ext w
  constructor
  · intro hw
    exact FP.active_subset_rels _ hw
  · intro hw
    have hle := FP.depth_max_relator (⟨w, hw⟩ : FP.toPresentation.Relator)
    exact ⟨hw, le_trans hle hn⟩

/-- If every certified relator depth is at most `n`, then all relators are active at `n`.
This version does not require finiteness of the relator set. -/
theorem rels_forall_depth
    (FP : FPres.{u} p) {n : ℕ}
    (h : ∀ r : FP.toPresentation.Relator, FP.depths.depth r ≤ n) :
    FP.activeRelatorSet n = FP.toPresentation.rels := by
  ext w
  constructor
  · intro hw
    exact FP.active_subset_rels _ hw
  · intro hw
    exact ⟨hw, h ⟨w, hw⟩⟩

/-- If every certified relator depth is at most `n`, the active presentation at `n`
is definitionally the original presentation (up to the bundled record equality). -/
theorem active_presentation_original
    (FP : FPres.{u} p) {n : ℕ}
    (h : ∀ r : FP.toPresentation.Relator, FP.depths.depth r ≤ n) :
    FP.activePresentation n = FP.toPresentation := by
  dsimp [activePresentation]
  rw [FP.rels_forall_depth h]
  cases FP.toPresentation
  rfl

/-- Exact relator counts vanish above the maximum certified depth. -/
theorem exact_count_max (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] {n : ℕ} (h : FP.maxRelatorDepth < n) :
    Nat.card (FP.exactPresentation n).Relator = 0 := by
  classical
  have hempty := FP.exact_empty_max h
  haveI : IsEmpty (FP.exactPresentation n).Relator := ⟨by
    intro r
    have hr : r.1 ∈ FP.exactRelatorSet n := r.2
    rw [hempty] at hr
    exact hr.elim⟩
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_eq_zero_iff.mpr inferInstance)

/-- At the maximum depth, the active subpresentation is the original presentation. -/
theorem active_presentation_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.activePresentation FP.maxRelatorDepth = FP.toPresentation := by
  dsimp [activePresentation]
  rw [FP.active_max_rels]
  cases FP.toPresentation
  rfl

/-- Beyond the maximum depth, the active subpresentation has stabilized to the original. -/
theorem presentation_original_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {n : ℕ} (hn : FP.maxRelatorDepth ≤ n) :
    FP.activePresentation n = FP.toPresentation := by
  dsimp [activePresentation]
  rw [FP.active_rels_max hn]
  cases FP.toPresentation
  rfl

/-- Number (as `Nat.card`) of generators of a filtered presentation. -/
noncomputable def generatorCount (FP : FPres.{u} p) : ℕ :=
  Nat.card FP.Gen

@[simp] theorem generator_active_presentation (FP : FPres.{u} p) (n : ℕ) :
    Nat.card (FP.activePresentation n).Gen = FP.generatorCount := rfl

@[simp] theorem generator_exact_presentation (FP : FPres.{u} p) (n : ℕ) :
    Nat.card (FP.exactPresentation n).Gen = FP.generatorCount := rfl

/-- Number (as `Nat.card`) of relators active by cutoff `n`. -/
noncomputable def activeRelatorCount (FP : FPres.{u} p) (n : ℕ) : ℕ :=
  Nat.card (FP.activePresentation n).Relator

/-- Number (as `Nat.card`) of relators of exact certified depth `n`. -/
noncomputable def exactRelatorCount (FP : FPres.{u} p) (n : ℕ) : ℕ :=
  Nat.card (FP.exactPresentation n).Relator

@[simp] theorem active_count_def (FP : FPres.{u} p) (n : ℕ) :
    FP.activeRelatorCount n = Nat.card (FP.activePresentation n).Relator := rfl

@[simp] theorem exact_count_def (FP : FPres.{u} p) (n : ℕ) :
    FP.exactRelatorCount n = Nat.card (FP.exactPresentation n).Relator := rfl

/-- Finset histogram multiplicity of relators of a given certified depth. -/
noncomputable def relatorDepthMultiplicity (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun r : FP.toPresentation.Relator => FP.depths.depth r = n)).card

/-- Exact relator counts agree with the elementary finite histogram of depths. -/
theorem exact_count_multiplicity
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.exactRelatorCount n = FP.relatorDepthMultiplicity n := by
  classical
  unfold exactRelatorCount relatorDepthMultiplicity
  calc
    Nat.card (FP.exactPresentation n).Relator =
        Nat.card {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt n} :=
      Nat.card_congr (FP.exactRelatorEquiv n)
    _ = Fintype.card {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt n} :=
      Nat.card_eq_fintype_card
    _ = (Finset.univ.filter (fun r : FP.toPresentation.Relator => FP.depths.depth r = n)).card := by
      simpa using
        (Fintype.card_subtype (fun r : FP.toPresentation.Relator => FP.depths.depth r = n))

/-- Active relator counts stabilize at the total relator count beyond the maximum depth. -/
theorem active_relators_max
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {n : ℕ} (hn : FP.maxRelatorDepth ≤ n) :
    FP.activeRelatorCount n = Nat.card FP.toPresentation.Relator := by
  unfold activeRelatorCount
  rw [FP.presentation_original_max hn]

/-- Packaged vanishing of the exact relator-count function above the maximum depth. -/
theorem exact_relator_max (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] {n : ℕ} (h : FP.maxRelatorDepth < n) :
    FP.exactRelatorCount n = 0 := by
  simpa [exactRelatorCount] using FP.exact_count_max h

/-- Cumulative active-presentation relator count as a sum of exact-depth counts. -/
theorem presentation_exact_fin
    (FP : FPres.{u} p) (n : ℕ)
    [Finite FP.toPresentation.Relator] :
    Nat.card (FP.activePresentation n).Relator =
      ∑ i : Fin (n + 1), Nat.card (FP.exactPresentation i.1).Relator := by
  classical
  calc
    Nat.card (FP.activePresentation n).Relator =
        Nat.card {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n} :=
      Nat.card_congr (FP.activeRelatorEquiv n)
    _ = ∑ i : Fin (n + 1),
          Nat.card {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt i.1} :=
      FP.depths.nat_exact_fin n
    _ = ∑ i : Fin (n + 1), Nat.card (FP.exactPresentation i.1).Relator := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.card_congr (FP.exactRelatorEquiv i.1).symm

/-- Cardinal recurrence for relators in successive active subpresentations. -/
theorem nat_presentation_succ
    (FP : FPres.{u} p) (n : ℕ)
    [Finite FP.toPresentation.Relator] :
    Nat.card (FP.activePresentation (n + 1)).Relator =
      Nat.card (FP.activePresentation n).Relator +
        Nat.card (FP.exactPresentation (n + 1)).Relator := by
  classical
  haveI : Finite (FP.activePresentation n).Relator := by
    exact Finite.of_equiv {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n}
      (FP.activeRelatorEquiv n).symm
  haveI : Finite (FP.activePresentation (n + 1)).Relator := by
    exact Finite.of_equiv {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt (n + 1)}
      (FP.activeRelatorEquiv (n + 1)).symm
  haveI : Finite (FP.exactPresentation (n + 1)).Relator := by
    exact Finite.of_equiv {r : FP.toPresentation.Relator // r ∈ FP.depths.exactAt (n + 1)}
      (FP.exactRelatorEquiv (n + 1)).symm
  calc
    Nat.card (FP.activePresentation (n + 1)).Relator =
        Nat.card ((FP.activePresentation n).Relator ⊕
          (FP.exactPresentation (n + 1)).Relator) :=
      Nat.card_congr (FP.activePresentationSum n)
    _ = _ := Nat.card_sum

/-- Packaged recurrence for the active/exact relator-count functions. -/
theorem active_count_succ
    (FP : FPres.{u} p) (n : ℕ)
    [Finite FP.toPresentation.Relator] :
    FP.activeRelatorCount (n + 1) =
      FP.activeRelatorCount n + FP.exactRelatorCount (n + 1) := by
  simpa [activeRelatorCount, exactRelatorCount] using
    FP.nat_presentation_succ n

/-- Packaged cumulative formula for active relator counts. -/
theorem active_count_exact
    (FP : FPres.{u} p) (n : ℕ)
    [Finite FP.toPresentation.Relator] :
    FP.activeRelatorCount n =
      ∑ i : Fin (n + 1), FP.exactRelatorCount i.1 := by
  simpa [activeRelatorCount, exactRelatorCount] using
    FP.presentation_exact_fin n

/-- The finite-support sequence of exact relator multiplicities.  Its support is
contained in `range (maxRelatorDepth+1)`. -/
noncomputable def relatorDepthFinsupp (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range (FP.maxRelatorDepth + 1))
    (fun n => FP.relatorDepthMultiplicity n) (by
      intro n hn
      rw [Finset.mem_range]
      by_contra hlt
      have hmax : FP.maxRelatorDepth < n := Nat.lt_of_not_ge (by
        intro hnle
        exact hlt (Nat.lt_succ_of_le hnle))
      have hz : FP.relatorDepthMultiplicity n = 0 := by
        rw [← FP.exact_count_multiplicity n]
        exact FP.exact_relator_max hmax
      exact hn hz)

@[simp] theorem relator_depth_finsupp (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.relatorDepthFinsupp n = FP.relatorDepthMultiplicity n :=
  Finsupp.onFinset_apply

/-- The support of the depth histogram is bounded by the maximum depth. -/
theorem finsupp_subset_range
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.relatorDepthFinsupp.support ⊆ Finset.range (FP.maxRelatorDepth + 1) := by
  intro n hn
  rw [Finsupp.mem_support_iff] at hn
  rw [Finset.mem_range]
  by_contra hlt
  have hmax : FP.maxRelatorDepth < n := Nat.lt_of_not_ge (by
    intro hnle
    exact hlt (Nat.lt_succ_of_le hnle))
  have hz : FP.relatorDepthMultiplicity n = 0 := by
    rw [← FP.exact_count_multiplicity n]
    exact FP.exact_relator_max hmax
  rw [FP.relator_depth_finsupp] at hn
  exact hn hz

/-- The finite histogram of relator depths sums to the total number of relators. -/
theorem depth_multiplicity_relators
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    (∑ i : Fin (FP.maxRelatorDepth + 1), FP.relatorDepthMultiplicity i.1) =
      Nat.card FP.toPresentation.Relator := by
  classical
  have hsum : FP.activeRelatorCount FP.maxRelatorDepth =
      ∑ i : Fin (FP.maxRelatorDepth + 1), FP.relatorDepthMultiplicity i.1 := by
    calc
      FP.activeRelatorCount FP.maxRelatorDepth =
          ∑ i : Fin (FP.maxRelatorDepth + 1), FP.exactRelatorCount i.1 :=
        FP.active_count_exact FP.maxRelatorDepth
      _ = ∑ i : Fin (FP.maxRelatorDepth + 1), FP.relatorDepthMultiplicity i.1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact FP.exact_count_multiplicity i.1
  rw [← hsum]
  unfold activeRelatorCount
  rw [FP.active_presentation_max]


/-- Weighted sum of a sequence over the certified depths of all relators. -/
noncomputable def relatorWeightedSum (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (a : ℕ → ℕ) : ℕ :=
  ∑ r : FP.toPresentation.Relator, a (FP.depths.depth r)

@[simp] theorem relator_weighted_const
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.relatorWeightedSum (fun _ => 1) = Fintype.card FP.toPresentation.Relator := by
  classical
  simp [relatorWeightedSum]

@[simp] theorem relator_depth_weighted
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.relatorWeightedSum (fun _ => 0) = 0 := by
  classical
  simp [relatorWeightedSum]

theorem relator_weighted_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (a b : ℕ → ℕ) :
    FP.relatorWeightedSum (fun n => a n + b n) =
      FP.relatorWeightedSum a + FP.relatorWeightedSum b := by
  classical
  simp [relatorWeightedSum, Finset.sum_add_distrib]

theorem relator_weighted_left
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (c : ℕ) (a : ℕ → ℕ) :
    FP.relatorWeightedSum (fun n => c * a n) =
      c * FP.relatorWeightedSum a := by
  classical
  simp [relatorWeightedSum, Finset.mul_sum]

/-- Weighting by a Kronecker delta recovers the depth multiplicity. -/
theorem relator_weighted_delta
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.relatorWeightedSum (fun k => if k = n then 1 else 0) =
      FP.relatorDepthMultiplicity n := by
  classical
  unfold relatorWeightedSum relatorDepthMultiplicity
  rw [Finset.card_filter]

/-- Weighted sums over relator depths can be computed from the finite histogram. -/
theorem relator_weighted_histogram
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (a : ℕ → ℕ) :
    FP.relatorWeightedSum a =
      ∑ n ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.relatorDepthMultiplicity n * a n := by
  classical
  let s : Finset FP.toPresentation.Relator := Finset.univ
  let t : Finset ℕ := Finset.range (FP.maxRelatorDepth + 1)
  have hmap : ∀ r ∈ s, FP.depths.depth r ∈ t := by
    intro r hr
    dsimp [t]
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (FP.depth_max_relator r)
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := s) (t := t)
    (g := fun r : FP.toPresentation.Relator => FP.depths.depth r) hmap
    (f := fun r : FP.toPresentation.Relator => a (FP.depths.depth r))
  symm
  calc
    ∑ n ∈ t, FP.relatorDepthMultiplicity n * a n =
        ∑ n ∈ t, ∑ r ∈ s with FP.depths.depth r = n, a (FP.depths.depth r) := by
      apply Finset.sum_congr rfl
      intro n hn
      -- on the fiber `depth r = n`, the summand is constantly `a n`
      have hconst : (∑ r ∈ s with FP.depths.depth r = n, a (FP.depths.depth r)) =
          (s.filter (fun r => FP.depths.depth r = n)).card * a n := by
        calc
          (∑ r ∈ s with FP.depths.depth r = n, a (FP.depths.depth r)) =
              ∑ r ∈ s.filter (fun r => FP.depths.depth r = n), a n := by
            apply Finset.sum_congr rfl
            intro r hr
            have hdepth : FP.depths.depth r = n := by
              simpa using (Finset.mem_filter.mp hr).2
            rw [hdepth]
          _ = (s.filter (fun r => FP.depths.depth r = n)).card * a n := by
            simp [Finset.sum_const]
      rw [hconst]
      dsimp [relatorDepthMultiplicity, s]
    _ = ∑ r ∈ s, a (FP.depths.depth r) := hfiber
    _ = FP.relatorWeightedSum a := by
      simp [relatorWeightedSum, s]

/-- Generator contribution in the usual one-step shifted coefficient recurrence. -/
noncomputable def generatorShiftContribution (FP : FPres.{u} p)
    (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  if _h : 0 < n then FP.generatorCount * b (n - 1) else 0

@[simp] theorem shift_contribution_zero (FP : FPres.{u} p)
    (b : ℕ → ℕ) : FP.generatorShiftContribution b 0 = 0 := by
  simp [generatorShiftContribution]

theorem shift_contribution_succ (FP : FPres.{u} p)
    (b : ℕ → ℕ) (n : ℕ) :
    FP.generatorShiftContribution b (n + 1) = FP.generatorCount * b n := by
  simp [generatorShiftContribution]

theorem shift_contribution_mono (FP : FPres.{u} p)
    {b c : ℕ → ℕ} (hbc : ∀ k, b k ≤ c k) (n : ℕ) :
    FP.generatorShiftContribution b n ≤ FP.generatorShiftContribution c n := by
  by_cases hn : 0 < n
  · simp [generatorShiftContribution, hn, Nat.mul_le_mul_left _ (hbc (n - 1))]
  · simp [generatorShiftContribution, hn]

/-- Prefix sums of the shifted generator contribution reindex to one shorter
prefix of the original sequence. -/
theorem sum_shift_contribution
    (FP : FPres.{u} p) (b : ℕ → ℕ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), FP.generatorShiftContribution b n) =
      FP.generatorCount * (∑ k ∈ Finset.range N, b k) := by
  induction N with
  | zero => simp [generatorShiftContribution]
  | succ N ih =>
      rw [Finset.sum_range_succ (f := fun n => FP.generatorShiftContribution b n) (n := N + 1)]
      rw [ih, FP.shift_contribution_succ b N]
      rw [Finset.sum_range_succ (f := fun k => b k) (n := N)]
      rw [Nat.mul_add]

/-- Generator-shift contribution is additive in the coefficient sequence. -/
theorem shift_contribution_add (FP : FPres.{u} p)
    (b c : ℕ → ℕ) (n : ℕ) :
    FP.generatorShiftContribution (fun k => b k + c k) n =
      FP.generatorShiftContribution b n + FP.generatorShiftContribution c n := by
  by_cases hn : 0 < n
  · simp [generatorShiftContribution, hn, Nat.mul_add]
  · simp [generatorShiftContribution, hn]

/-- Generator-shift contribution is homogeneous in the coefficient sequence. -/
theorem shift_contribution_left (FP : FPres.{u} p)
    (c : ℕ) (b : ℕ → ℕ) (n : ℕ) :
    FP.generatorShiftContribution (fun k => c * b k) n =
      c * FP.generatorShiftContribution b n := by
  by_cases hn : 0 < n
  · simp [generatorShiftContribution, hn, Nat.mul_assoc, Nat.mul_comm]
  · simp [generatorShiftContribution, hn]

/-- Convolution-style relator contribution at degree `n` against a coefficient
sequence `b`: sum over relators of `b (n-depth)` when the depth is at most `n`. -/
noncomputable def relatorDepthConvolution (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  FP.relatorWeightedSum (fun q => if _h : q ≤ n then b (n - q) else 0)

/-- Convolution against the constant-one sequence counts precisely the relators
active at the cutoff. -/
theorem relator_convolution_const
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.relatorDepthConvolution (fun _ => 1) n = FP.activeRelatorCount n := by
  classical
  unfold relatorDepthConvolution relatorWeightedSum activeRelatorCount
  calc
    (∑ r : FP.toPresentation.Relator,
        (if _h : FP.depths.depth r ≤ n then 1 else 0)) =
        (Finset.univ.filter
          (fun r : FP.toPresentation.Relator => FP.depths.depth r ≤ n)).card := by
      rw [Finset.card_filter]
      simp
    _ = Fintype.card {r : FP.toPresentation.Relator // FP.depths.depth r ≤ n} := by
      simpa using
        (Fintype.card_subtype
          (fun r : FP.toPresentation.Relator => FP.depths.depth r ≤ n)).symm
    _ = Fintype.card {r : FP.toPresentation.Relator // r ∈ FP.depths.activeAt n} := by
      refine Fintype.card_congr ?_
      refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
      · intro r; exact ⟨r.1, by simp [Presentation.RDepths.activeAt]⟩
      · intro r; exact ⟨r.1, (FP.depths.mem_activeAt r.1 n).mp r.2⟩
      · intro r; cases r; rfl
      · intro r; cases r; rfl
    _ = Fintype.card (FP.activePresentation n).Relator := by
      exact (Fintype.card_congr (FP.activeRelatorEquiv n)).symm
    _ = Nat.card (FP.activePresentation n).Relator := by
      exact (Nat.card_eq_fintype_card).symm


/-- Convolution against a constant sequence is the constant times the active
relator count. -/
theorem depth_convolution_const
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (c n : ℕ) :
    FP.relatorDepthConvolution (fun _ => c) n = c * FP.activeRelatorCount n := by
  classical
  unfold relatorDepthConvolution
  have hfun : (fun q => if _h : q ≤ n then c else 0) =
      (fun q => c * (if _h : q ≤ n then 1 else 0)) := by
    funext q
    by_cases h : q ≤ n <;> simp [h]
  rw [hfun, FP.relator_weighted_left]
  change c * FP.relatorDepthConvolution (fun _ => 1) n = c * FP.activeRelatorCount n
  rw [FP.relator_convolution_const n]


/-- If no relator has certified depth at most `n`, the degree-`n` convolution
vanishes for any coefficient sequence. -/
theorem relator_convolution_forall
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) {n : ℕ}
    (h : ∀ r : FP.toPresentation.Relator, n < FP.depths.depth r) :
    FP.relatorDepthConvolution b n = 0 := by
  classical
  unfold relatorDepthConvolution relatorWeightedSum
  apply Finset.sum_eq_zero
  intro r hr
  have hnle : ¬ FP.depths.depth r ≤ n := Nat.not_le_of_gt (h r)
  simp [hnle]


/-- The degree-`n` convolution only depends on coefficients in degrees `≤ n`. -/
theorem convolution_congr_upto
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b c : ℕ → ℕ} {n : ℕ} (hbc : ∀ k, k ≤ n → b k = c k) :
    FP.relatorDepthConvolution b n = FP.relatorDepthConvolution c n := by
  classical
  unfold relatorDepthConvolution relatorWeightedSum
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hq : FP.depths.depth r ≤ n
  · have hsub : n - FP.depths.depth r ≤ n := Nat.sub_le _ _
    simp [hq, hbc (n - FP.depths.depth r) hsub]
  · simp [hq]


/-- Relator convolution is homogeneous in the coefficient sequence. -/
theorem relator_convolution_left
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (c : ℕ) (b : ℕ → ℕ) (n : ℕ) :
    FP.relatorDepthConvolution (fun k => c * b k) n =
      c * FP.relatorDepthConvolution b n := by
  classical
  unfold relatorDepthConvolution
  have hfun : (fun q => if _h : q ≤ n then c * b (n - q) else 0) =
      (fun q => c * (if _h : q ≤ n then b (n - q) else 0)) := by
    funext q
    by_cases h : q ≤ n <;> simp [h]
  rw [hfun, FP.relator_weighted_left]


/-- Coefficientwise GS-style inequality predicate for a sequence `b`: generator
shift is bounded by the current coefficient plus relator convolution.  This is a
lightweight algebraic wrapper; later exactness results will supply hypotheses of
this form. -/
def gsCoefficientInequality (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) : Prop :=
  FP.generatorShiftContribution b n ≤ b n + FP.relatorDepthConvolution b n

/-- Integer-valued coefficient balance for the GS recurrence.  Nonnegativity of
this number is exactly `gsCoefficientInequality`.  Using integers avoids
truncated subtraction when summing coefficients later. -/
noncomputable def gsCoefficientBalance (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) : ℤ :=
  (b n : ℤ) + (FP.relatorDepthConvolution b n : ℤ) -
    (FP.generatorShiftContribution b n : ℤ)

theorem inequality_balance_nonneg
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientInequality b n ↔ 0 ≤ FP.gsCoefficientBalance b n := by
  unfold gsCoefficientInequality gsCoefficientBalance
  omega

@[simp] theorem coefficient_balance_seq
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.gsCoefficientBalance (fun _ => 0) n = 0 := by
  unfold gsCoefficientBalance relatorDepthConvolution relatorWeightedSum
  simp [generatorShiftContribution]

/-- Successor form of the integer balance. -/
theorem gs_balance_succ
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance b (n + 1) =
      (b (n + 1) : ℤ) + (FP.relatorDepthConvolution b (n + 1) : ℤ) -
        (FP.generatorCount * b n : ℤ) := by
  simp [gsCoefficientBalance, shift_contribution_succ]


/-- Integer balances are homogeneous under scaling of the coefficient sequence. -/
theorem gs_coefficient_balance
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (c : ℕ) (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance (fun k => c * b k) n =
      (c : ℤ) * FP.gsCoefficientBalance b n := by
  unfold gsCoefficientBalance
  rw [FP.shift_contribution_left c b n,
    FP.relator_convolution_left c b n]
  push_cast
  ring


/-- Prefix sum of integer GS balances through degree `N`. -/
noncomputable def gsBalanceSum (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), FP.gsCoefficientBalance b n

/-- If all coefficient inequalities hold, every prefix balance sum is nonnegative. -/
theorem prefix_nonneg_inequalities
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} (h : ∀ n, FP.gsCoefficientInequality b n) (N : ℕ) :
    0 ≤ FP.gsBalanceSum b N := by
  unfold gsBalanceSum
  apply Finset.sum_nonneg
  intro n hn
  exact (FP.inequality_balance_nonneg b n).1 (h n)

@[simp] theorem balance_prefix_seq
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (N : ℕ) :
    FP.gsBalanceSum (fun _ => 0) N = 0 := by
  simp [gsBalanceSum]


/-- A single coefficient inequality is preserved by multiplying the sequence by a
constant. -/
theorem gs_inequality_left
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {n c : ℕ} (h : FP.gsCoefficientInequality b n) :
    FP.gsCoefficientInequality (fun k => c * b k) n := by
  unfold gsCoefficientInequality at h ⊢
  rw [FP.shift_contribution_left c b n,
    FP.relator_convolution_left c b n]
  have hh := Nat.mul_le_mul_left c h
  -- rearrange the multiplied right-hand side.
  simpa [Nat.mul_add] using hh


theorem gs_inequality_succ (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientInequality b (n + 1) ↔
      FP.generatorCount * b n ≤ b (n + 1) + FP.relatorDepthConvolution b (n + 1) := by
  simp [gsCoefficientInequality, shift_contribution_succ]


/-- A sequence satisfies the coefficientwise GS inequalities in every degree. -/
def gsCoefficientInequalities (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) : Prop :=
  ∀ n, FP.gsCoefficientInequality b n

/-- All-degree inequalities are equivalently nonnegativity of every integer balance. -/
theorem inequalities_balance_nonneg
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) :
    FP.gsCoefficientInequalities b ↔ ∀ n, 0 ≤ FP.gsCoefficientBalance b n := by
  simp [gsCoefficientInequalities, FP.inequality_balance_nonneg]

@[simp] theorem gs_coefficient_inequalities
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    FP.gsCoefficientInequalities (fun _ => 0) := by
  intro n
  simp [gsCoefficientInequality, generatorShiftContribution]

/-- All coefficient inequalities are preserved by multiplying the sequence by a constant. -/
theorem gs_inequalities_left
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} (c : ℕ) (h : FP.gsCoefficientInequalities b) :
    FP.gsCoefficientInequalities (fun k => c * b k) := by
  intro n
  exact FP.gs_inequality_left (c := c) (h n)

/-- It is enough to check the displayed successor recurrence and degree zero. -/
theorem gs_inequalities_succ
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) :
    FP.gsCoefficientInequalities b ↔
      FP.gsCoefficientInequality b 0 ∧
        ∀ n, FP.generatorCount * b n ≤
          b (n + 1) + FP.relatorDepthConvolution b (n + 1) := by
  constructor
  · intro h
    refine ⟨h 0, ?_⟩
    intro n
    exact (FP.gs_inequality_succ b n).mp (h (n + 1))
  · rintro ⟨h0, hs⟩ n
    cases n with
    | zero => exact h0
    | succ n => exact (FP.gs_inequality_succ b n).mpr (hs n)


/-- Histogram form of the relator-depth convolution. -/
theorem convolution_histogram_sum
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) :
    FP.relatorDepthConvolution b n =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.relatorDepthMultiplicity q * (if _h : q ≤ n then b (n - q) else 0) := by
  unfold relatorDepthConvolution
  exact FP.relator_weighted_histogram _

/-- Same convolution formula using the packaged exact-depth counts. -/
theorem convolution_exact_sum
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) :
    FP.relatorDepthConvolution b n =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.exactRelatorCount q * (if _h : q ≤ n then b (n - q) else 0) := by
  rw [FP.convolution_histogram_sum b n]
  apply Finset.sum_congr rfl
  intro q hq
  rw [FP.exact_count_multiplicity q]

@[simp] theorem relator_depth_convolution
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.relatorDepthConvolution (fun _ => 0) n = 0 := by
  unfold relatorDepthConvolution
  simp

theorem relator_convolution_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b c : ℕ → ℕ) (n : ℕ) :
    FP.relatorDepthConvolution (fun k => b k + c k) n =
      FP.relatorDepthConvolution b n + FP.relatorDepthConvolution c n := by
  unfold relatorDepthConvolution
  have hfun : (fun q => if _h : q ≤ n then b (n - q) + c (n - q) else 0) =
      (fun q => (if _h : q ≤ n then b (n - q) else 0) +
        (if _h : q ≤ n then c (n - q) else 0)) := by
    funext q
    by_cases h : q ≤ n <;> simp [h]
  rw [hfun, FP.relator_weighted_add]

/-- Integer balances are additive in the coefficient sequence. -/
theorem coefficient_balance_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b c : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance (fun k => b k + c k) n =
      FP.gsCoefficientBalance b n + FP.gsCoefficientBalance c n := by
  unfold gsCoefficientBalance
  rw [FP.shift_contribution_add b c n,
    FP.relator_convolution_add b c n]
  push_cast
  ring


/-- Integer prefix sum of a coefficient sequence through degree `N`. -/
noncomputable def coefficientPrefixInt (b : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (b n : ℤ)

/-- Integer prefix sum of relator convolutions through degree `N`. -/
noncomputable def convolutionPrefixInt (FP : FPres.{u} p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (FP.relatorDepthConvolution b n : ℤ)

/-- Expanded form of the prefix balance sum, with the generator-shift prefix reindexed. -/
theorem gs_balance_prefixes
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceSum b N =
      coefficientPrefixInt b N + FP.convolutionPrefixInt b N -
        (FP.generatorCount : ℤ) * (∑ k ∈ Finset.range N, (b k : ℤ)) := by
  classical
  unfold gsBalanceSum coefficientPrefixInt convolutionPrefixInt gsCoefficientBalance
  have hshiftNat := FP.sum_shift_contribution b N
  have hshift :
      (∑ n ∈ Finset.range (N + 1), (FP.generatorShiftContribution b n : ℤ)) =
        (FP.generatorCount : ℤ) * (∑ k ∈ Finset.range N, (b k : ℤ)) := by
    exact_mod_cast hshiftNat
  simp_rw [sub_eq_add_neg, add_assoc]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_neg_distrib]
  rw [hshift]


/-- Prefix balance sums are additive in the coefficient sequence. -/
theorem gs_balance_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b c : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceSum (fun k => b k + c k) N =
      FP.gsBalanceSum b N + FP.gsBalanceSum c N := by
  unfold gsBalanceSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact FP.coefficient_balance_add b c n

/-- Prefix balance sums are homogeneous in the coefficient sequence. -/
theorem gs_balance_left
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (c : ℕ) (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceSum (fun k => c * b k) N =
      (c : ℤ) * FP.gsBalanceSum b N := by
  unfold gsBalanceSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact FP.gs_coefficient_balance c b n


/-- A single GS coefficient inequality is closed under pointwise addition of sequences. -/
theorem gs_inequality_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b c : ℕ → ℕ} {n : ℕ}
    (hb : FP.gsCoefficientInequality b n) (hc : FP.gsCoefficientInequality c n) :
    FP.gsCoefficientInequality (fun k => b k + c k) n := by
  apply (FP.inequality_balance_nonneg (fun k => b k + c k) n).2
  rw [FP.coefficient_balance_add b c n]
  exact add_nonneg
    ((FP.inequality_balance_nonneg b n).1 hb)
    ((FP.inequality_balance_nonneg c n).1 hc)

/-- All-degree GS inequalities are closed under pointwise addition. -/
theorem gs_inequalities_add
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b c : ℕ → ℕ} (hb : FP.gsCoefficientInequalities b)
    (hc : FP.gsCoefficientInequalities c) :
    FP.gsCoefficientInequalities (fun k => b k + c k) := by
  intro n
  exact FP.gs_inequality_add (hb n) (hc n)


/-- Monotonicity of relator-depth convolution in the coefficient sequence. -/
theorem relator_convolution_mono
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    {b c : ℕ → ℕ} (hbc : ∀ k, b k ≤ c k) (n : ℕ) :
    FP.relatorDepthConvolution b n ≤ FP.relatorDepthConvolution c n := by
  rw [FP.convolution_histogram_sum b n,
    FP.convolution_histogram_sum c n]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hqle : q ≤ n
  · simp [hqle, Nat.mul_le_mul_left _ (hbc (n - q))]
  · simp [hqle]

/-- Relator convolution can equivalently be restricted to depths `≤ n`. -/
theorem relator_convolution_filter
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) :
    FP.relatorDepthConvolution b n =
      ∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q ≤ n),
        FP.relatorDepthMultiplicity q * b (n - q) := by
  rw [FP.convolution_histogram_sum b n]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : q ≤ n
  · simp [h]
  · simp [h]

/-- Range-sum form of the finite depth histogram total. -/
theorem sum_finsupp_relators
    (FP : FPres.{u} p) [Fintype FP.toPresentation.Relator] :
    (∑ n ∈ Finset.range (FP.maxRelatorDepth + 1), FP.relatorDepthFinsupp n) =
      Nat.card FP.toPresentation.Relator := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => FP.relatorDepthFinsupp n)
    (FP.maxRelatorDepth + 1)]
  simpa using FP.depth_multiplicity_relators

@[simp] theorem activePresentation_gen (FP : FPres.{u} p) (n : ℕ) :
    (FP.activePresentation n).Gen = FP.Gen := rfl

/-- The active subpresentation as a filtered presentation, inheriting the original
certified depths. -/
noncomputable def activeFilteredPresentation (FP : FPres.{u} p) (n : ℕ) :
    FPres p where
  toPresentation := FP.activePresentation n
  depths :=
    { depth := fun r =>
        FP.depths.depth ⟨r.1, Classical.choose r.2⟩
      mem_depth := by
        intro r
        exact FP.depths.mem_depth ⟨r.1, Classical.choose r.2⟩ }

/-- Every relator in the active filtered presentation has inherited depth at most
its cutoff. -/
theorem active_filtered_presentation
    (FP : FPres.{u} p) (n : ℕ)
    (r : (FP.activeFilteredPresentation n).toPresentation.Relator) :
    (FP.activeFilteredPresentation n).depths.depth r ≤ n := by
  dsimp [activeFilteredPresentation]
  exact Classical.choose_spec r.2

/-- The canonical morphism from the active subpresentation to the full presentation. -/
def activeOriginalHom (FP : FPres.{u} p) (n : ℕ) :
    Presentation.Hom (FP.activePresentation n) FP.toPresentation :=
  Presentation.relatorsOriginalHom FP.toPresentation
    (FP.active_subset_rels n)

@[simp] theorem active_original_gen (FP : FPres.{u} p) (n : ℕ)
    (x : FP.Gen) : (FP.activeOriginalHom n).gen x = x := rfl

/-- The active-to-full presentation map is surjective on presented groups. -/
theorem original_hom_surjective (FP : FPres.{u} p) (n : ℕ) :
    Function.Surjective (FP.activeOriginalHom n).toGroupHom :=
  (FP.activeOriginalHom n).group_surjective_gen (by
    intro x
    exact ⟨x, rfl⟩)

/-- The induced map from an active cutoff to the original presentation on quotients
by presented Zassenhaus images. -/
noncomputable def activeOriginalQuotient
    (FP : FPres.{u} p) (n k : ℕ) :
    ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) k) →*
      (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation k) :=
  (FP.activeOriginalHom n).zass_image_quotmap (p := p) k

@[simp] theorem active_original_mk
    (FP : FPres.{u} p) (n k : ℕ)
    (x : (FP.activePresentation n).Group) :
    FP.activeOriginalQuotient n k
        (QuotientGroup.mk' (Presentation.zassenhausImage p (FP.activePresentation n) k) x) =
      QuotientGroup.mk' (Presentation.zassenhausImage p FP.toPresentation k)
        ((FP.activeOriginalHom n).toGroupHom x) := rfl

/-- Active-to-original maps remain surjective after quotienting by any presented
Zassenhaus image. -/
theorem active_original_surjective
    (FP : FPres.{u} p) (n k : ℕ) :
    Function.Surjective (FP.activeOriginalQuotient n k) :=
  (FP.activeOriginalHom n).zass_imagequot_mapsurj (p := p) k
    (FP.original_hom_surjective n)

/-- Active-to-original maps carry each presented Zassenhaus image onto the
corresponding image in the original presentation. -/
theorem original_hom_image
    (FP : FPres.{u} p) (n k : ℕ) :
    (Presentation.zassenhausImage p (FP.activePresentation n) k).map
        (FP.activeOriginalHom n).toGroupHom =
      Presentation.zassenhausImage p FP.toPresentation k := by
  apply le_antisymm
  · exact (FP.activeOriginalHom n).map_zass_imagele (p := p) k
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(FP.activePresentation n).quotientMap w, ?_, ?_⟩
    · exact Presentation.zassenhaus_image p (FP.activePresentation n) hw
    · change FP.toPresentation.quotientMap (FreeGroup.map id w) =
          FP.toPresentation.quotientMap w
      rw [FreeGroup.map.id]

/-- The active filtered presentation maps canonically to the original filtered presentation. -/
def activeFilteredOriginal (FP : FPres.{u} p) (n : ℕ) :
    Hom (FP.activeFilteredPresentation n) FP :=
  FP.activeOriginalHom n

@[simp] theorem filtered_original_gen (FP : FPres.{u} p)
    (n : ℕ) (x : FP.Gen) :
    (FP.activeFilteredOriginal n).gen x = x := rfl

/-- Increasing the cutoff gives a quotient morphism between active subpresentations. -/
def activeMonoHom (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Presentation.Hom (FP.activePresentation m) (FP.activePresentation n) :=
  Presentation.relatorsMonoHom FP.toPresentation (FP.active_set_mono hmn)

@[simp] theorem active_mono_gen (FP : FPres.{u} p) {m n : ℕ}
    (hmn : m ≤ n) (x : FP.Gen) : (FP.activeMonoHom hmn).gen x = x := rfl

/-- Include an exact-depth subpresentation into a later active cutoff. -/
def exactActiveHom (FP : FPres.{u} p) {k n : ℕ} (hkn : k ≤ n) :
    Presentation.Hom (FP.exactPresentation k) (FP.activePresentation n) :=
  Presentation.relatorsMonoHom FP.toPresentation
    (FP.exact_subset_active hkn)

@[simp] theorem exact_active_gen (FP : FPres.{u} p) {k n : ℕ}
    (hkn : k ≤ n) (x : FP.Gen) : (FP.exactActiveHom hkn).gen x = x := rfl

/-- Include an exact-depth subpresentation into the original presentation. -/
def exactOriginalHom (FP : FPres.{u} p) (k : ℕ) :
    Presentation.Hom (FP.exactPresentation k) FP.toPresentation :=
  Presentation.relatorsOriginalHom FP.toPresentation
    (FP.exact_subset_rels k)

@[simp] theorem exact_original_gen (FP : FPres.{u} p) (k : ℕ)
    (x : FP.Gen) : (FP.exactOriginalHom k).gen x = x := rfl

/-- Exact-to-original factors through any active cutoff containing that slice. -/
@[simp] theorem active_original_exact
    (FP : FPres.{u} p) {k n : ℕ} (hkn : k ≤ n) :
    (FP.activeOriginalHom n).comp (FP.exactActiveHom hkn) =
      FP.exactOriginalHom k := by
  ext x
  rfl

/-- Exact-to-active maps are compatible with increasing the active cutoff. -/
@[simp] theorem active_mono_exact
    (FP : FPres.{u} p) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (FP.activeMonoHom hmn).comp (FP.exactActiveHom hkm) =
      FP.exactActiveHom (Nat.le_trans hkm hmn) := by
  ext x
  rfl

/-- Exact-to-active maps are surjective on presented groups (same generators). -/
theorem exact_active_surjective (FP : FPres.{u} p) {k n : ℕ}
    (hkn : k ≤ n) : Function.Surjective (FP.exactActiveHom hkn).toGroupHom :=
  (FP.exactActiveHom hkn).group_surjective_gen (by
    intro x
    exact ⟨x, rfl⟩)

/-- Cutoff-increase maps between active presentations are surjective on groups. -/
theorem mono_hom_surjective (FP : FPres.{u} p) {m n : ℕ}
    (hmn : m ≤ n) : Function.Surjective (FP.activeMonoHom hmn).toGroupHom :=
  (FP.activeMonoHom hmn).group_surjective_gen (by
    intro x
    exact ⟨x, rfl⟩)

/-- The induced map on quotients of active presentations by presented Zassenhaus images. -/
noncomputable def activeMonoQuotient
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) k) →*
      ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) k) :=
  (FP.activeMonoHom hmn).zass_image_quotmap (p := p) k

@[simp] theorem active_mono_mk
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (k : ℕ)
    (x : (FP.activePresentation m).Group) :
    FP.activeMonoQuotient hmn k
        (QuotientGroup.mk' (Presentation.zassenhausImage p (FP.activePresentation m) k) x) =
      QuotientGroup.mk' (Presentation.zassenhausImage p (FP.activePresentation n) k)
        ((FP.activeMonoHom hmn).toGroupHom x) := rfl

/-- The active cutoff maps remain surjective after quotienting by any presented
Zassenhaus image. -/
theorem active_mono_surjective
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    Function.Surjective (FP.activeMonoQuotient hmn k) :=
  (FP.activeMonoHom hmn).zass_imagequot_mapsurj (p := p) k
    (FP.mono_hom_surjective hmn)

/-- For cutoff-increase maps, the presented Zassenhaus image is mapped onto the
corresponding image in the larger active presentation. -/
theorem mono_hom_image
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    (Presentation.zassenhausImage p (FP.activePresentation m) k).map
        (FP.activeMonoHom hmn).toGroupHom =
      Presentation.zassenhausImage p (FP.activePresentation n) k := by
  apply le_antisymm
  · exact (FP.activeMonoHom hmn).map_zass_imagele (p := p) k
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(FP.activePresentation m).quotientMap w, ?_, ?_⟩
    · exact Presentation.zassenhaus_image p (FP.activePresentation m) hw
    · change (FP.activePresentation n).quotientMap (FreeGroup.map id w) =
          (FP.activePresentation n).quotientMap w
      rw [FreeGroup.map.id]

/-- Increasing the cutoff gives a morphism between active filtered presentations. -/
def activeFilteredMono (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Hom (FP.activeFilteredPresentation m) (FP.activeFilteredPresentation n) :=
  FP.activeMonoHom hmn

@[simp] theorem filtered_mono_gen (FP : FPres.{u} p)
    {m n : ℕ} (hmn : m ≤ n) (x : FP.Gen) :
    (FP.activeFilteredMono hmn).gen x = x := rfl

@[simp] theorem filtered_original_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    (FP.activeFilteredOriginal n).comp (FP.activeFilteredMono hmn) =
      FP.activeFilteredOriginal m := by
  ext x
  rfl

@[simp] theorem original_hom_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    (FP.activeOriginalHom n).comp (FP.activeMonoHom hmn) =
      FP.activeOriginalHom m := by
  ext x
  rfl

/-- Quotient maps between active cutoffs compose compatibly with the map to the
original presentation. -/
@[simp] theorem active_original_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    (FP.activeOriginalQuotient n k).comp
        (FP.activeMonoQuotient hmn k) =
      FP.activeOriginalQuotient m k := by
  dsimp [activeOriginalQuotient,
    activeMonoQuotient]
  rw [← Presentation.Hom.zass_imagequot_mapcomp]
  simp

/-- Quotient maps for successive active cutoff increases compose transitively. -/
@[simp] theorem active_mono_comp
    (FP : FPres.{u} p) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (k : ℕ) :
    (FP.activeMonoQuotient hmn k).comp
        (FP.activeMonoQuotient hlm k) =
      FP.activeMonoQuotient (Nat.le_trans hlm hmn) k := by
  dsimp [activeMonoQuotient]
  rw [← Presentation.Hom.zass_imagequot_mapcomp]
  congr 1

/-- Kernel of the map between active subpresentations when the cutoff increases. -/
theorem ker_active_hom (FP : FPres.{u} p) {m n : ℕ}
    (hmn : m ≤ n) :
    MonoidHom.ker (FP.activeMonoHom hmn).toGroupHom =
      Subgroup.normalClosure
        ((FP.activePresentation m).quotientMap '' FP.activeRelatorSet n) :=
  Presentation.relators_mono FP.toPresentation
    (FP.active_set_mono hmn)

/-- For an arbitrary cutoff increase, the kernel is normally generated by the
exact-depth slices with depths in `(m,n]`. -/
theorem mono_exact_ioc (FP : FPres.{u} p)
    {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (FP.activeMonoHom hmn).toGroupHom =
      Subgroup.normalClosure
        ((FP.activePresentation m).quotientMap ''
          (⋃ i : {i : ℕ // m < i ∧ i ≤ n}, FP.exactRelatorSet i.1)) := by
  classical
  rw [FP.ker_active_hom hmn]
  rw [FP.union_ioc_exact hmn]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · rw [Presentation.quotient_rel_one]
      · exact Subgroup.one_mem _
      · simpa [activePresentation] using hw
    · exact Subgroup.subset_normalClosure ⟨w, hw, rfl⟩
  · apply Subgroup.normalClosure_mono
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    exact ⟨w, Or.inr hw, rfl⟩

/-- For a single cutoff step, the kernel is normally generated by the newly
appearing exact-depth relators. -/
theorem ker_mono_exact (FP : FPres.{u} p) (n : ℕ) :
    MonoidHom.ker (FP.activeMonoHom (Nat.le_succ n)).toGroupHom =
      Subgroup.normalClosure
        ((FP.activePresentation n).quotientMap '' FP.exactRelatorSet (n + 1)) := by
  classical
  rw [FP.ker_active_hom (Nat.le_succ n)]
  rw [FP.active_union_exact n]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · -- old active relators are already trivial in the source active presentation
      rw [Presentation.quotient_rel_one]
      · exact Subgroup.one_mem _
      · simpa [activePresentation] using hw
    · exact Subgroup.subset_normalClosure ⟨w, hw, rfl⟩
  · apply Subgroup.normalClosure_mono
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    exact ⟨w, Or.inr hw, rfl⟩

/-- The normal subgroup generated in an active presentation by an exact-depth
slice lies in the corresponding presented Zassenhaus image. -/
theorem normal_exact_set
    (FP : FPres.{u} p) (m k : ℕ) :
    Subgroup.normalClosure
        ((FP.activePresentation m).quotientMap '' FP.exactRelatorSet k) ≤
      Presentation.zassenhausImage p (FP.activePresentation m) k := by
  classical
  let D := GroupAlgebra.zSubgro p FP.Free k
  let qmap := (FP.activePresentation m).quotientMap
  change Subgroup.normalClosure (qmap '' FP.exactRelatorSet k) ≤ D.map qmap
  haveI : D.Normal := GroupAlgebra.zassenhausSubgroup_normal p FP.Free k
  haveI : (D.map qmap).Normal :=
    (show D.Normal from inferInstance).map qmap
      (FP.activePresentation m).quotientMap_surjective
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rcases hy with ⟨r, hr, rfl⟩
  rcases hr with ⟨hrel, hdepth⟩
  have hmem : r ∈ D :=
    GroupAlgebra.depth_least p FP.Free (le_of_eq hdepth.symm)
      (FP.depths.mem_depth ⟨r, hrel⟩)
  exact Subgroup.mem_map.mpr ⟨r, hmem, rfl⟩

/-- For a successor cutoff, the exact-generator description immediately places
the kernel in the matching presented Zassenhaus image. -/
theorem mono_presented_exact
    (FP : FPres.{u} p) (n : ℕ) :
    MonoidHom.ker (FP.activeMonoHom (Nat.le_succ n)).toGroupHom ≤
      Presentation.zassenhausImage p (FP.activePresentation n) (n + 1) := by
  rw [FP.ker_mono_exact n]
  exact FP.normal_exact_set n (n + 1)

/-- The kernel of the cutoff-increase map is generated by relators of depth at
least `m+1` (modulo those already active at `m`). -/
theorem ker_mono_left
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (FP.activeMonoHom hmn).toGroupHom ≤
      (GroupAlgebra.zSubgro p FP.Free (m + 1)).map
        (FP.activePresentation m).quotientMap := by
  classical
  rw [FP.ker_active_hom hmn]
  let D := GroupAlgebra.zSubgro p FP.Free (m + 1)
  let qmap := (FP.activePresentation m).quotientMap
  haveI : D.Normal := GroupAlgebra.zassenhausSubgroup_normal p FP.Free (m + 1)
  haveI : (D.map qmap).Normal :=
    (show D.Normal from inferInstance).map qmap
      (FP.activePresentation m).quotientMap_surjective
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rcases hy with ⟨r, hrn, rfl⟩
  by_cases hrm : r ∈ FP.activeRelatorSet m
  · change qmap r ∈ D.map qmap
    have hq : qmap r = 1 :=
      (FP.activePresentation m).quotient_rel_one hrm
    rw [hq]
    exact (D.map qmap).one_mem
  · rcases hrn with ⟨hr, _hdn⟩
    have hnotle : ¬ FP.depths.depth ⟨r, hr⟩ ≤ m := by
      intro hd
      exact hrm ⟨hr, hd⟩
    have hge : m + 1 ≤ FP.depths.depth ⟨r, hr⟩ := by omega
    have hmem : r ∈ D :=
      GroupAlgebra.depth_least p FP.Free hge
        (FP.depths.mem_depth ⟨r, hr⟩)
    exact Subgroup.mem_map.mpr ⟨r, hmem, rfl⟩

/-- Same kernel bound, using the named presented-group Zassenhaus image. -/
theorem active_mono_presented
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    MonoidHom.ker (FP.activeMonoHom hmn).toGroupHom ≤
      Presentation.zassenhausImage p (FP.activePresentation m) (m + 1) := by
  simpa [Presentation.zassenhausImage] using
    FP.ker_mono_left hmn

/-- A cutoff-increase kernel is contained in any earlier presented Zassenhaus image. -/
theorem ker_active_mono
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    MonoidHom.ker (FP.activeMonoHom hmn).toGroupHom ≤
      Presentation.zassenhausImage p (FP.activePresentation m) (i + 1) := by
  exact le_trans (FP.active_mono_presented hmn)
    (Presentation.zassenhausImage_antitone p (FP.activePresentation m)
      (Nat.succ_le_succ hi))

/-- More generally, cutoff-increase maps are injective on quotients by any earlier
presented Zassenhaus image. -/
theorem active_mono_injective
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    Function.Injective (FP.activeMonoQuotient hmn (i + 1)) := by
  apply Presentation.Hom.zassimage_quotmap_injcomaple
  apply Presentation.Hom.comapzass_imageleker_lemapeq
  · exact FP.ker_active_mono hmn hi
  · exact FP.mono_hom_image hmn (i + 1)

/-- Hence cutoff-increase maps are bijective on earlier presented-image quotients. -/
theorem active_mono_bijective
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    Function.Bijective (FP.activeMonoQuotient hmn (i + 1)) :=
  ⟨FP.active_mono_injective hmn hi,
    FP.active_mono_surjective hmn (i + 1)⟩

/-- Multiplicative equivalence on any presented-image quotient whose index is at
most the smaller active cutoff.  This is the uniform version of the critical
`m + 1` equivalence below. -/
noncomputable def activeMonoLeft
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) ≃*
      ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :=
  MulEquiv.ofBijective (FP.activeMonoQuotient hmn (i + 1))
    (FP.active_mono_bijective hmn hi)

@[simp] theorem mono_image_left
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    FP.activeMonoLeft hmn hi x =
      FP.activeMonoQuotient hmn (i + 1) x := rfl

@[simp] theorem active_mono_monoid
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    (FP.activeMonoLeft hmn hi).toMonoidHom =
      FP.activeMonoQuotient hmn (i + 1) := rfl

@[simp] theorem active_image_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    (FP.activeMonoLeft hmn hi).symm
        (FP.activeMonoQuotient hmn (i + 1) x) = x := by
  exact (FP.activeMonoLeft hmn hi).left_inv x

@[simp] theorem mono_left_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (y : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :
    FP.activeMonoQuotient hmn (i + 1)
        ((FP.activeMonoLeft hmn hi).symm y) = y := by
  change FP.activeMonoLeft hmn hi
      ((FP.activeMonoLeft hmn hi).symm y) = y
  exact (FP.activeMonoLeft hmn hi).right_inv y

/-- Equality to an active cutoff-increase quotient map, rewritten through the inverse
of the cutoff equivalence. -/
theorem active_mono_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1))
    (y : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :
    FP.activeMonoQuotient hmn (i + 1) x = y ↔
      x = (FP.activeMonoLeft hmn hi).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.active_image_symm hmn hi x).symm
  · intro h
    rw [h]
    exact FP.mono_left_symm hmn hi y

/-- Cardinality invariance for earlier presented-image quotients along active cutoff
increases. -/
theorem nat_active_mono
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    Nat.card ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) =
      Nat.card ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :=
  Nat.card_congr (FP.activeMonoLeft hmn hi).toEquiv

/-- At the next Zassenhaus level, increasing the active cutoff induces an injective
map on presented-image quotients: the newly added relators are already killed by
`D_{m+1}`. -/
theorem mono_succ_left
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (FP.activeMonoQuotient hmn (m + 1)) := by
  apply Presentation.Hom.zassimage_quotmap_injcomaple
  apply Presentation.Hom.comapzass_imageleker_lemapeq
  · exact FP.active_mono_presented hmn
  · exact FP.mono_hom_image hmn (m + 1)

/-- Consequently the next-level quotient map for an active cutoff increase is bijective. -/
theorem mono_image_bijective
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (FP.activeMonoQuotient hmn (m + 1)) :=
  ⟨FP.mono_succ_left hmn,
    FP.active_mono_surjective hmn (m + 1)⟩

/-- Multiplicative equivalence on next-level presented-image quotients induced by
increasing an active cutoff. -/
noncomputable def activeMonoSucc
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (m + 1)) ≃*
      ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (m + 1)) :=
  MulEquiv.ofBijective (FP.activeMonoQuotient hmn (m + 1))
    (FP.mono_image_bijective hmn)

@[simp] theorem active_image_left
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (m + 1)) :
    FP.activeMonoSucc hmn x =
      FP.activeMonoQuotient hmn (m + 1) x := rfl

@[simp] theorem active_mono_hom
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    (FP.activeMonoSucc hmn).toMonoidHom =
      FP.activeMonoQuotient hmn (m + 1) := rfl

@[simp] theorem mono_succ_symm
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (m + 1)) :
    (FP.activeMonoSucc hmn).symm
        (FP.activeMonoQuotient hmn (m + 1) x) = x := by
  exact (FP.activeMonoSucc hmn).left_inv x

@[simp] theorem active_mono_succ
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (y : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (m + 1)) :
    FP.activeMonoQuotient hmn (m + 1)
        ((FP.activeMonoSucc hmn).symm y) = y := by
  change FP.activeMonoSucc hmn
      ((FP.activeMonoSucc hmn).symm y) = y
  exact (FP.activeMonoSucc hmn).right_inv y

/-- Equality to the critical active cutoff quotient map, rewritten through its inverse. -/
theorem active_mono_image
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (m + 1))
    (y : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (m + 1)) :
    FP.activeMonoQuotient hmn (m + 1) x = y ↔
      x = (FP.activeMonoSucc hmn).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.mono_succ_symm hmn x).symm
  · intro h
    rw [h]
    exact FP.active_mono_succ hmn y

/-- Cardinality invariance for next-level active cutoff quotients. -/
theorem nat_mono_image
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Nat.card ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (m + 1)) =
      Nat.card ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (m + 1)) :=
  Nat.card_congr (FP.activeMonoSucc hmn).toEquiv

theorem ker_active_original (FP : FPres.{u} p) (n : ℕ) :
    MonoidHom.ker (FP.activeOriginalHom n).toGroupHom =
      Subgroup.normalClosure
        ((FP.activePresentation n).quotientMap '' FP.toPresentation.rels) :=
  Presentation.relators_mono FP.toPresentation
    (FP.active_subset_rels n)

/-- The kernel of the map from the cutoff-`n` active presentation to the full
presentation is generated by relators of depth at least `n+1`, hence lies in the
image of the `(n+1)`st Zassenhaus term of the ambient free group. -/
theorem ker_original_succ
    (FP : FPres.{u} p) (n : ℕ) :
    MonoidHom.ker (FP.activeOriginalHom n).toGroupHom ≤
      (GroupAlgebra.zSubgro p FP.Free (n + 1)).map
        (FP.activePresentation n).quotientMap := by
  classical
  rw [FP.ker_active_original n]
  let D := GroupAlgebra.zSubgro p FP.Free (n + 1)
  let qmap := (FP.activePresentation n).quotientMap
  haveI : D.Normal := GroupAlgebra.zassenhausSubgroup_normal p FP.Free (n + 1)
  haveI : (D.map qmap).Normal :=
    (show D.Normal from inferInstance).map qmap
      (FP.activePresentation n).quotientMap_surjective
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rcases hy with ⟨r, hr, rfl⟩
  by_cases hact : r ∈ FP.activeRelatorSet n
  · change qmap r ∈ D.map qmap
    have hrel : r ∈ (FP.activePresentation n).rels := hact
    have hq : qmap r = 1 :=
      (FP.activePresentation n).quotient_rel_one hrel
    rw [hq]
    exact (D.map qmap).one_mem
  · have hnotle : ¬ FP.depths.depth ⟨r, hr⟩ ≤ n := by
      intro hd
      exact hact ⟨hr, hd⟩
    have hge : n + 1 ≤ FP.depths.depth ⟨r, hr⟩ := by omega
    have hmem : r ∈ D :=
      GroupAlgebra.depth_least p FP.Free hge
        (FP.depths.mem_depth ⟨r, hr⟩)
    exact Subgroup.mem_map.mpr ⟨r, hmem, rfl⟩


/-- Same active-to-full kernel bound, using the named presented-group Zassenhaus image. -/
theorem original_presented_succ
    (FP : FPres.{u} p) (n : ℕ) :
    MonoidHom.ker (FP.activeOriginalHom n).toGroupHom ≤
      Presentation.zassenhausImage p (FP.activePresentation n) (n + 1) := by
  simpa [Presentation.zassenhausImage] using
    FP.ker_original_succ n

/-- The active-to-original kernel is contained in any earlier presented Zassenhaus image. -/
theorem original_presented_image
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    MonoidHom.ker (FP.activeOriginalHom n).toGroupHom ≤
      Presentation.zassenhausImage p (FP.activePresentation n) (i + 1) := by
  exact le_trans (FP.original_presented_succ n)
    (Presentation.zassenhausImage_antitone p (FP.activePresentation n)
      (Nat.succ_le_succ hi))

/-- Active-to-original maps are injective on quotients by any earlier presented image. -/
theorem active_original_injective
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    Function.Injective (FP.activeOriginalQuotient n (i + 1)) := by
  apply Presentation.Hom.zassimage_quotmap_injcomaple
  apply Presentation.Hom.comapzass_imageleker_lemapeq
  · exact FP.original_presented_image hi
  · exact FP.original_hom_image n (i + 1)

/-- Active-to-original maps are bijective on quotients by any earlier presented image. -/
theorem active_original_bijective
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    Function.Bijective (FP.activeOriginalQuotient n (i + 1)) :=
  ⟨FP.active_original_injective hi,
    FP.active_original_surjective n (i + 1)⟩

/-- Multiplicative equivalence between an active cutoff and the original presentation
on every presented-image quotient up to the cutoff. -/
noncomputable def activeOriginalImage
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) ≃*
      (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (i + 1)) :=
  MulEquiv.ofBijective (FP.activeOriginalQuotient n (i + 1))
    (FP.active_original_bijective hi)

@[simp] theorem active_original_equiv
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :
    FP.activeOriginalImage hi x =
      FP.activeOriginalQuotient n (i + 1) x := rfl

@[simp] theorem active_original_monoid
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    (FP.activeOriginalImage hi).toMonoidHom =
      FP.activeOriginalQuotient n (i + 1) := rfl

@[simp] theorem active_original_image
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :
    (FP.activeOriginalImage hi).symm
        (FP.activeOriginalQuotient n (i + 1) x) = x := by
  exact (FP.activeOriginalImage hi).left_inv x

@[simp] theorem original_zassenhaus_symm
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (y : FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (i + 1)) :
    FP.activeOriginalQuotient n (i + 1)
        ((FP.activeOriginalImage hi).symm y) = y := by
  change FP.activeOriginalImage hi
      ((FP.activeOriginalImage hi).symm y) = y
  exact (FP.activeOriginalImage hi).right_inv y

/-- Equality to an active-to-original quotient map, rewritten through the inverse equivalence. -/
theorem active_original_symm
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1))
    (y : FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (i + 1)) :
    FP.activeOriginalQuotient n (i + 1) x = y ↔
      x = (FP.activeOriginalImage hi).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.active_original_image hi x).symm
  · intro h
    rw [h]
    exact FP.original_zassenhaus_symm hi y

/-- Cardinality invariance for earlier presented-image quotients from an active cutoff
 to the original presentation. -/
theorem nat_active_original
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    Nat.card ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) =
      Nat.card (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (i + 1)) :=
  Nat.card_congr (FP.activeOriginalImage hi).toEquiv

/-- Once two active cutoffs are at least `i`, their `(i+1)` presented-image
quotients are canonically equivalent via the original presentation. -/
noncomputable def activeImageEquiv
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n) :
    ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) ≃*
      ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :=
  (FP.activeOriginalImage hm).trans
    (FP.activeOriginalImage hn).symm

/-- Stable cardinality of presented-image quotients: any two sufficiently large
active cutoffs give equal cardinalities at a fixed level. -/
theorem nat_active_image
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n) :
    Nat.card ((FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) =
      Nat.card ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (i + 1)) :=
  Nat.card_congr (FP.activeImageEquiv hm hn).toEquiv

/-- The stable quotient equivalence is characterized by commuting with the maps to
 the original presentation. -/
theorem active_image_original
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    FP.activeOriginalImage hn
        (FP.activeImageEquiv hm hn x) =
      FP.activeOriginalImage hm x := by
  dsimp [activeImageEquiv, MulEquiv.trans]
  exact MulEquiv.apply_symm_apply
    (FP.activeOriginalImage hn)
    (FP.activeOriginalImage hm x)

/-- Stable quotient equivalences compose transitively. -/
theorem active_zassenhaus_trans
    (FP : FPres.{u} p) {i m n k : ℕ}
    (hm : i ≤ m) (hn : i ≤ n) (hk : i ≤ k)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    FP.activeImageEquiv hn hk
        (FP.activeImageEquiv hm hn x) =
      FP.activeImageEquiv hm hk x := by
  apply (FP.activeOriginalImage hk).injective
  rw [FP.active_image_original hn hk]
  rw [FP.active_image_original hm hn]
  rw [FP.active_image_original hm hk]

/-- The stable quotient equivalence from a cutoff to itself is the identity. -/
@[simp] theorem active_image_self
    (FP : FPres.{u} p) {i m : ℕ} (hm : i ≤ m)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    FP.activeImageEquiv hm hm x = x := by
  apply (FP.activeOriginalImage hm).injective
  rw [FP.active_image_original hm hm]

/-- For nested cutoffs, the stable quotient equivalence agrees with the direct
monotone-cutoff equivalence. -/
theorem active_image_mono
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : (FP.activePresentation m).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation m) (i + 1)) :
    FP.activeImageEquiv hi (Nat.le_trans hi hmn) x =
      FP.activeMonoLeft hmn hi x := by
  apply (FP.activeOriginalImage
    (Nat.le_trans hi hmn)).injective
  rw [FP.active_image_original hi (Nat.le_trans hi hmn)]
  simp only [mono_image_left,
    active_original_equiv]
  have hcomp := FP.active_original_mono hmn (i + 1)
  have h := DFunLike.congr_fun hcomp x
  simpa only [MonoidHom.comp_apply] using h.symm

/-- The active-to-original map is injective on the quotient by the next presented
Zassenhaus image. -/
theorem active_original_succ
    (FP : FPres.{u} p) (n : ℕ) :
    Function.Injective (FP.activeOriginalQuotient n (n + 1)) := by
  apply Presentation.Hom.zassimage_quotmap_injcomaple
  apply Presentation.Hom.comapzass_imageleker_lemapeq
  · exact FP.original_presented_succ n
  · exact FP.original_hom_image n (n + 1)

/-- Thus the cutoff-`n` active presentation has the same next presented-image
Zassenhaus quotient as the full presentation. -/
theorem original_bijective_succ
    (FP : FPres.{u} p) (n : ℕ) :
    Function.Bijective (FP.activeOriginalQuotient n (n + 1)) :=
  ⟨FP.active_original_succ n,
    FP.active_original_surjective n (n + 1)⟩

/-- Multiplicative equivalence between the cutoff-`n` active next quotient and the
full presentation's corresponding presented-image quotient. -/
noncomputable def activeOriginalSucc
    (FP : FPres.{u} p) (n : ℕ) :
    ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (n + 1)) ≃*
      (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (n + 1)) :=
  MulEquiv.ofBijective (FP.activeOriginalQuotient n (n + 1))
    (FP.original_bijective_succ n)

@[simp] theorem original_image_succ
    (FP : FPres.{u} p) (n : ℕ)
    (x : (FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (n + 1)) :
    FP.activeOriginalSucc n x =
      FP.activeOriginalQuotient n (n + 1) x := rfl

/-- Cardinality invariance between an active cutoff and the full presentation at the
next presented-image Zassenhaus quotient. -/
theorem nat_original_succ
    (FP : FPres.{u} p) (n : ℕ) :
    Nat.card ((FP.activePresentation n).Group ⧸
        Presentation.zassenhausImage p (FP.activePresentation n) (n + 1)) =
      Nat.card (FP.Group ⧸ Presentation.zassenhausImage p FP.toPresentation (n + 1)) :=
  Nat.card_congr (FP.activeOriginalSucc n).toEquiv

/-- The larger active presentation is obtained from a smaller one by adding the
larger active relator set (the union simplifies by monotonicity). -/
theorem active_presentation_relators (FP : FPres.{u} p)
    {m n : ℕ} (hmn : m ≤ n) :
    (FP.activePresentation m).addRelators (FP.activeRelatorSet n) =
      FP.activePresentation n := by
  dsimp [activePresentation]
  congr 1
  exact Set.union_eq_right.mpr (FP.active_set_mono hmn)

/-- A successor active presentation is obtained by adding just the exact next slice. -/
theorem active_presentation_succ
    (FP : FPres.{u} p) (n : ℕ) :
    (FP.activePresentation n).addRelators (FP.exactRelatorSet (n + 1)) =
      FP.activePresentation (n + 1) := by
  dsimp [activePresentation, Presentation.addRelators]
  congr 1
  exact (FP.active_union_exact n).symm

/-- More generally, adding the union of exact slices in `(m,n]` to cutoff `m`
recovers cutoff `n`. -/
theorem active_presentation_ioc
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    (FP.activePresentation m).addRelators
        (⋃ i : {i : ℕ // m < i ∧ i ≤ n}, FP.exactRelatorSet i.1) =
      FP.activePresentation n := by
  dsimp [activePresentation, Presentation.addRelators]
  congr 1
  exact (FP.union_ioc_exact hmn).symm

/-- The trivial filtered presentation attached to any presentation. -/
def ofPresentation (p : ℕ) (P : Presentation.{u}) : FPres p where
  toPresentation := P
  depths := Presentation.RDepths.trivial (p := p) (P := P)

/-- Add extra relators to a filtered presentation, with explicit certified depths
for the new relators.  On relators already present in the old presentation we
keep the old depth certificate; on genuinely new relators we use the supplied
certificate.  If a word lies in both sets, the old certificate is chosen. -/
noncomputable def addRelators (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s)) :
    FPres p := by
  classical
  refine
    { toPresentation := FP.toPresentation.addRelators S
      depths := ?_ }
  refine
    { depth := fun r =>
        if h : (r.1 : FP.Free) ∈ FP.toPresentation.rels then
          FP.depths.depth ⟨r.1, h⟩
        else
          depthS ⟨r.1, ?_⟩
      mem_depth := ?_ }
  · have hr := r.property
    rcases hr with hr | hr
    · contradiction
    · exact hr
  · intro r
    change GroupAlgebra.zassenhausDepthLeast p FP.Free r.1
      (if h : (r.1 : FP.Free) ∈ FP.toPresentation.rels then
        FP.depths.depth ⟨r.1, h⟩
      else
        depthS ⟨r.1, by
          have hr := r.property
          rcases hr with hr | hr
          · contradiction
          · exact hr⟩)
    by_cases h : (r.1 : FP.Free) ∈ FP.toPresentation.rels
    · rw [dif_pos h]
      exact FP.depths.mem_depth ⟨r.1, h⟩
    · rw [dif_neg h]
      exact memS ⟨r.1, by
        have hr := r.property
        rcases hr with hr | hr
        · contradiction
        · exact hr⟩

/-- The canonical underlying morphism from a filtered presentation to its
extra-relator extension. -/
def addRelatorsHom (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s)) :
    Hom FP (addRelators FP S depthS memS) :=
  Presentation.addRelatorsHom FP.toPresentation S

/-- The canonical map on groups after adding filtered relators is surjective. -/
theorem relators_surjective (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s)) :
    Function.Surjective (addRelatorsHom FP S depthS memS).toGroupHom :=
  Presentation.relators_surjective FP.toPresentation S

/-- Kernel of the canonical filtered extra-relator quotient map, expressed in
the underlying presented group. -/
theorem ker_add_hom (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s)) :
    MonoidHom.ker (addRelatorsHom FP S depthS memS).toGroupHom =
      Subgroup.normalClosure (FP.toPresentation.quotientMap '' S) :=
  Presentation.ker_add_hom FP.toPresentation S

/-- If all added relators lie in the `n`th Zassenhaus term of the free group,
then the kernel of the extra-relator quotient is contained in the image of that
term in the old presented group. -/
theorem ker_relators_image
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    {n : ℕ}
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      s ∈ GroupAlgebra.zSubgro p FP.Free n) :
    MonoidHom.ker (addRelatorsHom FP S depthS memS).toGroupHom ≤
      (GroupAlgebra.zSubgro p FP.Free n).map
        FP.toPresentation.quotientMap := by
  classical
  rw [ker_add_hom]
  let D := GroupAlgebra.zSubgro p FP.Free n
  haveI : D.Normal := GroupAlgebra.zassenhausSubgroup_normal p FP.Free n
  haveI : (D.map FP.toPresentation.quotientMap).Normal :=
    (show D.Normal from inferInstance).map FP.toPresentation.quotientMap
      FP.toPresentation.quotientMap_surjective
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rcases hy with ⟨s, hs, rfl⟩
  change FP.toPresentation.quotientMap s ∈ D.map FP.toPresentation.quotientMap
  exact Subgroup.mem_map.mpr ⟨s, hS hs, rfl⟩

/-- Depth-bound version of `ker_relators_image`. -/
theorem ker_relators_depth
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    {n : ℕ} (hNew : ∀ s : {s : FP.Free // s ∈ S}, n ≤ depthS s) :
    MonoidHom.ker (addRelatorsHom FP S depthS memS).toGroupHom ≤
      (GroupAlgebra.zSubgro p FP.Free n).map
        FP.toPresentation.quotientMap :=
  ker_relators_image FP S depthS memS (fun {s} hs => by
    exact GroupAlgebra.depth_least p FP.Free
      (hNew ⟨s, hs⟩) (memS ⟨s, hs⟩))

/-- Uniform lower bounds on old and new relator depths combine after adding
relators. -/
theorem add_relators_depth (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    {n : ℕ}
    (hOld : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r)
    (hNew : ∀ s : {s : FP.Free // s ∈ S}, n ≤ depthS s) :
    ∀ r : (addRelators FP S depthS memS).toPresentation.Relator,
      n ≤ (addRelators FP S depthS memS).depths.depth r := by
  intro r
  dsimp [addRelators]
  by_cases h : (r.1 : FP.Free) ∈ FP.toPresentation.rels
  · convert hOld ⟨r.1, h⟩ using 1
    exact dif_pos h
  · convert hNew ⟨r.1, by
      have hr := r.property
      rcases hr with hr | hr
      · contradiction
      · exact hr⟩ using 1
    exact dif_neg h

/-- View an old relator as a relator of an extra-relator extension. -/
def relatorsOldRelator (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (r : FP.toPresentation.Relator) :
    (addRelators FP S depthS memS).toPresentation.Relator :=
  ⟨r.1, Or.inl r.2⟩

@[simp] theorem relators_old_relator
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (r : FP.toPresentation.Relator) :
    (addRelators FP S depthS memS).depths.depth
        (relatorsOldRelator FP S depthS memS r) =
      FP.depths.depth r := by
  dsimp [relatorsOldRelator, addRelators]
  exact dif_pos r.2

/-- View a new relator as a relator of an extra-relator extension. -/
def relatorsNewRelator (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (s : {s : FP.Free // s ∈ S}) :
    (addRelators FP S depthS memS).toPresentation.Relator :=
  ⟨s.1, Or.inr s.2⟩

/-- If a newly added relator was not already old, its chosen depth is the supplied
new depth. -/
@[simp] theorem relators_new_old
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (s : {s : FP.Free // s ∈ S})
    (hsOld : s.1 ∉ FP.toPresentation.rels) :
    (addRelators FP S depthS memS).depths.depth
        (relatorsNewRelator FP S depthS memS s) =
      depthS s := by
  dsimp [relatorsNewRelator, addRelators]
  exact dif_neg hsOld

/-- Adding relators of depth at least `n` does not change the canonical map to
the free `n`th Zassenhaus quotient: the new map composed with the quotient map
is the old map. -/
theorem quotient_relators_comp
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    {n : ℕ}
    (hOld : ∀ r : FP.toPresentation.Relator, n ≤ FP.depths.depth r)
    (hNew : ∀ s : {s : FP.Free // s ∈ S}, n ≤ depthS s) :
    ((addRelators FP S depthS memS).quotientZassenhaus
        (add_relators_depth FP S depthS memS hOld hNew)).comp
      (addRelatorsHom FP S depthS memS).toGroupHom =
    FP.quotientZassenhaus hOld := by
  apply MonoidHom.ext
  intro q
  rcases FP.toPresentation.quotientMap_surjective q with ⟨x, rfl⟩
  change (addRelators FP S depthS memS).quotientZassenhaus
      (add_relators_depth FP S depthS memS hOld hNew)
      ((addRelatorsHom FP S depthS memS).toGroupHom
        (FP.toPresentation.quotientMap x)) =
    FP.quotientZassenhaus hOld (FP.toPresentation.quotientMap x)
  rw [Presentation.Hom.group_quotient,
    quotient_zassenhaus,
    quotient_zassenhaus]
  change QuotientGroup.mk' (GroupAlgebra.zSubgro p FP.Free n)
      (FreeGroup.map id x) =
    QuotientGroup.mk' (GroupAlgebra.zSubgro p FP.Free n) x
  rw [FreeGroup.map.id]


/-- Monotonicity map between filtered extra-relator extensions when the added
relator set is enlarged.  Depth certificates are irrelevant for the underlying
presentation morphism. -/
def addRelatorsMono (FP : FPres.{u} p)
    {S T : Set FP.Free} (hST : S ⊆ T)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (depthT : {t : FP.Free // t ∈ T} → ℕ)
    (memT : ∀ t : {t : FP.Free // t ∈ T},
      GroupAlgebra.zassenhausDepthLeast p FP.Free t.1 (depthT t)) :
    Hom (addRelators FP S depthS memS) (addRelators FP T depthT memT) :=
  Presentation.addRelatorsMono FP.toPresentation hST

@[simp] theorem add_mono_gen (FP : FPres.{u} p)
    {S T : Set FP.Free} (hST : S ⊆ T)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (depthT : {t : FP.Free // t ∈ T} → ℕ)
    (memT : ∀ t : {t : FP.Free // t ∈ T},
      GroupAlgebra.zassenhausDepthLeast p FP.Free t.1 (depthT t)) (x : FP.Gen) :
    (addRelatorsMono FP hST depthS memS depthT memT).gen x = x := rfl

@[simp] theorem relators_mono_comp
    (FP : FPres.{u} p) {S T : Set FP.Free} (hST : S ⊆ T)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (depthT : {t : FP.Free // t ∈ T} → ℕ)
    (memT : ∀ t : {t : FP.Free // t ∈ T},
      GroupAlgebra.zassenhausDepthLeast p FP.Free t.1 (depthT t)) :
    (addRelatorsMono FP hST depthS memS depthT memT).comp
        (addRelatorsHom FP S depthS memS) =
      addRelatorsHom FP T depthT memT :=
  Presentation.relators_mono_comp FP.toPresentation hST

/-- If the added filtered relators are already consequences of the old relators,
the underlying presented group is unchanged. -/
noncomputable def addSubsetClosure
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : S ≤ FP.toPresentation.rNClos) :
    FP.Group ≃* (addRelators FP S depthS memS).Group :=
  Presentation.addSubsetClosure FP.toPresentation hS

@[simp] theorem add_subset_normal
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : S ≤ FP.toPresentation.rNClos) (x : FP.Group) :
    addSubsetClosure FP S depthS memS hS x =
      (addRelatorsHom FP S depthS memS).toGroupHom x := rfl

@[simp] theorem subset_normal_symm
    (FP : FPres.{u} p) (S : Set FP.Free)
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : S ≤ FP.toPresentation.rNClos)
    (y : (addRelators FP S depthS memS).Group) :
    (addSubsetClosure FP S depthS memS hS).symm y =
      (Presentation.subsetNormalClosure
        FP.toPresentation hS).toGroupHom y := rfl

/-! ### Descent of filtered morphisms through added relators -/

/-- A morphism out of a filtered presentation descends across a filtered
extra-relator extension when it kills the added relators in the target
presentation.  The depth data are bookkeeping only; the underlying descent is
`Presentation.Hom.descAddRelators`. -/
def descRelatorsHom {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos) :
    Hom (addRelators FP S depthS memS) FQ :=
  Presentation.Hom.descAddRelators f hS

@[simp] theorem desc_relators_gen {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos) (x : FP.Gen) :
    (descRelatorsHom FP f depthS memS hS).gen x = f.gen x := rfl

@[simp] theorem desc_relators_comp {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos) :
    (descRelatorsHom FP f depthS memS hS).comp
        (addRelatorsHom FP S depthS memS) = f :=
  Presentation.Hom.descadd_relatorscomp_addrelators f hS

@[simp] theorem desc_add_comp {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos) :
    (descRelatorsHom FP f depthS memS hS).toGroupHom.comp
        (addRelatorsHom FP S depthS memS).toGroupHom = f.toGroupHom :=
  Presentation.Hom.descadd_relatorsgroup_homcomp f hS

/-- Surjectivity descends through a filtered extra-relator quotient. -/
theorem desc_add_surjective {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos)
    (hf : Function.Surjective f.toGroupHom) :
    Function.Surjective (descRelatorsHom FP f depthS memS hS).toGroupHom :=
  Presentation.Hom.desc_add_relatorssurj f hS hf

/-- Injectivity criterion for a descended filtered morphism. -/
theorem desc_relators_injective {FQ : FPres.{u} p}
    (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos)
    (hker : MonoidHom.ker f.toGroupHom ≤
      Subgroup.normalClosure (FP.toPresentation.quotientMap '' S)) :
    Function.Injective (descRelatorsHom FP f depthS memS hS).toGroupHom :=
  Presentation.Hom.descadd_relatorsinj_kernelle f hS hker

/-- Bijectivity criterion for a descended filtered morphism. -/
theorem desc_bijective_surjective
    {FQ : FPres.{u} p} (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos)
    (hker : MonoidHom.ker f.toGroupHom ≤
      Subgroup.normalClosure (FP.toPresentation.quotientMap '' S))
    (hf : Function.Surjective f.toGroupHom) :
    Function.Bijective (descRelatorsHom FP f depthS memS hS).toGroupHom :=
  Presentation.Hom.descadd_relatorsbij_kernellesurj f hS hker hf

/-- Equivalence form of the filtered descent criterion. -/
noncomputable def desc_relators_surjective
    {FQ : FPres.{u} p} (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos)
    (hker : MonoidHom.ker f.toGroupHom ≤
      Subgroup.normalClosure (FP.toPresentation.quotientMap '' S))
    (hf : Function.Surjective f.toGroupHom) :
    (addRelators FP S depthS memS).Group ≃* FQ.Group :=
  Presentation.Hom.desc_relators_surjective f hS hker hf

@[simp] theorem desc_add_relators
    {FQ : FPres.{u} p} (f : Hom FP FQ) {S : Set FP.Free}
    (depthS : {s : FP.Free // s ∈ S} → ℕ)
    (memS : ∀ s : {s : FP.Free // s ∈ S},
      GroupAlgebra.zassenhausDepthLeast p FP.Free s.1 (depthS s))
    (hS : ∀ ⦃s : FP.Free⦄, s ∈ S →
      f.freeMap s ∈ FQ.toPresentation.rNClos)
    (hker : MonoidHom.ker f.toGroupHom ≤
      Subgroup.normalClosure (FP.toPresentation.quotientMap '' S))
    (hf : Function.Surjective f.toGroupHom)
    (x : (addRelators FP S depthS memS).Group) :
    desc_relators_surjective FP f depthS memS hS hker hf x =
      (descRelatorsHom FP f depthS memS hS).toGroupHom x := rfl


/-! ### Layer maps for presented Zassenhaus-image filtrations of active towers -/

/-- Cutoff-increase maps are termwise onto for the presented Zassenhaus-image filtrations. -/
theorem active_mono_filtration
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    DFilt.MapsOnto
      (Presentation.zassenhausImageFiltration p (FP.activePresentation m))
      (Presentation.zassenhausImageFiltration p (FP.activePresentation n))
      (FP.activeMonoHom hmn).toGroupHom := by
  intro k
  exact FP.mono_hom_image hmn k

/-- Active-to-original maps are termwise onto for the presented Zassenhaus-image filtrations. -/
theorem active_original_filtration
    (FP : FPres.{u} p) (n : ℕ) :
    DFilt.MapsOnto
      (Presentation.zassenhausImageFiltration p (FP.activePresentation n))
      (Presentation.zassenhausImageFiltration p FP.toPresentation)
      (FP.activeOriginalHom n).toGroupHom := by
  intro k
  exact FP.original_hom_image n k

/-- The induced map on presented Zassenhaus-image layer kernels for a cutoff increase. -/
noncomputable def activeMonoLayer
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (i : ℕ) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i →*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i :=
  DFilt.layerMap
    (DFilt.MapsOnto.preserves
      (FP.active_mono_filtration hmn)) i

/-- The induced map on presented Zassenhaus-image layer kernels from an active cutoff
 to the original presentation. -/
noncomputable def originalImageLayer
    (FP : FPres.{u} p) (n i : ℕ) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i →*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) i :=
  DFilt.layerMap
    (DFilt.MapsOnto.preserves
      (FP.active_original_filtration n)) i

/-- Increasing the active cutoff induces a bijection on every layer up to the
smaller cutoff. -/
theorem mono_bijective_left
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    Function.Bijective (FP.activeMonoLayer hmn i) := by
  dsimp [activeMonoLayer]
  apply DFilt.bijective_maps_comap
    (FP.active_mono_filtration hmn)
  exact Presentation.Hom.comapzass_imageleker_lemapeq
    (p := p) (f := FP.activeMonoHom hmn) (n := i + 1)
    (FP.ker_active_mono hmn hi)
    (FP.mono_hom_image hmn (i + 1))

/-- At layer `m`, increasing the active cutoff induces a bijection on presented
Zassenhaus-image layer kernels. -/
theorem active_bijective_left
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (FP.activeMonoLayer hmn m) := by
  dsimp [activeMonoLayer]
  apply DFilt.bijective_maps_comap
    (FP.active_mono_filtration hmn)
  exact Presentation.Hom.comapzass_imageleker_lemapeq
    (p := p) (f := FP.activeMonoHom hmn) (n := m + 1)
    (FP.active_mono_presented hmn)
    (FP.mono_hom_image hmn (m + 1))

/-- The active-to-original map induces a bijection on every layer up to the cutoff. -/
theorem original_image_bijective
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    Function.Bijective (FP.originalImageLayer n i) := by
  dsimp [originalImageLayer]
  apply DFilt.bijective_maps_comap
    (FP.active_original_filtration n)
  exact Presentation.Hom.comapzass_imageleker_lemapeq
    (p := p) (f := FP.activeOriginalHom n) (n := i + 1)
    (FP.original_presented_image hi)
    (FP.original_hom_image n (i + 1))

/-- At layer `n`, the active-to-original map induces a bijection on presented
Zassenhaus-image layer kernels. -/
theorem original_layer_bijective
    (FP : FPres.{u} p) (n : ℕ) :
    Function.Bijective (FP.originalImageLayer n n) := by
  dsimp [originalImageLayer]
  apply DFilt.bijective_maps_comap
    (FP.active_original_filtration n)
  exact Presentation.Hom.comapzass_imageleker_lemapeq
    (p := p) (f := FP.activeOriginalHom n) (n := n + 1)
    (FP.original_presented_succ n)
    (FP.original_hom_image n (n + 1))





@[simp] theorem active_mono_coe
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (i : ℕ)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    (FP.activeMonoLayer hmn i x).1 =
      FP.activeMonoQuotient hmn (i + 1)
        x.1 := by
  rfl

@[simp] theorem active_original_coe
    (FP : FPres.{u} p) (n i : ℕ)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :
    (FP.originalImageLayer n i x).1 =
      FP.activeOriginalQuotient n (i + 1)
        x.1 := by
  rfl

/-- Layer maps from a smaller cutoff to the original factor through larger cutoffs. -/
@[simp] theorem original_comp_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) (i : ℕ) :
    (FP.originalImageLayer n i).comp
        (FP.activeMonoLayer hmn i) =
      FP.originalImageLayer m i := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change (FP.originalImageLayer n i
      (FP.activeMonoLayer hmn i x)).1 =
    (FP.originalImageLayer m i x).1
  simp only [active_original_coe,
    active_mono_coe]
  have h := DFunLike.congr_fun
    (FP.active_original_mono hmn (i + 1)) x.1
  simpa only [MonoidHom.comp_apply] using h


/-- Layer-kernel equivalence induced by increasing the active cutoff at any layer up
 to the smaller cutoff. -/
noncomputable def activeMonoImage
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i ≃*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i :=
  MulEquiv.ofBijective (FP.activeMonoLayer hmn i)
    (FP.mono_bijective_left hmn hi)

@[simp] theorem active_mono_zassenhaus
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    FP.activeMonoImage hmn hi x =
      FP.activeMonoLayer hmn i x := rfl

@[simp] theorem mono_monoid_hom
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    (FP.activeMonoImage hmn hi).toMonoidHom =
      FP.activeMonoLayer hmn i := rfl

@[simp] theorem active_mono_left
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    (FP.activeMonoImage hmn hi).symm
        (FP.activeMonoLayer hmn i x) = x := by
  exact (FP.activeMonoImage hmn hi).left_inv x

@[simp] theorem mono_layer_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :
    FP.activeMonoLayer hmn i
        ((FP.activeMonoImage hmn hi).symm y) = y := by
  change FP.activeMonoImage hmn hi
      ((FP.activeMonoImage hmn hi).symm y) = y
  exact (FP.activeMonoImage hmn hi).right_inv y

/-- Equality to an active cutoff-increase layer map, rewritten through the inverse equivalence. -/
theorem mono_image_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :
    FP.activeMonoLayer hmn i x = y ↔
      x = (FP.activeMonoImage hmn hi).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.active_mono_left hmn hi x).symm
  · intro h
    rw [h]
    exact FP.mono_layer_symm hmn hi y

/-- Layer-kernel equivalence induced by the active-to-original map at any layer up
 to the cutoff. -/
noncomputable def activeOriginalEquiv
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i ≃*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) i :=
  MulEquiv.ofBijective (FP.originalImageLayer n i)
    (FP.original_image_bijective hi)

@[simp] theorem original_image_equiv
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :
    FP.activeOriginalEquiv hi x =
      FP.originalImageLayer n i x := rfl

@[simp] theorem original_monoid_hom
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    (FP.activeOriginalEquiv hi).toMonoidHom =
      FP.originalImageLayer n i := rfl

@[simp] theorem original_layer_symm
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :
    (FP.activeOriginalEquiv hi).symm
        (FP.originalImageLayer n i x) = x := by
  exact (FP.activeOriginalEquiv hi).left_inv x

@[simp] theorem active_original_layer
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) i) :
    FP.originalImageLayer n i
        ((FP.activeOriginalEquiv hi).symm y) = y := by
  change FP.activeOriginalEquiv hi
      ((FP.activeOriginalEquiv hi).symm y) = y
  exact (FP.activeOriginalEquiv hi).right_inv y

/-- Equality to an active-to-original layer map, rewritten through the inverse equivalence. -/
theorem original_image_symm
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) i) :
    FP.originalImageLayer n i x = y ↔
      x = (FP.activeOriginalEquiv hi).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.original_layer_symm hi x).symm
  · intro h
    rw [h]
    exact FP.active_original_layer hi y

/-- Once two active cutoffs are at least `i`, their `i`th presented-image layers
are canonically equivalent via the original presentation. -/
noncomputable def activeImageLayer
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i ≃*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i :=
  (FP.activeOriginalEquiv hm).trans
    (FP.activeOriginalEquiv hn).symm

/-- Layer-kernel equivalence induced by increasing the active cutoff at the critical layer. -/
noncomputable def monoImageLeft
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) m ≃*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) m :=
  MulEquiv.ofBijective (FP.activeMonoLayer hmn m)
    (FP.active_bijective_left hmn)

@[simp] theorem mono_image_layer
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) m) :
    FP.monoImageLeft hmn x =
      FP.activeMonoLayer hmn m x := rfl

@[simp] theorem mono_image_monoid
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    (FP.monoImageLeft hmn).toMonoidHom =
      FP.activeMonoLayer hmn m := rfl

@[simp] theorem active_mono_layer
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) m) :
    (FP.monoImageLeft hmn).symm
        (FP.activeMonoLayer hmn m x) = x := by
  exact (FP.monoImageLeft hmn).left_inv x

@[simp] theorem mono_zassenhaus_symm
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) m) :
    FP.activeMonoLayer hmn m
        ((FP.monoImageLeft hmn).symm y) = y := by
  change FP.monoImageLeft hmn
      ((FP.monoImageLeft hmn).symm y) = y
  exact (FP.monoImageLeft hmn).right_inv y

/-- Equality to the critical active layer map, rewritten through its inverse equivalence. -/
theorem active_left_symm
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) m)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) m) :
    FP.activeMonoLayer hmn m x = y ↔
      x = (FP.monoImageLeft hmn).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.active_mono_layer hmn x).symm
  · intro h
    rw [h]
    exact FP.mono_zassenhaus_symm hmn y

/-- Layer-kernel equivalence induced by the active-to-original map at the cutoff layer. -/
noncomputable def activeOriginalLayer
    (FP : FPres.{u} p) (n : ℕ) :
    DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) n ≃*
      DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) n :=
  MulEquiv.ofBijective (FP.originalImageLayer n n)
    (FP.original_layer_bijective n)

@[simp] theorem original_zassenhaus_image
    (FP : FPres.{u} p) (n : ℕ)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) n) :
    FP.activeOriginalLayer n x =
      FP.originalImageLayer n n x := rfl

@[simp] theorem active_original_hom
    (FP : FPres.{u} p) (n : ℕ) :
    (FP.activeOriginalLayer n).toMonoidHom =
      FP.originalImageLayer n n := rfl

@[simp] theorem original_equiv_symm
    (FP : FPres.{u} p) (n : ℕ)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) n) :
    (FP.activeOriginalLayer n).symm
        (FP.originalImageLayer n n x) = x := by
  exact (FP.activeOriginalLayer n).left_inv x

@[simp] theorem original_image_layer
    (FP : FPres.{u} p) (n : ℕ)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) n) :
    FP.originalImageLayer n n
        ((FP.activeOriginalLayer n).symm y) = y := by
  change FP.activeOriginalLayer n
      ((FP.activeOriginalLayer n).symm y) = y
  exact (FP.activeOriginalLayer n).right_inv y

/-- Equality to the critical active-to-original layer map, rewritten through its inverse. -/
theorem active_original_zassenhaus
    (FP : FPres.{u} p) (n : ℕ)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) n)
    (y : DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) n) :
    FP.originalImageLayer n n x = y ↔
      x = (FP.activeOriginalLayer n).symm y := by
  constructor
  · intro h
    rw [← h]
    exact (FP.original_equiv_symm n x).symm
  · intro h
    rw [h]
    exact FP.original_image_layer n y

/-- Cardinality invariance for presented-image layers below the smaller active cutoff. -/
theorem nat_mono_left
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m) :
    Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) =
      Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :=
  Nat.card_congr (FP.activeMonoImage hmn hi).toEquiv

/-- Cardinality invariance for presented-image layers from an active cutoff to the
original presentation, below the cutoff. -/
theorem nat_original_layer
    (FP : FPres.{u} p) {i n : ℕ} (hi : i ≤ n) :
    Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) =
      Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) i) :=
  Nat.card_congr (FP.activeOriginalEquiv hi).toEquiv

/-- Stable cardinality of presented-image layers: any two sufficiently large active
cutoffs give equal cardinalities at a fixed layer. -/
theorem nat_image_layer
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n) :
    Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) =
      Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) i) :=
  Nat.card_congr (FP.activeImageLayer hm hn).toEquiv

/-- The stable layer equivalence is characterized by commuting with the layer maps
 to the original presentation. -/
theorem active_layer_original
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    FP.activeOriginalEquiv hn
        (FP.activeImageLayer hm hn x) =
      FP.activeOriginalEquiv hm x := by
  dsimp [activeImageLayer, MulEquiv.trans]
  exact MulEquiv.apply_symm_apply
    (FP.activeOriginalEquiv hn)
    (FP.activeOriginalEquiv hm x)

/-- Stable layer equivalences compose transitively. -/
theorem active_layer_trans
    (FP : FPres.{u} p) {i m n k : ℕ}
    (hm : i ≤ m) (hn : i ≤ n) (hk : i ≤ k)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    FP.activeImageLayer hn hk
        (FP.activeImageLayer hm hn x) =
      FP.activeImageLayer hm hk x := by
  apply (FP.activeOriginalEquiv hk).injective
  rw [FP.active_layer_original hn hk]
  rw [FP.active_layer_original hm hn]
  rw [FP.active_layer_original hm hk]

/-- The inverse stable layer equivalence is the stable equivalence in the opposite direction. -/
@[simp] theorem active_layer_symm
    (FP : FPres.{u} p) {i m n : ℕ} (hm : i ≤ m) (hn : i ≤ n) :
    (FP.activeImageLayer hm hn).symm =
      FP.activeImageLayer hn hm := rfl

/-- Stable layer equivalences compose as expected, as an equality of equivalences. -/
theorem active_image_trans
    (FP : FPres.{u} p) {i m n k : ℕ}
    (hm : i ≤ m) (hn : i ≤ n) (hk : i ≤ k) :
    (FP.activeImageLayer hm hn).trans
        (FP.activeImageLayer hn hk) =
      FP.activeImageLayer hm hk := by
  ext x
  simpa using FP.active_layer_trans hm hn hk x

/-- The stable layer equivalence from a cutoff to itself is the identity. -/
@[simp] theorem active_layer_self
    (FP : FPres.{u} p) {i m : ℕ} (hm : i ≤ m)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    FP.activeImageLayer hm hm x = x := by
  apply (FP.activeOriginalEquiv hm).injective
  rw [FP.active_layer_original hm hm]

/-- The stable layer equivalence from a cutoff to itself is the identity equivalence. -/
@[simp] theorem active_zassenhaus_self
    (FP : FPres.{u} p) {i m : ℕ} (hm : i ≤ m) :
    FP.activeImageLayer hm hm =
      MulEquiv.refl _ := by
  ext x
  simpa using FP.active_layer_self hm x

/-- For nested cutoffs, the stable layer equivalence agrees with the direct
monotone-cutoff layer equivalence. -/
theorem active_layer_mono
    (FP : FPres.{u} p) {i m n : ℕ} (hmn : m ≤ n) (hi : i ≤ m)
    (x : DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) i) :
    FP.activeImageLayer hi (Nat.le_trans hi hmn) x =
      FP.activeMonoImage hmn hi x := by
  apply (FP.activeOriginalEquiv
    (Nat.le_trans hi hmn)).injective
  rw [FP.active_layer_original hi (Nat.le_trans hi hmn)]
  simp only [active_mono_zassenhaus,
    original_image_equiv]
  have hcomp := FP.original_comp_mono hmn i
  have h := DFunLike.congr_fun hcomp x
  simpa only [MonoidHom.comp_apply] using h.symm

/-- Cardinality invariance for critical presented-image layers along active cutoff increases. -/
theorem card_active_mono
    (FP : FPres.{u} p) {m n : ℕ} (hmn : m ≤ n) :
    Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation m)) m) =
      Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) m) :=
  Nat.card_congr (FP.monoImageLeft hmn).toEquiv

/-- Cardinality invariance for the critical presented-image layer from an active cutoff to full. -/
theorem nat_original_image
    (FP : FPres.{u} p) (n : ℕ) :
    Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p (FP.activePresentation n)) n) =
      Nat.card (DFilt.lKern
        (Presentation.zassenhausImageFiltration p FP.toPresentation) n) :=
  Nat.card_congr (FP.activeOriginalLayer n).toEquiv

end FPres
end Towers
