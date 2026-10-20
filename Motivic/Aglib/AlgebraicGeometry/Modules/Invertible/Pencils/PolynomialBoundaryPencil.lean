/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.GlobalBoundaryPencil
public import Mathlib.RingTheory.Polynomial.Basic

/-! # The global pencil on the literal polynomial parameter line -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible GlobalBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (b : X ⟶ Spec (.of R))

/-- This is literally the polynomial line used by finite correspondences. -/
abbrev parameterSpace :=
  Limits.pullback b (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))

/-- The first projection from the polynomial parameter line to the original scheme. -/
abbrev projection : parameterSpace b ⟶ X := pullback.fst _ _

/-- Its actual global polynomial coordinate. -/
def parameter : Γ(parameterSpace b, ⊤) :=
  (pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))).appTop
    ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X)

/-- Actual scalar-evaluation section. -/
def endpoint (c : R) : X ⟶ parameterSpace b :=
  pullback.lift (𝟙 X) (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))) (by
    simp only [Category.id_comp, Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.C : R →+* R[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 (CommRingCat.of R) := by
      ext r
      exact Polynomial.eval_C
    rw [he, Spec.map_id, Category.comp_id])

@[reassoc (attr := simp)] theorem endpoint_projection (c : R) :
    endpoint b c ≫ projection b = 𝟙 X := pullback.lift_fst _ _ _

@[simp] theorem endpoint_parameter (c : R) :
    (endpoint b c).appTop (parameter b) = b.appTop ((Scheme.ΓSpecIso (.of R)).inv c) := by
  change ((endpoint b c).appTop)
    ((pullback.snd b _).appTop ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, endpoint, pullback.lift_snd,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  apply congrArg (fun x ↦ b.appTop x)
  have hh := (congrArg (fun f : CommRingCat.of R[X] ⟶ Γ(Spec (.of R), ⊤) ↦ f Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Polynomial.evalRingHom c)))).symm
  change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))).appTop
      ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X) =
    (Scheme.ΓSpecIso (.of R)).inv ((Polynomial.evalRingHom c) Polynomial.X) at hh
  simpa using hh

/-- Pull back the original maps and use the literal polynomial coordinate. -/
def familyMap (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (pullbackLineBundle (projection b) L).val ⟶
      SheafOfModules.unit (parameterSpace b).ringCatSheaf :=
  pencil (Hom.pullbackToUnit a (projection b)) (Hom.pullbackToUnit c (projection b)) (parameter b)

/-- Scalar-zero restriction of the genuine family is the first original map. -/
theorem familyMap_zero (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.pullbackToUnit (familyMap b L a c) (endpoint b 0) =
      (sectionPullbackIso (endpoint b 0) (projection b)
        (endpoint_projection b 0)).hom.app L.val ≫ a := by
  change (Scheme.Modules.pullback _).map (pencil _ _ _) ≫ _ = _
  rw [pullback_pencil, endpoint_parameter]
  simp only [map_zero, pencil_zero]
  exact section_pullback_map _ _ _ a

/-- Scalar-one restriction is the second original map, with canonical source comparison. -/
theorem familyMap_one (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.pullbackToUnit (familyMap b L a c) (endpoint b 1) =
      (sectionPullbackIso (endpoint b 1) (projection b)
        (endpoint_projection b 1)).hom.app L.val ≫ c := by
  change (Scheme.Modules.pullback _).map (pencil _ _ _) ≫ _ = _
  rw [pullback_pencil, endpoint_parameter]
  simp only [map_one, pencil_one]
  exact section_pullback_map _ _ _ c

/-- Changing the source trivialization does not change the original image ideal. -/
theorem imageIdealData_precompIso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (a : N ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Hom.imageIdealData (e.hom ≫ a) = Hom.imageIdealData a := by
  unfold Hom.imageIdealData
  congr 1
  funext V
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    exact ⟨e.hom.app V.val m, rfl⟩
  · rintro x ⟨n, rfl⟩
    refine ⟨e.inv.app V.val n, ?_⟩
    exact congrArg (fun f ↦ f.app V.val n) (e.inv_hom_id_assoc a)

/-- The actual zero scheme is unchanged by the original source isomorphism. -/
def zeroSchemePrecompIso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (a : N ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Hom.zeroScheme (e.hom ≫ a) ≅ Hom.zeroScheme a :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (imageIdealData_precompIso e a))

@[reassoc (attr := simp)] theorem zeroSchemePrecompIso_hom_inclusion
    {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (a : N ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    (zeroSchemePrecompIso e a).hom ≫ Hom.zeroInclusion a = Hom.zeroInclusion (e.hom ≫ a) := by
  have transport (I J : Z.IdealSheafData) (h : I = J) :
      eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
    subst J
    simp
  exact transport _ _ (imageIdealData_precompIso e a)

@[reassoc (attr := simp)] theorem zeroScheme_congr_inclusion {Z : Scheme.{u}} {M : Z.Modules}
    {a c : M ⟶ SheafOfModules.unit Z.ringCatSheaf} (h : a = c) :
    eqToHom (congrArg Hom.zeroScheme h) ≫ Hom.zeroInclusion c = Hom.zeroInclusion a := by
  subst c
  simp

/-- The actual whole scalar-zero fibre is the zero scheme of the original first map. -/
def zeroFibreIso (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Limits.pullback (endpoint b 0) (Hom.zeroInclusion (familyMap b L a c)) ≅
      Hom.zeroScheme a := by
  let E := pullbackLineBundle (projection b) L
  let := lineBundle_isLocallyFree (parameterSpace b) E
  exact (Hom.zeroSchemePullbackIso (familyMap b L a c) (endpoint b 0)).symm ≪≫
    eqToIso (congrArg Hom.zeroScheme (familyMap_zero b L a c)) ≪≫
      zeroSchemePrecompIso ((sectionPullbackIso (endpoint b 0) (projection b)
        (endpoint_projection b 0)).app L.val) a

/-- The actual whole scalar-one fibre is the zero scheme of the original second map. -/
def oneFibreIso (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Limits.pullback (endpoint b 1) (Hom.zeroInclusion (familyMap b L a c)) ≅
      Hom.zeroScheme c := by
  let E := pullbackLineBundle (projection b) L
  let := lineBundle_isLocallyFree (parameterSpace b) E
  exact (Hom.zeroSchemePullbackIso (familyMap b L a c) (endpoint b 1)).symm ≪≫
    eqToIso (congrArg Hom.zeroScheme (familyMap_one b L a c)) ≪≫
      zeroSchemePrecompIso ((sectionPullbackIso (endpoint b 1) (projection b)
        (endpoint_projection b 1)).app L.val) c

/-- The zero-endpoint comparison retains the actual original inclusion. -/
@[reassoc] theorem zeroFibreIso_hom_inclusion (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (zeroFibreIso b L a c).hom ≫ Hom.zeroInclusion a =
      pullback.fst (endpoint b 0) (Hom.zeroInclusion (familyMap b L a c)) := by
  let E := pullbackLineBundle (projection b) L
  let := lineBundle_isLocallyFree (parameterSpace b) E
  simp only [zeroFibreIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Iso.app_hom]
  rw [zeroScheme_congr_inclusion (familyMap_zero b L a c)]
  rw [Iso.inv_comp_eq]
  exact (Hom.zeroSchemePullbackIso_hom_fst (familyMap b L a c) (endpoint b 0)).symm

/-- The one-endpoint comparison retains the actual original inclusion. -/
@[reassoc] theorem oneFibreIso_hom_inclusion (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (oneFibreIso b L a c).hom ≫ Hom.zeroInclusion c =
      pullback.fst (endpoint b 1) (Hom.zeroInclusion (familyMap b L a c)) := by
  let E := pullbackLineBundle (projection b) L
  let := lineBundle_isLocallyFree (parameterSpace b) E
  simp only [oneFibreIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Iso.app_hom]
  rw [zeroScheme_congr_inclusion (familyMap_one b L a c)]
  rw [Iso.inv_comp_eq]
  exact (Hom.zeroSchemePullbackIso_hom_fst (familyMap b L a c) (endpoint b 1)).symm

/-- Pasting the actual zero-scheme square with an ambient fibre square identifies
 the entire zero-family fibre, without any regularity or flatness hypothesis. -/
def zeroFibreOverIso {C D S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s)
    (E : LineBundle C) (a : E.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
    Limits.pullback s (Hom.zeroInclusion a ≫ q) ≅ Hom.zeroScheme (Hom.pullbackToUnit a j) := by
  let := lineBundle_isLocallyFree C E
  exact pullbackSymmetry s (Hom.zeroInclusion a ≫ q) ≪≫
    (((IsPullback.of_hasPullback j (Hom.zeroInclusion a)).flip).paste_vert hs).isoPullback.symm ≪≫
      (Hom.zeroSchemePullbackIso a j).symm

/-- The pasted comparison keeps the original base coordinate. -/
@[reassoc] theorem zeroFibreOverIso_hom_base {C D S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s)
    (E : LineBundle C) (a : E.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
    (zeroFibreOverIso j p q s hs E a).hom ≫
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ p =
      pullback.fst s (Hom.zeroInclusion a ≫ q) := by
  let := lineBundle_isLocallyFree C E
  have hi : (Hom.zeroSchemePullbackIso a j).inv ≫
      Hom.zeroInclusion (Hom.pullbackToUnit a j) = pullback.fst j (Hom.zeroInclusion a) := by
    rw [Iso.inv_comp_eq]
    exact (Hom.zeroSchemePullbackIso_hom_fst a j).symm
  simp only [zeroFibreOverIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← Category.assoc (Hom.zeroSchemePullbackIso a j).inv, hi,
    IsPullback.isoPullback_inv_snd, pullbackSymmetry_hom_comp_snd]

/-- The pasted comparison also keeps the original map into the total curve. -/
@[reassoc] theorem zeroFibreOverIso_hom_total {C D S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s)
    (E : LineBundle C) (a : E.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
    (zeroFibreOverIso j p q s hs E a).hom ≫
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j =
      pullback.snd s (Hom.zeroInclusion a ≫ q) ≫ Hom.zeroInclusion a := by
  let := lineBundle_isLocallyFree C E
  have hi : (Hom.zeroSchemePullbackIso a j).inv ≫
      Hom.zeroInclusion (Hom.pullbackToUnit a j) = pullback.fst j (Hom.zeroInclusion a) := by
    rw [Iso.inv_comp_eq]
    exact (Hom.zeroSchemePullbackIso_hom_fst a j).symm
  simp only [zeroFibreOverIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← Category.assoc (Hom.zeroSchemePullbackIso a j).inv, hi, pullback.condition,
    IsPullback.isoPullback_inv_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc]

/-- The literal polynomial parameter change induced by a map of original bases. -/
def parameterMap {D : Scheme.{u}} (f : D ⟶ X) :
    parameterSpace (f ≫ b) ⟶ parameterSpace b :=
  pullback.lift (projection (f ≫ b) ≫ f)
    (pullback.snd (f ≫ b) (Spec.map (CommRingCat.ofHom Polynomial.C))) (by
      simpa only [projection, Category.assoc] using
        (pullback.condition (f := f ≫ b)
          (g := Spec.map (CommRingCat.ofHom Polynomial.C))))

@[reassoc (attr := simp)] theorem parameterMap_projection {D : Scheme.{u}} (f : D ⟶ X) :
    parameterMap b f ≫ projection b = projection (f ≫ b) ≫ f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem parameterMap_snd {D : Scheme.{u}} (f : D ⟶ X) :
    parameterMap b f ≫ pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C)) =
      pullback.snd (f ≫ b) (Spec.map (CommRingCat.ofHom Polynomial.C)) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem endpoint_snd (c : R) :
    endpoint b c ≫ pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C)) =
      b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) := pullback.lift_snd _ _ _

@[reassoc] theorem endpoint_parameterMap {D : Scheme.{u}} (f : D ⟶ X) (c : R) :
    endpoint (f ≫ b) c ≫ parameterMap b f = f ≫ endpoint b c := by
  apply pullback.hom_ext
  · change _ ≫ projection b = _ ≫ projection b
    simp
  · simp

/-- The endpoint square of the actual polynomial family is Cartesian. -/
theorem endpoint_parameterMap_isPullback {D : Scheme.{u}} (f : D ⟶ X) (c : R) :
    IsPullback (endpoint (f ≫ b) c) f (parameterMap b f) (endpoint b c) where
  w := endpoint_parameterMap b f c
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have hf : (s.fst ≫ projection (f ≫ b)) ≫ f = s.snd := by
      have ht := congrArg (fun z ↦ z ≫ projection b) s.condition
      simpa only [Category.assoc, parameterMap_projection, endpoint_projection,
        Category.comp_id] using ht
    refine ⟨s.fst ≫ projection (f ≫ b), ?_, hf, ?_⟩
    · apply pullback.hom_ext
      · change _ ≫ projection (f ≫ b) = _ ≫ projection (f ≫ b)
        simp
      · simp only [PullbackCone.mk_fst]
        rw [Category.assoc, endpoint_snd, ← Category.assoc, ← Category.assoc, hf]
        have ht := congrArg (fun z ↦ z ≫
          pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))) s.condition
        simpa only [Category.assoc, parameterMap_snd, endpoint_snd] using ht.symm
    · intro u hu _
      have ht := congrArg (fun z ↦ z ≫ projection (f ≫ b)) hu
      simpa only [PullbackCone.mk_fst, Category.assoc, endpoint_projection,
        Category.comp_id] using ht)⟩

/-- The whole zero fibre over the original source base is the original section's zero scheme. -/
def zeroFibreOverBaseIso {D : Scheme.{u}} (f : D ⟶ X) (L : LineBundle D)
    (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    Limits.pullback (endpoint b 0)
      (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) ≅ Hom.zeroScheme a :=
  zeroFibreOverIso (endpoint (f ≫ b) 0) f (parameterMap b f) (endpoint b 0)
    (endpoint_parameterMap_isPullback b f 0) (pullbackLineBundle (projection (f ≫ b)) L)
    (familyMap (f ≫ b) L a c) ≪≫
    eqToIso (congrArg Hom.zeroScheme (familyMap_zero (f ≫ b) L a c)) ≪≫
      zeroSchemePrecompIso ((sectionPullbackIso (endpoint (f ≫ b) 0) (projection (f ≫ b))
        (endpoint_projection (f ≫ b) 0)).app L.val) a

@[reassoc] theorem zeroFibreOverBaseIso_hom_base {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    (zeroFibreOverBaseIso b f L a c).hom ≫ Hom.zeroInclusion a ≫ f =
      pullback.fst (endpoint b 0)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) := by
  simp only [zeroFibreOverBaseIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion_assoc, Iso.app_hom]
  rw [zeroScheme_congr_inclusion_assoc (familyMap_zero (f ≫ b) L a c)]
  exact zeroFibreOverIso_hom_base _ _ _ _ _ _ _

@[reassoc] theorem zeroFibreOverBaseIso_hom_original {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    (zeroFibreOverBaseIso b f L a c).hom ≫ Hom.zeroInclusion a =
      pullback.snd (endpoint b 0)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) ≫
          Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ projection (f ≫ b) := by
  simp only [zeroFibreOverBaseIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Iso.app_hom]
  rw [zeroScheme_congr_inclusion (familyMap_zero (f ≫ b) L a c)]
  have ht := congrArg (fun z ↦ z ≫ projection (f ≫ b))
    (zeroFibreOverIso_hom_total (endpoint (f ≫ b) 0) f (parameterMap b f) (endpoint b 0)
      (endpoint_parameterMap_isPullback b f 0) (pullbackLineBundle (projection (f ≫ b)) L)
      (familyMap (f ≫ b) L a c))
  simpa only [Category.assoc, endpoint_projection, Category.comp_id] using ht

/-- The whole one fibre over the original source base is the original section's zero scheme. -/
def oneFibreOverBaseIso {D : Scheme.{u}} (f : D ⟶ X) (L : LineBundle D)
    (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    Limits.pullback (endpoint b 1)
      (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) ≅ Hom.zeroScheme c :=
  zeroFibreOverIso (endpoint (f ≫ b) 1) f (parameterMap b f) (endpoint b 1)
    (endpoint_parameterMap_isPullback b f 1) (pullbackLineBundle (projection (f ≫ b)) L)
    (familyMap (f ≫ b) L a c) ≪≫
    eqToIso (congrArg Hom.zeroScheme (familyMap_one (f ≫ b) L a c)) ≪≫
      zeroSchemePrecompIso ((sectionPullbackIso (endpoint (f ≫ b) 1) (projection (f ≫ b))
        (endpoint_projection (f ≫ b) 1)).app L.val) c

@[reassoc] theorem oneFibreOverBaseIso_hom_base {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    (oneFibreOverBaseIso b f L a c).hom ≫ Hom.zeroInclusion c ≫ f =
      pullback.fst (endpoint b 1)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) := by
  simp only [oneFibreOverBaseIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion_assoc, Iso.app_hom]
  rw [zeroScheme_congr_inclusion_assoc (familyMap_one (f ≫ b) L a c)]
  exact zeroFibreOverIso_hom_base _ _ _ _ _ _ _

@[reassoc] theorem oneFibreOverBaseIso_hom_original {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    (oneFibreOverBaseIso b f L a c).hom ≫ Hom.zeroInclusion c =
      pullback.snd (endpoint b 1)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) ≫
          Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ projection (f ≫ b) := by
  simp only [oneFibreOverBaseIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Iso.app_hom]
  rw [zeroScheme_congr_inclusion (familyMap_one (f ≫ b) L a c)]
  have ht := congrArg (fun z ↦ z ≫ projection (f ≫ b))
    (zeroFibreOverIso_hom_total (endpoint (f ≫ b) 1) f (parameterMap b f) (endpoint b 1)
      (endpoint_parameterMap_isPullback b f 1) (pullbackLineBundle (projection (f ≫ b)) L)
      (familyMap (f ≫ b) L a c))
  simpa only [Category.assoc, endpoint_projection, Category.comp_id] using ht

end AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
