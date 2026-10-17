module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Image ideals and whole zero schemes under arbitrary base change -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X Y Z : Scheme.{u}} {M : Y.Modules}
variable (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf)

/-- The native image ideal detects annihilation by arbitrary structure maps. -/
theorem imageIdealData_le_ker_iff (h : ImageIdealLocalizes φ) (i : X ⟶ Y) :
    imageIdealData φ ≤ i.ker ↔ φ ≫ structureModuleMap i = 0 := by
  constructor
  · intro H
    apply moduleHom_ext_affine
    intro U
    ext m
    exact i.ideal_ker_le U (H U ((imageIdealData_eq φ h U).symm ▸
      (show φ.app U.val m ∈ sectionImageIdeal φ U.val from ⟨m, rfl⟩)))
  · intro H
    apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
    intro U x hx
    rw [imageIdealData_eq φ h U] at hx
    obtain ⟨m, rfl⟩ := hx
    exact congrArg (fun k ↦ k.val.app (op U.val) m) H

/-- Pullback of a module-to-unit morphism, with the canonical unit identification. -/
def pullbackToUnit (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback f).map φ ≫ (pullbackUnitIso f).hom

/-- Annihilation after arbitrary base change is the original annihilation equation. -/
theorem pullbackToUnit_annihilation_iff (f : X ⟶ Y) (i : Z ⟶ X) :
    pullbackToUnit φ f ≫ structureModuleMap i = 0 ↔
      φ ≫ structureModuleMap (i ≫ f) = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hz : adj.homEquiv M ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) 0 = 0 := by
    rw [Adjunction.homEquiv_unit]
    simp
  have he : adj.homEquiv _ _ (pullbackToUnit φ f ≫ structureModuleMap i) =
      φ ≫ structureModuleMap f ≫ (Scheme.Modules.pushforward f).map (structureModuleMap i) := by
    unfold pullbackToUnit
    rw [Category.assoc, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
    rfl
  rw [← (adj.homEquiv _ _).injective.eq_iff, hz, he,
    structureModuleMap_comp, ← Category.assoc]
  exact (cancel_mono ((Scheme.Modules.pushforwardComp i f).hom.app
    (SheafOfModules.unit Z.ringCatSheaf))).symm.trans (by simp)

/-- Image ideals commute with arbitrary base change, without any flatness hypothesis. -/
theorem imageIdealData_pullbackToUnit (f : X ⟶ Y)
    (h : ImageIdealLocalizes φ) (hf : ImageIdealLocalizes (pullbackToUnit φ f)) :
    imageIdealData (pullbackToUnit φ f) = (imageIdealData φ).comap f := by
  have H (I : X.IdealSheafData) :
      imageIdealData (pullbackToUnit φ f) ≤ I ↔ (imageIdealData φ).comap f ≤ I := by
    calc
      imageIdealData (pullbackToUnit φ f) ≤ I ↔
          pullbackToUnit φ f ≫ structureModuleMap I.subschemeι = 0 := by
        nth_rw 1 [← I.ker_subschemeι]
        exact imageIdealData_le_ker_iff _ hf _
      _ ↔ φ ≫ structureModuleMap (I.subschemeι ≫ f) = 0 :=
        pullbackToUnit_annihilation_iff φ f I.subschemeι
      _ ↔ imageIdealData φ ≤ I.map f :=
        (imageIdealData_le_ker_iff φ h (I.subschemeι ≫ f)).symm
      _ ↔ (imageIdealData φ).comap f ≤ I :=
        Scheme.IdealSheafData.le_map_iff_comap_le
  exact le_antisymm ((H _).mpr le_rfl) ((H _).mp le_rfl)

/-- The quasicoherent case needs no separately supplied localization witnesses. -/
theorem imageIdealData_pullbackToUnit_of_isQuasicoherent [M.IsQuasicoherent]
    (f : X ⟶ Y) :
    imageIdealData (pullbackToUnit φ f) = (imageIdealData φ).comap f :=
  imageIdealData_pullbackToUnit φ f (imageIdealLocalizes_of_isQuasicoherent φ)
    (imageIdealLocalizes_of_isQuasicoherent _)

/-- The whole zero scheme, including its nilpotents, commutes with arbitrary base change. -/
def zeroSchemePullbackIso [M.IsQuasicoherent] (f : X ⟶ Y) :
    zeroScheme (pullbackToUnit φ f) ≅ Limits.pullback f (zeroInclusion φ) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (imageIdealData_pullbackToUnit_of_isQuasicoherent φ f)) ≪≫
      (imageIdealData φ).comapIso f

@[reassoc (attr := simp)]
theorem zeroSchemePullbackIso_hom_fst [M.IsQuasicoherent] (f : X ⟶ Y) :
    (zeroSchemePullbackIso φ f).hom ≫ pullback.fst f (zeroInclusion φ) =
      zeroInclusion (pullbackToUnit φ f) := by
  dsimp only [zeroSchemePullbackIso, Iso.trans_hom, eqToIso.hom, zeroScheme, zeroInclusion]
  rw [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have transport (I J : X.IdealSheafData) (h : I = J) :
      eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι =
        I.subschemeι := by
    subst J
    simp
  exact transport _ _ (imageIdealData_pullbackToUnit_of_isQuasicoherent φ f)

/-- An invertible equation has the unit ideal as its scheme-theoretic image. -/
theorem imageIdealData_eq_top_of_isIso [IsIso φ] : imageIdealData φ = ⊤ := by
  have h (U : Y.affineOpens) : sectionImageIdeal φ U.val = ⊤ := by
    apply top_unique
    intro r _
    refine ⟨(inv φ).app U.val r, ?_⟩
    exact congrArg (fun k ↦ k.app U.val r) (IsIso.inv_hom_id φ)
  unfold imageIdealData
  simp_rw [h]
  exact Scheme.IdealSheafData.ofIdeals_ideal ⊤

/-- An invertible equation has empty whole zero scheme. -/
theorem isEmpty_zeroScheme_of_isIso [IsIso φ] : IsEmpty (zeroScheme φ) := by
  unfold zeroScheme
  rw [imageIdealData_eq_top_of_isIso φ]
  infer_instance

/-- An invertible pulled-back equation makes the actual scheme fiber product empty. -/
theorem isEmpty_pullback_zeroInclusion [M.IsQuasicoherent] (f : X ⟶ Y)
    [IsIso (pullbackToUnit φ f)] :
    IsEmpty (Limits.pullback (C := Scheme.{u}) f (zeroInclusion φ)) := by
  let := isEmpty_zeroScheme_of_isIso (pullbackToUnit φ f)
  exact ⟨fun x ↦ isEmptyElim ((zeroSchemePullbackIso φ f).inv x)⟩

end AlgebraicGeometry.Scheme.Modules.Hom
