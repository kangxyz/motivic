/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleResidueGerms
public import Motivic.Aglib.AlgebraicGeometry.NisnevichPersistentFiniteSubfamily

/-! # Actual small-site separatedness for residue-splitting zero families -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace Motivic.FiniteEtaleSite
variable {U : Scheme.{u}} [IsNoetherian U]

/-- An actual open subscheme as an object of the original small site. -/
def openObject (W : U.Opens) : FiniteEtaleSite U :=
  MorphismProperty.Over.mk ⊤ W.ι ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Restriction of an actual small-site object to an original base open. -/
def openRestrictedObject (V : FiniteEtaleSite U) (W : U.Opens) : FiniteEtaleSite U := by
  let : QuasiCompact (((V.hom ∣_ W) ≫ W.ι)) := inferInstance
  have : QuasiCompact ((V.hom ⁻¹ᵁ W).ι ≫ V.hom) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact MorphismProperty.Over.mk ⊤ ((V.hom ⁻¹ᵁ W).ι ≫ V.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

def openRestrictedInclusion (V : FiniteEtaleSite U) (W : U.Opens) :
    openRestrictedObject V W ⟶ V := MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ W).ι rfl

def openRestrictedMap (V : FiniteEtaleSite U) (W : U.Opens) :
    openRestrictedObject V W ⟶ openObject W :=
  MorphismProperty.Over.homMk (V.hom ∣_ W) (morphismRestrict_ι _ _)

@[reassoc] theorem openRestrictedMap_toBase (V : FiniteEtaleSite U) (W : U.Opens) :
    openRestrictedMap V W ≫ toBaseObject (openObject W) =
      openRestrictedInclusion V W ≫ toBaseObject V := by
  apply MorphismProperty.Over.Hom.ext
  exact morphismRestrict_ι V.hom W

/-- An actual residue-splitting family of zero restrictions forces the original
section to vanish on the specified base open. This uses small-site separatedness only. -/
theorem open_restriction_eq_zero_of_residue_splitting_family
    (G : Sheaf (nisnevichTopology U) AddCommGrpCat.{u + 1})
    (s : G.obj.obj (op (baseObject U))) (W : U.Opens)
    {I : Type v} (V : I → FiniteEtaleSite U)
    (hzero : ∀ i, G.obj.map (toBaseObject (V i)).op s = 0)
    (hcover : ∀ z : U, z ∈ W → ∃ (i : I) (y : (V i).left),
      (V i).hom y = z ∧ IsIso ((V i).hom.residueFieldMap y)) :
    G.obj.map (toBaseObject (openObject W)).op s = 0 := by
  let A := fun i => openRestrictedObject (V i) W
  let f := fun i => openRestrictedMap (V i) W
  have hpre : Presieve.ofArrows A f ∈ nisnevichPrecoverage U (openObject W) := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    refine ⟨fun i => ?_, ?_⟩
    · change Etale ((V i).hom ∣_ W)
      infer_instance
    · intro z
      obtain ⟨i, y, hy, hi⟩ := hcover z.val z.property
      let y' : (V i).hom ⁻¹ᵁ W := ⟨y, by change (V i).hom y ∈ W; rw [hy]; exact z.property⟩
      have hfy : (f i).left y' = z := by
        apply Subtype.ext
        exact (morphismRestrict_base_coe (V i).hom W y').trans hy
      refine ⟨i, y', hfy, ?_⟩
      let : IsIso ((V i).hom.residueFieldMap y) := hi
      have ha : IsIso (((V i).hom ⁻¹ᵁ W).ι.residueFieldMap y') := inferInstance
      have hb : IsIso ((((V i).hom ⁻¹ᵁ W).ι ≫ (V i).hom).residueFieldMap y') := by
        rw [Scheme.residueFieldMap_comp]
        change IsIso ((V i).hom.residueFieldMap y ≫ _)
        infer_instance
      have hc : IsIso (((V i).hom ∣_ W ≫ W.ι).residueFieldMap y') := by
        rw [morphismRestrict_ι]
        exact hb
      rw [Scheme.residueFieldMap_comp] at hc
      exact IsIso.of_isIso_comp_left (W.ι.residueFieldMap _) (((V i).hom ∣_ W).residueFieldMap y')
  have hcov : Sieve.ofArrows A f ∈ nisnevichTopology U (openObject W) :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsheaf := ((isSheaf_iff_isSheaf_of_type (nisnevichTopology U) _).mp
    ((sheafCompose (nisnevichTopology U)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property).isSheafFor
        (Presieve.ofArrows A f) hcov
  apply hsheaf.isSeparatedFor.ext
  rintro B a ⟨i⟩
  change G.obj.map (f i).op (G.obj.map (toBaseObject (openObject W)).op s) =
    G.obj.map (f i).op 0
  rw [map_zero, ← Functor.map_comp_apply, ← op_comp, openRestrictedMap_toBase,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hzero, map_zero]

end Motivic.FiniteEtaleSite
