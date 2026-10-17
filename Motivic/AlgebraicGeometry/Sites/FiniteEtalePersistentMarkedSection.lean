/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleMarkedPointDetection
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOpenZeroFamily

/-! # Persistent section detection on arbitrary original small-site test objects -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}}

/-- Compose actual étale structure maps, retaining the underlying object. -/
def composeObject (V : FiniteEtaleSite S) (W : FiniteEtaleSite V.left) :
    FiniteEtaleSite S :=
  MorphismProperty.Over.mk ⊤ (W.hom ≫ V.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

def composeObjectMap (V : FiniteEtaleSite S) {W Z : FiniteEtaleSite V.left}
    (f : W ⟶ Z) : composeObject V W ⟶ composeObject V Z :=
  MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (Z.hom ≫ V.hom) = W.hom ≫ V.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

def composeObjectProjection (V : FiniteEtaleSite S) (W : FiniteEtaleSite V.left) :
    composeObject V W ⟶ V := MorphismProperty.Over.homMk W.hom rfl

/-- Every original arrow into V is again an actual object of its small étale site. -/
def arrowObject {W V : FiniteEtaleSite S} (f : W ⟶ V) : FiniteEtaleSite V.left := by
  have hp : etaleSeparatedFiniteType (f.left ≫ V.hom) := by
    rw [MorphismProperty.Over.w]
    exact W.prop
  exact MorphismProperty.Over.mk ⊤ f.left
    (etaleSeparatedFiniteType.of_postcomp f.left V.hom V.prop hp)

/-- The original open part of V, still an object over the unchanged site base S. -/
def testOpenObject (V : FiniteEtaleSite S) [IsNoetherian V.left] (O : V.left.Opens) :
    FiniteEtaleSite S := composeObject V (openObject O)

def testOpenInclusion (V : FiniteEtaleSite S) [IsNoetherian V.left] (O : V.left.Opens) :
    testOpenObject V O ⟶ V := composeObjectProjection V (openObject O)

/-- Persistent marked germs of a section on any test object are detected after a true
base shrink; the coefficient remains the same sheaf on S throughout. -/
theorem exists_open_test_restriction_eq_zero_of_persistent_marked_germs
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (V : FiniteEtaleSite S) [IsNoetherian V.left]
    {X : Scheme.{u}} (g : V.left ⟶ X) (x : X) (s : G.obj.obj (op V))
    (hs : ∀ z : V.left, g z ⤳ x → markedSectionGerm G.obj V z s = 0) :
    ∃ O : X.Opens, x ∈ O ∧
      G.obj.map (testOpenInclusion V (g ⁻¹ᵁ O)).op s = 0 := by
  classical
  let I := {z : V.left // g z ⤳ x}
  choose W f y hy hi hz using fun i : I =>
    exists_marked_zero_neighborhood G.obj V i.val s (hs i.val i.property)
  let A := fun i => arrowObject (f i)
  have hf : ∀ z : V.left, g z ⤳ x → ∃ (i : I) (a : (A i).left),
      (A i).hom a = z ∧ IsIso ((A i).hom.residueFieldMap a) := by
    intro z h
    exact ⟨⟨z, h⟩, y ⟨z, h⟩, hy ⟨z, h⟩, hi ⟨z, h⟩⟩
  obtain ⟨O, hx, t, ht⟩ :=
    Nisnevich.exists_open_finset_persistent_residueFieldLifting g x (fun i => (A i).hom) hf
  let B := fun i => composeObject V (openRestrictedObject (A i) (g ⁻¹ᵁ O))
  let b := fun i => composeObjectMap V (openRestrictedMap (A i) (g ⁻¹ᵁ O))
  have hpre : Presieve.ofArrows B b ∈ nisnevichPrecoverage S (testOpenObject V (g ⁻¹ᵁ O)) := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff b).mpr
    refine ⟨fun i => ?_, ?_⟩
    · change Etale ((A i).hom ∣_ (g ⁻¹ᵁ O))
      infer_instance
    · intro z
      obtain ⟨i, _, a, ha, hia⟩ := ht z.val z.property
      let a' : (A i).hom ⁻¹ᵁ (g ⁻¹ᵁ O) :=
        ⟨a, by change g ((A i).hom a) ∈ O; erw [ha]; exact z.property⟩
      have hba : (b i).left a' = z := by
        apply Subtype.ext
        exact (morphismRestrict_base_coe (A i).hom (g ⁻¹ᵁ O) a').trans ha
      refine ⟨i, a', hba, ?_⟩
      let : IsIso ((A i).hom.residueFieldMap a) := hia
      have hc : IsIso ((((A i).hom ∣_ (g ⁻¹ᵁ O)) ≫
          (g ⁻¹ᵁ O).ι).residueFieldMap a') := by
        rw [morphismRestrict_ι, Scheme.residueFieldMap_comp]
        change IsIso ((A i).hom.residueFieldMap a ≫ _)
        infer_instance
      rw [Scheme.residueFieldMap_comp] at hc
      exact IsIso.of_isIso_comp_left ((g ⁻¹ᵁ O).ι.residueFieldMap _)
        (((A i).hom ∣_ (g ⁻¹ᵁ O)).residueFieldMap a')
  have hcov : Sieve.ofArrows B b ∈ nisnevichTopology S (testOpenObject V (g ⁻¹ᵁ O)) :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsheaf := ((isSheaf_iff_isSheaf_of_type (nisnevichTopology S) _).mp
    ((sheafCompose (nisnevichTopology S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property).isSheafFor
        (Presieve.ofArrows B b) hcov
  refine ⟨O, hx, ?_⟩
  apply hsheaf.isSeparatedFor.ext
  rintro C a ⟨i⟩
  let c : B i ⟶ W i := MorphismProperty.Over.homMk ((A i).hom ⁻¹ᵁ (g ⁻¹ᵁ O)).ι (by
    change _ ≫ (W i).hom = (_ ≫ (f i).left) ≫ V.hom
    rw [Category.assoc, MorphismProperty.Over.w])
  have hb : b i ≫ testOpenInclusion V (g ⁻¹ᵁ O) = c ≫ f i := by
    apply MorphismProperty.Over.Hom.ext
    exact morphismRestrict_ι (A i).hom (g ⁻¹ᵁ O)
  change G.obj.map (b i).op (G.obj.map (testOpenInclusion V (g ⁻¹ᵁ O)).op s) =
    G.obj.map (b i).op 0
  rw [map_zero]
  have he := congrArg (fun a => G.obj.map a.op s) hb
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at he
  exact he.trans ((congrArg (fun a => G.obj.map c.op a) (hz i)).trans (map_zero _))

end Motivic.FiniteEtaleSite
