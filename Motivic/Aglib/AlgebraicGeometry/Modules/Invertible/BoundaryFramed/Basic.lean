/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization

/-!
# Boundary-framed line bundles

The objects are native line bundles together with a specified trivialization on
an actual boundary morphism. Classes remember that trivialization: an ordinary
line-bundle isomorphism identifies them only when it preserves the frame.
No group structure or comparison with relative sheaf cohomology is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A native line bundle with a specified trivialization along a boundary morphism. -/
structure BoundaryFramedLineBundle {C D : Scheme.{u}} (i : D ⟶ C) where
  /-- The original locally rank-one module sheaf. -/
  lineBundle : LineBundle C
  /-- The specified trivialization of its pullback to the boundary. -/
  frame : (Modules.pullback i).obj lineBundle.val ≅ SheafOfModules.unit D.ringCatSheaf

namespace BoundaryFramedLineBundle

variable {C D : Scheme.{u}} {i : D ⟶ C}

/-- An actual line-bundle isomorphism preserving the specified boundary frames. -/
structure Iso (L M : BoundaryFramedLineBundle i) where
  /-- The original module-sheaf isomorphism. -/
  iso : L.lineBundle.val ≅ M.lineBundle.val
  /-- Its pullback intertwines the two specified trivializations. -/
  frame_hom : (Modules.pullback i).map iso.hom ≫ M.frame.hom = L.frame.hom

/-- The identity preserves the original boundary frame. -/
def Iso.refl (L : BoundaryFramedLineBundle i) : Iso L L where
  iso := CategoryTheory.Iso.refl _
  frame_hom := by simp

/-- The inverse of a frame-preserving isomorphism preserves the frames. -/
def Iso.symm {L M : BoundaryFramedLineBundle i} (e : Iso L M) : Iso M L where
  iso := e.iso.symm
  frame_hom := by
    rw [← e.frame_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    simp

/-- Composition retains the actual frame equation. -/
def Iso.trans {L M N : BoundaryFramedLineBundle i} (e : Iso L M) (f : Iso M N) :
    Iso L N where
  iso := e.iso ≪≫ f.iso
  frame_hom := by
    simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [f.frame_hom, e.frame_hom]

/-- Isomorphism identifies objects only when their specified frames agree. -/
def setoid (i : D ⟶ C) : Setoid (BoundaryFramedLineBundle i) where
  r L M := Nonempty (Iso L M)
  iseqv := ⟨fun L => ⟨Iso.refl L⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Boundary-framed isomorphism classes, without a claimed relative Picard group structure. -/
def Class (i : D ⟶ C) := Quotient (setoid i)

/-- The class of the original line bundle and specified frame. -/
def classOf (L : BoundaryFramedLineBundle i) : Class i := Quotient.mk (setoid i) L

/-- Equality of classes retains a frame-preserving isomorphism witness. -/
theorem classOf_eq_iff (L M : BoundaryFramedLineBundle i) :
    classOf L = classOf M ↔ Nonempty (Iso L M) := Quotient.eq

/-- Forget the frame, landing in the existing ordinary Picard group. -/
def forget (a : Class i) : PicardGroup C :=
  Quotient.liftOn a (fun L => Invertible.classOf C L.lineBundle) (by
    intro L M ⟨e⟩
    exact Quotient.sound ⟨e.iso⟩)

@[simp]
theorem forget_classOf (L : BoundaryFramedLineBundle i) :
    forget (classOf L) = Invertible.classOf C L.lineBundle := rfl

/-- A section invertible on the boundary gives its original line bundle a canonical frame. -/
def ofSection (i : D ⟶ C) (L : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)] : BoundaryFramedLineBundle i where
  lineBundle := L
  frame := (asIso (pullbackSectionMap i s)).symm

@[simp]
theorem ofSection_frame_inv (L : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)] :
    (ofSection i L s).frame.inv = pullbackSectionMap i s := rfl

end BoundaryFramedLineBundle

end AlgebraicGeometry.Scheme.Modules.Invertible
