/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.GlobalBoundary

/-! Direct consumers for constructed signed families and whole endpoint cycles. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram Motivic.GlobalBoundaryPencil

universe u

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ relativeLine X.hom) [IsProper q]
  (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
  (a b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) (t : Γ(C, ⊤))
  [IsIso ((Scheme.Modules.pullback i).map a)]
  (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit b i)
  (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
  (g : U ⟶ Y.left)
  (hbase : (j ≫ q) ≫ relativeLineHom X.hom = g ≫ Y.hom)

example : (Cor.graphFunctor k).map (endpointMorphism X 0) ≫
    signedCorrespondence X Y i q j L a b t h hcover g hbase = 0 :=
  signedCorrespondence_zero X Y i q j L a b t h hcover g hbase

example : (Cor.graphFunctor k).map (endpointMorphism X 1) ≫
    signedCorrespondence X Y i q j L a b t h hcover g hbase =
    endpointCorrespondence X Y i q j L a b t h hcover g hbase 1 -
      endpointCorrespondence X Y i q j L a b t h hcover g hbase 0 :=
  signedCorrespondence_one X Y i q j L a b t h hcover g hbase

#print axioms family_properties
#print axioms ofFiniteFlatSpan_precompIso
#print axioms signedCorrespondence_zero
#print axioms signedCorrespondence_one
