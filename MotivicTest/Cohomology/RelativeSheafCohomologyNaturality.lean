/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.RelativeSheafCohomologyNaturality
public import Motivic.Transfers.DegreeZeroCohomology

/-!
# Consumers of relative Ext naturality

These checks use the actual free-sheaf cokernels and Ext composition with
independent site-object, site-morphism, coefficient, and Ext universes. The
smooth-site consumers retain the original enlarged coefficient universe for
sheaves with transfers and test the signed boundaries in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  AlgebraicGeometry Motivic

universe w t v u

namespace MotivicTest.Cohomology.RelativeSheafCohomologyNaturality

section Generic

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  {U X V Y : C} (j : U ⟶ X) (j' : V ⟶ Y)
  (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')

/-- The relative source morphism is the genuine cokernel map. -/
theorem actual_cokernel_map :
    SheafCohomology.relativeSourceMap J j j' a b h =
      cokernel.map ((Hypercohomology.freeAbelianSheafFunctor J).map j)
        ((Hypercohomology.freeAbelianSheafFunctor J).map j')
        ((Hypercohomology.freeAbelianSheafFunctor J).map a)
        ((Hypercohomology.freeAbelianSheafFunctor J).map b)
        (by rw [← Functor.map_comp, ← Functor.map_comp, h]) := rfl

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Source restriction is actual Ext precomposition in the independent Ext universe. -/
theorem actual_restriction (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : SheafCohomology.relativeH J j' F n) :
    SheafCohomology.relativeRestriction J j j' a b h F n x =
      (Ext.mk₀ (SheafCohomology.relativeSourceMap J j j' a b h)).comp x (zero_add n) := rfl

/-- The generic square comparison retains the standard signed boundary. -/
theorem generic_signed_boundary_square [Mono j] [Mono j']
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (x : SheafCohomology.H J F n V) :
    SheafCohomology.relativeRestriction J j j' a b h F (n + 1)
        (SheafCohomology.relativeBoundary J j' F n x) =
      SheafCohomology.relativeBoundary J j F n ((SheafCohomology.presheaf J F n).map a.op x) :=
  SheafCohomology.relativeBoundary_restriction J j j' a b h F n x

/-- The generic coefficient comparison uses the original ordinary cohomology functor. -/
theorem generic_signed_boundary_coefficients [Mono j]
    {F G : Sheaf J AddCommGrpCat.{max v t}} (η : F ⟶ G) (n : ℕ)
    (x : SheafCohomology.H J F n U) :
    SheafCohomology.relativeCoefficientMap J j η (n + 1)
        (SheafCohomology.relativeBoundary J j F n x) =
      SheafCohomology.relativeBoundary J j G n
        (((SheafCohomology.presheafFunctor J n).map η).app (op U) x) :=
  SheafCohomology.relativeBoundary_coefficient J j η n x

end Generic

section Smooth

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

local instance {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X)
    [IsOpenImmersion j.left] : Mono j :=
  Hypercohomology.smoothSite_mono_of_isOpenImmersion j

variable {U X V Y : SmoothSite (Spec (.of k))} (j : U ⟶ X) (j' : V ⟶ Y)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')

/-- Squares of actual smooth open immersions respect the signed relative boundary. -/
theorem smooth_signed_boundary_square (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n V) :
    SheafCohomology.relativeRestriction.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j j' a b h
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) (n + 1)
        (SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) j'
          ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n x) =
      SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n
        ((SheafCohomology.presheaf.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n).map a.op x) :=
  SheafCohomology.relativeBoundary_restriction _ j j' a b h _ n x

/-- Actual transfer-sheaf coefficient morphisms respect the same signed boundary. -/
theorem smooth_signed_boundary_coefficients
    {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G) (n : ℕ)
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n U) :
    SheafCohomology.relativeCoefficientMap.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).map η) (n + 1)
        (SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) j
          ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n x) =
      SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj G) n
        (((SheafCohomology.presheafFunctor.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) n).map
          ((SheafWithTransfers.toSheaf.{u + 1, u} k).map η)).app (op U) x) :=
  SheafCohomology.relativeBoundary_coefficient _ j _ n x

end Smooth

end MotivicTest.Cohomology.RelativeSheafCohomologyNaturality
