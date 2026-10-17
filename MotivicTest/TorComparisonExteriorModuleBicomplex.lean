/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleBicomplex

/-! Real consumers of scalar restriction, both bicomplex differentials, and naturality. -/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex
open Motivic.TorComparison.ExteriorModule

universe u

namespace Motivic.MotivicTest.TorComparisonExteriorModuleBicomplex

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]
  (K : ChainComplex (ModuleCat.{u} U) ℕ) (L : ChainComplex (ModuleCat.{u} V) ℕ)

/-- The codomain is the literal tensor bicomplex of the restricted inputs. -/
def scalarIdentification : restrictedBicomplex k U V K L ≅ baseBicomplex k U V K L :=
  scalarBicomplexIso k U V K L

/-- The map in every bidegree is the constructed scalar-module identification. -/
theorem literal_component (i j : ℕ) :
    ((scalarBicomplexIso k U V K L).hom.f i).f j =
      (restrictObjIso k U V (K.X i) (L.X j)).hom :=
  scalarBicomplexIso_hom_f_f k U V K L i j

/-- Compatibility with the actual vertical differential, even away from adjacent degrees. -/
theorem vertical_differential (i j j' : ℕ) :
    ((scalarBicomplexIso k U V K L).hom.f i).f j ≫
        ((baseBicomplex k U V K L).X i).d j j' =
      ((restrictedBicomplex k U V K L).X i).d j j' ≫
        ((scalarBicomplexIso k U V K L).hom.f i).f j' :=
  ((scalarBicomplexIso k U V K L).hom.f i).comm j j'

/-- Compatibility with the actual horizontal differential in each vertical degree. -/
theorem horizontal_differential (i i' j : ℕ) :
    ((scalarBicomplexIso k U V K L).hom.f i).f j ≫
        ((baseBicomplex k U V K L).d i i').f j =
      ((restrictedBicomplex k U V K L).d i i').f j ≫
        ((scalarBicomplexIso k U V K L).hom.f i').f j :=
  congrArg (fun f ↦ f.f j) ((scalarBicomplexIso k U V K L).hom.comm i i')

/-- Both input maps participate in the proved naturality identity. -/
theorem simultaneous_naturality {K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    restrictedBicomplexMap k f g ≫ (scalarBicomplexIso k U V K' L').hom =
      (scalarBicomplexIso k U V K L).hom ≫ baseBicomplexMap k f g :=
  scalarBicomplexIso_naturality k f g

end Motivic.MotivicTest.TorComparisonExteriorModuleBicomplex
