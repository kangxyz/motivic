/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Motivic.AlgebraicGeometry.Correspondences.Generators.Basic

/-!
# Noetherian correspondence supports
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic
namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

instance isNoetherian_scheme [IsNoetherian X] (Z : FiniteCorrespondenceGenerator f g) :
    IsNoetherian Z.scheme :=
  isNoetherian_of_finiteType Z.projection

/-- The local rings of the actual correspondence support are Noetherian. -/
theorem stalk_isNoetherian [IsNoetherian X] (Z : FiniteCorrespondenceGenerator f g)
    (z : Z.scheme) : IsNoetherianRing (Z.scheme.presheaf.stalk z) := inferInstance

end FiniteCorrespondenceGenerator

end Motivic
