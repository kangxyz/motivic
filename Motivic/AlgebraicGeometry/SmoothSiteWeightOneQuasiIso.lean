/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.AcyclicKernelQuasiIso
public import Motivic.AlgebraicGeometry.SmoothSiteWeightOneExact

/-! # The actual reduced divisor norm is a quasi-isomorphism -/

@[expose] public noncomputable section

universe u

namespace Motivic

variable (k : Type u) [Field k]

/-- The genuine reduced divisor norm is a quasi-isomorphism, by the actual
short exact divisor sequence and the all-degree acyclicity of its kernel. -/
instance reducedNormSheafMap_quasiIso :
    QuasiIso (SmoothSiteTorusDivisor.reducedNormSheafMap (k := k)) :=
  quasiIso_of_shortExact_isZero_homology (SmoothSiteWeightOneExact.shortComplex k)
    (SmoothSiteWeightOneExact.shortExact k)
    (SmoothSite.isZero_homology_boundaryOneSheafComplex k)

end Motivic
