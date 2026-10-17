/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Category
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor
public import Motivic.AlgebraicGeometry.Correspondences.BinaryCoproducts
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichTopology
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichSignedLocalLift
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichFamilyLocalLift
public import Motivic.AlgebraicGeometry.Correspondences.SimplexSingularTransferFunctor
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.NisnevichComparison
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.NisnevichSheafification
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Yoneda
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichSheafification
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichSheavesWithTransfers

/-!
# Finite correspondences and presheaves with transfers

This entry point exposes the actual preadditive category of finite
correspondences, the graph functor from smooth schemes, additive presheaves
with transfers and their representables, and the smooth Nisnevich site.
It also exposes the actual additive simplex exterior endofunctors and the
all-degree additive contravariant singular functor with transfers. Their
identity and composition laws use the original correspondence cycles.
Signed correspondences also lift locally through arbitrary smooth Nisnevich
covering families, using finitely many labeled branches on actual pointed
smooth-site neighborhoods. The actual empty scheme is a zero object, and finite
disjoint unions give biproducts. Signed relations killed by a Nisnevich graph
are actual Čech boundaries after a pointed Nisnevich neighborhood.

The genuine singleton-cover topology on `Cor` has a principal covering basis,
stable under arbitrary signed correspondences. For additive presheaves, its
sheaf condition is equivalent to ordinary Nisnevich sheafness of graph
restriction, including arbitrary covering families and the empty scheme.
Transfer-preserving Nisnevich sheafification is left adjoint to the original
inclusion of sheaves with transfers. Its underlying ordinary sheafification
is canonically isomorphic to ordinary Nisnevich sheafification, with the
canonical units identified. The usable coefficient universe is `u + 1` for a
field in `Type u`.
-/
