# Conditional HI-presheaf sheafification reduction

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Cohomology.A1.Sheafification.DenseDetection` | Original dense restrictions without assumed HI of the target sheafification |
| `Motivic.Cohomology.A1.Sheafification.CylinderCriterion` | HI conditional on actual whole-cylinder lifting |
| `Motivic.Cohomology.A1.Sheafification.MiddleLift` | Assembly from the simultaneous given image-action relations and actual cover |
| `Motivic.Cohomology.A1.Sheafification.StrictInvariance` | Public strict corollary with the same explicit whole-cylinder input |

The [perfect-field theorem](../README.md) starts from an already-HI Nisnevich
sheaf with transfers. The stronger problem starts from an original
`P : PresheafWithTransfers.{u+1} k` over `k : Type u`, `[Field k]`, with
`P.IsA1Invariant`, and asks for HI of its actual
`G := ((nisnevichSheafify k).obj P).obj`. That step remains OPEN.

The [actual-unit image](../../../Transfers/Presheaf/Sheafification/README.md)
`I` is HI and Nisnevich-separated, with its original factorization and canonical
unit comparison. Dense-open restriction of `G` is injective without assuming
HI of `G`; the final dense-detection statement imposes no perfectness,
connectedness, affineness or integrality condition on its smooth-site target.

## The whole-cylinder input

`ModelWholeCylinderLifting P` takes an integral affine smooth `X` and every
section of `G` on `X × A1`. It supplies an open immersion `U ⟶ X`, `Nonempty U.left`,
and a lift in `I(U × A1)` after the original cylinder restriction. `U` is not
required affine. The whole line over the nonempty original base open is retained;
an arbitrary dense open of the total cylinder is insufficient.

The criterion derives HI of `G` from original coefficient HI and this explicit
input. Additionally `[PerfectField k]` and ordinary `HasExt.{u+1}` on
Nisnevich sheaves with coefficients in `AddCommGrpCat.{u+1}` give the public strict
corollary for the literal original ordinary cohomology projection in every
natural degree, including zero. The native theorem is
`Motivic.PresheafWithTransfers.nisnevichSheafify_isStrictA1Invariant_of_modelWholeCylinderLifting`.
This reduction provides no lifting producer.

## Simultaneous middle relations

The middle-lift assembly has no `hP` argument of its own. It takes the same three
actual correspondences, four simultaneous action identities on `I`, an actual
two-arrow Nisnevich cover, matching representatives and compatible original
base/cylinder maps. It constructs `t := I.transfer λA sA`; it does not assume
`I` is a sheaf. The actual sheaf `G` detects equality on the given cover.

The cover, four identities, and their uniform construction are not supplied.
Original norm actions concern `P.obj.map` and do not by themselves supply these
image-action and whole-cylinder inputs. See the [action guide](../../../Transfers/Presheaf/Actions/README.md).
Curve middle gluing, compatible geometric choices, normalized full-boundary
representatives and the actual action joins remain obligations; boundary Epi
or a correction in the last arrow of a complex does not supply middle exactness.

The [source record](../../../../docs/provenance/support-sensitive-action-20261018/README.md)
separates the supplied four-file historical reduction record from new
production-only/WIP sources and current integration checks. Its historical
origin audit covers image, dense detection and the cylinder criterion, not the
middle-lift or norm-action origins. Hash membership and old production records
do not provide current kernel acceptance or close the stronger theorem.
