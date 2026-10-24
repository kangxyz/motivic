> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#source-and-log-evidence) · [Context](original-context.md) · [Case index](README.md) · [Previous record](reuse-the-build-environment.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Source and log evidence

The retained receipts and `build.log` files are under
`/private/tmp/r5-investigations/motivic-ci-latest-20261021/root/`, with remote
copies under `/root/autodl-tmp/lean-build/logs/`. The table reuses these existing
measurements; no additional benchmark runs were requested for this guide.

| Run suffix after `remote-` | Source content SHA-256 | Scope |
| --- | --- | --- |
| `7d6f481b8525470286fd6ddc61abb8d6` | `22ccedfef9a95161496a180d8eeb46d9554f8596b681c6561e5f5c6137d06915` | Source/puncture baseline jobs passed; the enclosing run was later stopped |
| `b2bec531bd8d48d7b1bf439044ae5fbb` | `e0fdb0e38b13460d233ee2dee0ed55a1c427b13c6f72a2e394f9d57c33e31255` | Source job passed in 97 seconds; the enclosing run later timed out |
| `f4e45397b5f848cfbed7799758a01637` | `a13e07c7dcf9465c0f5525d892e21d25fa3d78e4770bce317b84e93098005863` | Source job passed in 96 seconds; the enclosing run was later stopped |
| `4a2c5ba14f864f48ae9abf37d50893f0` | `a09da017b566d807cde9c5359434e72b53f127d1e713dd612ef040f75739e67e` | Selected puncture and cover passed |
| `b38006877ae840e7bc8824c16bee9f72` | `a09da017b566d807cde9c5359434e72b53f127d1e713dd612ef040f75739e67e` | Pre-history-refactor library and package tests passed; history baseline times |
| `437211be4722480796277767eed3fe56` | `1599c245b700b5b7d675d6d21f6d4bf231507e867883ba372b21ea393add8a9e` | Rewritten line/restriction jobs passed; a separate draft middle proof failed |
| `6736b4a518924c80a4c64287b14eb302` | `75bc5aa1e6d41c66dfd69123c4ca457c478e38bedf57bd1849dc3b8e27ac047d` | Repaired middle relations and both lifting consumers passed |
| `52b2c5b89ae24fa28cffd6f5ba4b63da` | `550d67a4fafa3fea72646a88420ad52acf36f817e8dcc73269d51db29e22ae06` | Parent-record constructor variant passed in 294 seconds; not retained |
| `e54ab7cb8cc24d0e98116273a0160eb3` | `b7efba89a37d59701de2d6862008f8ed20952b0a3a95f0e826d0be2e93f81d49` | Witness-choice variant passed in 319 seconds and package tests passed; not retained |
| `84428111c0744095901a65dd5125e7ad` | `75bc5aa1e6d41c66dfd69123c4ca457c478e38bedf57bd1849dc3b8e27ac047d` | Native text style passed; separate diagnostic timed out and is not acceptance evidence |
| `95df3fc6263f42f3b1d78b428daa2120` | `395417e19b32e9ec4e4b7b68a60bc01a16ed44ea9d56c4b8d7a5b9681e3ad237` | Retained supplier abstraction: Line 51, Restrictions 5.8, HistoryLifting 36 and WholeCylinderLifting 141 seconds; affected build passed |
| `fede19f54895450987a8a984342dfe57` | `395417e19b32e9ec4e4b7b68a60bc01a16ed44ea9d56c4b8d7a5b9681e3ad237` | Final incremental library/package tests, generated entry, native text style, shared declaration lint and builtin lint all passed |

The history baseline is preserved with per-file hashes in the recovery-copy
index. The [integration record](../provenance/hi-presheaf-sheafification-20261020/README.md#abstract-history-refactor)
owns final check status. A successful individual module in an interrupted or
failed enclosing run is not a successful whole-run or CI result.
