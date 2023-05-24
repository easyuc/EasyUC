UC DSL Prelude
================================================================================

When a UC DSL specification does `ec_requires` and `uc_requires`, this
prelude directory is always searched first when looking for `.ec`
and `.uc` files.

The files `WF.ec`, `UCEncoding.ec`, `UCListAux.ec`, `UCListPO.ec`,
`UCUniv.ec` and `UCBasicTypes.ec` are symbolic links to those files in
`../Common`.

`UCBasicTypes.ec` is `ec_required` last when processing UC DSL files.
