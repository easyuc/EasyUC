UC DSL Prelude
================================================================================

When a UC DSL specification does `ec_requires` and `uc_requires`, this
prelude directory is always searched first when looking for `.ec`
and `.uc` files.

The files `UCEncoding.ec` and `UCUniv.ec` are symbolic links to those files
in `../Common`.

The file `UCBasicTypes.ec` is a more abstract version of
`../common/UCBasicTypes.ec`, in which `port` is an abstract type.
