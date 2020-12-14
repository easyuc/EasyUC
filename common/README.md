EasyUC Common Files
================================================================================

All EasyUC developments should `require` `UCCore.ec`, which consists of
core UC definitions and lemmas. It `require export`s (directly or
indirectly):

* `UCEncoding.ec` - Encoding and Partial Decoding Pairs (EPDPs)

* `UCUniv.ec` - universe of values (lists of booleans), plus EPDPs

* `UCBasicTypes.ec` - `require export`s `UCEncoding.ec` and `UCUniv.ec`,
  and defines types of addresses and ports

* `UCListPO.ec` - prefix ordering on lists

The directory also contains:

* `UCListAux.ec` - auxiliary lemmas on lists
