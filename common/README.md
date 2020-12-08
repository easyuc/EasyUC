EasyUC Common Files
================================================================================

All EasyUC developments should `require` `UCCore.ec`, which consists of
core UC definitions and lemmas. It `require export`s:

* `UCEncoding.ec` - Encoding and Partial Decoding Pairs (EPDPs)

* `UCUniv.ec` - universe of values (lists of booleans), plus EPDPs
