EasyUC Common Files
================================================================================

All EasyUC developments should `require` `UCCore.ec`, which consists of
core UC definitions and lemmas, including the proof of the dummy
adversary theorem.

It `require export`s (directly or indirectly):

* `UCEncoding.ec` - Encoding and Partial Decoding Pairs (EPDPs)

* `UCUniv.ec` - universe of values (lists of booleans), plus EPDPs

* `UCBasicTypes.ec` - `require export`s `UCEncoding.ec` and `UCUniv.ec`,
  and defines types of addresses, ports and messages

* `UCListPO.ec` - prefix ordering on lists

The directory also contains:

* `UCListAux.ec` - auxiliary lemmas on lists

* `UCComposition.ec` - proof of the composition theorem

There is also a shell script `check-all-scripts` for checking all
theories using two SMT provers: Alt-Ergo and Z3. It uses a default SMT
timeout of 2 seconds, but takes the timeout as an optional command
line argument.  The scripts check using versions 2.6.0 of Alt-Ergo and
4.15.3 of Z3.  If you use later versions of these provers and an
up-to-date version of EasyCrypt, feel free to report any script
failures.
