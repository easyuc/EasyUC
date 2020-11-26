The subdirectory ECsrc contains a copy of the EasyCrypt source (src)
directory.

The files in this directory beginning with ec* are EasyCrypt source
files that have been modified from the originals. The original
files can be found in ECsrc/modified-for-ucdsl.

- - - - -

The bash shell script ec-diff can be used to (run it with no
arguments):

* check whether any files in ECsrc, ECsrc/phl and ECsrc/system are
  different from the corresponding files of the current EasyCrypt src
  directory

* check whether the original versions of the ec* files in this
  directory that were saved in ECsrc/modified-for-ucdsl are the same
  as the corresponding files in the current EasyCrypt src directory

* do a diff of each of these ec* files with their original version
