# UCDSL Testsuite

UCDSL Testsuite is a software for dealing with UCDSL tests

## Installation

Use the Makefile that comes with the testsuite
To build the test suite use go to directory with Makefile and use
the following command.

```bash
make
```

## Usage

```bash

Usage: dsl-test [verbosity option] dir
dsl-test -debug file
  -verbose Verbosity option: enables verbose mode
  -quiet Verbosity option: enables quiet mode
  -debug Prints debug information of a TEST file
  -help  Display this list of options
  --help  Display this list of options

```

## Requirements

For the debug option there are pretty much no restrictions.
However for running the tests there are cetain conditions.

## 1. TEST File
Each test should be accompanaid by a 'TEST' file. Here TEST
refers to the name of the file, which should be in the same directory
as the test together with all the required files appropriately placed.

### Contents of TEST
Every TEST file can have 3 fields. description, args, outcome and comments.
'(*' marks the begining of the comments and '*)' marks the end of the comments.
Nested comments are allowed.

However there are certain conditions on where comments can appear.
These conditions are mentioned as in the sections below.

#### description
As the name suggests description contains description about the test.
This will be printed on screen and logged in verbose mode only.
The syntax for description is as follows

```
description (* optional comments *)
The description of the test goes here, (*, *) and any text between these
symbols will be considered as the part of the description.
.

```

To explain a bit, the description of the test starts in a new line after
the keyword description and any comments. These comments can span multiple lines
but the actual description of the test should start in a new line.

A ".\n" marks the end of the description.


#### args
args syntax
```

args (*comments *): options filename.uc

```

Comments are not allowed after ":"

####outcome

```

outcome (*comments *): success/failure
Error message incase of failure
.

```

Like description the outcome description(or error message) should start in
a new line after success/failure. The error message has to be exact replica
of the error message UCDSL outputs. Like in the case of args, no comments are
allowed after ":"

### Directory structure

The acceptable content of a director are                                                                                                                                                                 
  | TEST file + contents + optional sub directories                                                                                                                                                  
   | If a TEST file is found, subfolders will be ignored                                                                                                                                              
  | Files with names starting with readme ONLY + optional sub directories                                                                                                                             
   | Only sub folders will be searched for TEST files/tests                                                                                                                                           
  | No files but sub directories                                                                                                                                                                      
   | All subdirectories will be searched for TEST files/tests                                                                                                                                         
  | Any others will be ignored and an error message will be logged. 




