# Overview

This is a smarter automatic binding generator.  It uses program
analysis to infer most of the annotations that would normally be
required for a tool like SWIG.  The analysis frontend, IIGlue, takes
LLVM bitcode as its input.  This bitcode can be produced by either
clang or the dragonegg plugin for gcc.  My
[scripts](https://github.com/travitch/whole-program-llvm) for
generating whole-program LLVM bitcode are useful here.

The analysis currently automatically identifies:

 * Output parameters
 * Array parameters
 * Allocator and finalizer functions
 * Nullable pointers

Many details of the analysis can be found in the
[PLDI 2009 paper](http://pages.cs.wisc.edu/~travitch/pldi-2009/).

# Code Generation

A python ctypes code generator is included: IIGen.  This produces
a single Python file with:

 * Struct type definitions to enable field access
 * Enumeration definitions of symbolic constants
 * A function stub for every function in the library, callable from
   Python

The generated bindings have special treatment for certain C idioms.
Output parameters are fully managed by the bindings and are returned
as multiple return values (wrapped in tuples).  Array parameters can
accept Python lists.  Values returned by allocators are automatically
finalized using `__del__` methods.  Null checks are inserted for
parameters that will cause a crash if they are NULL.

The transformations performed on the code are described in the
docstrings of each function.

# Dependencies / Building

The analysis and code generator are written in Haskell.  Currently, it
requires GHC >= 7.2 (only tested with 7.4.1).  It also depends on LLVM
3.0 and llvm-config must be in your PATH.  The build system is
currently set up to use the LLVM shared libraries (instead of the
static libraries).  The whole-program LLVM compiler wrapper depends on
Python.

A few dependencies are not on [Hackage](http://hackage.haskell.org/packages/hackage.html):

 * llvm-base-types
 * llvm-data-interop
 * llvm-analysis
 * archive-inspection
 * hbgl
 * a forked version of language-python

These are currently only available from my github account.

Installation would look something like:

    REPOSITORIES="hbgl-experimental
    language-python
    archive-inspection
    llvm-base-types
    llvm-data-interop
    llvm-analysis
    foreign-inference"

    # Download the repositories
    for REPO in $REPOSITORIES
    do
        git clone git://github.com/travitch/$REPO.git
    done

    # Add ./ prefixes to each repository (for cabal)
    TOINSTALL=`echo ./$REPOSITORIES  | sed 's: : ./:g'`

    # Build the tools along with dependencies
    cabal install $TOINSTALL

    # Set up the whole-program LLVM wrapper
    git clone git://github.com/travitch/whole-program-llvm.git
    export PATH=$PATH:`pwd`/whole-program-llvm

This will put the `IIGlue` and `IIGen` binaries in `~/.cabal/bin`.
Binaries for i386 and x86_64 Linux are available on my
[research page](http://pages.cs.wisc.edu/~travitch/pldi-2009/).


# Usage

Example:

    tar xf gsl-1.15.tar.gz
    cd gsl-1.15

    # Compile using the whole-program llvm wrapper
    LLVM_COMPILER=clang
    CC=wllvm CFLAGS="-g" ./configure --prefix=`pwd`/root
    make && make install
    extract-bc root/lib/libgsl.so.0.16.0

    # Analyze
    IIGlue --repository=`pwd` root/lib/libgsl.so.0.16.0.bc

    # Generate FFI binding
    IIGen libgsl.so.0.16.0.json > gsl.py

First, the library must be converted to LLVM bitcode.  This example
uses my whole program LLVM wrapper to compile the library twice: once
into a normal binary and once into bitcode (obtained with
`extract-bc`).

Next, the bitcode is analyzed with `IIGlue`.  The `--repository` flag
tells the tool both where to put the summary for the input module,
along with where to find dependency modules.  The output is a summary
of the input module (in this case, `libgsl.so.0.16.0.json`).  Note
that `IIGlue` requires the LLVM `opt` executable to be in your `PATH`.

Finally, the summary is fed to `IIGen` to produce a Python module that
defines wrappers to call library functions.

## Options

The full set of options for `IIGlue` is:

     --dependency=DEPENDENCY   A dependency of the library being analyzed.

This option allows dependencies of a library to be specified.  The
summaries for dependencies are loaded and improve the precision of the
analysis.  Dependencies are specified by the name of the shared
library that the input depends on (e.g., `libcblas.so.0.0.0` is a
dependency for gsl).

     --repository=DIRECTORY    The directory containing dependency summaries.
                               The summary of the input library will be stored
                               here. (Default: consult environment)

This option is required, but may also be set through the environment
variable `INFERENCE_REPOSITORY`.  This option tells the analysis the
directory it should look in to find dependency summaries.  It also
tells the analysis where to write the summary for the input module.

     --diagnostics=DIAGNOSTIC  The level of diagnostics to show (Debug, Info,
                               Warning, Error).  Default: Warning

Control over diagnostic output

     --source=FILE             The source for the library being analyzed
                               (tarball or zip archive).  If provided, a report
                               will be generated

Tell the analysis the source tarball that was used to build the input
library.  This is used to provide detailed reports about the analysis
results, including source lines that led the analysis to report each
of its annotations.   This option is only used if `--reportDir` is
also specified.

     --reportDir=DIRECTORY     The directory in which the summary report will
                               be produced.  Defaults to the REPOSITORY.

Write an HTML report describing the annotations inferred to the given
directory.  If `--source` is also specified, the report includes
hyperlinked breakdowns of individual functions.

     --annotations=FILE        An optional file containing annotations for
                               the library being analyzed

If the analysis cannot infer all of the annotations you think it
should, you can use this option to provide it with some manual
annotations that it will include in its output and analysis.  This is
most useful to annotate complicated allocation functions that the
analysis cannot prove are actually allocators (due to memory pooling,
for example).

The format is the same as the output.

     -? --help                    Display help message



`IIGen` currently does not support any options.  It always writes its
output to standard output.  The modules it generates work with both
Python 2.x and Python 3.x.
