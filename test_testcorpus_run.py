#!/usr/bin/env python3

"""Compare "compiler" package output against reference data produced
by test_testcorpus_prepare.py.

usage: {PROG} [ -h ] [ -v ] [ testfile ... ]

-v - produce more verbose output
-h - print usage info and exit

If no test files are given on the command line, all files matching
testcorpus/*.py are run.
"""

import getopt
import glob
import os
from subprocess import check_call, CalledProcessError
import sys

PROG = os.path.basename(sys.argv[0])

def main():
    args = sys.argv[1:]
    verbose = False
    opts, args = getopt.getopt(args, "vh")
    for opt, _arg in opts:
        if opt == "-v":
            verbose = True
        elif opt == "-h":
            usage()
            return 0

    runs = failures = passes = 0

    testfiles = sorted(sys.argv[1:])
    if not testfiles:
        testfiles = sorted(glob.glob("testcorpus/*.py"))

    try:
        for testfile in testfiles:
            print(testfile, end=" ", file=sys.stderr)
            runs += 1
            try:
                check_call("./python3.5-nopeephole compiler_runtest.py"
                           f" {testfile} > {testfile}.out",
                           shell=True)
            except CalledProcessError as exc:
                print("FAIL", file=sys.stderr)
                if verbose:
                    print(exc, file=sys.stderr)
                failures += 1
                continue
            try:
                check_call(f"diff -u {testfile}.exp {testfile}.out", shell=True)
            except CalledProcessError as exc:
                print("FAIL", file=sys.stderr)
                if verbose:
                    print(exc, file=sys.stderr)
                failures += 1
            else:
                print("PASS", file=sys.stderr)
                passes += 1
    finally:
        print("tests:", runs, "passes:", passes, "failures:", failures)

    return failures

def usage():
    print(__doc__.format(**globals()).strip(), file=sys.stderr)

if __name__ == "__main__":
    sys.exit(main())
