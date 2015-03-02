#!/usr/bin/env python

# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import urllib2
import os
import tarfile
import sys
import platform
import zipfile
import argparse

################################################################################
# Base variables

CWD = os.path.dirname(os.path.abspath(__file__))
BASE_DIR = os.path.join(CWD, ".smt_solvers")
PATHS = []

# Address of a mirror website containing packages to avoid continuous
# downloads from original websites in CI
mirror = os.environ.get('PYSMT_INSTALL_MIRROR')


################################################################################
# Link generators

def get_msat_download_link(archive_name):
    if mirror is not None:
        return mirror + "/" + archive_name
    return "http://mathsat.fbk.eu/download.php?file=%s" % archive_name

def get_z3_download_link(git_version):
    if mirror is not None:
        return mirror + ("/z3-%s.zip" % git_version)
    return "http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=%s" % git_version

def get_cvc4_download_link(git_version):
    if mirror is not None:
        return mirror + ("/cvc4-%s.tar.gz" % git_version)
    return "https://codeload.github.com/CVC4/CVC4/tar.gz/%s" % git_version

def get_yices_download_link(archive_name):
    if mirror is not None:
        return mirror + "/" + archive_name
    return "http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file=%s&accept=I+Agree" % archive_name

def get_pyices_download_link(git_version):
    if mirror is not None:
        return mirror + ("/pyices-%s.tar.gz" % git_version)
    return "https://codeload.github.com/cheshire/pyices/tar.gz/%s" % git_version

def get_pycudd_download_link(archive_name):
    if mirror is not None:
        return mirror + "/" + archive_name
    return"http://bears.ece.ucsb.edu/ftp/pub/pycudd2.0/%s" % archive_name


################################################################################
# Utility functions

def get_architecture_bits():
    """Returns the native word width of this architecture. E.g. 32 or 64"""
    is_64bits = sys.maxsize > 2**32
    if is_64bits:
        return 64
    else:
        return 32

def get_python_version():
    """Returns the current python version as string E.g. '2.7'"""
    return "%d.%d" % sys.version_info[0:2]

def get_architecture():
    """Returns the short name of the architecture in use. E.g. 'x86_64'"""
    return platform.machine()

def untar(fname, directory=".", mode='r:gz'):
    """Extracts the tarfile using the specified mode in the given directory."""
    tfile = tarfile.open(fname, mode)
    tfile.extractall(directory)

def unzip(fname, directory="."):
    """Unzips the given archive into the given directory"""
    with zipfile.ZipFile(fname, "r") as myzip:
        myzip.extractall(directory)

def download(url, file_name):
    """Downloads the given url into the given file name"""
    u = urllib2.urlopen(url)
    f = open(file_name, 'wb')
    meta = u.info()
    if len(meta.getheaders("Content-Length")) > 0:
        file_size = int(meta.getheaders("Content-Length")[0])
        print("Downloading: %s Bytes: %s" % (file_name, file_size))

    block_sz = 8192
    count = 0
    while True:
        buff = u.read(block_sz)
        if not buff:
            break

        f.write(buff)
        if len(meta.getheaders("Content-Length")) > 0 and sys.stdout.isatty():
            count += len(buff)
            perc = (float(count) / float(file_size)) * 100.0
            str_perc = "%.1f%%" % perc
            sys.stdout.write('\r')
            sys.stdout.write(str_perc)
            sys.stdout.write(" " * (10 - len(str_perc)))

    print ""
    f.close()

################################################################################
# Installers

def install_msat(options):
    """Installer for the MathSAT5 solver python interafce"""

    base_name =  "mathsat-5.2.12-linux-%s" % get_architecture()
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    # Download the mathsat release if needed
    if not os.path.exists(archive):
        download(get_msat_download_link(archive_name), archive)

    # clear the destination directory, if any
    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)

    # Extract the MathSAT5 distribution
    untar(archive, BASE_DIR)

    # Build the python wrapper
    os.system('cd %s/python; python setup.py build' % dir_path)

    # Save the paths
    PATHS.append("%s/python" % dir_path)
    PATHS.append("%s/python/build/lib.linux-%s-%s" % (dir_path, get_architecture(), get_python_version()))


def install_z3(options):
    """Installer for the Z3 solver python interafce"""

    git = "cee7dd39444c9060186df79c2a2c7f8845de415b"
    base_name =  "z3"
    archive_name = "%s.zip" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)
    install_path = os.path.join(BASE_DIR, "z3_bin")

    # Download the z3 release if needed
    if not os.path.exists(archive):
        download(get_z3_download_link(git), archive)

    # clear the destination directory, if any
    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)

    # Extract the Z3 distribution
    unzip(archive, dir_path)

    # Creating the path in which z3 will be installed
    if not os.path.exists(install_path):
        os.mkdir(install_path)
    else:
        os.system("rm -rf %s/*" % install_path)

    #Building Z3 and its wrapper
    os.system("cd %s; python scripts/mk_make.py --prefix=%s" % (dir_path, install_path))
    os.system("cd %s/build; make -j%d; make install" % (dir_path, options.make_j))

    # Save the paths
    PATHS.append("%s/lib/python2.7/dist-packages" % install_path)



def install_cvc4(options):
    """Installer for the CVC4 solver python interafce"""

    git = "68f22235a62f5276b206e9a6692a85001beb8d42"
    base_name =  "CVC4-%s" % git
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    # Download the cvc4 release if needed
    if not os.path.exists(archive):
        download(get_cvc4_download_link(git), archive)

    # clear the destination directory, if any
    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)

    # Extract the CVC4 distribution
    untar(archive, BASE_DIR)

    # Patch the distribution to avoid a known problem
    os.system("cd %s; patch -p1 -i %s/patches/cvc4_wrapper.patch" % (dir_path, CWD))

    # Prepare the building system
    os.system("cd %s; bash autogen.sh;" % dir_path)
    # Build ANTLR
    os.system("cd %s/contrib; bash get-antlr-3.4;" % dir_path)
    # Configure and build CVC4
    os.system("cd %s; \
    ./configure --enable-language-bindings=python \
                --with-antlr-dir=%s/antlr-3.4 ANTLR=%s/antlr-3.4/bin/antlr3;\
    make -j%d" % (dir_path, dir_path, dir_path, options.make_j))
    # Fix the paths of the bindings
    os.system("cd %s/builds/src/bindings/python; mv .libs/CVC4.so.3.0.0 ./_CVC4.so" % dir_path)

    # Save the paths
    PATHS.append("%s/builds/src/bindings/python" % dir_path)



def install_yices(options):
    """Installer for the Yices solver python interafce"""

    base_name =  "yices-2.3.0"
    archive_name = "%s-%s-unknown-linux-gnu-static-gmp.tar.gz" % (base_name, get_architecture())
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)
    yices_path = os.path.join(BASE_DIR, "yices_bin")

    # Download the yices release if needed
    if not os.path.exists(archive):
        download(get_yices_download_link(archive_name), archive)

    # clear the destination directory, if any
    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)

    # Extract the Yices distribution
    untar(archive, BASE_DIR)

    # Prepare an empty folder for installing yices
    if not os.path.exists(yices_path):
        os.mkdir(yices_path)
    else:
        os.system("rm -rf %s" % yices_path)

    # Install Yices in 'yices_path'
    os.system("cd %s; ./install-yices %s" % (dir_path, yices_path))

    # pyices
    pyices_git = "aa0b91c39aa00c19c2160e83aad822dc468ce328"
    pyices_base_name =  "pyices-%s" % pyices_git
    pyices_archive_name = "%s.tar.gz" % pyices_base_name
    pyices_archive = os.path.join(BASE_DIR, pyices_archive_name)
    pyices_dir_path = os.path.join(BASE_DIR, pyices_base_name)

    # Download pyices if needed
    if not os.path.exists(pyices_archive):
        download(get_pyices_download_link(pyices_git), pyices_archive)

    # clear the destination directory, if any
    if os.path.exists(pyices_dir_path):
        os.system("rm -rf %s" % pyices_dir_path)

    # Extract the pyices distribution
    untar(pyices_archive, BASE_DIR)

    # Build pyices
    os.system("export YICES_PATH=\"%s\"; cd %s; python setup.py install --user" % (yices_path, pyices_dir_path))

    # Save the paths
    PATHS.append("%s/build/lib.linux-%s-%s" % (pyices_dir_path, get_architecture(), get_python_version()))



def install_pycudd(options):
    """Installer for the CUDD library python interafce"""

    base_name =  "pycudd2.0.2"
    archive_name = "%s.tar.gz" % base_name
    archive = os.path.join(BASE_DIR, archive_name)
    dir_path = os.path.join(BASE_DIR, base_name)

    # Download pycudd if needed
    if not os.path.exists(archive):
        download(get_pycudd_download_link(archive_name), archive)

    # clear the destination directory, if any
    if os.path.exists(dir_path):
        os.system("rm -rf %s" % dir_path)

    # Extract the pycudd distribution
    untar(archive, BASE_DIR)

    # patch the distribution
    os.system("cd %s; patch -p1 -i %s/patches/pycudd.patch" % (dir_path, CWD))

    # Select the correct Makefile to be used
    makefile = "Makefile"
    if get_architecture_bits() == 64:
        makefile = "Makefile_64bit"

    # Build the pycudd
    # NOTE: -j is not supported by this building system
    os.system("cd %s/cudd-2.4.2; ./setup.sh; make -f %s" % (dir_path, makefile))
    os.system("cd %s/cudd-2.4.2; make -f %s libso" % (dir_path, makefile))
    os.system("cd %s/pycudd; make" % dir_path)

    # Save the paths
    PATHS.append("%s/pycudd" % dir_path)

def check_install():
    """Checks which solvers are visible to pySMT."""

    from pysmt.shortcuts import Solver
    from pysmt.exceptions import NoSolverAvailableError

    required_solver = os.environ.get("PYSMT_SOLVER")
    if required_solver is None:
        required_solver = "None"

    for solver in ['msat', 'z3', 'cvc4', 'yices', 'bdd']:
        is_installed = False
        try:
            Solver(name=solver)
            is_installed = True
        except NoSolverAvailableError:
            is_installed = False
        print("%s: \t %s" % (solver, is_installed))

        if solver == required_solver and not is_installed:
            raise Exception("Was expecting to find %s installed" % required_solver)


def parse_options():
    parser = argparse.ArgumentParser(description='Install SMT Solvers')
    parser.add_argument('--z3', dest='z3', action='store_true',
                        default=False, help='Install Z3')
    parser.add_argument('--msat', dest='msat', action='store_true',
                        default=False, help='Install MathSAT')
    parser.add_argument('--cvc4', dest='cvc4', action='store_true',
                        default=False, help='Install CVC4')
    parser.add_argument('--yices', dest='yices', action='store_true',
                        default=False, help='Install Yices')
    parser.add_argument('--cudd', dest='cudd', action='store_true',
                        default=False, help='Install CUDD (pycudd)')
    parser.add_argument('--make-j', dest='make_j', metavar='N',
                        type=int, default=1,
                        help='Define paralellism for make (Default: 1)')
    parser.add_argument('--check', dest='check', action='store_true',
                        default=False,
                        help='Checks the installation of the solvers')
    parser.add_argument('--confirm-agreement', dest='skip_intro',
                        action='store_true', default=False,
                        help='Confirm that you agree with the licenses of the\
                        solvers and skip the interactive question')

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    options = parser.parse_args()
    return options


################################################################################
# Main functions

def print_welcome():
    msg = """\
This script allows you to install the solvers supported by pySMT.

By executing this script, you confirm that you have read and agreed
with the licenses of each solver.

Notice: the installation process might require building tools
        (e.g., make and gcc).
"""
    print(msg)
    res = raw_input("Continue? [Y]es/[N]o: ").lower()

    if res != "y":
        exit(-1)


def main():
    options = parse_options()

    # If checking only the installation, we exit immediately
    if options.check:
        check_install()
        exit(0)

    if not options.skip_intro:
        print_welcome()

    # create install folder if needed
    if not os.path.exists(BASE_DIR):
        os.mkdir(BASE_DIR)

    if options.z3:
        install_z3(options)

    if options.cvc4:
        install_cvc4(options)

    if options.msat:
        install_msat(options)

    if options.yices:
        install_yices(options)

    if options.cudd:
        install_pycudd(options)

    print("\n")
    print("*" * 80)
    print("Add the following to your .bashrc file or to your environment:")
    print("export PYTHONPATH=\"$PYTHONPATH:"+ ":".join(PATHS) + "\"")

    with open(os.path.join(BASE_DIR, "set_paths.sh"), "a") as fout:
        fout.write("export PYTHONPATH=\"$PYTHONPATH:"+ ":".join(PATHS) + "\"")


if __name__ == "__main__":
    main()
