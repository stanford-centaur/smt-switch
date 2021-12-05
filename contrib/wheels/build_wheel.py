import os
import re
import sys
import platform
import subprocess
import multiprocessing
import shutil
import glob

from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
from skbuild.cmaker import CMaker
from distutils.version import LooseVersion


class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):
    def run(self):
        try:
            out = subprocess.check_output(['cmake', '--version'])
        except OSError:
            raise RuntimeError(
                "CMake must be installed to build the following extensions: " +
                ", ".join(e.name for e in self.extensions))

        if self.is_windows():
            cmake_version = LooseVersion(
                re.search(r'version\s*([\d.]+)', out.decode()).group(1))
            if cmake_version < '3.1.0':
                raise RuntimeError("CMake >= 3.1.0 is required on Windows")

        for ext in self.extensions:
            self.build_extension(ext)

    @staticmethod
    def is_windows():
        tag = platform.system().lower()
        return tag == "windows"

    @staticmethod
    def is_linux():
        tag = platform.system().lower()
        return tag == "linux"

    def build_extension(self, ext):
        extdir = os.path.abspath(
            os.path.dirname(self.get_ext_fullpath(ext.name)))
        if not os.path.isdir(extdir):
            os.mkdir(extdir)

        cfg = 'Release'
        build_args = ['--config', cfg]

        cpu_count = max(2, multiprocessing.cpu_count() // 2)
        build_args += ['--', '-j{0}'.format(cpu_count)]

        # call configure
        # default install everything?
        solvers = ["bitwuzla", "cvc5", "z3"] # , "msat"]
        solver_path = {"btor": "boolector", "bitwuzla": "bitwuzla", "cvc5": "cvc5", "msat": "mathsat", "z3": "z3"}
        root_path = os.path.dirname(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
        build_dir = os.path.join(root_path, "build")

        for solver in solvers:
            solver_dir = os.path.join(root_path, "deps", solver_path[solver])
            if os.path.isdir(solver_dir):
                continue
            filename = os.path.join(root_path, "contrib", "setup-" + solver + ".sh")
            opts = ["--auto-yes"] if solver == "msat" else []
            subprocess.check_call([filename] + opts)

        # to avoid multiple build, only call reconfigure if we couldn't find the makefile
        # for python
        python_make_dir = os.path.join(build_dir, "python")
        if not os.path.isfile(os.path.join(python_make_dir, "Makefile")):
            args = ["--" + solver for solver in solvers] + ["--python"]
            args.append('-DPYTHON_VERSION_STRING:STRING=' + \
                        sys.version.split(' ')[0])
            python_version = CMaker.get_python_version()
            args.append('-DPYTHON_INCLUDE_DIR:PATH=' + \
                        CMaker.get_python_include_dir(python_version))
            args.append('-DPYTHON_LIBRARY:FILEPATH=' + \
                        CMaker.get_python_library(python_version))
            config_filename = os.path.join(root_path, "configure.sh")
            subprocess.check_call([config_filename] + args)

        # build the main library
        subprocess.check_call(
            ['cmake', '--build', '.', "--target", "smt-switch"] + build_args, cwd=build_dir)
        # build the python binding
        python_build_dir = os.path.join(os.path.join(build_dir, "python"), "smt_switch")
        subprocess.check_call(["make"], cwd=python_build_dir)
        # the build folder gets cleaned during the config, need to create it again
        # this is necessary since "build" is a python dist folder
        if not os.path.isdir(extdir):
            os.mkdir(extdir)
        # copy the library over. we need to consider other users that's not on linux
        lib_files = filter(lambda s: os.path.splitext(s)[1] != '.cxx',
                           glob.glob(os.path.join(python_build_dir, "smt_switch.*")))
        assert lib_files, 'Expecting library files but found none'
        for lib_filename in lib_files:
            print(f'Copying library: {lib_filename}')
            if os.path.splitext(lib_filename)[1] == ".cxx":
                continue
            dst_filename = os.path.join(extdir, os.path.basename(lib_filename))
            shutil.copy(lib_filename, dst_filename)


setup(
    name='smt-switch',
    version='0.2.2',
    author='Makai Mann',
    ext_modules=[CMakeExtension('smt-switch')],
    cmdclass=dict(build_ext=CMakeBuild),
    long_description='python bindings for the C++ solver-agnostic SMT solving library, smt-switch',
    url='http://github.com/makaimann/smt-switch',
    license='BSD',
    tests_require=['pytest'],
    zip_safe=False,
)

