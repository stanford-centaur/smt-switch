# Python_add_library and the Development.Module component, which leaves out
# the libpython that manylinux does not ship, are both newer than the rest of
# this tree needs.
if(CMAKE_VERSION VERSION_LESS 3.18)
  message(FATAL_ERROR "The Python bindings need CMake 3.18 or newer; this is ${CMAKE_VERSION}")
endif()

# The floor has to match requires-python in pyproject.toml: a wheel built
# against an older interpreter is one that pip then refuses to install.
# An active virtualenv or conda environment is preferred by FindPython itself.
find_package(Python 3.10 REQUIRED COMPONENTS Interpreter Development.Module)

include(CheckPythonModule)
check_python_module("Cython" 3.0.0)

# The C++ Cython generates does not build clean under the project's warnings,
# and is not ours to change.
smt_switch_drop_warning_options(original_options)

# Puts the copied and the generated Cython sources together in the package
# directory, as Cython finds the package a module belongs to by its directory.
add_subdirectory(smt_switch)
set(package_dir "${CMAKE_CURRENT_BINARY_DIR}/smt_switch")

# Each .pyx is a module, the generated one included. Every module cimports
# from the declarations, so any of them changing regenerates them all.
set(modules smt_solvers)
set(declarations "${package_dir}/smt_solvers.pxd")
foreach(source IN LISTS CYTHON_SOURCE_FILES)
  get_filename_component(name "${source}" NAME)
  get_filename_component(stem "${source}" NAME_WE)
  if(name MATCHES "\\.pyx$")
    list(APPEND modules "${stem}")
  elseif(name MATCHES "\\.pxd$")
    list(APPEND declarations "${package_dir}/${name}")
  endif()
endforeach()

foreach(module IN LISTS modules)
  add_custom_command(
    OUTPUT "${package_dir}/${module}.cpp"
    COMMAND
      "${Python_EXECUTABLE}" -m cython --cplus -3 -X binding=False -X embedsignature=True -o
      "smt_switch/${module}.cpp" "smt_switch/${module}.pyx"
    DEPENDS "${package_dir}/${module}.pyx" ${declarations}
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    COMMENT "Cythonizing smt_switch/${module}.pyx"
    VERBATIM
  )
  python_add_library(smt-switch-python-${module} MODULE WITH_SOABI "${package_dir}/${module}.cpp")
  set_target_properties(
    smt-switch-python-${module}
    PROPERTIES
      OUTPUT_NAME "${module}"
      LIBRARY_OUTPUT_DIRECTORY "${package_dir}"
      # Finds the solver libraries this was linked against outside the build
      # tree once installed.
      INSTALL_RPATH_USE_LINK_PATH ON
  )
  target_link_libraries(smt-switch-python-${module} PRIVATE smt-switch)
endforeach()
target_link_libraries(smt-switch-python-smt_solvers PRIVATE ${SOLVER_BACKEND_LIBS})

# A shared build installs the libraries the modules load into the package as
# well, so that the package is complete wherever it goes: in a virtualenv
# without the rest of the install, and in a wheel, which the repair tools
# fill only with what the package itself can find.
if(SMT_SWITCH_LIB_TYPE STREQUAL "SHARED")
  set(package_libraries smt-switch ${SOLVER_BACKEND_LIBS})
  foreach(module IN LISTS modules)
    set_target_properties(
      smt-switch-python-${module}
      PROPERTIES INSTALL_RPATH "${SMT_SWITCH_RPATH_ORIGIN}"
    )
  endforeach()
endif()

# scikit-build-core, which builds the wheels, says where the package goes.
# Otherwise it is the site-packages of the Python found above.
if(SKBUILD)
  set(SMT_SWITCH_PYTHON_INSTALL_DIR "${SKBUILD_PLATLIB_DIR}")
else()
  set(
    SMT_SWITCH_PYTHON_INSTALL_DIR
    "${Python_SITEARCH}"
    CACHE PATH
    "Where to install the Python bindings"
  )
endif()

set(installed_files "")
foreach(declaration IN LISTS declarations)
  get_filename_component(name "${declaration}" NAME)
  list(APPEND installed_files "smt_switch/${name}")
endforeach()
install(
  FILES "${package_dir}/__init__.py" ${declarations}
  DESTINATION "${SMT_SWITCH_PYTHON_INSTALL_DIR}/smt_switch"
  COMPONENT python
)
list(APPEND installed_files "smt_switch/__init__.py")
foreach(module IN LISTS modules)
  install(
    TARGETS smt-switch-python-${module}
    LIBRARY DESTINATION "${SMT_SWITCH_PYTHON_INSTALL_DIR}/smt_switch" COMPONENT python
  )
  list(APPEND installed_files "smt_switch/$<TARGET_FILE_NAME:smt-switch-python-${module}>")
endforeach()
if(SMT_SWITCH_LIB_TYPE STREQUAL "SHARED")
  install(
    TARGETS ${package_libraries}
    LIBRARY DESTINATION "${SMT_SWITCH_PYTHON_INSTALL_DIR}/smt_switch" COMPONENT python
  )
  foreach(library IN LISTS package_libraries)
    list(APPEND installed_files "smt_switch/$<TARGET_FILE_NAME:${library}>")
  endforeach()
endif()
file(GLOB frontend_sources "${CMAKE_CURRENT_SOURCE_DIR}/smt_switch/pysmt_frontend/*.py")
install(
  FILES ${frontend_sources}
  DESTINATION "${SMT_SWITCH_PYTHON_INSTALL_DIR}/smt_switch/pysmt_frontend"
  COMPONENT python
)
foreach(source IN LISTS frontend_sources)
  get_filename_component(name "${source}" NAME)
  list(APPEND installed_files "smt_switch/pysmt_frontend/${name}")
endforeach()

# What lets pip see the package, uninstall it, and replace it with a wheel.
# Only the name and version: the rest of the metadata is for PyPI, and lives
# in pyproject.toml. scikit-build-core writes its own into the wheel.
if(NOT SKBUILD)
  set(dist_info "smt_switch-${PROJECT_VERSION}.dist-info")
  set(dist_info_dir "${CMAKE_CURRENT_BINARY_DIR}/${dist_info}")
  file(
    WRITE "${dist_info_dir}/METADATA"
    "Metadata-Version: 2.1\nName: smt-switch\nVersion: ${PROJECT_VERSION}\n"
  )
  file(WRITE "${dist_info_dir}/INSTALLER" "cmake\n")
  list(
    APPEND installed_files
    "${dist_info}/METADATA"
    "${dist_info}/INSTALLER"
    "${dist_info}/RECORD"
  )
  # Paths with neither hash nor size, which a RECORD of an installed package
  # may leave out
  list(TRANSFORM installed_files APPEND ",,")
  list(JOIN installed_files "\n" record)
  file(GENERATE OUTPUT "${dist_info_dir}/RECORD" CONTENT "${record}\n")

  # One installed with another version would otherwise stay beside this one.
  install(
    CODE "set(smt_switch_python_install_dir [[${SMT_SWITCH_PYTHON_INSTALL_DIR}]])"
    COMPONENT python
  )
  install(
    CODE
      [[
        file(GLOB stale_dist_infos "$ENV{DESTDIR}${smt_switch_python_install_dir}/smt_switch-*.dist-info")
        if(stale_dist_infos)
          file(REMOVE_RECURSE ${stale_dist_infos})
        endif()
      ]]
    COMPONENT python
  )
  install(
    DIRECTORY "${dist_info_dir}"
    DESTINATION "${SMT_SWITCH_PYTHON_INSTALL_DIR}"
    COMPONENT python
  )
endif()
