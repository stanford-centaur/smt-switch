#[=======================================================================[.rst:
ImportedLocation
----------------

Reads the file behind an imported library at configure time.

.. command:: smt_switch_imported_location

  .. code-block:: cmake

    smt_switch_imported_location(<target> <out-var>)

  Sets ``<out-var>`` to the path of the library file that ``<target>``
  imports.

  ``$<TARGET_FILE:...>`` would normally be the way to ask this, but it is a
  generator expression, and two callers here need a plain string: the static
  repacking hands file names to a shell script, and ``python/setup.py.in`` is
  filled in by :command:`configure_file`, which runs before generation.

  Imported targets that come from a package's own export file carry their
  location under a configuration suffix, and the configuration a package was
  built in need not be the one we are building.  cvc5 exports only
  ``PRODUCTION`` and Boolector only ``RELEASE``, while smt-switch defaults to
  ``Release`` and can be configured as ``Debug``.  This falls back to the
  first exported configuration rather than insisting on a match, which is
  what these single-configuration packages need.

#]=======================================================================]

function(smt_switch_imported_location target out_var)
  get_target_property(_location "${target}" IMPORTED_LOCATION)
  if(NOT _location)
    get_target_property(_configurations "${target}" IMPORTED_CONFIGURATIONS)
    if(_configurations)
      string(TOUPPER "${CMAKE_BUILD_TYPE}" _build_type)
      if(NOT _build_type IN_LIST _configurations)
        list(GET _configurations 0 _build_type)
      endif()
      get_target_property(_location "${target}" IMPORTED_LOCATION_${_build_type})
    endif()
  endif()
  if(NOT _location)
    message(FATAL_ERROR "Could not determine the library file behind ${target}")
  endif()
  set("${out_var}" "${_location}" PARENT_SCOPE)
endfunction()
