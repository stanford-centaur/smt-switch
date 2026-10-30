# The default bison on macOS is too old, so we try installing one from Homebrew.
get_property(_explicit_roots GLOBAL PROPERTY SMT_SWITCH_EXPLICIT_ROOTS)
if(APPLE AND NOT BISON IN_LIST _explicit_roots)
  execute_process(
    COMMAND brew --prefix
    OUTPUT_VARIABLE _homebrew_prefix
    RESULT_VARIABLE _brew_result
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET
  )
  if(_brew_result EQUAL 0)
    list(APPEND BISON_ROOT "${_homebrew_prefix}/opt/bison")
  endif()
endif()
smt_switch_provision_if_missing(BISON bison 3.7.0)
find_package(BISON 3.7.0 REQUIRED)
find_package(FLEX 2.6.4 REQUIRED)
smt_switch_check_root(FLEX)

bison_target(
  SmtLibParser
  "${CMAKE_CURRENT_SOURCE_DIR}/src/smtlib_parser.yy"
  "${CMAKE_CURRENT_BINARY_DIR}/smtlib_parser.cpp"
  DEFINES_FILE "${CMAKE_CURRENT_BINARY_DIR}/smtlib_parser.h"
)

flex_target(
  SmtLibScanner
  "${CMAKE_CURRENT_SOURCE_DIR}/src/smtlib_scanner.l"
  "${CMAKE_CURRENT_BINARY_DIR}/smtlib_scanner.cpp"
  DEFINES_FILE "${CMAKE_CURRENT_BINARY_DIR}/smtlib_scanner.h"
)

add_flex_bison_dependency(SmtLibScanner SmtLibParser)

# bison's skeleton sets yynerrs_ without reading it.
set_source_files_properties(
  ${BISON_SmtLibParser_OUTPUTS}
  PROPERTIES COMPILE_OPTIONS -Wno-unused-but-set-variable
)
# These warnings are triggered on the flex-generated sources.
set_source_files_properties(
  ${FLEX_SmtLibScanner_OUTPUTS}
  PROPERTIES COMPILE_OPTIONS "-Wno-sign-compare;-Wno-extra-semi-stmt;-Wno-unused-function"
)

add_library(
  smt-switch-smtlib
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/smtlib_reader.cpp"
  ${BISON_SmtLibParser_OUTPUTS}
  ${FLEX_SmtLibScanner_OUTPUTS}
)
target_include_directories(
  smt-switch-smtlib
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
# The parser headers bison and flex generate are used by the reader's sources.
target_include_directories(smt-switch-smtlib PRIVATE "${CMAKE_CURRENT_BINARY_DIR}")

target_link_libraries(smt-switch-smtlib PUBLIC smt-switch)

add_library(SmtSwitch::smt-switch-smtlib ALIAS smt-switch-smtlib)
install(TARGETS smt-switch-smtlib EXPORT SmtSwitchSmtLibTargets DESTINATION lib)
install(EXPORT SmtSwitchSmtLibTargets NAMESPACE SmtSwitch:: DESTINATION "${SMT_SWITCH_CMAKE_DIR}")
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
