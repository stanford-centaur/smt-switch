#[=======================================================================[.rst:
CompilerWarnings
----------------

Turns on every warning both compilers offer that this tree can act on.

Each flag is named here one by one rather than pulled in by a group, so that
upgrading a compiler warns about nothing the list has not already accepted.  One
list serves GCC and clang: every flag is filtered against what the compiler in
use reports it accepts, so the ones it has never heard of cost nothing.  Being
listed is not quite acceptance -- GCC lists flags it then refuses for a C++
translation unit -- so a second pass drops whatever it names when handed the
surviving set.

A flag commented out is one that fires today.  Fix what it reports, delete the
two comment characters, and nothing else about the line changes.  A group
containing such a flag is commented out as well, and a flag that fires on either
compiler is held back for both -- giving up a little coverage on the one where
the tree is already clean, in exchange for a single list.

The note after each flag is the compiler's own account of it: GCC's
``--help=warnings`` wording where GCC has the flag, otherwise the message clang
prints, shortened to the line and with its placeholders named ``X``, ``Y``,
``Z``.  Umbrella flags describe themselves circularly and are written out here
by hand.

``-Werror`` is added when ``SMT_SWITCH_STRICT`` is on, which is what
``configure.sh --strict`` sets: everyone is told, only a build that asks is
stopped.  The option is declared beside the ``include()`` in the top-level
``CMakeLists.txt``, so that reading that file is enough to find it.

Omissions
^^^^^^^^^

Flags reporting that C++17 code is not valid in an older standard are left out,
that being the point of pinning the standard: the ``-Wc++98-compat``,
``-Wc++11-compat``, ``-Wc++14-compat``, ``-Wc++17-compat`` and
``-Wpre-c++17-compat`` families, along with ``-Wbinary-literal`` and
``-Wlocal-type-template-args``, which say the same of one construct each.  So
are the ``-Wc++NN-extensions`` flags for NN up to 17, which fire only when the
standard in use is older than the feature.  Note that c++0x, c++1y and c++1z
were the working names for C++11, C++14 and C++17, so those spellings are the
same flags again.  Flags about *newer* standards are kept, as is
``-Wc++11-narrowing``, whose name says c++11 but whose subject is ordinary C++17
code.

Some flags fire only under an older standard without their name saying so,
C++17 either accepting what they report or reporting it under another flag:
``-Wlong-long``, ``-Wconstexpr-not-const``, ``-Wnoexcept-type``,
``-Wdeprecated-increment-bool`` and ``-Wdeprecated-register``, the last two
superseded by ``-Wincrement-bool`` and ``-Wregister``.  These are left out too,
as are the two ``-Wc++11-compat`` flags about writable string literals and
reserved literal suffixes, which fire only under C++98 and whose C++17
counterparts are ``-Wwrite-strings`` and ``-Wreserved-user-defined-literal``.

Whole families that cannot fire here are left out too: Objective-C and ARC,
OpenMP and OpenACC, CUDA, HIP, OpenCL and SYCL, targets this project is not
built for, MSVC compatibility mode, clang modules, nullability attributes, and
warnings only C has -- the flags are attached to ``CXX`` sources alone.  GCC's
``-Wanalyzer-`` family says nothing without ``-fanalyzer``.
``-Waggregate-return``, ``-Wnamespaces``, ``-Wtemplates``,
``-Wmultiple-inheritance`` and ``-Wvirtual-inheritance`` enforce a restricted
C++ subset this tree does not follow, which GCC documents as their purpose;
``-Wabi-tag`` is for shipping both libstdc++ ABIs at once, and ``-Wpadded``
treats padding as a defect rather than a layout choice.  ``-Wabi`` is out
because without a version to compare against GCC rejects it outright, and
``-Wpoison-system-directories`` because it reports an include path unsafe for
cross-compilation, which describes where Homebrew puts things.

So are flags with no diagnostic behind them on *either* compiler: clang keeps a
number of groups that are empty, and GCC documents a few of its own as doing
nothing.  A flag empty on one compiler is often real on the other, so this
applies only where neither can report through it.  Neither needs compiling to
find: GCC prints "Does nothing" as the description of such a flag, and clang's
groups are tabulated in ``clang/Basic/DiagnosticGroups.inc``, which its
development headers install.

A flag needing a compiler mode this project does not build with is kept when
that mode is one a build here could plausibly turn on: the coverage, profile-use
and ``-flto`` flags stay, while the precompiled-header ones are gone.

Spellings
^^^^^^^^^

Where two spellings name the same warning, only one is listed, preferring the
one both compilers accept: hence ``-Wmissing-noreturn`` over its GCC-only
synonym ``-Wsuggest-attribute=noreturn``, and ``-Wnarrowing`` over clang's
``-Wc++11-narrowing``.  Failing that, clang's canonical group name is kept,
since that is the name it prints in brackets after the diagnostic.  One pair is
deliberately left doubled: clang makes ``-Weffc++`` an alias for
``-Wnon-virtual-dtor``, while on GCC the two are separate flags.

Which flags are synonyms has to be worked out again for each compiler release.
GCC names its own outright under ``-Q --help=warnings``, while in clang's
``DiagnosticGroups.inc`` a group with no diagnostics of its own and a single
subgroup is an alias for that subgroup.

Levels
^^^^^^

A flag taking a level is asked for the level that reports the most, a default
being chosen to be quiet rather than thorough: ``-Wstringop-overflow=4`` over
the default of 2, ``-Wcatch-value=3`` over 1.  The levels are cumulative, each
also warning about what the one below it does -- except ``-Wstrict-aliasing``,
which runs the other way, level 1 reporting the most and 3 the least.

Clang accepts no levelled spelling, so where it has the flag at all the plain
spelling stays on its own line for clang while the levelled one is added for
GCC.  Both reaching GCC is deliberate: the last level on the command line is the
one that takes effect, and the levelled spelling always sorts after the plain
one.  ``-Wcast-align`` is the same arrangement with a word rather than a number.

Code that is not ours
^^^^^^^^^^^^^^^^^^^^^

.. command:: smt_switch_drop_warning_options

  .. code-block:: cmake

    smt_switch_drop_warning_options(<saved-var>)

  Takes the flags above off the compile options of the calling directory, and
  so off every target defined there afterwards and every subdirectory added
  after it, and sets ``<saved-var>`` to the options as they were, for putting
  back.  It is for code that does not build clean under them and that we
  cannot change: GoogleTest, and the C++ that Cython generates for the Python
  bindings.
#]=======================================================================]

set(
  cxx_warnings_wanted
  "-W#pragma-messages" # whatever #pragma message prints
  -WTU-local-entity-exposure # TU local entity X is exposed
  -Wabbreviated-auto-in-template-arg # diagnose a placeholder type in a template argument
  -Wabsolute-value # suspicious calls of standard functions computing absolute values
  -Wabstract-final-class # abstract class is marked 'final'
  -Wabstract-vbase-init # initializer for virtual base class X of abstract class Y
  -Waddress # suspicious uses of memory addresses
  -Waddress-of-packed-member # the address of packed member of struct or union is taken
  -Waddress-of-temporary # taking the address of a temporary object of type X
  -Waggressive-loop-optimizations # a loop with constant number of iterations triggers undefined
  -Walias-template-in-declaration-name # a declarative nested name specifier cannot name an alias
  -Walign-mismatch # passing X-byte aligned argument to Y-byte aligned parameter Z of W
  -Wall # the baseline set: mistakes almost nobody intends
  -Walloc-size # allocating insufficient storage for the target type of the assigned pointer
  -Walloc-zero # calls to allocation functions that specify zero bytes
  -Walloca # any use of alloca
  -Walloca-with-align-alignof # second argument to __builtin_alloca_with_align
  -Walways-inline-coroutine # this coroutine may be split into pieces
  -Wambiguous-delete # multiple suitable X functions for Y
  -Wambiguous-ellipsis # '...' in this location creates a C-style varargs function
  -Wambiguous-member-template # lookup of X in member access expression is ambiguous
  -Wambiguous-reversed-operator # ISO C++20 considers use of overloaded operator 'X'
  -Wanon-enum-enum-conversion # arithmetic between different enumeration types (X and Y)
  -Wanonymous-pack-parens # C++11 and later require a parenthesized pack declaration to be named
  -Wapinotes # a malformed API notes file
  -Wargument-outside-range # argument value X is outside the valid range [Y, Z]
  -Wargument-undefined-behaviour # argument value X will result in undefined behaviour
  -Warith-conversion # conversion of the result of arithmetic might change the value
  -Warray-bounds # an array is accessed out of bounds
  -Warray-bounds-pointer-arithmetic # the pointer decremented by X refers before the beginning
  -Warray-bounds=2 # an array is accessed out of bounds
  -Warray-compare # comparisons between two operands of array type
  -Warray-compare-cxx26 # comparison between two arrays is ill-formed in C++26
  -Warray-parameter # mismatched declarations of array parameters and unsafe accesses to them
  -Warray-parameter=2 # mismatched declarations of array parameters and unsafe accesses to them
  -Wasm-operand-widths # value size does not match register size specified by the constraint
  -Wassign-enum # integer constant not in range of enumerated type X
  -Wassume # assumption is ignored because it contains (potential) side-effects
  -Watomic-access # accessing a member of an atomic structure or union is undefined behavior
  -Watomic-alignment # misaligned atomic operation may incur significant performance penalty
  -Watomic-implicit-seq-cst # implicit use of sequentially-consistent atomic
  -Watomic-memory-ordering # success memory order argument to atomic operation is invalid
  -Watomic-property-with-user-defined-accessor # writable atomic property X cannot pair
  -Wattribute-alias # type safety and similar errors and mismatches in declarations with alias
  -Wattribute-alias=2 # type safety and similar errors and mismatches in declarations with alias
  -Wattribute-packed-for-bitfield # 'packed' attribute was ignored on bit-fields with single-byte
  -Wattribute-preprocessor-tokens # 'X' is not allowed in an attribute argument list
  -Wattribute-statement # X attribute minimum and maximum arguments are equal
  -Wattribute-warning # uses of __attribute__((warning)) declarations
  -Wattributes # inappropriate attribute usage
  -Wauto-decl-extensions # type inference of a declaration other than a plain identifier
  -Wauto-disable-vptr-sanitizer # implicitly disabling vptr sanitizer because rtti wasn't enabled
  -Wauto-profile # problems with auto-profile data
  -Wauto-storage-class # 'auto' as a storage class specifier, which C++11 and later removed
  -Wauto-var-id # 'auto' deduced as 'id' in declaration of X
  -Wavailability # availability does not match previous declaration
  -Wbackend-plugin # X
  -Wbackslash-newline-escape # backslash and newline separated by space
  -Wbad-function-cast # casting functions to incompatible types
  -Wbidi-chars # UTF-8 bidirectional control characters
  -Wbind-to-temporary-copy # a reference bound to a temporary with an inaccessible copy ctor
  -Wbit-int-extension # '_BitInt' in C17 and earlier is a Clang extension
  -Wbitfield-constant-conversion # implicit truncation from X to bit-field changes value from Y
  -Wbitfield-enum-conversion # signed bit-field X needs an extra bit to represent the largest
  -Wbitfield-width # width of bit-field X (Y bits) exceeds the width of its type
  -Wbitwise-conditional-parentheses # operator '?:' has lower precedence than 'X'
  -Wbitwise-instead-of-logical # use of bitwise 'X' with boolean operands
  -Wbitwise-op-parentheses # 'X' within 'Y'
  -Wbool-compare # boolean expression compared with an integer value different from true/false
  -Wbool-conversion # initialization of pointer of type X to null from a constant boolean
  -Wbool-operation # certain operations on boolean expressions
  -Wbounds-safety-counted-by-elt-type-unknown-size # 'counted_by' cannot be applied to a pointer
  -Wbraced-scalar-init # braces around scalar initializer
  -Wbranch-protection # unsupported branch protection specification 'X'
  -Wbridge-cast # X cannot bridge to Y
  -Wbuiltin-assume-aligned-alignment # requested alignment must be X bytes or smaller
  -Wbuiltin-declaration-mismatch # a built-in function is declared with the wrong signature
  -Wbuiltin-macro-redefined # a built-in preprocessor macro is undefined or redefined
  -Wbuiltin-memcpy-chk-size # 'X' will always overflow
  -Wbuiltin-requires-header # declaration of built-in function 'X' requires inclusion
  -Wc++11-narrowing-const-reference # type X cannot be narrowed to Y in initializer list
  -Wc++20-attribute-extensions # use of the X attribute is a C++20 extension
  -Wc++20-compat # C++ constructs whose meaning differs between ISO C++ 2017 and ISO C++ 2020
  -Wc++20-compat-pedantic # covers -Wc++20-compat
  -Wc++20-designator # designated initializers are a C++20 extension
  -Wc++20-extensions # C++20 constructs in code compiled with an older standard
  -Wc++23-attribute-extensions # use of the X attribute is a C++23 extension
  -Wc++23-extensions # C++23 constructs in code compiled with an older standard
  -Wc++23-lambda-attributes # an attribute specifier sequence in this position is a C++23 extension
  -Wc++26-compat # C++ constructs whose meaning differs between ISO C++ 2023 and ISO C++ 2026
  -Wc++26-extensions # C++26 constructs in code compiled with an older standard
  -Wc-attribute-extension # ISO C does not allow an attribute list to appear here
  -Wc99-designator # array designators are a C99 extension
  -Wcall-to-pure-virtual-from-ctor-dtor # call to pure virtual member function X
  -Wcalled-once-parameter # X parameter marked 'called_once' is called twice
  -Wcalloc-transposed-args # suspicious calls to calloc-like functions where sizeof expression
  -Wcannot-profile # profiling instrumentation was requested
  -Wcast-align # pointer casts which increase alignment
  -Wcast-align=strict # the same for any widening of alignment, not just where it can fault
  -Wcast-calling-convention # cast between incompatible calling conventions 'X' and 'Y'
  -Wcast-function-type # casts between incompatible function types
  -Wcast-function-type-mismatch # cast from X to Y converts to incompatible function type
  -Wcast-function-type-strict # cast from X to Y converts to incompatible function type
  # -Wcast-qual # casts which discard qualifiers
  -Wcast-qual-unrelated # ISO C++ does not allow const_cast from X to Y
  -Wcast-user-defined # a cast to reference type that does not use a related user-defined
  -Wcatch-value=3 # catch handlers of non-reference type
  -Wcfi-unchecked-callee # implicit conversion from X to Y discards 'cfi_unchecked_callee'
  -Wchanges-meaning # complain about a name being declared as a class member after a previous use
  -Wchar-subscripts # subscripts whose type is 'char'
  -Wcharacter-conversion # implicit conversion from X to Y may change the meaning
  -Wclass-conversion # a conversion function will never be called due to the type it converts
  -Wclass-memaccess # unsafe raw memory writes to objects of class types
  -Wclass-varargs # passing object of class type X through variadic function
  -Wclobbered # variables that might be changed by 'longjmp' or 'vfork'
  -Wcmse-union-leak # passing union across security boundary via parameter X may leak information
  -Wcomma # possible misuse of comma operator here
  -Wcomma-subscript # uses of a comma operator within a subscripting expression
  -Wcomment # possibly nested block comments, and C++ comments spanning more than one physical line
  -Wcompare-distinct-pointer-types # pointers of distinct types are compared without a cast
  -Wcomplain-wrong-lang # complain when a command-line option is valid
  -Wcompletion-handler # completion handler is called twice
  -Wcomplex-component-init # complex initialization specifying real and imaginary components
  -Wcompound-token-split # covers -Wcompound-token-split-by-macro, -Wcompound-token-split-by-space
  -Wcompound-token-split-by-macro # X and Y tokens introducing statement expression appear
  -Wcompound-token-split-by-space # X and Y tokens introducing statement expression
  -Wconditional-type-mismatch # pointer/integer type mismatch in conditional expression (X and Y)
  -Wconditional-uninitialized # variable X may be uninitialized when used here
  -Wconditionally-supported # conditionally-supported constructs
  -Wconfig-macros # definition of configuration macro 'X' has no effect on the import of 'Y'
  -Wconstant-conversion # implicit conversion from X to Y changes value from Z to W
  -Wconstant-evaluated # 'X' will always evaluate to 'true' in a manifestly constant-evaluated
  -Wconstant-logical-operand # use of logical 'X' with constant operand
  -Wconsumed # return state set for an unconsumable type 'X'
  # -Wconversion # implicit type conversions that may change a value
  -Wconversion-null # converting NULL from/to a non-pointer type
  -Wcoro-non-aligned-allocation-function # under -fcoro-aligned-allocation
  -Wcoro-type-aware-allocation-function # type aware X will not be used for coroutine allocation
  -Wcoroutine # coroutine_handle<>::address not returning 'void*'
  -Wcoroutine-missing-unhandled-exception # X is required to declare the member
  -Wcoverage-invalid-line-number # a function ends earlier than it begins due to an invalid
  -Wcoverage-mismatch # profiles in -fprofile-use do not match
  -Wcoverage-too-many-conditions # a conditional has too many terms and condition coverage
  -Wcoverage-too-many-paths # a function exceeds the number of paths and path coverage give up
  -Wcovered-switch-default # default label in switch which covers all enumeration values
  -Wcpp # a #warning directive is encountered
  # -Wctad-maybe-unsupported # performing class template argument deduction
  -Wctor-dtor-privacy # all constructors and destructors are private
  -Wcxx-attribute-extension # ISO C++ does not allow an attribute list to appear here
  -Wdangling # temporary whose address is used as value of reference member of local variable X
  -Wdangling-assignment # object backing the pointer X will be destroyed at the end
  -Wdangling-assignment-gsl # object backing the pointer X will be destroyed at the end
  -Wdangling-capture # object whose reference is captured will be destroyed at the end
  -Wdangling-else # dangling else
  -Wdangling-field # temporary bound to reference member of allocated object
  -Wdangling-gsl # object backing the pointer will be destroyed at the end of the full-expression
  -Wdangling-initializer-list # array backing initializer list subobject of the allocated object
  -Wdangling-pointer=2 # uses of pointers to auto variables whose lifetime has ended
  -Wdangling-reference # a reference is bound to a temporary whose lifetime has ended
  -Wdarwin-sdk-settings # SDK settings were ignored as 'SDKSettings.json' could not be parsed
  -Wdate-time # __TIME__, __DATE__ and __TIMESTAMP__ usage
  -Wdealloc-in-category # -dealloc is being overridden in a category
  -Wdebug-compression-unavailable # cannot compress debug sections (X not enabled)
  -Wdecls-in-multiple-modules # declaration X is detected to be defined in multiple module units
  -Wdefault-const-init # covers -Wdefault-const-init-field
  -Wdefault-const-init-field # default initialization of an object of type X with const member
  -Wdefault-const-init-field-unsafe # default initialization of an object of type X
  -Wdefault-const-init-unsafe # covers -Wdefault-const-init-field-unsafe
  -Wdefault-const-init-var # default initialization of an object of type X is incompatible with C++
  -Wdefault-const-init-var-unsafe # default initialization of an object of type X leaves
  -Wdefaulted-function-deleted # an explicitly defaulted function is deleted
  -Wdelayed-template-parsing-in-cxx20 # -fdelayed-template-parsing is deprecated after C++20
  -Wdelegating-ctor-cycles # constructor for X creates a delegation cycle
  -Wdelete-abstract-non-virtual-dtor # delete called on X that is abstract
  -Wdelete-incomplete # deleting a pointer to incomplete type
  -Wdelete-non-abstract-non-virtual-dtor # delete called on non-final X that has virtual functions
  -Wdelete-non-virtual-dtor # deleting polymorphic objects with non- virtual destructors
  -Wdelimited-escape-sequence-extension # delimited escape sequences are a C++23 extension
  -Wdeprecate-lax-vec-conv-all # implicit conversion between vector types is deprecated
  -Wdeprecated # a deprecated compiler feature, class, method, or field is used
  -Wdeprecated-altivec-src-compat # current handling of vector bool and vector pixel types
  -Wdeprecated-anon-enum-enum-conversion # arithmetic between different enumeration types
  -Wdeprecated-array-compare # comparison between two arrays is deprecated
  -Wdeprecated-attributes # the '[[_Noreturn]]' attribute spelling is deprecated in C23
  -Wdeprecated-builtins # builtin X is deprecated
  -Wdeprecated-comma-subscript # top-level comma expression in array subscript
  -Wdeprecated-copy # mark implicitly-declared copy operations as deprecated if the class
  -Wdeprecated-copy-dtor # mark implicitly-declared copy operations as deprecated if the class
  -Wdeprecated-copy-with-user-provided-copy # definition of implicit copy constructor for X
  -Wdeprecated-copy-with-user-provided-dtor # definition of implicit copy constructor for X
  -Wdeprecated-coroutine # 'for co_await' belongs to CoroutineTS instead of C++20
  -Wdeprecated-declarations # uses of __attribute__((deprecated)) declarations
  -Wdeprecated-declarations-switch-case # X is deprecated
  -Wdeprecated-dynamic-exception-spec # dynamic exception specifications are deprecated
  -Wdeprecated-enum-compare # arithmetic between different enumeration types is deprecated
  -Wdeprecated-enum-compare-conditional # arithmetic between different enumeration types
  -Wdeprecated-enum-enum-conversion # deprecated arithmetic conversions on operands of enumeration
  -Wdeprecated-enum-float-conversion # deprecated arithmetic conversions on operands where one
  -Wdeprecated-implementations # implementing unavailable method
  -Wdeprecated-literal-operator # deprecated space between and suffix in a user-defined literal
  -Wdeprecated-missing-comma-variadic-parameter # declaration of a variadic function without
  -Wdeprecated-module-dot-map # 'X' as a module map name is deprecated
  -Wdeprecated-non-prototype # calls with arguments to functions declared without parameters
  -Wdeprecated-octal-literals # octal literals without a '0o' prefix are deprecated
  -Wdeprecated-ofast # argument '-Ofast' is deprecated
  -Wdeprecated-pragma # macro X has been marked as deprecated: Y
  -Wdeprecated-redundant-constexpr-static-def # out-of-line definition of constexpr static data
  -Wdeprecated-this-capture # implicit capture of 'this' with a capture default of '='
  -Wdeprecated-type # '_ExtInt' is deprecated
  -Wdeprecated-variadic-comma-omission # deprecated omission of comma before ... in varargs
  -Wdeprecated-volatile # volatile qualifier in structured binding declaration is deprecated
  -Wdisabled-macro-expansion # disabled expansion of recursive macro
  -Wdisabled-optimization # an optimization pass is disabled
  -Wdistributed-object-modifiers # conflicting distributed object modifiers on return
  -Wdiv-by-zero # compile-time integer division by zero
  # -Wdocumentation # not a Doxygen trailing comment
  # -Wdocumentation-deprecated-sync # declaration is marked with '\\deprecated' command
  -Wdocumentation-html # HTML end tag does not match any start tag
  -Wdocumentation-pedantic # whitespace is not allowed in parameter passing direction
  -Wdocumentation-unknown-command # unknown command tag name
  -Wdollar-in-identifier-extension # 'X' in identifier
  -Wdouble-promotion # implicit conversions from 'float' to 'double'
  -Wdtor-name # ISO C++ considers this destructor name lookup to be ambiguous
  -Wdtor-typedef # destructor cannot be declared using a typedef X of the class name
  -Wduplicate-decl-specifier # a declaration has duplicate const
  -Wduplicate-enum # element X has been implicitly assigned Y
  -Wduplicate-header-ownership # header 'X' is owned by multiple modules
  -Wduplicate-method-arg # redeclaration of method parameter X
  -Wduplicate-method-match # multiple declarations of method X found and ignored
  -Wduplicated-branches # duplicated branches in if-else statements
  -Wduplicated-cond # duplicated conditions in an if-else-if chain
  -Wdxil-validation # dxv not found
  -Wdynamic-class-memaccess # destination for this X call is a pointer to class containing
  -Wdynamic-exception-spec # ISO C++17 does not allow dynamic exception specifications
  -Weager-load-cxx-named-modules # the form '-fmodule-file=<BMI-path>'
  # -Weffc++ # violations of Effective C++ style rules
  -Welaborated-enum-base # an additional enum-base is used in an elaborated-type-specifier
  -Welaborated-enum-class # reference to enumeration must use 'enum' not 'enum struct'
  -Wembedded-directive # embedding a directive within macro arguments has undefined behavior
  -Wempty-body # an empty body in an if or else statement
  -Wempty-decomposition # ISO C++17 does not allow a structured binding group to be empty
  -Wempty-init-stmt # empty initialization statement of 'if' has no effect
  -Wempty-translation-unit # ISO C requires a translation unit to contain at least one declaration
  -Wencode-type # encoding of X type is incomplete because Y component has unknown encoding
  -Wendif-labels # stray tokens after #else and #endif
  -Wenum-compare # comparison of different enum types
  -Wenum-compare-conditional # arithmetic between different enumeration types (X and Y)
  -Wenum-compare-switch # comparison of different enumeration types in switch statement (X and Y)
  -Wenum-compare-typo # comparison operator 'X' is potentially a typo for a shift operator 'Y'
  -Wenum-conversion # implicit conversion of enum types
  -Wenum-enum-conversion # arithmetic between different enumeration types (X and Y)
  -Wenum-float-conversion # arithmetic between floating-point type X enumeration type Y
  -Wenum-too-large # enumeration values exceed range of largest integer
  -Wexceptions # an exception handler is shadowed by another handler
  -Wexcess-initializers # excess elements in char array initializer
  -Wexcessive-regsave # interrupt service routine should only call a function with attribute
  # -Wexit-time-destructors # declaration requires an exit-time destructor
  -Wexpansion-stmt-missing-braces # ISO C++ requires the body of an expansion statement
  -Wexpansion-to-defined # 'defined' is used outside #if
  -Wexperimental-header-units # the implementation of header units is in an experimental phase
  -Wexplicit-initialize-call # explicit call to +initialize results in duplicate call
  -Wexplicit-ownership-type # method parameter of type X with no explicit ownership
  -Wexplicit-specialization-storage-class # explicit specialization cannot have a storage class
  -Wexpose-global-module-tu-local # a module exposes a TU-local entity from the global module
  -Wext-cxx-type-aware-allocators # type aware allocators are a Clang extension
  -Wextern-c-compat # empty struct has size 0 in C, size 1 in C++
  -Wextern-initializer # 'extern' variable has an initializer
  -Wexternal-tu-local # naming a TU-local entity declared in another translation unit
  -Wextra # the set beyond -Wall; -Wunused-parameter needs the two together
  -Wextra-qualification # extra qualification on member X
  # -Wextra-semi # semicolon after in-class function definition
  # -Wextra-semi-stmt # empty expression statement has no effect
  -Wextractapi-misuse # missing symbol graph output directory, defaulting to working directory
  -Wextraneous-template-head # extraneous template parameter list in template specialization
  -Wfinal-dtor-non-final-class # class with destructor marked 'final' cannot be inherited
  -Wfinal-macro # macro X has been marked as final and should not be undefined
  -Wfixed-point-overflow # overflow in expression
  -Wflag-enum # enumeration value X is out of range of flags in enumeration type Y
  -Wflex-array-member-not-at-end # a structure containing a C99 flexible array member as the last
  -Wflexible-array-extensions # X may not be nested in a struct due to flexible array member
  # -Wfloat-conversion # implicit type conversions that cause loss of floating point precision
  # -Wfloat-equal # testing floating point numbers for equality
  -Wfloat-overflow-conversion # implicit conversion of out of range value from X to Y is undefined
  -Wfloat-zero-conversion # implicit conversion from X to Y changes non-zero value from Z to W
  -Wfor-loop-analysis # variable X is decremented both in the loop header and in the loop body
  -Wformat # printf/scanf/strftime/strfmon format string anomalies
  -Wformat-contains-nul # format strings that contain NUL bytes
  -Wformat-diag # GCC format strings with strings unsuitable for diagnostics
  -Wformat-extra-args # passing too many arguments to a function for its format string
  -Wformat-insufficient-args # more '%' conversions than data arguments
  -Wformat-invalid-specifier # invalid conversion specifier 'X'
  -Wformat-non-iso # positional arguments are not supported by ISO C
  -Wformat-nonliteral # format strings that are not literals
  -Wformat-overflow # function calls with format strings that write past the end
  -Wformat-overflow-non-kprintf # 'X' will always overflow
  -Wformat-overflow=2 # function calls with format strings that write past the end
  -Wformat-pedantic # signedness of format specifier 'X' is incompatible with 'Y'
  -Wformat-security # possible security problems with format functions
  -Wformat-signedness # sign differences with format functions
  -Wformat-truncation # calls to snprintf and similar functions that truncate output
  -Wformat-truncation-non-kprintf # 'X' will always be truncated
  -Wformat-truncation=2 # calls to snprintf and similar functions that truncate output
  -Wformat-type-confusion # format specifies type X but the argument has type Y
  -Wformat-y2k # strftime formats yielding 2-digit years
  -Wformat-zero-length # zero-length formats
  -Wformat=2 # printf/scanf/strftime/strfmon format string anomalies
  -Wfortify-source # 'X' will always overflow
  -Wfour-char-constants # multi-character character constant
  -Wframe-address # __builtin_frame_address or __builtin_return_address is used unsafely
  -Wfree-nonheap-object # attempting to free a non-heap object
  -Wfriend-enum # elaborated enum specifier cannot be declared as a friend
  -Wfunction-effect-redeclarations # redeclaration is missing 'X' attribute from previous
  -Wfunction-effects # attribute 'X' should not be added via type conversion
  -Wfunction-multiversion # CPU list contains duplicate entries
  -Wfuse-ld-path # '-fuse-ld=' taking a path is deprecated
  -Wgcc-compat # 'enable_if' is a clang extension
  -Wgcc-install-dir-libstdcxx # future releases of the clang compiler
  # -Wglobal-constructors # declaration requires a global constructor
  -Wglobal-isel # -fglobal-isel support is incomplete for this architecture at the current
  -Wglobal-module # the global module fragment not containing only preprocessing directives
  -Wgnu # covers -Wgnu-alignof-expression
  -Wgnu-alignof-expression # X applied to an expression is a GNU extension
  -Wgnu-anonymous-struct # anonymous structs are a GNU extension
  -Wgnu-array-member-paren-init # parenthesized initialization of a member array is a GNU extension
  -Wgnu-auto-type # '__auto_type' is a GNU extension
  -Wgnu-case-range # case ranges are a GNU extension
  -Wgnu-complex-integer # complex integer types are a GNU extension
  -Wgnu-compound-literal-initializer # initialization of an array of type X from a compound
  -Wgnu-conditional-omitted-operand # use of GNU ?: conditional expression extension
  -Wgnu-designator # use of GNU 'missing =' extension in designator
  -Wgnu-empty-struct # empty struct is a GNU extension
  -Wgnu-flexible-array-initializer # flexible array initialization is a GNU extension
  -Wgnu-flexible-array-union-member # flexible array member X in a union is a GNU extension
  -Wgnu-folding-constant # in-class initializer for static data member is not a constant expression
  -Wgnu-imaginary-constant # imaginary constants are a GNU extension
  -Wgnu-include-next # #include_next is a language extension
  -Wgnu-inline-cpp-without-extern # 'gnu_inline' attribute without 'extern' in C++ treated
  -Wgnu-label-as-value # use of GNU address-of-label extension
  -Wgnu-line-marker # this style of line directive is a GNU extension
  -Wgnu-null-pointer-arithmetic # arithmetic on a null pointer treated as a cast from integer
  -Wgnu-pointer-arith # arithmetic on a pointers to the function types X and Y is a GNU extension
  -Wgnu-redeclared-enum # redeclaration of already-defined enum X is a GNU extension
  -Wgnu-statement-expression # use of GNU statement expression extension
  -Wgnu-statement-expression-from-macro-expansion # use of GNU statement expression extension
  -Wgnu-static-float-init # in-class initializer for static data member of type X
  -Wgnu-string-literal-operator-template # string literal operator templates are a GNU extension
  -Wgnu-union-cast # cast to union type is a GNU extension
  -Wgnu-variable-sized-type-not-at-end # field X with variable sized type Y not at the end
  -Wgnu-zero-line-directive # #line directive with zero argument is a GNU extension
  -Wgnu-zero-variadic-macro-arguments # token pasting of ',' and '__VA_ARGS__' is a GNU extension
  -Wgpu-maybe-wrong-side # capture host side class data member by this pointer in device or host
  -Wgroupshared-initializer # initializer of groupshared variable will be ignored
  -Whardened # -fhardened did not enable an option from its set
  -Wheader-guard # #ifndef of a header guard is followed by #define of a different macro
  # -Wheader-hygiene # using namespace directive in global context in header
  -Whexagon-reserved-caller-saved # reserving the caller-saved register 'X'
  -Whigher-precision-for-complex-division # excess precision is requested
  -Widiomatic-parentheses # using the result of an assignment as a condition without parentheses
  -Wif-not-aligned # the field in a struct is not aligned
  -Wignored-attributes # attributes are ignored
  -Wignored-availability-without-sdk-settings # X availability is ignored without a valid
  -Wignored-base-class-qualifiers # 'X' qualifierY on base class type Z no effect
  -Wignored-optimization-argument # optimization flag 'X' is not supported
  -Wignored-pragma-intrinsic # X is not a recognized builtin
  -Wignored-pragmas # missing debug command
  -Wignored-qualifiers # type qualifiers are ignored
  -Wignored-reference-qualifiers # 'X' qualifier on reference type Y has no effect
  -Wimplicit # implicit declarations
  -Wimplicit-const-int-float-conversion # implicit conversion from X to Y changes value from Z to W
  -Wimplicit-conversion-floating-point-to-bool # implicit conversion turns floating-point number
  -Wimplicit-enum-enum-cast # implicit conversion from enumeration type X to different enumeration
  -Wimplicit-exception-spec-mismatch # function previously declared with an explicit exception
  -Wimplicit-fallthrough # a switch case falls through
  -Wimplicit-fallthrough-per-function # unannotated fall-through between switch labels
  -Wimplicit-fallthrough=5 # a switch case falls through
  -Wimplicit-fixed-point-conversion # implicit conversion from X cannot fit within the range
  # -Wimplicit-float-conversion # implicit conversion loses floating-point precision: X to Y
  -Wimplicit-int # a declaration does not specify a type
  # -Wimplicit-int-conversion # higher order bits are zeroes after implicit conversion
  -Wimplicit-int-conversion-on-negation # implicit conversion loses integer precision: X to Y
  -Wimplicit-int-enum-cast # implicit conversion from X to enumeration type Y is invalid in C++
  # -Wimplicit-int-float-conversion # implicit conversion from X to Y may lose precision
  -Wimplicit-overflow-behavior-conversion # implicit conversion from X to Y discards overflow
  -Wimplicit-overflow-behavior-conversion-assignment # implicit conversion from X to Y during
  -Wimplicit-overflow-behavior-conversion-assignment-pedantic # implicit conversion from X to Y
  -Wimplicit-overflow-behavior-conversion-function-boundary # passing argument of type X
  -Wimplicit-overflow-behavior-conversion-function-boundary-pedantic # passing argument of type X
  -Wimplicit-overflow-behavior-conversion-pedantic # implicit conversion from X to Y discards
  -Wimplicit-retain-self # block implicitly retains 'self'
  -Wimplicit-void-ptr-cast # implicit conversion when assigning to X from type Y
  -Wimplicitly-unsigned-literal # integer literal is too large to be represented in a signed
  -Wimport-implementation-partition-unit-in-interface-unit # importing an implementation partition
  -Wimport-preprocessor-directive-pedantic # #import is a language extension
  -Winaccessible-base # a base is inaccessible in derived due to ambiguity
  -Winclude-angled-in-module-purview # '#include <filename>' attaches the declarations
  -Winclude-next-absolute-path # #include_next in file found relative to primary source file
  -Winclude-next-outside-header # #include_next in primary source file
  -Wincompatible-exception-spec # target exception specification is not superset of source
  -Wincompatible-function-pointer-types # incompatible function pointer types assigning to X from Y
  -Wincompatible-function-pointer-types-strict # incompatible function pointer types assigning
  -Wincompatible-library-redeclaration # incompatible redeclaration of library function X
  -Wincompatible-pointer-types # there is a conversion between pointers
  -Wincompatible-pointer-types-discards-overflow-behavior # assigning to X from Y discards
  -Wincompatible-pointer-types-discards-qualifiers # assigning to X from Y discards qualifiers
  -Wincompatible-property-type # property type X is incompatible with type Y inherited from Z
  -Wincompatible-sysroot # using sysroot for 'X' but targeting 'Y'
  -Wincomplete-framework-module-declaration # skipping 'X'
  -Wincomplete-implementation # method definition for X not found
  -Wincomplete-module # covers -Wincomplete-umbrella, -Wnon-modular-include-in-module
  -Wincomplete-setjmp-declaration # declaration of built-in function 'X' requires the declaration
  -Winconsistent-dllimport # X redeclared without 'dllimport' attribute: 'dllexport' attribute
  -Winconsistent-missing-destructor-override # X overrides a destructor
  -Winconsistent-missing-override # X overrides a member function but is not marked 'override'
  -Wincrement-bool # ISO C++17 does not allow incrementing expression of type bool
  -Winfinite-recursion # infinitely recursive calls
  -Winherited-variadic-ctor # an inheriting constructor, C++11 and later, whose base is variadic
  -Winit-list-lifetime # uses of std::initializer_list that can result in dangling pointers
  -Winit-priority-reserved # requested 'init_priority' X is reserved for internal use
  -Winit-self # variables which are initialized to themselves
  -Winjected-class-name # ISO C++ specifies that qualified reference to X is a constructor name
  # -Winline # an inlined function cannot be inlined
  -Winline-asm # a problem inside an asm statement
  -Winline-namespace-reopened-noninline # inline namespace reopened as a non-inline namespace
  -Winline-new-delete # replacement function X cannot be declared 'inline'
  -Winstallapi-violation # violations found for X
  -Winstantiation-after-specialization # explicit instantiation of X that occurs after an explicit
  -Wint-conversion # incompatible integer to pointer and pointer to integer conversions
  -Wint-in-bool-context # suspicious integer expressions in boolean context
  -Wint-to-pointer-cast # there is a cast to a pointer from an integer of a different size
  -Wint-to-void-pointer-cast # cast to X from smaller integer type Y
  -Winteger-overflow # overflow in expression
  -Winterference-size # nonsensical values of --param destructive-interference-size
  -Winvalid-command-line-argument # missing plugin argument for plugin X in Y
  -Winvalid-constexpr # a function never produces a constant expression
  -Winvalid-feature-combination # invalid feature combination: X
  -Winvalid-gnu-asm-cast # invalid use of a cast in an inline asm context requiring an lvalue
  -Winvalid-iboutlet # instance variable with X attribute must be an object type (invalid Y)
  -Winvalid-imported-macros # macros that have conflicting header units definitions
  -Winvalid-initializer-from-system-header # invalid constructor from class in system header
  -Winvalid-ios-deployment-target # invalid iOS deployment version 'X'
  -Winvalid-memory-model # an atomic memory model parameter is known to be outside the valid range
  -Winvalid-no-builtin-names # 'X' is not a valid builtin name for Y
  -Winvalid-noreturn # function X declared 'noreturn' should not return
  -Winvalid-offsetof # invalid uses of the 'offsetof' macro
  -Winvalid-or-nonexistent-directory # unable to find X directory
  -Winvalid-partial-specialization # class template partial specialization
  -Winvalid-pp-token # empty character constant
  -Winvalid-source-encoding # illegal character encoding in string literal
  -Winvalid-specialization # X cannot be specialized: Y
  -Winvalid-static-assert-message # the message in this static assertion
  -Winvalid-token-paste # pasting formed 'X', an invalid preprocessing token
  -Winvalid-unevaluated-string # encoding prefix 'X' on an unevaluated string literal
  -Winvalid-utf8 # invalid UTF-8 characters
  -Winvalid-version-availability # invalid X version 'Y' in availability attribute
  -Wjump-seh-finally # jump out of __finally block has undefined behavior
  -Wkeyword-compat # keyword 'X' will be made available as an identifier here
  -Wkeyword-macro # defining or undefining macros with identifiers equal to keywords
  -Wknr-promoted-parameter # promoted type X of K&R function parameter is not compatible
  -Wlanguage-extension-token # extension used
  -Wlarge-by-value-copy # X is a large (Y bytes) pass-by-value argument
  -Wlegacy-constant-register-binding # binding type 'i' ignored
  # -Wlifetime-safety # covers -Wlifetime-safety-permissive, -Wlifetime-safety-strict
  # -Wlifetime-safety-all # covers -Wlifetime-safety
  -Wlifetime-safety-annotation-placement # covers -Wlifetime-safety-inapplicable-lifetimebound
  -Wlifetime-safety-annotation-verification # covers -Wlifetime-safety-noescape
  # -Wlifetime-safety-cross-tu-constructor-suggestions # parameter in cross-TU constructor
  -Wlifetime-safety-cross-tu-misplaced-lifetimebound # 'lifetimebound' attribute
  # -Wlifetime-safety-cross-tu-suggestions # parameter in cross-TU function
  -Wlifetime-safety-dangling-field # stack memory associated with X escapes to the Y
  -Wlifetime-safety-dangling-field-moved # stack memory associated with X may escape to the Y
  -Wlifetime-safety-dangling-global # stack memory associated with X escapes to the Y
  -Wlifetime-safety-dangling-global-moved # stack memory associated with X may escape to the Y
  -Wlifetime-safety-inapplicable-lifetimebound # 'lifetimebound' attribute
  # -Wlifetime-safety-intra-tu-constructor-suggestions # parameter in intra-TU constructor
  -Wlifetime-safety-intra-tu-misplaced-lifetimebound # 'lifetimebound' attribute
  # -Wlifetime-safety-intra-tu-suggestions # parameter in intra-TU function
  # -Wlifetime-safety-invalidation # X is later invalidated
  -Wlifetime-safety-lifetimebound-violation # could not verify that the return value
  -Wlifetime-safety-misplaced-lifetimebound # covers
  -Wlifetime-safety-noescape # parameter is marked [[clang::noescape]] but escapes
  -Wlifetime-safety-permissive # covers -Wlifetime-safety-use-after-scope
  -Wlifetime-safety-return-stack-addr # stack memory associated with X is returned
  -Wlifetime-safety-return-stack-addr-moved # stack memory associated with X may be returned later
  # -Wlifetime-safety-strict # covers -Wlifetime-safety-permissive
  # -Wlifetime-safety-suggestions # covers -Wlifetime-safety-cross-tu-suggestions
  -Wlifetime-safety-use-after-free # X does not live long enough
  -Wlifetime-safety-use-after-scope # X does not live long enough
  -Wlifetime-safety-use-after-scope-moved # X may not live long enough
  -Wlifetime-safety-validations # covers -Wlifetime-safety-annotation-placement
  -Wlinker-warnings # linking module 'X': Y
  -Wliteral-conversion # implicit conversion of out of range value from X to Y is undefined
  -Wliteral-range # magnitude of floating-point constant too large for type X
  -Wliteral-suffix # a string or character literal is followed by a ud-suffix
  -Wlogical-not-parentheses # logical not is used on the left hand side operand of a comparison
  -Wlogical-op # a logical operator is suspiciously always evaluating to true or false
  -Wlogical-op-parentheses # '&&' within '||'
  -Wloop-analysis # covers -Wfor-loop-analysis, -Wrange-loop-analysis
  -Wlto-type-mismatch # during link time optimization warn about mismatched types of global
  -Wmacro-redefined # X macro redefined
  -Wmain # suspicious declarations of 'main'
  -Wmain-attached-to-named-module # 'main' never has module linkage
  -Wmain-return-type # return type of 'main' is not 'int'
  -Wmalformed-warning-check # __has_warning expected option name (e.g. '-Wundef')
  -Wmany-braces-around-scalar-init # too many braces around scalar initializer
  -Wmath-errno-enabled-with-veclib # math errno enabled by 'X'
  -Wmathematical-notation-identifier-extension # mathematical notation character <U+X>
  -Wmatrix-conversion # implicit conversion truncates matrix: X to Y
  -Wmax-tokens # the number of preprocessor source tokens (X) exceeds this token limit (Y)
  -Wmax-unsigned-zero # taking the max of a value and unsigned zero is always equal to the other
  -Wmaybe-musttail-local-addr # pointer/reference to a local or temporary variable possibly
  -Wmaybe-uninitialized # maybe uninitialized automatic variables
  -Wmemset-elt-size # suspicious calls to memset where the third argument contains the number
  -Wmemset-transposed-args # suspicious calls to memset where the third argument
  -Wmemsize-comparison # size argument in X call is a comparison
  -Wmethod-signatures # conflicting return type in implementation of X: Y vs Z
  -Wmisexpect # potential performance regression from use of __builtin_expect: annotation
  -Wmisleading-indentation # the indentation of the code does not reflect the block structure
  -Wmismatched-dealloc # deallocation calls with arguments returned from mismatched allocation
  -Wmismatched-new-delete # mismatches between calls to operator new or delete
  -Wmismatched-parameter-types # conflicting parameter types in implementation of X: Y vs Z
  -Wmismatched-return-types # conflicting return type in implementation of X: Y vs Z
  -Wmismatched-tags # a class is redeclared or referenced using a mismatched class-key
  -Wmissing-attributes # declarations of entities that may be missing attributes that related
  -Wmissing-braces # possibly missing braces around initializers
  -Wmissing-constinit # 'constinit' specifier missing on initializing declaration of X
  # -Wmissing-declarations # global functions without previous declarations
  -Wmissing-designated-field-initializers # missing field X initializer
  -Wmissing-exception-spec # X is missing exception specification 'Y'
  -Wmissing-field-initializers # missing fields in struct initializers
  -Wmissing-format-attribute # diagnostic behavior may be improved by adding the 'X' attribute
  -Wmissing-include-dirs # user-specified include directories that do not exist
  -Wmissing-method-return-type # method has no return type specified
  -Wmissing-multilib # no multilib found matching flags: X
  -Wmissing-noescape # parameter of overriding method should be annotated with __attribute__()
  # -Wmissing-noreturn # block could be declared with attribute 'noreturn'
  -Wmissing-profile # profiles in -fprofile-use do not exist
  -Wmissing-requires # likely missing requires keyword
  -Wmissing-sysroot # no such sysroot directory: 'X'
  -Wmissing-template-arg-list-after-template-kw # a template argument list
  -Wmissing-template-keyword # the template keyword is missing after a member access token
  # -Wmissing-variable-declarations # global variables without previous declarations
  -Wmisspelled-assumption # unknown assumption string 'X' may be misspelled
  -Wmix-packoffset # cannot mix packoffset elements with nonpackoffset elements in a cbuffer
  -Wmmap-deprecated-symlink-to-modular-header # header 'X' may be a symlink to 'Y' owned by module
  -Wmost # covers -Warray-parameter
  -Wmove # covers -Wpessimizing-move, -Wredundant-move, -Wreturn-std-move, -Wself-move
  -Wmulti-gpu # multiple X architectures are detected: Y
  -Wmultichar # use of multi-character character constants
  -Wmultilib-not-found # no multilib structure encoded for Arm, Aarch64 and PPC targets
  -Wmultiple-move-vbase # defaulted move assignment operator of X will move assign virtual base
  -Wmultistatement-macros # unsafe macros expanding to multiple statements used as a body
  -Wmusttail-local-addr # passing a pointer/reference to a local or temporary variable
  -Wnan-infinity-disabled # use of infinity via a macro is undefined behavior due to the currently
  -Wnarrowing # a narrowing conversion inside { }, ill-formed since C++11
  -Wnested-anon-types # anonymous types declared in an anonymous struct are an extension
  -Wnew-returns-null # X should not return a null pointer
  -Wnewline-eof # no newline at end of file
  -Wnoderef # dereferencing expression marked as 'noderef'
  # -Wnoexcept # a noexcept expression evaluates to false
  -Wnon-c-typedef-for-linkage # non-C compatible unnamed classes with a typedef name for linkage
  # -Wnon-gcc # covers -Wsign-compare, -Wconversion, -Wliteral-range
  -Wnon-literal-null-conversion # expression
  -Wnon-pod-varargs # cannot pass object of non-POD type X through variadic function
  -Wnon-power-of-two-alignment # requested alignment is not a power of 2
  -Wnon-template-friend # non-templatized friend functions are declared within a template
  -Wnon-virtual-dtor # a polymorphic base whose destructor is not virtual
  -Wnonnull # NULL being passed to argument slots marked as requiring non-NULL
  -Wnonnull-compare # comparing pointer parameter with nonnull attribute with NULL
  -Wnonportable-include-path # non-portable path to file 'X'
  -Wnonportable-include-path-separator # non-portable path to file 'X'
  -Wnonportable-private-apinotes-path # private API notes file for module 'X'
  -Wnonportable-private-system-apinotes-path # private API notes file for module 'X'
  -Wnonportable-system-include-path # non-portable path to file 'X'
  -Wnonportable-vector-initialization # vector initializers are not compatible with NEON
  -Wnontrivial-memaccess # destination for this X call is a pointer to record Y
  -Wnontrivial-memcall # first argument in call to X is a pointer to non-trivially copyable type Y
  -Wnormalized # non-normalized Unicode strings
  # -Wnrvo # the named return value optimization is not performed although it is allowed
  -Wnsreturns-mismatch # overriding method has mismatched ns_returns_not_retained attributes
  -Wnull-arithmetic # use of NULL in arithmetic operation
  -Wnull-character # null character ignored
  # -Wnull-dereference # dereferencing a NULL pointer may lead to erroneous or undefined behavior
  -Wnull-pointer-arithmetic # performing pointer arithmetic on a null pointer
  -Wnull-pointer-subtraction # performing pointer subtraction with a null pointer
  -Wnullable-to-nonnull-conversion # implicit conversion from nullable pointer X to non-nullable
  -Wnvcc-compat # target-attribute based function overloads are not supported by NVCC
  -Woctal-prefix-extension # octal integer literals are a Clang extension
  -Wodr # some C++ One Definition Rule violations during link time optimization
  # -Wold-style-cast # a C-style cast is used in a program
  -Woption-ignored # -fjmc works only for ELF
  -Wordered-compare-function-pointers # ordered comparison of function pointers (X and Y)
  -Wout-of-line-declaration # out-of-line declaration of a member must be a definition
  -Wout-of-scope-function # use of out-of-scope declaration of X
  -Wover-aligned # type X requires Y bytes of alignment and the default allocator only guarantees
  -Woverflow # overflow in arithmetic expressions
  -Woverflow-behavior-attribute-ignored # X attribute is ignored because it is not enabled
  -Woverlength-strings # a string is longer than the maximum portable length specified
  -Woverloaded-shift-op-parentheses # overloaded operator >> has higher precedence than comparison
  -Woverloaded-virtual # a derived declaration hiding a base overload
  -Woverloaded-virtual=2 # overloaded virtual function names
  -Woverride-init # overriding initializers without side effects
  -Woverride-module # overriding the module target triple with X
  -Woverriding-complex-range # 'X' sets complex range to 'Y' overriding the setting of 'Z'
  -Woverriding-deployment-version # overriding deployment version from 'X' to 'Y'
  -Woverriding-method-mismatch # conflicting variadic declaration of method and its implementation
  -Woverriding-option # overriding 'X' option with 'Y'
  -Wpacked # the packed attribute has no effect on struct layout
  -Wpacked-bitfield-compat # packed bit-fields whose offset changed in GCC 4.4
  -Wpacked-non-pod # not packing field X as it is non-POD for the purposes of layout
  -Wpacked-not-aligned # fields in a struct with the packed attribute are misaligned
  -Wpadded-bitfield # padding struct X with Y byteY to align anonymous bit-field
  -Wparentheses # possibly missing parentheses
  -Wparentheses-equality # equality comparison with extraneous parentheses
  -Wpass-failed # an optimisation pass reporting it could not run
  -Wpedantic # anything the pinned standard does not permit, GNU extensions included
  -Wpedantic-macros # covers -Wdeprecated-pragma
  -Wperf-constraint-implies-noexcept # function with 'X' attribute should be declared noexcept
  -Wpessimizing-move # calling std::move on a local object in a return statement preventing copy
  -Wpgo-coverage # unsupported MC/DC boolean expression
  -Wplacement-new=2 # placement new expressions with undefined behavior
  -Wpmf-conversions # converting the type of pointers to member functions
  -Wpointer-arith # function pointer arithmetic
  -Wpointer-bool-conversion # address of 'X' will always evaluate to 'true'
  -Wpointer-compare # a pointer is compared with a zero character constant
  -Wpointer-integer-compare # comparison between pointer and integer (X and Y)
  -Wpointer-to-enum-cast # cast to smaller integer type X from Y
  -Wpointer-to-int-cast # a pointer is cast to an integer of a different size
  -Wpointer-type-mismatch # pointer type mismatch (X and Y)
  -Wpotentially-evaluated-expression # expression with side effects will be evaluated
  -Wpragma-clang-attribute # unused attribute X in '#pragma clang attribute push' region
  -Wpragma-once-outside-header # #pragma once outside of a header
  -Wpragma-pack # unterminated '#pragma pack (push, ...)' at end of file
  -Wpragma-pack-suspicious-include # non-default #pragma pack value changes the alignment
  -Wpragma-system-header-outside-header # #pragma system_header ignored in main file
  -Wpragmas # misuses of pragmas
  -Wpre-c++20-compat # built as C++20 or later, a construct C++17 and earlier reject
  -Wpre-c++20-compat-pedantic # the same, for constructs older standards merely warned about
  -Wpre-c++23-compat # built as C++23 or later, a construct C++20 and earlier reject
  -Wpre-c++26-compat # built as C++26 or later, a construct C++23 and earlier reject
  -Wpredefined-identifier-outside-function # predefined identifier is only valid inside function
  -Wpreferred-type-bitfield-enum-conversion # signed bit-field X needs an extra bit to represent
  -Wprio-ctor-dtor # constructor or destructors with priorities from 0 to 100 are used
  -Wprivate-extern # use of __private_extern__ on a declaration may not produce external symbol
  -Wprivate-header # use of private header from outside its module: 'X'
  -Wprofile-instr-missing # profile data may be incomplete: of X functionX, Y no data
  -Wprofile-instr-out-of-date # profile data may be out of date: of X functionX, Y mismatched data
  -Wprofile-instr-unprofiled # no profile data available for file 'X'
  -Wprotocol # inherited methods are unimplemented
  -Wpsabi # code affected by incompatible psABI changes
  -Wptrauth-null-pointers # signing a null pointer will yield a non-null pointer
  -Wqualified-void-return-type # function cannot return qualified void type X
  -Wrange-loop-analysis # covers -Wrange-loop-construct, -Wrange-loop-bind-reference
  -Wrange-loop-bind-reference # loop variable X binds to a temporary value produced by a range
  -Wrange-loop-construct # a range-based for-loop is creating unnecessary copies
  -Wread-only-types # object of type X cannot be placed in read-only memory
  -Wredeclared-class-member # class member cannot be redeclared
  -Wreduced-bmi-output-overrided # the implicit output of a reduced BMI being overridden
  -Wredundant-attribute # redundant X attribute
  -Wredundant-consteval-if # consteval if is always true in an unevaluated context
  -Wredundant-decls # multiple declarations of the same object
  -Wredundant-move # redundant calls to std::move
  -Wredundant-parens # redundant parentheses surrounding declarator
  # -Wredundant-tags # a class or enumerated type is referenced using a redundant class-key
  -Wreference-tu-local-entity-in-other-tu # instantiation of X triggers reference to TU-local
  -Wregister # uses of register storage specifier
  -Wreinterpret-base-class # 'reinterpret_cast' from class X to its virtual base Y behaves
  -Wreorder # the compiler reorders code
  -Wreorder-ctor # initializer order does not match the declaration order
  -Wreorder-init-list # ISO C++ requires field designators to be specified in declaration order
  -Wrequires-super-attribute # X attribute cannot be applied to methods in protocols
  -Wreserved-attribute-identifier # X is a reserved attribute identifier
  -Wreserved-identifier # identifier X is reserved because it starts with '_' at global scope
  -Wreserved-macro-identifier # macro name is a reserved identifier
  -Wreserved-module-identifier # X is a reserved name for a module
  -Wreserved-user-defined-literal # invalid suffix on literal
  -Wrestrict # an argument passed to a restrict- qualified parameter aliases with another argument
  -Wrestrict-expansion # macro X has been marked as unsafe for use in headers: Y
  -Wretained-language-linkage # friend function X retaining previous language linkage
  -Wreturn-local-addr # returning a pointer/reference to a local or temporary variable
  -Wreturn-mismatch # void-returning functions return a non-void expressions
  -Wreturn-type # a function's return type defaults to 'int' (C) or inconsistent return types (C++)
  -Wreturn-type-c-linkage # X has C-linkage specified, but returns user-defined type Y
  -Wrewrite-not-bool # ISO C++20 requires return type of selected 'operator==' function
  -Wrtti # typeid will not work since RTTI data is disabled by -fno-rtti-data
  -Wsarif-format-unstable # diagnostic formatting in SARIF mode is currently unstable
  -Wscalable-static-analysis-framework # must enable some summary extractors
  -Wscalar-storage-order # suspicious constructs involving reverse scalar storage order
  -Wsection # duplicate code segment specifiers
  -Wself-assign # explicitly assigning value of variable of type X to itself
  -Wself-assign-field # assigning field to itself
  -Wself-assign-overloaded # explicitly assigning value of variable of type X to itself
  -Wself-move # a value is moved to itself with std::move
  -Wsemicolon-before-method-body # semicolon before method body is ignored
  -Wsentinel # not enough variable arguments in X declaration to fit a sentinel
  -Wsequence-point # possible violations of sequence point rules
  -Wserialized-diagnostics # unable to merge a subprocess's serialized diagnostics
  -Wsfinae-incomplete=2 # an incomplete type affecting semantics in a non-error context
  -Wshadow # one variable shadows another
  -Wshadow-all # covers -Wshadow
  -Wshadow-field # parameter X of Y shadows member inherited from type Z
  -Wshadow-field-in-constructor # constructor parameter X shadows the field Y of Z
  -Wshadow-field-in-constructor-modified # modifying constructor parameter X that shadows a field
  -Wshadow-header # multiple candidates for header 'X' found
  -Wshadow-uncaptured-local # declaration shadows a local variable
  -Wshadow=compatible-local # one local variable shadows another local variable or parameter
  -Wshadow=local # one local variable shadows another local variable or parameter
  -Wshift-bool # right shifting a 'bool' implicitly converts it to 'int'
  -Wshift-count-negative # shift count is negative
  -Wshift-count-overflow # shift count >= width of type
  -Wshift-negative-value # left shifting a negative value
  -Wshift-op-parentheses # operator 'X' has lower precedence than 'Y'
  -Wshift-overflow # left shift of a signed value overflows
  -Wshift-overflow=2 # left shift of a signed value overflows
  -Wshift-sign-overflow # signed shift result sets the sign bit of the shift expression's
  # -Wshorten-64-to-32 # implicit conversion loses integer precision: X to Y
  -Wsign-compare # signed-unsigned comparisons
  # -Wsign-conversion # implicit type conversions between signed and unsigned integers
  # -Wsign-promo # overload promotes from unsigned to signed
  -Wsigned-unsigned-wchar # 'X' cannot be signed or unsigned
  -Wsimdlen # the clause simdlen(1) has no effect when targeting aarch64
  -Wsingle-bit-bitfield-constant-conversion # implicit truncation from X to a one-bit wide
  -Wsized-deallocation # missing sized deallocation functions
  -Wsizeof-array-argument # sizeof is applied on a parameter declared as an array
  -Wsizeof-array-decay # sizeof on pointer operation will return size of X instead of Y
  -Wsizeof-array-div # divisions of two sizeof operators when the first one is applied to an array
  -Wsizeof-pointer-div # suspicious divisions of two sizeof expressions that don't work correctly
  -Wsizeof-pointer-memaccess # suspicious length parameters to certain string functions
  -Wslash-u-filename # '/UX' treated as the '/U' option
  -Wslh-asm-goto # speculative load hardening does not protect functions with asm goto
  -Wsometimes-uninitialized # variable X is used uninitialized whenever 'Y' condition is true
  -Wsource-mgr # a problem loading or mapping a source file
  -Wstack-exhausted # stack nearly exhausted
  -Wstack-protector # not issuing stack smashing protection for some reason
  -Wstatic-float-init # in-class initializer for static data member of type X requires 'constexpr'
  -Wstatic-in-inline # using static function X in an inline function with external linkage
  -Wstatic-inline-explicit-instantiation # ignoring 'static' keyword on explicit template
  -Wstatic-local-in-inline # non-constant static local variable in inline function
  -Wstatic-self-init # static variable X is suspiciously used within its own initialization
  -Wstdlibcxx-not-found # include path for libstdc++ headers not found
  -Wstrict-aliasing=2 # 1 is stronger but reports Boolector's own type punning
  -Wstrict-null-sentinel # uncasted NULL used as sentinel
  # -Wstrict-overflow=5 # optimizations that assume that signed overflow is undefined
  -Wstrict-primary-template-shadow # declaration of X shadows template parameter
  -Wstring-compare # calls to strcmp and strncmp used in equality expressions
  -Wstring-concatenation # suspicious concatenation of string literals in an array initialization
  -Wstring-conversion # implicit conversion turns string literal into bool: X to Y
  -Wstring-plus-char # adding X to a string pointer does not append to the string
  -Wstring-plus-int # adding X to a string does not append to the string
  -Wstringop-overflow=4 # buffer overflow in string manipulation functions like memcpy and strcpy
  -Wstringop-overread # reading past the end of a source array in string manipulation functions
  -Wstringop-truncation # truncation in string manipulation functions like strncat and strncpy
  -Wstrlcpy-strlcat-size # size argument in X call appears to be size of the source
  -Wstrncat-size # the value of the size argument to 'strncat' is wrong
  -Wsubobject-linkage # a class type has a base or a field whose type uses the anonymous namespace
  # -Wsuggest-attribute=cold # functions which might be candidates for __attribute__((cold))
  # -Wsuggest-attribute=const # functions which might be candidates for __attribute__((const))
  -Wsuggest-attribute=malloc # functions which might be candidates for __attribute__((malloc))
  # -Wsuggest-attribute=pure # functions which might be candidates for __attribute__((pure))
  -Wsuggest-destructor-override # X overrides a destructor but is not marked 'override'
  # -Wsuggest-final-methods # C++ virtual methods where adding final keyword
  # -Wsuggest-final-types # C++ polymorphic types where adding final keyword
  -Wsuggest-override # suggest that the override keyword be used when the declaration
  -Wsuspicious-bzero # 'size' argument to bzero is '0'
  -Wsuspicious-memaccess # covers -Wsizeof-pointer-memaccess
  -Wswift-name-attribute # X attribute is missing parameter label clause
  -Wswitch # enumerated switches, with no default, missing a case
  -Wswitch-bool # switches with boolean controlling expression
  # -Wswitch-default # enumerated switches missing a 'default:' statement
  # -Wswitch-enum # all enumerated switches missing a specific case
  -Wswitch-outside-range # switch values that are outside of the switch's type range
  -Wswitch-unreachable # statements between switch's controlling expression and the first case
  -Wsync-alignment # __sync builtin operation must have natural alignment (consider using __atomic)
  -Wsync-fetch-and-nand-semantics-changed # the semantics of this intrinsic changed with GCC
  -Wsync-nand # __sync_fetch_and_nand and __sync_nand_and_fetch built-in functions are used
  -Wtarget-clones-mixed-specifiers # mixing 'target_clones' specifier mechanisms
  -Wtautological-bitwise-compare # bitwise or with non-zero value always evaluates to true
  -Wtautological-compare # a comparison always evaluates to true or false
  -Wtautological-constant-compare # result of comparison of constant X with expression of type Y
  -Wtautological-constant-in-range-compare # covers -Wtype-limits
  -Wtautological-constant-out-of-range-compare # result of comparison of constant X
  -Wtautological-negation-compare # '||' of a value and its negation always evaluates to true
  -Wtautological-overlap-compare # non-overlapping comparisons always evaluate to false
  -Wtautological-pointer-compare # comparison of address of 'X' not equal to a null pointer
  -Wtautological-type-limit-compare # result of comparison X Y Z is always W
  -Wtautological-undefined-compare # 'this' pointer cannot be null in well-defined C++ code
  -Wtautological-unsigned-char-zero-compare # result of comparison of X Y char expression
  -Wtautological-unsigned-enum-zero-compare # result of comparison of X Y unsigned enum expression
  -Wtautological-unsigned-zero-compare # result of comparison of X Y unsigned expression
  -Wtautological-value-range-compare # result of comparison of X Y Z-bit signed value is always W
  -Wtcb-enforcement # calling X is a violation of trusted computing base 'Y'
  -Wtemplate-body # diagnose errors when parsing a template
  -Wtemplate-id-cdtor # simple-template-id in a constructor or destructor
  -Wtemplate-in-declaration-name # 'template' cannot be used after a declarative nested name
  -Wtemplate-names-tu-local # templates naming TU-local entities in a module
  -Wtentative-definition-array # tentative array definition assumed to have one element
  -Wtentative-definition-compat # duplicate declaration of X is invalid in C++
  -Wtentative-definition-incomplete-type # tentative definition of variable with internal linkage
  -Wterminate # a throw expression will always result in a call to terminate()
  -Wthread-safety # covers -Wthread-safety-attributes
  -Wthread-safety-analysis # cannot resolve lock expression
  -Wthread-safety-attributes # ignoring X attribute because its argument is invalid
  -Wthread-safety-beta # thread safety beta warning
  # -Wthread-safety-negative # acquiring X 'Y' requires negative capability 'Z'
  -Wthread-safety-pointer # passing pointer X requires holding Y 'Z'
  -Wthread-safety-precise # calling function X requires holding Y 'Z'
  -Wthread-safety-reference # passing variable X by reference requires holding Y 'Z'
  -Wthread-safety-reference-return # returning variable X by reference requires holding Y 'Z'
  -Wthread-safety-verbose # thread safety verbose warning
  # -Wtrailing-whitespace # trailing whitespace on lines except when in raw string literals
  -Wtrampolines # a trampoline is generated
  -Wtrigraphs # trigraphs are encountered that might affect the meaning of the program
  -Wtrivial-auto-var-init # cases where -ftrivial-auto-var-init cannot initialize an auto variable
  -Wtsan # unsupported features in ThreadSanitizer
  -Wtype-limits # a comparison is always true or always false due to the limited range of the data
  -Wtype-safety # specified X type tag requires a null pointer
  -Wtypename-missing # missing 'typename' prior to dependent type name X
  -Wunable-to-open-stats-file # unable to open statistics output file 'X': 'Y'
  -Wunaligned-access # field X within Y is less aligned than Z and is usually due to Y being packed
  -Wunaligned-qualifier-implicit-cast # implicit cast from type X to type Y drops __unaligned
  -Wunavailable-declarations # X may be unavailable because the receiver type is unknown
  -Wundef # an #if testing a macro that was never defined
  -Wundef-prefix # X is not defined, evaluates to 0
  -Wundef-true # 'true' is not defined, evaluates to 0
  -Wundefined-arm-za # builtin call is not valid when calling from a function without active ZA
  -Wundefined-arm-zt0 # builtin call is not valid when calling from a function without active ZT0
  -Wundefined-bool-conversion # 'this' pointer cannot be null in well-defined C++ code
  -Wundefined-func-template # instantiation of function X required here
  -Wundefined-inline # inline function X is not defined
  -Wundefined-internal # function X has internal linkage but is not defined
  -Wundefined-internal-type # ISO C++ requires a definition in this translation unit for function X
  -Wundefined-reinterpret-cast # reinterpret_cast from X to Y has undefined behavior
  -Wundefined-var-template # instantiation of variable X required here
  -Wunderaligned-exception-object # underaligned exception object thrown
  -Wunderlying-atomic-qualifier-ignored # '_Atomic' qualifier ignored
  -Wunderlying-cv-qualifier-ignored # 'const' and 'volatile' qualifiers in enumeration underlying
  -Wunevaluated-expression # expression with side effects has no effect in an unevaluated context
  -Wunguarded-availability # X is unavailable
  -Wunguarded-availability-new # X is unavailable
  -Wunicode # invalid forms of delimited or named escape sequences
  -Wunicode-homoglyph # treating Unicode character <U+X> as an identifier character
  -Wunicode-whitespace # treating Unicode character as whitespace
  -Wunicode-zero-width # identifier contains Unicode character <U+X>
  -Wuninitialized # uninitialized automatic variables
  -Wuninitialized-const-pointer # variable X is uninitialized when passed as a const pointer
  -Wuninitialized-const-reference # variable X is uninitialized when passed as a const reference
  -Wuninitialized-explicit-init # field X requires explicit initialization
  -Wunique-object-duplication # X may be duplicated when built into a shared library: it is mutable
  -Wunknown-argument # joined argument treated as 'X'
  -Wunknown-assumption # unknown assumption string 'X'
  -Wunknown-attributes # unknown attribute X ignored
  -Wunknown-directives # invalid preprocessing directive, did you mean '#X'?
  -Wunknown-escape-sequence # unknown escape sequence '\\X'
  -Wunknown-pragmas # unrecognized pragmas
  -Wunknown-sanitizers # unknown sanitizer 'X' ignored
  -Wunknown-warning-option # unknown warning option 'X'
  -Wunnamed-type-template-args # template argument uses unnamed type
  -Wunnecessary-virtual-specifier # virtual method X is inside a 'final' class
  -Wunneeded-internal-declaration # 'static' function X declared in header file
  -Wunneeded-member-function # member function X is not needed and will not be emitted
  -Wunqualified-std-cast-call # unqualified call to 'X'
  # -Wunreachable-code # code will never be executed
  # -Wunreachable-code-aggressive # covers -Wunreachable-code
  # -Wunreachable-code-break # 'break' will never be executed
  -Wunreachable-code-fallthrough # fallthrough annotation in unreachable code
  -Wunreachable-code-generic-assoc # due to lvalue conversion of the controlling expression
  -Wunreachable-code-loop-increment # loop will run at most once (loop increment never executed)
  # -Wunreachable-code-return # 'return' will never be executed
  # -Wunsafe-buffer-usage # X is an unsafe pointer used for buffer access
  -Wunsafe-buffer-usage-in-container # the two-parameter std::span construction
  -Wunsafe-buffer-usage-in-format-attr-call # formatting function X is unsafe
  # -Wunsafe-buffer-usage-in-libc-call # function X is unsafe
  -Wunsafe-buffer-usage-in-static-sized-array # direct access on T[N] is unsafe due to the lack
  -Wunsafe-buffer-usage-in-unique-ptr-array-access # direct access using operator[]
  -Wunsupported-abi # float ABI 'X' is not supported by current library
  -Wunsupported-abs # ignoring '-mabs=2008' option because the 'X' architecture does not support it
  -Wunsupported-availability-guard # availability not guarded by __builtin_available
  -Wunsupported-cb # ignoring '-mcompact-branches=' option
  -Wunsupported-dll-base-class-template # propagating dll attribute to already instantiated base
  -Wunsupported-floating-point-opt # overriding currently unsupported use of floating point
  -Wunsupported-friend # dependent nested name specifier X for friend template declaration
  -Wunsupported-gpopt # ignoring '-mgpopt' option as it cannot be used with the implicit usage
  -Wunsupported-nan # ignoring '-mnan=2008' option because the 'X' architecture does not support it
  -Wunsupported-target-opt # debug information option 'X' is not supported for target 'Y'
  -Wunsupported-visibility # target does not support 'protected' visibility
  -Wunterminated-string-initialization # character arrays initialized as unterminated character
  -Wunusable-partial-specialization # class template partial specialization contains a template
  -Wunused # enable all -Wunused- warnings
  -Wunused-but-set-global # variable X set but not used
  -Wunused-but-set-parameter # a function parameter is only set, otherwise unused
  -Wunused-but-set-parameter=3 # a function parameter is only set, otherwise unused
  -Wunused-but-set-variable # a variable is only set, otherwise unused
  -Wunused-but-set-variable=3 # a variable is only set, otherwise unused
  -Wunused-command-line-argument # argument unused during compilation: 'X'
  -Wunused-comparison # equality comparison result unused
  -Wunused-const-variable # a const variable is unused
  -Wunused-const-variable=2 # a const variable is unused
  # -Wunused-exception-parameter # unused exception parameter X
  -Wunused-function # a function is unused
  -Wunused-getter-return-value # property access result unused - getters should not be used
  -Wunused-label # a label is unused
  -Wunused-lambda-capture # lambda capture X is not used
  -Wunused-local-typedefs # typedefs locally defined in a function are not used
  # -Wunused-macros # macros defined in the main file that are not used
  -Wunused-member-function # unused member function X
  -Wunused-parameter # a function parameter is unused
  -Wunused-private-field # private field X is not used
  -Wunused-result # a caller of a function
  -Wunused-template # unused function template X
  -Wunused-value # an expression value is unused
  -Wunused-variable # a variable is unused
  -Wunused-volatile-lvalue # expression result unused
  -Wuse-after-free=3 # uses of pointers to deallocated storage
  -Wused-but-marked-unused # X was marked unused but was used
  # -Wuseless-cast # useless casts
  -Wuser-defined-literals # user-defined literal suffixes not starting with '_' are reserved
  -Wuser-defined-warnings # whatever #pragma clang warning prints
  -Wvarargs # questionable usage of the macros used to retrieve variable arguments
  -Wvariadic-macro-arguments-omitted # passing no argument for the '...' parameter of a variadic
  -Wvariadic-macros # using variadic macros
  -Wvec-elem-size # vector operands do not have the same elements sizes (X and Y)
  -Wvector-conversion # implicit conversion truncates vector: X to Y
  -Wvector-operation-performance # a vector operation is compiled outside the SIMD
  -Wvexing-parse # the most vexing parse syntactic ambiguity
  -Wvirtual-move-assign # a virtual base has a non-trivial move assignment operator
  -Wvisibility # declaration of X will not be visible outside of this function
  -Wvla # a variable length array is used
  -Wvla-cxx-extension # variable length arrays in C++ are a Clang extension
  -Wvla-extension # variable length arrays are a C99 feature
  -Wvla-extension-static-assert # variable length arrays in C++ are a Clang extension
  -Wvla-parameter # mismatched declarations of VLA parameters
  -Wvoid-pointer-to-enum-cast # cast to smaller integer type X from Y
  -Wvoid-pointer-to-int-cast # cast to smaller integer type X from Y
  -Wvoid-ptr-dereference # ISO C does not allow indirection on operand of type X
  -Wvolatile # deprecated uses of volatile qualifier
  -Wvolatile-register-var # a register variable is declared volatile
  -Wweak-template-vtables # this warning is no longer in use
  -Wweak-vtables # X has no out-of-line virtual method definitions
  -Wwrite-strings # in C++
  -Wxor-used-as-pow # xor operators where it appears the user meant exponentiation
  # -Wzero-as-null-pointer-constant # a literal '0' is used as null pointer
  -Wzero-length-array # zero size arrays are an extension
  -Wzero-length-bounds # accesses to interior zero-length array members
)

# GCC lists its warnings under --help=warnings and clang under
# --print-diagnostic-options, so try both and keep whichever answers. The list
# above names more than any one release knows, and an unknown -W is fatal to
# GCC, so a flag missing from the answer is left out.
execute_process(
  COMMAND "${CMAKE_CXX_COMPILER}" --help=warnings
  OUTPUT_VARIABLE cxx_warnings_listing
  ERROR_QUIET
)
string(REGEX MATCHALL "-W[A-Za-z0-9+=_#-]+" cxx_warnings_offered "${cxx_warnings_listing}")
if(NOT "-Wall" IN_LIST cxx_warnings_offered)
  execute_process(
    COMMAND "${CMAKE_CXX_COMPILER}" --print-diagnostic-options
    OUTPUT_VARIABLE cxx_warnings_listing
    ERROR_QUIET
  )
  string(REGEX MATCHALL "-W[A-Za-z0-9+=_#-]+" cxx_warnings_offered "${cxx_warnings_listing}")
endif()

if(NOT "-Wall" IN_LIST cxx_warnings_offered)
  message(STATUS "${CMAKE_CXX_COMPILER_ID} does not list its warnings; passing none")
  set(cxx_warnings "")
  if(SMT_SWITCH_STRICT)
    # Not that -Werror is known to be refused, but that nothing here is known
    # of this compiler, and an option it does not have would stop the build.
    message(
      STATUS
      "--strict cannot be honoured for ${CMAKE_CXX_COMPILER_ID}; warnings stay warnings"
    )
  endif()
else()
  list(JOIN cxx_warnings_offered ";" cxx_warnings_offered_joined)
  set(cxx_warnings_offered_joined ";${cxx_warnings_offered_joined};")
  set(cxx_warnings "")
  foreach(cxx_warning IN LISTS cxx_warnings_wanted)
    # GCC lists a flag taking a value as -Wname=, so ask about that shape too.
    string(REGEX REPLACE "=.*$" "=" cxx_warning_valued "${cxx_warning}")
    string(FIND "${cxx_warnings_offered_joined}" ";${cxx_warning};" cxx_warning_at)
    string(FIND "${cxx_warnings_offered_joined}" ";${cxx_warning_valued};" cxx_warning_valued_at)
    if(NOT cxx_warning_at EQUAL -1 OR NOT cxx_warning_valued_at EQUAL -1)
      list(APPEND cxx_warnings "${cxx_warning}")
    endif()
  endforeach()

  # GCC lists flags it then refuses for a C++ translation unit, so probe which
  # ones it would reject with a test compilation.
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/cxx-warnings-probe.cpp" "")
  execute_process(
    COMMAND
      "${CMAKE_CXX_COMPILER}" -fsyntax-only ${cxx_warnings}
      "${CMAKE_CURRENT_BINARY_DIR}/cxx-warnings-probe.cpp"
    ERROR_VARIABLE cxx_warnings_refused
    OUTPUT_QUIET
  )
  string(
    REGEX MATCHALL "-W[A-Za-z0-9+=_-]+[^ ]* is valid for"
    cxx_warnings_refused
    "${cxx_warnings_refused}"
  )
  foreach(cxx_warning IN LISTS cxx_warnings_refused)
    string(REGEX MATCH "-W[A-Za-z0-9+=_-]+" cxx_warning "${cxx_warning}")
    list(REMOVE_ITEM cxx_warnings "${cxx_warning}")
  endforeach()

  # Exemptions of one file from one warning, for code generated here rather
  # than written. Clang reads them from version 20; a compiler refusing the
  # option gets none.
  set(cxx_warnings_mappings "${CMAKE_CURRENT_LIST_DIR}/warning-suppressions.txt")
  execute_process(
    COMMAND
      "${CMAKE_CXX_COMPILER}" -fsyntax-only
      "--warning-suppression-mappings=${cxx_warnings_mappings}"
      "${CMAKE_CURRENT_BINARY_DIR}/cxx-warnings-probe.cpp"
    RESULT_VARIABLE cxx_warnings_mappings_result
    OUTPUT_QUIET
    ERROR_QUIET
  )
  if(cxx_warnings_mappings_result EQUAL 0)
    list(APPEND cxx_warnings "--warning-suppression-mappings=${cxx_warnings_mappings}")
  endif()

  if(SMT_SWITCH_STRICT)
    list(APPEND cxx_warnings -Werror)
  endif()
endif()

# Named, so that code which does not build clean under these can take exactly
# this option back off, rather than guess which of its pieces are warnings.
set(SMT_SWITCH_CXX_WARNING_OPTIONS "$<$<COMPILE_LANGUAGE:CXX>:${cxx_warnings}>")
add_compile_options("${SMT_SWITCH_CXX_WARNING_OPTIONS}")

function(smt_switch_drop_warning_options saved_var)
  get_directory_property(options_inherited COMPILE_OPTIONS)
  string(
    REPLACE "${SMT_SWITCH_CXX_WARNING_OPTIONS}"
    ""
    options_without_warnings
    "${options_inherited}"
  )
  list(REMOVE_ITEM options_without_warnings "")
  set_directory_properties(PROPERTIES COMPILE_OPTIONS "${options_without_warnings}")
  set(${saved_var} "${options_inherited}" PARENT_SCOPE)
endfunction()
