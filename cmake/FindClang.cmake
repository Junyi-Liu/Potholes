# Locate libclangBasic
#
# This module defines
#  CLANG_FOUND, if false, do not try to link to clang
#  CLANG_LIBRARY, where to find clang
#  CLANG_INCLUDE_DIR, where to find yaml.h
#
# By default, the dynamic libraries of clang will be found. To find the static ones instead,
# you must set the CLANG_STATIC_LIBRARY variable to TRUE before calling find_package(YamlCpp ...).
#
# If clang is not installed in a standard path, you can use the CLANG_DIR CMake variable
# to tell CMake where clang is.

# attempt to find static library first if this is set

GET_PROPERTY(ENVIRONMENT_PLATFORM_DIR GLOBAL PROPERTY ENVIRONMENT_PLATFORM_DIR)


# find the clang include directory
find_path(CLANG_INCLUDE_DIR clang/Basic/LLVM.h
          PATH_SUFFIXES include
          PATHS
          /usr/local/include/
    ${ENVIRONMENT_PLATFORM_DIR}/include
	  )

set (CLANG_LIBS
	clang
	clangFrontend
	clangAST
	clangAnalysis
	clangBasic
	clangCodeGen
	clangDriver
	clangEdit
	clangFrontendTool
	clangTooling
	clangLex
	clangParse
	clangRewriteCore
	clangSema
	clangSerialization
	clangStaticAnalyzerCheckers
	clangStaticAnalyzerCore
	clangStaticAnalyzerFrontend
)

foreach(LIB ${CLANG_LIBS})
	    FIND_LIBRARY(${LIB}_FOUND 
			 NAMES ${LIB}
			 PATH_SUFFIXES lib64 lib
			 PATHS /usr/local
			       ${ENVIRONMENT_PLATFORM_DIR}/lib
			 )
 	    list(APPEND CLANG_LIBRARIES ${${LIB}_FOUND})
endforeach(LIB)



# handle the QUIETLY and REQUIRED arguments and set CLANG_FOUND to TRUE if all listed variables are TRUE
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CLANG DEFAULT_MSG CLANG_LIBRARIES CLANG_INCLUDE_DIR)
mark_as_advanced(CLANG_INCLUDE_DIR CLANG_LIBRARIES)

