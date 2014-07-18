# Locate libclangBasic
#
# This module defines
#  PET_FOUND, if false, do not try to link to clang
#  PET_LIBRARY, where to find clang
#  PET_INCLUDE_DIR, where to find yaml.h
#
# By default, the dynamic libraries of clang will be found. To find the static ones instead,
# you must set the PET_STATIC_LIBRARY variable to TRUE before calling find_package(YamlCpp ...).
#
# If clang is not installed in a standard path, you can use the PET_DIR CMake variable
# to tell CMake where clang is.

# attempt to find static library first if this is set

GET_PROPERTY(ENVIRONMENT_PLATFORM_DIR GLOBAL PROPERTY ENVIRONMENT_PLATFORM_DIR)

# find the clang include directory
find_path(PET_INCLUDE_DIR 
	  NAMES pet.h expr.h tree.h
          PATH_SUFFIXES include 
          PATHS
          #/Users/Junyi/research/HLS/pet
	  ${ENVIRONMENT_PLATFORM_DIR}/include
	  )

# find the clang library
find_library(PET_LIBRARY
             NAMES pet
             PATH_SUFFIXES lib64 lib
             PATHS   /usr/local
 	     ${ENVIRONMENT_PLATFORM_DIR}/lib
                   )

set (PET_LIBRARIES ${PET_LIBRARY})

# handle the QUIETLY and REQUIRED arguments and set PET_FOUND to TRUE if all listed variables are TRUE
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(PET DEFAULT_MSG PET_LIBRARY PET_INCLUDE_DIR)


#mark_as_advanced(PET_INCLUDE_DIR PET_LIBRARY)

