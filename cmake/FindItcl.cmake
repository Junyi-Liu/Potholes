
include(FindPackageHandleStandardArgs)

IF(NOT ITCL_FOUND)
   GET_PROPERTY(ENVIRONMENT_PLATFORM_DIR GLOBAL PROPERTY ENVIRONMENT_PLATFORM_DIR)

  FIND_LIBRARY(ITCL_LIBRARY 
    NAMES itcl3.4
    HINTS /System/Library/Tcl/8.5/itcl3.4
    	  ${ENVIRONMENT_PLATFORM_DIR}/lib64)
    #PATHS ${ENVIRONMENT_PLATFORM_DIR}/lib/tcl/itcl3.4)
    
  FIND_PATH(ITCL_INCLUDE_DIR itcl.h 
    HINTS /Users/Junyi/research/Tools/itcl3.4/generic
    #HINTS ${ENVIRONMENT_PLATFORM_DIR}/include
    DOC "ITCL includes")
ENDIF(NOT ITCL_FOUND)


find_package_handle_standard_args(itcl DEFAULT_MSG ITCL_LIBRARY ITCL_INCLUDE_DIR)
