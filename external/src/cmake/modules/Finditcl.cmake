
include(FindPackageHandleStandardArgs)

IF(NOT ITCL_FOUND)
  FIND_LIBRARY(ITCL_LIBRARY libitcl3.4.dylib 
    PATHS "${PROJECT_SOURCE_DIR}/external/build/itcl3.4.1")
  FIND_PATH(ITCL_INCLUDE_DIRS itcl.h "${PROJECT_SOURCE_DIR}/external/include" DOC "ITCL includes")
ENDIF(NOT ITCL_FOUND)


find_package_handle_standard_args(itcl DEFAULT_MSG ITCL_LIBRARY ITCL_INCLUDE_DIRS)
