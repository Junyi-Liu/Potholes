
proc get_platform_library_extension { dir } { 
    switch $::tcl_platform(os) { 
    Darwin {
        load [file join $dir ../lib/libPotholes.dylib] 
    }
    Linux { 
        load [file join $dir ../lib/libPotholes.so] 
    }
    default {
    error "Error : Unsupported Platform"
    }
    }
    

}

package ifneeded Potholes 1.0 [list apply {dir {
#    set ::env(ITCL_LIBRARY) [file join $::env(ENVIRONMENT_PLATFORM_DIR) lib tcl]
    switch $::tcl_platform(os) { 
	Darwin {
	}
	Linux { 
	    set ::env(ITCL_LIBRARY) [file join $::env(ENVIRONMENT_PLATFORM_DIR)/.. lib64 tcl8.5 itcl3.4]
	}
	default {
	    error "Error : Unsupported Platform"
	}
    }    
   
    uplevel 1 [list source [file join $dir preparePackage.tcl] ]

    get_platform_library_extension $dir 

    #puts "after PROJECT setting"

    #uplevel 1 [list source [file join $dir loadPackage.tcl] ] 
    uplevel 1 [list source [file join $dir analysis.tcl] ]
    uplevel 1 [list source [file join $dir scop.tcl] ]
    uplevel 1 [list source [file join $dir project.tcl] ]  
}} $dir]
