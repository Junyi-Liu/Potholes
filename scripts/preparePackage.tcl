rename ::source ::Potholes::Source_1

set ::Potholes::UnsupportedPlatform -1

proc ::source args {
    if {[lsearch $args "-rsrc"] == -1} { 
	uplevel 1 ::Potholes::Source_1 $args
    } else {
	throw ::Potholes::UnsupportedPlatform 
    }
}
