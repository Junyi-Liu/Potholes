#!/usr/bin/tclsh

set lib_dir "$::env(ENVIRONMENT_PLATFORM_DIR)/lib"
set scp_dir "$::env(ENVIRONMENT_PLATFORM_DIR)/scripts"

set auto_path [linsert $auto_path 0 $scp_dir]
set auto_path [linsert $auto_path 0 $lib_dir]

puts $auto_path

package require Potholes

set process_pid [pid]
puts "The process pid = $process_pid"

#after 10000
after 1000

set database "/Users/Junyi/research/HLS/application/pth_play/compile_commands.json"

# construct analysis object
set analysis [Potholes::Analysis #auto $database]

# load sources based on database
foreach source [$analysis get -sources] { 
    puts $source
}

# get Scop object and apply transformation
foreach scop [$analysis get -scops] { 
    puts $scop 
    set filename [$scop filename]
    puts $filename
    $analysis transform -promote-scop-to-function $scop
}

set solution "Solution_test"
set project [Potholes::Project #auto $analysis $solution]

itcl::delete object $project
itcl::delete object $analysis
