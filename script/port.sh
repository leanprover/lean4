# usage:
# Make sure port.sh and port.pl are executable (chmod u+x port.pl port.sh)
# in the scripts directory, type ./port.sh to port the files specified below
# from the standard library to the HoTT library
# This file requires both port.pl and port.txt to be in the scripts folder
#
# WARNING: This will overwrite all destination files without warning!
#
# to add a new file to port to this file, add a new line of the form 
#
#  ./port.pl ../library/path/to/source.lean ../hott/path/to/destination.hlean "from1" "to1" "from2" "to2" [...]
#
# This will port the file ../library/path/to/source.lean to ../hott/path/to/destination.hlean 
# renaming core definitions form the standard library to core definitions in the HoTT library. 
# These renamings are specified in port.txt. Additional changes can be added by the extra arguments.
# The extra arguments will replace "fromi" by "toi" in the specified file, 
# before doing any other renamings.
#
# Note: parentheses (and other characters with a special meaning in regular expressions)
# have to be escaped

now=$(date +"%B %d, %Y")
./port.pl ../library/data/nat/basic.lean ../hott/types/nat/basic.hlean "Module: data.nat.basic" "Module: types.nat.basic
(Ported from standard library file data.nat.basic on $now)" "import logic.connectives data.num algebra.binary algebra.ring" "import algebra.binary" "open binary eq.ops" "open core prod binary" "nat.no_confusion H \(λe, e\)" "lift.down (nat.no_confusion H (λe, e))"

# ./port.pl ../library/logic/connectives.lean ../hott/logic.hlean
