# usage:
# Make sure port.sh and port.pl are executable (chmod u+x port.pl port.sh)
# in the scripts directory, type ./port.sh to port the files specified below
# from the standard library to the HoTT library
# This file requires both port.pl and port.txt to be in the scripts folder
#
# WARNING: This will overwrite all destination files without warning!
#
# See port.pl for the syntax, if you want to add new files to port.

now=$(date +"%B %d, %Y")
./port.pl ../library/data/nat/basic.lean ../hott/types/nat/basic2.hlean "Module: data.nat.basic" "Module: types.nat.basic
(Ported from standard library file data.nat.basic on $now)" "import logic.connectives data.num algebra.binary algebra.ring" "import algebra.ring" "open binary eq.ops" "open core prod binary" "nat.no_confusion H \(λe, e\)" "lift.down (nat.no_confusion H (λe, e))"

# ./port.pl ../library/logic/connectives.lean ../hott/logic.hlean
/port.pl ../library/algebra/ring.lean ../hott/algebra/ring.hlean "import logic.eq logic.connectives data.unit data.sigma data.prod" "import algebra.group" "import algebra.function algebra.binary algebra.group" "" "open eq eq.ops" "open core"
