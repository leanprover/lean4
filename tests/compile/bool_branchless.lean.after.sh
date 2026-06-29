set -euo pipefail

lean_file="${0%.after.sh}"
c_file="${lean_file}.c"

grep -Eq '= lean_bool_not\(' "$c_file"
grep -Eq '= lean_bool_xor\(' "$c_file"
grep -Eq '= lean_bool_to_nat\(' "$c_file"
