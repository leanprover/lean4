#!/bin/bash
if [ $# -ne 2 -a $# -ne 3 ]; then
    echo "Usage: compare_with_glpk.sh --min [--mpq] mps_file_name"
    echo "or compare_with_glpk.sh --max [--mpq] mps_file_name"
    exit 1
fi
minmax_option=$1
if [ $minmax_option != "--min" -a $minmax_option != "--max" ]; then
    echo "Usage: compare_with_glpk.sh --min [--mpq] mps_file_name"
    echo "or compare_with_glpk.sh --max [--mpq] mps_file_name"
    exit 1
fi

if [ $minmax_option == "--min"  ]; then
    prefix="_min";
else
    if [ $minmax_option == "--max"  ]; then
        prefix="_max"
    else 
        echo "Usage: compare_with_glpk.sh minmax_option mps_file_name"
        echo  "where minmax_option can be --min or --max"
        exit 1
    fi
fi
mpq_option=""
if [ $# -eq 3 ]; then
    mpq_option=$2
    if [ $mpq_option != "--mpq" ]; then
        echo "Usage: compare_with_glpk.sh --min [--mpq] mps_file_name"
        echo "or compare_with_glpk.sh --max [--mpq] mps_file_name"
        exit 1
    fi
    mps_input_file=$3
else 
    mps_input_file=$2
fi

filename=$(basename "$mps_input_file")
extension="${filename##*.}"
filename="${filename%.*}"
#testpath="${mps_input_file%/*}"
testpath="/tmp"
glpsol_output="${testpath}""/""${filename}"$prefix".out"
lp_tst_output="${testpath}""/""${filename}"$prefix".lp_tst.out""$mpq_option"
lp_tst=$HOME"/projects/lean/build/release/tests/util/lp/lp_tst"
cost_compare=$HOME"/projects/lean/build/release/tests/util/lp/double_compare"

if  [ $# -ne 3 ]; then
    glpsol --nointopt --nomip $minmax_option --tmlim 60 -o "${glpsol_output}" "${mps_input_file}" > /dev/null
    status=$?
    if [ $status -ne 0 ]; then
        echo "glpsol failed"
        exit 2
    fi
fi
              
function get_status_from_output() {
    local  __resultvar=$1
    local status_str=$(grep Status $2)
    local tokens=( $status_str )
    local  myresult=${tokens[1]}
    eval $__resultvar="'$myresult'" 
}

function get_cost_from_glpout() {
    local  __resultvar=$1
    local status_str=$(grep Objective "${glpsol_output}")
    local tokens=( $status_str )
    local  myresult=${tokens[3]}
    eval $__resultvar="'$myresult'" 
}

get_status_from_output glp_status $glpsol_output

get_cost_from_glpout glp_cost

# ~/projects/lean/build/debug/tests/util/lp/double_compare 24501.2549 2.450125496e+04 0.01
# compare_return=$?
# if [ $compare_return -eq 2 ]; then
#     echo "Wrong usage of double_compare";
# else
#     if [ $compare_return -ne 0 ]; then
#         echo "the difference is too large"
#     else
#         echo "the difference is OK"
#     fi
# fi

if [ $# -eq 2 ] ; then
    $lp_tst --file $mps_input_file --time_limit 60 $minmax_option > $lp_tst_output
else 
    $lp_tst --file $mps_input_file --time_limit 12000 $minmax_option "--mpq" > $lp_tst_output
fi
status=$?
if [ $status -ne 0 ]; then
    echo "lp_tst failed"
    exit 1
fi

get_status_from_output lp_tst_status $lp_tst_output

if [ $glp_status != $lp_tst_status ]; then
    if [ "$glp_status" = UNDEFINED ] && [ "$lp_tst_status" = UNBOUNDED ]; then
        exit 0
    else
        if [ "$glp_status" = UNDEFINED ] && [ "$lp_tst_status" = INFEASIBLE ]; then
            exit 0
        else 
            echo "glpsol and lp_tst disagree: glpsol status is ""$glp_status"
            echo "but lp_tst status is ""$lp_tst_status"
            exit 1
        fi
    fi
fi

if [ $glp_status != OPTIMAL ]; then
    cout "exiting 0"
    exit 0
fi 


function get_cost_from_lp_tst_out() {
    local  __resultvar=$1
    local cost_str=$(grep cost "${lp_tst_output}"| tail -1)
    local tokens=( $cost_str )
    local  myresult=${tokens[2]}
    eval $__resultvar="'$myresult'" 
}


get_cost_from_lp_tst_out lp_tst_cost

$cost_compare $lp_tst_cost $glp_cost
status=$?
if [ $status -ne 0 ]; then
    echo "the costs differ too much"
    echo "glp cost is ""$glp_cost"", but lp_tst_cost is ""$lp_tst_cost"
    exit 1
fi
exit 0
