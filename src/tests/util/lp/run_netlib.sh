#!/bin/bash
failures=0
successes=0
inconclusive=0
total=0
if [ $# -eq 1 ]; then
    mpq_option=$1
    if [ $mpq_option != "--mpq" ]; then
        echo "Usage: run_netlib.sh [--mpq]"
        exit 1
    fi
else
    mpq_option="none"
    if [ $# -ne 0 ] ; then
       echo "Too many arguments. Usage: run_netlib.sh [--mpq]"
       exit 1
    fi
fi

date

function analyze_run_result() {
    status=$?
    if [ $status -ne 0 ]; then
        if [ $status -ne 2 ]; then
            let "failures +=  1"
            echo "Failure"
        else
            echo "Inconclusive"
            let "inconclusive += 1"
        fi
    else
        let "successes += 1"
        echo "Success"
    fi
}

for f in test_files/netlib/*.SIF ; do
    let "total += 2"
    echo "processing "$f" for minimum"
    ./compare_with_glpk.sh --min $f
    analyze_run_result

    echo "processing "$f" for maximum"
    ./compare_with_glpk.sh --max $f
    analyze_run_result

    if [ $mpq_option == "--mpq" ]; then
        let "total += 1"
        echo "processing "$f" for rationals for minimum"
        ./compare_with_glpk.sh --min --mpq $f
        analyze_run_result
    fi
done

echo "Total runs="$total", failures="$failures", successes="$successes", inconclusive="$inconclusive
date
