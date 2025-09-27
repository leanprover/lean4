#!/usr/bin/env bash
source ../../../common.sh

find_parent_with_file() {
    local dir="$1"
    local target_file="$2"

    while [[ "$dir" != "/" ]]; do
        if [[ -e "$dir/$target_file" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done

    if [[ -e "/$target_file" ]]; then
        echo "/"
        return 0
    fi

    return 1
}

run_path="$(pwd)/run.lean"

cd "$(find_parent_with_file "$f" "lean-toolchain")"

lake build

# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

# these tests don't have to succeed
exec_capture lean -Dlinter.all=false --run $run_path -p "$f" || true
diff_produced
