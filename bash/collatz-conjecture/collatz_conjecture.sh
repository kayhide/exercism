#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

run() {
    local -i step=$1
    local -i x=$2
    echo "$step" "$x"

    if (( x > 1 )); then
        if (( x % 2 == 0 )); then
            run $(( step + 1 )) $(( x / 2 ))
        else
            run $(( step + 1 )) $(( x * 3 + 1 ))
        fi
    fi
}

main () {
    (( $1 <= 0 )) && die "Error: Only positive numbers are allowed"
    run 0 "$1" | tail -n 1 | cut -d " " -f 1
}

main "$@"
