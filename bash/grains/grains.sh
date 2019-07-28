#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    if [[ $1 == total ]]; then
        printf "%u" $(( -1 ))
    elif (( 0 < $1 && $1 <= 64 )); then
        printf "%u" $(( 1 << ( $1 - 1 ) ))
    else
        die "Error: invalid input"
    fi
    echo
}

main "$@"
