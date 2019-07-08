#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    [[ -z "${1+x}" || -z "${2+x}" ]] &&
        die 'Usage: hamming.sh <string1> <string2>'

    local x="$1"
    local y="$2"

    local n=0
    while [[ -n "$x" && -n "$y" ]]; do
        [[ "${x:0:1}" != "${y:0:1}" ]] && n=$(( n + 1 ))
        x="${x:1}"
        y="${y:1}"
    done

    [[ -n "$x" || -n "$y" ]] &&
        die 'left and right strands must be of equal length'

    echo $n
}

main "$@"
