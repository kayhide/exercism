#!/usr/bin/env bash

set -eu

main() {
    if [[ -z "${1+x}" || -z "${1+x}" ]]; then
        echo 'Usage: hamming.sh <string1> <string2>'
        exit 1
    fi

    local x="$1"
    local y="$2"

    local n=0
    while [[ -n "$x" && -n "$y" ]]; do
        [[ "${x:0:1}" != "${y:0:1}" ]] && n=$(( n + 1 ))
        x="${x:1}"
        y="${y:1}"
    done

    if [[ -n "$x" || -n "$y" ]]; then
        echo 'left and right strands must be of equal length'
        exit 1
    fi
    echo $n
}

main "$@"
