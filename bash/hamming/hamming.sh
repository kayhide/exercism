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

    local nx="${#x}"
    local ny="${#y}"
    (( nx != ny )) &&
        die 'left and right strands must be of equal length'

    local n=0
    for (( i = 0; i < nx; ++i )); do
        [[ "${x:$i:1}" != "${y:$i:1}" ]] && n=$(( n + 1 ))
    done

    echo $n
}

main "$@"
