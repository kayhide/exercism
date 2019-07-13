#!/usr/bin/env bash

set -eu

main() {
    local n=$1
    read -r -a xs <<< "${@:2}"

    local lo=0
    local hi=${#xs[@]}
    while (( ${xs[$lo]} != n )) && (( lo + 1 < hi )); do
        local i=$(( (lo + hi) / 2 ))
        (( n < ${xs[$i]} )) && hi=$i || lo=$i
    done
    (( ${xs[$lo]} == n )) && echo $lo || echo -1
}

main "$@"
