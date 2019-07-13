#!/usr/bin/env bash

set -eu

main() {
    local n=$1
    shift
    read -r -a xs <<< "$@"
    local lo=0
    local hi=${#xs[@]}
    while (( lo + 1 < hi )); do
        local i=$(( (hi - lo) / 2 + lo ))
        (( ${xs[$i]} == n )) && lo=$i && break
        (( ${xs[$i]} < n )) && lo=$i || hi=$i
    done
    (( ${xs[$lo]} == n )) && echo $lo || echo -1
}

main "$@"
