#!/usr/bin/env bash

set -eu

main() {
    local nucleotides=(A C G T)
    declare -A counts
    for x in "${nucleotides[@]}"; do
        counts[$x]=0
    done

    local strand="$1"
    while [[ -n "$strand" ]]; do
        local x=${strand:0:1}
        [[ -z ${counts[$x]+x} ]] && break
        counts[$x]=$(( 1 + counts[$x] ))
        strand="${strand:1}"
    done

    if [[ -n "$strand" ]]; then
        echo "Invalid nucleotide in strand"
        exit 1
    fi

    for x in "${nucleotides[@]}"; do
        echo "$x: ${counts[$x]}"
    done
}

main "$@"
