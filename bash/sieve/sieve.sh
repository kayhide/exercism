#!/usr/bin/env bash

set -eu

main() {
    local nums=()
    local limit=$1

    for (( i=2; i <= limit; ++i )); do
        nums[$i]=$i
    done

    for (( i=2; i <= limit; ++i )); do
        for (( j=$(( i + i )); j <= limit; j+=i )); do
            unset "nums[$j]"
        done
    done

    IFS=$'\n'
    echo "${nums[*]}"
}

main "$@"
