#!/usr/bin/env bash

set -eu

main() {
    local num=$1
    is_divisible_by() {
        (( num % $1 == 0 ))
    }

    local drops=""
    if is_divisible_by 3; then
        drops+="Pling"
    fi
    if is_divisible_by 5; then
        drops+="Plang"
    fi
    if is_divisible_by 7; then
        drops+="Plong"
    fi

    echo "${drops:-$1}"
}

main "$@"
