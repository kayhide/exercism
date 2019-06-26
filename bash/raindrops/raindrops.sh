#!/usr/bin/env bash

set -eu

is_divisible() {
    (( $1 % $2 == 0 ))
}

main() {
    local drops=""
    is_divisible "$1" 3 && drops+="Pling"
    is_divisible "$1" 5 && drops+="Plang"
    is_divisible "$1" 7 && drops+="Plong"

    echo "${drops:-$1}"
}

main "$@"
