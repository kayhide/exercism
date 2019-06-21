#!/usr/bin/env bash

set -eu

is_divisible() {
    if (( $1 % $2 == 0 )); then
        echo true
    else
        echo false
    fi
}

main() {
    local drops=""
    if $(is_divisible $1 3); then
        drops="Pling"
    fi
    if $(is_divisible $1 5); then
        drops+="Plang"
    fi
    if $(is_divisible $1 7); then
        drops+="Plong"
    fi

    echo "${drops:-$1}"
}

main "$@"
