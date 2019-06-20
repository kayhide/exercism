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
    if (( $# != 1 )) || [[ ! $1 =~ ^[0-9]+$ ]]; then
        echo 'Usage: leap.sh <year>'
        exit 1
    fi

    if $(is_divisible $1 400) ||
            ( ! $(is_divisible $1 100 ) && $(is_divisible $1 4) ); then
        echo true
    else
        echo false
    fi
}

main "$@"
