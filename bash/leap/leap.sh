#!/usr/bin/env bash

set -eu

main() {
    if (( $# != 1 )) || [[ ! $1 =~ ^[0-9]+$ ]]; then
        echo 'Usage: leap.sh <year>'
        exit 1
    fi


    local num=$1
    is_divisible_by() {
        (( num % $1 == 0 ))
    }

    if is_divisible_by 400 ||
            ( ! is_divisible_by 100 && is_divisible_by 4 ); then
        echo true
    else
        echo false
    fi
}

main "$@"
