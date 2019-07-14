#!/usr/bin/env bash

set -eu

fold() {
    local acc="$2"
    local x
    for x in "${@:3}"; do
        acc=$($1 "$acc" "$x")
    done
    echo "$acc"
}

square_of_sum() {
    fn() {
        echo $(( $1 + $2 ))
    }
    echo $(( $(fold fn 0 $(seq 1 "$1")) ** 2 ))
}

sum_of_squares() {
    fn() {
        echo $(( $1 + $2 ** 2 ))
    }
    fold fn 0 $(seq 1 "$1")
}

difference() {
    fn() {
        read -r -a acc <<<"$1"
        echo $(( acc[0] + $2 )) $(( acc[1] + $2 ** 2 ))
    }
    read -r -a acc < <(fold fn "0 0" $(seq 1 "$1"))
    echo $(( acc[0] ** 2 - acc[1] ))
}

main() {
    $1 "$2"
}

main "$@"
