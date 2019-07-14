#!/usr/bin/env bash

set -eu

square_of_sum() {
    local sum=0
    for (( i = 1; i <= $1 ; ++i )); do
        (( sum += i  ))
    done
    echo $(( sum ** 2 ))
}

sum_of_squares() {
    local sum=0
    for (( i = 1; i <= $1 ; ++i )); do
        (( sum += i ** 2 ))
    done
    echo $sum
}

difference() {
    local x=0
    local y=0
    for (( i = 1; i <= $1 ; ++i )); do
        (( x += i ))
        (( y += i ** 2 ))
    done
    echo $(( x ** 2 - y ))
}

main() {
    $1 "$2"
}

main "$@"
