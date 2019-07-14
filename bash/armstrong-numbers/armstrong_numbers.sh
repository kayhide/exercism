#!/usr/bin/env bash

set -eu

main() {
    local sum=0
    local n=${#1}
    for (( i = 0; i < n; ++i )); do
        sum=$(( sum + ${1:$i:1} ** n ))
    done
    (( $1 == sum )) && echo true || echo false
}

main "$@"
