#!/usr/bin/env bash

set -eu

main() {
    local -i sum=0
    local -i n=${#1}
    for (( i = 0; i < n; ++i )); do
        (( sum += ${1:$i:1} ** n )) || true
    done
    (( $1 == sum )) && echo true || echo false
}

main "$@"
