#!/usr/bin/env bash

set -eu

die() {
    echo false
    exit
}

main() {
    local xs="${1// }"

    (( "${#xs}" < 2 )) && die
    [[ $xs == *[^[:digit:]]* ]] && die

    local n=${#xs}
    local -i sum=0
    for (( i = 0; i < n; ++i )); do
        local -i x="${xs:$(( n - i - 1 )):1}"
        if (( i % 2 )); then
            sum+=$(( (x * 2) / 10 + (x * 2) % 10 ))
        else
            sum+=$x
        fi
    done
    (( sum % 10 )) && echo false || echo true
}

main "$@"
