#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

is_invalid() {
    [[ ${#1} != 10 || $1 == [01]* || ${1:3} == [01]* ]]
}

main() {
    local num=${1//[^0-9]/}
    [[ ${#num} == 11 && $num == 1* ]] && num=${num:1}

    is_invalid "$num" && die "Invalid number.  [1]NXX-NXX-XXXX N=2-9, X=0-9"

    echo "$num"
}

main "$@"
