#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    local num=${1//[^0-9]/}
    num=${num#1}

    [[ ! $num =~ ^[2-9][0-9]{2}[2-9][0-9]{6}$ ]] &&
        die "Invalid number.  [1]NXX-NXX-XXXX N=2-9, X=0-9"

    echo "$num"
}

main "$@"
