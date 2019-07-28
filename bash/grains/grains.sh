#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    case $1 in
        total )
            printf "%u" $(( -1 ))
            ;;
        * )
            (( $1 < 1 || 64 < $1 )) && die "Error: invalid input"
            printf "%u" $(( 1 << ( $1 - 1 ) ))
            ;;
    esac
    echo
}

main "$@"
