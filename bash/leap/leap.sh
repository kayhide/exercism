#!/usr/bin/env bash

set -eu

main() {
    if (( $# != 1 )); then
        echo 'Usage: leap.sh <year>'
        exit 1
    elif [[ ! $1 =~ ^[0-9]+$ ]]; then
        echo 'Usage: leap.sh <year>'
        exit 1
    fi

    if (( $1 % 4 == 0 )); then
        if (( $1 % 100 == 0 )); then
            if (( $1 % 400 == 0 )); then
                echo true
            else
                echo false
            fi
        else
            echo true
        fi
    else
        echo false
    fi
}

main "$@"
