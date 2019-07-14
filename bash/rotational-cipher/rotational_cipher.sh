#!/usr/bin/env bash

set -eu

ord() {
    echo $(( $(printf "%d" "'$1") ))
}

chr() {
    printf "%b" "$(printf "\\%03o" "$1")"
}


main() {
    local n=${#1}
    local mod=$2

    rot_with() {
        local base=$1
        local src=$(( $(ord "$2") - base ))
        local dst=$(( (src + mod) % 26 ))
        chr $(( dst + base ))
    }

    rot() {
        if [[ $1 =~ [a-z] ]]; then
            rot_with "$(ord a)" "$1"
        elif [[ $1 =~ [A-Z] ]]; then
            rot_with "$(ord A)" "$1"
        else
            echo "$1"
        fi
    }

    for (( i = 0; i < n; ++i )); do
        echo -n "$(rot "${1:i:1}")"
    done
}

main "$@"
