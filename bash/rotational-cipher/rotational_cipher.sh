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

    rot() {
        if [[ $1 =~ [A-Z] ]]; then
            local base=65
        elif [[ $1 =~ [a-z] ]]; then
            local base=97
        fi

        if [[ -z ${base+z} ]]; then
            echo "$1"
        else
            local src=$(( $(ord "$1") - base ))
            local dst=$(( (src + mod) % 26 ))
            chr $(( dst + base ))
        fi
    }

    for (( i = 0; i < n; ++i )); do
        echo -n "$(rot "${1:i:1}")"
    done
}

main "$@"
