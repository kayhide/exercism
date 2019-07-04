#!/usr/bin/env bash

set -eu

reverse_echo() {
    local res=()
    for x in "$@"; do
        res=("$x" "${res[@]}")
    done
    echo "${res[*]}"
}

main() {
    local actions=("wink" "double blink" "close your eyes" "jump")
    local n=${#actions[@]}

    local val=$1
    for (( i=0; i < n; ++i )); do
        (( val % 2 )) || unset -v "actions[$i]"
        val=$(( val / 2 ))
    done

    IFS=","
    if (( val % 2 )); then
        reverse_echo "${actions[@]}"
    else
        echo "${actions[*]}"
    fi
}

main "$@"
