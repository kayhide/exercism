#!/usr/bin/env bash

set -eu

main() {
    local actions=("wink" "double blink" "close your eyes" "jump")
    local n=${#actions[@]}

    local val=$1
    local res=()

    if (( 1 << n & val )); then
        push() {
            res=("${actions[$1]}" "${res[@]}")
        }
    else
        push() {
            res+=("${actions[$1]}")
        }
    fi

    for (( i=0; i < n; ++i )); do
        (( 1 << i & val )) && push $i
    done

    IFS=","
    echo "${res[*]}"
}

main "$@"
