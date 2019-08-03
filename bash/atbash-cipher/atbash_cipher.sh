#!/usr/bin/env bash

set -eu

code() {
    local plain="abcdefghijklmnopqrstuvwxyz"
    local cypher="zyxwvutsrqponmlkjihgfedcba"
    declare -A coder
    local -i n=${#plain}
    for (( i = 0; i < n; ++i )); do
        coder[${plain:$i:1}]=${cypher:$i:1}
    done

    local -l src="$1"
    local -i n="${#src}"
    for (( i = 0; i < n; ++i )); do
        print_space $i
        local c="${src:i:1}"
        echo -n "${coder[$c]:-$c}"
    done
    echo
}

encode() {
    print_space() {
        if (( $1 > 0 && $1 % 5 == 0 )); then
            echo -n " "
        fi
    }
    code "${1//[ ,\.]}"
}

decode() {
    print_space() { true; }
    code "${1// }"
}

main() {
    $1 "$2"
}

main "$@"
