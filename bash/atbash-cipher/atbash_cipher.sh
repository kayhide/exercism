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
        is_spacing $i && echo -n " "
        local c="${src:i:1}"
        echo -n "${coder[$c]:-$c}"
    done
    echo
}

encode() {
    is_spacing() { (( $1 > 0 && $1 % 5 == 0 )); }
    code "${1//[ ,\.]}"
}

decode() {
    is_spacing() { false; }
    code "${1// }"
}

main() {
    $1 "$2"
}

main "$@"
