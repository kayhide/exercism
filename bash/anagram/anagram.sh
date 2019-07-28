#!/usr/bin/env bash

set -eu

is_anagram() {
    (( ${#1} == ${#2} )) || return
    [[ "$1" != "$2" ]] || return

    local -i n=${#1}
    for (( i = 0; i < n; ++i )); do
        local c=${1:$i:1}
        [[ "${1//[^$c]}" == "${2//[^$c]}" ]] || return
    done
}


main() {
    local -l ref="$1"
    read -r -a xs <<< "$2"
    local -a res=()
    for x in "${xs[@]}"; do
        is_anagram "$ref" "${x,,}" && res+=( "$x" )
    done
    echo "${res[@]}"
}

main "$@"

