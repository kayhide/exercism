#!/usr/bin/env bash

set -eu

main() {
    declare -A words

    local str="$1"
    str="${str//\\n/ }"
    str="${str//[^0-9a-zA-Z\']/ }"
    str="${str,,}"
    read -r -a xs <<< "$str"
    for w in "${xs[@]}"; do
        [[ $w == \'*\' ]] && w=${w:1:-1}
        words[$w]=$(( ${words[$w]:-0} + 1 ))
    done

    for w in "${!words[@]}"; do
        echo "$w: ${words[$w]}"
    done
}

main "$@"
