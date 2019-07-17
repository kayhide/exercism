#!/usr/bin/env bash

set -eu

to_i() {
    echo $(( $(printf "%d" "'$1") - 97 ))
}

main() {
    local -i bits=0

    while read -r -n1 char; do
        if [[ $char == [[:alpha:]] ]]; then
            (( bits |= 1 << $(to_i "${char,,}") )) || true
        fi
    done <<< "$1"

    local -i full=$(( (1 << 26) - 1 ))
    (( bits == full )) && echo true || echo false
}

main "$@"
