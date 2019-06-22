#!/usr/bin/env bash

set -eu

push() {
    echo "$1$2"
}

pop_or_push() {
    if [[ "${3:0:1}" == "$1" ]]; then
        echo "${3:1}"
    else
        echo "$2$3"
    fi
}

main() {
    local stack=""

    for i in $(seq 0 $(( ${#1} - 1 )) ); do
        local c="${1:i:1}"
        >&2 echo -n "$c : $stack"
        case "$c" in
            "[" ) stack=$(push "[" "$stack") ;;
            "]" ) stack=$(pop_or_push "[" "]" "$stack") ;;
            "(" ) stack=$(push "(" "$stack") ;;
            ")" ) stack=$(pop_or_push "(" ")" "$stack") ;;
            "{" ) stack=$(push "{" "$stack") ;;
            "}" ) stack=$(pop_or_push "{" "}" "$stack") ;;
        esac
        >&2 echo " => $stack"
    done

    if [[ -z "$stack" ]]; then
        echo true
    else
        echo false
    fi
}

main "$@" 2> /dev/null

# Enable debug prints which are echoed into stderr.
# main "$@"
