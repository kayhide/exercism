#!/usr/bin/env bash

set -eu

main() {
    local -i bits=0
    while read -r -n1 char; do
        if [[ $char == [[:lower:]] ]]; then
            (( bits = bits & 7 | 1 ))
        elif [[ $char == [[:upper:]] ]]; then
            (( bits = bits & 7 | 2 ))
        elif [[ $char == [[:digit:]] ]]; then
            (( bits = bits & 7 | 4 ))
        elif [[ $char == \? ]]; then
            (( bits |= 8 ))
        fi
    done <<< "${1:-}"

    local res=""
    res+=$(( bits >> 0 & 1 ))
    res+=$(( bits >> 1 & 1 ))
    res+=$(( bits >> 2 & 1 ))
    res+=$(( bits >> 3 & 1 ))
    case $res in
        01*1 ) echo "Calm down, I know what I'm doing!" ;;
        01** ) echo "Whoa, chill out!" ;;
        ***1 ) echo "Sure." ;;
        0000 ) echo "Fine. Be that way!" ;;
        *    ) echo "Whatever." ;;
    esac
}

main "$@"
