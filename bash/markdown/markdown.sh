#!/usr/bin/env bash

strong() {
    read -r line
    while [[ $line =~ ^(.*)__(.+)__(.*) ]]; do
        line="${BASH_REMATCH[1]}<strong>${BASH_REMATCH[2]}</strong>${BASH_REMATCH[3]}"
    done
    echo "$line"
}

em() {
    read -r line
    while [[ $line =~ ^(.*)_(.+)_(.*) ]]; do
        line="${BASH_REMATCH[1]}<em>${BASH_REMATCH[2]}</em>${BASH_REMATCH[3]}"
    done
    echo "$line"
}

main() {
    local html=""
    local list_stack=()         # list_stack holds open ul tags.

    # If list_stack is empty, inserts ul open tag and push it to the list_stack.
    list_push() {
        if [[ ${list_stack[0]} != "$1" ]]; then
            html+="<$1>"
            list_stack+=( "$1" "${list_stack[*]}" )
        fi
    }

    # If list_stack is not empty, inserts ul close tag and pops it from the list_stack.
    list_pop() {
        local top="${list_stack[0]}"
        if [[ -n "$top" ]]; then
            html+="</$top>"
            list_stack=( "${list_stack[@]:2}" )
        fi
    }

    while read -r line; do
        if [[ $line =~ ^(\*|\#+)\ +(.*) ]]; then
            pre="${BASH_REMATCH[1]}"
            line="${BASH_REMATCH[2]}"
            case "$pre" in
                "*" )
                    list_push ul
                    tag="li"
                    ;;
                "#"* )
                    list_pop
                    tag="h${#pre}"
                    ;;
            esac
        else
            list_pop
            tag="p"
        fi
        html+="<$tag>$(echo "$line" | strong | em)</$tag>"
    done < "$1"

    list_pop
    echo "$html"
}

main "$@"
