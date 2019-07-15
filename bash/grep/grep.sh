#!/usr/bin/env bash

set -eu

grep_file() {
    local pattern="$1"
    local file="$2"

    if $MATCH_ENTIRE_LINE; then
        test_() { [[ "$1" == "$pattern" ]]; }
    else
        test_() { [[ "$1" == *"$pattern"* ]]; }
    fi

    if $IGNORE_CASE; then
        pattern=${pattern,,}
        test__() { test_ "${@,,}"; }
    else
        test__() { test_ "$@"; }
    fi

    if $INVERT_MATCH; then
        test___() { ! test__ "$@"; }
    else
        test___() { test__ "$@"; }
    fi


    local i=0
    while read -r line; do
        i=$(( i + 1 ))
        if test___ "$line"; then
            if $SHOW_ONLY_FILENAME; then
                echo "$file"
                break
            else
                $SHOW_FILENAME && echo -n "$file:"
                $SHOW_LINE_NUMBER && echo -n "$i:"
                echo "$line"
            fi
        fi
    done < "$file"
}

main() {
    SHOW_LINE_NUMBER=false
    IGNORE_CASE=false
    SHOW_ONLY_FILENAME=false
    MATCH_ENTIRE_LINE=false
    INVERT_MATCH=false
    while [[ "$1" == "-"* ]]; do
        case "$1" in
            -n ) SHOW_LINE_NUMBER=true ;;
            -i ) IGNORE_CASE=true ;;
            -l ) SHOW_ONLY_FILENAME=true ;;
            -x ) MATCH_ENTIRE_LINE=true ;;
            -v ) INVERT_MATCH=true ;;
            * )
                echo "Unknown flag: $1"
                exit 1
                ;;
        esac
        shift
    done

    local pattern="$1"
    shift

    if (( $# > 1 )); then
        SHOW_FILENAME=true
    else
        SHOW_FILENAME=false
    fi

    for file in "$@"; do
        grep_file "$pattern" "$file"
    done
}

main "$@"
