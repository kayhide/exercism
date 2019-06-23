#!/usr/bin/env bash

set -eu

main() {
    local head="${1:-}"
    while (( $# > 1 )); do
        echo "For want of a $1 the $2 was lost."
        shift
    done

    if [[ -n "$head" ]]; then
        echo "And all for the want of a $head."
    fi
}

main "$@"
