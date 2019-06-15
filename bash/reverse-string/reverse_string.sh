#!/usr/bin/env bash

set -eu

main() {
    if [[ -n "$1" ]]; then
        main "${1:1}"
    fi
    printf "${1:0:1}"
}

main "$@"
