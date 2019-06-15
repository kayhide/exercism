#!/usr/bin/env bash

set -eu

main() {
    if [[ -z ${1+x} || -n ${2+x} ]]; then
        echo "Usage: ./error_handling <greetee>"
        exit 1
    fi
    echo "Hello, $1"
}

main "$@"
