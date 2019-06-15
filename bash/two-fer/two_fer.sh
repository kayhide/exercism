#!/usr/bin/env bash

set -eu

main() {
    echo "One for ${1:-you}, one for me."
}

main "$@"
