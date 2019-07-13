#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    echo "Hello, World!"
}

main "$@"
