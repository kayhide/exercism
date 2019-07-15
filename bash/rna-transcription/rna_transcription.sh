#!/usr/bin/env bash

set -eu

die() {
    echo "$@"
    exit 1
}

main() {
    local rna=""
    while read -r -n1 char; do
        case "${char:-}" in
            "" ) ;;
            G ) rna+=C ;;
            C ) rna+=G ;;
            T ) rna+=A ;;
            A ) rna+=U ;;
            * ) die "Invalid nucleotide detected." ;;
        esac
    done <<< "${1:-}"
    echo "$rna"
}

main "$@"
