#!/usr/bin/env bash

set -eu

main() {
    local res=""
    local IFS=" -_"
    read -r -a words <<< "$@"
    for word in "${words[@]}"; do
        res+=${word:0:1}
    done
    echo "${res^^}"
}

main "$@"
