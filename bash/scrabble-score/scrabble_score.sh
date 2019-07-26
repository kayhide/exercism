#!/usr/bin/env bash

set -eu

main() {
    local str="$1"
    str=${str,,}
    str=${str//[^[:alpha:]]}
    str=${str//[aeioulnrst]/_}  # 1
    str=${str//[dg]/__}         # 2
    str=${str//[bcmp]/___}      # 3
    str=${str//[fhvwy]/____}    # 4
    str=${str//[k]/_____}       # 5
    str=${str//[jx]/________}   # 8
    str=${str//[qz]/__________} # 10
    echo ${#str}
}

main "$@"
