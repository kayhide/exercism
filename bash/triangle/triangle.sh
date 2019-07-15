#!/usr/bin/env bash

set -eu

# This solution does not use "bc" command.
# Despite, scale all edges so that their length are integers.

scale_digit() {
    local x
    if [[ $1 =~ (.+)\.(.)(.*) ]]; then
        x="${BASH_REMATCH[1]}${BASH_REMATCH[2]}.${BASH_REMATCH[3]}"
        x="${x#0}"              # Drop leading zero
        x="${x%.}"              # Drop trailing dot
    else
        x="${x}0"               # Multiply by 10
    fi
    echo "$x"
}

to_integer() {
    read -r -a xs <<< "$@"
    local -i n="${#xs}"
    while [[ "${xs[*]}" =~ \. ]]; do # Repeat scaling while any of the values is float.
        for (( i = 0; i < n; ++i )); do
            xs[$i]="$(scale_digit "${xs[$i]}")"
        done
    done
    echo "${xs[*]}"
}

is_triangle() {
    (( $1 > 0 && $2 > 0 && $3 > 0 )) &&
        (( $1 + $2 > $3 && $2 + $3 > $1 && $3 + $1 > $2 ))
}

count_matching_edges() {
    local -i n=0
    (( $1 == $2 && ++n )) || true
    (( $2 == $3 && ++n )) || true
    (( $3 == $1 && ++n )) || true
    echo $n
}

equilateral() {
    (( $(count_matching_edges "$@") == 3 ))
}

isosceles() {
    (( $(count_matching_edges "$@") >= 1 ))
}

scalene() {
    (( $(count_matching_edges "$@") == 0 ))
}

main() {
    read -r -a xs < <(to_integer "${@:2}")
    ( is_triangle "${xs[@]}" && $1 "${xs[@]}" ) && echo true || echo false
}

main "$@"
