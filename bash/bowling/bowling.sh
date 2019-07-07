#!/usr/bin/env bash

set -eu

FRAMES=()
CURRENT=()
ENDING=()

is_ended() {
    (( ${#ENDING[@]} == 3 )) ||
        ( (( ${#ENDING[@]} == 2 )) && (( ENDING[0] + ENDING[1] < 10 )) )
}

is_striking() {
    (( ${#CURRENT[@]} == 1 )) && (( CURRENT[0] == 10 ))
}

is_sparing() {
    (( ${#CURRENT[@]} == 2 )) && (( CURRENT[0] + CURRENT[1] == 10 ))
}

die() {
    echo "$@" >&2
    exit 1
}

pack() {
    for x in "$@"; do
        (( x == 10 )) && echo -n x || echo -n "$x"
    done
    echo
}

unpack() {
    for (( i = 0; i < ${#1}; ++i )); do
        [[ "${1:i:1}" == "x" ]] && echo 10 || echo "${1:i:1}"
    done
}


roll() {
    (( $1 < 0 )) && die "Negative roll is invalid"
    (( CURRENT[0] + $1 > 10 )) && die "Pin count exceeds pins on the lane"
    is_ended && die "Cannot roll after game is over"

    CURRENT+=( "$1" )
    if (( ${#FRAMES[@]} < 9 )); then
        if is_striking; then
            FRAMES+=( "X" )
            CURRENT=()
        elif is_sparing; then
            FRAMES+=( "${CURRENT[0]}/" )
            CURRENT=()
        elif (( ${#CURRENT[@]} == 2 )); then
            FRAMES+=( "$(pack "${CURRENT[@]}")" )
            CURRENT=()
        fi
    else
        ENDING+=( "$1" )
        if is_striking || is_sparing; then
            CURRENT=()
        fi
        if is_ended; then
            FRAMES+=( "$(pack "${ENDING[@]}")" )
        fi
    fi
}

score() {
    ! is_ended && die "Score cannot be taken until the end of the game"

    >&3 echo "# ${FRAMES[*]}"

    local sum=0
    local doubling=1            # Consumes lowest 2 bits for every adding.

    add() {
        sum=$(( sum + $1 * ( doubling & 3 ) ))
        doubling=$(( (doubling >> 2) + 1 ))
    }


    for frame in "${FRAMES[@]}"; do
        case $frame in
            "X" )
                add 10
                doubling=$(( doubling + 5 )) # +1 for the current, +(1 << 2) for the next.
                ;;
            *"/" )
                add "${frame:0:1}"
                add $(( 10 - "${frame:0:1}" ))
                doubling=$(( doubling + 1 ))
                ;;
            * )
                for n in $(unpack "$frame"); do
                    add "$n"
                done
                ;;
        esac
    done
    >&3 echo "#  => $sum"
    echo "$sum"
}

main() {
    for i in "$@"; do
        roll "$i"
    done
    score
}

# Uncomment this to show debug outputs which are redirected to &3.
# main "$@"

main "$@" 3> /dev/null
