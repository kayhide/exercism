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

pack() {
    for x in "$@"; do
        echo -n "$x"
    done
    echo
}

roll() {
    if (( $1 < 0 )); then
        echo "Negative roll is invalid"
        exit 1
    elif (( CURRENT[0] + $1 > 10 )); then
        echo "Pin count exceeds pins on the lane"
        exit 1
    elif is_ended; then
        echo "Cannot roll after game is over"
        exit 1
    fi

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
            xs=""
            for x in "${ENDING[@]}"; do
                (( x == 10 )) && xs+="x" || xs+="$x"
            done
            FRAMES+=( "$xs" )
        fi
    fi
}

score() {
    >&3 echo "# ${FRAMES[*]}"

    if ! is_ended; then
        echo "Score cannot be taken until the end of the game"
        exit 1
    fi


    local sum=0
    local doubling=()

    add() {
        local i
        sum=$(( sum + ${1/x/10} * ( 1 + ${#doubling[@]} ) ))
        for (( i = 0; i < ${#doubling[@]}; ++i )); do
            doubling[i]=$(( doubling[i] - 1 ))
        done
        for (( i = 0; i < ${#doubling[@]}; ++i )); do
            (( doubling[i] == 0 )) && unset "doubling[i]"
        done
        doubling=( "${doubling[@]}" )
    }


    for frame in "${FRAMES[@]}"; do
        case $frame in
            "X" )
                add 10
                doubling+=( 2 )
                ;;
            *"/" )
                add "${frame:0:1}"
                add $(( 10 - "${frame:0:1}" ))
                doubling+=( 1 )
                ;;
            * )
                local i
                for (( i = 0; i < ${#frame}; ++i )); do
                    add "${frame:i:1}"
                done
                ;;
        esac
    done
    >&3 echo "#  => $sum"
    echo "$sum"
}

main() {
    for i in "$@"; do
        roll "$i" || exit 1
    done
    score || exit 1
}

# Uncomment this to show debug outputs which are redirected to &3.
# main "$@"

main "$@" 3> /dev/null
