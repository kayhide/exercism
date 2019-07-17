#!/usr/bin/env bash

set -eu

# I define the starting bucket as a "primary" and the other "secondary".
# It always transfers the content from the primary backet to the secondary one,
# and the other way never happens.
# After transferring, the next move should be one of refilling the emptied
# primary or draining the filled secondary.
#
# If there is no solution, it will end up with the both buckets saturated.

die() {
    echo "$*"
    exit 1
}

min() { (( $1 < $2 )) && echo "$1" || echo "$2"; }

# Executes one move.
# step :: ( primary_content : int, secondary_content : int) -> ( primary_content : int, secondary_content : int)
step() {
    if is_primary_empty "$@"; then
        fill "$@"
    elif is_primary_full "$@"; then
        transfer "$@"
    elif is_secondary_full "$@"; then
        drain "$@"
    elif is_secondary_empty "$@"; then
        transfer "$@"
    fi
}

transfer() {
    local -i x
    x=$(min "$1" $(( SECONDARY_CAPACITY - $2 )) )
    echo $(( $1 - x )) $(( $2 + x ))
}
fill() { echo "$PRIMARY_CAPACITY" "$2"; }
drain() { echo "$1" 0; }

is_primary_empty() { (( $1 == 0 )) ; }
is_primary_full() { (( $1 == PRIMARY_CAPACITY )) ; }
is_secondary_empty() { (( $2 == 0 )) ; }
is_secondary_full() { (( $2 == SECONDARY_CAPACITY )) ; }

is_goaled() { (( $1 == GOAL )) || (( $2 == GOAL )); }
is_saturated() { (( $1 == PRIMARY_CAPACITY )) && (( $2 == SECONDARY_CAPACITY )); }


main() {
    (( $3 > $1 && $3 > $2 )) && die "invalid goal"

    GOAL="$3"
    case "$4" in
        one )
            PRIMARY_TEXT=one
            PRIMARY_CAPACITY="$1"
            SECONDARY_TEXT=two
            SECONDARY_CAPACITY="$2"
            ;;
        two )
            PRIMARY_TEXT=two
            PRIMARY_CAPACITY="$2"
            SECONDARY_TEXT=one
            SECONDARY_CAPACITY="$1"
            ;;
        * )
            die "Invalid starting bucket: $4"
            ;;
    esac


    case $GOAL in
        $PRIMARY_CAPACITY )
            echo "moves: 1, goalBucket: $PRIMARY_TEXT, otherBucket: 0"
            exit
            ;;
        $SECONDARY_CAPACITY )
            echo "moves: 2, goalBucket: $SECONDARY_TEXT, otherBucket: $PRIMARY_CAPACITY"
            exit
            ;;
    esac

    local -a state=(0 0)
    local -i i=0
    while ! is_goaled "${state[@]}" && ! is_saturated "${state[@]}"; do
        read -r -a state < <(step "${state[@]}")
        (( ++i ))
        >&3 echo " $i: ${state[*]} / $PRIMARY_CAPACITY $SECONDARY_CAPACITY"
    done

    case $GOAL in
        ${state[0]} )
            echo "moves: $i, goalBucket: $PRIMARY_TEXT, otherBucket: ${state[1]}"
            ;;
        ${state[1]} )
            echo "moves: $i, goalBucket: $SECONDARY_TEXT, otherBucket: ${state[0]}"
            ;;
        * )
            die "invalid goal"
            ;;
    esac
}

main "$@" 3> /dev/null
# main "$@"
