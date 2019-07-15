#!/usr/bin/env bash

set -eu

# Depending on the starting bucket, determine one of the two patterns of moves.
# Here, I call the one "rightwise" and the other "leftwise".
# When the pattern is "rightwise", it always transfers the content from the
# bucket 1 to the 2, and never happens the other way.
# After transferring, the next move should be one of refilling the emptied source
# or draining the filled destination.
#
# If there is no solution, it will end up with the both buckets saturated.
#
# I also call the source bucket "primary" and the destination "secondary".

die() {
    echo "$*"
    exit 1
}

min() { (( $1 < $2 )) && echo "$1" || echo "$2"; }

# Defines rightwise moves where the primary bucket is the bucket 1.
define_rightwise_moves() {
    PRIMARY_TEXT=one
    PRIMARY_CAPACITY="$BUCKET_ONE"
    SECONDARY_TEXT=two
    SECONDARY_CAPACITY="$BUCKET_TWO"

    transfer() {
        local -i x
        x=$(min "$1" $(( BUCKET_TWO - $2 )) )
        echo $(( $1 - x )) $(( $2 + x ))
    }
    fill() { echo "$BUCKET_ONE" "$2"; }
    drain() { echo "$1" 0; }

    is_primary_empty() { (( $1 == 0 )) ; }
    is_primary_full() { (( $1 == BUCKET_ONE )) ; }
    is_secondary_empty() { (( $2 == 0 )) ; }
    is_secondary_full() { (( $2 == BUCKET_TWO )) ; }
}

# Defines leftwise moves where the primary bucket is the bucket 2.
define_leftwise_moves() {
    PRIMARY_TEXT=two
    PRIMARY_CAPACITY="$BUCKET_TWO"
    SECONDARY_TEXT=one
    SECONDARY_CAPACITY="$BUCKET_ONE"

    transfer() {
        local -i x
        x=$(min "$2" $(( BUCKET_ONE - $1 )) )
        echo $(( $1 + x )) $(( $2 - x ))
    }
    fill() { echo "$1" "$BUCKET_TWO"; }
    drain() { echo 0 "$2"; }

    is_primary_empty() { (( $2 == 0 )) ; }
    is_primary_full() { (( $2 == BUCKET_TWO )) ; }
    is_secondary_empty() { (( $1 == 0 )) ; }
    is_secondary_full() { (( $1 == BUCKET_ONE )) ; }
}

# Executs one move.
# Depends on defined moves.
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

is_primary_goalable() { (( GOAL == PRIMARY_CAPACITY )) ; }
is_secondary_goalable() { (( GOAL == SECONDARY_CAPACITY )) ; }

is_goaled() { (( $1 == GOAL )) || (( $2 == GOAL )); }
is_saturated() { (( $1 == BUCKET_ONE )) && (( $2 == BUCKET_TWO )); }


main() {
    BUCKET_ONE="$1"
    BUCKET_TWO="$2"
    GOAL="$3"

    (( $3 > $1 && $3 > $2 )) && die "invalid goal"

    case "$4" in
        one ) define_rightwise_moves ;;
        two ) define_leftwise_moves ;;
        * ) die "Invalid starting bucket: $4"
    esac

    if is_primary_goalable; then
        echo "moves: 1, goalBucket: $PRIMARY_TEXT, otherBucket: 0"
        exit
    fi
    if is_secondary_goalable; then
        echo "moves: 2, goalBucket: $SECONDARY_TEXT, otherBucket: $PRIMARY_CAPACITY"
        exit
    fi

    local -a state=(0 0)
    local -i i=0
    while ! is_goaled "${state[@]}" && ! is_saturated "${state[@]}"; do
        read -r -a state < <(step "${state[@]}")
        (( ++i ))
        >&3 echo " $i: ${state[*]} / $BUCKET_ONE $BUCKET_TWO"
    done

    if (( "${state[0]}" == GOAL )); then
        echo "moves: $i, goalBucket: one, otherBucket: ${state[1]}"
    elif (( "${state[1]}" == GOAL )); then
        echo "moves: $i, goalBucket: two, otherBucket: ${state[0]}"
    else
        die "invalid goal"
    fi
}

main "$@" 3> /dev/null
# main "$@"
