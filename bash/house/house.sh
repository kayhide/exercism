#!/usr/bin/env bash

set -eu

mapfile -t ITEMS <<EOF
the house that Jack built.
the malt
the rat
the cat
the dog
the cow with the crumpled horn
the maiden all forlorn
the man all tattered and torn
the priest all shaven and shorn
the rooster that crowed in the morn
the farmer sowing his corn
the horse and the hound and the horn
EOF

mapfile -t ACTIONS <<EOF
lay in
ate
killed
worried
tossed
milked
kissed
married
woke
kept
belonged to
EOF


verse() {
    head $(( $1 - 1 ))
    tail $(( $1 - 2 ))
}

head() {
    echo "This is ${ITEMS[$1]}"
}

tail() {
    if (( $1 >= 0 )); then
        echo "that ${ACTIONS[$1]} ${ITEMS[$1]}"
        tail $(( $1 - 1 ))
    fi
}

die() {
    echo "$@"
    eixt 1
}

main() {
    ! (( 1 <= $1 )) && die "invalid"
    ! (( $1 <= $2 )) && die "invalid"
    ! (( $2 <= 12 )) && die "invalid"

    for (( i = $1; i <= $2; ++i )); do
        verse $i
        echo
    done
}

main "$@"
