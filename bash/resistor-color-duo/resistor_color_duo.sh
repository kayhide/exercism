#!/usr/bin/env bash

set -eu

to_int() {
    case "$1" in
        black  ) echo -n 0 ;;
        brown  ) echo -n 1 ;;
        red    ) echo -n 2 ;;
        orange ) echo -n 3 ;;
        yellow ) echo -n 4 ;;
        green  ) echo -n 5 ;;
        blue   ) echo -n 6 ;;
        violet ) echo -n 7 ;;
        grey   ) echo -n 8 ;;
        white  ) echo -n 9 ;;
    esac
}

main() {
    local num=""
    for c in "$@"; do
        num+=$(to_int $c)
    done
    echo ${num:-invalid color}
}

main "$@"
