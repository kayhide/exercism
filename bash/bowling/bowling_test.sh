#!/usr/bin/env bash

# The canonical cases call for the implementation of
# _methods_ `score` and `roll`. That's not feasible for a
# shell script. We'll just pass in all the individual rolls
# and expect the score (or error) as output.


@test "should be able to score a game with all zeros" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 0 ]]
}

@test "should be able to score a game with no strikes or spares" {
    run bash bowling.sh 3 6 3 6 3 6 3 6 3 6 3 6 3 6 3 6 3 6 3 6
    [[ $status -eq 0 ]]
    [[ $output == 90 ]]
}

@test "a spare followed by zeros is worth ten points" {
    run bash bowling.sh 6 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 10 ]]
}

@test "points scored in the roll after a spare are counted twice" {
    run bash bowling.sh 6 4 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 16 ]]
}

@test "consecutive spares each get a one roll bonus" {
    run bash bowling.sh 5 5 3 7 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 31 ]]
}

@test "a spare in the last frame gets a one roll bonus that is counted once" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7 3 7
    [[ $status -eq 0 ]]
    [[ $output == 17 ]]
}

@test "a strike earns ten points in a frame with a single roll" {
    run bash bowling.sh 10 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 10 ]]
}

@test "points scored in the two rolls after a strike are counted twice as a bonus" {
    run bash bowling.sh 10 5 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 26 ]]
}

@test "consecutive strikes each get the two roll bonus" {
    run bash bowling.sh 10 10 10 5 3 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 0 ]]
    [[ $output == 81 ]]
}

@test "a strike in the last frame gets a two roll bonus that is counted once" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 7 1
    [[ $status -eq 0 ]]
    [[ $output == 18 ]]
}

@test "rolling a spare with the two roll bonus does not get a bonus roll" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 7 3
    [[ $status -eq 0 ]]
    [[ $output == 20 ]]
}

@test "strikes with the two roll bonus do not get bonus rolls" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 10 10
    [[ $status -eq 0 ]]
    [[ $output == 30 ]]
}

@test "a strike with the one roll bonus after a spare in the last frame does not get a bonus" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7 3 10
    [[ $status -eq 0 ]]
    [[ $output == 20 ]]
}

@test "all strikes is a perfect game" {
    run bash bowling.sh 10 10 10 10 10 10 10 10 10 10 10 10
    [[ $status -eq 0 ]]
    [[ $output == 300 ]]
}

@test "rolls cannot score negative points" {
    run bash bowling.sh  -1
    [[ $status -eq 1 ]]
    [[ $output == *"Negative roll is invalid"* ]]
}

@test "a roll cannot score more than 10 points" {
    run bash bowling.sh  11
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "two rolls in a frame cannot score more than 10 points" {
    run bash bowling.sh 5 6
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "bonus roll after a strike in the last frame cannot score more than 10 points" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 11
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "two bonus rolls after a strike in the last frame cannot score more than 10 points" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 5 6
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "two bonus rolls after a strike in the last frame can score more than 10 points if one is a strike" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 10 6
    [[ $status -eq 0 ]]
    [[ $output == 26 ]]
}

@test "the second bonus rolls after a strike in the last frame cannot be a strike if the first one is not a strike" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 6 10
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "second bonus roll after a strike in the last frame cannot score more than 10 points" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 10 11
    [[ $status -eq 1 ]]
    [[ $output == *"Pin count exceeds pins on the lane"* ]]
}

@test "an unstarted game cannot be scored" {
    run bash bowling.sh
    [[ $status -eq 1 ]]
    [[ $output == *"Score cannot be taken until the end of the game"* ]]
}

@test "an incomplete game cannot be scored" {
    run bash bowling.sh 0 0
    [[ $status -eq 1 ]]
    [[ $output == *"Score cannot be taken until the end of the game"* ]]
}

@test "cannot roll if game already has ten frames" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    [[ $status -eq 1 ]]
    [[ $output == *"Cannot roll after game is over"* ]]
}

@test "bonus rolls for a strike in the last frame must be rolled before score can be calculated" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10
    [[ $status -eq 1 ]]
    [[ $output == *"Score cannot be taken until the end of the game"* ]]
}

@test "both bonus rolls for a strike in the last frame must be rolled before score can be calculated" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 10
    [[ $status -eq 1 ]]
    [[ $output == *"Score cannot be taken until the end of the game"* ]]
}

@test "bonus roll for a spare in the last frame must be rolled before score can be calculated" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7 3
    [[ $status -eq 1 ]]
    [[ $output == *"Score cannot be taken until the end of the game"* ]]
}

@test "cannot roll after bonus roll for spare" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7 3 2 2
    [[ $status -eq 1 ]]
    [[ $output == *"Cannot roll after game is over"* ]]
}

@test "cannot roll after bonus rolls for strike" {
    run bash bowling.sh 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10 3 2 2
    [[ $status -eq 1 ]]
    [[ $output == *"Cannot roll after game is over"* ]]
}
