----------------------------- MODULE frogs -----------------------------
EXTENDS Integers, TLC


\* k rocks         R
\* n green frogs   G
\* m brown frogs   B
\* k > n+m

CONSTANT G, R, B
ASSUME G > 0
ASSUME R > 0
ASSUME B > 0

VARIABLES count, rocks

-----------------------------------------------------------------------------
TypeInv == /\ rocks \in [0..G+R+B-1 -> -1..1] 
           \* [positions -> possible values]
           \* if -1 then green frog
           \* if 0 then no frog -> rock
           \* if 1 then brown frog

GreenFrogs == 0..G-1
BrownFrogs == G+R..G+R+B-1
GreenFrogsWin == R+B..G+R+B-1
BrownFrogsWin == 0..B-1

Init == /\ PrintT("init")
        /\ count = G + R + B
        /\ rocks = [r \in 0..count-1 |-> IF r \in GreenFrogs THEN -1 ELSE IF r \in BrownFrogs THEN 1 ELSE 0]
        \* if two greens, two rocks and three browns then [-1, -1, 0, 0, 1, 1, 1]
        /\ PrintT(rocks)
     
GreenToRock(f) == /\ rocks[f] = -1 \* f is a green frog
                  /\ f+1 < count-1 \* next position is not water
                  /\ rocks[f+1] = 0 \* there's a rock in the next position
                  /\ rocks' = [rocks EXCEPT ![f] = 0, ![f+1] = -1] \* jump
                  /\ UNCHANGED<<count>>
                  
GreenOverBrown(f) == /\ rocks[f] = -1 \* f is a green frog
                     /\ f+1 < count \* next position is not water
                     /\ f+2 < count \* next next position is not water
                     /\ rocks[f+1] = 1 \* there's a brown frog in the next position
                     /\ rocks[f+2] = 0 \* there's a rock in the next next position
                     /\ rocks' = [rocks EXCEPT ![f] = 0, ![f+2] = -1] \* jump
                     /\ UNCHANGED<<count>>
                     
BrownToRock(f) == /\ rocks[f] = 1 \* f is a brown frog
                  /\ f-1 >= 0 \* next position is not water
                  /\ rocks[f-1] = 0 \* there's a rock is the next position
                  /\ rocks' = [rocks EXCEPT ![f] = 0, ![f-1] = 1] \* jump
                  /\ UNCHANGED<<count>>

BrownOverGreen(f) == /\ rocks[f] = 1 \* f is a brown frog
                     /\ f-1 >= 0 \* next position is not water
                     /\ f-2 >= 0 \* next next position is not water
                     /\ rocks[f-1] = -1 \* there's a green frog in the next position
                     /\ rocks[f-2] = 0 \* there's a rock in the next next position
                     /\ rocks' = [rocks EXCEPT ![f] = 0, ![f-2] = 1] \* jump
                     /\ UNCHANGED<<count>>
                     
Jump(f) == \/ GreenToRock(f) 
           \/ GreenOverBrown(f) 
           \/ BrownToRock(f) 
           \/ BrownOverGreen(f)
           
DoNothing(f) == UNCHANGED<<count, rocks>>

Next ==  \E p \in 0..count-1 : Jump(p) \/ DoNothing(p)

Spec == /\ Init
        /\ [][Next]_<<rocks, count>>
  
-----------------------------------------------------------------------------

Win == [] ~(rocks = [r \in 0..count-1 |-> IF r \in GreenFrogsWin THEN -1 ELSE IF r \in BrownFrogsWin THEN 1 ELSE 0])

=============================================================================
