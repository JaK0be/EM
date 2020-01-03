------------------------------- MODULE model -------------------------------
EXTENDS Integers

VARIABLE pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch,
         brake, sideBrakeLightsActivated, middleBrakeLightFlashing,
         reverseGear, keyState,
         blinkLeft, blinkRight,
         highBeamLights,
         sideBrakeLights, middleBrakeLight,
         reverseLight

InvType == /\ pitmanArmHeight \in 0..2
           /\ pitmanArmDepth \in 0..2 \*0-Neutral;1-Backward;2-Forward
           /\ hazardWarningSwitch \in {0,1}
           /\ brake \in 0..225 \* 225 = 45 degrees
           /\ sideBrakeLightsActivated \in {0,1}
           /\ middleBrakeLightFlashing \in {0,1}
           /\ reverseGear \in {0,1}
           /\ keyState \in 0..2
           /\ blinkLeft \in {0,1}
           /\ blinkRight \in {0,1}
           /\ highBeamLights \in {0,1} \*0-Desligado;1-Ligado
           /\ sideBrakeLights \in {0,1}
           /\ middleBrakeLight \in {0,1}
           /\ reverseLight \in {0,1}

Init == /\ pitmanArmHeight = 0
        /\ pitmanArmDepth = 0
        /\ hazardWarningSwitch = 0
        /\ brake = 0
        /\ sideBrakeLightsActivated = 0
        /\ middleBrakeLightFlashing = 0
        /\ reverseGear = 0
        /\ keyState = 0
        /\ blinkLeft = 0
        /\ blinkRight = 0
        /\ highBeamLights = 0
        /\ sideBrakeLights = 0
        /\ middleBrakeLight = 0
        /\ reverseLight = 0

SideBrakeLights == IF sideBrakeLightsActivated = 1
                   THEN (sideBrakeLights' = 1 /\ sideBrakeLightsActivated' = IF brake < 5  THEN 0 ELSE sideBrakeLightsActivated)
                   ELSE (sideBrakeLights' = 0 /\ sideBrakeLightsActivated' = IF brake > 15 THEN 1 ELSE sideBrakeLightsActivated)

MiddleBrakeLight == IF middleBrakeLightFlashing = 1
                    THEN (middleBrakeLight' = 1 - middleBrakeLight /\ middleBrakeLightFlashing' = IF brake = 0   THEN 0 ELSE middleBrakeLightFlashing)
                    ELSE (middleBrakeLight' = 0                    /\ middleBrakeLightFlashing' = IF brake > 200 THEN 1 ELSE middleBrakeLightFlashing)

normalBraking == /\ brake = 0
                 /\ brake' \in 15..200 \* Varia entre 3º e 40º
                 /\ SideBrakeLights
                 /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                                 hazardWarningSwitch, reverseGear,
                                 blinkLeft, blinkRight, highBeamLights,
                                 middleBrakeLight, reverseLight >>
                                 
fullBraking == /\ brake \in 0..200 \*Garante que não está em fullBraking
               /\ brake' \in 201..225
               /\ SideBrakeLights /\ MiddleBrakeLight
               /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                               hazardWarningSwitch, reverseGear,
                               blinkLeft, blinkRight, highBeamLights,
                               reverseLight >>
                               
stopBraking == /\ brake \in 1..225
               /\ brake' = 0
               /\ SideBrakeLights /\ MiddleBrakeLight 
               /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                               hazardWarningSwitch, reverseGear,
                               blinkLeft, blinkRight, highBeamLights,
                               reverseLight >>

putKeyOnIgnition == /\ keyState = 0
                    /\ keyState' = 1
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear, blinkLeft,blinkRight,
                                    highBeamLights, sideBrakeLights,
                                    middleBrakeLight, reverseLight >>


putKeyOnPosition == /\ keyState = 1
                    /\ keyState' = 2
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear, blinkLeft,blinkRight,
                                    highBeamLights, sideBrakeLights,
                                    middleBrakeLight, reverseLight >>

pitmanBackward == /\ keyState = 2
                  /\ pitmanArmDepth = 0
                  /\ pitmanArmDepth' = 1
                  /\ highBeamLights' = 1
                  /\ SideBrakeLights /\ MiddleBrakeLight
                  /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear, blinkLeft,
                                  blinkRight, sideBrakeLights,
                                  middleBrakeLight, reverseLight,
                                  keyState >>

pitmanBackwardOff == /\ keyState = 2
                     /\ pitmanArmDepth = 1
                     /\ pitmanArmDepth' = 0
                     /\ highBeamLights' = 0
                     /\ SideBrakeLights /\ MiddleBrakeLight
                     /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear, blinkLeft,
                                  blinkRight, sideBrakeLights,
                                  middleBrakeLight, reverseLight,
                                  keyState >>

pitmanForward == /\ keyState = 2
                 /\ pitmanArmDepth = 0
                 /\ pitmanArmDepth' = 2
                 /\ highBeamLights' = 1
                 /\ SideBrakeLights /\ MiddleBrakeLight
                 /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                 brake, reverseGear, blinkLeft,
                                 blinkRight, sideBrakeLights,
                                 middleBrakeLight, reverseLight,
                                 keyState >>

pitmanForwardOff == /\ keyState = 2
                    /\ pitmanArmDepth = 2
                    /\ pitmanArmDepth' = 0
                    /\ highBeamLights' = 0
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                    brake, reverseGear, blinkLeft,
                                    blinkRight, sideBrakeLights,
                                    middleBrakeLight, reverseLight,
                                    keyState >>

reverse == /\ reverseGear = 0
           /\ reverseGear' = 1
           /\ reverseLight' = 1
           /\ SideBrakeLights /\ MiddleBrakeLight
           /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                           hazardWarningSwitch,brake,
                           blinkLeft,blinkRight,sideBrakeLights,
                           highBeamLights, middleBrakeLight,
                           keyState >>

outReverse == /\ reverseGear = 1
              /\ reverseGear' = 0
              /\ reverseLight' = 0
              /\ SideBrakeLights /\ MiddleBrakeLight
              /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                              hazardWarningSwitch,brake,
                              blinkLeft,blinkRight,sideBrakeLights,
                              highBeamLights, middleBrakeLight,
                              keyState >>

Next == \/ putKeyOnIgnition
        \/ putKeyOnPosition
        \/ pitmanBackward
        \/ pitmanBackwardOff
        \/ pitmanForward
        \/ pitmanForwardOff
        \/ outReverse
        \/ reverse
        \/ normalBraking
        \/ fullBraking
        \/ stopBraking

vars == <<pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch, brake, reverseGear, keyState,
          blinkLeft, blinkRight, sideBrakeLightsActivated, middleBrakeLightFlashing,
          highBeamLights,
          sideBrakeLights, middleBrakeLight,
          reverseLight>>


Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Fri Jan 03 16:47:20 WET 2020 by pedrogoncalves
\* Created Sun Dec 29 22:40:26 WET 2019 by pedrogoncalves