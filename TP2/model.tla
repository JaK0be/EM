------------------------------- MODULE model -------------------------------
EXTENDS Integers

VARIABLE pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch, brake, reverseGear, keyState,
         blinkLeft, blinkRight,
         highBeamLights,
         sideBrakeLights, middleBrakeLight,
         reverseLight

InvType == /\ pitmanArmHeight \in 0..2
           /\ pitmanArmDepth \in 0..2 \*0-Neutral;1-Backward;2-Forward
           /\ hazardWarningSwitch \in {0,1}
           /\ brake \in 0..2
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
        /\ reverseGear = 0
        /\ keyState = 0
        /\ blinkLeft = 0
        /\ blinkRight = 0
        /\ highBeamLights = 0
        /\ sideBrakeLights = 0
        /\ middleBrakeLight = 0
        /\ reverseLight = 0


putKeyOnIgnition == /\ keyState = 0
                    /\ keyState' = 1
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear, blinkLeft,blinkRight,
                                    highBeamLights, sideBrakeLights,
                                    middleBrakeLight, reverseLight >>


putKeyOnPosition == /\ keyState = 1
                    /\ keyState' = 2
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear, blinkLeft,blinkRight,
                                    highBeamLights, sideBrakeLights,
                                    middleBrakeLight, reverseLight >>

pitmanBackward == /\ keyState = 2
                  /\ pitmanArmDepth = 0
                  /\ pitmanArmDepth' = 1
                  /\ highBeamLights' = 1
                  /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear, blinkLeft,
                                  blinkRight, sideBrakeLights,
                                  middleBrakeLight, reverseLight,
                                  keyState >>

pitmanBackwardOff == /\ keyState = 2
                     /\ pitmanArmDepth = 1
                     /\ pitmanArmDepth' = 0
                     /\ highBeamLights' = 0
                     /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear, blinkLeft,
                                  blinkRight, sideBrakeLights,
                                  middleBrakeLight, reverseLight,
                                  keyState >>

pitmanForward == /\ keyState = 2
                 /\ pitmanArmDepth = 0
                 /\ pitmanArmDepth' = 2
                 /\ highBeamLights' = 1
                 /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                 brake, reverseGear, blinkLeft,
                                 blinkRight, sideBrakeLights,
                                 middleBrakeLight, reverseLight,
                                 keyState >>

pitmanForwardOff == /\ keyState = 2
                    /\ pitmanArmDepth = 2
                    /\ pitmanArmDepth' = 0
                    /\ highBeamLights' = 0
                    /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                    brake, reverseGear, blinkLeft,
                                    blinkRight, sideBrakeLights,
                                    middleBrakeLight, reverseLight,
                                    keyState >>

reverse == /\ reverseGear = 0
           /\ reverseGear' = 1
           /\ reverseLight' = 1
           /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                           hazardWarningSwitch,brake,
                           blinkLeft,blinkRight,sideBrakeLights,
                           highBeamLights, middleBrakeLight,
                           keyState >>

outReverse == /\ reverseGear = 1
              /\ reverseGear' = 0
              /\ reverseLight' = 0
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

vars == <<pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch, brake, reverseGear, keyState,
          blinkLeft, blinkRight,
          highBeamLights,
          sideBrakeLights, middleBrakeLight,
          reverseLight>>


Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Dec 30 01:45:44 WET 2019 by pedrogoncalves
\* Created Sun Dec 29 22:40:26 WET 2019 by pedrogoncalves
