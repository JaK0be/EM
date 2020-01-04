------------------------------- MODULE model -------------------------------
EXTENDS Integers

VARIABLE pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch,
         brake, sideBrakeLightsActivated, middleBrakeLightFlashing,
         reverseGear, keyState,
         blinkLeft, blinkRight,
         highBeamLights,
         sideBrakeLights, middleBrakeLight,
         reverseLight

InvType == /\ pitmanArmHeight \in 0..2 \*0-Neureal;1-Upward;2-Downward
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

LeftBlinkLight == IF pitmanArmHeight = 2
                  THEN (blinkLeft' = 1 - blinkLeft)
                  ELSE (blinkLeft' = 0)

RightBlinkLight == IF pitmanArmHeight = 1
                   THEN (blinkRight' = 1 - blinkRight)
                   ELSE (blinkRight' = 0)

normalBraking == /\ keyState = 2
                 /\ brake = 0
                 /\ brake' \in 15..200 \* Varia entre 3º e 40º
                 /\ SideBrakeLights /\ MiddleBrakeLight
                 /\ LeftBlinkLight /\ RightBlinkLight
                 /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                                 hazardWarningSwitch, reverseGear,
                                 highBeamLights,
                                 reverseLight >>

fullBraking == /\ keyState = 2
               /\ brake \in 0..200 \*Garante que não está em fullBraking
               /\ brake' \in 201..225
               /\ SideBrakeLights /\ MiddleBrakeLight
               /\ LeftBlinkLight /\ RightBlinkLight
               /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                               hazardWarningSwitch, reverseGear,
                               highBeamLights,
                               reverseLight >>

stopBraking == /\ keyState = 2
               /\ brake \in 1..225
               /\ brake' = 0
               /\ sideBrakeLights' = 0
               /\ sideBrakeLightsActivated' = 0
               /\ middleBrakeLight' = 0
               /\ middleBrakeLightFlashing' = 0
               /\ SideBrakeLights /\ MiddleBrakeLight
               /\ LeftBlinkLight /\ RightBlinkLight
               /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                               hazardWarningSwitch, reverseGear,
                               highBeamLights,
                               reverseLight >>

putKeyOnIgnition == /\ keyState = 0
                    /\ keyState' = 1
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ LeftBlinkLight /\ RightBlinkLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear,
                                    highBeamLights,
                                    reverseLight >>


putKeyOnPosition == /\ keyState = 1
                    /\ keyState' = 2
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ LeftBlinkLight /\ RightBlinkLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear,
                                    highBeamLights,
                                    reverseLight >>

pitmanUpward == /\ keyState = 2
                /\ pitmanArmHeight = 0
                /\ pitmanArmHeight' = 1
                /\ SideBrakeLights /\ MiddleBrakeLight
                /\ LeftBlinkLight /\ RightBlinkLight
                /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                brake, reverseGear,
                                reverseLight, highBeamLights,
                                keyState >>

pitmanUpwardOff == /\ keyState = 2
                   /\ pitmanArmHeight = 1
                   /\ pitmanArmHeight' = 0
                   /\ blinkRight' = 0
                   /\ SideBrakeLights /\ MiddleBrakeLight
                   /\ LeftBlinkLight /\ RightBlinkLight
                   /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                brake, reverseGear,
                                reverseLight, highBeamLights,
                                keyState >>

pitmanDownward == /\ keyState = 2
                  /\ pitmanArmHeight = 0
                  /\ pitmanArmHeight' = 2
                  /\ SideBrakeLights /\ MiddleBrakeLight
                  /\ LeftBlinkLight /\ RightBlinkLight
                  /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                  brake, reverseGear, highBeamLights,
                                  reverseLight,
                                  keyState >>

pitmanDownwardOff == /\ keyState = 2
                     /\ pitmanArmHeight = 2
                     /\ pitmanArmHeight' = 0
                     /\ blinkLeft' = 0
                     /\ SideBrakeLights /\ MiddleBrakeLight
                     /\ LeftBlinkLight /\ RightBlinkLight
                     /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                     brake, reverseGear, highBeamLights,
                                     reverseLight,
                                     keyState >>

pitmanBackward == /\ keyState = 2
                  /\ pitmanArmDepth = 0
                  /\ pitmanArmDepth' = 1
                  /\ highBeamLights' = 1
                  /\ SideBrakeLights /\ MiddleBrakeLight
                  /\ LeftBlinkLight /\ RightBlinkLight
                  /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear,
                                  reverseLight,
                                  keyState >>

pitmanBackwardOff == /\ keyState = 2
                     /\ pitmanArmDepth = 1
                     /\ pitmanArmDepth' = 0
                     /\ highBeamLights' = 0
                     /\ SideBrakeLights /\ MiddleBrakeLight
                     /\ LeftBlinkLight /\ RightBlinkLight
                     /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                  brake, reverseGear,
                                  reverseLight,
                                  keyState >>

pitmanForward == /\ keyState = 2
                 /\ pitmanArmDepth = 0
                 /\ pitmanArmDepth' = 2
                 /\ highBeamLights' = 1
                 /\ SideBrakeLights /\ MiddleBrakeLight
                 /\ LeftBlinkLight /\ RightBlinkLight
                 /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                 brake, reverseGear,
                                 reverseLight,
                                 keyState >>

pitmanForwardOff == /\ keyState = 2
                    /\ pitmanArmDepth = 2
                    /\ pitmanArmDepth' = 0
                    /\ highBeamLights' = 0
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ LeftBlinkLight /\ RightBlinkLight
                    /\ UNCHANGED << pitmanArmHeight, hazardWarningSwitch,
                                    brake, reverseGear,
                                    reverseLight,
                                    keyState >>

reverse == /\ keyState = 2
           /\ reverseGear = 0
           /\ reverseGear' = 1
           /\ reverseLight' = 1
           /\ SideBrakeLights /\ MiddleBrakeLight
           /\ LeftBlinkLight /\ RightBlinkLight
           /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                           hazardWarningSwitch,brake,
                           highBeamLights,
                           keyState >>

outReverse == /\ keyState = 2
              /\ reverseGear = 1
              /\ reverseGear' = 0
              /\ reverseLight' = 0
              /\ SideBrakeLights /\ MiddleBrakeLight
              /\ LeftBlinkLight /\ RightBlinkLight
              /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                              hazardWarningSwitch,brake,
                              highBeamLights,
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
        \/ pitmanUpward
        \/ pitmanUpwardOff
        \/ pitmanDownward
        \/ pitmanDownwardOff

\* Propriedades do Sistema 
\** Safety

safety1 == []((sideBrakeLights = 1)=>(brake > 5)) \*Luzes de travagem laterais só se ligam se ângulo do pedal do travão for superior a 3º 

safety2 == []((blinkLeft = 1) => (blinkRight = 0)) \*Só se verifica pois os 4piscas não estão implementados

safety3 == []((blinkRight = 1) => (blinkLeft = 0)) \*Só se verifica pois os 4piscas não estão implementados

safety4 == []((reverseLight = 1) => (reverseGear = 1)) \*Luz de marcha atrás só se encontra ligada se essa mudança estiver engrenhada

safety5 == []((middleBrakeLight = 1)=>(brake > 200)) \*Luz de travagem central só se liga se ângulo do pedal do travão for superior a 40º 

safety6 == []((pitmanArmHeight = 0) => (blinkRight = 0 /\ blinkLeft = 0)) \*Se pitmanHeight se encontrar na posição neutra, piscas estão desligados (Só se verifica pois 4piscas não estão implementados) 

safety7 == []((highBeamLights = 1) => (pitmanArmDepth > 0)) \*Para máximos estarem ligados, pitmanArmDepth não pode estar em posição neutra

\** Liveness

\*liveness == <>(blinkLeft=1)
  

vars == <<pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch, brake, reverseGear, keyState,
          blinkLeft, blinkRight, sideBrakeLightsActivated, middleBrakeLightFlashing,
          highBeamLights,
          sideBrakeLights, middleBrakeLight,
          reverseLight>>


Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sat Jan 04 16:40:38 WET 2020 by pedrogoncalves
\* Created Sun Dec 29 22:40:26 WET 2019 by pedrogoncalves