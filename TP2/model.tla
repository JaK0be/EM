------------------------------- MODULE model -------------------------------
\* Temas: sistema de luzes (parcial), mercado europeu
\* Autores:
\*    - Alexandre Pinho (A82441)
\*    - Pedro Gonçalves (A82313)

EXTENDS Integers

\* Variáveis que representam os vários
\* componentes do sistema, tais como,
\* luzes, posições dos pitman, estado da chave na ignição, etc
VARIABLE pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch,
         brake, sideBrakeLightsActivated, middleBrakeLightFlashing,
         reverseGear, keyState,
         blinkLeft, blinkRight,
         highBeamLights,
         sideBrakeLights, middleBrakeLight,
         reverseLight

\* Definição dos tipos das variáveis
InvType == /\ pitmanArmHeight \in 0..2 \*0-Neutral;1-Upward;2-Downward
           /\ pitmanArmDepth \in 0..2 \*0-Neutral;1-Backward;2-Forward
           /\ hazardWarningSwitch \in {0,1}
           /\ brake \in 0..225 \* 225 = 45 degrees
           /\ sideBrakeLightsActivated \in {0,1} \*0-Não;1-Sim
           /\ middleBrakeLightFlashing \in {0,1} \*0-Não;1-Sim
           /\ reverseGear \in {0,1} \*0-Não Engrenada;1-Engrenada
           /\ keyState \in 0..2 \*0-No Key Inserted;1-Key On Ignition;2-Key On Position
           /\ blinkLeft \in {0,1} \*0-Desligado;1-Ligado
           /\ blinkRight \in {0,1} \*0-Desligado;1-Ligado
           /\ highBeamLights \in {0,1} \*0-Desligado;1-Ligado
           /\ sideBrakeLights \in {0,1} \*0-Desligado;1-Ligado
           /\ middleBrakeLight \in {0,1} \*0-Desligado;1-Ligado
           /\ reverseLight \in {0,1} \*0-Desligado;1-Ligado

\* Estado Inicial das Variáveis
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

\* Módulo que liga e desliga as luzes laterais dos travões
SideBrakeLights == IF sideBrakeLightsActivated = 1
                   THEN (sideBrakeLights' = 1 /\ sideBrakeLightsActivated' = IF brake < 5  THEN 0 ELSE sideBrakeLightsActivated)
                   ELSE (sideBrakeLights' = 0 /\ sideBrakeLightsActivated' = IF brake > 15 THEN 1 ELSE sideBrakeLightsActivated)

\* Módulo que define o piscar da luz de travagem central
\* É ativada após o ângulo do pedal do travão ser superior a 40º
\* Só se desliga quando o ângulo do pedal do travão volta a 0º
MiddleBrakeLight == IF middleBrakeLightFlashing = 1
                    THEN (middleBrakeLight' = 1 - middleBrakeLight /\ middleBrakeLightFlashing' = IF brake = 0   THEN 0 ELSE middleBrakeLightFlashing)
                    ELSE (middleBrakeLight' = 0                    /\ middleBrakeLightFlashing' = IF brake > 200 THEN 1 ELSE middleBrakeLightFlashing)

\* Módulo que define o piscar do pisca esquerdo
LeftBlinkLight == IF pitmanArmHeight = 2
                  THEN (blinkLeft' = 1 - blinkLeft)
                  ELSE (blinkLeft' = 0)

\* Módulo que define o piscar do pisca direito
RightBlinkLight == IF pitmanArmHeight = 1
                   THEN (blinkRight' = 1 - blinkRight)
                   ELSE (blinkRight' = 0)

\* Módulo que define a operação de aplicar o
\* pedal do travão entre 3º e 40º
\* Apenas as luzes de travagem laterais ficam ativas
normalBraking == /\ keyState = 2
                 /\ brake = 0
                 /\ brake' \in 15..200 \* Varia entre 3º e 40º
                 /\ SideBrakeLights /\ MiddleBrakeLight
                 /\ LeftBlinkLight /\ RightBlinkLight
                 /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                                 hazardWarningSwitch, reverseGear,
                                 highBeamLights,
                                 reverseLight >>

\* Módulo que define a operação de aplicar o
\* pedal do travão com um ângulo superior a 40º
\* As luzes de travagem laterais ficam ativas 
\* e a luz de travagem central fica a piscar
\* até o ângulo do pedal voltar a 0 
fullBraking == /\ keyState = 2
               /\ brake \in 0..200 \*Garante que não está em fullBraking
               /\ brake' \in 201..225
               /\ SideBrakeLights /\ MiddleBrakeLight
               /\ LeftBlinkLight /\ RightBlinkLight
               /\ UNCHANGED << keyState, pitmanArmHeight, pitmanArmDepth,
                               hazardWarningSwitch, reverseGear,
                               highBeamLights,
                               reverseLight >>

\* Módulo que define a operação de parar de travar
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

\* Módulo que define a operação de colocar
\* a chave na ignição
putKeyOnIgnition == /\ keyState = 0
                    /\ keyState' = 1
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ LeftBlinkLight /\ RightBlinkLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear,
                                    highBeamLights,
                                    reverseLight >>

\* Módulo que define a operação de ligar o carro
putKeyOnPosition == /\ keyState = 1
                    /\ keyState' = 2
                    /\ SideBrakeLights /\ MiddleBrakeLight
                    /\ LeftBlinkLight /\ RightBlinkLight
                    /\ UNCHANGED << pitmanArmHeight,pitmanArmDepth,
                                    hazardWarningSwitch, brake,
                                    reverseGear,
                                    highBeamLights,
                                    reverseLight >>

\* Módulo que define a operação de ligar os piscas da direita
pitmanUpward == /\ keyState = 2
                /\ pitmanArmHeight = 0
                /\ pitmanArmHeight' = 1
                /\ SideBrakeLights /\ MiddleBrakeLight
                /\ LeftBlinkLight /\ RightBlinkLight
                /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                brake, reverseGear,
                                reverseLight, highBeamLights,
                                keyState >>

\* Módulo que define a operação de desligar os piscas da esquerda
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

\* Módulo que define a operação de ligar os piscas da esquerda
pitmanDownward == /\ keyState = 2
                  /\ pitmanArmHeight = 0
                  /\ pitmanArmHeight' = 2
                  /\ SideBrakeLights /\ MiddleBrakeLight
                  /\ LeftBlinkLight /\ RightBlinkLight
                  /\ UNCHANGED << pitmanArmDepth, hazardWarningSwitch,
                                  brake, reverseGear, highBeamLights,
                                  reverseLight,
                                  keyState >>

\* Módulo que define a operação de desligar os piscas da esquerda
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

\* Módulo que define a operação de ligar os máximos em modo temporário
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

\* Módulo que define a operação de desligar os máximos de modo temporário
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

\* Módulo que define a operação de ligar os máximos em modo permanente
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

\* Módulo que define a operação de desligar os máximos de modo permanente
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

\* Módulo que define a operação de engrenar a mudança de marcha-atrás
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

\* Módulo que define a operação de desengrenar a mudança de marcha-atrás 
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

\* Luzes de travagem laterais só se ligam se o 
\* ângulo do pedal do travão for superior a 3º 
safety1 == []((sideBrakeLights = 1)=>(brake > 5))

\* Só se verifica pois os 4piscas não estão implementados
safety2 == []((blinkLeft = 1) => (blinkRight = 0))

\* Só se verifica pois os 4piscas não estão implementados
safety3 == []((blinkRight = 1) => (blinkLeft = 0))

\* Luz de marcha atrás só se encontra ligada se essa mudança estiver engrenhada
safety4 == []((reverseLight = 1) => (reverseGear = 1)) 

\* Luz de travagem central só se liga se o 
\* ângulo do pedal do travão for superior a 40º
safety5 == []((middleBrakeLight = 1)=>(brake > 200))  

\* Se pitmanHeight se encontrar na posição neutra,
\* piscas estão desligados (Só se verifica pois 4piscas não estão implementados)
safety6 == []((pitmanArmHeight = 0) => (blinkRight = 0 /\ blinkLeft = 0))  

\*Para máximos estarem ligados, pitmanArmDepth não pode estar em posição neutra
safety7 == []((highBeamLights = 1) => (pitmanArmDepth > 0)) 

\** Liveness

\* Assumindo fairness, é sempre possível chegar a um estado
\* em que se liga pelo menos uma das luzes
liveness1 == [](<>(blinkLeft=1 \/ blinkRight=1 \/ highBeamLights=1 \/ reverseLight=1 \/ sideBrakeLights=1))
  

vars == <<pitmanArmHeight, pitmanArmDepth, hazardWarningSwitch, brake, reverseGear, keyState,
          blinkLeft, blinkRight, sideBrakeLightsActivated, middleBrakeLightFlashing,
          highBeamLights,
          sideBrakeLights, middleBrakeLight,
          reverseLight>>


Spec == Init /\ [][Next]_vars /\ WF_vars(putKeyOnIgnition)
                              /\ WF_vars(putKeyOnPosition)
                              /\ WF_vars(pitmanBackward)
                              /\ WF_vars(pitmanBackwardOff)
                              /\ WF_vars(pitmanForward)
                              /\ WF_vars(pitmanForwardOff)
                              /\ WF_vars(outReverse)
                              /\ WF_vars(reverse)
                              /\ WF_vars(normalBraking)
                              /\ WF_vars(fullBraking)
                              /\ WF_vars(stopBraking)
                              /\ WF_vars(pitmanUpward)
                              /\ WF_vars(pitmanUpwardOff)
                              /\ WF_vars(pitmanDownward)
                              /\ WF_vars(pitmanDownwardOff)

=============================================================================
\* Modification History
\* Last modified Mon Jan 06 22:17:39 WET 2020 by pedrogoncalves
\* Created Sun Dec 29 22:40:26 WET 2019 by pedrogoncalves