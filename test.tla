-------------------------------- MODULE test --------------------------------

EXTENDS Naturals

CONSTANT ws

VARIABLE lio, seqnos

Init == /\ lio = 0
        /\ seqnos = <<>>

ConsumerStep == /\ lio' = lio + 1
                /\ seqnos = <<>>
                
ProducerStep == /\ lio' = lio
                /\ seqnos = <<>>

Next == ConsumerStep /\ ProducerStep

Spec == Init /\ [][Next]_<<lio, seqnos>>

=============================================================================
\* Modification History
\* Last modified Wed Dec 11 00:50:23 CET 2019 by df
\* Created Wed Dec 11 00:33:04 CET 2019