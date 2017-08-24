\* 
\* Copyright (c) 2017 Thales Austria GmbH
\*
\* Permission is hereby granted, free of charge, to any person obtaining a copy
\* of this software and associated documentation files (the "Software"), to deal
\* in the Software without restriction, including without limitation the rights
\* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
\* copies of the Software, and to permit persons to whom the Software is
\* furnished to do so, subject to the following conditions:
\* 
\* The above copyright notice and this permission notice shall be included in all
\* copies or substantial portions of the Software.
\* 
\* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
\* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
\* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
\* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
\* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
\* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
\* SOFTWARE.
\*

---------------------------- MODULE pingpong_env -----------------------------
EXTENDS pingpong, Naturals


CONSTANTS

    \* the maximum duration of a timeout
    MAX_TIMEOUT_DURATION



VARIABLES

    \* the messages sent by nodes with the following structure:
    \* receiving node |->
    \*      sending node |->
    \*          sequence of sent messages 
    messages,

    \* timeout array with the following structure:
    \* receiving node |->
    \*      slots |->
    \*          timeout \/ NO_TIMEOUT if empty
    timeouts
    
------------------------------------------------------------------------------
\* variable lists
env_vars ==  <<messages, timeouts>>
mod_vars == <<env_vars, vars>>
other_vars == <<stack, local_vars>>


------------------------------------------------------------------------------

\*****************************************************************************
\* definitions for message exchange

\* slot for next message in queue
NEXT_MESSAGE == 0

\* empty sequence, buffers, arrays as defined in structure for messages
\* denoted above
EMPTY_RECEIVE_ARRAY == [sender \in NODE_SET |->  << >>]
EMPTY_MESSAGE_BUFFERS == [receiver \in NODE_SET |-> EMPTY_RECEIVE_ARRAY]

\*****************************************************************************
\* definitions for timeouts

\* slot for timeouts that can expire
CURR_TIMEOUT == 0

\* slots for timeouts
TIMEOUT_DURATIONS == CURR_TIMEOUT .. MAX_TIMEOUT_DURATION

\* array with no timeouts
EMPTY_TIMEOUT_ARRAY ==
    [n \in NODE_SET |->
            [ t \in TIMEOUT_DURATIONS |->  NO_TIMEOUT
            ]
        ]

------------------------------------------------------------------------------



\* all but one node can fail
NodeCanStillFail ==
    Cardinality({n \in NODE_SET: pc[n] = NODE_FAILED}) < N - 1
    

\* prepare reception of a message for a node
ReceiveMessage ==

    \E n \in NODE_SET: \E sender \in NODE_SET:
    
            \* a message is available
        /\ DOMAIN messages[n][sender] /= {}
        
            \* remove message from environment
        /\ messages' =
            [messages EXCEPT ![n][sender] =
                Tail(messages[n][sender])]
            
            \* store message in event parameter for procedure
        /\ event' = [event EXCEPT ![n] = Head(messages[n][sender])]
      
            \* set program counter to the procedure's execution address
        /\ pc' = [pc EXCEPT ![n] = NODE_PROCEDURE_EVENT_ADDRESS]
        
        /\ UNCHANGED <<timeouts, timeout_request_add, timeout_request_del,
                        msg_to_send, other_vars>>


\* prepare reception of a timeout for a Node
ReceiveTimeout ==

    \E n \in NODE_SET:
            
            \* the timout must be enabled for the node
        /\ timeouts[n][CURR_TIMEOUT] /= NO_TIMEOUT
        
            \* remove the timeout
        /\ timeouts' = [timeouts EXCEPT ![n][CURR_TIMEOUT] = NO_TIMEOUT]
        
            \* set event parameter to the timeout
        /\ event' = [event EXCEPT ![n] =
                    [type |-> timeouts[n][CURR_TIMEOUT].type]
                ]
        
            \* set program counter to the procedure's execution address
        /\ pc' = [pc EXCEPT ![n] = NODE_PROCEDURE_EVENT_ADDRESS]
        
        /\ UNCHANGED <<messages, timeout_request_add, timeout_request_del,
                        msg_to_send, other_vars>>


\* shift timeouts
ShiftTimeouts ==
    LET
        \* there are no timeouts in slot 0 pending
        noTimeoutCanBeConsumedAnyMore ==
            \A n \in NODE_SET: timeouts[n][CURR_TIMEOUT] = NO_TIMEOUT
        
        \* there are still messages in transit
        messagesInTransit == messages /= EMPTY_MESSAGE_BUFFERS
                

        \* "shift" registered timeouts closer to expiration
        nextTimeouts ==
            [ n \in NODE_SET |->
                [ t \in TIMEOUT_DURATIONS |-> CASE
                    t = MAX_TIMEOUT_DURATION ->
                        NO_TIMEOUT
                            []
                        
                    OTHER ->
                        timeouts[n][t + 1]
                ]
            ]
    IN
    
    /\ noTimeoutCanBeConsumedAnyMore

    /\ ~messagesInTransit
    
    /\ timeouts' = nextTimeouts
    
    /\ UNCHANGED <<messages, vars>>


\* power up a previously turned off node 
PowerUpNode ==

    \E n \in NODE_SET:
    
            \* node must be off
        /\ pc[n] = NODE_OFF
        
            \* set pc to execute init procedure
        /\ pc' = [pc EXCEPT ![n] = NODE_PROCEDURE_INIT_ADDRESS]
        
        
        /\ UNCHANGED <<messages, timeouts, timeout_request_add,
                        timeout_request_del, msg_to_send, event, other_vars>>


\* fail a node while it is not sending any messages
FailNode ==

    /\ NodeCanStillFail

    /\ \E n \in NODE_SET:
    
            \* node is off or ready
        /\ pc[n] \in {NODE_OFF, NODE_READY}
        
            \* set pc to execute init procedure
        /\ pc' = [pc EXCEPT ![n] = NODE_FAILED]
        
            \* remove all pending messages
        /\ messages' = [messages EXCEPT ![n] = EMPTY_RECEIVE_ARRAY ]
     
            \* remove all pending timeouts
        /\ timeouts' =
                [timeouts EXCEPT ![n] =
                    [ t \in TIMEOUT_DURATIONS |-> NO_TIMEOUT]
                ]
        
        /\ ResetInternalVariables(n)
        
        /\ UNCHANGED <<timeout_request_add, timeout_request_del, msg_to_send,
                        event, stack>>


\* procedure execution
Execute(ce) ==

        \* generated actions from pluscal code
    \/ node_init(ce)

    \/ node_event(ce)

    /\ UNCHANGED <<env_vars>>


\* adapt environment after execution
Finish(n) ==
    LET
    
        \* add message sent by node to be received by the other nodes
        nextMessages ==
            IF msg_to_send /= NO_MESSAGE
                THEN
                    LET
                        dest == msg_to_send.dest
                        msg == msg_to_send.msg
                    IN
                    [recv \in NODE_SET |-> CASE
                   
                            \* sending node won't receive own message
                        recv = n ->
                            messages[recv]
                                []
                        
                            \* inactive nodes won't receive message
                        pc[recv] \in INACTIVE_NODE_STATES ->
                            EMPTY_RECEIVE_ARRAY
                                []
                        
                            \* addressed nodes will receive message
                        dest = ALL_NODES \/ dest = recv -> 
                            [messages[recv] EXCEPT ![n] =
                                    Append(messages[recv][n], msg)]
                                []
                       
                            \* not addressed nodes won't receive message 
                        OTHER -> 
                            messages[recv]
                    ]
                    
            ELSE  messages


        nextRunningTimeout(time, oldTimeout) == CASE

                \* check requested timeout duration for sanity
            timeout_request_add /= NO_TIMEOUT /\
                    timeout_request_add.time > MAX_TIMEOUT_DURATION ->
                Assert(FALSE, <<"The duration of timeout",
                    timeout_request_add.type,
                    "of", timeout_request_add.time ,
                    "exceeds the maximum configured timeout duration of",
                    MAX_TIMEOUT_DURATION>>)
                    []

                \* add new timeout
            timeout_request_add /= NO_TIMEOUT /\
                        timeout_request_add.time = time ->
                [ type |-> timeout_request_add.type ]
                    []
            
                \* cancel running timeouts of same type
            timeout_request_add /= NO_TIMEOUT /\
                        oldTimeout.type = timeout_request_add.type ->
                NO_TIMEOUT
                    []
            
                \* execute explicit cancel requests  
            timeout_request_del /= NO_TIMEOUT /\
                        oldTimeout.type = timeout_request_del.type -> 
                NO_TIMEOUT
                    []
                    
            OTHER -> oldTimeout
        
       
        \* update nodes timeouts 
        nextTimeouts ==
            [timeouts EXCEPT ![n] =
                [ t \in TIMEOUT_DURATIONS |->
                    nextRunningTimeout(t, timeouts[n][t])
                ]
            ]
        
    IN
        \* reset program counter
    /\ pc' = [pc EXCEPT ![n] = NODE_READY]

        \* reset msg_to_send to default value to minimize state space
    /\ msg_to_send' = NO_MESSAGE
    
        \* reset event to initial value to minimize state space
    /\ event' = [event EXCEPT ![n] = defaultInitValue]
    
        \* reset timeout_requests
    /\ timeout_request_add' = NO_TIMEOUT
    
    /\ timeout_request_del' = NO_TIMEOUT
    
        \* update messages sent in environment
    /\ messages' = nextMessages
    
        \* update timeouts
    /\ timeouts' = nextTimeouts
    
    /\ UNCHANGED <<other_vars>>
        

\* fail node after procedure execution with potential partial reception of
\* sent messages
FailFinish(n) ==
    LET
        \* erase pending messages for failing node and add sent message to
        \* receive nodes
        nextMessages(ReceivedNodes) ==
            
            IF msg_to_send /= NO_MESSAGE
                THEN
                    LET
                        dest == msg_to_send.dest
                        msg == msg_to_send.msg
                    IN
                    [recv \in NODE_SET |-> CASE
                    
                            \* erase pending messages for node
                        recv = n ->
                            EMPTY_RECEIVE_ARRAY
                                []

                            \* do not deliver messages to other nodes
                        pc[recv] \in INACTIVE_NODE_STATES ->
                            EMPTY_RECEIVE_ARRAY
                                []
                        
                            \* deliver depeding on destination and ReceivedNodes
                        /\ dest = ALL_NODES \/ dest = recv
                        /\ recv \in ReceivedNodes -> 
                            [messages[recv] EXCEPT ![n] =
                                    Append(messages[recv][n], msg)]
                                []
                                
                        OTHER -> 
                            messages[recv]
                    ]
                    
            ELSE [messages EXCEPT ![n] =
                EMPTY_RECEIVE_ARRAY]
        
        
        \* erase pending timeouts
        nextTimeouts ==
            [timeouts EXCEPT ![n] =
                [ t \in TIMEOUT_DURATIONS |-> NO_TIMEOUT]
            ]
    IN
    
    /\ NodeCanStillFail
   
        \* fail node 
    /\ pc' = [pc EXCEPT ![n] = NODE_FAILED]

        \* reset msg_to_send to default value to minimize state space
    /\ msg_to_send' = NO_MESSAGE
    
        \* reset event to initial value to minimize state space
    /\ event' = [event EXCEPT ![n] = defaultInitValue]
    
        \* reset timeout_requests
    /\ timeout_request_add' = NO_TIMEOUT
    
    /\ timeout_request_del' = NO_TIMEOUT
    
        \* update messages to be delivered in environment by selecting a
        \* non-empty subset of nodes in NODE_SET - all combinations will be
        \* evaluated
    /\ \E s \in {rn \in SUBSET NODE_SET: Cardinality(rn) > 0}:
        messages' = nextMessages(s)
    
        \* reset timeouts
    /\ timeouts' = nextTimeouts
    
    /\ ResetInternalVariables(n)

    /\ UNCHANGED <<stack>>

------------------------------------------------------------------------------

\* Inital state of model
ModInit ==

        \* pluscal variables
    /\ VarInit
    
        \* pluscal execution environment 
    /\ event = [ n \in NODE_SET |-> defaultInitValue]
    /\ stack = [ n \in NODE_SET |-> << >>]
    /\ pc = [n \in NODE_SET |-> NODE_OFF]
    
        \* environment
    /\ messages = EMPTY_MESSAGE_BUFFERS
        
    /\ timeouts = EMPTY_TIMEOUT_ARRAY
        

------------------------------------------------------------------------------

\* choose an event for a node
NextUndeterministicEvent ==

        \* ALL nodes must not execute or finish a step
    /\ (\A n \in NODE_SET: pc[n] \in NON_EXECUTING_STATES)
    /\ 
        \/ ReceiveMessage
        \/ ReceiveTimeout
        \/ ShiftTimeouts
        \/ PowerUpNode


\* execute pluscal process
NextExecuteStep ==

    \E ce \in NODE_SET:

            \* there is an execution address in the pc
        /\ pc[ce] \notin
            NON_EXECUTING_STATES \cup
                {NODE_READY, NODE_PROCEDURE_EXECUTION_ENDED}

        /\ Execute(ce) 


\* restore environment after procedure execution
NextFinishStep ==

    \E n \in NODE_SET:
    
            \* procedure must result in Error
        /\ pc[n] = NODE_PROCEDURE_EXECUTION_ENDED
        
            \* store changes in environment
        /\  Finish(n)


\* all actions that have some notion of progress
ProgressNext ==

        \* choose one of the nodes or the environment to execute
    \/ NextUndeterministicEvent
   
        \* execute event (if needed by the event chosen above)
    \/ NextExecuteStep
        
        \* finish execution of event (if needed by the event chosen above)
    \/ NextFinishStep


\* all actions that impose a fault
FaultNext ==

    \* Node fails while inactive
    \/  /\ (\A n \in NODE_SET: pc[n] \in NON_EXECUTING_STATES)
            
        /\ FailNode
        
    \* Node fails during sending of messages
    \/  \E n \in NODE_SET:

            \* pc must show that procedure execution is finished
        /\ pc[n] \in {NODE_PROCEDURE_EXECUTION_ENDED}
           
        /\ FailFinish(n)


\* All actions that can happen in the model
ModNext ==
    \/ ProgressNext    
    \/ FaultNext


\* The model specification
ModSpec ==
    /\ ModInit
    /\ [][ModNext]_mod_vars
    /\ WF_mod_vars(ProgressNext)

\* Note: strong fairness for upper layer is not needed here, since no upper
\* layer actions are defined in this small example

==============================================================================

