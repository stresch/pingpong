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

------------------------------- MODULE pingpong ------------------------------

EXTENDS seqnr, Sequences, FiniteSets, Integers, TLC

CONSTANT

    \* the number of nodes
    N

------------------------------------------------------------------------------
\* node related constants

\* number of nodes
NODE_SET == 0..N-1

\* constants for no and all nodes
NO_NODE == N
ALL_NODES == N + 1 

\* node states/addresses for program counter
NODE_OFF == "off"
NODE_READY == "ready"
NODE_FAILED == "failed"

NODE_PROCEDURE_INIT_ADDRESS == "init"
NODE_PROCEDURE_EVENT_ADDRESS == "event_h"
NODE_PROCEDURE_EXECUTION_ENDED == "Error"

INACTIVE_NODE_STATES == {NODE_OFF, NODE_FAILED}
NON_EXECUTING_STATES == INACTIVE_NODE_STATES \cup {NODE_READY}


------------------------------------------------------------------------------
\* states for pingpong state machine

STATE_START == "state_start"
STATE_RUNNING == "state_running"

\* node view information
ON == "on"
OFF == "off"

------------------------------------------------------------------------------
\* timeout definitions
TO_PING == "to_ping"
TO_PING_TIME == 1
TO_PING_STARTUP_TIME == TO_PING_TIME + 1

\* special no-timeout for TLC comparison
NO_TIMEOUT == [type |-> "__notimeout"]

------------------------------------------------------------------------------
\* message definitions
MSG_PING == "msg_ping"
MSG_PONG == "msg_pong"

\* special no-message for TLC comparison
NO_MESSAGE == [no_message |-> ""]

------------------------------------------------------------------------------

\* Here are the PlusCal definitions that are translated to TLA+ in the same
\* file below, marked TRANSLATION in the comments 

(* --algorithm PingPong {


    variables
       
        \*********************************************************************
        \* variables for communication with environment

        \* sending message
        msg_to_send;
        
        \* adding timeout
        timeout_request_add;
        
        \* deleting timeout
        timeout_request_del;
        
        
        \*********************************************************************
        \* variables on node level
        
       
        state;     \* current state of node 
        view;      \* observed state of other nodes
        seqnr;     \* the sequence number of the current ping
  
    define {
        
        \* node level variable list
        local_vars == <<state, view, seqnr>>
    }

    \*************************************************************************
    \* API to upper layer
    \* 

    \* is not neccessary for the ping pong example

    \*************************************************************************
    \* API to environment 
    \*   

    \* send message    
    macro send_msg (destination, message) {
        msg_to_send := [ dest |-> destination, msg |-> message ];
    }
    
    \* broadcast message 
    macro bcast_msg (message) {
        msg_to_send := [ dest |-> ALL_NODES, msg |-> message ];
    }

    \* add a timer - this removes a timer of the same type, if it is present
    macro start_timeout (timer_type, timer_time) {
        timeout_request_add :=
            [ type |-> timer_type,
            time |-> timer_time];
    }
    
    
    \* delete a timer
    macro stop_timeout (timer_type) {
        timeout_request_del :=
            [ type |-> timer_type];
    }



    \*************************************************************************
    \* algorithm specific functions
    \* 

    
    \* set all but own and initiating node to OFF 
    macro reset_node_view (initiator_node) {
        view[self] :=
            [ n \in NODE_SET |-> CASE
                n = self ->
                    ON
                        []
                n = initiator_node ->
                    ON
                        []
                OTHER ->
                    OFF
            ]; 
    }
   
    \* set node answering with pong to ON
    macro register_node_on (node) {
        view[self][node] := ON;
    }
    

    \* send new ping
    macro send_message (initiator_node, message_type) {
       
        \* start timeout ping
        start_timeout(TO_PING, TO_PING_TIME);
       
        \* send out the ping or pong message
        bcast_msg([
                sender |-> self,
                type |-> message_type,
                seqnr |-> seqnr[self]
            ]);
                
    }
   
    \*************************************************************************
    \* functions driven by environment
    \*

    \* initialization
    procedure node_init () {
init:
        state[self] := STATE_START;

        \* set all but own state to off
        reset_node_view(NO_NODE);

        \* start a timeout to send ping for the first time
        start_timeout(TO_PING, TO_PING_STARTUP_TIME);
    }


    \* event handling
    procedure node_event (event) {
event_h:

        if (STATE_START = state[self]) {

            if (MSG_PING = event.type \/ MSG_PONG = event.type) {

                \* this node is in start ->
                \*  + adapt the seqence number
                \*  + reset node view
                \*  + send ping as answer

                seqnr[self] := event.seqnr;
                reset_node_view(event.sender);
                send_message(event.sender, MSG_PONG);

                \* set the node state to runnig
                state[self] := STATE_RUNNING;
    
            } else if (TO_PING = event.type) {

                \* no other node here->
                \*  + start with a ping
                send_message(NO_NODE, MSG_PING);

                \* set the node state to runnig
                state[self] := STATE_RUNNING;
            
            } else {

                \* unexpected event
                print <<"event:", event>>;
                assert FALSE;
            }


        } else if (STATE_RUNNING = state[self]) {

            if (MSG_PING = event.type) {

                \* check for sanity
                if (cmp_seqnr(event.seqnr, seqnr[self]) = 0) {

                    \* ping requires pong as answer ->
                    \*  + register node
                    \*  + send pong

                    register_node_on(event.sender);
                    send_message(event.sender, MSG_PONG);


                } else if (event.seqnr = inc_seqnr(seqnr[self])) {
                    
                    \* the node initiated ping -> 
                    \*  + adapt the seqence number
                    \*  + reset node view
                    \*  + answer with pong

                    seqnr[self] := inc_seqnr(seqnr[self]);
                    reset_node_view(event.sender);
                    send_message(event.sender, MSG_PONG);


                } else {

                    \* ignore other messages
                    skip;
                }

            } else if (MSG_PONG = event.type) {

                \* check for sanity
                if (cmp_seqnr(event.seqnr, seqnr[self]) = 0) {

                    \* answer to last ping ->
                    \*  + register node
                    register_node_on(event.sender);

                } else if (event.seqnr = inc_seqnr(seqnr[self])) {
                    
                    \* the node has a new pong -> 
                    \*  + adapt the seqence number
                    \*  + reset node view
                    \*  + delay (restart) timeout for ping after the current
                    \*    one
                    \*  + wait for ping to send out pong

                    seqnr[self] := inc_seqnr(seqnr[self]);
                    reset_node_view(event.sender);
                    start_timeout(TO_PING, TO_PING_STARTUP_TIME);


                } else {

                    \* ignore other messages
                    skip;
                }

            } else if (TO_PING = event.type) {

                \* trigger new ping through timeout ->
                \*  + increment seuqence number
                \*  + reset node view
                \*  + send the next ping

                seqnr[self] := inc_seqnr(seqnr[self]);
                reset_node_view(NO_NODE);
                send_message(NO_NODE, MSG_PING);

            } else {

                \* unexpected event
                assert FALSE;
            }


        } else {

            \* unexpected state
            assert FALSE;
        }

    }
    
    \* initially all node are off 
    process (p \in NODE_SET) {
        off: skip;
    }
}
*)

-------------------------------------------------------------------------------
\* BEGIN TRANSLATION
\* END TRANSLATION
-------------------------------------------------------------------------------

\* value for init and reset
UNUSED_INIT_VALUE == "__unused_init_value"


\* resetting state of failing nodes to reduce state space
ResetInternalVariables(n) ==

        /\ state' = [state EXCEPT ![n] = UNUSED_INIT_VALUE]

        /\ view' = [view EXCEPT ![n] =
            [on \in NODE_SET |-> UNUSED_INIT_VALUE]]

        /\ seqnr' = [seqnr EXCEPT ![n] = 0]


\* initialize variables here
VarInit == 
            \* API
        /\ msg_to_send = NO_MESSAGE
        /\ timeout_request_add = NO_TIMEOUT
        /\ timeout_request_del = NO_TIMEOUT

            \* node state
        /\ state = [n \in NODE_SET |-> UNUSED_INIT_VALUE]
        /\ view = [n \in NODE_SET |-> [on \in NODE_SET |-> UNUSED_INIT_VALUE]]
        /\ seqnr = [n \in NODE_SET |-> 0]


================================================================================

