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

--------------------------- MODULE pingpong_prop -----------------------------
EXTENDS pingpong_env, Naturals

\* helper definitions for node states
NodeIsOn(n) ==
     pc[n] \notin INACTIVE_NODE_STATES

NodeIsOff(n) ==
    pc[n] = NODE_OFF

NodeIsFailed(n) ==
    pc[n] = NODE_FAILED

NodeIsReady(n) ==
    pc[n] = NODE_READY

\* invariant: no off node is seen as on
InvOffNodesNeverSeenAsOn ==
    \A n \in NODE_SET: \A o \in NODE_SET:
        NodeIsOff(n) => view[o][n] /= ON

\* invariant: an initialized node sees itself always as on
InvOnNodeSeesItselfAsOn ==
    \A n \in NODE_SET:
        NodeIsOn(n) /\ pc[n] /= NODE_PROCEDURE_INIT_ADDRESS
            => view[n][n] = ON

\* invariant: timeouts are registered for nodes that have been initialized
InvOnNodesHaveTimeoutRegistered ==
    \A n \in NODE_SET:
        NodeIsReady(n) =>
            \E t \in TIMEOUT_DURATIONS:
                timeouts[n][t].type = TO_PING

\* property: if node is ON, it eventually sees other nodes that are on as ON
\* and those that are off or failed as OFF
PropOnNodeEventuallyGetsCorrectViewOfSystem ==
    [] (
        \A n \in NODE_SET: NodeIsOn(n) =>
            <> (
                \/ \A o \in NODE_SET:

                    /\ NodeIsOn(o) => view[n][o] = ON

                    /\ NodeIsOff(o) => view[n][o] = OFF

                    /\ NodeIsFailed(o) => view[n][o] = OFF

                \/ NodeIsFailed(n)
            )
    )

==============================================================================

