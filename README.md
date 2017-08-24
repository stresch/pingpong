TLA+ Pingpong Example
=====================

Nodes use timeouts, ping and pong messages to determine whether the other nodes
are on or off. 

Each node initially starts a timeout with a long duration and listens for ping
messages. If the timeout expires the node itself sends out a ping message with
a sequence number, otherwise it answers to a received ping message with a pong
message having the same sequence number. Afterwards it periodically restarts
the timeout and sends ping messages with incrementing sequence numbers after
reception of the timeout or a pong message with the next sequence number. A
node sees the other nodes as on if it received a ping or pong message with the
same sequence number it currently expects. Note, that this is algorithm is
solely intended to showcase the framework.

All but one node can fail in the example.


Files
-----

+ README.md

    this file

+ generic.cfg

    the generic config for the modelchecker - defines which system
    definition, invariants and properties are used for model checking

+ pingpong.tla

    the pingpong state machine of the nodes in PlusCal

+ pingpong_cfg.tla

    the configuration values in TLA+

+ pingpong_env.tla

    the environment in TLA+

+ pingpong_prop.tla

    the property definitions for modelchecking

+ pingpong_trace.tla

    properties to get traces

+ scn_1_node.tla

    the model checking scenario for one node

+ scn_2_nodes.tla

    the model checking scenario for two nodes

+ scn_3_nodes.tla

    the model checking scenario for three nodes

+ seqnr.tla

    definitions for sequence numbers


Translating and Modelchecking
-----------------------------

1. Prerequisite

  1.1. Installed Java VM

  1.2. Installed TLA+ tools at $BASE_INSTALL_DIR/tla

    ```
    BASE_INSTALL_DIR=<install_path>

    cd $BASE_INSTALL_DIR  
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.5.3/tla.zip  
    unzip tla.zip
    ```

2. Translate PlusCal Code to TLA+

    ```
    java -cp $BASE_INSTALL_DIR/tla pcal.trans -nocfg pingpong.tla
    ```


3. Execute TLC for scenarios

    ```
    java -cp $BASE_INSTALL_DIR/tla tlc2.TLC -config generic.cfg scn_1_node.tla  
    java -cp $BASE_INSTALL_DIR/tla tlc2.TLC -config generic.cfg scn_2_nodes.tla  
    java -cp $BASE_INSTALL_DIR/tla tlc2.TLC -config generic.cfg scn_3_nodes.tla
    ```

Get an Example Trace
--------------------

1. Uncomment a trace property, e.g. TraceAllNodesAreOnAndSeeAllAsOn, in
   generic.cfg:
    
    ```
    [...]
    \* Traces:
    \* Uncomment the corresponding trace property and run tlc to obtain a trace

    TraceAllNodesAreOnAndSeeAllAsOn
    \* TraceOneNodeIsOnAndOthersAreOffAndItSeesThemAsOff
    [...]
    ```    

2. Run TLC

    ```
    java -cp $BASE_INSTALL_DIR/tla tlc2.TLC -config generic.cfg scn_2_nodes.tla  
    ```    

