The Sum To N Specification file
===============================

Here we provide a specification file containing two reachability rules - the main
proof rule and the circularity rule.

```{.k}
module ADD1-SPEC
    import ETHEREUM-SIMULATION

    rule
        <k>         .   </k>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
                <op>  #next ~> #execute => . </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callStack>.List</callStack>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST </program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack> .WordStack => 0 : (N *Int N +Int 1) /Int 2 : .WordStack </wordStack>
                    <localMem>.Map</localMem>
                    <pc>0 => 22</pc>
                    <gas>G => ?G:Int</gas>
                    <previousGas>0 => ?PG:Int</previousGas>
                </txExecState>
    requires (N >Int 0) andBool (N <Int (2 ^Int 128)) andBool (G >=Int (52 *Int N) +Int 29)
```
The Cirucularity Rule
---------------------


```{.k}
    rule
        <k>         .   </k>
        <exit-code> 1   </exit-code>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
                <op>  #execute => #end </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callStack>.List</callStack>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST </program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack> NP:Int : ( PSUM:Int : .WordStack ) => 0 : (PSUM +Int (NP *Int (NP +Int 1)) /Int 2) : .WordStack </wordStack>
                    <localMem>.Map</localMem>
                    <pc>4 => 22</pc>
                    <gas> GC:Int => ?GC </gas>
                    <previousGas> PG:Int => ?PG </previousGas>
                </txExecState>
    requires (NP >=Int 0) andBool (NP <Int (2 ^Int 128)) andBool N <Int (2 ^Int 128) andBool ((N *Int (N +Int 1) /Int 2) ==Int (PSUM +Int (NP *Int (NP +Int 1) /Int 2))) andBool (G >=Int (52 *Int N) +Int 29)
endmodule
```
