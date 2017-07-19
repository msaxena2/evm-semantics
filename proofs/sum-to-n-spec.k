// The Sum To N Specification file
// ===============================

// Here we provide a specification file containing two reachability rules - the
// main proof rule and the circularity rule.


module ADD1-SPEC
    import ETHEREUM-SIMULATION

    rule
        <k>         .   </k>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
                <op> #execute </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callStack>.List</callStack>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST </program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack> .WordStack => 0 : (N *Int (N +Int 1)) /Int 2 : .WordStack </wordStack>
                    <localMem>.Map</localMem>
                    <pc>4 => 22</pc>
                    <gas>G => G2:Int</gas>
                    <previousGas>PG => PG2:Int</previousGas>
                </txExecState>
    requires (N >Int 0) andBool (N <Int (2 ^Int 128)) andBool (G >Int (52 *Int N) +Int 300) andBool G <Int (2 ^Int 256)


// The Cirucularity Rule
// ---------------------


    rule
        <k>         .   </k>
        <mode>      NORMAL </mode>
        <schedule>  DEFAULT </schedule>
        <analysis>  .Map </analysis>
                <op>  #execute </op>
                <output>.WordStack</output>
                <memoryUsed>0</memoryUsed>
                <callStack>.List</callStack>
                <txExecState>
                    <program>0 |-> PUSH ( 1 , 0 ) 2 |-> PUSH ( 1 , N:Int ) 4 |-> JUMPDEST 5 |-> DUP ( 1 ) 6 |-> ISZERO 7 |-> PUSH ( 1 , 21 ) 9 |-> JUMPI 10 |-> DUP ( 1 ) 11 |-> SWAP ( 2 ) 12 |-> ADD 13 |-> SWAP ( 1 ) 14 |-> PUSH ( 1 , 1 ) 16 |-> SWAP ( 1 ) 17 |-> SUB 18 |-> PUSH ( 1 , 4 ) 20 |-> JUMP 21 |-> JUMPDEST </program>
                    <id>87579061662017136990230301793909925042452127430</id>
                    <caller>428365927726247537526132020791190998556166378203</caller>
                    <callData>0 : .WordStack</callData>
                    <callValue>0</callValue>
                    <wordStack> NP:Int : ( PSUM:Int : .WordStack ) => 0 : (N *Int (N +Int 1)) /Int 2 : .WordStack </wordStack>
                    <localMem>.Map</localMem>
                    <pc>4 => 22</pc>
                    <gas> GC:Int => GC2:Int </gas>
                    <previousGas> PG:Int => PG2:Int </previousGas>
                </txExecState>
    requires (NP >=Int 0) andBool (NP <=Int N) andBool N <Int (2 ^Int 128) andBool ((N *Int (N +Int 1) /Int 2) ==Int (PSUM +Int (NP *Int (NP +Int 1) /Int 2))) andBool ((PSUM +Int NP) <Int 2^Int 256) andBool (GC >Int (52 *Int NP) +Int 294) andBool PG >Int GC andBool ((NP) <Int (2 ^Int 128)) andBool ((PSUM +Int NP) >=Int 0)
endmodule

