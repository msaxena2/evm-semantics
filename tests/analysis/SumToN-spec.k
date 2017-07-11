module ADD1-SPEC
    import ETHEREUM-SIMULATION

rule 
<k>  
.
</k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op>  #execute => #execute</op>
<memoryUsed> 0   </memoryUsed>
 <callStack> .List => .List </callStack>
<localMem> .Map</localMem>
<gas> N =>N1 </gas>
<previousGas> 0 => N1+Int 20000 </previousGas>
<pc> 0 => 26 </pc>
 <id> ACCT </id>
 <accounts>
<account>
<acctID> ACCT </acctID>
<storage> .Map=> (0|->(I*Int (I +Int 1)/Int 2))</storage>
...
</account>
</accounts>
<wordStack> .WordStack => .WordStack </wordStack>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ; 
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ; 
PUSH(1, 0) ; SSTORE ; .OpCodes
)</program>
requires N>=Int (52*Int I) +Int 20032 andBool I>=Int 1  
ensures N-Int N1==Int (52*Int I )+Int 20032


//loop invariant
rule
<k> . </k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op> #execute=> #execute</op>
<memoryUsed> 0  </memoryUsed>
<callStack> .List => .List </callStack>
<localMem>.Map</localMem>
<gas> N =>N1 </gas>
<previousGas> N +Int 8 => N1+Int 20000 </previousGas>
<pc> 4=>26</pc>
 <id> ACCT </id>
 <accounts>
<account>
<acctID> ACCT </acctID>
<storage> .Map=> (0|->(I2 +Int (I1 *Int (I1 +Int 1)/Int 2)))</storage>
...
</account>
</accounts>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ; 
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ; 
PUSH(1, 0) ; SSTORE ; .OpCodes)</program>
<wordStack> I1:Int : I2:Int : .WordStack =>.WordStack </wordStack>

requires N>=Int (52*Int I1) +Int 20026 andBool I1>=Int 0  andBool I1<=Int I andBool I2>=Int 0
ensures N-Int N1==Int (52*Int I1 )+Int 20026

endmodule
