// The Sum To N Specification file
// ===============================

// Here we provide a specification file containing two reachability rules - the
// main proof rule and the circularity rule.


module ADD1-SPEC
    import ETHEREUM-SIMULATION
rule
<k>
.
</k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op>  #execute => ?OP:K</op>
<memoryUsed> 0   </memoryUsed>
 <callStack> .List => .List </callStack>
<localMem> .Map </localMem>
<gas> G =>G1 </gas>
<previousGas> 0 => G1+Int 2 </previousGas>
<pc> 0 => 23 </pc>
 <id> ACCT </id>
  <network>
<activeAccounts>   SetItem (ACCT)   </activeAccounts>
 <accounts>
<account>
<acctID> ACCT </acctID>
<storage> .Map</storage>
<balance> 0:Word </balance>
<code>    .Map   </code>
<acctMap> M:Map   </acctMap>
</account>
</accounts>
<messages> .Bag </messages>
</network>
<wordStack> .WordStack => (I *Int (I +Int 1)/Int 2) : .WordStack </wordStack>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ; .OpCodes
)</program>
requires G>=Int (52*Int I) +Int 29 andBool I>=Int 1  
ensures G-Int G1==Int (52*Int I )+Int 29
//loop invariant
rule
<k> .K </k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op>  #execute=> ?OP:K</op>
<memoryUsed> 0  </memoryUsed>
<callStack> .List => .List </callStack>
<localMem>.Map</localMem>
<gas> G =>G1 </gas>
<previousGas> _ => G1+Int 2 </previousGas>
<pc> 4=>23</pc>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ;
 .OpCodes)</program>
<wordStack> N : S : .WordStack =>(S +Int (N *Int (N +Int 1)/Int 2)) : .WordStack </wordStack>
requires G>=Int (52*Int N) +Int 23 andBool N>=Int 0 andBool N<=Int I andBool S>=Int 0 andBool N<Int 2^Int 32 andBool N +Int S <Int 2^Int 256
ensures G-Int G1==Int (52*Int N )+Int 23 
endmodule

