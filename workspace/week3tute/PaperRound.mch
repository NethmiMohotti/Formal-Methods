/* PaperRound
* Author: Nethmi Mohotti
* Creation date: 12/11/2023
*/
MACHINE
    PaperRound
VARIABLES 
    houseset
INVARIANT 
    houseset <: NAT1
INITIALISATION 
    houseset := {}
OPERATIONS
    add(new) =
    PRE new : NAT1 & new /: houseset
    THEN
        houseset := houseset \/ { new }
    END ;
    ans <-- number =
    BEGIN
        ans := card( houseset )
    END;
    
        
    END
    