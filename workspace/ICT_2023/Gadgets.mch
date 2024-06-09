/* Gadgets
 * Author: Nethmi Mohotti
 * Creation date: 11/21/2023
 */
MACHINE
    Gadgets
SETS
    GADGETS = {Clunky, Dodgy, Questionable};
    PARTS = {Cog, Lever, Hinge}
    
CONSTANTS
    Required
PROPERTIES
    Required : GADGETS <-> PARTS & 
    Required = { Clunky|-> Cog, Clunky|->Hinge,Dodgy|->Cog, Dodgy|-> Lever, Questionable|-> Hinge, Questionable|-> Lever}
    
VARIABLES
    supply

INVARIANT
    supply: PARTS -->NAT

INITIALISATION
    supply := {Cog |-> 5, Lever |-> 5, Hinge |-> 5}

/*OPERATIONS
    create(gg) = 
    PRE 
        gg:GADGETS & !(pp).(pp: Required[{gg}]=> supply(gg)>0)
    THEN
        supply := supply <+ {(gg |-> supply(gg)-1) || gg: Required[{gg}]}
    END*/
END
