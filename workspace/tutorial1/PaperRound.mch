/* PaperRound
* Author: Nethmi Mohotti
* Creation date: 10/4/2023
*/
MACHINE
    PaperRound
SETS
    ANSWERS = {delivered,notDelivered};
    ANSWERS2 = {deliveredTo,notDeliveredTo}; 
    OUTPUT = {magazine_Delivered, magazine_not_delivered};
    OUTCOME = { NoMoreDeliveries, NotDeliveredTo,NotDeliveringPaperAndMagazine};
    STATUS = { PaperAndMagazine, OnlyPaper, OnlyMagazine, NoDeliveries, NotBothPaperAndMagazine }
    //OUTCOME = {YES,NO}
    
    //3.7 set a constant and a limit to the constant  
CONSTANTS
    max_deliveries
PROPERTIES
    max_deliveries : NAT1 & max_deliveries = 10
    
    
VARIABLES
    houseset,
    magazine //new variable
    
INVARIANT
    houseset <: NAT1 &
    magazine <: NAT1 &//type of the new variable
    magazine <: houseset &
    card(houseset) <= max_deliveries  //3.7 limit the number of deliveries to 10
    
INITIALISATION
    //houseset, magazine := {}, {}
    houseset := {} ||
    magazine := {} //initial value of the new variable
    //ASSERTIONS
    //(houseset/={}) =>(3:houseset);
    //not(houseset={})
    
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
    
    //add New Houses
    ans <-- getsPapers(houseNumber) =
    PRE houseNumber : NAT1 & houseNumber:houseset
    THEN
        ans := card({ houseNumber } /\ houseset)
    END;
    
    //remove the house that gets delivered papers
    removed <-- cancelPapers(houseNumber) =
    PRE houseNumber : NAT1 & houseNumber:houseset
    THEN
        removed := houseset - {houseNumber}
    END;
    
    //get the fist house paper delivers    
    firstHouse <-- getFirstHouse= 
    IF (houseset /= {})
    THEN
        firstHouse := min(houseset)
    END;
    
    //get the last house paper delivers
    lastHouse <-- getLastHouse = 
    IF (houseset /= {})
    THEN
        lastHouse := max(houseset)
        
    END;
    
    //get the house that has paper
    paper <-- hasPaper(houseNumber)= 
    PRE houseNumber : NAT1 
    THEN
        IF (houseNumber:houseset)
        THEN
            paper := 1 //paper:=YES
        ELSE
            paper :=0 //paper :=NO
        END
    END;
    
    //stop delivery
    deliveredNum <-- stopDelivery(houseNumber)= 
    PRE houseNumber : NAT1
    THEN
        IF (houseNumber:houseset) 
        THEN
            houseset := houseset - {houseNumber}
            || deliveredNum := delivered
        ELSE
            deliveredNum := notDelivered        
        END
    END;
    
    ///////////////////////////******************************/////////////////////    
    //    addition(new) =
    //    PRE new : NAT1 & new /: deliveredset
    //    THEN
    //        deliveredset := deliveredset \/ { new }
    //    END ;
    //    
    //    ans <-- numMag =
    //    BEGIN
    //        ans := card( deliveredset )
    //    END;
    
    //adding houses to the deliverset
    //addMagazine <-- deliverMagazine(houseNumber) =
    deliverMagazine(houseNumber) =
    PRE houseNumber : NAT1 & houseNumber:houseset & houseNumber/:magazine
    THEN
        magazine := magazine \/ {houseNumber}
        //addMagazine := card({ houseNumber } /\ magazine) 
    END;
    
    
    //remove the delivered houses from houseset
    magazineDelivered <-- stopMagazine(houseNumber)= 
    PRE houseNumber : NAT1
    THEN
        IF (houseNumber:houseset) 
        THEN
            houseset := houseset - {houseNumber}
            || magazineDelivered := deliveredTo
        ELSE
            magazineDelivered := notDeliveredTo        
        END
    END;
    
    
    //output a delivery massage to the magazine delivered 
    deliverMag <-- deliveries(houseNumber)=
    PRE deliverMag: OUTPUT & houseNumber : NAT1 
    THEN
        IF ((houseNumber:houseset)&(houseNumber:magazine))
        THEN
            deliverMag := magazine_Delivered
            
        ELSE 
            deliverMag := magazine_not_delivered
        END
    END;
    
    //take a house number and remove it from the set  
    outcome <-- stopalldeliverys( houseNumber ) = 
    PRE
        outcome : OUTCOME  &  houseNumber : NAT1
    THEN
        IF ( ( houseNumber : houseset ) & ( houseNumber : magazine) )
        THEN
            houseset := houseset - { houseNumber }
            ||
            magazine := magazine - { houseNumber }
            ||
            outcome := NoMoreDeliveries 
        ELSE
            outcome := NotDeliveringPaperAndMagazine  
        END
    END;
    
    
    ///////////***************//////////////////
    //Exercise 3.5
    statusoutput <-- status(houseNumber)=
    PRE statusoutput: STATUS & houseNumber : NAT1 
    THEN
        IF ((houseNumber:houseset)&(houseNumber:magazine))
        THEN
            statusoutput := PaperAndMagazine
        ELSIF (houseNumber : houseset)
        THEN 
            statusoutput := OnlyPaper
        ELSIF (houseNumber:magazine)
        THEN 
            statusoutput := OnlyMagazine
            
        ELSE 
            statusoutput := NoDeliveries
        END
    END;
    
    
    //3.7 operation to output how many more deliveries could be made for a house
    remaining_Deliveries <-- howManyMore =
    BEGIN
        remaining_Deliveries :=   max_deliveries - card( houseset ) 
    END
    
    
END

IF
                THEN
                END