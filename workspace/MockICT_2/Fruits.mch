/* Fruits
* Author: Nethmi Mohotti
* Creation date: 1/8/2024
*/
MACHINE
    Fruits
SETS
    FRUITS = {Apples, Bananas, Lemons, Pineapples};
    OUTPUT = {Buying_fruit, Not_enough_budget}
CONSTANTS
    FruitPrice
PROPERTIES
    
    FruitPrice : FRUITS --> NAT &
    FruitPrice = {(Apples |-> 60),(Bananas |-> 100), (Lemons |-> 50), (Pineapples |-> 250)}
DEFINITIONS
    isMoneyAvailable(money,price) == {money > price}
VARIABLES
    budget
    //, price
INVARIANT
    budget : NAT 
    // & price : NAT
INITIALISATION
    budget := 300 
    //|| price := 0
OPERATIONS
    buying <-- buy(fruit) = 
    PRE
        fruit :FRUITS
    THEN
        //price := FruitPrice(fruit) ||
        IF 
            //isMoneyAvailable(budget,price)
            isMoneyAvailable(budget,FruitPrice(fruit))
        THEN
            //budget := budget - price ||
            budget := budget - FruitPrice(fruit) ||
            buying := Buying_fruit
        ELSE
            buying := Not_enough_budget
            
            
        END  
    END
END
