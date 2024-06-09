/* PostOffice
* Author: Nethmi Mohotti
* Creation date: 1/11/2024
*/
MACHINE
    PostOffice
    
SETS
    //Customer = {cust1, cust2, cust3} ;  
    Status = {waiting, removed_to_serve};
    OUTPUT = {cust_removed_to_serve , cust_not_in_the_queue}
CONSTANTS 
    Customer,
    MaxQueueLength    // Maximum length of the queue *)
    
PROPERTIES
    Customer <: NAT & Customer = 1..100 & // Set of customer IDs, assuming a maximum of 100 customers *)
    MaxQueueLength = 10
    
VARIABLES
    queue,  // Map from customer ID to status *)
    numberOfCustomers // Number of customers in the queue *)
    
INVARIANT
    
    queue : Customer --> Status & // Map from customer ID to status *)
    numberOfCustomers: NAT & numberOfCustomers <= MaxQueueLength  // The number of customers should not exceed the maximum *)
    
INITIALISATION
    queue := Customer*Status ||
    numberOfCustomers := 0 
    
    
OPERATIONS
    JoinPOQueue(customerID) =
    PRE
        numberOfCustomers < MaxQueueLength &
        (customerID /: dom(queue))  // Customer is not already in the queue *)
    THEN
        queue(customerID) := waiting ||
        queue := queue <+ {customerID|-> queue(customerID)}||
        numberOfCustomers := numberOfCustomers + 1
    END;
    
   
    
    served <-- GetServed(custId) = 
    PRE
        numberOfCustomers >0
    THEN
        IF (numberOfCustomers < MaxQueueLength & (custId /: dom(queue)) ) // Customer is not already in the queue *)
            THEN
                
                queue(custId) := removed_to_serve ||
                queue := queue <+ {custId|-> queue(custId)}||
                numberOfCustomers := numberOfCustomers - 1 ||
                served := cust_removed_to_serve
            ELSE
                served := cust_not_in_the_queue
                
            END
        END   
    END
    