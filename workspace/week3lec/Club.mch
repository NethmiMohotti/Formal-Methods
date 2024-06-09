/* Club
* Author: Nethmi Mohotti
* Creation date: 12/11/2023
*/
MACHINE
    Club (NAME, capacity)
CONSTRAINTS
    capacity: NAT1 & 5<= capacity 
    & capacity <= card (NAME)
SETS
    MEMBERCHECK = { is_a_member, is_waiting, not_a_member}
CONSTANTS
    queuetotal
PROPERTIES
    queuetotal : NAT1 & queuetotal > 2
VARIABLES
    members, waiting
INVARIANT
    queuetotal < capacity &
    members <: NAME &
    waiting <: NAME &
    members /\ waiting = {} &
    card(members) <= capacity &
    card(waiting) <= queuetotal
INITIALISATION
    members := {} || waiting := {}
OPERATIONS
    join(newmember) = 
    PRE newmember : waiting & card(members)<capacity
    THEN
        members := members \/ {newmember}
    END;
    
    join_queue(newperson) =
    PRE newperson : NAME &
        newperson /: waiting & 
        newperson /: members & 
        card(waiting) < queuetotal
    THEN
        waiting := waiting \/ {newperson}
    END;
    
    
    remove(memberdel) =
    PRE memberdel : members 
    THEN 
        members := members - {memberdel}
    END;
    
    
    check <-- is_member(member) =
    PRE member : NAME
        THEN
        IF (member :members)
        THEN
            check := is_a_member
        ELSIF (member : waiting)
            THEN
            check := is_waiting
        ELSE
            check := not_a_member
        END
    END;
    
    semi_reset =
    BEGIN
        members, waiting := {}, members
    END
    
END

