/* logic_lecture
* Author: Nethmi Mohotti
* Creation date: 11/8/2023
*/
MACHINE
    logic_lecture
    
SETS
    ANSWER = {yes,no}
CONSTANTS
    AA,BB
PROPERTIES
    //AA = {0,1,2} & BB = {0,2,4}
    AA <: NAT & AA = 0..2 
    &
    BB <: NAT & BB = {0,2,4}

DEFINITIONS
    squares(limit) == ({xx|xx:NAT & (#(yy).((yy:1..limit) & xx=yy*yy))});
    
    primes(lim) == ({xx|xx:NAT & (!(yy).((yy:2..(xx/2)) & xx mod yy =0))});
    even( nn )  == ( ( nn mod 2 ) = 0 ) ;
    
    odd( nn )   == ( ( nn mod 2 ) = 1 ) ;    
    smallPrime( nn )        == ( nn : {2, 3, 5, 7 } ) ;   
    ascending( xx, yy, zz ) == ( (xx <= yy)  &  (yy <= zz) )
    //ascending( xx, yy, zz ) == (   (xx : NAT & yy : NAT & zz : NAT) 
    //                                   & (xx <= yy)  &  (yy <= zz) )

ASSERTIONS
    !(xx).(xx:AA => xx <= 2);
    !(yy).(yy:BB => yy <= 3);
    #(xx).( xx : AA & xx = 2 );
    #(yy).((yy:BB)& yy=3);
    !(nn).(nn:NAT => (nn=0 or nn>0));
    not(#(yy).(yy:NAT & yy <0))
    
    
OPERATIONS
    
    ans <-- ascending_val( xx, yy, zz ) =
    PRE
        ans : ANSWER
        &
        xx : NAT & yy : NAT & zz : NAT
        & 
        ascending(xx, yy, zz)
    THEN 
        ans := yes
    END;
    
    // Exercise 4.8
    
    truthValue <-- isAscending( xx, yy, zz ) =
    PRE
        truthValue : BOOL  &      
        xx : NAT & yy : NAT & zz : NAT 
    THEN 
        truthValue := bool( ascending( xx, yy, zz ) )
    END;
    
    truthValue <-- isEven( xx ) =
    PRE
        truthValue : BOOL  & xx : NAT       
    THEN 
        truthValue := bool( even( xx ) )
    END;
    
    truthValue <-- isOdd( xx ) =
    PRE
        truthValue : BOOL  & xx : NAT       
    THEN 
        truthValue := bool( odd( xx ) )
    END           
    
END
