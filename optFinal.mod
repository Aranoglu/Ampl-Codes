set recoveries;
set time;


param d {recoveries} >=0;    #The monthly increase in ROM sold to the facility when ith payback percentage (ri) is offered by the facility [ton]
param r {recoveries} >= 0;   #The ith payback percentage value
param rm ;                   #Minimum of all payback percentage values
param b {recoveries} >= 0;   #The initial amount of ROM sold to the facility when ith payback percentage (ri) is offered by the facility for the first time [ton]




param m ;    #Maximum capacity of the total monthly ROM production [ton]
param p ;     #Average gold price $/g
param s ;     #The reduction percentage in gold price when the miner sells their locally produced ROM directly 
param l ;     #The miner’s cost of extracting the ROM and locally processing it [$/ton]
param f ;     #The miner’s cost of extracting the ROM, selling and transporting it to the facility [$/ton]
param g {time} ;     #Fixed gold recovery percentage of ROM, if it is locally processed
param v ;        #Grade of gold in one ton of ROM [gram/ton]

    
var R {i in recoveries, 0..card(time)} binary ;           #1, if and only if the miner selects the ith payback percentage (ri) offered by the facility in month t, 0 otherwise



var Y {t in time} >= 0 , integer ;                        #Increase in the amount of ROM sold to the facility in month t [ton]

var X {t in time} >= 0 , integer ;                        #Decrease in the amount of ROM sold to the facility in month t  [ton]



var A { i in recoveries,t in 0..card(time)} >=0 ;         #The amount of gold that the facility loses if currently ri is offered as the payback percentage value, 
                                                          #and the miner decreases the amount of ROM sold to it in month t [gram]

var F {t in time} >=0  ;                                  #The amount of gold that the miner is paid back by the facility in month t [gram]


var Z {t in (time)} >=0,  binary;                  #1, if and only if the amount of ROM sold to the facility is increased in month t, 0 otherwise

var B {t in time} >=0, binary;                            #1, if and only if the amount of ROM sold to the facility is decreased in month t, 0 otherwise

var D {t in time}>=0 ;                                    # 1, if and only if the miner sells their ROM to the facility for the first time in month t, 0 otherwise

var K {t in 0..card(time)} >=0 ,  binary;                 #1, if and only if the amount of gold lost by the facility (due to a decrease made by the miner in the 
                                                          #amount of ROM sold to it) in month t is nonzero (i.e., Ait ̸ = 0), 0 otherwise



maximize Profit : 
    ( ( sum { t in time} p  * F[t] ) - (sum { t in time} f * (sum {j in 1 .. t} Y[j] -sum {q in 1 .. t} X[q]  )) - (sum{i in recoveries, t in time} A[i,t]  * p)
     + s * p * v * (sum{t in time} g[t]* (m-(sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q]))) - l * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q])))); 
 

subject to Constraint3 {i in recoveries, t in time}: Y[t] <= b[i] * D[t] + d[i] * Z[t] + m * (1- R[i,t]);
subject to Constraint4 {i in recoveries, t in time}: Y[t] >= b[i] * D[t] + d[i] * Z[t]  - (m + b[i] + d[i]) * (1-R[i,t]);



subject to Constraint5 {t in time}                 : Y[t] <= m * Z[t];



subject to Constraint6 {t in time}: sum {i in recoveries} R[i,t] = 1;
subject to Constraint7 {i in recoveries} : R[i,0] = 0;


subject to Constraint8 {i in recoveries, t in time}: R[i,t] <= R[i,t-1] + Z[t];
subject to Constraint9 {i in recoveries, t in time}: R[i,t] >= R[i,t-1] - Z[t];

subject to Constraint101 {t in time}                 : D[t] <= Z[t];
subject to Constraint102 {t in time}                 : D[t] >=  (2 * Z[t] - sum {k in 1 .. t} Z[k]);
subject to Constraint11 : sum{t in time} D[t] <= 1;

subject to Constraint121 {t in time}                 :  m * B[t]   >= X[t]   ;
subject to Constraint122 {t in time}:   B[t] <= X[t];

subject to Constraint13 {t in time}                 :  B[t] + Z[t] <= 1;
subject to Constraint141 {t in time}                 : sum {j in 1 .. t} Y[j] >=  sum {q in 1 .. t} X[q]; 
subject to Constraint142 {t in time}                 : sum {j in 1 .. t} Y[j] -sum {q in 1 .. t} X[q] <= m;

subject to Constraint151 {t in time}: K[t] * rm * v <= sum{i in recoveries} A[i,t];
subject to Constraint152 {t in time}: sum{i in recoveries} A[i,t] <= v * m *  K[t] ;

subject to Constraint16 : K[0] = 0;
subject to Constraint17 {i in recoveries}: A[i,0] = 0;

subject to Constraint18 {i in recoveries, t in time}:  A[i,t] <= v * (m)  * (R[i,t]);

subject to Constraint19 {i in recoveries, t in time}: A[i,t] <= A[i,t-1]+ X[t] * v * (1-r[i]) + v * m*(1 - R[i,t])+ v * m * (1- B[t]) ;
subject to Constraint20 {i in recoveries, t in time}: A[i,t] >= A[i,t-1]+ X[t] * v * (1-r[i]) - v * m*(1 - R[i,t])- v * m * (1- B[t]) ;

subject to Constraint21 {i in recoveries, t in time}: A[i,t] <= A[i,t-1]- Y[t] * v * (0.1-r[i]) + v * m*(1 - R[i,t])+ v * m * (2- Z[t] - K[t-1]) ;
subject to Constraint22 {i in recoveries, t in time}: A[i,t] >= A[i,t-1]- Y[t] * v * (0.1-r[i]) - v * m*(1 - R[i,t])- v * m * (2- Z[t] - K[t-1]) ;

subject to Constraint23 {i in recoveries, t in time}: A[i,t] <= A[i,t-1] + v * m * ( B[t] + Z[t] );
subject to Constraint24 {i in recoveries, t in time}: A[i,t] >= A[i,t-1] - v * m * ( B[t] + Z[t] );

subject to Constraint25 {i in recoveries,t in time}: F[t] <= ( sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q]) *  r[i] * v  + v * m * (1 - R[i,t]) ;
subject to Constraint26 {i in recoveries,t in time}: F[t] >= ( sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q]) *  r[i] * v  - v * m * (1 - R[i,t]) ;



subject to Constraint31 {i in recoveries}: A[i,1] = 0;
subject to Constraint32 : X[1] = 0;
subject to Constraint34 : B[1] = 0;

subject to Constraint50 :( ( sum { t in time} p  * F[t] ) - (sum { t in time} f * (sum {j in 1 .. t} Y[j] -sum {q in 1 .. t} X[q]  )) - (sum{i in recoveries, t in time} A[i,t]  * p)
     + s * p  * (sum{t in time} g[t]* (m-(sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q]))) - l * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] - sum {q in 1 .. t} X[q]))))<= card(time) *r[card(recoveries)] * m * p ; 





      
 