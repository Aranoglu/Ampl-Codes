set recoveries;
set time;


param d {recoveries} >=0;    #incriment per month
param r {recoveries} >= 0;   #provided recovery from facility

param b {recoveries} >= 0;   #Initial base ore sold to facility

param h{recoveries};



param m ;    #maximum Total daily production ton/day
param p ;     #Average gold price $/g
param s ;     #selling reduction percentage for nonreported production 
param l ;     #Production cost locally (details in my notes)
param f ;     #Production cost with facility (details in my notes)
param g ;     #fixed recovered gold per ton for local processing

param e ;
param coef;

param Yo {time};
#param Go {time,recoveries};
param Ro {time,recoveries} ;
param Ao {t in 0..card(time),recoveries};
param Qo {time,recoveries} ;
param Zo {t in 0..card(time)};
param Xo {time};
param Fo {t in 0..card(time)};
param Bo {time};
param Do {time};
    
var R {i in recoveries, t in time} binary , := Ro[t,i];     #which recovery percentag to be given

#var Q {i in recoveries, t in time} binary , := Qo[t,i] ;

var Y {t in time} >= 0 , integer, := Yo[t] ;                 #The increase in ore amount that is sold to facility at time t

var X {t in time} <= 0, integer , := Xo[t] ;

#var G { i in recoveries,t in time} >=0 , := Go[t,i]  ;           #for linearization of Z*r

var A { i in recoveries,t in 0..card(time)} <=0, :=Ao[t,i] ;

var F {t in 0..card(time)} >=0 , := Fo[t] ;
#var L {time} >=0;                   #the local production that remainse until time t before is is totally gone to facility

var Z {t in 0..card(time)} >=0, := Zo[t] ;                  #the production that is sent monthly to the facility 

var B {t in time} binary, := Bo[t];

var D {t in time}>=0 , := Do[t] ;

maximize Profit : 
   coef* ( ( sum { t in time} p  * F[t] ) - (sum { t in time} f * (sum {j in 1 .. t} Y[j] +sum {q in 1 .. t} X[q]  )) - (-sum{i in recoveries, t in time} A[i,t]  * p)
     + e * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]))) - l * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q])))); 
 

subject to Constraint1 {i in recoveries, t in time}: Y[t] <= h[i] + (m - h[i]) * (1-R[i,t])+ (m-h[i]) * (1 - D[t]);
subject to Constraint2 {i in recoveries, t in time}: Y[t] >= h[i] - h[i] * (1- R[i,t]) - h[i] * (1 - D[t]);

subject to Constraint25 {i in recoveries, t in time}: Y[t] <= d[i] + (m - d[i]) * (1-R[i,t])+ (m-d[i]) * (D[t]);
subject to Constraint26 {i in recoveries, t in time}: Y[t] >= d[i] - d[i] * (1- R[i,t]) -d[i] * ( D[t]);

subject to Constraint3 {t in time}                 : Y[t] <= m * Z[t];

subject to Constraint4 {t in time}: sum {i in recoveries} R[i,t] = Z[t];

subject to Constraint5 {t in time}: sum {i in recoveries} R[i,t] <= 1;

#subject to Constraint5 {i in recoveries, t in time}: X[t] >= - d[i] - (m - d[i]) * (1-Q[i,t]);
#subject to Constraint6 {i in recoveries, t in time}: X[t] <= - d[i] + d[i] * (1- Q[i,t]);
subject to Constraint7 {t in time}                 : X[t] >= - m * B[t];

subject to Constraint8 {t in time}:   B[t] <=sum {i in recoveries} R[i,t];
#subject to Constraint50 {t in time}                 :  B[t] <= 1;
#subject to Constraint9 {t in time}                 :  B[t] + Z[t] <= 2;
subject to Constraint10 {t in time}                 : sum {j in 1 .. t} Y[j] >= - sum {q in 1 .. t} X[q]; 
subject to Constraint11 {t in time}                 : sum {j in 1 .. t} Y[j] +sum {q in 1 .. t} X[q] <= m;

#subject to Constraint12 { t in time}:  F[t] <= (m) * (sum {i in recoveries} R[i,t]);
#subject to Constraint13 {i in recoveries, t in time}: G[i,t] <= sum {j in 1 .. t} Y[j] * r[i];
#subject to Constraint14 {i in recoveries, t in time}: G[i,t] >= sum {j in 1 .. t} Y[j] * r[i] - m*(1 - R[i,t]); 

subject to Constraint15 {i in recoveries, t in time}:  A[i,t] >= (-m)  * (R[i,t]);
subject to Constraint16 {i in recoveries, t in time}: A[i,t] >=  X[t] * (0.1-r[i]) ;
subject to Constraint17 {i in recoveries, t in time}: A[i,t] <=  X[t] * (0.1-r[i])  + m*(1 - R[i,t]); 

subject to Constraint44 {i in recoveries, t in time}: A[i,t] <= A[i,t-1] + m * (Z[t]  );
subject to Constraint45 {i in recoveries, t in time}: A[i,t] >= A[i,t-1] - m * (Z[t] );
subject to Constraint46 {i in recoveries}: A[i,0] = 0;

subject to Constraint18 : F[0] = 0;
subject to Constraint19 {i in recoveries,t in time}: F[t] <= ( sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]) *  r[i]  + m * (1 - R[i,t]);
subject to Constraint20 {i in recoveries,t in time}: F[t] >= ( sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]) *  r[i]  - m * (1 - R[i,t]);

subject to Constraint21 {t in time}: F[t] <= F[t-1] + m * (Z[t]+ B[t] );
subject to Constraint22 {t in time}: F[t] >= F[t-1] - m * (Z[t]+ B[t] );

#subject to Constraint23 {i in recoveries,t in time}: F[t] <= (sum {q in 1 .. t} X[q] + sum {j in 1 .. t} Y[j]) * r[i]  + m * (1 - Q[i,t]);
#subject to Constraint24 {i in recoveries,t in time}: F[t] >= (sum {q in 1 .. t} X[q] + sum {j in 1 .. t} Y[j]) * r[i]  - m * (1 - Q[i,t]);

subject to Constraint28 : Z[0] = 0;
subject to Constraint35 {t in time}                 : D[t] <= Z[t];
subject to Constraint27 {t in time}                 : D[t] >=  (2 * Z[t] - sum {k in 1 .. t} Z[k]);
#subject to Constraint29 {t in time}                 : D[t] <=  (sum {k in 1 .. t} Z[k] - sum {k in 1 .. (t-1)} Z[k]);
subject to Constraint30 : sum{t in time} D[t] <= 1;


subject to Constraint31 {i in recoveries}: A[i,1] = 0;
subject to Constraint32 : X[1] = 0;
#subject to Constraint33 {i in recoveries}: Q[i,1] = 0;
subject to Constraint34 : B[1] = 0;
subject to Constraint40 :( sum { t in time} p  * F[t] ) - (sum { t in time} f * (sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q] )) - (-sum{i in recoveries, t in time} A[i,t]  * p)
   + e * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]))) - l * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]))) <= card(time) * r[card(recoveries)] * m * p ; 

#subject to Constraint42 {i in recoveries, t in 2..card(time)}: Q[i,t] * r[i] <= Q[i,t-1] * r[i] + R[i,t-1] * r[i];

#subject to Constraint43 {i in recoveries, t in 2..card(time)}: Q[i,t] * r[i] <= Q[i,t-1] * r[i] + R[i,t-1] * r[i];
     
#subject to Constraint41 :( sum { t in time} p  * F[t] ) - (sum { t in time} f * (sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q] )) 
#     + e * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]))) - l * (sum{t in time} (m-(sum {j in 1 .. t} Y[j] + sum {q in 1 .. t} X[q]))) <= ( (r[card(recoveries)] *   (sum {t in time ,j in 1 .. t} Y[j] + sum {t in time, q in 1 .. t} X[q] ) * p)
 #     +( e *  (m-(sum {t in time, j in 1 .. t} Y[j] + sum {t in time ,q in 1 .. t} X[q]))));
      
 