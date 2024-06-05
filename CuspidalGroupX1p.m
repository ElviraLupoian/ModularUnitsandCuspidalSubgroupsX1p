// this code computes the cuspidal groups C1(p) of X1(p) for prime level p
//  input the primes in the list below 
// it outputs the list <p,C1(p)>, where p is  the prime and C1(p) the corresponding cuspidal group

P := [] ; // we set this to  PrimesInInterval(11,100) for the cuspidal groups computed in the thesis 

M := [] ;

GPR := [] ;
Kers := [] ;



for i in [1..#P] do ;
p := P[i] ;
s := [ a : a in [2..p-1] ] ;
t := [ [b^i : i in [0..p-2] ] : b in s] ; 
tt := [ [ a mod p : a in b] : b in t] ;
k := [ #Set(c) : c in tt];
ind := [ i : i in [1..#k] |  k[i] eq (p-1) ] ;
t := ind[1] ;
M[i] := s[t] ;
end for;



P := Eltseq(P) ;
n := #P ;

for i in [1..n] do;
p := P[i] ;
a := M[i] ;

b := p mod 12;
b := Integers() ! b;
bb := a^(2*(p-2));

s := (1/2)*(p-1) ;
s := Integers() ! s;


B2 := function(x) ;
t := x - Floor(x) ;
return t^2 -t +1/6;
end function; 

Ords1 := [] ;

for i in [0..s-2] do;
oo := [] ;
for j in [0..s-1] do ;
oo[j+1] := (p/2)*B2((a^(i+j))/p) - (p/2)*(a^(2*i +2))*B2((a^(s-1+j))/p) + (p/12)*(a^(2*i +2) -1) ;
end for;
for j in [0..s-1] do ;
oo[ s+ j+1] := (1/12)*(1 - a^(2*i +2)) + p*(a^(2*i +2) -1)*(p/2)*B2((a^(s-1 + j))/p);
end for;
Ords1[i+1] := oo ;
end for ;

o := [] ;
for j in [0..s-1] do ;
o[j+1] := (p/2)*p*B2((a^(s-1+j))/p) -b*p*(1/12);
end for ;

for j in [0..s-1] do ;
o[ s + j + 1] := p*(1/12) + (-b)*p*(p/2)*B2((a^(s-1+j))/p);
end for;

Ords1[s] := o;

Ords2 := [] ;

for i in [0..s-2] do;
oo := [] ;
for j in [0..s-1] do ;
oo[j+1] :=  (1/12) + (1/12)*(-a^(2*i +2) + p*b*(a^(2*i +2) -1));
end for;
for j in [0..s-1] do ;
oo[ s+ j+1] := (p/2)*B2((a^(i+j))/p) + (p/2)*(-a^(2*i+2) + p*b*(a^(2*i +2) -1))*B2((a^(s-1+j))/p);
end for;
Ords2[i+1] := oo ;
end for ;

o := [];


for j in [0..s-1] do ;
o[j+1] := p;
end for ;

for j in [0..s-1] do ;
o[ s + j + 1] := 6*(p^2)*B2((a^(s-1 +j))/p) ;
end for;

Ords2[s] := o;


Z := FreeAbelianGroup(p-1) ;
T := sub<Z| [ Z.i - Z.(p-1) : i in [1..p-2] ]>;

Ords1 := [ [ Integers() ! a : a in b ] : b in Ords1 ];
rel1 := [ &+[a[i]*Z.i : i in [1..p-1] ] : a in Ords1 ];

Ords2 := [ [ Integers() ! a : a in b ] : b in Ords2 ];
rel2 := [ &+[a[i]*Z.i : i in [1..p-1] ] : a in Ords2 ];
rel := rel1 cat rel2;

CS := quo< T | rel >;
<p, CS>;
end for ;


