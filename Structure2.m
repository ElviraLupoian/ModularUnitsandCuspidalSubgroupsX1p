// we investigate the structure of the cuspidal group in the followisng examples 

P := [ 43, 61,67,71, 79, 139,223, 229,283,367,439,467,499,587,607,643,727,809,823,947];

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

CS,pi := quo< T | rel >;
CSS, pii := sub<CS | [ pi(Z.i - Z.s) : i in [1..s] ]>;
g1  := [ Order(a) : a in Generators(CS) ];
g2 := [ Order(a) : a in Generators(CSS) ];
g1 := Sort(g1) ;
g2 := Sort(g2) ;
c1 := Order(pi(Z.1 -Z.2));
D1 := pi(Z.1 -Z.2);
n11 := c1/g2[1];
n11 := Integers() ! n11;
 D2 :=  pi(Z.1 - Z.s);
C1 := sub< CS | n11*D1>;
C2 := sub< CS | D2>;
C3 := sub< CS | n11*D1, D2>;
<p, C3 eq CSS, C1 meet C2>;
D3 := pi(Z.(s+1) - Z.(s+2));
D4 := pi(Z.1 -Z.(s+1));
n := Order(D4)/Order(D2);
n := Integers() ! n ;
C4 := sub< CS | n11*D1, n11*D3, n*D2 + n^2*D4, D4>;
C5 := sub< CS | n11*D1>;
C6 := sub< CS | n11*D3>;
C7 := sub< CS | n*D2 + n^2*D4>;
C8 := sub< CS | D4>;
<p, C4 eq CS, C5 meet C6, C5 meet C7, C5 meet C8, C6 meet C7, C6 meet C8, C7 meet C8>;
end for ;
