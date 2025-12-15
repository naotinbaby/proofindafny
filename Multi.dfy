type ISeq = nat->int
function power2 (n:int):real
ensures power2(n)>0.0
{
    if n<=0 then 1.0 else 2.0*power2(n-1)
} 
function power (n:nat):nat
ensures power(n)>0
{
     if n==0 then 1 else 2*power(n-1)
}
function set_z(n:int,p:nat):int{
    power(p)*n
}



lemma circle(p: int, q: nat, n: int)
    requires q > 0
    requires n == ((p as real / q as real)+0.5).Floor
    ensures (n as real - 0.5) * q as real <= p as real < (n as real + 0.5) * q as real
// \left(n - \frac{1}{2}\right) \cdot q \le p < \left(n + \frac{1}{2}\right) \cdot q
{
    circle'(p as real, q as real, n);
}

lemma frac(a: real, b: real, c: real)
    requires b > 0.0
    requires a/b < c
    ensures (a/b)*b < c*b
// b > 0 \land \frac{a}{b} < c \Rightarrow \frac{a}{b}\cdot b < c \cdot b
{}

lemma circle'(p: real, q: real, n: int)
    requires q > 0.0
    requires n == ((p / q)+0.5).Floor
    ensures (n as real - 0.5) * q <= p < (n as real + 0.5) * q
// \left(n - \frac{1}{2}\right) \cdot q \le p < \left(n + \frac{1}{2}\right) \cdot q
{
    assert (p/q) - 0.5 < n as real <= (p/q) + 0.5;
    assert n as real <= (p/q) + 0.5;
    assert (p/q) - 0.5 < n as real;
    assert n as real - 0.5 <= p/q;
    assert p/q < n as real + 0.5;
    assert (n as real - 0.5) * q <= p; // I don't know why but this line is also needed.
    assert (p/q)*q <= p;
    frac(p, q, n as real + 0.5); // This is needed!
    assert (p/q)*q < (n as real + 0.5)*q;
    assert p < (n as real + 0.5) * q;
}
ghost predicate DArrow(v: real, n: ISeq)
{
    forall p: nat :: (n(p) - 1) as real / power2(p) as real < v < (n(p) + 1) as real / power2(p) as real
}

function mul_a(x1:ISeq,x2:ISeq,z1:nat,z2:nat,m:nat,l:nat):ISeq{
    (p:nat) =>
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 :=x1(p+s2+m);
    var n2 :=x2(p+s1+l);
    var r :=(((n1*n2) as real/power2(p+s1+s2+m+l) as real)+0.5).Floor;
    r
}

function abv (n:int):nat
{
    if n>=0 then n else -n
}

lemma DArrow2(r:int,p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures  ((n1-1) as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2))<v1+v2<((n1+1)as real/power2(p+m+2))+((n2+1)as real/power2(p+l+2))
{}

// Lemma 5
lemma lmn5(n: nat, m: nat)
    requires m > 0
    // ensures n == log2(m).Floor ==> power2(n) as real <= m <= power2(n+1) as real
    ensures n == log2floor(m) ==> power(n) <= m <= power(n+1)

function searchi(m: nat, lowi: nat, maxi: nat, ans: nat): nat
    requires lowi > 0
    decreases maxi - lowi
{
    if maxi < lowi then 0
    else if lowi <= m < 2*lowi then ans
    else searchi(m, lowi*2, maxi, ans+1)
}

function log2floor(m: nat): nat
    requires m > 0
{
    searchi(m, 1, power(m), 0)
}


 

/*lemma DArrowMul(r:int,p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,n1:int,n2:int,s1:nat,s2:nat)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
ensures  ((n1-1) as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2))<v1+v2<((n1+1)as real/power2(p+m+2))+((n2+1)as real/power2(p+l+2))
{}*/

function Min(a:int,b:int):int
{
    if a<b then a else b
}

function Max(a:int,b:int):int
{
    if a<b then b else a
}
lemma mult1sup1(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures v1*v2<(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{   
    if  (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1){
    calc{
        (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    >=
        (((n1-1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }
    else if  (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2+1){
    calc{
        (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    >=
        (((n1-1)*(n2+1))as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1-1)as real)/power2(p+s2+m))*(((n2+1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }
    else if (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1+1)*(n2-1){
    calc{
        v1*v2;
    <
        ((n1+1)*(n2-1)) as real/power2(2*p+s1+s2+m+l);
    <=
        (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    }
    }
    else{
    calc{
        v1*v2;
    <
        ((n1+1)*(n2+1)) as real/power2(2*p+s1+s2+m+l);
    <=
        (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    }
    }
}

lemma mult1sup2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<v1*v2
{}

lemma mult1 (v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<v1*v2<(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{

}


lemma mult(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures DArrow(v1*v2,mul_a(x1,x2,z1,z2,m,l))
{}