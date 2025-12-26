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

/*lemma DArrow2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3
ensures  (Min(Min((n1-1)*(n2-1),(n1-1)*(n2+1)),Min((n1+1)*(n2-1),(n1+1)*(n2+1)))) as real/power2(2*p+s1+s2+m+l)<v1*v2<(Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1)))) as real/power2(2*p+s1+s2+m+l)
*/


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

lemma powerpos (n:nat,m:nat)
ensures power2(n+m)==power2(n)*power2(m)
{
    if n==0{

    }else{
        if m==0{
        }else{
            powerpos(n-1,m-1);
        }
    }
}

lemma muldivpower(a:real,b:nat,c:real,d:nat)
ensures (a/power2(b))*(c/power2(d))==(a*c)/power2(b+d)
{
    powerpos(b,d);
}

lemma powersup(n:int)
ensures power2(n)>0.0
{}
/*lemma sup1sup1(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
//requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1)
         ==> v1*v2<(n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l))
{
    if (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1){
    /*calc{
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    >=
        (((n1-1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    =={muldivpower((n1-1)as real,p+s2+m,(n2-1)as real,p+s1+l);}
        (((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }*/
    assert (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l))>=(((n1-1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    {muldivpower((n1-1)as real,p+s2+m,(n2-1)as real,p+s1+l);}
    assert ((n1-1)as real*(n2-1)as real)/power2(2*p+s1+s2+m+l)==(((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    }

    /*if (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1){
    calc{
        v1*v2;
    <//{DArrow2(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);}
        (((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    =={muldivpower((n1-1)as real,p+s2+m,(n2-1)as real,p+s1+l);}
     (((n1-1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    <=
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    }
    }*/
}

lemma sup1sup1'(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires  (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1)
//requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l))>v1*v2
{}*/

lemma LessThanTrans(a: real, b: real, c: real)
    requires a < b
    requires b < c
    ensures a < c
{}

lemma LessEqTrans(a: real, b: real, c: real)
    requires a <= b
    requires b <= c
    ensures a <= c
{}

// l1 <= 0.0 <= h2, l1 <= v1 <= h1, l2 <= 0.0 <= h2, l2 <= v2 <= h2
lemma maxminMM(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l2 <= v2 <= h2
    requires l2 <= 0.0 <= h2
    requires l1 <= v1 <= h1
    requires l1 <= 0.0 <= h1
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    var l21 := l2;
    var h21 := 0.0;
    var l22 := 0.0;
    var h22 := h2;
    if v1 <= 0.0 {
        if v2 <= 0.0 {
            maxminNN(v1, v2, l11, h11, l21, h21, x, y);
            assert x <= v1 * v2 <= y;
        } else if 0.0 <= v2 {
            maxminNP(v1, v2, l11, h11, l22, h22, x, y);
            assert x <= v1 * v2 <= y;
        }
    } else if 0.0 <= v1 {
        if v2 <= 0.0 {
            maxminPN(v1, v2, l12, h12, l21, h21, x, y);
            assert x <= v1 * v2 <= y;
        } else if 0.0 <= v2 {
            maxminPP(v1, v2, l12, h12, l22, h22, x, y);
            assert x <= v1 * v2 <= y;
        }
    }
}


// l1 <= v1 <= h1 <= 0.0, l2 <= 0.0 <= h2, l2 <= v2 <= h2
lemma maxminNM(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l2 <= v2 <= h2
    requires l2 <= 0.0 <= h2
    requires l1 <= v1 <= h1 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
/*
    var l21 := l2;
    var h21 := 0.0;
    var l22 := 0.0;
    var h22 := h2;
    if v2 <= 0.0 {
        maxminNN(v1, v2, l1, h1, l21, h21, x, y);
    } else if 0.0 <= v2 {
        maxminNP(v1, v2, l1, h1, l22, h22, x, y);
    }
*/
    maxminMN(v2, v1, l2, h2, l1, h1, x, y);
}

// 0 <= l1 <= v1 <= h1, l2 <= 0.0 <= h2, l2 <= v2 <= h2
lemma maxminPM(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l2 <= v2 <= h2
    requires l2 <= 0.0 <= h2
    requires 0.0 <= l1 <= v1 <= h1
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
/*
    var l21 := l2;
    var h21 := 0.0;
    var l22 := 0.0;
    var h22 := h2;
    if v2 <= 0.0 {
        maxminPN(v1, v2, l1, h1, l21, h21, x, y);
    } else if 0.0 <= v2 {
        maxminPP(v1, v2, l1, h1, l22, h22, x, y);
    }
*/
    maxminMP(v2, v1, l2, h2, l1, h1, x, y);
}

// l2 <= v2 <= h2 <= 0.0, l1 <= 0.0 <= h1, l1 <= v1 <= h1
lemma maxminMN(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 <= v1 <= h1
    requires l1 <= 0.0 <= h1
    requires l2 <= v2 <= h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    if v1 <= 0.0 {
        maxminNN(v1, v2, l11, h11, l2, h2, x, y);
    } else if 0.0 <= v1 {
        maxminPN(v1, v2, l12, h12, l2, h2, x, y);
    }
}

// 0.0 <= l2 <= v2 <= h2, l1 <= 0.0 <= h1, l1 <= v1 <= h1
lemma maxminMP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 <= v1 <= h1
    requires l1 <= 0.0 <= h1
    requires 0.0 <= l2 <= v2 <= h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    if v1 <= 0.0 {
        maxminNP(v1, v2, l11, h11, l2, h2, x, y);
    } else if 0.0 <= v1 {
        maxminPP(v1, v2, l12, h12, l2, h2, x, y);
    }
}

// l1 <= v1 <= h1 <= 0.0 <= l2 <= v2 <= h2
lemma maxminNP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 <= v1 <= h1 <= 0.0
    requires 0.0 <= l2 <= v2 <= h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
/*
    assert v1 * v2 <= v1 * l2; // (l2 < v2) * v1
    assert v1 * l2 <= h1 * l2; // (v1 < h1) * l2
    LessEqTrans(v1 * v2, v1 * l2, h1 * l2);
    assert v1 * v2 <= h1 * l2;

    assert v1 * h2 <= v1 * v2; // (v2 < h2) * v1
    assert l1 * h2 <= v1 * h2; // (l1 < v1) * h2
    LessEqTrans(l1 * h2, v1 * h2, v1 * v2);
    assert l1 * h2 <= v1 * v2;

    assert x <= l1 * h2 <= v1 * v2 <= h1 * l2 <= y;
*/
    maxminPN(v2, v1, l2, h2, l1, h1, x, y);
}

// l2 <= v2 <= h2 <= 0.0 <= l1 <= v1 <= h1
lemma maxminPN(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires 0.0 <= l1 <= v1 <= h1
    requires l2 <= v2 <= h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    assert h1 * l2 <= h1 * v2; // (l2 <= v2) * h1
    assert h1 * v2 <= v1 * v2; // (v1 <= h1) * v2
    LessEqTrans(h1 * l2, h1 * v2, v1 * v2);
    assert h1 * l2 <= v1 * v2;
    
    assert v1 * v2 <= v1 * h2; // (v2 <= h2) * v1
    assert v1 * h2 <= l1 * h2; // (l1 <= v1) * h2
    LessEqTrans(v1 * v2, v1 * h2, l1 * h2);
    assert v1 * v2 <= l1 * h2;
    
    assert x <= l2 * h1 <= v1 * v2 <= l1 * h2 <= y;
}

// l1 <= v1 <= h1 <= 0.0, l2 <= v2 <= h2 <= 0.0
lemma maxminNN(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 <= v1 <= h1 <= 0.0
    requires l2 <= v2 <= h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    assert v1 * l2 <= l1 * l2; // (l1 <= v1) * l2
    assert v1 * v2 <= v1 * l2; // (l2 <= v2) * v1
    LessEqTrans(v1 * v2, v1 * l2, l1 * l2);
    assert v1 * v2 <= l1 * l2;
    
    assert h1 * h2 <= v1 * h2; // (v1 <= h1) * h2
    assert v1 * h2 <= v1 * v2; // (v2 <= h2) * v1
    LessEqTrans(h1 * h2, v1 * h2, v1 * v2);
    assert h1 * h2 <= v1 * v2;

    assert x <= h1 * h2 <= v1 * v2 <= l1 * l2 <= y;
}

// 0.0 <= l1 <= v1 <= h1, 0.0 <= l2 <= v2 <= h2
lemma maxminPP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires 0.0 <= l1 <= v1 <= h1
    requires 0.0 <= l2 <= v2 <= h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    assert v1 * h2 <= h1 * h2; // (v1 <= h1) * h2
    assert v1 * v2 <= v1 * h2; // (v2 <= h2) * v1
    LessEqTrans(v1 * v2, v1 * h2, h1 * h2);
    assert v1 * v2 <= h1 * h2;

    assert l1 * l2 <= v1 * l2; // (l1 <= v1) * l2
    assert v1 * l2 <= v1 * v2; // (l2 <= v2) * v1
    LessEqTrans(l1 * l2, v1 * l2, v1 * v2);
    assert l1 * l2 <= v1 * v2;
    
    assert x <= l1 * l2 <= v1 * v2 <= h1 * h2 <= y;
}


lemma maxmin(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 < v1 < h1
    requires l2 < v2 < h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x <= v1 * v2 <= y
{
    if 0.0 <= l1 {
        if 0.0 <= l2 {
            // min = l1*l2, max = h1*h2
            maxminPP(v1, v2, l1, h1, l2, h2, x, y);
        } else if l2 < 0.0 <= h2 {    
            // min = h1*l2, max = h1*h2
            maxminPM(v1, v2, l1, h1, l2, h2, x, y);
        } else { // h2 < 0.0
            // min = h1*l2, max = h2*l1
            maxminPN(v1, v2, l1, h1, l2, h2, x, y);
        }
    } else if l1 < 0.0 <= h1 {
        if 0.0 <= l2 {
            // min = l1*h2, max = h1*h2
            maxminMP(v1, v2, l1, h1, l2, h2, x, y);
        } else if l2 < 0.0 <= h2 {    
            // min = min{l1*h2, h1*l2}, max= max{l1*l2, h1*h2}
            maxminMM(v1, v2, l1, h1, l2, h2, x, y);
        } else { // h2 < 0.0
            // min = h1*l2, max = l1*l2
            maxminMN(v1, v2, l1, h1, l2, h2, x, y);
        }
    } else { // h1 < 0.0
        if 0.0 <= l2 {
            // min = l1*h2, max = h1*l2
            maxminNP(v1, v2, l1, h1, l2, h2, x, y);
        } else if l2 < 0.0 <= h2 {    
            // min = h1*h2, max = l1*l2
            maxminNM(v1, v2, l1, h1, l2, h2, x, y);
        } else { // h2 < 0.0
            // min = l1*l2, max = h1*h2
            maxminNN(v1, v2, l1, h1, l2, h2, x, y);
        }
    }
}

 

/*lemma mult1sup1(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures v1*v2<(n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l))
{   
    /*if  (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1-1)*(n2-1){
    calc{
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    >=
        (((n1-1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1-1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }
    else if  (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1+1)*(n2-1){
    calc{
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    >=
        (((n1+1)*(n2-1))as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1+1)as real)/power2(p+s2+m))*(((n2-1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }
    else if (Max(Max((n1-1)*(n2-1),(n1-1)*(n2+1)),Max((n1+1)*(n2-1),(n1+1)*(n2+1))))==(n1+1)*(n2+1){
    calc{        
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    >=
        (((n1+1)*(n2+1))as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1+1)as real)/power2(p+s2+m))*(((n2+1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }
    else{
    calc{
        (n1*n2+abv(n1)+abv(n2)+1)as real/(power2(2*p+s1+s2+m+l));
    >=
        ((n1-1)as real*(n2+1)as real)/power2(2*p+s1+s2+m+l);
    ==
        (((n1-1)as real)/power2(p+s2+m))*(((n2+1)as real)/power2(p+s1+l));
    >
        v1*v2;
    }
    }*/
    
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
*/

lemma check1(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))
{
    //assert ((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))==((n1-1)as real*(n2-1)as real)/(power2(p+s2+m)*power2(p+s1+l));
    muldivpower((n1-1)as real,p+s2+m,(n2-1) as real ,p+s1+l);
    //assert ((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))==((n1-1)as real*(n2-1)as real)/(power2(p+s2+m+p+s1+l));
}

lemma check2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))
{
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m)*power2(p+s1+l));
    muldivpower((n1-1)as real,p+s2+m,(n2+1) as real ,p+s1+l);
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m+p+s1+l));
}

lemma check3(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))
{
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m)*power2(p+s1+l));
    muldivpower((n1+1)as real,p+s2+m,(n2-1) as real ,p+s1+l);
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m+p+s1+l));
}

lemma check4(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))
{
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m)*power2(p+s1+l));
    muldivpower((n1+1)as real,p+s2+m,(n2+1) as real ,p+s1+l);
    //assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))==((n1-1)as real*(n2+1)as real)/(power2(p+s2+m+p+s1+l));
}

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
    check1(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
    assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l));
    check2(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
    assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l));
    check3(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
    assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l));
    check4(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
    assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l));
    /*assert ((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    assert ((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
    assert ((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));*/
    //maxmin(v1,v2,(n1-1) as real/power2(p+s2+m),(n1+1) as real/power2(p+s2+m),(n2-1) as real/power2(p+s1+l),(n2+1)as real/power2(p+s1+l),(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l)),(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l)));

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