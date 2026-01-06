type ISeq = nat->int
// function power2 (n:int):real
function power2 (n:nat):real
ensures power2(n)>0.0
{
    if n==0 then 1.0 else if n>0 then 2.0*power2(n-1) else power2'(n)
} 

function power2'(n:int):real
requires n<=0
ensures 0.0<power2'(n)<=1.0
decreases -n
{
    if n==0 then 1.0 else 0.5*power2'(n+1)
}

function power2int(n: int): real
{
    if n >= 0 then power2nat(n as nat)
    else 1.0 / power2nat(-n as nat)
}
lemma power2intorder(n: int, m: int)
    requires n >= m
    ensures power2int(n) >= power2int(m)
    decreases n - m
{
    if n == m {
    } else if n > m {
        power2intorder(n - 1, m);
    } else if n < m {
        assert false;
    }
}
lemma powerpower2int(n: nat)
    requires n >= 0
    ensures power(n) as real == power2int(n)
{}
function power2nat(n: nat): real
    ensures power2nat(n) > 0.0
{
    if n == 0 then 1.0 else 2.0 * power2nat(n - 1)
}
lemma power2natpos(m: nat, n: nat)
    ensures power2nat(m + n) == power2nat(m) * power2nat(n)
{
    if m == 0 {
    } else {
        if n == 0 {
        } else {
            power2natpos(m - 1, n - 1);
        }
    }
}
lemma power2natpos101(m: nat, n: nat)
    requires m <= n
    ensures power2nat(n - m) == (1.0/power2nat(m)) * power2nat(n)
{
    if m == 0 {
    } else {
        if n == 0 {
        } else {
            power2natpos101(m - 1, n - 1);
        }
    }
}
lemma power2natpos001(m: nat, n: nat)
    requires m >= n
    ensures 1.0/power2nat(m - n) == (1.0/power2nat(m)) * power2nat(n)
{
    if m == 0 {
    } else {
        if n == 0 {
        } else {
            power2natpos001(m - 1, n - 1);
        }
    }
}
lemma power2natpos110(m: nat, n: nat)
    requires m >= n
    ensures power2nat(m - n) == power2nat(m) * (1.0/power2nat(n))
{
    if m == 0 {
    } else {
        if n == 0 {
        } else {
            power2natpos110(m - 1, n - 1);
        }
    }
}
lemma power2natpos010(m: nat, n: nat)
    requires n >= m
    ensures 1.0/power2nat(n - m) == power2nat(m) * (1.0/power2nat(n))
{
    if m == 0 {
    } else if m > 0 {
        if n == 0 {
        } else if n > 0 {
            power2natpos010(m - 1, n - 1);
        }
    }
}
lemma power2natpos000(m: nat, n: nat)
    ensures 1.0/power2nat(m + n) == (1.0/power2nat(m)) * (1.0/power2nat(n))
{
    if m == 0 {
    } else if m > 0 {
        if n == 0 {
        } else if n > 0 {
            power2natpos000(m - 1, n - 1);
        }
    }
}
lemma power2intpos(m: int, n: int)
    ensures power2int(m + n) == power2int(m) * power2int(n)
{
    var pmn: real;
    var pm: real;
    var pn: real;
    if n >= 0 {
        if m >= 0 {
            power2natpos(m, n);
        } else if m < 0 {
            if m + n >= 0 {
                power2natpos101((-m) as nat, n);
            } else if m + n < 0 {
                power2natpos001((-m) as nat, n);
            }
        }
    } else if n < 0 {
        if m >= 0 {
            if m + n >= 0 {
                power2natpos110(m, (-n) as nat);
            } else if m + n < 0 {
                power2natpos010(m, (-n) as nat);
            }
        } else if m < 0 {
            power2natpos000((-m) as nat, (-n) as nat);
        }
    }
}


function power (n:int):nat
ensures power(n)>=1
{
     if n<=0 then 1 else 2*power(n-1)
}
function set_z(n:int,p:nat):int{
    power(p)*n
}

lemma powersup'(n:nat)
ensures power2(n)>=1.0
{}

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
lemma {:axiom} lma5(n: nat, m: nat)
    requires m > 0
    requires n == log2floor_org(m)
    ensures power(n) <= m < power(n+1)

function searchi(m: nat, lowi: nat, maxi: nat, ans: nat): nat
    requires lowi > 0
    decreases maxi - lowi
{
    if maxi < lowi then 0
    else if lowi <= m < 2*lowi then ans
    else searchi(m, lowi*2, maxi, ans+1)
}

function log2floor_org(m: nat): nat
    requires m > 0
{
    searchi(m, 1, power(m), 0)
}

function log2floor(m: nat): nat
    requires m > 0
{
    // log2floor_org(m)
    log2floor_new(m)
}

method testlog2floor()
{
    assert log2floor_org(1) == log2floor_new(1);
    assert log2floor_org(2) == log2floor_new(2);
    assert log2floor_org(3) == log2floor_new(3);
    assert log2floor_org(4) == log2floor_new(4);
    assert log2floor_org(5) == log2floor_new(5);
    assert log2floor_org(6) == log2floor_new(6);
    assert log2floor_org(7) == log2floor_new(7);
    assert log2floor_org(8) == log2floor_new(8);
    assert log2floor_org(9) == log2floor_new(9);
    assert log2floor_org(10) == log2floor_new(10);
    assert log2floor_org(11) == log2floor_new(11);
}


lemma lma5'(n: nat, m: nat)
    requires m > 0
    requires n == log2floor_new(m)
    ensures power(n) <= m < power(n+1)
{}

function log2floor_new(m: nat): nat
    requires m > 0
    // ensures power2(log2floor_new(m)) <= m as real < power2(log2floor_new(m)+1)
    ensures power(log2floor_new(m)) <= m < power(log2floor_new(m)+1)
{
    searchinterval(m, 1, 0)
}

function searchinterval(m: nat, lo: nat, cnt: nat): nat
    requires 0 < lo <= m
    // requires power2(cnt) == lo as real
    requires power(cnt) == lo
    // ensures power2(searchinterval(m, lo, cnt)) <= m as real < power2(searchinterval(m, lo, cnt)+1)
    ensures power(searchinterval(m, lo, cnt)) <= m < power(searchinterval(m, lo, cnt)+1)
    decreases m - lo
{
    if lo <= m < 2*lo then cnt
    else searchinterval(m, 2*lo, cnt+1)
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
    if a < b then a else b
}

function Max(a:int,b:int):int
{
    if a < b then b else a
}

// lemma power1pos(n: nat, m: int)
lemma power1pos(n: nat, m: nat)
    ensures power(n + m) == power(n) * power(m)
{
    if n == 0 {
    } else {
        if m == 0 {
        } else {
            power1pos(n - 1, m - 1);
        }
    }
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

// lemma powerpos' (n:nat,m:int)
lemma powerpos' (n:nat,m:nat)
ensures power2(n+m)==power2(n)*power2(m)
{
    if n==0{
    }else{
        if m==0{

        }else if m < 0{
            powerpos'(n-1,m+1);
        }else{
            powerpos(n-1,m);
        }

    }
}

lemma muldivpower(a:real,b:nat,c:real,d:nat)
ensures (a / power2(b)) * (c / power2(d)) == (a*c) / power2(b+d)
{
    powerpos(b,d);
    assert power2(b+d) == power2(b)*power2(d);
    assert (a / power2(b)) * (c / power2(d)) == (a*c) / power2(b+d);
}

lemma power1sup(n: nat)
    ensures power(n) > 0
{}

// lemma powersup(n:int)
lemma powersup(n:nat)
ensures power2(n) > 0.0
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

lemma LessEqThanTrans(a: real, b: real, c: real)
    requires a <= b
    requires b < c
    ensures a < c
{}

lemma LessThanEqTrans(a: real, b: real, c: real)
    requires a < b
    requires b <= c
    ensures a < c
{}

// l1 <= 0.0 <= h1, l1 <= v1 <= h1, l2 <= 0.0 <= h2, l2 <= v2 <= h2
lemma maxminMM(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l2 < v2 < h2
    requires l2 <= 0.0 <= h2
    requires l1 < v1 < h1
    requires l1 <= 0.0 <= h1
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    var l21 := l2;
    var h21 := 0.0;
    var l22 := 0.0;
    var h22 := h2;
    if v1 < 0.0 {
        if v2 < 0.0 {
            maxminNN(v1, v2, l11, h11, l21, h21, x, y);
        } else if 0.0 < v2 {
            maxminNP(v1, v2, l11, h11, l22, h22, x, y);
        } else if v2 == 0.0 {
        } else {
            assert false;
        }
    } else if 0.0 < v1 {
        if v2 < 0.0 {
            maxminPN(v1, v2, l12, h12, l21, h21, x, y);
        } else if 0.0 < v2 {
            maxminPP(v1, v2, l12, h12, l22, h22, x, y);
        } else if v2 == 0.0 {
            assert l1 <= 0.0 < h1; // need to mention
            assert l2 < 0.0 < h2;
        } else {
            assert false;
        }
    } else {
        assert v1 == 0.0;
        if v2 < 0.0 {
        } else if 0.0 < v2 {
        } else if v2 == 0.0 {
        } else {
            assert false;
        }
    }
}


// l1 <= v1 <= h1 <= 0.0, l2 <= 0.0 <= h2, l2 <= v2 <= h2
lemma maxminNM(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l2 < v2 < h2
    requires l2 <= 0.0 <= h2
    requires l1 < v1 < h1 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
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
    requires l2 < v2 < h2
    requires l2 <= 0.0 <= h2
    requires 0.0 <= l1 < v1 < h1
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
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
    requires l1 < v1 < h1
    requires l1 <= 0.0 <= h1
    requires l2 < v2 < h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    if v1 < 0.0 {
        maxminNN(v1, v2, l11, h11, l2, h2, x, y);
    } else if 0.0 < v1 {
        maxminPN(v1, v2, l12, h12, l2, h2, x, y);
    } else if v1 == 0.0 {
    } else {
        assert false;
    }
}

// 0.0 <= l2 <= v2 <= h2, l1 <= 0.0 <= h1, l1 <= v1 <= h1
lemma maxminMP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 < v1 < h1
    requires l1 <= 0.0 <= h1
    requires 0.0 <= l2 < v2 < h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    var l11 := l1;
    var h11 := 0.0;
    var l12 := 0.0;
    var h12 := h1;
    if v1 < 0.0 {
        maxminNP(v1, v2, l11, h11, l2, h2, x, y);
    } else if 0.0 < v1 {
        maxminPP(v1, v2, l12, h12, l2, h2, x, y);
    } else if v1 == 0.0 {
    } else {
        assert false;
    }
}

// l1 <= v1 <= h1 <= 0.0 <= l2 <= v2 <= h2
lemma maxminNP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 < v1 < h1 <= 0.0
    requires 0.0 <= l2 < v2 < h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
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
    requires 0.0 <= l1 < v1 < h1
    requires l2 < v2 < h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    assert h1 * l2 < h1 * v2; // (l2 < v2) * h1
    assert h1 * v2 < v1 * v2; // (v1 < h1) * v2
    LessEqTrans(h1 * l2, h1 * v2, v1 * v2);
    assert h1 * l2 < v1 * v2;
    
    assert v1 * v2 < v1 * h2; // (v2 < h2) * v1
    assert v1 * h2 <= l1 * h2; // (l1 < v1) * h2
    LessEqTrans(v1 * v2, v1 * h2, l1 * h2);
    assert v1 * v2 < l1 * h2;
    
    assert x <= l2 * h1 < v1 * v2 < l1 * h2 <= y;
}

// l1 <= v1 <= h1 <= 0.0, l2 <= v2 <= h2 <= 0.0
lemma maxminNN(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 < v1 < h1 <= 0.0
    requires l2 < v2 < h2 <= 0.0
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    assert v1 * l2 <= l1 * l2; // (l1 < v1) * l2
    assert v1 * v2 < v1 * l2; // (l2 < v2) * v1
    LessEqTrans(v1 * v2, v1 * l2, l1 * l2);
    assert v1 * v2 < l1 * l2;
    
    assert h1 * h2 <= v1 * h2; // (v1 < h1) * h2
    assert v1 * h2 < v1 * v2; // (v2 < h2) * v1
    LessEqThanTrans(h1 * h2, v1 * h2, v1 * v2);
    assert h1 * h2 < v1 * v2;

    assert x <= h1 * h2 < v1 * v2 < l1 * l2 <= y;
}

// 0.0 <= l1 <= v1 <= h1, 0.0 <= l2 <= v2 <= h2
lemma maxminPP(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires 0.0 <= l1 < v1 < h1
    requires 0.0 <= l2 < v2 < h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    ensures x < v1 * v2 < y
{
    assert v1 * h2 < h1 * h2; // (v1 < h1) * h2
    assert v1 * v2 < v1 * h2; // (v2 < h2) * v1
    LessThanTrans(v1 * v2, v1 * h2, h1 * h2);
    assert v1 * v2 < h1 * h2;

    assert l1 * l2 <= v1 * l2; // (l1 < v1) * l2
    assert v1 * l2 < v1 * v2; // (l2 < v2) * v1
    LessEqTrans(l1 * l2, v1 * l2, v1 * v2);
    assert l1 * l2 < v1 * v2;
    
    assert x <= l1 * l2 < v1 * v2 < h1 * h2 <= y;
}


lemma maxmin(v1: real, v2: real, l1: real, h1: real, l2: real, h2: real, x: real, y: real)
    requires l1 < v1 < h1
    requires l2 < v2 < h2
    requires x <= l1 * l2 <= y
    requires x <= l1 * h2 <= y
    requires x <= h1 * l2 <= y
    requires x <= h1 * h2 <= y
    // ensures x <= v1 * v2 <= y
    ensures x < v1 * v2 < y
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
        // l1 < 0.0 <= h1
        // l1 < v1 < h1
        if 0.0 <= l2 {
            // 0.0 <= l2 < v2 < h2
            // min = l1*h2, max = h1*h2
            maxminMP(v1, v2, l1, h1, l2, h2, x, y);
        } else if l2 < 0.0 <= h2 {    
            // min = min{l1*h2, h1*l2}, max= max{l1*l2, h1*h2}
            maxminMM(v1, v2, l1, h1, l2, h2, x, y);
            assert x < v1 * v2 < y;
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

lemma prop_frac1(a: real, b: real, c: real, d: real)
    requires c > 0.0
    requires d > 0.0
    ensures (a*b) / (c*d) == (a/c) * (b/d)
{}

lemma check1(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))
    <= ((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))
    <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{
    var x := p+s2+m;
    var y := p+s1+l;
    var a := (n1-1) as real;
    var b := (n2-1) as real;
    var c := power2(x);
    var d := power2(y);

    // [goal]
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    //     <= (a/power2(x))*(b/power2(y))
    //     <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y));
    // [subgoal]
    // assert (a/power2(x)) * (b/power2(y)) == (a*b) / power2(x+y);

    powersup'(x);
    assert power2(x) >= 1.0;
    powersup'(y);
    assert power2(y) >= 1.0;
    prop_frac1(a, b, c, d);
    assert (a/c)*(b/d) == (a*b)/(c*d);
    muldivpower(a, x, b, y);
    assert (a / power2(x)) * (b / power2(y)) == (a*b) / power2(x+y); // subgoal
    assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    <= (a/power2(x))*(b/power2(y))
    <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y)); // goal
}

lemma check2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures 
    (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))
    <= ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))
    <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{
    var x := p+s2+m;
    var y := p+s1+l;
    var a := (n1-1) as real;
    var b := (n2+1) as real;
    var c := power2(x);
    var d := power2(y);

    // [goal]
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    //     <= (a/power2(x))*(b/power2(y))
    //     <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y));
    // [subgoal]
    // assert (a/power2(x)) * (b/power2(y)) == (a*b) / power2(x+y);

    powersup'(x);
    assert power2(x) >= 1.0;
    powersup'(y);
    assert power2(y) >= 1.0;
    prop_frac1(a, b, c, d);
    assert (a/c)*(b/d) == (a*b)/(c*d);
    muldivpower(a, x, b, y);
    assert (a / power2(x)) * (b / power2(y)) == (a*b) / power2(x+y); // subgoal
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    // <= (a/power2(x))*(b/power2(y))
    // <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y)); // goal
}

lemma check3(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures
    (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))
    <= ((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))
    <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{
    var x := p+s2+m;
    var y := p+s1+l;
    var a := (n1+1) as real;
    var b := (n2-1) as real;
    var c := power2(x);
    var d := power2(y);

    // [goal]
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    //     <= (a/power2(x))*(b/power2(y))
    //     <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y));
    // [subgoal]
    // assert (a/power2(x)) * (b/power2(y)) == (a*b) / power2(x+y);

    powersup'(x);
    assert power2(x) >= 1.0;
    powersup'(y);
    assert power2(y) >= 1.0;
    prop_frac1(a, b, c, d);
    assert (a/c)*(b/d) == (a*b)/(c*d);
    muldivpower(a, x, b, y);
    assert (a / power2(x)) * (b / power2(y)) == (a*b) / power2(x+y); // subgoal
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    // <= (a/power2(x))*(b/power2(y))
    // <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y)); // goal
}

lemma check4(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+s2+m)
requires n2==x2(p+s1+l)
requires s1== log2floor(abv(x1(z1))+2)+3
requires s2== log2floor(abv(x2(z2))+2)+3 
requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
ensures 
    (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))
    <= ((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))
    <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
{
    var x := p+s2+m;
    var y := p+s1+l;
    var a := (n1+1) as real;
    var b := (n2+1) as real;
    var c := power2(x);
    var d := power2(y);

    // [goal]
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    //     <= (a/power2(x))*(b/power2(y))
    //     <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y));
    // [subgoal]
    // assert (a/power2(x)) * (b/power2(y)) == (a*b) / power2(x+y);

    powersup'(x);
    assert power2(x) >= 1.0;
    powersup'(y);
    assert power2(y) >= 1.0;
    prop_frac1(a, b, c, d);
    assert (a/c)*(b/d) == (a*b)/(c*d);
    muldivpower(a, x, b, y);
    assert (a / power2(x)) * (b / power2(y)) == (a*b) / power2(x+y); // subgoal
    // assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(x+y))
    // <= (a/power2(x))*(b/power2(y))
    // <= (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(x+y)); // goal
}

// lemma mult1 (v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
// requires DArrow(v1,x1)
// requires DArrow(v2,x2)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3 
// requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
// ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<v1*v2<(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))
// {
//     check1(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
//     assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     //assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l));
//     check2(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
//     assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     //assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l));
//     check3(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
//     assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     //assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l));
//     check4(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2,r);
//     assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     //assert(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))<=((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l));
    
//     /*assert ((n1-1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     assert ((n1-1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     assert ((n1+1) as real/power2(p+s2+m))*((n2-1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));
//     assert ((n1+1) as real/power2(p+s2+m))*((n2+1) as real/power2(p+s1+l))<=(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l));*/
//     maxmin(v1,v2,(n1-1) as real/power2(p+s2+m),(n1+1) as real/power2(p+s2+m),(n2-1) as real/power2(p+s1+l),(n2+1)as real/power2(p+s1+l),(n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l)),(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l)));

// }

lemma prop_frac2(a: real, b: real)
    requires a != 0.0
    ensures b/a + 1.0/(2.0*a) == (b+1.0)/a - 1.0/(2.0*a)
{}
lemma prop_frac3(a:real,b:real)
requires a!=0.0
ensures (b/a)-(1.0/(2.0*a))==((b-1.0)/a)+1.0/(2.0*a)
{}

lemma divwork(a:real,b:nat,c:nat)
ensures (a/power2(b))/power2(c)==a/power2(b+c)
{
    powerpos(b,c);
}

// lemma circlecheck(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3 
// requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
// ensures (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))<((r as real+1.0)/power2(p))-((1.0/power2(p+1))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l)))
// {
//     assert (n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))==(((n1*n2) as real)/power2(2*p+s1+s2+m+l))+((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l));
//     var x := ((n1*n2) as real)/power2(p+s1+s2+m+l);
//     var y := ((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l));
//     assert x - 0.5 < r as real;
//     assert x < 0.5 + r as real;
//     assert x / power2(p) as real < 0.5 / power2(p) + r as real/ power2(p);
//     assert x / power2(p) as real < 1.0 / power2(p+1) + r as real/ power2(p);
//     assert power2(p+1) == 2.0*power2(p);
//     assert x / power2(p) as real < 1.0 / (2.0*power2(p)) + r as real/ power2(p);
//     prop_frac2(power2(p), r as real);
//     assert 1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
//     assert x / power2(p) as real < (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
//     assert x / power2(p) as real + y
//         < (r as real + 1.0) / power2(p) - (1.0 / (2.0*power2(p)) - y);
//     //assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/(power2(p+s1+s2+m+l) * power2(p));
//     //checker1(1, p+s1+s2+m+l);
//     divwork(n1 as real*n2 as real,p+s1+s2+m+l,p);
//     assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/(power2(p) * power2(p+s1+s2+m+l));
//     powerpos(p, p+s1+s2+m+l);
//     assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/power2(p+p+s1+s2+m+l);
//     //assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/power2(2*p+s1+s2+m+l);
//     assert ((n1 as real *n2 as real)/power2(2*p+s1+s2+m+l))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l))<((r as real+1.0)/power2(p))-((1.0/power2(p+1))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l)));
//     assert(n1 as real*n2 as real+abv(n1) as real+abv(n2) as real+1.0)/(power2(2*p+s1+s2+m+l))<((r as real+1.0)/power2(p))-((1.0/power2(p+1))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l)));
// }
lemma circlecheck(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires  r==(((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor
ensures ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))<((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2))
{
    /*
    var x := (set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2);
    var y := (power2(l)+power2(m))/power2(p+m+l+2);
    assert x - 0.5 < r as real;
    assert x < 0.5 + r as real;
    assert x / power2(p) as real < 0.5 / power2(p) + r as real/ power2(p);
    assert x / power2(p) as real < 1.0 / power2(p+1) + r as real/ power2(p);
    assert power2(p+1) == 2.0*power2(p);
    assert x / power2(p) as real < 1.0 / (2.0*power2(p)) + r as real/ power2(p);
    prop_frac2(power2(p) as real, r as real);
    assert 1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
    assert x / power2(p) as real < (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
    assert x / power2(p) as real + y
        < (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p)) + y;
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/(set_z(1,m+l+2) as real * power2(p));
    checker1(1, m+l+2);
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/(power2(p) * power2(m+l+2));
    powerpos(p, m+l+2);
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/power2(p+m+l+2);
    assert
       ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))
        < ((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2));
    */
    circlechecks(p, l, m, x1, x2);
}

lemma circlechecks(p:nat,l:nat,m:nat,x1:ISeq,x2:ISeq)
ensures
    var n1 := x1(p+m+2);
    var n2 := x2(p+l+2);
    var r := (((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor;
    ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))<((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2))
{
    var n1 := x1(p+m+2);
    var n2 := x2(p+l+2);
    var r := (((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor;

    var x := (set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2);
    var y := (power2(l)+power2(m))/power2(p+m+l+2);
    assert x - 0.5 < r as real;
    assert x < 0.5 + r as real;
    assert x / power2(p) as real < 0.5 / power2(p) + r as real/ power2(p);
    assert x / power2(p) as real < 1.0 / power2(p+1) + r as real/ power2(p);
    assert power2(p+1) == 2.0*power2(p);
    assert x / power2(p) as real < 1.0 / (2.0*power2(p)) + r as real/ power2(p);
    prop_frac2(power2(p) as real, r as real);
    assert 1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
    assert x / power2(p) as real < (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p));
    assert x / power2(p) as real + y
        < (r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p)) + y;
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/(set_z(1,m+l+2) as real * power2(p));
    checker1(1, m+l+2);
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/(power2(p) * power2(m+l+2));
    powerpos(p, m+l+2);
    assert (1.0/set_z(1,m+l+2) as real) / power2(p) == 1.0/power2(p+m+l+2);
    assert
       ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))
        < ((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2));
}



// lemma circlecheck2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq,r:int)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3 
// requires r==(((n1*n2) as real/power2(p+s1+s2+m+l))+0.5).Floor
// ensures (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))>=((r as real-1.0)/power2(p))+((1.0/power2(p+1))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l)))
// {
//     assert (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))==(((n1*n2) as real)/power2(2*p+s1+s2+m+l))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l));
//     var x := ((n1*n2) as real)/power2(p+s1+s2+m+l);
//     var y := ((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l));
//     assert x +0.5 >= r as real;
//     assert x >= -0.5 + r as real;
//     assert x / power2(p) as real >= -0.5 / power2(p) + r as real/ power2(p);
//     assert x / power2(p) as real >= -1.0 / power2(p+1) + r as real/ power2(p);
//     assert power2(p+1) == 2.0*power2(p);
//     assert x / power2(p) as real >= -1.0 / (2.0*power2(p)) + r as real/ power2(p);
//     prop_frac3(power2(p) as real, r as real);
//     assert -1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
//     assert x / power2(p) as real >= (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
//     assert x / power2(p) as real - y
//         <=(r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p)) - y;
//     divwork(n1 as real*n2 as real,p+s1+s2+m+l,p);
//     assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/(power2(p) * power2(p+s1+s2+m+l));
//     powerpos(p, p+s1+s2+m+l);
//     assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/power2(p+p+s1+s2+m+l);
//     assert (1.0/power2(p+s1+s2+m+l)) / power2(p) == 1.0/power2(2*p+s1+s2+m+l);
//     assert
//        (n1 as real*n2 as real-abv(n1) as real-abv(n2) as real-1.0)/(power2(2*p+s1+s2+m+l))>=((r as real-1.0)/power2(p))+((1.0/power2(p+1))-((abv(n1) as real+abv(n2) as real+1.0)/power2(2*p+s1+s2+m+l)));
// }

lemma circlecheck2(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires   r==(((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor
ensures (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>=((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2))
{
    /*
    var x := (set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2);
    var y := (power2(l)+power2(m))/power2(p+m+l+2);
    assert x +0.5 >= r as real;
    assert x >= -0.5 + r as real;
    assert x / power2(p) as real >= -0.5 / power2(p) + r as real/ power2(p);
    assert x / power2(p) as real >= -1.0 / power2(p+1) + r as real/ power2(p);
    assert power2(p+1) == 2.0*power2(p);
    assert x / power2(p) as real >= -1.0 / (2.0*power2(p)) + r as real/ power2(p);
    prop_frac3(power2(p) as real, r as real);
    assert -1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
    assert x / power2(p) as real >= (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
    assert x / power2(p) as real - y
        <=(r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p)) - y;
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/(power2(m+l+2) * power2(p));
    checker1(1, m+l+2);
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/(power2(p) * power2(m+l+2));
    powerpos(p, m+l+2);
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/power2(p+m+l+2);
    assert
       (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>=((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
    */
    circlecheck2s(p, l, m, x1, x2);
}
lemma circlecheck2s(p:nat,l:nat,m:nat,x1:ISeq,x2:ISeq)
ensures
    var n1 := x1(p+m+2);
    var n2 := x2(p+l+2);
    var r := (((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor;
    (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>=((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2))
{
    var n1 := x1(p+m+2);
    var n2 := x2(p+l+2);
    var r := (((set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2))+0.5).Floor;
    var x := (set_z(n1,l) as real +set_z(n2,m) as real)/power2(m+l+2);
    var y := (power2(l)+power2(m))/power2(p+m+l+2);
    assert x +0.5 >= r as real;
    assert x >= -0.5 + r as real;
    assert x / power2(p) as real >= -0.5 / power2(p) + r as real/ power2(p);
    assert x / power2(p) as real >= -1.0 / power2(p+1) + r as real/ power2(p);
    assert power2(p+1) == 2.0*power2(p);
    assert x / power2(p) as real >= -1.0 / (2.0*power2(p)) + r as real/ power2(p);
    prop_frac3(power2(p) as real, r as real);
    assert -1.0 / (2.0*power2(p)) + r as real/ power2(p) == (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
    assert x / power2(p) as real >= (r as real - 1.0) / power2(p) + 1.0 / (2.0*power2(p));
    assert x / power2(p) as real - y
        <=(r as real + 1.0) / power2(p) - 1.0 / (2.0*power2(p)) - y;
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/(power2(m+l+2) * power2(p));
    checker1(1, m+l+2);
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/(power2(p) * power2(m+l+2));
    powerpos(p, m+l+2);
    assert (1.0/power2(m+l+2)) / power2(p) == 1.0/power2(p+m+l+2);
    assert
       (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>=((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
}
lemma checker1(n1:int,l:nat)
ensures n1 as real *power2(l)==set_z(n1,l)as real
{}


lemma {:axiom} lemma6(p:nat,p':nat,x:ISeq,v:real)
requires p > p'
requires DArrow(v,x)
ensures (x(p')-1)*power(p-p')-1 < x(p) < (x(p')+1)*power(p-p')+1

lemma froml6a(p:nat,p':nat,x:ISeq,v:real)
requires DArrow(v,x)
requires p>p'
ensures abv(x(p))+1 < power(p-p') * (abv(x(p')) + 1) + 2
{
    lemma6(p, p', x, v);
    assert x(p)<(x(p')+1)*power(p-p')+1;
}

lemma froml6(p:nat,p':nat,x:ISeq,v:real)
requires DArrow(v,x)
requires p>p'
ensures abv(x(p))+1<power((p-p'))*(abv(x(p'))+2)
{
    lemma6(p,p',x,v);
    assert x(p)<(x(p')+1)*power(p-p')+1;
    assert abv(x(p))<(abv(x(p'))+1)*power(p-p')+1;
    assert abv(x(p))+1<abv(x(p'))*power(p-p')+power(p-p')+2;
    assert abv(x(p))+1<abv(x(p'))*power(p-p')+power(p-p'+1);
    assert abv(x(p))+1<(abv(x(p'))+2)*power(p-p');
    assert abv(x(p))+1<power((p-p'))*(abv(x(p'))+2);
}

lemma {:axiom} lemma5(n:int,m:nat)
requires m > 0
requires n==log2floor(m)
// ensures power(n) <= m < power(n)
ensures power(n) <= m < power(n+1)

lemma inequality0(a: int, b: int, c: int)
    requires a < b
    requires c > 0
    ensures c * a < c * b
{}
lemma inequality11(a: real, b: real, c: real, d: real)
    requires a <= b
    requires c <= d
    ensures a + c <= b + d
{}
lemma inequality2(a: real, b: real, c: real)
    requires a <= b
    requires c > 0.0
    ensures c * a <= c * b
{}

// lemma following(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq)
// requires DArrow(v1,x1)
// requires DArrow(v2,x2)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires z1 < 4
// requires z2 < 4
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3
// ensures abv(n1)+1<power(p+s1+s2+m-z1-2)
// {
//     if p+s2+m > z1 {

//         var part1 := abv(n1) + 1;
//         var powps2m := power(p+s2+m-z1);
//         var abvx1z1 := abv(x1(z1))+2;
//         // var part2 := power(p+s2+m-z1) * (abv(x1(z1))+2);
//         var part2 := powps2m * abvx1z1;
//         froml6(p+s2+m, z1, x1, v1);
//         // assert abv(x1(p+s2+m))+1 < power(p+s2+m-z1) * (abv(x1(z1))+2);
//         // assert abv(n1)+1 < power(p+s2+m-z1) * (abv(x1(z1))+2);
//         assert part1 < part2;

//         // [subgoal]
//         // assert power(p+s2+m-z1) * (abv(x1(z1) + 2)) < power(p+s1+s2+m-z1-2);
//         // assert powps2m * abvx1z1 < power(p+s1+s2+m-z1-2);

//         var n := log2floor(abvx1z1);
//         lma5'(n, abvx1z1);
//         assert abvx1z1 < power(n + 1);

//         power1sup(p+s2+m-z1);
//         assert powps2m > 0;
//         inequality0(abvx1z1, power(n + 1), powps2m);
//         assert part2 == powps2m * abvx1z1 < powps2m * power(n + 1);
//         assert n + 1 == s1 - 2;
//         assert part2 < powps2m * power(s1 - 2);
//         calc {
//             power(p+s2+m-z1) * power(s1 - 2);
//             { power1pos(p+s2+m-z1, s1 - 2); }
//             power((p+s2+m-z1) + (s1-2));
//             power(p+s1+s2+m-z1-2);
//         }
//         assert part1 < part2 < power(p+s1+s2+m-z1-2); // goal
    
//     } else {
//         assert false;
//     }
// }

lemma followings(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
        abv(n1)+1<power(p+s1+s2+m-z1-2)
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);

    if p+s2+m > z1 {

        var part1 := abv(n1) + 1;
        var powps2m := power(p+s2+m-z1);
        var abvx1z1 := abv(x1(z1))+2;
        // var part2 := power(p+s2+m-z1) * (abv(x1(z1))+2);
        var part2 := powps2m * abvx1z1;
        froml6(p+s2+m, z1, x1, v1);
        // assert abv(x1(p+s2+m))+1 < power(p+s2+m-z1) * (abv(x1(z1))+2);
        // assert abv(n1)+1 < power(p+s2+m-z1) * (abv(x1(z1))+2);
        assert part1 < part2;

        // [subgoal]
        // assert power(p+s2+m-z1) * (abv(x1(z1) + 2)) < power(p+s1+s2+m-z1-2);
        // assert powps2m * abvx1z1 < power(p+s1+s2+m-z1-2);

        var n := log2floor(abvx1z1);
        lma5'(n, abvx1z1);
        assert abvx1z1 < power(n + 1);

        power1sup(p+s2+m-z1);
        assert powps2m > 0;
        inequality0(abvx1z1, power(n + 1), powps2m);
        assert part2 == powps2m * abvx1z1 < powps2m * power(n + 1);
        assert n + 1 == s1 - 2;
        assert part2 < powps2m * power(s1 - 2);
        calc {
            power(p+s2+m-z1) * power(s1 - 2);
            { power1pos(p+s2+m-z1, s1 - 2); }
            power((p+s2+m-z1) + (s1-2));
            power(p+s1+s2+m-z1-2);
        }
        assert part1 < part2 < power(p+s1+s2+m-z1-2); // goal
    
    } else {
        assert false;
    }
}

// lemma following2(v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq)
// requires DArrow(v1,x1)
// requires DArrow(v2,x2)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires z1 < 4
// requires z2 < 4
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3
// ensures abv(n2)+1<power(p+s1+s2+l-z2-2)
// {
//     // copy of the body of "following"
//     if p+s1+l > z2 {

//         var part1 := abv(n2) + 1;
//         var powps1l := power(p+s1+l-z2);
//         var abvx2z2 := abv(x2(z2))+2;
//         var part2 := powps1l * abvx2z2;
//         froml6(p+s1+l, z2, x2, v2);
//         assert part1 < part2;

//         var n := log2floor(abvx2z2);
//         lma5'(n, abvx2z2);
//         assert abvx2z2 < power(n + 1);

//         power1sup(p+s1+l-z2);
//         assert powps1l > 0;
//         inequality0(abvx2z2, power(n + 1), powps1l);
//         assert part2 == powps1l * abvx2z2 < powps1l * power(n + 1);
//         assert n + 1 == s2 - 2;
//         assert part2 < powps1l * power(s2 - 2);
//         calc {
//             power(p+s1+l-z2) * power(s2 - 2);
//             { power1pos(p+s1+l-z2, s2 - 2); }
//             power((p+s1+l-z2) + (s2-2));
//             power(p+s1+s2+l-z2-2);
//         }
//         assert part1 < part2 < power(p+s1+s2+l-z2-2); // goal
    
//     } else {
//         assert false;
//     }
// }

lemma following2s(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
requires z1 < 4
requires z2 < 4
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3
// ensures abv(n2)+1<power(p+s1+s2+l-z2-2)
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n2 := x2(p+s1+l);
        abv(n2)+1<power(p+s1+s2+l-z2-2)

{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);

    // copy of the body of "following"
    if p+s1+l > z2 {

        var part1 := abv(n2) + 1;
        var powps1l := power(p+s1+l-z2);
        var abvx2z2 := abv(x2(z2))+2;
        var part2 := powps1l * abvx2z2;
        froml6(p+s1+l, z2, x2, v2);
        assert part1 < part2;

        var n := log2floor(abvx2z2);
        lma5'(n, abvx2z2);
        assert abvx2z2 < power(n + 1);

        power1sup(p+s1+l-z2);
        assert powps1l > 0;
        inequality0(abvx2z2, power(n + 1), powps1l);
        assert part2 == powps1l * abvx2z2 < powps1l * power(n + 1);
        assert n + 1 == s2 - 2;
        assert part2 < powps1l * power(s2 - 2);
        calc {
            power(p+s1+l-z2) * power(s2 - 2);
            { power1pos(p+s1+l-z2, s2 - 2); }
            power((p+s1+l-z2) + (s2-2));
            power(p+s1+s2+l-z2-2);
        }
        assert part1 < part2 < power(p+s1+s2+l-z2-2); // goal
    
    } else {
        assert false;
    }
}


// lemma thus (v1:real,v2:real,p:nat,s1:nat,s2:nat,z1:nat,z2:nat,m:nat,l:nat,n1:int,n2:int,x1:ISeq,x2:ISeq)
// requires DArrow(v1,x1)
// requires DArrow(v2,x2)
// requires n1==x1(p+s2+m)
// requires n2==x2(p+s1+l)
// requires z1 < 4
// requires z2 < 4
// requires s1== log2floor(abv(x1(z1))+2)+3
// requires s2== log2floor(abv(x2(z2))+2)+3
// // ensures abv(n1)+abv(n2)+1 < power(p+s1+s2+m+l-1)
// // ensures abv(n1)+abv(n2)+1 < power2int(p+s1+s2+m+l-1)
// {        
//     // assert abv(n1) + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2) - 1 by {
//     following(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2);
//     // followings(v1,v2,p,z1,z2,m,l,x1,x2);
//     assert abv(n1) + 1 < power(p+s1+s2+m-z1-2);
//     following2(v1,v2,p,s1,s2,z1,z2,m,l,n1,n2,x1,x2);
//     // following2s(v1,v2,p,z1,z2,m,l,x1,x2);
//     assert abv(n2) + 1 < power(p+s1+s2+l-z2-2);
//     assert abv(n1) + 1 + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2);
//     assert abv(n1) + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2) - 1;
//     // }
//     var ps1s2 := p+s1+s2;
//     var ps1s2mz1 := ps1s2+m-z1-2;
//     var ps1s2lz2 := ps1s2+l-z2-2;
//     assert abv(n1) + abv(n2) + 1 < power(ps1s2mz1) + power(ps1s2lz2) - 1;
//     assert (ps1s2-2)+(m-z1) >= 0;

//     assert power(ps1s2mz1) as real == power2int(ps1s2-2)*power2int(m-z1) by {

//     // assert power(ps1s2mz1) as real == power((ps1s2-2)+(m-z1)) as real;
//     // powerpower2int((ps1s2-2)+(m-z1));
//     // assert power((ps1s2-2)+(m-z1)) as real == power2int((ps1s2-2)+(m-z1));
//     // power2intpos(ps1s2-2, m-z1);
//     // assert power2int((ps1s2-2)+(m-z1)) == power2int(ps1s2-2)*power2int(m-z1);
//     calc {
//         power(ps1s2mz1) as real;
//         power((ps1s2-2)+(m-z1)) as real;
//         { powerpower2int((ps1s2-2)+(m-z1)); }
//         power2int((ps1s2-2)+(m-z1));
//         { power2intpos(ps1s2-2, m-z1); }
//         // { assert power2int((ps1s2-2)+(m-z1)) == power2int(ps1s2-2)*power2int(m-z1); }
//         power2int(ps1s2-2)*power2int(m-z1);
//     }
//     // calc {
//     //     power(ps1s2mz1) as real;
//     //     { powerpower2int(ps1s2mz1); }
//     //     power2int(ps1s2mz1);
//     //     power2int((ps1s2-2)+(m-z1));
//     //     { power2intpos(ps1s2-2, m-z1); }
//     //     // { assert power2int((ps1s2-2)+(m-z1)) == power2int(ps1s2-2)*power2int(m-z1); }
//     //     power2int(ps1s2-2)*power2int(m-z1);
//     // }
//     }
//     // assert (ps1s2-2)+(l-z2) >= 0;
//     // assert power(ps1s2lz2) as real == power2int(ps1s2-2)*power2int(l-z2) by {
//     calc {
//         power(ps1s2lz2) as real;
//         power((ps1s2-2)+(l-z2)) as real;
//         { powerpower2int((ps1s2-2)+(l-z2)); }
//         power2int((ps1s2-2)+(l-z2));
//         { power2intpos(ps1s2-2, l-z2); }
//         // { assert power2int((ps1s2-2)+(l-z2)) == power2int(ps1s2-2)*power2int(l-z2); }
//         power2int(ps1s2-2)*power2int(l-z2);
//     }
//     // }
//     // var ex1 := abv(n1) as real + abv(n2) as real + 1.0;
//     // var ex2 := power(ps1s2mz1) as real + power(ps1s2lz2) as real - 1.0;
//     // var ex3 := power2int(ps1s2-2)*power2int(m-z1) + power2int(ps1s2-2)*power2int(l-z2) - 1.0;
//     // var ex4 := power2int(ps1s2-2)*(power2int(m-z1) + power2int(l-z2)) - 1.0;
//     // assert ex1 < ex2;
//     assert abv(n1) as real + abv(n2) as real + 1.0
//         < power(ps1s2mz1) as real + power(ps1s2lz2) as real - 1.0;
//     assert power(ps1s2mz1) as real + power(ps1s2lz2) as real - 1.0
//         == power2int(ps1s2-2)*power2int(m-z1) + power2int(ps1s2-2)*power2int(l-z2) - 1.0;
//     assert power2int(ps1s2-2)*power2int(m-z1) + power2int(ps1s2-2)*power2int(l-z2) - 1.0
//         == power2int(ps1s2-2)*(power2int(m-z1) + power2int(l-z2)) - 1.0;

//     // assert abv(n1) as real + abv(n2) as real + 1.0
//     //      < power2int(ps1s2-2)*(power2int(m-z1) + power2int(l-z2)) - 1.0;
//     // powerpos'(p+s1+s2-2,m-z1);
//     // // powerpos'(p+s1+s2-2,l-z2);
//     // // assert abv(n1)+abv(n2)+1<(power(p+s1+s2-2))*(power(m-z1)+power(l-z2))-1;
//     // // assert abv(n1)+abv(n2)+1<power(p+s1+s2+m+l-1);
// }


lemma leftInequalitySub1(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    abv(n1) + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2) - 1
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    followings(v1,v2,p,z1,z2,m,l,x1,x2);
    assert abv(n1) + 1 < power(p+s1+s2+m-z1-2);
    following2s(v1,v2,p,z1,z2,m,l,x1,x2);
    assert abv(n2) + 1 < power(p+s1+s2+l-z2-2);
    assert abv(n1) + 1 + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2);
    assert abv(n1) + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2) - 1;
}



lemma leftInequalitySub2(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    var ps1s2 := p+s1+s2;
    var ps1s2mz1 := ps1s2+m-z1-2;
    power(ps1s2mz1) as real == power2int(ps1s2-2)*power2int(m-z1)
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    var ps1s2 := p+s1+s2;
    var ps1s2mz1 := ps1s2+m-z1-2;
    assert power(ps1s2mz1) as real == power((ps1s2-2)+(m-z1)) as real;
    powerpower2int((ps1s2-2)+(m-z1));
    assert power((ps1s2-2)+(m-z1)) as real == power2int((ps1s2-2)+(m-z1));
    power2intpos(ps1s2-2, m-z1);
    assert power2int((ps1s2-2)+(m-z1)) == power2int(ps1s2-2)*power2int(m-z1);
}

lemma leftInequalitySub2'(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    var ps1s2 := p+s1+s2;
    var ps1s2lz2 := ps1s2+l-z2-2;
    power(ps1s2lz2) as real == power2int(ps1s2-2)*power2int(l-z2)
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    var ps1s2 := p+s1+s2;
    var ps1s2lz2 := ps1s2+l-z2-2;
    assert power(ps1s2lz2) as real == power((ps1s2-2)+(l-z2)) as real;
    powerpower2int((ps1s2-2)+(l-z2));
    assert power((ps1s2-2)+(l-z2)) as real == power2int((ps1s2-2)+(l-z2));
    power2intpos(ps1s2-2, l-z2);
    assert power2int((ps1s2-2)+(l-z2)) == power2int(ps1s2-2)*power2int(l-z2);
}

lemma leftInequality(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    abv(n1) as real + abv(n2) as real + 1.0
    < power2int(p+s1+s2-2)*(power2int(m-z1) + power2int(l-z2)) - 1.0
{        
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    var ps1s2 := p+s1+s2;
    leftInequalitySub1(v1, v2, p, z1, z2, m, l, x1, x2);
    assert abv(n1) + abv(n2) + 1 < power(p+s1+s2+m-z1-2) + power(p+s1+s2+l-z2-2) - 1;
    assert abv(n1) + abv(n2) + 1 < power(ps1s2+m-z1-2) + power(ps1s2+l-z2-2) - 1;
    assert (ps1s2-2)+(m-z1) >= 0;
    leftInequalitySub2(v1, v2, p, z1, z2, m, l, x1, x2);
    assert (ps1s2-2)+(l-z2) >= 0;
    leftInequalitySub2'(v1, v2, p, z1, z2, m, l, x1, x2);
    assert abv(n1) as real + abv(n2) as real + 1.0
        < power(ps1s2+m-z1-2) as real + power(ps1s2+l-z2-2) as real - 1.0;
}



lemma middleInequality(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var ml := if m >= l then m else l;
    var zz := if z1 >= z2 then z2 else z1;
    var mz1 := power2int(m-z1);
    var lz2 := power2int(l-z2);
    power2int(p+s1+s2-2)*(power2int(m-z1) + power2int(l-z2)) - 1.0
    <= power2int(p+s1+s2-1)*power2int(ml-zz) - 1.0
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var ps1s2 := p+s1+s2;
    var ml := if m >= l then m else l;
    var zz := if z1 >= z2 then z2 else z1;
    var powmlzz := power2int(ml-zz);

    var mz1 := power2int(m-z1);
    var lz2 := power2int(l-z2);

    power2intorder(ml-zz, m-z1); // 1st term
    assert mz1 <= powmlzz;
    power2intorder(ml-zz, l-z2); // 2nd term
    assert lz2 <= powmlzz;

    inequality11(mz1, powmlzz, lz2, powmlzz);
    assert mz1 + lz2 <= powmlzz + powmlzz;
    inequality2(mz1 + lz2, powmlzz + powmlzz, power2int(ps1s2-2));
    calc {
        power2int(ps1s2-2)*(mz1 + lz2) - 1.0;
        <= power2int(ps1s2-2)*(powmlzz + powmlzz) - 1.0;
        power2int(ps1s2-1)*powmlzz - 1.0;
    }
    assert 
        power2int(ps1s2-2)*(mz1 + lz2) - 1.0
        <= power2int(ps1s2-1)*powmlzz - 1.0;
}

lemma three_reals(factor: real, a: real, b: real)
    requires factor >= 0.0
    requires a <= b
    ensures factor * a - 1.0 < factor * b
{}

lemma rightInequality(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var ml := if m >= l then m else l;
    var zz := if z1 >= z2 then z2 else z1;
    power2int(p+s1+s2-1)*power2int(ml-zz) - 1.0
    < power2int(p+s1+s2+m+l-1)
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var ml := if m >= l then m else l;
    var zz := if z1 >= z2 then z2 else z1;
    var small := power2int(ml-zz);
    var large := power2int(m+l);
    var factor := power2int(p+s1+s2-1);
    assert factor >= 0.0;
    assert ml-zz <= m+l;
    power2intorder(m+l, ml-zz);
    assert small <= large;
    three_reals(power2int(p+s1+s2-1), power2int(ml-zz), power2int(m+l));
    assert power2int(p+s1+s2-1)*power2int(ml-zz) - 1.0 < power2int(p+s1+s2-1)*power2int(m+l);    
    power2intpos(p+s1+s2-1, m+l);
    assert power2int(p+s1+s2-1)*power2int(m+l) == power2int((p+s1+s2-1)+(m+l));
    assert (p+s1+s2-1)+(m+l) == p+s1+s2+m+l-1;
    assert power2int((p+s1+s2-1)+(m+l)) == power2int(p+s1+s2+m+l-1);
    calc {
        power2int(p+s1+s2-1)*power2int(ml-zz) - 1.0;
    <   power2int(p+s1+s2-1)*power2int(m+l);
        power2int(p+s1+s2+m+l-1);
    }
}


lemma mul_core(v1:real,v2:real,p:nat,z1:nat,z2:nat,m:nat,l:nat,x1:ISeq,x2:ISeq)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires z1 < 4
requires z2 < 4
ensures 
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    var n1 := x1(p+s2+m);
    var n2 := x2(p+s1+l);
    abv(n1) as real + abv(n2) as real + 1.0
    < power2int(p+s1+s2+m+l-1)
{
    var s1 := log2floor(abv(x1(z1))+2)+3;
    var s2 := log2floor(abv(x2(z2))+2)+3;
    leftInequality(v1, v2, p, z1, z2, m, l, x1, x2);
    middleInequality(v1, v2, p, z1, z2, m, l, x1, x2);
    rightInequality(v1, v2, p, z1, z2, m, l, x1, x2);
}