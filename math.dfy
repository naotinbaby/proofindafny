type ISeq = nat->int
function power2 (n:int):real
ensures power2(n)>0.0
{
    if n<=0 then 1.0 else 2.0*power2(n-1)
} 
function power (n:nat):int
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
/*{
    calc{
        n as real-0.5 <=p as real/q as real <n as real+0.5;
        (n as real-0.5)*q as real <= p as real <(n as real +0.5)*q as real;
    }
}*/

/*lemma circle2(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires r==(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor
ensures (set_z(n1,l) as real + set_z(n2,m) as real)>(r as real-0.5)*power2(m+l+2)
{
    circle((set_z(n1,l)+set_z(n2,m)),power(m+l+2),r);
}*/


lemma circlecheck(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires r==(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor
ensures ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))<((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2))
/*{
    calc{
        (set_z(n1,l) as real + set_z(n2,m) as real);
    >{circle((set_z(n1,l)+set_z(n2,m)),power(m+l+2),r);}
        (r as real-0.5)*power2(m+l+2);
    ==
        (r as real *power2(m+l+2))-power2(m+l+1);
    }
}*/

lemma circlecheck2(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires r==(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor
ensures (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2))


ghost predicate DArrow(v: real, n: ISeq)
{
    forall p: nat :: (n(p) - 1) as real / power2(p) < v < (n(p) + 1) as real / power2(p)
}

function add_a(x1:ISeq,x2:ISeq,m:nat,l:nat):ISeq{
    (p:nat) => 
    var n1:=x1(p+m+2);
    var n2:=x2(p+l+2);
    var r :=(((n1 as real)*power2(l)+(n2 as real)*power2(m))/power2(m+l+2)).Floor;
    r
}

lemma DArrow2(r:int,p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures ((n1-1) as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2))<v1+v2<((n1+1)as real/power2(p+m+2))+((n2+1)as real/power2(p+l+2))
{}

lemma l01(m:nat,l:nat)
ensures power2(m+l+1)-power2(l)-power2(m)>=0.0
{
    if m==0{
        if l==0{
        }else{
            l01(m,l-1);
        }
    }else{
        if l==0{
            l01(m-1,l);
        }else{
            l01(m-1,l-1);
            assert power2(m+l-1)-power2(m-1)-power2(l-1)>=0.0;
        }
    }
}

lemma l02(m:nat,l:nat)
ensures -(power2(m+l+1)-power2(l)-power2(m))<=0.0
{
    if m==0{
        if l==0{
        }else{
        l02(m,l-1);
        }
    }else{
        if l==0{
            l02(m-1,l);
        }else{
            l02(m-1,l-1);
        }
    }
}

lemma l03(m:nat,l:nat,p:nat)
ensures -(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2)<=0.0
{
    calc{
        -(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    <={l02(m,l);}
        0.0/power2(p+m+l+2);
    ==
        0.0;
    }
}

lemma l04(m:nat,l:nat,p:nat)
ensures (power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2)>=0.0
{
    calc{
        (power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    >={l01(m,l);}
        0.0/power2(p+m+l+2);
    ==
        0.0;
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

lemma powerpos2(n:nat,m:nat,n1:real)
ensures n1/power2(n+m)==n1/(power2(n)*power2(m))
{
   powerpos(n,m);
}

lemma powerpower(n:nat)
ensures power(n) as real/power(n) as real==power2(n)/power2(n)==1.0
{
    calc{
        power(n) as real/power(n) as real;
        power(n) as real*(1.0/power(n) as real);
    }
}
lemma powerpos5(a:real,b:real,c:real,d:real)
requires b!=0.0
requires d!=0.0
ensures (a/b)*(c/d)==(a*c)/(b*d)
{}
lemma powerpos3(n:nat,m:nat)
ensures 1.0/power2(n)==(1.0*power2(m))/power2(m+n)
{
    calc{
        1.0/power2(n);
        (1.0/power2(n))*1.0;
        {powerpower(m);}
        (1.0/power2(n))*(power2(m)/power2(m));
        {powerpos5(1.0 ,power2(n),power2(m),power2(m));}
        (1.0 *power2(m))/(power2(n)*power2(m));
        {powerpos2(n,m,power2(m));}
        (1.0 *power2(m))/power2(m+n);
    }
}

lemma powerpos4(n:nat,m:nat,n1:real)
ensures n1/power2(n)==(n1*power2(m))/power2(m+n)
{
    calc{
        n1/power2(n);
        (n1/power2(n))*1.0;
        {powerpower(m);}
        (n1/power2(n))*(power2(m)/power2(m));
        (n1*power2(m))/(power2(n)*power2(m));
        {powerpos2(n,m,power2(m));}
        (n1*power2(m))/power2(m+n);
    }
}
lemma powerpos6 (a:real,b:real,c:real)
requires b>0.0
ensures  (a/b)+(c/b)==(a+c)/b
{}
lemma mathsup(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires r==(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor
ensures -(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2))==-(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2)
{
    calc{
        -(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2));
        {powerpos3(p+1,m+l+1);}
        -(power2(m+l+1)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2));
        -(power2(m+l+1)/power2(p+m+l+2))-((-power2(l)-power2(m))/power2(p+m+l+2));
        -((power2(m+l+1))-power2(l)-power2(m))/power2(p+m+l+2);
    }
}

lemma mathsup4(n1:int,n2:int,l:nat,m:nat,p:nat,x1:ISeq,x2:ISeq)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures  ((n1+1)as real *power2(l)+(n2+1)as real*power2(m))/power2(p+m+l+2)==(set_z(n1,l)as real+set_z(n2,m) as real+power2(l)+power2(m))/power2(p+m+l+2)
{
    calc{
        ((n1+1)as real *power2(l)+(n2+1)as real*power2(m))/power2(p+m+l+2);
        (n1 as real *power2(l)+power2(l)+power2(m)*n2 as real+power2(m))/power2(p+m+l+2);
        {checker1(n1,l);}{checker2(n2,m);}
        (set_z(n1,l)as real+set_z(n2,m) as real+power2(l)+power2(m))/power2(p+m+l+2);
    }
}
lemma mathsup2(n1:int,n2:int,l:nat,m:nat,p:nat,x1:ISeq,x2:ISeq)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures ((n1+1)as real/power2(p+m+2))+((n2+1)as real/power2(p+l+2))==((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2))
{
    calc{
        ((n1+1)as real/power2(p+m+2))+((n2+1)as real/power2(p+l+2));
        {powerpos4(p+m+2,l,(n1+1)as real);}{powerpos4(p+l+2,m,(n2+1)as real);}
        ((n1+1)as real *power2(l))/power2(p+m+l+2)+((n2+1)as real*power2(m))/power2(p+m+l+2);
        {mathsup4(n1,n2,l,m,p,x1,x2);}
        (set_z(n1,l)as real+set_z(n2,m) as real+power2(l)+power2(m))/power2(p+m+l+2);
        ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2));
    }
}

lemma mathsup3(n1:int,n2:int,l:nat,m:nat,p:nat,x1:ISeq,x2:ISeq)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures ((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2))==(set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)
{
    calc{
        ((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2));
        {powerpos4(p+m+2,l,(n1-1) as real);}{powerpos4(p+l+2,m,(n2-1)as real);}
        ((n1-1)as real * power2(l))/power2(p+m+l+2)+((n2-1) as real *power2(m))/power2(p+m+l+2);
        {powerpos6((n1-1)as real*power2(l),power2(p+m+l+2),(n2-1) as real *power2(m));}
        ((n1-1)as real * power2(l)+(n2-1) as real*power2(m))/power2(p+m+l+2);
        (n1 as real *power2(l)-power2(l)+power2(m)*n2 as real-power2(m))/power2(p+m+l+2);
        (n1 as real*power2(l)+n2 as real *power2(m)-power2(l)-power2(m))/power2(p+m+l+2);
        {checker1(n1,l);}{checker2(n2,m);}
        (set_z(n1,l)as real+set_z(n2,m)as real-power2(l)-power2(m))/power2(p+m+l+2);
        {mathpower(n1,n2,l,m,p,x1,x2);}
        (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2);
    }
}
lemma mathsup5(p:nat,l:nat,m:nat,r:int,x1:ISeq,x2:ISeq,n1:int,n2:int)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
requires r==(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor
ensures (1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2))==(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2)
{
    calc{
        (1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
        {powerpos3(p+1,m+l+1);}
        (power2(m+l+1)/power2(p+m+l+2))-((power2(l)+power2(m))/power2(p+m+l+2));
        {checker3(power2(l),power2(m),power2(p+m+l+2));}
        (power2(m+l+1)/power2(p+m+l+2))+((-power2(l)-power2(m))/power2(p+m+l+2));
        (power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    }
}
lemma checker3(a:real,b:real,c:real)
requires c!=0.0
ensures -((a+b)/c)==(-a-b)/c
{}

lemma checker1(n1:int,l:nat)
ensures n1 as real *power2(l)==set_z(n1,l)as real
{}
lemma checker2(n2:int,m:nat)
ensures n2 as real *power2(m)==set_z(n2,m)as real
{}

lemma mathpower(n1:int,n2:int,l:nat,m:nat,p:nat,x1:ISeq,x2:ISeq)
requires n1==x1(p+m+2)
requires n2==x2(p+l+2)
ensures (set_z(n1,l)as real+set_z(n2,m)as real-power2(l)-power2(m))/power2(p+m+l+2)==(set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)
{}

lemma math2(p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
ensures ((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2)) < v1+v2
{    
    var n1:=x1(p+m+2) ;
    var n2:=x2(p+l+2) ;
    var r:=(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor;
    /*calc{
                  v1+v2;
    >{DArrow2(r,p,v1,v2,m,l,x1,x2,n1,n2);}
        ((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2));
    =={mathsup3(n1,n2,l,m,p,x1,x2);}
        (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2);
    >={circlecheck2(p,l,m,r,x1,x2,n1,n2);}{abc(v1+v2,((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2)),((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2)));}
        ((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
    /*=={mathsup5(p,l,m,r,x1,x2,n1,n2);}
         ((r as real+1.0)/power2(p))+(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    >={l04(m,l,p);}
        (r as real-1.0)/power2(p);*/  
    }*/
    DArrow2(r,p,v1,v2,m,l,x1,x2,n1,n2);
    assert v1+v2>((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2));
    mathsup3(n1,n2,l,m,p,x1,x2);
    assert ((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2))==(set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2);
    assert v1+v2>(set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2);
    circlecheck2(p,l,m,r,x1,x2,n1,n2);
    assert (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2)>=((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
    assert v1+v2>((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
    mathsup5(p,l,m,r,x1,x2,n1,n2);
    assert ((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2)) ==((r as real-1.0)/power2(p))+(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    assert v1+v2>((r as real-1.0)/power2(p))+(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    assert ((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2)) < v1+v2;
}

lemma abc(a:real,b:real,c:real)
requires a>b && b>=c
ensures a>c
{}

/*lemma math3(p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
ensures v1+v2 < ((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2))
{   
    var n1:=x1(p+m+2) ;
    var n2:=x2(p+l+2) ;
    var r:=(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor;
    calc{
        v1+v2;
    <{DArrow2(r,p,v1,v2,m,l,x1,x2,n1,n2);}
        ((n1 as real+1.0)/power2(p+m+2))+((n2 as real+1.0)/power2(p+l+2));
    =={mathsup2(n1,n2,l,m,p,x1,x2);}
    //   ((n1+1)as real *power2(l)+(n2+1)as real*power2(m))/power2(p+m+l+2);
    //=={mathsup4(n1,n2,l,m,p,x1,x2);}
    //   (set_z(n1,l)as real+set_z(n2,m) as real+power2(l)+power2(m))/power2(p+m+l+2);
    //==
        ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2));
    <{circlecheck(p,l,m,r,x1,x2,n1,n2);}
        ((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2));
    /*=={mathsup(p,l,m,r,x1,x2,n1,n2);}
        ((r as real+1.0)/power2(p))-(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    <{l03(m,l,p);}
        (r as real+1.0)/power2(p);*/
    }
}


/*lemma math (p:nat,v1:real,v2:real,m:nat,l:nat,x1:ISeq,x2:ISeq,r:int)
requires DArrow(v1,x1)
requires DArrow(v2,x2)
ensures DArrow(v1+v2,add_a(x1,x2,m,l))
//ensures (r as real-1.0)/power2(p) < v1+v2 < (r as real+1.0)/power2(p)
{
    var n1:=x1(p+m+2) ;
    var n2:=x2(p+l+2) ;
    var r:=(((set_z(n1,l) as real +set_z(n2,m) as real)/set_z(1,m+l+2) as real)+0.5).Floor;
    calc{
        v1+v2;
    <{DArrow2(r,p,v1,v2,m,l,x1,x2,n1,n2);}
        ((n1 as real+1.0)/power2(p+m+2))+((n2 as real+1.0)/power2(p+l+2));
    =={mathsup2(n1,n2,l,m,p,x1,x2);}
    //   ((n1+1)as real *power2(l)+(n2+1)as real*power2(m))/power2(p+m+l+2);
    //=={mathsup4(n1,n2,l,m,p,x1,x2);}
  
    //   (set_z(n1,l)as real+set_z(n2,m) as real+power2(l)+power2(m))/power2(p+m+l+2);
    //==
        ((set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2))+((power2(l)+power2(m))/power2(p+m+l+2));
    <{circlecheck(p,l,m,r,x1,x2,n1,n2);}
        ((r as real+1.0)/power2(p))-(1.0/power2(p+1))+((power2(l)+power2(m))/power2(p+m+l+2));
    =={mathsup(p,l,m,r,x1,x2,n1,n2);}
        ((r as real+1.0)/power2(p))-(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    <={l03(m,l,p);}
        (r as real+1.0)/power2(p);
    }
    calc{
              v1+v2;
    >{DArrow2(r,p,v1,v2,m,l,x1,x2,n1,n2);}
        ((n1-1)as real/power2(p+m+2))+((n2-1)as real/power2(p+l+2));
    =={mathsup3(n1,n2,l,m,p,x1,x2);}
        (set_z(n1,l)as real+set_z(n2,m)as real)/power2(p+m+l+2)-(power2(l)+power2(m))/power2(p+m+l+2);
    >={circle((set_z(n2,l)+set_z(n1,m)),power(m+l+2),r);}
        ((r as real-1.0)/power2(p))+(1.0/power2(p+1))-((power2(l)+power2(m))/power2(p+m+l+2));
    == 
         ((r as real+1.0)/power2(p))+(power2(m+l+1)-power2(l)-power2(m))/power2(p+m+l+2);
    >={l04(m,l,p);}
        (r as real-1.0)/power2(p);  
    }
}
