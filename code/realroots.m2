--RealRoots.m2
newPackage(
    "RealRoots",
    Version=>0.1,
    Date=>"Oct 9, 2020",
    Authors=>{
	{Name=>"Dan Grayson",
	 Email=>"",
	 HomePage=>""},
     	{Name=>"Jordy Lopez",
	 Email=>"jordy.lopez@math.tamu.edu",
	 HomePage=>""},
    	{Name=>"Kelly Maluccio",
	 Email=>"kmaluccio@math.tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~kmaluccio"},
    	{Name=>"Frank Sottile",
	 Email=>"",
	 HomePage=>""},
	{Name=>"Thomas Yahl",
	 Email=>"Thomasjyahl@math.tamu.edu",
	 HomePage=>"https://math.tamu.edu/~thomasjyahl"}
	},
    Headline=>"Package for exploring counting and locating real solutions to polynomial systems",
    PackageImports=>{},
    PackageExports=>{},
    DebuggingMode=>True
    )


export{
    "eliminant",
    "regularRep",
    "charPoly",
    "SturmSequence",
    "sign",
    "signAtNegInfinity",
    "signAtZero",
    "signAtInfinity",
    "numRealSturm",
    "numPosRoots",
    "numNegRoots",
    "variations",
    "traceForm",
    "traceFormSignature",
    "numRealTrace"
    }

--thomas is going to fix this..
eliminant = method()
eliminant (RingElement,PolynomialRing) := (RingElement) => (h,C)-> (
    Z := C_0; 
    A := ring h;
    assert( dim A == 0 );
    F := coefficientRing A;
    assert( isField F );
    assert( F === coefficientRing C );
    B := basis A;
    d := numgens source B;
    M := fold((M, i) -> M || 
              substitute(contract(B, h^(i+1)), F), 
              substitute(contract(B, 1_A), F), 
              flatten subsets(d, d));
    N := ((ker transpose M)).generators;
    P := matrix {toList apply(0..d, i -> Z^i)} * N;
              (flatten entries(P))_0
    )


regularRep = method()
regularRep (RingElement) := (Matrix) => f->(
    assert( dim ring f == 0 );
    b := basis ring f;
    k := coefficientRing ring f;
    substitute(contract(transpose b, f*b), k)
    )

charPoly = method()
charPoly (RingElement,PolynomialRing) := (RingElement) => (h,C)->(
    A := ring h;
    F := coefficientRing A;
    S := F[C];
    C = value C;
    mh := regularRep(h) ** S;
    Idz := S_0 * id_(S^(numgens source mh));
    det(Idz - mh)
    )

SturmSequence = method()
SturmSequence (RingElement) := (Sequence) => f->(
    assert( isPolynomialRing ring f);
    assert(numgens ring f === 1);
    R := ring f;
    assert(char R == 0);
    x := R_0;
    n := first degree f;
    c := new MutableList from toList (0..n);
    if n>=0 then (
	c#0 = f;
	if n >=1 then (
	    c#1 = diff(x,f);
	    scan(2..n, i -> c#i = -c#(i-2) % c#(i-1));
	    ));
    toList c
    )


sign=method()
sign (Number) := (ZZ) => n ->(
     if n < 0 then -1 
       else if n == 0 then 0
       else if n > 0 then 1
     )

signAtNegInfinity=method()
signAtNegInfinity (RingElement) := (ZZ) => g->(
    sign((if odd first degree g
	    then -1 else 1)*
	leadCoefficient g)
    )

signAtZero=method()
signAtZero (RingElement) := (ZZ) => g->(
    sign substitute (g,(ring g)_0=>0)
    )

signAtInfinity=method()
signAtInfinity (RingElement) := (ZZ) => g->(
    sign leadCoefficient g
    )

numRealSturm=method()
numRealSturm (RingElement) := (ZZ) => f->( 
    c := SturmSequence f;
    variations (signAtNegInfinity \ c)
        - variations (signAtInfinity \ c)
    )

numPosRoots = method()
numPosRoots (RingElement) := (ZZ) => f->(
    c := SturmSequence f;
    variations(signAtZero \ c) - variations(signAtInfinity \ c)
    )

numNegRoots = method()
numNegRoots (RingElement) := (ZZ) => f->(
    c := SturmSequence f;
    variations(signAtInfinity \ c) - variations(signAtZero \ c)
    )

variations = method()
variations (Sequence) := (ZZ) => c->(
    n := 0;
    last := 0;
    scan(c, x -> if x =!=0 then (
	    if last < 0 and x > 0 or last > 0 and x < 0 then n = n+1;
	    last = x;
	    ));
    n
    )

traceForm = method()
traceForm (RingElement) := (RingElement) => h->(
    assert(dim ring h == 0);
    b := basis ring h;
    k := coefficientRing ring h;
    mm := substitute(contract(transpose b, h*b**b),k);
    tr := matrix {apply(first entries b, x -> trace regularRep x)};
    adjoint(tr*mm, source tr, source tr)
    )

traceFormSignature = method()
traceFormSignature (RingElement) := (Sequence) => h->(
    A := ring h;
    assert( dim A == 0 );
    assert( char A == 0 );
    S := QQ[Z];
    TrF := traceForm(h) ** S;
    IdZ := Z * id_(S^(numgens source TrF));
    f := det(TrF - IdZ);
    << "The trace form S_h with h = " << h << 
      " has rank " << rank(TrF) << " and signature " << 
      numPosRoots(f) - numNegRoots(f) << endl
    )

numRealTrace = method()
numRealTrace (QuotientRing) := (ZZ) => A->(
    assert(dim A == 0);
    assert(char A == 0);
    S := QQ[Z];
    TrF := traceForm(1_A) ** S;
    IdZ := Z * id_(S^(numgens source TrF));
    f := det(TrF - IdZ);
    numPosRoots(f) - numNegRoots(f)
    )

beginDocumentation()


end

--Put notes, examples, etc down here. It won't go in the actual package.

--Notes:
----
----1) Remember to include tests for the code in documentation.
----2) How do we make sure that polynomials f and g have real coefficients?
----
----
----
----
----
----




