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
eliminant (RingElement,PolynomialRing) := (RingElement) => (f,C)-> (
    Z := C_0; 
    R := ring f;
    assert( dim R == 0 );
    K := coefficientRing R;
    assert( isField K );
    assert( K === coefficientRing C );
    B := basis R;
    n := numgens source B;
    M := fold((M, i) -> M || 
              substitute(contract(B, f^(i+1)), K), 
              substitute(contract(B, 1_R), K), 
              flatten subsets(n, n));
    N := ((ker transpose M)).generators;
    P := matrix {toList apply(0..n, i -> Z^i)} * N;
              (flatten entries(P))_0
    )


regularRep = method()
regularRep (RingElement) := (Matrix) => f->(
    assert( dim ring f == 0 );
    B := basis ring f;
    K := coefficientRing ring f;
    substitute(contract(transpose B, f*B), K)
    )

charPoly = method() -- overload this to take matrices
charPoly (RingElement,Symbol) := (RingElement) => (f,Z)->(
    R := ring f;
    K := coefficientRing R;
    S := K[Z];
    Z = value Z;
    mf := regularRep(f) ** S;
    Idz := S_0 * id_(S^(numgens source mf));
    det(Idz - mf)
    )

SturmSequence = method()
SturmSequence (RingElement) := (List) => f->(
    assert( isPolynomialRing ring f);
    assert(numgens ring f === 1);
    R := ring f;
    assert(char R == 0);
    x := R_0;
    d := first degree f;
    l := new MutableList from toList (0..d);
    if d>=0 then (
	l#0 = f;
	if d >=1 then (
	    l#1 = diff(x,f);
	    scan(2..d, i -> l#i = -l#(i-2) % l#(i-1));
	    ));
    toList l
    )


sign=method()
sign (Number) := (ZZ) => n ->(
     if n < 0 then -1 
       else if n == 0 then 0
       else if n > 0 then 1
     )

signAtNegInfinity=method()
signAtNegInfinity (RingElement) := (ZZ) => f->(
    sign((if odd first degree f
	    then -1 else 1)*
	leadCoefficient f)
    )

signAtZero=method()
signAtZero (RingElement) := (ZZ) => f->(
    sign substitute (f,(ring f)_0=>0)
    )

signAtInfinity=method()
signAtInfinity (RingElement) := (ZZ) => f->(
    sign leadCoefficient f
    )

numRealSturm=method()
numRealSturm (RingElement) := (ZZ) => f->( 
    l := SturmSequence f;
    variations (signAtNegInfinity \ l)
        - variations (signAtInfinity \ l)
    )

numPosRoots = method()
numPosRoots (RingElement) := (ZZ) => f->(
    l := SturmSequence f;
    variations(signAtZero \ l) - variations(signAtInfinity \ l)
    )

numNegRoots = method()
numNegRoots (RingElement) := (ZZ) => f->(
    l := SturmSequence f;
    variations(signAtInfinity \ l) - variations(signAtZero \ l)
    )

variations = method()
variations (List) := (ZZ) => l->(
    n := 0;
    last := 0;
    scan(l, x -> if x =!=0 then (
	    if last < 0 and x > 0 or last > 0 and x < 0 then n = n+1;
	    last = x;
	    ));
    n
    )

traceForm = method()
traceForm (RingElement) := (RingElement) => f->(
    assert(dim ring f == 0);
    B := basis ring f;
    K := coefficientRing ring f;
    mm := substitute(contract(transpose B, f*B**B),K);--change name of mm to ?? and tr
    tr := matrix {apply(first entries B, x -> trace regularRep x)};
    adjoint(tr*mm, source tr, source tr)
    )

traceFormSignature = method()
traceFormSignature (RingElement) := (Sequence) => f->(
    R := ring f;
    assert( dim R == 0 );
    assert( char R == 0 ); --check char elsewhere
    S := QQ[Z];
    TrF := traceForm(f) ** S;
    IdZ := Z * id_(S^(numgens source TrF));
    ch := det(TrF - IdZ);  --use charPoly(TrF)
    << "The trace form S_f with f = " << f << 
      " has rank " << rank(TrF) << " and signature " << 
      numPosRoots(ch) - numNegRoots(ch) << endl
    ) --no strings in output!

numRealTrace = method()
numRealTrace (QuotientRing) := (ZZ) => R->(
    assert(dim R == 0);   --CONSIDER: input for trace stuff quotientRing/RingElement?
    assert(char R == 0);
    S := QQ[Z];
    TrF := traceForm(1_R) ** S;
    IdZ := Z * id_(S^(numgens source TrF));
    ch := det(TrF - IdZ); --use charPoly(TrF)
    numPosRoots(ch) - numNegRoots(ch)
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




