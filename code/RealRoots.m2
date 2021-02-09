--RealRoots.m2
newPackage(
    "RealRoots",
    Version=>"0.1",
    Date=>"Oct 9, 2020",
    Authors=>{
	{Name=>"Dan Grayson",
	 Email=>"",
	 HomePage=>""},
     	{Name=>"Jordy Lopez",
	 Email=>"jordy.lopez@math.tamu.edu",
	 HomePage=>""},
    	{Name=>"Kelly Maluccio",
	 Email=>"kmaluccio@tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~kmaluccio"},
    	{Name=>"Frank Sottile",
	 Email=>"sottile@math.tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~frank.sottile/"},
	{Name=>"Thomas Yahl",
	 Email=>"Thomasjyahl@math.tamu.edu",
	 HomePage=>"https://math.tamu.edu/~thomasjyahl"}
	},
    Headline=>"Package for exploring counting and locating real solutions to polynomial systems",
    PackageImports=>{},
    PackageExports=>{},
    DebuggingMode=>true
    )


export{
    "eliminant",
    "eliminant1",
    "eliminant2",
    "regularRep",
    "charPoly",
    "SturmSequence", --do we need to export this
    "numRealSturm",
    "numPosRoots",
    "numNegRoots",
    "variations",
    "traceForm",
    "traceForm1",
    "traceFormSignature",
    "numRealTrace"
    }

--needs better name
--also need to worry about fields with parameters
isUnivariate = method()
isUnivariate (Ring) := Boolean => R->(
    K := coefficientRing R;
    if instance(K,InexactField) then print "Warning: Computations over inexact field";
    (isPolynomialRing R) and (numgens R === 1) and (isField K) and (char K === 0)
    )


isArtinian = method()
isArtinian (Ring) := Boolean => R->(
    K := coefficientRing R;
    if instance(K,InexactField) then print "Warning: Computations over inexact field";
    (isField K) and (char K===0) and (dim R===0)
    )


eliminant = method()
eliminant (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    B := basis R;
    n := numgens source B;
    K := coefficientRing R;
    
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
    P := map(R^1,R^(n+1),(i,j)->f^j);
    M := last coefficients(P, Monomials=>B);
    coeffs := sub(gens ker M,K);
    (map(S^1,S^(n+1),(i,j)->S_0^j) * coeffs)_(0,0)
    )

eliminant1 = method()
eliminant1 (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    K := coefficientRing R;
    
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
    phi := map(R,S,{f});
    (ker phi)_0
    )

eliminant2 = method()
eliminant2 (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    n := numgens source basis R;
    
    g := charPoly(f);
    if (first degree g === n) then g else error "oops!"
    )


regularRep = method()
regularRep (RingElement) := Matrix => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    K := coefficientRing R;
    
    B := basis R;
    C := last coefficients(f*B,Monomials=>B);
    (B,sub(C,K))
    )


charPoly = method()
charPoly (Matrix) := RingElement => M->(
    n := numgens source M;
    if not (numgens target M === n) then error "Error: Expected a square matrix";
    
    K := ring M;
    if not (isField K and char K === 0) then error "Error: Expected a field of characteristic zero";
    
    Z := getSymbol "Z";
    S := K(monoid [Z]);

    IdZ := S_0*id_(S^n);
    det(IdZ - M)
    )

charPoly (RingElement) := RingElement => f->(
    (B,mf) := regularRep(f);
    charPoly(mf)
    )


SturmSequence = method()
SturmSequence (RingElement) := List => f->(    
    R := ring f;
    if not isUnivariate(R) then error "Error: Expected univariate polynomial";
    if (f == 0) then error "Error: Expected nonzero polynomial";
    
    x := R_0;
    d := first degree f;
    l := new MutableList from toList(0..d);
    if d >= 0 then (
	l#0 = f;
	if d >= 1 then (
	    l#1 = diff(x,f);
	    scan(2..d, i -> l#i = -l#(i-2) % l#(i-1))
	    )
	);
    toList l
    )


sign = method()
sign (Number) := ZZ => n ->(
     if n < 0 then -1 
     else if n == 0 then 0
     else if n > 0 then 1
     )


signAtNegInfinity = method()
signAtNegInfinity (RingElement) := ZZ => f->(
    sign( (if odd first degree f then -1 else 1) * leadCoefficient f )
    )


signAt = method()
signAt (RingElement,Number) := ZZ => (f,r)->(
    sign( substitute(f,(ring f)_0=>r) )
    )


signAtInfinity = method()
signAtInfinity (RingElement) := ZZ => f->(
    sign( leadCoefficient f )
    )


numRealSturm = method()
numRealSturm (RingElement) := ZZ => f->( 
    l := SturmSequence f;
    variations apply(l,signAtNegInfinity) - variations apply(l,signAtInfinity)
    )

numRealSturm (RingElement,Number,Number) := ZZ => (f,a,b)->(
    l := SturmSequence f;
    variations apply(l,g->signAt(g,a)) - variations apply(l,g->signAt(g,b))
    )

numRealSturm (RingElement,Number,InfiniteNumber) := ZZ => (f,a,b)->(
    l := SturmSequence f;
    variations apply(l,g->signAt(g,a)) - variations apply(l,g->signAtInfinity(g))
    )

numRealSturm (RingElement,InfiniteNumber,Number) := ZZ => (f,a,b)->(
    l := SturmSequence f;
    variations apply(l,g->signAtNegInfinity(g)) - variations apply(l,g->signAt(g,b))
    )


numPosRoots = method()
numPosRoots (RingElement) := ZZ => f->(
    l := SturmSequence f;
    variations apply(l,g->signAt(g,0)) - variations apply(l,signAtInfinity)
    )


numNegRoots = method()
numNegRoots (RingElement) := ZZ => f->(
    l := SturmSequence f;
    variations apply(l,signAtNegInfinity) - variations apply(l,g->signAt(g,0))
    )


--consolidate w/ signAt functions?
variations = method()
variations (List) := ZZ => l->(
    n := 0;
    last := 0;
    scan(l, x -> if x =!=0 then (
	    if last < 0 and x > 0 or last > 0 and x < 0 then n = n+1;
	    last = x;
	    )
	);
    n
    )


traceForm = method()
traceForm (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian R then error "Error: Expected Artinian ring";    
    B := basis R;
    K := coefficientRing R;

    mm := substitute(contract(transpose B, f*B**B),K);--change name of mm to ?? and tr
    tr := matrix {apply(first entries B, x -> trace last regularRep x)};
    adjoint(tr*mm, source tr, source tr)
    )

traceForm1 = method()
traceForm1 (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected Artinian ring";
    B := first entries basis R;
    
    matrix table(B,B,(g,h)->trace last regularRep(f*g*h))
    )--this is BAD

traceFormSignature = method()
traceFormSignature (RingElement) := Sequence => f->(
    R := ring f;
    if not isArtinian R then error "Expected Artinian ring";
    K := coefficientRing R;
    
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
    TrF := traceForm(f) ** S;
    IdZ := S_0 * id_(S^(numgens source TrF));
    ch := det(TrF - IdZ);  --use charPoly(TrF)
    << "The trace form S_f with f = " << f << 
      " has rank " << rank(TrF) << " and signature " << 
      numPosRoots(ch) - numNegRoots(ch) << endl
    ) --no strings in output!


numRealTrace = method()
numRealTrace (RingElement) := ZZ => f->() --Empty for now

numRealTrace (List) := ZZ => F->() --Empty for now

numRealTrace (QuotientRing) := ZZ => R->(
    --CONSIDER: input for trace stuff quotientRing/RingElement?
    if not isArtinian R then error "Expected Artinian ring";
    K := coefficientRing R;
        
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
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




