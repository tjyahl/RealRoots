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
	 Email=>"jordy.lopez@tamu.edu",
	 HomePage=>""},
    	{Name=>"Kelly Maluccio",
	 Email=>"kmaluccio@tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~kmaluccio"},
    	{Name=>"Frank Sottile",
	 Email=>"sottile@tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~frank.sottile/"},
	{Name=>"Thomas Yahl",
	 Email=>"Thomasjyahl@tamu.edu",
	 HomePage=>"https://math.tamu.edu/~thomasjyahl"}
	},
    Headline=>"Package for exploring, counting, and locating real solutions to polynomial systems",
    PackageImports=>{},
    PackageExports=>{},
    DebuggingMode=>true
    )


export{
    "eliminant",
    "regularRep",
    "charPoly",
    "variations",
    "SylvesterSequence",
    "numSylvester",
    "SturmSequence",
    "numRealSturm",
    "numRealRoots",
    "numPosRoots",
    "numNegRoots",
    "realRootIsolation",
    "derivSequence",
    "BudanFourierBound",
    "traceForm",
    "traceFormSignature",
    "numRealTrace"
    }


----------------------------
--METHODS FOR INTERNAL USE--
----------------------------

--Check that a ring is a univariate polynomial ring over a field of characteristic zero 
----better naming?
----worry about more interesting fields?
isUnivariate = method()
isUnivariate (Ring) := Boolean => R->(
    K := coefficientRing R;
    if instance(K,InexactField) then print "Warning: Computations over inexact field";
    (isPolynomialRing R) and (numgens R === 1) and (isField K) and (char K === 0)
    )


--Check that a ring is Artinian over a field of characteristic zero
isArtinian = method()
isArtinian (Ring) := Boolean => R->(
    K := coefficientRing R;
    if instance(K,InexactField) then print "Warning: Computations over inexact field";
    (isField K) and (char K===0) and (dim R===0)
    )


--Computes the sign of a real number
sign = method()
sign (RR) := ZZ => n ->(
     if n < 0 then -1 
     else if n == 0 then 0
     else if n > 0 then 1
     )


--Computes the sign of a real univariate polynomial at negative infinity
signAtNegInfinity = method()
signAtNegInfinity (RingElement) := ZZ => f->(
    sign( (if odd first degree f then -1 else 1) * leadCoefficient f )
    )


--Computes the sign of a real univariate polynomial at a given real number
signAt = method()
signAt (RingElement,RR) := ZZ => (f,r)->(
    sign( substitute(f,(ring f)_0=>r) )
    )


--Computes the sign of a real univariate polynomial at infinity
signAtInfinity = method()
signAtInfinity (RingElement) := ZZ => f->(
    sign( leadCoefficient f )
    )




--------------------
--EXPORTED METHODS--
--------------------

--Compute the eliminant in an Artinian ring with respect to f
----better naming for strategies?
----check that "Strategy" works as option name
----fix second option to use minimal polynomial/give better error
eliminant = method(Options=>{Strategy=>0})
eliminant (RingElement) := RingElement => opts->f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    
    if (opts.Strategy === 1) then (
	--This strategy computes the eliminant as the kernel of the multiplication map
	K := coefficientRing R;
    	Z := getSymbol "Z";
    	S := K(monoid [Z]);
    	phi := map(R,S,{f});
    	(ker phi)_0
        
	) else if (opts.Strategy === 2) then (
	--This strategy computes the eliminant as a characteristic polynomial when possible
	n := numgens source basis R;
    	g := charPoly(f);
    	if (first degree g === n) then g else error "Error: Eliminant not computed"
    	
	) else (
	--This strategy computes the eliminant by finding a minimal linear combination in powers of f
    	B := basis R;
    	n = numgens source B;
    	K = coefficientRing R;
	
    	Z = getSymbol "Z";
    	S = K(monoid [Z]);
    	
    	P := map(R^1,R^(n+1),(i,j)->f^j);
    	M := last coefficients(P, Monomials=>B);
    	coeffs := sub(gens ker M,K);
    	(map(S^1,S^(n+1),(i,j)->S_0^j) * coeffs)_(0,0)
	) 
    )


--Computes a matrix representation of the multiplication map determined by f
regularRep = method()
regularRep (RingElement) := Matrix => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    K := coefficientRing R;
    
    B := basis R;
    C := last coefficients(f*B,Monomials=>B);
    (B,sub(C,K))
    )


--Computes the characteristic polynomial of a matrix
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

--Computes the characteristic polynomial of the regular representation of f
charPoly (RingElement) := RingElement => f->(
    (B,mf) := regularRep(f);
    charPoly(mf)
    )


--Computes the number of sign changes in a list of real numbers
----can likely be written better
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


--Computes the Sylvester sequence of a pair (f,g)
SylvesterSequence = method()
SylvesterSequence (RingElement, RingElement) := List => (f,g)->(
    R := ring f;
    if not (ring g === R) then error "Error: Polynomials should be in the same ring";
    if not isUnivariate(R) then error "Error: Expected univariate polynomials";
    
    --'d' is a bound for the length of the Sylvester sequence:
    m := if f == 0 then 0 else first degree f;
    n := if g == 0 then 0 else first degree g;
    d := 2 + min {m,n};
    
    Syl := new MutableList from toList(0..d);
    Syl#0 = f;
    Syl#1 = g;
    scan(2..d, i -> Syl#i = -Syl#(i-2) % Syl#(i-1));
    	    
    toList Syl
    )


--Computes the difference in the number of roots of f where g is positive and where g is negative
----consider naming "numRealSylvester" for consistency with "numRealSturm" and "numRealTrace"
----letting g = 1 gives the number of real roots from the Sturm sequence
numSylvester = method()
numSylvester (RingElement, RingElement, Number, Number) := ZZ => (f, g, a, b)->(
    l := SylvesterSequence(f,diff((ring f)_0,f)*g);
    variations apply(l,h->signAt(h,a)) - variations apply(l,h->signAt(h,b))
    )


--Computes the sequence of derivatives of f
derivSequence = method()
derivSequence (RingElement) := List => f ->(
    R := ring f;
    if not isUnivariate(R) then error "Error: Expected univariate polynomial";
    if (f == 0) then error "Error: Expected nonzero polynomial";
    
    t := R_0;
    d := first degree f;
    apply(d+1, i -> diff(t^i,f))
    )


--Computes the difference in variations of the derivative sequence at specified values
BudanFourierBound = method()
BudanFourierBound (RingElement) := ZZ => f->( 
    l := derivSequence f;
    variations apply(l,signAtNegInfinity) - variations apply(l,signAtInfinity)
    )


BudanFourierBound (RingElement,Number,Number) := ZZ => (f,a,b)->(
    l := derivSequence f;
    variations apply(l,g->signAt(g,a)) - variations apply(l,g->signAt(g,b))
    )


BudanFourierBound (RingElement,Number,InfiniteNumber) := ZZ => (f,a,b)->(
    l := derivSequence f;
    variations apply(l,g->signAt(g,a)) - variations apply(l,g->signAtInfinity(g))
    )


BudanFourierBound (RingElement,InfiniteNumber,Number) := ZZ => (f,a,b)->(
    l := derivSequence f;
    variations apply(l,g->signAtNegInfinity(g)) - variations apply(l,g->signAt(g,b))
    )


--Computes the Sturm sequence of f via a Sylvester sequence
SturmSequence = method()
SturmSequence (RingElement) := List => f->(
    if (f == 0) then error "Error: Expected nonzero polynomial";
    R := ring f;
    x := R_0;
    SylvesterSequence(f,diff(x,f))
    )
   


--Computes the difference in variations of the Sturm sequence at specified values
----make it clear in documentation how infinity/-infinity works (because M2 doesn't do "-infinity")
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


numRealSturm (RingElement,InfiniteNumber,InfiniteNumber) := ZZ => (f,a,b)->(
    l := SturmSequence f;
    variations apply(l,g->signAtNegInfinity(g)) - variations apply(l,g->signAtInfinity(g))
    )


--Computes the number of real/positive/negative solutions to a real univariate polynomial
----consolidate methods for each of these with options?
numRealRoots = method()
numRealRoots (RingElement) := ZZ => f->(
    numRealSturm(f,infinity,infinity)
    )


numPosRoots = method()
numPosRoots (RingElement) := ZZ => f->(
    numRealSturm(f,0,infinity)
    )


numNegRoots = method()
numNegRoots (RingElement) := ZZ => f->(
    numRealSturm(f,infinity,0)
    )


--Uses Sturm sequence and a bisection method to isolate real solutions to a real univariate polynomial within a tolerance
----better naming?
realRootIsolation = method()
realRootIsolation (RingElement,RR) := List => (f,eps)->(
    R := ring f;
    if not isUnivariate(R) then error "Error: Expected univariate polynomial";
    l := SturmSequence(f);
    M :=   --how to find such bound? 
    L :=
    
    while (max apply(L, I -> I#1 - I#0 > eps)
	 or numRealRootsf(f,I) > 0) do (
	 
	 for (I in L) do(
	     drop(1,L);    	    	 
    )
    )

--another possibility

realRootIsolation = method()
realRootIsolation (RingElement) := List => f->(
    R := ring f;
    if not isUnivariate(R) then error "Error: Expected univariate polynomial";
    L := {(0,0,f)};
    Isol := { };
    d := degree f;
    x := R_0;
    
    
    while L != { } do(
	for c in ZZ and k in ZZ do 
	q := 2^(k*n)*sub(f,x=>(x+c/2^k));
	select (c,k,q) in L and remove (c,k,q) from L
	if sub(f,{x=>0}) == 0 then     --need to fix this
	q := q/x;
	n := n-1; --rational root found
	append(Isol,(c,k,0));
	
	
	v := numRealSturm((x+1)^n*sub(q,{x=> 1/(x+1)}));
	if v == 1 then
	    append(Isol,(c,k,1));
	if v > 1 then
	    append(L, (2*c, k+1, 2^n*sub(q,x=>x/2)));
	    append(L, (2*c+1, k+1, 2^n*sub(q,x=>(x+1)/2)));
	    
       	toList L
	)
    )
    


--Computes the trace form of f in an Artinian ring
----change names? mm? tr?
----change the substitute(contract(...)) business
traceForm = method()
traceForm (RingElement) := RingElement => f->(
    R := ring f;
    if not isArtinian R then error "Error: Expected Artinian ring";    
    B := basis R;
    K := coefficientRing R;

    mm := substitute(contract(transpose B, f*B**B),K);
    tr := matrix {apply(first entries B, x -> trace last regularRep x)};
    adjoint(tr*mm, source tr, source tr)
    )


--Computes the rank and signature of the trace form of f
----change name
----change output
----use charpoly below
traceFormSignature = method()
traceFormSignature (RingElement) := Sequence => f->(
    R := ring f;
    if not isArtinian R then error "Expected Artinian ring";
    K := coefficientRing R;
    
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
    TrF := traceForm(f) ** S;
    IdZ := S_0 * id_(S^(numgens source TrF));
    ch := det(TrF - IdZ); 
    << "The trace form S_f with f = " << f << 
      " has rank " << rank(TrF) << " and signature " << 
      numPosRoots(ch) - numNegRoots(ch) << endl
    )


--Compute the number of real points of a scheme/real univariate polynomial/real polynomial system using the trace form.
----fix the below
numRealTrace = method()
numRealTrace (QuotientRing) := ZZ => R->(
    if not isArtinian R then error "Expected Artinian ring";
    K := coefficientRing R;
        
    Z := getSymbol "Z";
    S := K(monoid [Z]);
    
    TrF := traceForm(1_R) ** S;
    IdZ := Z * id_(S^(numgens source TrF));
    ch := det(TrF - IdZ);
    numPosRoots(ch) - numNegRoots(ch)
    )


numRealTrace (RingElement) := ZZ => f->(
    R := ring f;
    numRealTrace(R/f)
    )


numRealTrace (List) := ZZ => F->(
    I := ideal F;
    R := ring I;
    numRealTrace(R/I)
    )





beginDocumentation()
document {
	Key => RealRoots,
	Headline =>"Package for exploring counting and locating real solutions to polynomial systems",
	"The purpose of this package is to provide tools for elimination and solving, with a particular emphasis
	on counting and isolating real zeros of ideals in QQ[X].",
	}

document {
	Key => {(eliminant, RingElement),eliminant},
	Usage => "eliminant(f)",
	Inputs => {"f"},
	Outputs => { RingElement => { "the eliminant of", TT "f", "with respect to the polynomial ring in one variable", TT "Z"}},
	PARA {"This computes the eliminant of an element f of an Artinian ring R and returns a polynomial in Z"},
	EXAMPLE lines ///
	    	R = QQ[x,y]
		F = {y^2-x^2-1,x-y^2+4*y-2}
		I = ideal F
		S = R/I
		eliminant(x)
	       	eliminant(y)	      
	 	 ///,
	SeeAlso => {"eliminant1", "eliminant2"}
     	}

document {
	Key => {(regularRep, RingElement),regularRep},
	Usage => "regularRep(f)",
	Inputs => {"f"},
	Outputs => { Matrix => { "the matrix of the linear map defined by multiplication by", TT "f", "in terms of the standard basis of a finite-dimensional k-vector space", TT "A" }},
	PARA {"This command gives the matrix of the linear map defined by multiplication by f in terms of the standard basis of a finite-dimensional k-vector space A" },
	EXAMPLE lines ///
		 R = QQ[x,y]
		 F = {y^2-x^2-1,x-y^2+4*y-2}
		 I = ideal F
		 S = R/I
		 regularRep(y)
	 	 ///--,
--	SeeAlso => {"", ""}
     	}

document {
	Key => {(charPoly, Matrix),charPoly},
	Usage => "charPoly(M)",
	Inputs => {"M"},
	Outputs => { RingElement => { "the characteristic polynomial of", TT "M"}},
	PARA {"This computes the characteristic polynomial of M"},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 F = {y^2-x^2-1,x-y^2+4*y-2}
		 I = ideal F
		 S = R/I
		 M = regularRep(y)
		 charPoly(M)
	 	 ///,
 --	SeeAlso => {"",""}
     	}

 document {
	Key => {(SylvesterSequence, RingElement, RingElement),SylvesterSequence},
	Usage => "SylvesterSequence(f,g)",
	Inputs => {"f","g"},
	Outputs => { List => { "the Sylvester sequence of", TT "f", "and",TT "g"}},
	PARA {"This computes the Sylvester sequence of two univariate polynomials f and g in the same ring"},
	EXAMPLE lines ///
	         R = QQ[t]
		 f = (t+1)*(t+2)
		 g = (t+2)
		 SylvesterSequence(f,g)
	 	 ///,
	SeeAlso => {"numSylvester"}
     	}
    
    document {
	Key => {(numSylvester, RingElement, RingElement, Number, Number),numSylvester},
	Usage => "numSylvester(f,g,a,b)",
	Inputs => {"f","g","a","b"},
	Outputs => { ZZ => {"the difference between number of roots of",TT "f","when",TT "g",
		"is positive and when g is negative"}},--check
	PARA {"This computes the difference in variations of the Sylvester sequence of", TT "f"," and ",TT "f'g"," at the values", TT "a"," and ", TT "b"},
	EXAMPLE lines ///
	    	 R = QQ[t]
		 f = (t-2)*(t-1)*(t+3)
		 g = t+1
		 a = -5
		 b = 4
		 numSylvester(f,g,a,b)
	 	 ///,
	SeeAlso => {"SylvesterSequence"}
     	}

document {
	Key => {(SturmSequence, RingElement),SturmSequence},
	Usage => "SturmSequence(f)",
	Inputs => {"f"},
	Outputs => { List => { "the Sturm sequence of", TT "f"}},
	PARA {"This computes the Sturm Sequence of a univariate polynomial f"},
	EXAMPLE lines ///
	 	 R = QQ[t]
		 f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
		 SturmSequence(f)
	 	 ///,
	SeeAlso => {"numRealSturm"}
     	}

document {
	Key => {(numRealSturm, RingElement),numRealSturm},
	Usage => "numRealSturm(M)",
	Inputs => {"f"},
	Outputs => { ZZ => { "the number of real roots of a univariate polynomial", TT "f"," not counting multiplicity"}},
	PARA {"This computes the difference in variation of the Sturm sequence of", TT "f", "at the values", TT "a"," and ",TT "b"},
	EXAMPLE lines ///
	    	 R = QQ[t]
		 f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
		 numRealSturm(f)
	 	 ///,
	SeeAlso => {"numPosRoots", "numNegRoots"}
     	}

document {
    	Key => {(numPosRoots, RingElement), numPosRoots},
	Usage => "numPosRoots(f)",
	Inputs => {"f"},
	Outputs => { ZZ => {"the number of positive real roots of a polynomial", TT "f"}},
	PARA {"This uses Sturm sequences to compute the number of positive real roots of a polynomial f with real coefficients"},
	EXAMPLE lines ///
	        R = QQ[t]
	        f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
	        numPosRoots(f)
		///,
	SeeAlso => {"numNegRoots","numRealSturm"}
	}
    
document {
    	Key => {(numNegRoots, RingElement), numNegRoots},
	Usage => "numNegRoots(f)",
	Inputs => {"f"},
	Outputs => { ZZ => {"the number of negative real roots of a polynomial", TT "f"}},
	PARA {"This uses Sturm sequences to compute the number of negative real roots of a polynomial f with real coefficients"},
	EXAMPLE lines ///
	        R = QQ[t]
	        f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
	        numNegRoots(f)
		///,
	SeeAlso => {"numPosRoots","numRealSturm"}
	}
    
document {
    	Key => {(variations, List),variations},
	Usage => "variations(l)",
	Inputs => {"l"},
	Outputs => { ZZ => { "the number of sign changes in a sequence", TT "l" }},
	PARA {"This computes the number of changes of sign in a sequence l"},
	EXAMPLE lines ///
	         R = QQ[t]
		 f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
		 c =  SturmSequence(f)
		 variations(c)
	 	 ///,
--	SeeAlso => {}
     	}
    
    document {
	Key => {(BudanFourierBound, RingElement),BudanFourierBound}, --maybe we can call it bfBound (Budan-Fourier bound?)
	Usage => "BudanFourierBound(f))",
	Inputs => {"f"},
	Outputs => { ZZ => { "a sharp upper  bound for the number of real roots of a univariate polynomial", TT "f"}},
	PARA {"This computes a sharp upper bound for the number of real roots of a univariate polynomial f"},
	EXAMPLE lines ///
	         R = QQ[t]
		 f = 45 - 39*t - 34*t^2+38*t^3-11*t^4+t^5
		 BudanFourierBound(f)
	 	 ///,
--	SeeAlso => {"", ""}
     	}
    
document {
	Key => {(traceForm, RingElement),traceForm},
	Usage => "traceForm(f)",
	Inputs => {"f"},
	Outputs => { RingElement => { "the trace quadratic form of", TT "f" }},
	PARA {"This computes the trace quadratic form of an element f in an Artinian ring"},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 traceForm(x-y)
	 	 ///,
	SeeAlso => {"traceFormSignature", "numRealTrace"} --need to update this to add traceForm1 as another input? or its own documentation?
     	}

document {
	Key => {(traceFormSignature, RingElement),traceFormSignature},
	Usage => "traceFormSignature(f)",
	Inputs => {"f"},
	Outputs => { Sequence => { "the rank and signature of the trace quadratic form of", TT "f" }},
	PARA {"This computes the rank and signature of the trace quadratic form of an element f in an Artinian ring of characteristic zero"},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 traceFormSignature(x-y+1)
	 	 ///,
	SeeAlso => {"traceForm", "numRealTrace"}
     	}

document {
	Key => {(numRealTrace, QuotientRing),numRealTrace},
	Usage => "numRealTrace(R)",
	Inputs => {"R"},
	Outputs => { ZZ => { "the number of real points of Spec", TT "R" }},
	PARA {"This computes the number of real points of Spec(R) where R is an Artinian ring with characteristic zero"},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 F = {y^2-x^2-1,x-y^2+4*y-2}
		 I = ideal F
		 S = R/I
		 numRealTrace(S)
	 	 ///,
	SeeAlso => {"traceForm"} --need to update this documentation to allow for multiple inputs
     	}
end

--Put notes, examples, etc down here. It won't go in the actual package.

--Notes:
----
----1) Remember to include tests for the code in documentation.
----2) How do we make sure that polynomials f and g have real coefficients?
----3) Optional inputs for certain methods? Update this in the code and in documentation
----4) EXAMPLES to put in documentation: 
         ----R = QQ[x,y], F = {x^5-49/95*x^3*y+y^6, y^5-49/95*x*y^3+x^6} (AG class example) and F = {y^2-x^2-1,x-y^2+4*y-2} (Frank's example)
----
----




