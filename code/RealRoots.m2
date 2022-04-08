--RealRoots.m2
newPackage(
    "RealRoots",
    Version=>"0.1",
    Date=>"Oct 9, 2020",
    Authors=>{
     	{Name=>"Jordy Lopez Garcia",
	 Email=>"jordy.lopez@tamu.edu",
	 HomePage=>"https://www.github.com/jordylopez27"},
    	{Name=>"Kelly Maluccio",
	 Email=>"keleburke@aggienetwork.com",
	 HomePage=>"https://www.github.com/kmaluccio"},
    	{Name=>"Frank Sottile",
	 Email=>"sottile@tamu.edu",
	 HomePage=>"https://www.math.tamu.edu/~frank.sottile/"},
	{Name=>"Thomas Yahl",
	 Email=>"thomasjyahl@tamu.edu",
	 HomePage=>"https://www.github.com/tjyahl"}
	},
    Headline=>"Package for symbolically exploring, counting, and locating real solutions to general polynomial systems",
    PackageImports=>{},
    PackageExports=>{},
    DebuggingMode=>true
    )


export{
    --methods
    "eliminant",
    "regularRep",
    "characteristicPolynomial",
    "variations",
    "SylvesterSequence",
    "numSylvester",
    "SturmSequence",
    "numSturm",
    "realRootIsolation",
    "BudanFourierBound",
    "traceForm",
    "numTrace",
    "rationalUnivariateRep",
    "HurwitzMatrix",
    "HurwitzDeterminant",
    "isHurwitzStable",
    --"variable",
    --"signAt",
    --"derivSequence",
    --"sign",
    --options
    "Multiplicity"
    }


----------------------------
--METHODS FOR INTERNAL USE--
----------------------------

--Check that a polynomial is univariate
isUnivariatePolynomial = method()
isUnivariatePolynomial (RingElement) := Boolean => f->(
    #(support f) <= 1
    )

--Determines the variable of a univariate polynomial
variable = method()
variable (RingElement) := RingElement => f->(
    if not isUnivariatePolynomial(f) then error "Error: Expected univariate polynomial";
    S := support f;
    if S === {} then (ring f)_0 else S#0
    )

variable (Ideal) := RingElement => I->(
    S := support I;
    if S === {} then (ring I)_0 else S#0
    )


--Check that a ring is zero-dimensional
isArtinian = method()
isArtinian (Ring) := Boolean => R->(
    if instance(coefficientRing R,InexactField) then print "Warning: Computations over inexact field";
    dim R === 0
    )

        
--Computes the sign of a real number
sign = method()
for A in {ZZ,QQ,RR} do
sign (A) := ZZ => n->(
     if n < 0 then -1 
     else if n == 0 then 0
     else if n > 0 then 1
     )


--Computes the sign of a real univariate polynomial at a given real number
signAt = method()
for A in {ZZ,QQ,RR} do
signAt (RingElement,A) := ZZ => (f,r)->(
    sign(substitute(f,{variable f => r}))
    )

signAt (RingElement,InfiniteNumber) := ZZ => (f,r)->(
    if (r>0) then (
	sign(leadCoefficient f)
	) else (
	sign((if odd first degree f then -1 else 1)*(leadCoefficient f))
	)
    )


--Computes the sequence of derivatives of f
derivSequence = method()
derivSequence (RingElement) := List => f->(
    if not isUnivariatePolynomial(f) then error "Error: Expected univariate polynomial.";
    if (f == 0) then error "Error: Expected nonzero polynomial";
    
    t := variable f;
    d := first degree f;
    apply(d+1, i -> diff(t^i,f))
    )

--------------------
--EXPORTED METHODS--
--------------------

--Compute the eliminant of 'f' in the quotient ideal defined by 'I'
----better naming for strategies?
----fix second option to use minimal polynomial/give better error
eliminant = method(Options=>{Strategy=>0})
eliminant (RingElement,Ideal) := RingElement => opts->(f,I)->(
    R := ring f;
    if not (ring I === R) then error "Error: Expected polynomial and ideal of the same ring";
    eliminant(sub(f,R/I))
    )
    
eliminant (RingElement) := RingElement => opts->f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    
    if (opts.Strategy === 0) then (
	--This strategy computes the eliminant as the kernel of the multiplication map
	K := coefficientRing R;
    	Z := getSymbol "Z";
    	S := K(monoid [Z]);
    	phi := map(R,S,{f});
    	(ker phi)_0
        
	) else if (opts.Strategy === 1) then (
      	--This strategy computes the eliminant by finding a minimal linear combination in powers of f
    	B := basis R;
    	n := numgens source B;
	
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
regularRep (RingElement,Ideal) := Matrix => (f,I)->(
    R := ring f;
    if not (ring I === R) then error "Error: Expected polynomial ring and ideal of the same ring";
    regularRep(sub(f,R/I))
    )

regularRep (RingElement) := Matrix => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected element of Artinian ring";
    K := coefficientRing R;
    
    B := basis R;
    C := last coefficients(f*B,Monomials=>B);
    (B,sub(C,K))
    )


--Computes the characteristic polynomial of a matrix.
characteristicPolynomial = method(Options => {Variable => "Z"})
characteristicPolynomial (Matrix) := RingElement => opts->M->(
    n := numgens source M;
    if not (numgens target M === n) then error "Error: Expected a square matrix";
    
    K := ring M; 
    Z := opts.Variable;
    S := K(monoid [Z]);

    IdZ := S_0*id_(S^n);
    det(IdZ - M)
    )

--Computes the characteristic polynomial of the regular representation of f
characteristicPolynomial (RingElement,Ideal) := RingElement => opts->(f,I)->(
    R := ring f;
    if not (ring(I) === R) then error "Error: Expected polynomial ring and ideal of the same ring";
    characteristicPolynomial(sub(f,R/I))
    )

characteristicPolynomial (RingElement) := RingElement => opts->f->(
    (B,mf) := regularRep(f);
    characteristicPolynomial(mf)
    )


--Computes the number of sign changes in a list of real numbers
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


--Computes the difference in variations of the derivative sequence at specified values
BudanFourierBound = method()
for A in {Number,InfiniteNumber} do 
for B in {Number,InfiniteNumber} do
BudanFourierBound (RingElement,A,B) := ZZ => (f,a,b)->(
    if not isUnivariatePolynomial(f) then error "Error: Expected univariate polynomial.";
    if not (a<b) then error "Error: Expected non-empty interval";
    l := derivSequence f;
    variations apply(l,g->signAt(g,a)) - variations apply(l,g->signAt(g,b))
    )

BudanFourierBound (RingElement) := ZZ => f->(
    BudanFourierBound(f,-infinity,infinity)
    )


--Computes the Sylvester sequence of a pair (f,g)
----This isn't actually the Sylvester sequence since we divide by gcd(f,g)
SylvesterSequence = method()
SylvesterSequence (RingElement, RingElement) := List => (f,g)->(
    R := ring f;
    if not (ring g === R) then error "Error: Polynomials should be in the same ring";
    if not (isUnivariatePolynomial(f) and isUnivariatePolynomial(g)) then error "Error: Expected univariate polynomials";
    if not (variable f == variable g) then error "Error: Expected polynomials in the same variable";
    
    --dividing out common factors
    ----gcd only works over ZZ and QQ?
    h := gcd(f,g);
    f = sub(f/h,R);
    g = sub(g/h,R);
        
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
----letting g = 1 gives the number of real roots from the Sturm sequence
numSylvester = method()
for A in {Number,InfiniteNumber} do 
for B in {Number,InfiniteNumber} do
numSylvester (RingElement,RingElement,A,B) := ZZ => (f, g, a, b)->(
    if not (a<b) then error "Error: Expected non-empty interval";
    l := SylvesterSequence(f,diff(variable f,f)*g);
    variations apply(l,h->signAt(h,a)) - variations apply(l,h->signAt(h,b))
    )

numSylvester (RingElement,RingElement) := ZZ => (f,g)->(
    numSylvester(f,g,-infinity,infinity)
    )


--Computes the Sturm sequence of f via a Sylvester sequence
SturmSequence = method()
SturmSequence (RingElement) := List => f->(
    if (f == 0) then error "Error: Expected nonzero polynomial";
    SylvesterSequence(f,diff(variable f,f))
    )


--Computes the difference in variations of the Sturm sequence at specified values
numSturm = method(Options=>{Multiplicity=>false})
for A in {Number,InfiniteNumber} do
for B in {Number,InfiniteNumber} do
numSturm (RingElement,A,B) := ZZ => opts->(f,a,b)->(
    R := ring f;
    h := gcd(f,diff(R_0,f));
    f = sub(f/h,R);
    n := numSylvester(f,1_R,a,b);
    if (opts.Multiplicity==true) then (
	while(first degree h > 0) do (
	    n = n + numSturm(h,a,b,opts);
	    h = gcd(h,diff(R_0,h));
	    )
	);
    n
    )

numSturm (RingElement) := ZZ => opts->f->( 
    numSturm(f,-infinity,infinity,opts)
    )


--Uses Sturm sequence and a bisection method to isolate real solutions to a real univariate polynomial within a tolerance
realRootIsolation = method()
realRootIsolation (RingElement,Number) := List => (f,r)->(
    if instance(r,InexactNumber) then error "Error: Expected integer or rational number";
    if not r > 0 then error "Error: Expected positive integer or positive rational number";
    
    if not isUnivariatePolynomial(f) then error "Error: Expected univariate polynomial";
    R := ring f;
    
    f = sub(f/gcd(f,diff(variable f,f)),R);
    
    if (numSturm(f)>0) then (
	l := SturmSequence(f);
	
	--bound for real roots
	C := (listForm f)/last;
    	M := (sum(C,abs))/(leadCoefficient f);
	
	L := {{-M,M}};
	midp := 0;
	v := new MutableHashTable from {M=>variations apply(l,g->signAt(g,M)),-M=>variations apply(l,g->signAt(g,-M))};
	
	while (max apply(L,I-> I#1-I#0) > r) or (max apply(L,I-> v#(I#0)-v#(I#1)) > 1) do (
	    for I in L do (
		midp = (sum I)/2;
		v#midp = variations apply(l,g->signAt(g,midp));
		L = drop(L,1);
		if (v#(I#0)-v#midp > 0) then (
		    L = append(L,{I#0,midp})
		    );
		if (v#midp-v#(I#1) > 0) then (
		    L = append(L,{midp,I#1})
		    )
		)
	    );
	L
	) else (
	{}
	)
    )
    
    
--Computes the trace form of f in an Artinian ring 
----use subrings in case of extra variables
traceForm = method()
traceForm (RingElement,Ideal) := Matrix => (f,I)->(
    R := ring f;
    if not (ring I === R) then error "Error: Expected RingElement and Ideal in same Ring";
    traceForm(sub(f,R/I))
    )

traceForm (RingElement) := Matrix => f->(
    R := ring f;
    if not isArtinian(R) then error "Error: Expected zero-dimensional ring";
    B := basis R;
    K := coefficientRing R;

    mm := sub(last coefficients(f*B**B,Monomials=>B),K);
    tr := matrix {apply(first entries B, x -> trace last regularRep x)};
    adjoint(tr*mm, source tr, source tr)
    )


--Compute the number of real points of a scheme/real univariate polynomial/real polynomial system using the trace form.
numTrace = method()
numTrace (RingElement) := ZZ => f->(
    R := ring f;
    numTrace(R/f)
    )

numTrace (List) := ZZ => F->(
    I := ideal F;
    R := ring I;
    numTrace(R/I)
    )

numTrace (Ideal) := ZZ=> I->(
    R := ring I;
    numTrace(R/I)
    )

numTrace (QuotientRing) := ZZ=> R->(
    if not isArtinian R then error "Expected Artinian ring";
    K := coefficientRing R;
    
    ch := characteristicPolynomial(traceForm(1_R));
    chNeg := sub(ch,(ring ch)_0=>-(ring ch)_0);
    numSturm(ch,0,infinity,Multiplicity=>true) - numSturm(chNeg,0,infinity,Multiplicity=>true)
    )


--Computes the Rational Univariate Representation of a zero-dimensional ideal
rationalUnivariateRep = method()
rationalUnivariateRep (Ideal) := List => I->(
    R := ring I;
    S := R/I;
    if not isArtinian(S) then error "Error: Expected I to be a zero-dimensional ideal";
    d := rank traceForm(1_S);
    
    i := 1;
    X := gens R;
    n := #X;
    while (i < n*(binomial(d,2))) do (
    	l := sum(X,apply(n,k->i^k),(a,b)->a*b);
	m := last regularRep(sub(l,S));
	f := characteristicPolynomial(m);
	
	fbar := f/gcd(f,diff((support f)_0,f));
	fbar = sub(fbar,ring f);
	print(first degree fbar);
	if (first degree fbar === d) then return toList(f,l);
	i = i+1
	)
    )

--Computes a Hurwitz matrix of order k
HurwitzMatrix = method()
HurwitzMatrix (RingElement,ZZ) := Matrix => (f,k)->(
   
    if k <= 0 then error "Error: Expected positive integer in second input.";  
	
    d := (degree f)_0;
    
    if k > d then error "Error: k is at most d.";
    
    x := variable f;
    C := toList reverse apply(0..d, i -> coefficient(x^i,f));
    zerocoeff := (l,a) -> (if a < 0 or d-a < 0 then 0 else l#(d-a));
    Z := toList apply(1..d, i -> zerocoeff(C,d+1-2*i));
    
    --here we generate the d x d matrix
    if k == 1 then matrix{{C#1}} else (
    L := for j from 2 to d when j < d + 1 list toList apply(1..d, i -> zerocoeff(C,d+j-2*i));
    T := join({Z},L);
    M := matrix T; 
    
    --now we find the submatrices of the d x x matrix
    I := submatrix'(M,{k..d},{k..d})
    )
    )

--Computes a Hurwitz matrix of order k and then computes its determinant
HurwitzDeterminant = method()
HurwitzDeterminant (RingElement,ZZ) := RR => (f,k)->(
    R := ring f;
   
    if k < 0 then error "Error: Expected non-negative integer in second input.";  
    if k == 0 then 1_QQ else (
	
    d := (degree f)_0;
    x := R_0;
    C := toList reverse apply(0..d, i -> coefficient(x^i,f));
    zerocoeff := (l,a) -> (if a < 0 or d-a < 0 then 0 else l#(d-a));
    Z := toList apply(1..d, i -> zerocoeff(C,d+1-2*i));
    
    --here we generate the d x d matrix
    L := for j from 2 to d when j < d + 1 list toList apply(1..d, i -> zerocoeff(C,d+j-2*i));
    T := join({Z},L);
    M := matrix T; 
    
    --now we find the minors
    I := minors(k,M);
    I_0
    )
    )

--Determines whether or not a univariate polynomial of degree >=1 and leading coefficient > 0
isHurwitzStable = method()
isHurwitzStable (RingElement) := Boolean => f->(
    R := ring f;
    d := (degree f)_0;
    if d < 1 then print "Warning: polynomial must be of degree 1 or higher.";
    if leadCoefficient f <= 0 then print "Warning: leading coefficient must be positive.";
    S := for i from 2 to d when i < d + 1 list HurwitzDeterminant(f,i); 
    T := apply(S, i -> sign(i));
    sum T == d-1 
    )

--------------------
---DOCUMENTATION----
--------------------

beginDocumentation()
document {
	Key => RealRoots,
	Headline => "Package for exploring, counting and locating real solutions to polynomial systems",
	"The purpose of this package is to provide general tools for elimination and solving systems of polynomial equations.", -- with a particular emphasis
	--on counting and isolating real zeros of ideals in ",TEX///$\mathbb{Q}[x]$///,".",
	}

document {
	Key => {eliminant,(eliminant, RingElement),(eliminant,RingElement,Ideal),[eliminant,Strategy]},
	Headline => "the eliminant of a univariate polynomial of an Artinian ring",
	Usage => "eliminant(f)",
	Inputs => {
	    RingElement => "f" => {"a univariate polynomial of an Artinian ring"},
	    },
	Outputs => { RingElement => {"the eliminant of", TT "f", "with respect to a polynomial ring in one variable", TT "Z"}},
	PARA {"This computes the eliminant of ", TT "f", " of an Artinian ring ", TT "R", " and returns a polynomial in ",TT "Z","."},
	EXAMPLE lines ///
	    	R = QQ[x,y]
		F = {y^2 - x^2 - 1,x - y^2 + 4*y - 2}
		I = ideal F
		S = R/I
		eliminant(x)
	       	eliminant(y)	      
	 	 ///,
     	}

document {
	Key => {regularRep,(regularRep, RingElement, Ideal), (regularRep, RingElement)},
	Headline => "the regular representation of a rational polynomial",
	Usage => "regularRep(f,I)",
	Inputs => {
	    RingElement => "f"=> {"a rational polynomial"},
	    Ideal => "I" => {"a zero-dimensional ideal in the same ring as ", TT "f"},
	    },
	Outputs => {Matrix => {"the matrix of the linear map defined by multiplication by ", TT "f", " in terms of the standard basis of a finite-dimensional k-vector space", TT "I" }},
	PARA {"This command gives the matrix of the linear map defined by multiplication by ", TT "f", " in terms of the standard basis of a finite-dimensional k-vector space ", TT "I","."},
	EXAMPLE lines ///
		 R = QQ[x,y]
		 F = {y^2 - x^2 - 1,x - y^2 + 4*y - 2}
		 I = ideal F
		 regularRep(y,I)
		 S = R/I
		 regularRep(y)
	 	 ///,
     	}

document {
	Key => {characteristicPolynomial, (characteristicPolynomial, Matrix),(characteristicPolynomial,RingElement),(characteristicPolynomial,RingElement,Ideal),[characteristicPolynomial,Variable]},
	Headline => "the characteristic polynomial of a matrix and the characteristic polynomial of the regular representation of a polynomial",
	Usage => "characteristicPolynomial(M)
	          characteristicPolynomial(f)
		  characteristicPolynomial(f,I)",
	Inputs => {
	    Matrix => "M" => {"a square matrix"},
	    RingElement => "f" => {"a polynomial"},
	    Ideal => "I"  => {"(optional) a zero-dimensional ideal"},
	    },
	Outputs => {RingElement => {"the characteristic polynomial of ", TT "M", " and the characteristic polynomial of the regular representation of ", TT "f"}},
	PARA {"This computes the characteristic polynomial of ", TT "M", " and the characteristic polynomial of the regular representation of ", TT "f","."},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 M = matrix{{2,1},{1,-1}}
		 characteristicPolynomial(M)
		 ///,
    	PARA {"We can also change the variable name, as we show below."},
	EXAMPLE lines ///
	         characteristicPolynomial(M,Variable => "x")
		 ///,
       	EXAMPLE lines ///
		 F = {y^2 - x^2 - 1,x - y^2 + 4*y - 2}
		 I = ideal F
		 S = R/I
		 N = last regularRep(y)
		 characteristicPolynomial(N)
		 ///,
     	}
--characteristicPolynomial change to characteristicPolynomial


 document {
	Key => {SylvesterSequence,(SylvesterSequence, RingElement, RingElement)},
	Headline => "the Sylvester sequence of two rational univariate polynomials",
	Usage => "SylvesterSequence(f,g)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial"},
	    RingElement => "g" => {"a rational univariate polynomial in the same variable as ", TT"f"},
	    },
	Outputs => { List => { "the Sylvester sequence of ", TT "f", " and ",TT "g"}},
	PARA {"This computes the Sylvester sequence of two rational univariate polynomials ", TT "f", " and ", TT "g", " in the same ring."},
	EXAMPLE lines ///
	         R = QQ[t]
		 f = (t + 1)*(t + 2)
		 g = t + 2
		 SylvesterSequence(f,g)
	 	 ///,
	SeeAlso => {"numSylvester"}
     	}
    
document {
	Key => {numSylvester,(numSylvester, RingElement, RingElement, Number,Number),(numSylvester, RingElement, RingElement, InfiniteNumber,InfiniteNumber),(numSylvester, RingElement, RingElement, InfiniteNumber,Number),(numSylvester, RingElement, RingElement, Number,InfiniteNumber),(numSylvester,RingElement,RingElement)},
	Headline => "the difference in variations of the Sylvester sequence of two rational univariate polynomials",
	Usage => "numSylvester(f,g,a,b)
	          numSylvester(f,g)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial"},
	    RingElement => "g" => {"a rational univariate polynomial"},
	    Number => "a" => {"(optional) the lower bound of the interval"},
	    Number => "b" => {"(optional) the upper bound of the interval"},
	    },
	Outputs => { ZZ => {"the difference between number of roots of ",TT "f"," when ",TT "g",
		"is positive and when g is negative"}},
	PARA {"This computes the difference in variations of the Sylvester sequence of ", TT "f"," and ",TT "f'g"," on the interval ",TEX///$(a,b]$///,"."},
	EXAMPLE lines ///
	    	 R = QQ[t]
		 f = (t - 2)*(t - 1)*(t + 3)
		 g = t + 1
		 a = -5
		 b = 4
		 numSylvester(f,g,a,b)
	 	 ///,
	SeeAlso => {"SylvesterSequence"}
     	}

document {
	Key => {SturmSequence,(SturmSequence, RingElement)},
	Headline => "the Sturm sequence of a rational univariate polynomial",
	Usage => "SturmSequence(f)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial"},
	    },
	Outputs => { List => {"the Sturm sequence of", TT "f"}},
	PARA {"This computes the Sturm Sequence of a univariate polynomial ", TT "f","."},
	EXAMPLE lines ///
	 	 R = QQ[t]
		 f = 45 - 39*t - 34*t^2 + 38*t^3 - 11*t^4 + t^5
		 roots f
		 SturmSequence(f)
	 	 ///,
	SeeAlso => {"numSturm"}
     	}

document {
    	Key => {"Multiplicity(RealRoots)", [numSturm, Multiplicity]},
	PARA {"This is an optional input for counting roots with multiplicity."}
    }

document {
    	Key => {"Multiplicity"},
	PARA {"This is a symbol for counting roots with multiplicity."}
    }

document {
	Key => {numSturm,(numSturm, RingElement, Number,Number), (numSturm,RingElement,Number,InfiniteNumber), (numSturm, RingElement,InfiniteNumber,Number), (numSturm, RingElement,InfiniteNumber,InfiniteNumber),(numSturm,RingElement)},
	Headline => "the number of real roots of a rational univariate polynomial, not counting multiplicity",
	Usage => "numSturm(f,a,b)
	          numSturm(f)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial, not necessarily from a univariate polynomial ring"},
	    Number => "a" => {"a lower bound of the interval"},
	    Number => "b" => {"an upper bound of the interval"},
	    },
	Outputs => { ZZ => {"the number of real roots of ", TT "f"," not counting multiplicity in the interval ",TEX///$(a,b)$///,"."}},
	PARA {"This computes the difference in variation of the Sturm sequence of ", TT "f", ". If ", TT "a", " and ", TT "b"," are not specified, the interval will be taken from ",TEX///$\infty$///," to ",TEX///$\infty$///,"."},
	EXAMPLE lines ///
	    	 R = QQ[t]
		 f = (t - 5)*(t - 3)^2*(t - 1)*(t + 1)
		 roots f
		 numSturm(f)
		 numSturm(f,0,5)
		 numSturm(f,-2,2)
		 numSturm(f,-1,5)
	 	 ///,
	PARA {"In the above example, multiplicity is not counted, so to include it we can make the multiplicity option ",TT "true"," in the example below."},
	EXAMPLE lines ///
		numSturm(f,Multiplicity=>true)
		numSturm(f,0,5,Multiplicity=>true)
		numSturm(f,0,3,Multiplicity=>true)
		///,
	PARA {"If ", TT "a"," is an ", TT "InfiniteNumber", ", then the lower bound will be ",TEX///$\infty$///,", and if ", TT "b"," is an ", TT "InfiniteNumber", ", then the upper bound is ",TEX///$\infty$///,"."},
	EXAMPLE lines ///
	    	numSturm(f,-infinity, 0)
		numSturm(f,0,infinity)
		numSturm(f,-infinity,infinity)
		///,
	SeeAlso => {"SturmSequence"}
     	}
    
document {
    	Key => {variations,(variations, List)},
	Headline => "the number of sign changes of an ordered list of numbers",
	Usage => "variations(l)",
	Inputs => {
	    List => "l" => {" of ordered numbers"},
	    },
	Outputs => {ZZ => { "the number of sign changes in the ordered list ", TT "l" }},
	PARA {"This computes the number of sign changes in the ordered list ", TT "l","."},
	EXAMPLE lines ///
		 L = for i to 10 list random(-50,50)
		 variations(L)
	 	 ///,
     	}
    
document {
        Key => {realRootIsolation,(realRootIsolation, RingElement,Number)},
	Headline => "a list that isolates the real roots of a rational univariate polynomial",
	Usage => "realRootIsolation(f,r)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial"},
	    Number => "r" => {"a positive rational number, which determines the length of the intervals where each root is isolated"},
	    },
	Outputs => {List => {"of intervals that contain all the real roots of ", TT "f", ".  Each interval has length at most ", TT "r", 
		    " and contains a single root of ", TT "f",", not counting multiplicity."}},
	PARA {"This method uses a Sturm sequence and a bisection method to isolate real solutions of a polynomial", TT "f",
	       " to a real univariate polynomial in intervals of length at most ", TT "r"},
	EXAMPLE lines ///
	    	 R = QQ[t]
		 f = 45 - 39*t - 34*t^2 + 38*t^3 - 11*t^4 + t^5
		 realRootIsolation(f,1/2)
	 	 ///,
	SeeAlso => {"SturmSequence"}
     	}
    
document {
	Key => {BudanFourierBound, (BudanFourierBound, RingElement,Number,Number), (BudanFourierBound, RingElement, Number, InfiniteNumber), (BudanFourierBound, RingElement, InfiniteNumber, Number),(BudanFourierBound, RingElement, InfiniteNumber, InfiniteNumber),(BudanFourierBound,RingElement)},
	Headline => "a bound for the number of real roots of a univariate polynomial with rational coefficients",
	Usage => "BudanFourierBound(f, a, b)
	          BudanFourierBound(f)",
	Inputs => {
	    RingElement => "f" => {"a univariate polynomial with rational coefficients, where", TT " ring f ", "is not necessarily univariate"},
	    Number => "a" => {"(optional) the lower bound of the interval"},
	    InfiniteNumber => "a" => {"(optional) the lower bound of the interval"},
	    Number => "b" => {"(optional) the upper bound of the interval"},
	    InfiniteNumber => "b" => {"(optional) the upper bound of the interval"},
	    },
	Outputs => { ZZ => { "the bound for the number of real roots of a rational univariate polynomial", TT " f ", "in the interval ", TT "(a,b]"}},
	PARA {"This computes the bound from the Budan Fourier Theorem for the number of real roots of a rational univariate polynomial", TT " f ", "in the interval", TT "(a,b]",
	      ", counted with multiplicity. If the interval is not specified, it 
	      computes such bound on ", TEX///$(-\infty, \infty)$///,". Moreover,", TT " ring f ", "is allowed to be multivariate."},
	EXAMPLE lines ///
	         R = QQ[t]
		 f = 45 - 39*t - 34*t^2 + 38*t^3 - 11*t^4 + t^5
		 BudanFourierBound(f)
		 g = (t + 5)*(t + 3)*(t + 1)*(t - 1)^2*(t - 4)*(t - 6)
		 BudanFourierBound(g,-6,infinity)
		 BudanFourierBound(g,-1,5)
	 	 ///,
	PARA {"We also provide examples when the interval includes ", TEX///$-\infty$///," or ", TEX///$\infty$///, "."},
	EXAMPLE lines ///
	         BudanFourierBound(g,-infinity,0)
	         BudanFourierBound(g,3,infinity)
		 BudanFourierBound(g,-infinity,infinity)
		 ///
     	}
    
    --add South Texas example on Budan Fourier
    
document {
	Key => {traceForm,(traceForm, RingElement),(traceForm,RingElement,Ideal)},
	Headline => "the trace quadratic form of a rational polynomial in an Artinian ring",
	Usage => "traceForm(f)
	          traceForm(f,I),",
	Inputs => {
	    RingElement => "f" => {"a rational polynomial in an Artinian Ring"},
	    Ideal => "I" => {"the ideal generated by ", TT "f"},
	    },
	Outputs => {Matrix => {"a symmetric matrix representing the trace quadratic form of ", TT "f" , " in the standard basis of the Artinian ring"}},
	PARA {"This computes the trace quadratic form of a polynomial ", TT "f", " in an Artinian ring."},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 F = {y^2 - x^2 - 1, x - y^2 + 4*y - 2}
		 I = ideal F
		 S = R/I
		 f = y^2 - x^2 - x*y + 4
		 traceForm(f)
	 	 ///,
	SeeAlso => {"numTrace"}
     	}
    

document {
	Key => {numTrace,(numTrace, QuotientRing), (numTrace, RingElement), (numTrace, List),(numTrace,Ideal)},
        Headline => "the number of real points of the spectrum of an Artinian ring (of characteristic 0)",
	Usage => "numRealTrace(R)",
	Inputs => {
	    QuotientRing => "S" => {"an Artinian ring"},
	    RingElement => "f" => {"a rational univariate polynomial"},
	    Ideal => "I" => {"the ideal generated by ", TT "f"},
	    List => "l" => {"a system of rational univariate polynomials"},
	    },
	Outputs => { ZZ => {"the number of real points of Spec", TT "R" }},
	PARA {"This computes the number of real points of Spec", TT "R", ", where ", TT "R", " is an Artinian ring with characteristic zero"},
	EXAMPLE lines ///
	         R = QQ[x,y]
		 F = {y^2 - x^2 - 1,x - y^2 + 4*y - 2}
		 I = ideal F
		 S = R/I
		 numTrace(S)
		 ///,
	EXAMPLE lines ///
		 R = QQ[x,y]
		 I = ideal(1 - x^2*y + 2*x*y^2, y - 2*x - x*y + x^2)
		 numTrace(I)
	 	 ///,
	SeeAlso => {"traceForm"}
     	}
    
document {
        Key => {rationalUnivariateRep, (rationalUnivariateRep, Ideal)},
	Headline => "the rational univariate representation of a zero-dimensional ideal",
	Usage => "rationalUnivariateRep(I)",
	Inputs => {
	    Ideal => "I" => {"a zero-dimensional ideal"},
	    },
	Outputs => {List => {"the rational univariate representation of ",TT "I"}},
	PARA{"This computes the rational univariate representation of a zero-dimensional ideal."},
	
	EXAMPLE lines ///
	R = QQ[x,y]
	I = ideal(x*y - 1,2*x - y + 3)
	rationalUnivariateRep(I)
	///
    }
    
document {
	Key => {HurwitzMatrix,(HurwitzMatrix, RingElement, ZZ)},
	Headline => "the k x k submatrix generated by the corresponding leading principal minor of the n x n  Hurwitz matrix H of a rational univariate polynomial of degree n",
	Usage => "HurwitzMatrix(f,k)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial of degree n"},
	    ZZ => "k" => {"a nonnegative integer that determines the dimensions of a square submatrix of the n x n Hurwitz matrix of ",TT "f","."},
	    },
	Outputs => {Matrix => {"the k x k submatrix ",TEX///$H_{k}$///," generated by the corresponding leading principal minor of the n x n Hurwitz matrix ",TEX///$H$///," of ", TT "f","."}},
	PARA{"This computes the k x k submatrix ",TEX///$H_{k}$///," of the corresponding leading principal minor of the n x n Hurwitz matrix ",TEX///$H$///," of a rational univariate polynomial ", TT "f"," of degree n with positive leading coefficient and degree at least 1.
	    The polynomial, however, is not necessarily from a univariate polynomial ring."},
	
	EXAMPLE lines ///
	    	R = QQ[x]
	        f = 3*x^4 - 7*x^3 + 5*x - 7 
		HurwitzMatrix(f,4)
	        HurwitzMatrix(f,3)	      
	 	 ///,
	PARA{"We can also use mutliple variables to represent unknown coefficients. Note that we create another ring ",TT "S"," so 
	    that ", TT "x", " and ", TT "y"," are not considered variables in the same ring and so confuse the monomials ", TEX///$x$///, " or ",TEX///$y$///,
	    " with ",TEX///$xy$///,"."},
	EXAMPLE lines ///
	        S = R[y]
		g = y^3 + 2*y^2 + y + 1
		HurwitzMatrix(g,3)
		HurwitzMatrix(g,2)
		HurwitzMatrix(g,1)
		 ///,
	SeeAlso => {"HurwitzDeterminant","isHurwitzStable"} 
	}   
    
document {
	Key => {HurwitzDeterminant,(HurwitzDeterminant, RingElement, ZZ)},
	Headline => "the leading principal minor of the n x n Hurwitz matrix H of a rational univariate polynomial of degree n, after removing the last n-k rows and n-k columns of H",
	Usage => "HurwitzDeterminant(f,k)",
	Inputs => {
	    RingElement => "f" => {"a rational univariate polynomial of degree n"},
	    ZZ => "k" => {"a nonnegative integer that determines the dimensions of a square submatrix of the n x n Hurwitz matrix of ",TT "f","."},
	    },
	Outputs => { RR => {"the leading principal minor of the Hurwitz matrix ",TEX///$H$///," of a rational univariate polynomial ", TT "f", " of degree n, after removing the last ",TEX///$n-k$///," rows and ",TEX///$n-k$///," columns of ",TEX///$H$///}},
    	PARA{"This computes the leading principal minor of the Hurwitz matrix ",TEX///$H$///," of a rational univariate polynomial ", TT "f"," with positive leading coefficient and degree at least 1.
	    The polynomial, however, is not necessarily from a univariate polynomial ring. Note the minor removed the last ",TEX///$n-k$///," rows and the last ",TEX///$n-k$///," columns of the Hurwitz matrix ", TEX///$H$///,"."},
	EXAMPLE lines ///
	    	R = QQ[x]
	        f = 3*x^4 - 7*x^3 + 5*x - 7 
		HurwitzDeterminant(f,4)
	        HurwitzDeterminant(f,3)	      
	 	 ///,
       PARA{"We can also use mutliple variables to represent unknown coefficients. Note that we create another ring ",TT "S"," so 
       that ", TT "x", " and ", TT "y"," are not considered variables in the same ring and so confuse the monomials ",TEX///$x$///, " or ",TEX///$y$///,
       " with ",TEX///$xy$///,"."},
       EXAMPLE lines ///
	        S = R[y]
		g = y^3 + 2*y^2 + y - x + 1
		HurwitzDeterminant(g,3)
		HurwitzDeterminant(g,2)
		HurwitzDeterminant(g,1)
		HurwitzDeterminant(g,0)
		 ///,
	SeeAlso => {"HurwitzMatrix","isHurwitzStable"}
     	}
    
document {
	Key => {isHurwitzStable,(isHurwitzStable, RingElement)},
	Headline => "determines whether or not a rational univariate polynomial is Hurwitz stable",
	Usage => "isHurwitzStable(f)",
	Inputs => {RingElement => "f" => {"a rational univariate polynomial"}},
	Outputs => { Boolean => { "the Hurwitz stability of a rational univariate polynomial ", TT "f"}},
	PARA {"Recall that a univariate polynomial is Hurwitz stable if all its roots have negative real parts. This method determines the Hurwitz stability of a rational univariate polynomial ", TT "f", "with positive leading coefficient and degree at least 1. 
	    The polynomial, however, is not necessarily from a univariate polynomial ring."},
	EXAMPLE lines ///
	    	R = QQ[x]
            	f = 3*x^4 - 7*x^3 + 5*x - 7 
		g = x^2 + 10*x + 21
		isHurwitzStable(f)
		isHurwitzStable(g)	      
	 	 ///,
	SeeAlso => {"HurwitzMatrix","HurwitzDeterminant"}	 
     	}

TEST ///
    R = QQ[x,y];
    F = {y^2-x^2-1,x-y^2+4*y-2};
    I = ideal F;
    S = R/I;
    a = eliminant(x);
    T = ring a;
    assert(flatten entries last coefficients(eliminant(x)) == {1,-2,-9,-6,-7});
    assert(flatten entries last regularRep(y) == {0, 0, -3, -2, 0, 0, -1, 1, 0, 1, 4, 0, 1, 0, 4, 4});
    M = last regularRep(y);
    pol = characteristicPolynomial(M);
    G = ring pol;
    ans = Z^4 - 8*Z^3 + 19*Z^2 - 16*Z + 5;
    assert(pol == ans); 
    ///

TEST ///
    c1 = {4, 5, -1, -11, 13, -9, 8};
    c2 = {9, 0, 1, 0, -1, -2, 11, 0, 14};
    assert(variations(c1) == 4);
    assert(variations(c2) == 2);
    ///

TEST ///
    R = QQ[t];
    f = (t-1)*(t+1);
    g = (t+1);
    assert(SylvesterSequence(f,g) == {t-1, 1, 0});
    assert(SturmSequence(f) == {t^2-1, 2*t, 1, 0});
    ///

TEST ///
    R = QQ[t];
    f = (t-4)*(t-1)^2*(t+1)*(t+3)*(t+5)*(t-6);--roots at 6, 4, 1 (mult 2), -1, -3, -5
    g = (2*t-1)*(3*t+8)*(t-9)*(6*t+1);--rational roots at -8/3, -1/6, 1/2, 9
    p = (t-5)*(t-2)*(t+3)*(t+4)*(t-8)*(t+13);--roots at -13, -4, -3, 2, 5, 8
    assert(BudanFourierBound(f) == 7);
    assert(BudanFourierBound(g) == 4);
    assert(BudanFourierBound(p) == 6);
    assert(BudanFourierBound(g,-infinity,0) == 2);
    assert(BudanFourierBound(g,-1,infinity) == 3);
    
    assert(numSturm(f)== 6);
    assert(numSturm(f,-6,0) == 3);
    assert(numSturm(f,-1,10) == 3);
    assert(numSturm(f,Multiplicity=>true) == 7);
    assert(numSturm(f,-10,5,Multiplicity=>true) == 6);
    assert(numSturm(f,0,6,Multiplicity=>true) == 4);
    
    
    assert(numSturm(g) == 4);
    assert(numSturm(g,-3,1) == 3);
    assert(numSturm(g,0,10) == 2);
    
    assert(numSturm(p) == 6);
    assert(numSturm(p,-15,0) == 3);
    assert(numSturm(p,2,10) == 2);
    ///
    
TEST ///
    R = QQ[t];
    f = (t-2)*(t-1)*(t+3);
    g = t+1;
    assert(numSylvester(f,g,-5,4) == 1);
    h = (t-4)*(t-1)^2*(t+1)*(t+3)*(t+5)*(t-6);
    p = t+5;
    assert(numSylvester(h,p,-10,10) == 5);
    assert(numSylvester(h,p,0,10) == 3);
    ///
    
TEST ///
    R = QQ[t];
    f = (t-1)^2*(t+3)*(t+5)*(t-6);
    assert(realRootIsolation(f,1/2) == {{-161/32, -299/64}, {-207/64, -23/8}, {23/32, 69/64}, {23/4, 391/64}});
    ///    
    
TEST ///
    R = QQ[x,y];
    F = {y^2 - x^2 - 1, x-y^2+4*y-2};
    I = ideal F;
    S = R/I;
    f = y^2 - x^2 - x*y + 4;
    assert(flatten entries traceForm(f) == {4, -86, -340, -42, -86, -266, -1262, -340, -340, -1262, -5884, -1454, -42, -340, -1454, -262});
    ///
    
TEST ///
     R = QQ[x,y];
     I = ideal(1 - x^2*y + 2*x*y^2, y - 2*x - x*y + x^2);
     assert(numTrace(I) == 3);
     F = {y^2-x^2-1,x-y^2+4*y-2};
     assert(numTrace(F) == 2);
     I = ideal F;
     S = R/I;
     assert(numTrace(S) == 2);
    ///
    
TEST ///
     R = QQ[x];
     f = 3*x^4 - 7*x^3 + 5*x - 7;
     assert(HurwitzMatrix(f,4) == sub(matrix{{-7,5,0,0},{3,0,-7,0},{0,-7,5,0},{0,3,0,-7}},QQ));
     assert(HurwitzDeterminant(f,4)== -1876);
     assert(HurwitzMatrix(f,3) == sub( matrix{{-7,5,0},{3,0,-7},{0,-7,5}},QQ));
     assert(HurwitzDeterminant(f,3) == 268);
     assert(isHurwitzStable(f) == false);
     g = x^2 + 10*x + 21;
     assert(isHurwitzStable(g) == true);
     ///

--TEST ///
  --   R = QQ[x,y];
  --   I = ideal(x*y - 1,2*x - y + 3);
    -- Z = (support I)_0; --little trick to compute Z not being symbol
    -- assert(rationalUnivariateRep(I) == {Z^2 - (3/2)*Z - 9, x + y});
    -- ///	 
    
end





--Computes the rank and signature of the trace form of f
----change name
----change output
traceFormInfo = method()
traceFormInfo (RingElement,Ideal) := Sequence => (f,I)->(
    R := ring f;
    traceFormInfo(sub(f,R/I))
    )

traceFormInfo (RingElement) := Sequence => f->(
    R := ring f;
    if not isArtinian R then error "Expected Artinian ring";
    
    trf := traceForm f;
    ch := characteristicPolynomial(trf);
    chNeg := sub(ch,(ring ch)_0=>-(ring ch)_0);
    sig := numSturm(ch,0,infinity,Multiplicity=>true) - numSturm(chNeg,0,infinity,Multiplicity=>true);
    (rank(trf),sig)
    )

--document {
--	Key => {(traceFormInfo, RingElement),traceFormInfo},
--	Usage => "traceFormInfo(f)",
--	Inputs => {"f"},
--	Outputs => { Sequence => { "the rank and signature of the trace quadratic form of", TT "f" }},
--	PARA {"This computes the rank and signature of the trace quadratic form of an element ", TT "f", " in an Artinian ring of characteristic zero"},
--	EXAMPLE lines ///
--	         R = QQ[x,y]
--		 I = ideal(1 - x^2*y + 2*x*y^2, y - 2*x - x*y + x^2)
--		 A = R/I
--		 traceFormInfo(x*y)
--		 traceFormInfo(x - 2)
--		 traceFormInfo(x + y - 3)
--	 	 ///,
--	SeeAlso => {"traceForm", "numTrace"}
  --   	}

rationalUnivariateRep = method()
rationalUnivariateRep (Ideal) := RingElement => I ->(
    R := ring I;
    S := R/I;
    --if not isArtinian(S) then error "Error: Expected I to be a zero-dimensional ideal";
    d := rank traceForm(1_S);
    
    i := 1;
    X := gens R;
    n := #X;
    while (i < n*(binomial(d,2))) do (
    	l := sum(X,apply(n,k->i^k),(a,b)->a*b);
	m := last regularRep(sub(l,S));
	f := characteristicPolynomial(m);
	
	F := f/gcd(f,diff((support f)_0,f));
	F = sub(F,ring f);
	print(first degree F);
	if (first degree F === d) then return toList(F,l);
	i = i+1
	)
    )



