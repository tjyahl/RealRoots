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
	 Email=>"",
	 HomePage=>""},
    	{Name=>"Kelly Maluccio",
	 Email=>"",
	 HomePage=>""},
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
    "regularRep"
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


beginDocumentation()


end

--Put notes, examples, etc down here. It won't go in the actual package.

--Notes:
----
----1) Remember to include tests for the code in documentation.
----
----
----
----
----
----
----




