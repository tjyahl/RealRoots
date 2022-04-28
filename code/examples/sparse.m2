--

restart

monomialMapEvaluation = method()
--Evaluates the monomial map corresponding to the matrix A at the point v. 
monomialMapEvaluation (List,Matrix) := List => (v,A)->(
    L := apply(entries transpose A,r->product(v,r,(x,n)->x^n));
    L
    )

generateSystem = method(Options => {Verbose=>0})
--Given a pair of supports A and coefficients C, this forms the monomials and the corresponding system of polynomials.
--This is an internal method to get the system back from our internal data structure (A,C) for polynomial systems
--This is the inverse function to pullSystemData
generateSystem (List,List) := List => o->(A,C)->(
    --error handling
    n := numgens target A#0;
    if not (#A === #C and apply(A,M->numgens source M) === apply(C,c->#c) and all(A,M->numgens target M === n)) then (
	error "generateSystem: Inconsistent number of equations, monomials, or coefficients"
	);
    if not (all(A,M->all(flatten entries M,a->a>=0))) then (
	if (o.Verbose > 0) then (print("generateSystem: Shifting supports to positive orthant"));
	A = apply(A,M->matrix apply(entries M,v->apply(v,z->z-min v)));
	);    
    x := symbol x;
    R := QQ[x_1..x_n];
    F := apply(#A,i->sum(C#i,monomialMapEvaluation(gens R,A#i),(c,m)->c*m));
    F
    )


loadPackage("RealRoots",FileName=>"../RealRoots.m2")

A = {matrix{{0,0,1,1},{0,1,0,1}},matrix{{0,0,1,1},{0,1,0,1}}}
C = apply(#A,i->apply(numgens source A#i,j->random(QQ)))
F = generateSystem(A,C)

R = (ring first F)/(ideal F)

characteristicPolynomial R_0
characteristicPoly R_0



