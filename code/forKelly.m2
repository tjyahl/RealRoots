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
