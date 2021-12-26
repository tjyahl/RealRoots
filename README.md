# RealRoots.m2
## Overview
Create, edit, and improve upon a package in Macaulay2 called RealRoots. This package is for symbolically exploring, counting, and locating real solutions to polynomial systems. This package uses classical methods for elimination and solving real solutions, with particular emphasis on counting and isolating real zeros of ideals in QQ[X].

### Methods
Methods are the functions written in the package. Any method that has been exported is available to the user. To find more details about these methods, see [RealRoots_Documentation](https://faculty.math.illinois.edu/Macaulay2/doc/Macaulay2/share/doc/Macaulay2/RealRoots/html/index.html).

The main method used to solve systems of multivariate polynomials is elimination. Once variables are eliminated, the problem becomes solving univariate polynomials. To perform these calculations, Sylvester or Sturm sequences are used to count the number of real solutions in a particular range and find intervals where each solution lies. Note this range can be from negative infinity to infinity in which case the result is the total number of real solutions to the polynomial(s).

### Code
The code can be seen in the .m2 file called RealRoots. There are also tests and examples available in the documentation which can be viewed in the code or in the documentation page using the above link. Be sure to load the package in M2 when running methods or examples from the code or applying methods in this package to solve problems and examples of interest.
