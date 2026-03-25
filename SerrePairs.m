ChangeDirectory("/Users/Jacob/OpenImage-master");
load "main/FindOpenImage.m";

// Checks if E_1 x E_2 is surjective mod 4.
// Note: This function assumes that E_1 and
// E_2 are surjective mod 4 individually.
// Output of `True' means surjective mod 4 (rigorous)
// Output of `False' means likely nonsurjective mod 4 (heuristic)
IsSurjMod4 := function(E1,E2:B:=100000)
	R<x> := PolynomialRing(Integers(4));
	OnlySurj := {
	    <x^2 + 1, x^2 + 3*x + 1>,
	    <x^2 + 1, x^2 + x + 1>,
	    <x^2 + x + 1, x^2 + 1>,
	    <x^2 + 3*x + 1, x^2 + 1>
	};
	N1 := Conductor(E1);
	N2 := Conductor(E2);
	for p in PrimesUpTo(B) do
		if (N1 * N2) mod p ne 0 then
			if <R!(x^2-TraceOfFrobenius(E1,p)*x+p),R!(x^2-TraceOfFrobenius(E2,p)*x+p)> in OnlySurj then
				return true;
			end if;
		end if;
	end for;
	return false;
end function;


// Checks if E_1 x E_2 has index at most 2
// mod 6. Note: This function assumes that E_1 and
// E_2 are Serre curves, E_1 x E_2 is surjective
// mod 4, and E_1 x E_2 is surjective mod 3.
// Output of `True' means index mod 6 is at most 2 (rigorous)
// Output of `False' means index mod 6 is likely greater than 2 (heuristic)
IsIndexAtMost2Mod6 := function(E1,E2:B:=3000000)
	R<x> := PolynomialRing(Integers(6));
	OnlySurj := {
	    <x^2 + 3*x + 1, x^2 + 3*x + 1>
	};
	N1 := Conductor(E1);
	N2 := Conductor(E2);
	for p in PrimesUpTo(B) do
		if (N1 * N2) mod p ne 0 then
			// p, <R!(x^2-TraceOfFrobenius(E1,p)*x+p), R!(x^2-TraceOfFrobenius(E2,p)*x+p)>;
			if <R!(x^2-TraceOfFrobenius(E1,p)*x+p),R!(x^2-TraceOfFrobenius(E2,p)*x+p)> in OnlySurj then
				return true;
			end if;
		end if;
	end for;
	return false;
end function;


// Finds Lambda as in the article 
// ``An Effective Open Image Theorem for Products of Principally Polarized Abelian Varieties''
// by Jacob Mayle and Tian Wang
FindLambda := function(E1, E2 : B := 100000)
    Lambda := 0;
    N1 := Conductor(E1);
    N2 := Conductor(E2);
    for p in PrimesUpTo(B) do
        if (N1*N2) mod p ne 0 then
        	a1p := TraceOfFrobenius(E1,p);
        	a2p := TraceOfFrobenius(E2,p);
        	M := (a1p-a2p)*(a1p+a2p);
        	Lambda := GCD(Lambda,M);
        end if;
    end for;
    return Lambda;
end function;


// This function is due to Andrew V. Sutherland, associated with the article
// ``Computing images of Galois representations attached to elliptic curves''
TorsionRank:=function(E,N,ell)
    e := Valuation(N,ell);
    if e lt 2 then return e; end if;
    if #BaseRing(E) mod ell ne 1 then return 1; end if;
    M:=ExactQuotient(N,ell^e);
    O := E!0;
    // Get a point P of order ell
    P:=O;
    while P eq O do P:= M*Random(E); end while;
    a:=1; X:=ell*P; while X ne O do a+:=1; P:= X; X*:=ell; end while;
    if a eq e then return 1; end if;
    // generate random points Q of ell-power order until we either find a basis for the ell-torsion or prove the ell-power torsion is cyclic.
    while true do
        Q:=M*Random(E);
        if Q eq E!0 then continue; end if;
        a:=1; X:=ell*Q; while X ne O do a+:=1; Q:= X; X*:=ell; end while;
        if a eq e then return 1; end if;
        if WeilPairing(P,Q,ell) ne 1 then return 2; end if;
    end while;
end function;


// This function is due to Andrew V. Sutherland, associated with the article
// ``Computing images of Galois representations attached to elliptic curves''
EpSigs:=function(E,S:t:=TraceOfFrobenius(E))
    if Type(S) ne SeqEnum then S:=[S]; end if;
    q:=#BaseRing(E);
    T:=[*<>:ell in S*];
    for i:=1 to #S do
        ell:=S[i];
        if IsDivisibleBy(q,ell) then continue; end if;
        r:=TorsionRank(E,q+1-t,ell);
        T[i]:=<GF(ell)!q, GF(ell)!t, r>;
    end for;
    return T;
end function;


// Checks if E_1 x E_2 is surjective mod 3,
// based on the article of Mayle-Wang.
// Output of `True' means surjective mod 3 (rigorous)
// Output of `False' means likely nonsurjective mod 3 (heuristic)
IsSurjMod3 := function(E1,E2:B:=100000)
	OnlySurj := { <1, 2>, <2, 1> };
	N1 := Conductor(E1);
	N2 := Conductor(E2);
	for p in PrimesUpTo(B) do
		if (3 * N1 * N2) mod p ne 0 then
			if <EpSigs(ChangeRing(E1,GF(p)),3)[1][3], EpSigs(ChangeRing(E2,GF(p)),3)[1][3]> in OnlySurj then
				return true;
			end if;
		end if;
	end for;
	return false;
end function;

// Assumes E1 and E2 are Serre curves; this can be
// checked using Zywina's FindOpenImage code.
// Returns "true" if E1 x E2 is a Serre pair and
// returns "false" if unable to show that E1 x E2
// is a Serre pair (in this case, E1 x E2 is likely
// not a Serre pair but this is heuristic).
IsSerrePair := function(E1, E2)
    print "Assuming E1 and E2 are both Serre curves...";
    E1 := MinimalModel(E1);
    E2 := MinimalModel(E2);
    
    Lambda := FindLambda(E1, E2);
    if Lambda ne 0 and Set(PrimeDivisors(Lambda)) subset {2,3} then
        print "The mod ell representation is surjective for all primes ell >= 5.";
    else
        print "There likely exists a nonsurjective prime ell >= 5 for E1 x E2";
        print "Thus, E1 x E2 is likely not a Serre pair.";
        return false;
    end if;

    // This is only necessary to check because it is an assumption for
    // the IsIndexAtMost2Mod6 function. There is no harm in checking it
    // since the mod 3 representation is always surjective for a Serre pair.
    if IsSurjMod3(E1,E2) then
        print "The mod 3 Galois representation of E1 x E2 is surjective.";
    else
        print "The mod 3 Galois representation of E1 x E2 is likely not surjective.";
        print "Thus, E1 x E2 is likely not a Serre pair.";
        return false;
    end if;

   if IsSurjMod4(E1,E2) then
        print "The mod 4 Galois representation of E1 x E2 is surjective.";
    else
        print "The mod 4 Galois representation of E1 x E2 is likely not surjective.";
        print "Thus, E1 x E2 is likely not a Serre pair.";
        return false;
    end if;

    if IsIndexAtMost2Mod6(E1,E2) then
        print "The mod 6 Galois image of E1 x E2 has index at most 2.";
    else
        print "The mod 6 Galois image of E1 x E2 likely has index greater than 2.";
        print "Thus, E1 x E2 is likely not a Serre pair.";
        return false;
    end if;


    print "Therefore, E1 x E2 is a Serre pair.";
    return true;
end function;

// Assumes E1 and E2 form a Serre pair.
// Computes the quantity f_{E_1,E_2}(m) (where
// m is the adelic level of E1 x E2) by counting 
/// conjugacy classes in the mod m Galois image.
ComputefSerrePairImg := function(E1, E2)
    G1 := FindOpenImage(E1);
    G2 := FindOpenImage(E2);
    m := LCM(#BaseRing(G1), #BaseRing(G2));
    G1 := gl2Lift(G1, m);
    G2 := gl2Lift(G2, m);

    C1 := ConjugacyClasses(G1);
    C2 := ConjugacyClasses(G2);
    
    I := Matrix(One(GL(2, Integers(m))));
    S1 := {* Determinant(c[3])^^c[2] : c in C1 | Determinant(I-c[3]) eq 0 *};
    S2 := {* Determinant(c[3])^^c[2] : c in C2 | Determinant(I-c[3]) eq 0 *};

    return &+[Multiplicity(S1, s) * Multiplicity(S2, s) : s in MultisetToSet(S1)] / (#G1 * #G2 / EulerPhi(m));
    
end function;

// Computes F_1(d) as in the article
F1 := function(d)
    if d eq 1 then
        return 1;
    end if;
    
    return &*[ ((p+2)*(p^2-p-1)) / ((p-1)^3*(p+1)^2) : p in PrimeDivisors(d) ];
end function;

// Computes F_2(d) as in the article
F2 := function(d)
    if d eq 1 then
        return 1;
    end if;
    
    return &*[ (-2*p-1) / ((p-1)^3*(p+1)^2) : p in PrimeDivisors(d) ];
end function;

// Computes F_1^*(d) as in the article
F1star := function(d)
    if d eq 1 then
        return 1;
    end if;

    return &*[ F1(p)/(1 - F1(p)) : p in PrimeDivisors(d) ];
end function;

// Computes F_2^*(d) as in the article
F2star := function(d)
    if d eq 1 then
        return 1;
    end if;

    return &*[ Abs(F2(p))/(1 - F1(p)) : p in PrimeDivisors(d) ];
end function;

// Assumes m1 and m2 are the adelic levels of two
// elliptic curves forming a Serre pair.
// Computes the quantity f_{E_1,E_2}(d) using the
// closed formula from the article.
ComputefSerrePairFormula := function(d, m1, m2)
    mp := LCM(m1,m2) div Gcd(m1,m2); 

    if d mod m1 ne 0 and d mod m2 ne 0 then
        return F1(d);
    end if;

    if d mod m1 eq 0 and d mod m2 ne 0 then
        return (1 + (2/5)*(F2(m1)/F1(m1))) * F1(d);
    end if;
    
    if d mod m1 ne 0 and d mod m2 eq 0 then
        return (1 + (2/5)*(F2(m2)/F1(m2))) * F1(d);
    end if;
    
    return (1 + (2/5)*(F2(m1)/F1(m1)) + (2/5)*(F2(m2)/F1(m2)) + (1/4)*(F2(mp)/F1(mp))) * F1(d);
end function;
