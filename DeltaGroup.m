// Given a subgroup G of GL(2, Z/nZ), return its image under the determinant map in (Z/nZ)^*.
Det := function(G)
	U, phi := UnitGroup(BaseRing(G));
	return sub< U | [Determinant(g) @@ phi : g in Generators(G)]>;
end function;

// Given an integer n >= 2, return the fiber product GL(2,Z/nZ) x_det GL(2,Z/nZ), along with 
// projection maps to each factor.
ConstructDelta := function(n)
	R := Integers(n);
	U, phi := UnitGroup(R);
	G := GL(2, R);
	GG := DirectProduct(G, G);
	psi := hom<GG->U | [<g, (Determinant(Submatrix(g,1,1,2,2))*Determinant(Submatrix(g,3,3,2,2))^-1) @@ phi> : g in Generators(GG)]>;
	D := Kernel(psi);
	pr1 := hom<D->G | [<d, Submatrix(d,1,1,2,2)> : d in Generators(D)]>;
	pr2 := hom<D->G | [<d, Submatrix(d,3,3,2,2)> : d in Generators(D)]>;
	return D, pr1, pr2;
end function;

// Given a subgroup H of GL(2,Z/nZ) x_det GL(2,Z/nZ), return "true" if the image of H under 
// the determinant map is all of (Z/nZ)^*. A projection map (either one) must be provided.
HasFullDet := function(H, pr)
	return #Det(pr(H)) eq EulerPhi(#BaseRing(H));
end function;

// Given a subgroup H of G, return "true" if the commutator subgroup of H equals that of G.
HasFullCom := function(H, G)
    return CommutatorSubgroup(H) eq CommutatorSubgroup(G);
end function;
