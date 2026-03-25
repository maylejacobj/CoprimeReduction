// *** Characterizing Serre pairs ***
// By Lemma 3.1 of ``GL2-representations with maximal image'' by Nathan Jones,
// we should look at the mod 36 Galois image.
n := 36;
G := GL(2, Integers(n));
Delta, pr1, pr2 := ConstructDelta(n);


// Here, we look at maximal subgroups (first layer)
// First layer subgroups with full determinant
Level1FullDet := {H`subgroup : H in MaximalSubgroups(Delta) | HasFullDet(H`subgroup, pr1)};

// First layer subgroups with full determinant and commutator
Level1FullDetComm := {H : H in Level1FullDet | HasFullCom(H, Delta)};


// Now, we look at maximal subgroups of maximal subgroups (second layer)
// Second layer subgroups with full determinant
Level2FullDet := &join{{H`subgroup : H in MaximalSubgroups(K) | HasFullDet(H`subgroup, pr1)} : K in Level1FullDet};

// Second layer subgroups with full determinant and commutator
Level2FullDetComm := {H : H in Level2FullDet | HasFullCom(H, Delta)};

// We confirm that no second-layer subgroup has full determinant and commutator
assert IsEmpty(Level2FullDetComm);


// Since there are no second layer (or lower) subgroups with full determinant and commutator,
// all such subgroups must be first layer (or Delta itself). There are seven such subgroups.
AllSubsFullDetCom := Include(Level1FullDetComm, Delta);


// We construct the set of maximal subgroups of a full determinant and commutator subgroup
// that have full determinant but do not have full commutator.
MaxOfFullDetComButNonFullCom := &join {{K`subgroup : K in MaximalSubgroups(H) | HasFullDet(K`subgroup, pr1) and not HasFullCom(K`subgroup, Delta)} : H in AllSubsFullDetCom};

// We are interested in subgroups from MaxOfFullDetComButNonFullCom arising as mod 36 images
// of products of Serre curves. Thus, each projection should have full commutator.
MaxOfFullDetComButNonFullComWithFullComInEachFactor := {H : H in MaxOfFullDetComButNonFullCom | HasFullCom(pr1(H),G) and HasFullCom(pr2(H),G)};


// At this stage, we have two important sets:
// * AllSubsFullDetCom: These subgroups are the possible mod 36 images of Serre pairs.
// * MaxOfFullDetComButNonFullComWithFullComInEachFactor: These subgroups are the possible mod
//      36 images for products of Serre curves that are not Serre pairs.
// To efficiently distinguish these two sets, we look modulo 6 and modulo 4.
DeltaMod6 := ConstructDelta(6);
DeltaMod4 := ConstructDelta(4);
for H in MaxOfFullDetComButNonFullComWithFullComInEachFactor do
	sub<DeltaMod4|Generators(H)> eq DeltaMod4 and Index(DeltaMod6, sub<DeltaMod6|Generators(H)>) le 2;
end for;
// Running the above code indicates "false" for all subgroups in 
// MaxOfFullDetComButNonFullComWithFullComInEachFactor,  meaning none of these groups are 
// both surjective modulo 4 and have index <=2 modulo 6.

// On the other hand, all of the groups in AllSubsFullDetCom are both surjective modulo 4 and 
// have index <= 2 modulo 6, as we now check.
for H in AllSubsFullDetCom do
	sub<DeltaMod4|Generators(H)> eq DeltaMod4 and Index(DeltaMod6, sub<DeltaMod6|Generators(H)>) le 2;
end for;
// Running the above code indicates "true" for all groups in AllSubsFullDetCom, verifying
// our claim.