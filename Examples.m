// Some examples using IsSerrePair to check whether
// a pair of Serre curves is a Serre pair.

// Example 1
E1 := EllipticCurve("37a1"); // Serre curve
E2 := EllipticCurve("43a1"); // Serre curve
IsSerrePair(E1, E2); // Serre pair

// Example 2
E1 := EllipticCurve("58a1"); // Serre curve
E2 := EllipticCurve("76a1"); // Serre curve
IsSerrePair(E1, E2); // Serre pair

// Example 3
E1 := EllipticCurve("235a1"); // Serre curve
E2 := EllipticCurve("235b1"); // Serre curve
IsSerrePair(E1, E2); // Likely not a Serre pair

// Example 4
E1 := EllipticCurve("1053d1"); // Serre curve
E2 := EllipticCurve("1300e1"); // Serre curve
IsSerrePair(E1, E2); // Likely not a Serre pair


// Proposition 34
// We verify that the claim of the proposition holds
// for all good primes p <= 10^6
E1 := EllipticCurve("484a2"); // LMFDB: 484.a1
E2 := EllipticCurve("847a1"); // LMFDB: 847.c1
N1 := Conductor(E1); N2 := Conductor(E2);
N := 10^6;
for p in PrimesUpTo(N) do
    if (N1 * N2) mod p ne 0 then
        g := GCD(p+1-TraceOfFrobenius(E1,p), p+1-TraceOfFrobenius(E2,p));
        if (p mod 11) in [2,6,7,8,10] then
            if g mod 2 ne 0 then
                print "Counterexample found:", p;
            end if;
        end if;
        if (p mod 11) in [1,3,4,5,9] then
            if g mod 3 ne 0 then
                print "Counterexample found:", p;
            end if;
        end if;
    end if;
end for;
// No counterexamples are found.


// Examples of computing coprimality constant for Serre pairs
// in two different ways and checking numerically

// Example 35
E1 := EllipticCurve([32, 212]); // 140.b1
E2 := EllipticCurve([-12393, 197073]); // 34020.c1
IsSerrePair(E1, E2); 
// true

// We check that the value of f agrees whether computed from the image
// or via the formula in the article:
ComputefSerrePairImg(E1, E2);
// 168823/1358954496
m1 := 70; m2 := 210;
m12 := LCM(m1, m2);
ComputefSerrePairFormula(m12, m1, m2);
// 168823/1358954496
// They match!

// We now compute R(70, 210)
S := &+ [MoebiusMu(d) * ComputefSerrePairFormula(d, m1, m2) : d in Divisors(m12)];
P := &* [1 - F1(ell) : ell in PrimeDivisors(m12)];
S/P;
// 5014419112/5014521525

// We now count primes of coprime reduction numerically
N1 := Conductor(E1);
N2 := Conductor(E2);
CtCoprime := 0;
N := 10^6;
for p in PrimesUpTo(N) do
    if (N1 * N2) mod p ne 0 then
        ap1 := TraceOfFrobenius(E1,p);
        ap2 := TraceOfFrobenius(E2,p);
        if GCD(p+1-ap1, p+1-ap2) eq 1 then
            CtCoprime := CtCoprime + 1;
        end if;
    end if;
end for;
NumPrimes := #PrimesUpTo(N);
print CtCoprime, NumPrimes;
RealField() ! (CtCoprime/NumPrimes);
// With N = 10^6, we get 0.392914469158449896812657647329


// Example 36
E1 := EllipticCurve([0, 0, 1, -81, 290]); // 297.a1
E2 := EllipticCurve([0, 0, 1, -3, -2]); // 405.a1
IsSerrePair(E1, E2);
// true

// We check that the value of f agrees whether computed from the image
// or via the formula in the article:
ComputefSerrePairImg(E1, E2);
// 5263/884736
m1 := 6;
m2 := 10;
m12 := LCM(m1, m2);
ComputefSerrePairFormula(m12, m1, m2);
// 5263/884736
// They match!

// We now compute R(6, 10)
S := &+ [MoebiusMu(d) * ComputefSerrePairFormula(d, m1, m2) : d in Divisors(m12)];
P := &* [1 - F1(ell) : ell in PrimeDivisors(m12)];
S/P;
// 1150648/1118065

// We now count primes of coprime reduction numerically
N1 := Conductor(E1);
N2 := Conductor(E2);
CtCoprime := 0;
N := 10^6;
for p in PrimesUpTo(N) do
    if (N1 * N2) mod p ne 0 then
        ap1 := TraceOfFrobenius(E1,p);
        ap2 := TraceOfFrobenius(E2,p);
        if GCD(p+1-ap1, p+1-ap2) eq 1 then
            CtCoprime := CtCoprime + 1;
        end if;
    end if;
end for;
NumPrimes := #PrimesUpTo(N);
print CtCoprime, NumPrimes;
RealField() ! (CtCoprime/NumPrimes);
// For N = 10^6, we get 0.407144131060663965960916201686