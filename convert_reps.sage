# import fgb_sage

p = previous_prime(2^15)
field = GF(p)

R0 = PolynomialRing(field, 'x,a,b,c,d,e,f')
R0.inject_variables()

print(" ===============")
print(" == 0 ≤ x < 8 ==")
print(" ===============")
print(" == Gröbner Fan of 'roots of nullifier' ==")

polys0 = [
	(x-0) * (x-1) - a,
	(x-2) * (x-3) - b,
	(x-4) * (x-5) - c,
	(x-6) * (x-7) - d,
	a * b - e,
	c * d - f,
	e * f,
]
I0 = Ideal(polys0)
# gb0 = fgb_sage.groebner_basis(I0)
fan0 = I0.groebner_fan()
gbs0 = fan0.reduced_groebner_bases()

print(f"num GBs in Fan:   {(len(gbs0))}")
print(f"min polys in GB:  {min([len(gb) for gb in gbs0])}")
print(f"max polys in GB:  {max([len(gb) for gb in gbs0])}")
print(f"mean polys in GB: {mean([len(gb) for gb in gbs0]).n(digits=3)}")

print()
print(" == Gröbner Fan of 'binary decomposition' ==")

polys1 = [
	a^2 - a,
	b^2 - b,
	c^2 - c,
	4*a + 2*b + c - x,
]
I1 = Ideal(polys1)
# gb1 = fgb_sage.groebner_basis(I1)
fan1 = I1.groebner_fan()
gbs1 = fan1.reduced_groebner_bases()

print(f"num GBs in Fan:   {(len(gbs0))}")
print(f"min polys in GB:  {min([len(gb) for gb in gbs1])}")
print(f"max polys in GB:  {max([len(gb) for gb in gbs1])}")
print(f"mean polys in GB: {mean([len(gb) for gb in gbs1]).n(digits=3)}")

print()
def dumb_inclusion_check(gb, fan):
	return sorted(gb).__repr__() in [sorted(gb).__repr__() for gb in fan]
print(f"fans share gb: {any([dumb_inclusion_check(gb, fan0) for gb in fan1])}")

print()
print(f"Elimination Ideal I0: {I0.elimination_ideal(R0.gens()[1:]).groebner_basis()}")
print(f"Elimination Ideal I1: {I1.elimination_ideal(R0.gens()[1:]).groebner_basis()}")

f = I0.elimination_ideal(R0.gens()[1:]).groebner_basis()[0].univariate_polynomial()

print()
print(f"Factors of that poly: {f.factor()}")