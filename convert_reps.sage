# import fgb_sage

p = previous_prime(2^15)
field = GF(p)

R0 = PolynomialRing(field, 'x,y,z')
R0.inject_variables()

print(" ===============")
print(" == 0 ≤ x < 4 ==")
print(" ===============")
print(" == Gröbner Fan of 'roots of nullifier' ==")

polys0 = [
	(x-0) * (x-1) - y,
	(x-2) * (x-3) - z,
	y * z,
]
I0 = Ideal(polys0)
# gb0 = fgb_sage.groebner_basis(I0)
fan0 = I0.groebner_fan()
for gb in sorted(fan0.reduced_groebner_bases()):
	print(f"{len(gb)} – {sorted(gb)}")

print()
print(" == Gröbner Fan of 'binary decomposition' ==")

polys1 = [
	y^2 - y,
	z^2 - z,
	2*z + y - x,
]
I1 = Ideal(polys1)
# gb1 = fgb_sage.groebner_basis(I1)
fan1 = I1.groebner_fan()
for gb in sorted(fan1.reduced_groebner_bases()):
	print(f"{len(gb)} – {sorted(gb)}")

print()
def dumb_inclusion_check(gb, fan):
	return sorted(gb).__repr__() in [sorted(gb).__repr__() for gb in fan]
print(f"fans share gb: {any([dumb_inclusion_check(gb, fan0) for gb in fan1])}")

print()
print(f"Elimination Ideal I0: {I0.elimination_ideal([y,z]).groebner_basis()}")
print(f"Elimination Ideal I1: {I1.elimination_ideal([y,z]).groebner_basis()}")

f = I0.elimination_ideal([y,z]).groebner_basis()[0].univariate_polynomial()

print()
print(f"Factors of that poly: {f.factor()}")