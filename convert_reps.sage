# import fgb_sage

'''
The Question.
Given
    • set of constraints c
    • target function w
    • ideal I
find set of polynomials f_0, …, f_k such that
    • c holds ∀f_i
    • w(f_0, …, f_k) is minimized
    • I is the elimination ideal of <f_i> when eliminating vars(<f_i>) - vars(I)
'''

p = previous_prime(2^15)
field = GF(p)

R = PolynomialRing(field, 'x,a,b,c,d,e,f')
R.inject_variables()

def print_gb_fan_stats(gb_fan):
    gbs = gb_fan.reduced_groebner_bases()
    lens_of_gbs = [len(gb) for gb in gbs]
    print(f"num GBs in Fan:   {(len(gbs))}")
    print(f"min #polys in GB:  {min(lens_of_gbs)}")
    print(f"max #polys in GB:  {max(lens_of_gbs)}")
    print(f"mean #polys in GB: {mean(lens_of_gbs).n(digits=3)}")


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
print_gb_fan_stats(fan0)

print()
print(" == Gröbner Fan of 'binary decomposition' ==")

polys1 = [
	a * a - a,
	b * b - b,
	c * c - c,
	4*a + 2*b + c - x,
]
I1 = Ideal(polys1)
# gb1 = fgb_sage.groebner_basis(I1)
fan1 = I1.groebner_fan()
print_gb_fan_stats(fan1)

print()
def dumb_inclusion_check(gb, fan):
	return sorted(gb).__repr__() in [sorted(gb).__repr__() for gb in fan]
print(f"fans share gb: {any([dumb_inclusion_check(gb, fan0) for gb in fan1])}")

elim_ideal_0 = I0.elimination_ideal(R.gens()[1:]).groebner_basis()
elim_ideal_1 = I1.elimination_ideal(R.gens()[1:]).groebner_basis()

print()
print(f"Elimination Ideal I0: {elim_ideal_0}")
print(f"Elimination Ideal I1: {elim_ideal_1}")
print(f"Identical elimination ideals: {elim_ideal_0 == elim_ideal_1}")

f = elim_ideal_0[0].univariate_polynomial()

print()
print(f"Factors of that poly: {f.factor()}")
