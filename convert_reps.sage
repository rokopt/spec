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
    print(f"num GBs in Fan:         {(len(gbs))}")
    print(f"min #polys in GB:       {min(lens_of_gbs)}")
    print(f"max #polys in GB:       {max(lens_of_gbs)}")
    print(f"mean #polys in GB:      {mean(lens_of_gbs).n(digits=3)}")


print(" ===============")
print(" == 0 ≤ x < 8 ==")
print(" ===============")

target_poly = prod([x-i for i in range(8)])
print(f"Target polynomial: {target_poly}")

print()
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
fan0 = I0.groebner_fan()
print(f"#polys in input system: {len(polys0)}")
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
fan1 = I1.groebner_fan()
print(f"#polys in input system: {len(polys1)}")
print_gb_fan_stats(fan1)

print()
print(" == Gröbner Fan using reduction by square polynomials ==")

reductor_0 = x^2 - a
reductor_1 = a^2 - b
reductor_2 = b^2 - c
reductor_3 = a*b - d
reduced_poly_0 = target_poly.reduce([reductor_0])
reduced_poly_1 = reduced_poly_0.reduce([reductor_1])
reduced_poly_2 = reduced_poly_1.reduce([reductor_2])
reduced_poly_3 = reduced_poly_1.reduce([reductor_3])

polys2 = [reduced_poly_3, reductor_0, reductor_1, reductor_2, reductor_3]
I2 = Ideal(polys2)
fan2 = I2.groebner_fan()
print(f"#polys in input system: {len(polys2)}")
print_gb_fan_stats(fan2)

# == comparison of above fans & gbs

elim_ideal_0 = I0.elimination_ideal(R.gens()[1:]).groebner_basis()
elim_ideal_1 = I1.elimination_ideal(R.gens()[1:]).groebner_basis()
elim_ideal_2 = I2.elimination_ideal(R.gens()[1:]).groebner_basis()

print()
print(f"Elimination Ideal I0: {elim_ideal_0}")
print(f"Elimination Ideal I1: {elim_ideal_1}")
print(f"Elimination Ideal I2: {elim_ideal_2}")
print(f"Identical elimination ideals: {elim_ideal_0 == elim_ideal_1 and elim_ideal_1 == elim_ideal_2}")

f = elim_ideal_0[0].univariate_polynomial()

print()
print(f"Factors of that poly: {f.factor()}")
