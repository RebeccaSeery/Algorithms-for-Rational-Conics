from sage.all import *
from rational_conics import R, test_degenerate, coefficients, diagonalize, remove_denominators

var('x, y, z, m, n')  # m and n are needed as if we load rational_conics.py and then this file it overwrites the variables and causes errors.

def to_square_quotient(a, p):
    a = ZZ(a*a.denom()**2)
    if a == 0:
        raise ValueError('a cannot be 0')
    
    if p == infinity:
        return sign(a)
    
    elif not is_prime(p):
        raise ValueError('p must be prime or infinity')
    
    elif p != 2:
        v = valuation(a, p)
        u = a / p**v
        return vector(ZZ, [(-1)**v, kronecker(u, p)])

    # p = 2
    v2 = valuation(a, 2)
    u = IntegerModRing(8)(a / 2**v2)
    v3, v5 = 0, 0
    if u == 3 or u == 7:
        v3 = 1
    if u == 5 or u == 7:
        v5 = 1
    return vector(ZZ, [(-1)**v2, (-1)**v3, (-1)**v5])


def to_mod_2_vector_space(xs):
    return vector(ZZ, [0 if x == 1 else 1 for x in xs])


def hilbert(a, b, p):
    a = to_square_quotient(a, p)
    b = to_square_quotient(b, p)

    if p == infinity:
        [a, b] = to_mod_2_vector_space([a, b])
        return ZZ((-1)**(a*b))
    else:
        a = to_mod_2_vector_space(a)
        b = to_mod_2_vector_space(b)
    
    if p % 4 == 1:
        M = Matrix(ZZ, [[0, 1], [1, 0]])
        return ZZ((-1)**(a*M*b))
    elif p % 4 == 3:
        M = Matrix(ZZ, [[1, 1], [1, 0]])
        return ZZ((-1)**(a*M*b))

    # p = 2
    M = Matrix(ZZ, [[0, 1, 1], [1, 1, 0], [1, 0, 0]])
    return ZZ((-1)**(a*M*b))


def d(a, b, c, p):
    if a*b*c == 0:
        raise ValueError('The form must be nondegenerate')
    if p == infinity:
        return vector(ZZ, [
            [x > 0 for x in [a, b, c]].count(True),
            [x < 0 for x in [a, b, c]].count(True)])
    elif not is_prime(p):
        raise ValueError('p must be prime')
    return to_square_quotient(a*b*c, p)


def epsilon(a, b, c, p):
    return hilbert(a, b, p) * hilbert(a, c, p) * hilbert(b, c, p)


def is_isomorphic_as_forms(coeffs1, coeffs2):
    a1, b1, c1 = coeffs1
    a2, b2, c2 = coeffs2
    d1 = a1*b1*c1
    d2 = a2*b2*c2
    
    if d1 == 0 or d2 == 0:
        raise ValueError('The forms must be nondegenerate')

    if not d(a1, b1, c1, infinity) == d(a2, b2, c2, infinity):
        return False
    
    # For the forms to be isomorphic, we need d1 = d2 in Q*/(Q*^2)
    if not is_square(QQ(d1/d2)):
        return False
    
    for p in prime_divisors(2*d1*d2) + [infinity]:
        if not epsilon(a1, b1, c1, p) == epsilon(a2, b2, c2, p):
            return False

    return True


def is_isomorphic_as_conics(coeffs1, coeffs2):
    a1, b1, c1 = coeffs1
    a2, b2, c2 = coeffs2

    d1 = a1*b1*c1
    d2 = a2*b2*c2
    
    if d1 == 0 or d2 == 0:
        raise ValueError('The conics must be nondegenerate')
    

    return is_isomorphic_as_forms(d2*vector(QQ, coeffs1), d1*vector(QQ, coeffs2))


def places_not_locally_solvable(a, b, c):
    '''Returns the places p at which the conic a*x**2 + b*y**2 + c*z**2 = 0 has no solutions'''
    failure_points = []

    if hilbert(-a*c, -b*c, infinity) == -1:
        failure_points.append(infinity)

    for p in prime_divisors(2*a*b*c):
        if hilbert(-a*c, -b*c, p) == -1:
            failure_points.append(p)

    return failure_points


def places_conic_not_locally_solvable(f):
    coeffs = coefficients(f)
    coeffs, _ = diagonalize(coeffs)
    a, b, c = remove_denominators(coeffs)
    return places_not_locally_solvable(a, b, c)


def demo_solvable(f):
    '''This function can be called to demonstrate the code for local solvability over Q_p.'''
    places = places_conic_not_locally_solvable(f)
    if places == []:
        print('f(x, y) = '+str(f)+' is solvable over Q_p for all p (including Q_infinity = R), and therefore it is solvable over Q.')
    else:
        print('f(x, y) = '+str(f)+' is not locally solvable over Q_p for p = '+str(tuple(places)))

def demo_isomorphic(f1, f2):
    '''This is used to demonstrate the code that tests if two conics/forms are isomorphic.'''
    coeffs1 = coefficients(f1)
    coeffs1, _ = diagonalize(coeffs1)
    coeffs1 = remove_denominators(coeffs1)
    coeffs2 = coefficients(f2)
    coeffs2, _ = diagonalize(coeffs2)
    coeffs2 = remove_denominators(coeffs2)

    if is_isomorphic_as_conics(coeffs1, coeffs2):
        if is_isomorphic_as_forms(coeffs1, coeffs2):
            print('f_1(x, y) = '+str(f1)+' and '+'f_2(x, y) = '+str(f2)+' are isomorphic as quadratic forms and therefore also as conics.')
        else:
            print('f_1(x, y) = '+str(f1)+' and '+'f_2(x, y) = '+str(f2)+' are isomorphic as conics but not as quadratic forms.')
    else:
        print('f_1(x, y) = '+str(f1)+' and '+'f_2(x, y) = '+str(f2)+' are not isomorphic as quadratic forms or even as conics.')
    





def test():
    print(to_square_quotient(6, 3))
    print(to_square_quotient(6, 5))
    print(to_square_quotient(-8, infinity))
    print(to_square_quotient(4, 2))
    print(to_square_quotient(17, 2))
    print(to_square_quotient(6, 2))

    print('\n\n')

    print(hilbert(6, 2, 5))
    print(hilbert(6, 2, 3))  # -1
    print(hilbert(6, 2, 2))  # -1
    print(hilbert(-1, -1, infinity))  # -1

    print('\n\n')

    print(is_isomorphic_as_forms((1, 2, -3), (3, 1, -2)))
    print(is_isomorphic_as_conics((1, 2, -3), (3, 1, -2)))

    print(is_isomorphic_as_forms((1, 2, -3), (3, -1, -2)))
    print(is_isomorphic_as_conics((1, 2, -3), (3, -1, -2)))

    print(is_isomorphic_as_forms((2, 3, -5), (1, 1, -1)))
    print(is_isomorphic_as_conics((2, 3, -5), (1, 1, -1)))

    print('\n\n')

    a = QQ(174839507349205743885342098)
    b = QQ(100924631243586773741746381789/3)
    c = QQ(320478392574389207819834921048921048)

    print(places_not_locally_solvable(a, b, c))

    f = R(7438219*x**2 + 74389201*x*y + 4732189/77438291*y**2 + 748932*x + 6438172438621*y + 74839214/73821)
    demo_solvable(f)

    f1 = R(7438219*x**2 + 74389201*x*y + 4732189/77438291*y**2 + 748932*x + 6438172438621*y + 74839214/73821)
    f2 = R(7438219*x**2 - 74389201*x*y + 4732189/77438291*y**2 - 748932*x + 6438172438621*y + 74839214/73821)
    demo_isomorphic(f1, f2)

    f1 = R(x**2 + y**2 - 1)
    f2 = R(x**2 + y**2 - 3)
    demo_isomorphic(f1, f2)



