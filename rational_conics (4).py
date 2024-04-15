from sage.all import *
from sqrts import extended_euclidean, sqrt_mod_n

var('x, y, z, m, n')
R = QQ['x, y']
x, y = R(x), R(y)


def test_degenerate(coeffs):
    a, b, c, d, e, f = coeffs
    A = matrix(QQ, [[a, b/2, d/2],
                    [b/2, c, e/2],
                    [d/2, e/2, f]])
    return det(A) == 0


def coefficients(f, diagonal=True):
    if not (f in R or f in S):
        raise ValueError('f should be in either QQ[x,y] or ZZ[x,y,z], not '+str(f))

    a = f.monomial_coefficient(R(x**2))
    b = f.monomial_coefficient(R(x*y))
    c = f.monomial_coefficient(R(y**2))
    d = f.monomial_coefficient(R(x))
    e = f.monomial_coefficient(R(y))
    f = f.monomial_coefficient(R(1))
    return [a, b, c, d, e, f]


def transform_conic(coeffs, T):
    '''Changes variables x -> Tx.
    Returns the coefficients of the conic in the new vector space.'''
    a, b, c, d, e, f = coeffs
    A = matrix(QQ, [[a, b/2, d/2],
                    [b/2, c, e/2],
                    [d/2, e/2, f]])
    new_A = T.inverse().transpose() * A * T.inverse()
    a, b, c, d, e, f = new_A[0,0], 2*new_A[0,1], new_A[1,1], 2*new_A[0,2], 2*new_A[1,2], new_A[2,2]
    return [a, b, c, d, e, f]
    

def diagonalize(coeffs):
    '''Changes variables to obtain a conic of the form ax^2 + by^2 + c.
    Args:
    f - a conic in the ring QQ['x, y'] of the form ax^2 + bxy + cy^2 + dx + ey + f
    '''
    a, b, c, d, e, f = coeffs
    Q = QuadraticForm(QQ, 3, [a/2,b/2,d/2,c/2,e/2,f/2])
    D, T = Q.rational_diagonal_form(return_matrix=True)
    
    a, b, c = D[0,0], D[1,1], D[2,2]
    
    return [a,b,c], T


def remove_denominators(coeffs):
    denominator = lcm([coeff.denominator() for coeff in coeffs])
    return [coeff * denominator for coeff in coeffs]


def remove_squares(coeffs):
    '''Removes the square component form each item in coeffs.
    coeffs - List of coefficients. Should be either [a, b, c] or [a, b].
    Returns the new coefficients and the transformation matrix.
    '''
    T = matrix.identity(QQ, 3)
    
    # Remove squares from each of the coefficients:
    for i in range(len(coeffs)):
        for p in prime_divisors(coeffs[i]):
            v = valuation(coeffs[i], p)
            if v > 1:
                if v % 2 == 0:
                    coeffs[i] /= p**v
                    T[i,i] *= p**(v/2)
                elif v % 2 == 1:
                    coeffs[i] /= p**(v-1)
                    T[i,i] *= p**((v-1)/2)
    return coeffs, T


def remove_c(coeffs):
    '''coeffs = [a, b, c] is a list of 3 nonzero squarefree integers. They are not all positive or all negative.'''
    a, b, c = coeffs
    
    if [x < 0 for x in coeffs].count(True) == 2:
        a, b, c = -a, -b, -c
        # We do not need to track this transformation because it does not affect the solution set

    if c < 0:
        T = matrix.identity(QQ, 3)  # We already have a, b > 0, c < 0
    elif a < 0:
        a, c = c, a
        T = Matrix(QQ, [[0,0,1], [0,1,0], [1,0,0]])
    elif b < 0:
        b, c = c, b
        T = Matrix(QQ, [[1,0,0], [0,0,1], [0,1,0]])
    else:
        raise ValueError('a, b, and c cannot be all positive or all negative.')
    if c != -1:
        a *= -c
        b *= -c
        T = Matrix(QQ, [[1,0,0], [0,1,0], [0,0,c]]) * T

    return [a, b], T


def hasse_minkowski(a, b):
    [a, b], T = remove_squares([a, b])
    
    if abs(a) > abs(b):
        a, b = b, a
        T = Matrix([[0,1,0],[1,0,0],[0,0,1]]) * T
    
    # Terminating Conditions:
    if a == 1:
        return T.inverse() * vector(QQ, [1,0,1])
    elif b == 1:
        return T.inverse() * vector(QQ, [0,1,1])
    elif abs(a) + abs(b) <= 2:
        return None
    
    M = IntegerModRing(b)
    if not is_square(M(a)):
        return None
    t = sqrt_mod_n(a, b)
    if t > abs(b)/2:
        t -= b
    assert -abs(b)/2 <= t <= abs(b)/2

    new_b = (t*t - a) / b

    solution = hasse_minkowski(a, new_b)
    if solution is None:
        return None
    [p,q,r] = solution
    return T.inverse() * vector(QQ, [-t*p+r, new_b*q, -a*p+t*r])


def get_initial_point(coeffs):
    coeffs, T_diag = diagonalize(coeffs)
    a, b, c = remove_denominators(coeffs)
    
    if a == 0:
        return T.inverse() * vector(QQ, [1, 0, 0])
    elif b == 0:
        return T.inverse() * vector(QQ, [0, 1, 0])
    elif c == 0:
        return T.inverse() * vector(QQ, [0, 0, 1])
    elif all(map(lambda x: x > 0, [a, b, c])) or all(map(lambda x: x < 0, [a, b, c])):
        return None

    
    [a, b, c], T = remove_squares([a, b, c])
    
    [a, b], T_ = remove_c([a, b, c])
    T = T_ * T

    [a, b], T_ = remove_squares([a, b])  # We may need to square-free-ify again as we have changed a and b
    T = T_ * T

    solution = hasse_minkowski(a, b)
    if solution is None:
        return None
    
    return list(T_diag * T.inverse() * solution)


def integer_inverse_matrix(p, q, r):
    '''
    Computes a matrix A which sends (p:q:r) to (1:0:0) and has integer coefficients,
    and whose inverse also has integer coefficients.
    The integer coefficients ensure that we get a nice parametrization.
    '''
    g, u_pq, v_pq = extended_euclidean(p, q)
    d, u_rg, v_rg = extended_euclidean(r, g)
    if d != 1:
        raise ValueError('p, q and r should be coprime')
    if g == 0:
        assert(p == 0 and q == 0 and r == 1)
        A = Matrix(QQ, [[0,  1, 0],
                        [0,  0, 1],
                        [1,  0, 0]])
    else:
        A = Matrix(QQ, [[p, -v_pq, -u_rg*p/g],
                        [q,  u_pq, -u_rg*q/g],
                        [r,  0,     v_rg]])
    return A



def full_solve(C):
    if not C in R:
        try:
            C = R(C)
        except:
            raise ValueError('C should be a conic in QQ[x,y], not '+str(C))
    
    coeffs = coefficients(C)
    coeffs = remove_denominators(coeffs)
    a, b, c, d, e, f = coeffs

    if test_degenerate(coeffs):
        return None
    
    solution = get_initial_point(coeffs)
    if solution is None:
        return None
    
    [p,q,r] = solution

    # We want p, q, r to be coprime integers to get a nice parametrization.
    # We can multiply by anything nonzero to get another solution since the conic is homogenous.
    [p,q,r] = remove_denominators([p,q,r])
    devisor = gcd((p, q, r))
    p, q, r = p/devisor, q/devisor, r/devisor

    if r != 0:
        # This formula comes from the line-intersection property.
        # There is a slight speed-up by using this instead of the next one.
        # However, it does not work if the initial point is at infinity.
        x0 = -b*q*n**2 + c*p*m**2 - 2*q*c*m*n - d*r*n**2 - e*r*m*n - a*p*n**2
        y0 = -c*m**2*q - d*m*n*r - e*m**2*r - 2*a*m*n*p - b*m**2*p + a*n**2*q
        z0 = a*n**2*r + b*m*n*r + c*m**2*r

    else:
        # Transform so that (p, q, r) = (1, 0, 0):
        A = integer_inverse_matrix(p, q, r)
        a1, b1, c1, d1, e1, f1 = transform_conic(coeffs, A.inverse())
        C1 = R(a1*x**2 + b1*x*y + c1*y**2 + d1*x + e1*y + f1)

        # Use the line-intersection property in this transformed place:
        x1 = c1*n**2 - e1*m*n + f1*m**2
        y1 = -b1*n**2 + d1*m*n
        z1 = b1*m*n - d1*m**2
        solution = vector(QQ[m,n], [x1, y1, z1])

        final_solution = A * solution  # Transform back
        x0, y0, z0 = final_solution[0], final_solution[1], final_solution[2]


    #x0, y0, z0 = clean_parametrization(x0, y0, z0)

    return x0, y0, z0





def check(f, solution):
    if solution is None:
        print('f(x,y) = '+str(f)+' returned No Solutions\n')
        return
    
    elif len(solution) == 2:
        v = f.subs(x=solution[0], y=solution[1])
        if v == 0:
            print('f(x,y) = '+str(f)+' on '+str(solution)+' was 0\n')
        else:
            print('f(x,y) = '+str(f)+' on '+str(solution)+' was '+str(v)+' as opposed to 0\n')
    
    elif len(solution) == 3:
        g = f.homogenize('z')
        v = g.subs(x=solution[0], y=solution[1], z=solution[2])
        if v == 0:
            print('f(x,y) = '+str(f)+' on '+str(solution)+' was 0\n')
        else:
            print('f(x,y) = '+str(f)+' on '+str(solution)+' was '+str(v)+' as opposed to 0\n')


def demo_solve(f):
    '''This is used to deonstrate the code to solve conics.'''
    print('f(x,y) = '+str(f))
    coeffs = coefficients(f)
    coeffs = remove_denominators(coeffs)
    
    if test_degenerate(coeffs):
        print('Conic is degenerate')
        return
    
    solution = get_initial_point(coeffs)
    if solution is None:
        print('No solutions')
        return
    
    [p,q,r] = solution
    print('Initial point:', (p, q, r), '\n')

    x0, y0, z0 = full_solve(f)
    print('Parametrization:', (x0/z0, y0/z0), '\n')
    for m0, n0 in [(1, 0), (1, 2)]:
        try:
            sol = ((x0/z0).subs(m=m0, n=n0), (y0/z0).subs(m=m0, n=n0))
            print('Plugging in m='+str(m0)+', n='+str(n0)+':', sol)
            check(f, tuple(sol))
        except:
            sol = (x0.subs(m=m0, n=n0), y0.subs(m=m0, n=n0), z0.subs(m=m0, n=n0))
            print('Plugging in m='+str(m0)+', n='+str(n0), 'gives a point at infinity:', sol)
            check(f, tuple(sol))


def test_solve():
    print('Running tests:\n')
    functions = [R(x**2 + y**2 - 1),  # Pythagorean triples
                 R(2*x**2 + 4*y**2 - 1),
                 R(x**2 + 1/2*y**2 - 1/2),
                 R(29*x**2 + 11*y**2 - 1),
                 R(x**2 + y**2 - 3),  # Circle of Radius sqrt(3)
                 R(17*x**2 + 8*y**2 - 1),
                 R(x**2 + 2*x*y + y**2 - x + 1),
                 R(x**2 + 2*x*y + y**2 - 32*x + 16),
                 R(x**2 + x*y + y**2 - 32*x + 16),
                 R(y**2 + 2*x),
                 R(x**2 + 2*x*y + 4*y**2),  # Degenerate Conic
                 R(x**2 + y**2),  # Degenerate Conic
                 R(83*x**2 + 32*x*y - 2*y**2 + 1/2*x + 25*y + 74)]
    for f in functions:
        demo_solve(f)
        print('\n', end='')

f = R(x**2 + y**2 - 1)
g = R(x**2 + y**2 - 3)


"""
# Test the code:
if __name__ == '__main__':
    test_solve()
"""





