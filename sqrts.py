from sage.all import *
import random


def tonelli_shanks(a, p):
    S = IntegerModRing(p)
    a = S(a)
    
    if p == 2:
        return sqrt_mod_2(a)
    elif a == 0:
        return 0
    elif kronecker(a, p) == -1:  # Check if a is not square mod p
        return None
    else:
        e = valuation(p-1, 2)
        q = (p-1) / 2**e

        legendre = 0
        while legendre != -1:
            z = S(random.randrange(2, p))
            legendre = kronecker(z, p)
        b = z**q  # b is in S

        r = a**((q+1)/2)
        t = a**q
        if t == 1:
            return r
        else:
            m = e-1
            while m > 0:
                if t**(2**(m-1)) == -1:
                    r *= b
                    t *= b**2
                b = b**2
                m -= 1
            return r

def sqrt_mod_2(a):
    a = IntegerModRing(4)(a)
    return ZZ(a)  # a is its own square root mod 2 because 0*0 = 0 and 1*1 = 1

def sqrt_mod_4(a):
    a = IntegerModRing(4)(a)
    if a == 0 or a == 1:
        return ZZ(a)
    if a == 2 or a == 3:
        return None

def sqrt_mod_8(a):
    a = IntegerModRing(8)(a)
    if a == 0 or a == 1:
        return ZZ(a)
    else:
        return None

def sqrt_2_adic(a, v):
    '''Computes the square root of a mod 2**v using Strong Hensel's Lemma.'''
    if IntegerModRing(2**v)(a) == 0:
        return 0
    
    v0 = valuation(a, 2)
    if v0 % 2 == 1:
        return None
    
    if v == 1:
        return sqrt_mod_2(a)
    elif v == 2:
        return sqrt_mod_4(a)
    
    a = ZZ(IntegerModRing(2**v)(a))
    R = Zp(2, prec = 2*v)
    u = R(a / 2**v0)
    S = IntegerModRing(8)
    
    u0 = sqrt_mod_8(u)
    if u0 is None:
        return None

    xn = R(u0)
    current_precision = 3  # We have a square root mod 8=2**3
    while current_precision < v:
        xn = xn - R((xn*xn-u) / (2*xn))
        current_precision = 2*current_precision - 2
    return Zp(2, prec=v)(xn * 2**(v0/2))


def sqrt_p_adic(a, p, v):
    '''Algorithm to compute p-adic square roots using Hensel's Lemma. v is precision.'''
    if IntegerModRing(p**v)(a) == 0:
        return 0

    v0 = valuation(a, p)
    if v0 % 2 == 1:
        return None
    if p == 2:
        return sqrt_2_adic(a, v)

    R = Zp(p, prec=v)
    u = R(a / p**v0)
    S = IntegerModRing(p)
    u0 = S(u)
    if not is_square(u0):
        return None
    
    xn = R(ZZ(tonelli_shanks(u0, p)))  # A conversion to ZZ is needed to maintain precision
    for i in range(ceil(log(v, 2).n())):
        xn = xn - R((xn*xn-u) / (2*xn))

    return xn * p**(v0/2)



def extended_euclidean(a, b):
    if abs(b) > abs(a):
        d, v, u = extended_euclidean(b, a)
        return d, u, v

    elif b == 0:
        if a == 0:
            return 0, 1, 1
        return abs(a), ZZ(a/abs(a)), 0

    else:
        d, u, v = extended_euclidean(b, a % b)
        if d > 0:
            return d, v, u - floor(a/b) * v
        else:
            return -d, -v, -u + floor(a/b) * v

def crt(congruences):
    '''
    Congruences: a list of tuples (n_i, x_i)
    Finds x mod n = n_1n_2...n_k which satisfies all the congruences.'''
    N = 1
    for _, n_i in congruences:
        N *= n_i

    x = 0
    for x_i, n_i in congruences:
        N_i = N / n_i
        d, u, v = extended_euclidean(n_i, N_i)
        if d != 1:
            raise ValueError('The moduli are required to be pairwise coprime.')
        x += x_i * N_i * v
    return x

def sqrt_mod_n(a, n):
    S = IntegerModRing(n)
    congruences = []
    for p in prime_divisors(n):
        v = valuation(n, p)
        R = IntegerModRing(p**v)
        x = sqrt_p_adic(a, p, v)
        if x is None:
            return None
        x = ZZ(x)
        congruences.append((x, p**v))
    return ZZ(S(crt(congruences)))

def test_euclidean():
    test_pairs = [(50, 70), (-50, 70), (50, -70), (-50, -70), (-70, -50)]
    for x, y in test_pairs:
        d, u, v = extended_euclidean(x, y)
        print('extended_euclid('+str(x)+', '+str(y)+') = '+str(d))
        print(str(u)+'*'+str(x)+' + '+str(v)+'*'+str(y)+' = '+str(u*x+v*y))
    print('\n')

def test_mod_p():
    print('sqrt(4) = '+str(tonelli_shanks(4, 7))+' (mod 7)')
    print('sqrt(1) = '+str(tonelli_shanks(1, 3))+' (mod 3)')
    print('sqrt(16) = '+str(tonelli_shanks(16, 17))+' (mod 17)')
    print('sqrt(-1) = '+str(tonelli_shanks(-1, 17))+' (mod 17)')

def test_p_adic():
    print('sqrt(4) = '+str(sqrt_p_adic(4, 5, 30))+'\n')
    print('sqrt(6) = '+str(sqrt_p_adic(6, 5, 30))+'\n')
    print('sqrt(150) = '+str(sqrt_p_adic(150, 5, 30))+'\n')
    print('sqrt(17) = '+str(sqrt_p_adic(17, 2, 30))+'\n')
    print('sqrt(144) = '+str(sqrt_p_adic(144, 2, 30)))  # computes -12 in Z_2   0_0
    print('sqrt(16) = '+str(sqrt_p_adic(16, 2, 6)))
    print('sqrt(2) = '+str(sqrt_p_adic(2, 3, 30))+'\n')

def test_modular():
    print('sqrt(36) = '+str(sqrt_mod_n(36, 101))+' (mod 101)')
    print('sqrt(4) = '+str(sqrt_mod_n(4, 10))+' (mod 10)')
    print('sqrt(100) = '+str(sqrt_mod_n(100, 630))+' (mod 630)')
    print('sqrt(1216) = '+str(sqrt_mod_n(1216, 1728))+' (mod 1728)')
    print('sqrt(12) = '+str(sqrt_mod_n(12, 88))+' (mod 88)')

    '''
    for n in range(2, 1000):  # managed to test up to 640 or so before cypari leak
        for a in range(n):
            x = sqrt_mod_n(a, n)
            R = IntegerModRing(n)
            if x is None:
                y = sqrt(R(a))
                if y in R:
                    print(f'computing sqrt({a}) (mod {n}).')
                    print(f'program output: {x}')
                    print(f'true output: {y}')
                    print('fail\n')
            elif R(x*x) != R(a):
                print(f'computing sqrt({a}) (mod {n}).', end=' ')
                print(f'program output: {x}')
                print('fail\n')
        if n % 10 == 0: print(f'finished testing roots up to mod {n}')
    '''

if __name__ == '__main__':
    test_mod_p()
    test_p_adic()
    print('\n\n')
    test_modular()
    test_euclidean()



