from sympy import *

class PeriodicCohomologyRing:
    def __init__(self, edges, cycles):
        if len(set(edges)) < len(edges):
            raise Exception('Names of edges repeated.')
        self.edges = edges
        self.cycles = cycles
        self.n = len(edges)
        self.d = len(cycles)
    
    def __str__(self):
        return 'Cohomology ring of the graph with edges {' + ','.join(self.edges) + '}'
    
    def term(self, coeff, expn):
        return PeriodicCohomologyRing.RingTerm(self, coeff, expn)
    
    def elem(self, terms):
        return PeriodicCohomologyRing.RingElem(self, terms)
    
    def _cycle(self, *coords):
        if len(coords) != self.d:
            return Exception(f'Should contain {self.d} input.')
        return tuple(sum([t[i] for t in [tuple(map(lambda i: a*i, c)) for a, c in zip(coords, self.cycles)]]) for i in range(self.n))
    
    def _const_to_term(self, const):
        return self.term(const, (0, 0, 0, 0, 0))
    
    def _cpe_to_term(self, const, power, expn):
            return self.term(lambda *v: const * prod(v[i]**power[i] for i in range(self.n)), expn)
    
    def _sum_terms(self, terms):
        if terms:
            s = terms[0]
            for term in terms[1:]:
                s += term
            return s
        return self._const_to_term(0)
        
    class RingTerm:
        def __init__(self, ring, coeff, expn):
            self.ring = ring
            self.coeff = coeff
            self.expn = tuple(expn)
            self.deg = sum(expn)
            self._syms = S([chr(105 + i) for i in range(self.ring.n)])
        
        def __str__(self):
            expr = str(self._symbolic())
            if expr == '0':
                return '0'
            dummies = [str(s) for i, s in enumerate(self._syms) if self.expn[i] != 0]
            var_expn = [f'{e}_{v}^{i}' if i != 1 else f'{e}_{v}' for e, v, i in zip(self.ring.edges, self._syms, self.expn) if i != 0]
            if expr == '1':
                return 'SUM_{' + ','.join(dummies) + '} ' + ' '.join(var_expn)
            in_brac = 0
            need_brac = False
            for (i, char) in enumerate(expr):
                if char == '(':
                    in_brac += 1
                if char == ')':
                    in_brac -= 1
                if i != 0 and char in ['+', '-'] and in_brac == 0:
                    need_brac = True
                    break
            if need_brac:
                return 'SUM_{' + ','.join(dummies) + '}' + f' ({expr}) ' + ' '.join(var_expn)
            return 'SUM_{' + ','.join(dummies) + '}' + f' {expr} ' + ' '.join(var_expn)
        
        def __add__(self, other):
            if self.expn != other.expn:
                raise Exception('The terms do not have the same variables.')
            return self.ring.term(lambda *v: self.coeff(*v) + other.coeff(*v), self.expn)
        
        def __sub__(self, other):
            if self.expn != other.expn:
                raise Exception('The terms do not have the same variables.')
            return self.ring.term(lambda *v: self.coeff(*v) - other.coeff(*v), self.expn)
        
        def __mul__(self, other):
            if type(self) == type(other):
                return self.ring.term(lambda *v: self.coeff(*v) * other.coeff(*v), [i + j for i, j in zip(self.expn, other.expn)])
            else:
                return self.ring.term(lambda *v: self.coeff(*v) * other, self.expn)

        def __rmul__(self, other):
            return self.ring.term(lambda *v: other * self.coeff(*v), self.expn)

        def act(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.term(lambda *v: self.coeff(*[x + i for x, i in zip(v, self.ring._cycle(*g))]), self.expn)
        
        def dif(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.act(*g) - self
        
        def print_grad(self):
            basis = [tuple(1 if j == i else 0 for j in range(self.ring.d)) for i in range(self.ring.d)]
            print('  ', self)
            for i, g in enumerate(basis):
                print(f'd{i+1}', self.dif(*g))
        
        def _symbolic(self):
            return simplify(self.coeff(*self._syms))
        
        def _polynomial(self):
            return Poly(self.coeff(*self._syms), self._syms)
        
        def _to_monomials(self):
            return self.ring.elem([self.ring._cpe_to_term(const, power, self.expn) for power, const in self._polynomial().as_dict().items()])
        
        def _indep_parts(self):
            indep_expn = [self.expn[i] if self._syms[i] not in self._symbolic().free_symbols else 0 for i in range(self.ring.n)]
            indep_terms = []
            for i in range(self.ring.n):
                indep_terms += [self.ring.term(lambda *v: 1, tuple(1 if j == i else 0 for j in range(self.ring.n)))] * indep_expn[i]
            rem_term = self.ring.term(self.coeff, [a - b for a, b in zip(self.expn, indep_expn)])
            return (indep_terms, rem_term)
    
    class RingElem():
        def __init__(self, ring, terms):
            self.ring = ring
            self.terms = [term for term in terms if str(term) != '0']
        
        def __str__(self):
            if self.terms:
                return ' + '.join([str(term) for term in self.terms])
            return '0'
        
        def __add__(self, other):
            return self.ring.elem(self.terms + other.terms)
        
        def __sub__(self, other):
            return self.ring.elem(self.terms + [-1 * term for term in other.terms])
        
        def __mul__(self, other):
            return self.ring.elem([term_1 * term_2 for term_1 in self.terms for term_2 in other.terms])
        
        def __rmul__(self, other):
            return self.ring.elem([other * term for term in self.terms])
        
        def act(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.elem([term.act(*g) for term in self.terms])
        
        def dif(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.elem([term.dif(*g) for term in self.terms])
        
        def print_grad(self):
            basis = [tuple(1 if j == i else 0 for j in range(self.ring.d)) for i in range(self.ring.d)]
            print('  ', self)
            for i, g in enumerate(basis):
                print(f'd{i+1}', self.dif(*g))
        
        def _combine_terms(self):
            expns = set(term.expn for term in self.terms)
            return self.ring.elem([self.ring._sum_terms([term for term in self.terms if term.expn == expn]) for expn in expns])
        
        
        

TP2 = PeriodicCohomologyRing(['x', 'y', 'z'], [(1, 0, -1), (0, 1, -1)])
tp2 = TP2.term(lambda i, j, k: -(j+k)*(j+k+1)*(2*j+2*k+1)/6, [0, 1, 1])
# tp2.print_grad()

TP3 = PeriodicCohomologyRing(['x', 'y', 'z', 'w'], [(1, 0, 0, -1), (0, 1, 0, -1), (0, 0, 1, -1)])
tp3 = TP3.term(lambda i, j, k, l: -(j+k+l)**2*(j+k+l+1)**2/4, [0, 1, 1, 1])
# tp3.print_grad()

X = PeriodicCohomologyRing(['x', 'y', 'z', 'w', 'a'], [(1, -1, 0, 0, 0), (0, 1, -1, 0, 1), (0, 0, 1, -1, 0)])
x = X.term(lambda i, j, k, l, m: -(j+k+l+m)**2*(j+k+l+m+1)**2/4, (0, 1, 1, 1, 1))
# y = X.term(lambda i, j, k, l, m: -(k+l+m)**2*(k+l+m+1)**2/4, [0, 1, 1, 1, 1])
y = X.term(lambda i, j, k, l, m: (k+l)**2, [0, 1, 1, 1, 1])
# print(y._term_to_monomials())
[print(t) for t in y._indep_parts()]

# e = X.elem([x, y])
# print(y)
# print(y._to_monomials())



# x.print_grad()
# y.print_grad()
# print(y._polynomial())
# print(y._polynomial().as_dict())
# expn = (0, 1, 1, 1, 1)
# data = [(const, power, expn) for power, const in y._polynomial().as_dict().items()]
# print(data)





# i, j, k = symbols('i, j, k')
# x = (i+j)**2
# print(Poly(x, (i, j, k)).as_dict())