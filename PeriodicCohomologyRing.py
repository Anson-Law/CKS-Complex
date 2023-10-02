from sympy import *
from collections import Counter
from functools import reduce

class PeriodicCohomologyRing:
    def __init__(self, edges, cycles, bonds=None, tree=None):
        if len(set(edges)) < len(edges):
            raise Exception('Names of edges repeated.')
        self._repl_dict = {}
        if tree is not None:
            for (i, e) in enumerate(edges):
                if e not in tree:
                    check = [cycle for cycle in cycles if cycle[i] != 0]
                    if len(check) != 1 or check[0][i] != 1:
                        raise Exception('Tree and cycles are not compatible with each other.')
                    self._repl_dict[e] = tuple(-k if j != i else 0 for j, k in enumerate(check[0]))
                else:
                    self._repl_dict[e] = tuple(1 if f == e else 0 for f in edges)
        self.edges = edges
        self.cycles = cycles
        self.bonds = bonds
        self.tree = tree
        self.n = len(edges)
        self.d = len(cycles)
    
    def __str__(self):
        return 'Cohomology ring of the graph with edges {' + ','.join(self.edges) + '}'
    
    def term(self, coeff, expn, check_bond=True):
        return PeriodicCohomologyRing.RingTerm(self, coeff, expn, check_bond)
    
    def elem(self, terms, combine_terms=False):
        return PeriodicCohomologyRing.RingElem(self, terms, combine_terms)
    
    def _cycle(self, *coords):
        if len(coords) != self.d:
            return Exception(f'Should contain {self.d} input.')
        return tuple(sum([t[i] for t in [tuple(map(lambda i: a*i, c)) for a, c in zip(coords, self.cycles)]]) for i in range(self.n))
    
    def _const_to_term(self, const, check_bond=True):
        return self.term(lambda *v: const, tuple(0 for _ in range(self.n)), check_bond)
    
    def _edge_to_term(self, edge, check_bond=True):
        ind = self.edges.index(edge)
        return self.term(lambda *v: 1, tuple(1 if i == ind else 0 for i in range(self.n)), check_bond)
    
    def as_term(self, x):
        if isinstance(x, PeriodicCohomologyRing.RingTerm):
            return x
        elif x in self.edges:
            return self._edge_to_term(self, x)
        elif sympify(x).is_number:
            return self._const_to_term(x)
        else:
            raise Exception(f'Unknown type {type(x)}.')
    
    def as_elem(self, x):
        if isinstance(x, PeriodicCohomologyRing.RingElem):
            return x
        elif isinstance(x, PeriodicCohomologyRing.RingTerm):
            return self.elem([x])
        elif x in self.edges:
            return self.elem([self._edge_to_term(self, x)])
        elif sympify(x).is_number:
            return self.elem([self._const_to_term(x)])
        else:
            raise Exception(f'Unknown type {type(x)}.')
    
    def _cpe_to_term(self, const, power, expn, check_bond=True):
            return self.term(lambda *v: const * prod(v[i]**power[i] for i in range(self.n)), expn, check_bond)
    
    def _sum_terms(self, terms):
        if terms:
            s = terms[0]
            for term in terms[1:]:
                s += term
            return s
        return self._const_to_term(0)
    
    def _prod_terms(self, terms):
        if terms:
            s = terms[0]
            for term in terms[1:]:
                s *= term
            return s
        return self._const_to_term(1)
    
    def _sum_elems(self, elems):
        if elems:
            s = elems[0]
            for elem in elems[1:]:
                s += elem
            return s
        return self.elem([self._const_to_term(0)])
    
    def _prod_elems(self, elems):
        if elems:
            s = elems[0]
            for elem in elems[1:]:
                s *= elem
            return s
        return self.elem([self._const_to_term(1)])
    
    def E1(self, edge):
        return self.elem([self.term(lambda *v: 1, tuple(1 if e == edge else 0 for e in self.edges))])
    
    def Ei(self, edge):
        return self.elem([self.term(lambda *v: v[self.edges.index(edge)], tuple(1 if e == edge else 0 for e in self.edges))])
    
    #####
    # def bond_to_inv(self, bond):
    #     if bond not in self.bonds:
    #         raise Exception('Not a valid bond.')
    #     syms_1 = symbols([chr(ord(x) - 32) + '1' for x in self.edges])
    #     syms_i = symbols([chr(ord(x) - 32) + 'i' for x in self.edges])
    #     bond_id = [i for i, x in enumerate(self.edges) if x in bond]
    #     x = sum([prod([syms_i[j] if i == j else syms_1[j] for j in bond_id]) for i in bond_id])
    #     bond_subs = [(syms_1[i], sum([k * syms_1[j] for (j, k) in enumerate(self._repl_dict[e])])) for (i, e) in enumerate(self.edges)]
    #     remain = [t for t in factor(expand(x.subs(bond_subs))).args if t in syms_1]
    #     invariant = [t for t in factor(expand(x.subs(bond_subs))).args if t not in syms_1]
    #     return invariant

    # def bond_to_inv(self, bond):
    #     if bond not in self.bonds:
    #         raise Exception('Not a valid bond.')
    #     bond_id = [i for i, x in enumerate(self.edges) if x in bond]
    #     x = self.term(lambda *v: sum([v[i] for i in bond_id]), tuple(1 if i in bond_id else 0 for i in range(self.n)), check_bond=False)._to_monomials(check_bond=False)
    #     x1 = X._sum_elems([term._normalize() for term in x.terms])._combine_terms()
    #     indep_edges = list(reduce(lambda x, y: x & y, [Counter(term._indep_parts()[0]) for term in x1.terms]).elements())
    #     indep_edges_id = tuple(indep_edges.count(e) for e in self.edges)
    #     remaining_elem = X.elem([X.term(term.coeff, tuple(i - j for i, j in zip(term.expn, indep_edges_id))) for term in x1.terms])
    #     return (indep_edges, remaining_elem)
        
    class RingTerm:
        def __init__(self, ring, coeff, expn, check_bond):
            if len(expn) != ring.n:
                raise Exception(f'The argument expn should be of length {ring.n}.')
            self.ring = ring
            support = [e for (i, e) in enumerate(ring.edges) if expn[i]]
            if check_bond and any([all([e in support for e in bond]) for bond in ring.bonds]):
                self.coeff = lambda *v: 0
                self.expn = tuple(expn)
            else:
                self.coeff = coeff
                self.expn = tuple(expn)
            self.deg = sum(expn)
            self._syms = symbols([chr(105 + i) for i in range(self.ring.n)])
        
        def __str__(self):
            expr = str(self._symbolic())
            if all(i == 0 for i in self.expn) or expr == '0':
                return expr
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
            neg = False
            if expr.startswith('-') and not need_brac:
                expr = expr[1:]
                neg = True
            if need_brac:
                return ('- ' if neg else '') + 'SUM_{' + ','.join(dummies) + '}' + f' ({expr}) ' + ' '.join(var_expn)
            return ('- ' if neg else '') + 'SUM_{' + ','.join(dummies) + '}' + f' {expr} ' + ' '.join(var_expn)
        
        def __add__(self, other):
            if self.expn != other.expn:
                raise Exception('The terms do not have the same variables.')
            return self.ring.term(lambda *v: self.coeff(*v) + other.coeff(*v), self.expn)
        
        def __sub__(self, other):
            if self.expn != other.expn:
                raise Exception('The terms do not have the same variables.')
            return self.ring.term(lambda *v: self.coeff(*v) - other.coeff(*v), self.expn)
        
        def __mul__(self, other):
            _other = self.ring.as_term(other)
            return self.ring.term(lambda *v: self.coeff(*v) * _other.coeff(*v), [i + j for i, j in zip(self.expn, _other.expn)])

        def __rmul__(self, other):
            _other = self.ring.as_term(other)
            return self.ring.term(lambda *v: _other.coeff(*v) * self.coeff(*v), [i + j for i, j in zip(_other.expn, self.expn)])
        
        def __neg__(self):
            return -1 * self

        def act(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.term(lambda *v: self.coeff(*[x + i for x, i in zip(v, self.ring._cycle(*g))]), self.expn)
        
        def dif(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.act(*g) - self
        
        def grad(self):
            basis = [tuple(1 if j == i else 0 for j in range(self.ring.d)) for i in range(self.ring.d)]
            return tuple(self.dif(g) for g in basis)
        
        def show_grad(self):
            tup = self.grad()
            print('  ', self)
            for i, term in enumerate(tup):
                print(f'd{i+1}', term)
        
        def _symbolic(self):
            return simplify(self.coeff(*self._syms))
        
        def _polynomial(self):
            return Poly(self.coeff(*self._syms), self._syms)
        
        def _to_monomials(self, check_bond=True):
            return self.ring.elem([self.ring._cpe_to_term(const, power, self.expn, check_bond) for power, const in self._polynomial().as_dict().items()])
        
        def _indep_parts(self):
            indep_expn = [self.expn[i] if self._syms[i] not in self._symbolic().free_symbols else max(self.expn[i]-1, 0) for i in range(self.ring.n)]
            indep_edges = []
            for i, e in enumerate(self.ring.edges):
                indep_edges += [e] * indep_expn[i]
            rem_term = self.ring.term(self.coeff, [a - b for a, b in zip(self.expn, indep_expn)])
            return (indep_edges, rem_term)
        
        def _normalize(self):
            indep_edges, rem_term = self._indep_parts()
            indep_repl = [self.ring.elem([j * self.ring._edge_to_term(self.ring.edges[i]) for i, j in enumerate(self.ring._repl_dict[e])]) for e in indep_edges]
            return self.ring._prod_elems(indep_repl + [self.ring.elem([rem_term])])
            
        #####
        # def show_indep_parts(self, *syms):
        #     if not syms:
        #         syms = symbols([chr(ord(x) - 32) for x in self.ring.edges])
        #     indep_edges, rem_term = self._indep_parts()
        #     indep_term = prod([syms[self.ring.edges.index(e)] for e in indep_edges])
        #     if indep_edges:
        #         if any(rem_term.expn):
        #             print(f'{indep_term}*({rem_term})')
        #         print(rem_term._symbolic() * indep_term)
        #     return print(rem_term)

    class RingElem():
        def __init__(self, ring, terms, combine_terms):
            self.ring = ring
            _terms = [term for term in terms if str(term) != '0']
            if combine_terms:
                _expns = set(term.expn for term in _terms)
                self.terms = [self.ring._sum_terms([term for term in _terms if term.expn == expn]) for expn in _expns]
            else:
                self.terms = _terms
        
        def __str__(self):
            show = ''
            for term in self.terms:
                sterm = str(term)
                if sterm.startswith('-'):
                    show += f' - {sterm[2:]}'
                else:
                    show += f' + {sterm}'
            return show.lstrip(' +') if show else '0'
        
        def __add__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem(self.terms + _other.terms)
        
        def __radd__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem(_other.terms + self.terms)
        
        def __sub__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem(self.terms + (-_other).terms)
        
        def __rsub__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem(_other.terms + (-self).terms)
        
        def __mul__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem([term_1 * term_2 for term_1 in self.terms for term_2 in _other.terms])
        
        def __rmul__(self, other):
            _other = self.ring.as_elem(other)
            return self.ring.elem([term_1 * term_2 for term_1 in _other.terms for term_2 in self.terms])
        
        def __neg__(self):
            return -1 * self
        
        def __eq__(self, other):
            _self = self.normalize()
            _other = self.ring.as_elem(other).normalize()
            eq = []
            for term1 in _self.terms:
                for term2 in _other.terms:
                    if term1.expn == term2.expn:
                        eq.append(term1._symbolic() == term2._symbolic())
            return len(eq) == len(_self.terms) and len(_self.terms) == len(_other.terms) and all(eq)
        
        def _combine_terms(self):
            expns = set(term.expn for term in self.terms)
            return self.ring.elem([self.ring._sum_terms([term for term in self.terms if term.expn == expn]) for expn in expns])
        
        def act(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.elem([term.act(*g) for term in self.terms])
        
        def dif(self, *g):
            if len(g) != self.ring.d:
                raise Exception(f'Should contain {self.ring.d} arguments.')
            return self.ring.elem([term.dif(*g) for term in self.terms])
        
        def grad(self, norm=True):
            basis = [tuple(1 if j == i else 0 for j in range(self.ring.d)) for i in range(self.ring.d)]
            if norm:
                return tuple(self.dif(*g).normalize() for g in basis)
            return tuple(self.dif(*g) for g in basis)
        
        def show_grad(self, norm=True):
            tup = self.grad(norm=norm)
            print('  ', self)
            for i, elem in enumerate(tup):
                print(f'd{i+1}', elem)
        
        def normalize(self):
            x = self.ring._sum_elems([term._to_monomials() for term in self._combine_terms().terms])
            return self.ring._sum_elems([term._normalize() for term in x.terms])._combine_terms()
        
        #####
        # def show_indep_parts(self, *syms):
        #     if not syms:
        #         syms = symbols([chr(ord(x) - 32) for x in self.ring.edges])
        #     show = []
        #     if self.terms:
        #         for term in self.terms:
        #             indep_edges, rem_term = term._indep_parts()
        #             indep_term = prod([syms[self.ring.edges.index(e)] for e in indep_edges])
        #             if indep_edges:
        #                 if any(rem_term.expn):
        #                     show.append(f'{indep_term}*({rem_term})')
        #                 else:
        #                     show.append(str(rem_term._symbolic() * indep_term))
        #             else:
        #                 show.append(str(rem_term))
        #     else:
        #         show = '0'
        #     print(' + '.join(show))
        
        
        

# TP2 = PeriodicCohomologyRing(['x', 'y', 'z'], [(1, 0, -1), (0, 1, -1)])
# tp2 = TP2.term(lambda i, j, k: -(j+k)*(j+k+1)*(2*j+2*k+1)/6, (0, 1, 1))
# tp2.show_grad()

# TP3 = PeriodicCohomologyRing(['x', 'y', 'z', 'w'], [(1, 0, 0, -1), (0, 1, 0, -1), (0, 0, 1, -1)])
# tp3 = TP3.term(lambda i, j, k, l: -(j+k+l)**2*(j+k+l+1)**2/4, (0, 1, 1, 1))
# tp3.show_grad()

R = PeriodicCohomologyRing(
    ['x', 'y', 'z', 'w', 'a'],
    [(1, -1, 0, 0, 0), (0, 1, -1, 0, 1), (0, 0, -1, 1, 0)],
    bonds = [['x', 'y', 'a'], ['z', 'w', 'a'], ['x', 'y', 'z', 'w']],
    tree = ['y', 'z']
)

inv0 = R.Ei('x') + R.Ei('y') + R.Ei('z') + R.Ei('w') + R.Ei('a')
inv1 = R.E1('a') * (R.Ei('x') + R.Ei('y')) - R.E1('y') * R.Ei('a')
inv2 = R.E1('a') * (R.Ei('z') + R.Ei('w')) + R.E1('z') * R.Ei('a')
inv3 = R.E1('z') * (R.Ei('x') + R.Ei('y')) + R.E1('y') * (R.Ei('z') + R.Ei('w'))
print(inv1 + inv2 == R.E1('a') * inv0)
print(inv3 - inv1 == R.E1('y') * inv0)
print(inv3 + inv2 == R.E1('z') * inv0)

