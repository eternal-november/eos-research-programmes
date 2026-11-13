"""Tiny exact polynomial arithmetic, using only Python's standard library.

A monomial is a sorted tuple of variable names, with repetition for powers.
This module is intentionally elementary and has no floating-point operations.
"""
from fractions import Fraction
from collections import Counter


def rational(value):
    if isinstance(value, float):
        raise TypeError('Use an int, Fraction, or rational string, never float.')
    return Fraction(value)


class Poly:
    def __init__(self, terms=None):
        self.terms = {}
        for monomial, coefficient in (terms or {}).items():
            key = tuple(sorted(monomial))
            value = self.terms.get(key, Fraction(0)) + rational(coefficient)
            if value:
                self.terms[key] = value
            else:
                self.terms.pop(key, None)

    @staticmethod
    def constant(value):
        return Poly({(): rational(value)})

    @staticmethod
    def variable(name):
        return Poly({(name,): Fraction(1)})

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Poly) else Poly.constant(other)

    def __add__(self, other):
        terms = dict(self.terms)
        for monomial, value in self.coerce(other).terms.items():
            terms[monomial] = terms.get(monomial, Fraction(0)) + value
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        terms = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                key = tuple(sorted(m + n))
                terms[key] = terms.get(key, Fraction(0)) + c * d
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, power):
        if not isinstance(power, int) or power < 0:
            raise ValueError('Only nonnegative integer powers are supported.')
        result = Poly.constant(1)
        for _ in range(power):
            result = result * self
        return result

    def __truediv__(self, scalar):
        return self * (1 / rational(scalar))

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    @property
    def variables(self):
        return set(v for m in self.terms for v in m)

    @property
    def degree(self):
        return max((len(m) for m in self.terms), default=0)

    def derivative(self, variable):
        terms = {}
        for monomial, coefficient in self.terms.items():
            multiplicity = monomial.count(variable)
            if multiplicity:
                reduced = list(monomial)
                reduced.remove(variable)
                key = tuple(reduced)
                terms[key] = terms.get(key, Fraction(0)) + coefficient * multiplicity
        return Poly(terms)

    def evaluate(self, point):
        result = Fraction(0)
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for variable in monomial:
                if variable not in point:
                    raise KeyError('Missing coordinate: ' + variable)
                term *= rational(point[variable])
            result += term
        return result

    def evaluate_with_squared_coordinates(self, point, squared_coordinates):
        """Evaluate a polynomial even in selected coordinates exactly.

        A coordinate whose square is rational can be an algebraic square
        root. Every occurrence must have even exponent; odd powers raise
        rather than being silently approximated. Only Fraction arithmetic
        is used, and all supplied squared values must be nonnegative.
        """
        squares = {v: rational(value) for v, value in squared_coordinates.items()}
        if any(value < 0 for value in squares.values()):
            raise ValueError('A real squared coordinate cannot be negative.')
        result = Fraction(0)
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for variable, exponent in Counter(monomial).items():
                if variable in squares:
                    if exponent % 2:
                        raise ValueError('Odd power of square-root coordinate: ' + variable)
                    term *= squares[variable] ** (exponent // 2)
                else:
                    if variable not in point:
                        raise KeyError('Missing coordinate: ' + variable)
                    term *= rational(point[variable]) ** exponent
            result += term
        return result

    def substituted(self, mapping):
        """Substitute selected variables by exact constants or polynomials."""
        result = Poly.constant(0)
        for monomial, coefficient in self.terms.items():
            term = Poly.constant(coefficient)
            for variable in monomial:
                term = term * mapping.get(variable, Poly.variable(variable))
            result = result + term
        return result

    def renamed(self, mapping):
        terms = {}
        for monomial, coefficient in self.terms.items():
            key = tuple(sorted(mapping.get(v, v) for v in monomial))
            terms[key] = terms.get(key, Fraction(0)) + coefficient
        return Poly(terms)

    def __repr__(self):
        if not self.terms:
            return '0'
        chunks = []
        for monomial, coefficient in sorted(self.terms.items(), key=lambda p: (len(p[0]), p[0])):
            counts = Counter(monomial)
            variables = '*'.join(v if n == 1 else f'{v}^{n}' for v, n in sorted(counts.items()))
            chunks.append(str(coefficient) + ('*' + variables if variables else ''))
        return ' + '.join(chunks)


def objective(residuals):
    """Unweighted sum of squared residuals, with no hidden one-half factor."""
    return sum((residual ** 2 for residual in residuals.values()), Poly.constant(0))


def gradient(polynomial, point, variables=None):
    variables = sorted(polynomial.variables) if variables is None else list(variables)
    return {v: polynomial.derivative(v).evaluate(point) for v in variables}


def jacobian_gradient(residuals, point, variables):
    """An independent chain-rule calculation of 2 J_r(point)^T r(point)."""
    return {
        v: sum((2 * r.evaluate(point) * r.derivative(v).evaluate(point)
                for r in residuals.values()), Fraction(0))
        for v in variables
    }
