"""Exact cached linear evidence and certified relaxed bounds, with no truth access.

Each output has a separate integer coefficient vector g in [0, gmax]^d with
at most sparsity nonzeros. Features are lag-major binary histories, although
only their flattened ordering matters here. Observed integer equations are
retained verbatim. LP bounds use the NECESSARY relaxation sum(g)<=gmax*sparsity,
not exact support-count inference. Floating solver output is never a proof:
arbitrary rational dual multipliers yield a directly checkable exact bound.
"""
from fractions import Fraction
import math
import numbers


class CachedLinearEvidence:
    """Reuse all observed equations across future histories and missions.

    infer_vector returns an output tuple of Fractions, or None outside row span.
    get_fully_identified_operator returns output-major coefficient tuples.
    bound_vector returns an integer upper bound and an exact certificate; all
    Fraction fields can be serialized using numerator/denominator. No MILP
    infeasibility or sparse obstruction is claimed by this implementation.
    """

    def __init__(self, n_inputs, n_outputs, max_lag, sparsity, gmax=4):
        values = (n_inputs, n_outputs, max_lag, sparsity, gmax)
        if any(not isinstance(x, numbers.Integral) for x in values):
            raise ValueError('Dimensions, sparsity, and gmax must be integers')
        if n_inputs < 1 or n_outputs < 1 or max_lag < 0 or sparsity < 0 or gmax < 1:
            raise ValueError('Invalid dimensions, sparsity, or gmax')
        self.n_inputs, self.n_outputs, self.max_lag = map(int, values[:3])
        self.d = self.n_inputs * (self.max_lag + 1)
        self.sparsity, self.gmax = int(sparsity), int(gmax)
        self.A, self.b = [], []
        self._basis = {}  # pivot -> (normalized feature row, output row)
        self.stats = dict(rows=0, rank=0, infer_calls=0, span_hits=0,
                          bound_calls=0, lp_calls=0, lp_failures=0)

    @staticmethod
    def _integers(row, length, binary=False):
        row = tuple(row)
        if len(row) != length:
            raise ValueError(f'Expected row of length {length}')
        result = []
        for value in row:
            try:
                integer = int(value)
            except (ValueError, TypeError, OverflowError) as exc:
                raise ValueError('Expected finite exact integers') from exc
            if value != integer or (binary and integer not in (0, 1)):
                raise ValueError('Expected binary features' if binary else 'Expected exact integers')
            result.append(integer)
        return tuple(result)

    def add_rows(self, A, b):
        """Add row-major A (k,d), b (k,m), atomically rejecting inconsistency.

        Checks exact linear consistency, not sparse-model feasibility. A zero
        feature row must have zero outputs; other zero outputs remain useful
        equalities (including nonnegativity consequences in the LP).
        """
        rows = [self._integers(row, self.d, binary=True) for row in A]
        outputs = [self._integers(row, self.n_outputs) for row in b]
        if len(rows) != len(outputs):
            raise ValueError('A and b must have the same number of rows')
        basis = {p: (v.copy(), w.copy()) for p, (v, w) in self._basis.items()}
        for row, output in zip(rows, outputs):
            v, w = list(map(Fraction, row)), list(map(Fraction, output))
            for p in sorted(basis):
                bv, bw = basis[p]
                c = v[p]
                if c:
                    v = [x - c*y for x, y in zip(v, bv)]
                    w = [x - c*y for x, y in zip(w, bw)]
            pivot = next((j for j, x in enumerate(v) if x), None)
            if pivot is None:
                if any(w):
                    raise ValueError('Observations are exactly linearly inconsistent')
                continue
            c = v[pivot]
            v, w = [x/c for x in v], [x/c for x in w]
            for p, (bv, bw) in list(basis.items()):
                c = bv[pivot]
                if c:
                    basis[p] = ([x-c*y for x, y in zip(bv, v)],
                                [x-c*y for x, y in zip(bw, w)])
            basis[pivot] = (v, w)
        self.A.extend(rows)
        self.b.extend(outputs)
        self._basis = basis
        self.stats.update(rows=len(self.A), rank=len(basis))

    def infer_vector(self, a):
        """Infer all output values exactly when a is in the evidence row span."""
        a = self._integers(a, self.d)
        self.stats['infer_calls'] += 1
        v, result = list(map(Fraction, a)), [Fraction(0)]*self.n_outputs
        for p in sorted(self._basis):
            bv, bw = self._basis[p]
            c = v[p]
            if c:
                v = [x-c*y for x, y in zip(v, bv)]
                result = [x+c*y for x, y in zip(result, bw)]
        if any(v):
            return None
        self.stats['span_hits'] += 1
        return tuple(result)

    def get_fully_identified_operator(self):
        if len(self._basis) != self.d:
            return None
        return tuple(tuple(self._basis[j][1][i] for j in range(self.d))
                     for i in range(self.n_outputs))

    @staticmethod
    def _rationalize(value):
        # Fixed dyadic grid; validity never depends on approximation quality.
        if not math.isfinite(float(value)):
            raise ValueError('Non-finite solver multiplier')
        return Fraction(round(float(value)*(1 << 20)), 1 << 20)

    def _certificate(self, a, output, y, lam):
        residual = tuple(Fraction(a[j])-sum(
            (y[k]*self.A[k][j] for k in range(len(self.A))), Fraction(0))-lam
            for j in range(self.d))
        exact = (sum((y[k]*self.b[k][output] for k in range(len(self.A))), Fraction(0))
                 + lam*self.gmax*self.sparsity
                 + self.gmax*sum((max(Fraction(0), r) for r in residual), Fraction(0)))
        return dict(y=tuple(y), lambda_=lam, residual=residual,
                    exact_upper=exact, gmax=self.gmax, sparsity=self.sparsity,
                    relaxation='box bounds and sum(g) <= gmax*sparsity')

    def bound_vector(self, a, output):
        """Certified upper bound on integer a@g for one output.

        For any rational y and lambda>=0 the bound is
        y*b + lambda*gmax*s + gmax*sum(max(0,a-A.T*y-lambda)).
        Taking floor is sound because both a and g are integral. The certificate
        refers to the current stored rows in order. Even LP errors fall back to
        a valid bound, not an infeasibility assertion. witness is always None.
        """
        a = self._integers(a, self.d)
        if not isinstance(output, numbers.Integral) or not 0 <= output < self.n_outputs:
            raise ValueError('Invalid output index')
        self.stats['bound_calls'] += 1
        zeros = [Fraction(0)]*len(self.A)
        # Box-only and sum-budget candidates are valid without a solver.
        candidates = [self._certificate(a, output, zeros, Fraction(0)),
                      self._certificate(a, output, zeros, Fraction(max(0, max(a))))]
        status = 'not_run'
        try:
            import numpy as np
            from scipy.optimize import linprog
            self.stats['lp_calls'] += 1
            result = linprog(-np.asarray(a, dtype=float),
                             A_ub=np.ones((1, self.d)),
                             b_ub=[self.gmax*self.sparsity],
                             A_eq=np.asarray(self.A, dtype=float) if self.A else None,
                             b_eq=np.asarray([b[output] for b in self.b], dtype=float) if self.A else None,
                             bounds=(0, self.gmax), method='highs')
            status = str(result.message)
            if result.success:
                y = [self._rationalize(-v) for v in result.eqlin.marginals]
                lam = max(Fraction(0), self._rationalize(-result.ineqlin.marginals[0]))
                candidates.append(self._certificate(a, output, y, lam))
            else:
                self.stats['lp_failures'] += 1
        except (ImportError, ValueError, RuntimeError, OverflowError) as exc:
            status = f'LP unavailable or failed: {type(exc).__name__}: {exc}'
            self.stats['lp_failures'] += 1
        certificate = min(candidates, key=lambda c: c['exact_upper'])
        return dict(upper=math.floor(certificate['exact_upper']),
                    certificate=certificate, solver_status=status, witness=None)
