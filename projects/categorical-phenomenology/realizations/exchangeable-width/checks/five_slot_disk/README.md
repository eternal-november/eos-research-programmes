# Explicit five-slot disk filling

A vertex abc means that components A,B,C occupy slots a,b,c. The color generator is g(a,b,c)=(b,c,a). Take gamma=123 423 421 431 231. The boundary is gamma*(g gamma)*(g² gamma).

Initial boundary: 123 423 421 431 231 234 214 314 312 342 142 143 123

Elementary edge-path homotopy (T+ inserts a triangle side, T− removes a triangle corner, S crosses a square, B removes a backtrack):

1. T+: 123 523 423 421 431 231 234 214 314 312 342 142 143 123
2. S: 123 523 521 421 431 231 234 214 314 312 342 142 143 123
3. S: 123 523 521 531 431 231 234 214 314 312 342 142 143 123
4. T−: 123 523 521 531 231 234 214 314 312 342 142 143 123
5. S: 123 523 521 531 534 234 214 314 312 342 142 143 123
6. S: 123 523 521 524 534 234 214 314 312 342 142 143 123
7. T−: 123 523 524 534 234 214 314 312 342 142 143 123
8. S: 123 523 524 534 514 214 314 312 342 142 143 123
9. T−: 123 523 524 514 214 314 312 342 142 143 123
10. T−: 123 523 524 514 314 312 342 142 143 123
11. S: 123 523 513 514 314 312 342 142 143 123
12. S: 123 523 513 514 512 312 342 142 143 123
13. T−: 123 523 513 512 312 342 142 143 123
14. S: 123 523 513 512 542 342 142 143 123
15. T−: 123 523 513 512 542 142 143 123
16. S: 123 523 513 543 542 142 143 123
17. T−: 123 523 543 542 142 143 123
18. S: 123 143 543 542 142 143 123
19. S: 123 143 142 542 142 143 123
20. B: 123 143 142 143 123
21. B: 123 143 123
22. B: 123

Counts: {'triangle_expand': 1, 'square': 11, 'triangle_contract': 7, 'backtrack': 3}. The 19 triangle/square crossings give a finite van Kampen filling; backtrack removals are degenerate folds.

Every triangle varies one component among three unused-by-the-others slots; every square varies two components independently between disjoint pairs of slots. Fill these by the corresponding simplex/product-simplex cells of D_{3,5}. Their composition is an explicit piecewise polynomial disk map. The threshold-and-renormalize D-to-S map then supplies continuous split stochastic Q,L. The threshold map may reparameterize the boundary moves; this is harmless if the boundary path is defined using that map, or attach the explicit homotopy annulus to match a chosen prior split path.
