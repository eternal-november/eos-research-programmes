# Byzantine control

This project studies distributed control when observation, decision, actuation and recovery can fail independently. The [motivating problem](MOTIVATING-PROBLEM.md) defines the research question.

- [Reusable control results](portability/COMPLETION-AUDIT.md) cover two positive architectures and an independently selected extension.
- [Exclusive service](exclusive-service/RULE.md) derives a deadline for one actual effect across alternative opportunities and applies it to a physical carrier and two quorum-gated stores.
- [Source models and proofs](local-control/SYNTHESIS.md) give the detailed control installation and its operating assumptions.
- [Reproducing the checks](REPRODUCING.md) covers the current examples and the historical verification suite.
