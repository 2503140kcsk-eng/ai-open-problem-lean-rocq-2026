# Expected cumulative loss, global targets, and model boundaries

Status: 2026-11-01. This note separates three distinct claims:
(1) a one-round conditional-section bound;
(2) ordinary expected cumulative loss on a path probability space;
(3) the source paper's public minimax-regret game with one globally selected
terminal hypothesis family.

## 1. Source game and information order

Source: Shao, Fang, Lin, and Tao, Partial Feedback Online Learning,
arXiv:2601.21462v3:
- https://arxiv.org/html/2601.21462v3
- https://arxiv.org/abs/2601.21462

The public move order is:
1. the adversary selects the current context x_t;
2. the learner selects its distribution pi_t;
3. the adversary reveals a visible acceptable witness yvis_t;
4. Nature samples yhat_t from pi_t.

The current witness cannot depend on the current draw. The public adversary
can use previous completed rounds, including previous realized predictions.
The terminal acceptable sets are evaluated after play. In the set-realizable
regime, one fixed F* subset H induces all acceptable sets:
S_t = F*(x_t), and yvis_t belongs to S_t for every t.
The comparator loss is zero because every member of the nonempty F* is
accepted at every round.

The paper's Section 5.3 explicitly leaves open the general randomized-
versus-deterministic learnability separation in the public setting. Its
Theorem 19 is an oblivious-versus-public separation, which is a different
claim.

## 2. Exact ordinary expected-loss bridge

Let (Omega,F,P) be the complete path probability space. Let F_{t-1} be the
information immediately before the round-t draw, and let
L_t(omega) = 1{yhat_t(omega) is not in S_t(omega)}
be the actual pathwise loss after the terminal target has been selected.

The ordinary conditional stage risk is
r_t = E[L_t | F_{t-1}].
If every L_t is measurable and integrable, conditional expectation gives
E[L_t] = E[r_t]. For finite T, linearity gives

    E[sum_{t=1}^T L_t] = sum_t E[L_t] = sum_t E[r_t].

The Lean theorem ExpectedLossBridge.integral_finset_condExp_eq_integral_finset
formalizes this finite-sum identity, allowing a different conditioning
sigma-algebra at each round. It explicitly assumes:
- each F_{t-1} is a sub-sigma-algebra of F;
- the corresponding trimmed measure is sigma-finite, as required by
  Mathlib's conditional-expectation API;
- each completed-path loss is integrable.

For a probability measure, a measurable indicator loss is bounded by one and
is therefore integrable. Thus, for 0-1 losses, joint measurability of the
full path loss is the substantive premise.

The Rocq file ExpectedLossBridge.v independently checks the finite-sum
aggregation from linearity of expectation and the tower identity, both
stated as explicit hypotheses. It does not construct conditional expectation
from a measure in Rocq.

## 3. The shared-global-target warning

For one round, if G is the set of terminal families still compatible with
the relevant constraints and C_t is the intersection of their acceptable
label sets at x_t, then the pointwise identity

    sup_{F* in G} 1{y not in F*(x_t)} = 1{y not in C_t}

is correct. When C_t complement is measurable, its probability is a valid
one-round worst-case section risk.

But the source game's terminal F* is common to all rounds. In general,

    sup_{F* in G} sum_t L_t(F*)  is not equal to
    sum_t sup_{F* in G} L_t(F*).

The right side can select a different F* on each round. Therefore adding
one-round core risks is not, by itself, an exact representation of the
source game's terminal supremum.

The full path object that must be handled is

    L_T(omega) =
      sup_{F* in G(omega)} sum_t 1{yhat_t(omega) not in F*(x_t(omega))}.

To use the ordinary expected-loss bridge, this joint terminal supremum must
be measurable and integrable. An alternative backward-induction proof must
also preserve the same globally consistent F* across every remaining round.
This PR does not yet identify the general public minimax-regret operator
with the sum of its one-round core risks.

## 4. Why omega-one section nullity is not ordinary path-space measurability

The candidate uses Y=omega_1 with the countable-cocountable sigma-algebra
and the 0-1 probability:
mu(A)=0 for countable A, and mu(A)=1 for cocountable A.
For each fixed w<omega_1, the lower segment {y:y<w} is countable and null.
A miss against an upper tail whose threshold is no larger than the pre-draw
witness is contained in that lower segment.

However, the order relation E={(alpha,beta): beta<alpha} has countable
vertical sections and cocountable horizontal sections. If it were measurable
in the product sigma-algebra, Tonelli/Fubini would give both product measure
zero and one. In fact every product-measurable superset of E has product
measure one. Hence sectionwise nullity does not imply joint measurability
or product-nullity of the adaptive full-path error graph.

Consequently:
- the one-step conditional-section theorem is valid in its stated model;
- the ordinary trajectory/tower theorem cannot be applied to an arbitrary
  adaptive pathwise indicator without a separate joint-measurability proof;
- the current omega-one code does not establish equality between its
  stagewise semantics and conventional path-space expected regret.

This is a mathematical model boundary, not a compile failure.

## 5. Standard-Borel majority-core obstruction

Suppose Y and Theta are standard Borel, M subset Theta x Y is Borel, and
S_theta={y:(theta,y) in M}. Define
C_y = intersection of every S_theta containing y.
If sup_y mu(Y minus C_y) <= epsilon < 1/2, then there is a deterministic
x0 contained in every nonempty S_theta.

Proof:
1. The complement of R(x,y) iff x in C_y is the projection of the Borel
   set D={(x,y,theta): y in S_theta and x notin S_theta}.
2. Hence R complement is analytic and R is coanalytic. These sets are
   universally measurable, so R is measurable in the completion of
   mu x mu and Fubini applies.
3. R is transitive. Every incoming section has measure at least
   1-epsilon > 1/2.
4. Fubini yields an outgoing section of measure greater than one half.
   It intersects every incoming section in positive measure. Transitivity
   gives R(x0,y) for every y.

Lean's StandardBorelCore.lean formalizes the measure-theoretic core when
product measurability is supplied explicitly. The standard-Borel-to-completed-
product-measurability bridge in steps 1-2 remains a written descriptive-set-
theory argument. Rocq's StandardBorelCore.v checks the transitivity/majority
argument with the Fubini and intersection principles explicit as hypotheses.

This rules out a direct Borel standard-space transplant satisfying the
uniform core-risk premise below one half. It does not prove that every
standard-Borel randomized-versus-deterministic separation is impossible.
The threshold is sharp: on Y={0,1} with uniform measure and admissible
singletons {0},{1}, each core has measure exactly one half and no point is
contained in both nonempty sets.

## 6. Random-generation boundary

A sampler with a finite or countably enumerable seed space has countable
output range R subset omega_1. The target law assigns mu(R)=0, whereas the
push-forward of any source probability assigns mass one to R. Thus exact
sampling is impossible and total-variation distance is one.

This does not exclude every uncountable ideal source. For a Lebesgue-uniform
source on [0,1], exact measurable push-forward to the countable-cocountable
omega-one law exists iff cov(N) <= aleph_1. CH is sufficient; Shelah's
consistency result for countable cofinality of the null-ideal covering
number gives models where the inequality fails. This criterion is documented
in RNG_COMPATIBILITY.md but is not itself machine checked in this project.

## 7. Tool roles

TOOL_ROLES.md assigns distinct responsibilities:
- Lean + Mathlib: measure, kernels, conditional expectation and topology;
- Rocq + Gaia: independent abstract ideal/ordinal checks with foundations
  exposed;
- Naproche: structured prose-proof auditing;
- LeanDojo-v2: theorem retrieval/proof-search suggestions (optional GPU/API
  routes excluded from the free CI path);
- cvc5: finite SMT counterexamples and arithmetic side conditions;
- SageMath, SymPy and Wolfram: exact finite examples and symbolic checks;
- GAP: finite symmetry/orbit work if a finite reduction appears;
- Macaulay2: polynomial-ideal work only if an algebraic finite model arises;
- Context7, Parallel Search and Sider Scholar: API/literature retrieval;
- GitHub Actions: pinned Lean/Rocq builds.

These tools are not all build dependencies. Adding unrelated CAS packages
would enlarge the trusted build surface without strengthening the theorem.

## 8. Remaining theorem

This PR does not prove the unrestricted randomized-o(T) /
deterministic-Omega(T) public-setting separation. The checked scope is:
- omega-one one-step conditional-section bounds in Lean and their abstract
  countable-ideal/order counterpart in Rocq;
- ordinary expected-loss/conditional-risk finite-sum aggregation in Lean
  under explicit measure-theoretic hypotheses;
- its algebraic finite-sum companion in Rocq under explicit tower/linearity
  assumptions;
- standard-Borel majority-core measure argument in Lean with product
  measurability assumed and in Rocq with Fubini/intersection interfaces;
- the descriptive-set-theory bridge and exact omega-one RNG criterion remain
  documented rather than fully machine checked;
- identification of the full public terminal-global-target regret with the
  omega-one stagewise semantics remains unresolved.
