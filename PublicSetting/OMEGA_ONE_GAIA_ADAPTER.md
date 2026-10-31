# Concrete Rocq \(\omega_1\): Gaia adapter

This adapter uses the concrete set-theoretic ordinal construction in
[rocq-community/gaia](https://github.com/rocq-community/gaia), package
`coq-gaia-ordinals.2.4`.

The key declarations in Gaia are:

- `Ordinals1.aleph_one := cnext omega0`;
- `Ordinals1.countable_ordinal a := ordinalp a /\\ countable_set a`;
- `Ordinals1.aleph_oneP`, proving that membership in `aleph_one` is
  equivalent to being a countable ordinal.

The adapter at `Rocq/ConcreteOmegaOne.v` re-exports this characterization
under the project name `PublicSettingConcreteOmegaOne.omegaOne`. It also
states two further properties for verification:

- `omegaOne_countable_sup`: the supremum of a countable family of countable
  ordinals remains a countable ordinal;
- `omegaOne_not_countable`: the carrier `omegaOne` itself is not countable,
  using Gaia's `Cantor_Omega` cardinality theorem.

This is materially stronger than the project's previous generic
`CountableIdeal`/ordered-type interface: it supplies an actual set in
Gaia's set-theoretic universe instead of a parameter `Ord : Type` plus
Schutte axioms.

## Foundational assumptions

This is not a proof in bare, axiom-free Calculus of Inductive Constructions.
Gaia formalizes Bourbaki-style set theory and its foundation includes
classical/existential-choice and set-extensionality principles (for example
the declarations in `theories/sets/sset1.v`).  Those assumptions must remain
visible in the project's foundational audit.  They are different from simply
postulating the existence of an abstract `Ord` satisfying the three Schutte
axioms, but they are still assumptions of the chosen set-theoretic model.

The Rocq CI installs the pinned Gaia 2.4 package and compiles the adapter. A
successful build demonstrates kernel acceptance of the adapter against the
selected package version; it does not erase Gaia's stated foundational
assumptions or establish that the rest of the project's measure-theoretic
development has been transferred to this concrete carrier.
