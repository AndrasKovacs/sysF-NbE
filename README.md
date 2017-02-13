# sysF-NbE
Correctness of normalization by evaluation for intrinsic System F

Work in progress. We have currently a normalization function via a mixed presheaf/Kripke model which is ~90% done. We have the substitution calculus laws for types but not yet for terms. We also have the standard impredicative set model, just for fun.

Later we will add correctness proofs for normalization, which along with the substitution calculus for terms would be the bulk of the project.

The amount of coercion shoveling will be quite striking, but so far I'm doing quite well with heterogeneous equality. I have experimented with cubical equality (see other branch), but ultimately decided on plain het. equalities, because it seems more prudent to work in conventional metatheory as I intend to write a paper about this when it's finished.

We currently use --type-in-type in the models for the necessarily impredicative Set0. It's not a big deal, I think (easily hand-checked), but later we might switch to some more localized impredicativity emulation if there's a nice one.

We also use Axiom K for the het. equalities. I have ideas about how to get rid of K but keep heq, but it's a nontrivial amount of work and I won't do it in the first version.

