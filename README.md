# sysF-NbE
Correctness of normalization by evaluation for intrinsic System F

Work in progress. Generally, we will be using presheaf models. The amount of coercion shoveling will be quite striking, but hopefully manageable. 

This branch uses an implementation of cubical equality using rewrite rules, in hope that the computation rules for coercion and function extensionality would be useful. It's a simplified version of Conor McBride's "cubical crossroads". 

We currently use --type-in-type everywhere, partly because of the necessarily impredicative Set0 needed for all our models, partly because Agda-2.5.2 rejects the universe polymorphic rewrite rule for cubical coercion at Pi type (a bug, I assume).

