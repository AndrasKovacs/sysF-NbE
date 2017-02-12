# sysF-NbE
Correctness of normalization by evaluation for intrinsic System F

Work in progress. Generally, we will be using presheaf models. The amount of coercion shoveling will be quite striking, but hopefully manageable. I will be probably playing around with cubical computation rules for coercion, or if the situtation gets really out of hand I may even dabble in reflection-based automation (but that's probably a lot of work and at that point we'd be likely better off with Coq).

We currently use --type-in-type everywhere, partly because of the necessarily impredicative Set0 needed for all our models, partly because Agda-2.5.2 rejects the universe polymorphic rewrite rule for cubical coercion at Pi type (a bug, I assume).

