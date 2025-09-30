# A Formalization of ∞-Categories in Lean 4

A formal verification project based on the work by Enric Cosme Llópez on
_Higher-order categories_.

## Overview

In many works on Category Theory, in addition to the usual many-sorted notions
of n-categories and of ∞-categories, the single-sorted versions of them are
also commonly used.

The aim of this project is to provide a formalization of the latter notions and
the proof of their equivalence in Lean 4.

> [!INFO]
> For the moment, this is an active research project for a Mathematics degree
> final project. The project is in early stages.

## Development

In this section, we document how to work with the repository. The development
environment is mainly managed with [Nix][nix] and *[devenv][devenv]*. However,
it is also documented how to work without the latter.

### Nix setup

To set up the development environment with Nix, you need to have Nix and
*devenv* installed. Once you have them, you can enter the development
environment by running the following command in the root of the repository:

```bash
devenv shell
```

> [!TIP]
> If using [direnv][direnv], you can automatically load the development
> environment whenever you enter the repository directory by running
> `direnv allow` once in the root of the repository.

Usage is work in progress.

### Manual setup

Work in progress.

## Conventions

Work in progress.

## Authors

- *(Author)* [Mario Vago Marzal][mario]
- *(Supervisor)* [Enric Cosme Llópez][enric]

## License

Copyright (c) 2025 Mario Vago Marzal. All rights reserved.

This project is licensed under the Apache License 2.0. See the
[LICENSE](LICENSE) file for details.

<!-- External links -->
[nix]: https://nixos.org/
[devenv]: https://devenv.sh/
[direnv]: https://direnv.net/
[mario]: https://github.com/mariovagomarzal
[enric]: https://github.com/encosllo
