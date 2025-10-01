# A Formalization of ∞-Categories in Lean 4

A formal verification project based on the work by Enric Cosme Llópez on
_Higher-order categories_.

## Overview

In many works on Category Theory, in addition to the usual many-sorted notions
of n-categories and of ∞-categories, the single-sorted versions of them are
also commonly used.

The aim of this project is to provide a formalization of the latter notions and
the proof of their equivalence in Lean 4.

> [!NOTE]
> For the moment, this is an active research project for a Mathematics degree
> final project. The project is in early stages and the following documentation
> is intended for self-reference only.

## Development

In this section, we document how to work with the repository. The development
environment is mainly managed with [Nix][nix] and _[devenv][devenv]_. However,
it is also documented how to work without the latter.

### Nix setup

To set up the development environment with Nix, you need to have Nix and
_devenv_ installed. Once you have them, you can enter the development shell
by running the following command in the root of the repository:

```bash
devenv shell
```

> [!TIP]
> If using [direnv][direnv], you can automatically load the development
> environment whenever you enter the repository directory by running
> `direnv allow` once in the root of the repository.

Once inside the development shell, all the necessary tools and dependencies
will be available. Run the following command to see available packages, scripts,
tasks and processes:

```bash
devenv info
```

Check out the `devenv.nix` file for more details on the development environment.

### Manual setup

Work in progress.

## Conventions

In this section, we document the workflow and conventions used in this
repository.

### Commit messages

This project follows the [Conventional Commits][conventional-commits]
specification for commit messages. The commit message format is as follows:

```text
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Where `<type>` is one of the following: `feat`, `fix`, `docs`, `style`,
`refactor`, `test`, `chore`, `build`, `ci`, `perf`, `revert`.

> [!TIP]
> If working with the development environment defined with _devenv_, a git hook
> is automatically installed to check the commit messages before committing.

### Branching

There are no strict rules for branching in this repository.

## Authors

- _(Author)_ [Mario Vago Marzal][mario]
- _(Supervisor)_ [Enric Cosme Llópez][enric]

## License

Copyright (c) 2025 Mario Vago Marzal. All rights reserved.

This project is licensed under the Apache License 2.0. See the
[LICENSE](LICENSE) file for details.

<!-- External links -->
[nix]: https://nixos.org/
[devenv]: https://devenv.sh/
[direnv]: https://direnv.net/
[conventional-commits]: https://www.conventionalcommits.org/en/v1.0.0/
[mario]: https://github.com/mariovagomarzal
[enric]: https://github.com/encosllo
