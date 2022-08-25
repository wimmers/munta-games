# Munta Games

This repository contains an extension of [Munta](https://github.com/wimmers/munta) towards timed games.
The current scope is a definition of the basic formalism, and a prototype safety checker for
controllers of safety games.

## Installation

Follow these steps:

1. Install [Isabelle-2021-1](https://isabelle.in.tum.de/)
2. Install the corresponding version of the [AFP](https://www.isa-afp.org/download/)
3. Register the AFP as an Isabelle component, see [AFP installation instructions](https://www.isa-afp.org/help/)
4. Obtain a copy of [Munta](https://github.com/wimmers/munta/tree/timed-games)
5. Register Munta as an Isabelle component, see [AFP installation instructions](https://www.isa-afp.org/help/)
6. Obtain a copy of this repository

## Building

Full Isabelle build:

```
cd munta-games
isabelle build -D .
```

## Development

For development, load Isabelle/jEdit with a suitable base session, e.g.:

```
isabelle jedit -d . -l Generalized_Networks Normalized_Zone_Semantics_Certification_Impl2.thy &
```

Note that this command can take very long when run the first time, since the base sesion needs to be built first.