# system-f-agda

A formalization of the polymorphic lambda calculus extended with
iso-recursive types

The code in this repository contains an Agda formalization of the
Girard-Reynolds polymorphic lambda calculus (System F) extended with
iso-recursive types.


Verifying the formalization
---------------------------

The formalization is written in (Agda)[https://github.com/agda/agda]
and makes heavy use of the (Agda standard
library)[https://agda.github.io/agda-stdlib].  The code in this
repository has been verified using Agda 2.4.2.2.  The latest versions
of the Agda distribution and standard library, along with setup
instructions, can be found at

 * https://github.com/agda/agda
 * https://agda.github.io/agda-stdlib

The easiest way to verify all the code is to compile the `README.agda`
file from the `src/` directory,

    agda src/README.agda -i src -i <path-to-Agda-standard-library>

or to simply load the `README.agda` file in the (Agda Emacs
mode)[https://github.com/agda/agda#configuring-the-emacs-mode]
(`agda2-mode`) by opening the file and typing `C-c C-l`.

Using the `agda2-mode` one can also run Agda functions interactively
in GNU/Emacs by typing `C-x C-n <expression>`.  E.g. typing

    C-x C-n typeOf [] (Λ (λ' (var zero) (var zero)))

in the module `SystemF.TypeCheck` runs the type-checking decision
procedures to determine the type of the polymorphic identity function.
It should return

    yes (∀' (var zero →' var zero) , Λ (λ' (var zero) (var zero)))


Source code
-----------

The Agda sources of the formalization are freely available on GitHub:

 * https://github.com/sstucki/system-f-agda


License and copyright
---------------------

See the `LICENSE` file.


------------------------------------------------------------------------
Author: Sandro Stucki
Copyright (c) 2015 EPFL
