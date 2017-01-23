# Unifying Theories of Programming Theorem Prover 

## U(TP)2

This is an application written using literate Haskell.
This means that the Haskell source files have extension `.lhs`
and are LaTeX sources with Haskell embedded in 
`\begin{code}..\end{code}` environments.

The main file for the application program is `src/UTP2.lhs`

The main file for the enclosing LaTeX documentation is `UTP2-MAIN.tex`

A Hackers Guide is being prepared in `UTP2-Hacking-MAIN.tex`

## Building

### macOS

The following instructions have shown to build UTP2 on macOS 10.11.6 on a
relatively fresh install.

UTP2 requires the command-line tool `wx-config` which can be installed as part
of wx. With Homebrew this is as easy as: `brew install wxmac`

XCode developer tools are also required, however they can't just be installed
via `xcode-select --install` since they are searched for in very specific
locations, maybe you can symlink them? Instead install XCode from the App
Store. You might have to agree to XCode's terms and conditions which you can
find by opening XCode.

The project should now build with stack.
