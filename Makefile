all: nix; cabal build
nix: default.nix esym.nix; nix-shell --command "cabal configure"
repl: default.nix; cabal repl
default.nix: esym.cabal; cabal2nix . > default.nix
