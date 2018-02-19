{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs;
  drv = pkgs.haskellPackages.callPackage (import ./default.nix) {};
in
  if pkgs.lib.inNixShell then drv.env else drv
