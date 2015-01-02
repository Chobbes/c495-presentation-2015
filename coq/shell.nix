let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;
in rec {
  coqEnv = stdenv.mkDerivation rec {
    name = "coq-env";
    src = ./.;
    buildInputs = with pkgs; [ coq emacs prooftree emacs24Packages.proofgeneral ] ;
  };
}
