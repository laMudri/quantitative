{ stdenv, texlive }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk beamer stmaryrd mathpartir rsfs
                      cmll xcolor paralist makecell tikz-cd ncctools;
  };
in stdenv.mkDerivation {
  name = "quantitative-types-presentation";
  src = ./.;
  buildInputs = [ tex-env ];
  buildPhase = ''
    latexmk quantitative.tex
  '';
  installPhase = "";
}
