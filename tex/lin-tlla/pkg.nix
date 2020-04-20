{ stdenv, texlive }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk beamer stmaryrd mathpartir rsfs
                      cmll xcolor paralist makecell tikz-cd ncctools thmtools
                      xifthen ifmtarg polytable etoolbox environ xkeyval
                      lazylist trimspaces;
  };
in stdenv.mkDerivation {
  name = "lin-ttla";
  src = ./.;
  buildInputs = [ tex-env ];
  buildPhase = ''
    latexmk quant-subst.tex
  '';
  installPhase = "";
}
