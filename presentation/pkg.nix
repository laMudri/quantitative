{ stdenv, texlive }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk beamer stmaryrd mathpartir
                      cmll xcolor paralist makecell;
  };
in stdenv.mkDerivation {
  name = "quantitative-presentation";
  src = ./.;
  buildInputs = [ tex-env ];
  buildPhase = ''
    latexmk
  '';
  installPhase = "";
}
