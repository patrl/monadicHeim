{ mkDerivation, base, containers, mtl, stdenv }:
mkDerivation {
  pname = "update";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base containers mtl ];
  license = stdenv.lib.licenses.bsd3;
}
