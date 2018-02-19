{ mkDerivation, aeson, base, base16-bytestring, bytestring, mtl
, stdenv, text
}:
mkDerivation {
  pname = "esym";
  version = "0.5";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson base base16-bytestring bytestring mtl text
  ];
  homepage = "https://github.com/dapphub/esym";
  description = "EVM symbolic executor";
  license = stdenv.lib.licenses.agpl3;
}
