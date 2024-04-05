{buildIdris}: let
  pkg = buildIdris {
    ipkgName = "fvect";
    version = "0.1.0";
    src = ./.;
    idrisLibraries = [];
  };
in
  pkg.library
