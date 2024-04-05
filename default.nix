{buildIdris}: let
  pkg = buildIdris {
    ipkgName = "fvect";
    version = "0.2.0";
    src = ./.;
    idrisLibraries = [];
  };
in
  pkg.library
