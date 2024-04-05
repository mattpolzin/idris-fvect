{
  description = "Library around a Fin-based Vector type";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";

    idris = {
      url = "github:idris-lang/idris2";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    idrisLsp = {
      url = "github:idris-community/idris2-lsp";
      inputs.alejandra.follows = "alejandra";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.idris.follows = "idris";
    };

    alejandra = {
      url = "github:kamadorueda/alejandra";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    nixpkgs,
    idris,
    idrisLsp,
    alejandra,
  }: let
    inherit (nixpkgs) lib;
    eachSystem = f: lib.foldl lib.recursiveUpdate {} (map f (lib.attrNames idris.packages));
  in
    eachSystem (system: {
      fvect.${system} = lib.makeOverridable (import ./.) {
        buildIdris = idris.buildIdris.${system};
      };

      packages.${system} = {
        withSource = self.fvect.${system} {withSource = true;};
        default = self.fvect.${system} {};
      };

      devShells.${system}.default = nixpkgs.legacyPackages.${system}.mkShell {
        inputsFrom = [
          self.packages.${system}.default
        ];
        packages = [
          idrisLsp.packages.${system}.default
        ];
      };

      formatter.${system} = alejandra.packages.${system}.default;
    });
}
