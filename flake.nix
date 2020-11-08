{
  description = "Nim Dhall evaluator";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {

      devShell = forAllSystems (system:
        with nixpkgs.legacyPackages.${system};
        mkShell { buildInputs = [ nim openssl ]; });

    };
}
