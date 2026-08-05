{
  description = "Intrinsic Verification of Parsers and Formal Grammar Theory in Dependent Lambek Calculus (Agda implementation)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical-categorical-logic = {
      url = "github:um-catlab/cubical-categorical-logic";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };

    # Track cubical-categorical-logic's toolchain rather than pinning our own:
    # whatever cubical c-c-l was built against is what we typecheck against,
    # by construction. Bumping the c-c-l input is the only way to move cubical.
    cubical.follows = "cubical-categorical-logic/cubical";
    agda.follows = "cubical-categorical-logic/agda";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    cubical,
    cubical-categorical-logic,
    ...
  }:
    let
      overlay = final: prev: {
        grammars-and-semantic-actions = final.agdaPackages.mkDerivation {
          pname = "grammars-and-semantic-actions";
          version = "0.1";

          src = final.lib.cleanSourceWith {
            filter = name: _type:
              !(final.lib.hasSuffix ".nix" name)
              && !(final.lib.hasSuffix "flake.lock" name)
              && !(final.lib.hasSuffix ".envrc" name);
            src = final.lib.cleanSource ./src;
          };

          LC_ALL = "C.UTF-8";

          nativeBuildInputs = [ final.agdaWithCubicalCategoricalLogic ];

          buildPhase = ''
            runHook preBuild
            make check
            runHook postBuild
          '';

          meta = {
            description = "Cubical Agda formalisation of Dependent Lambek Calculus";
          };
        };
      };
    in
    { overlays.default = overlay; } //
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            cubical.inputs.agda.overlays.default
            cubical.overlays.default
            cubical-categorical-logic.overlays.default
            overlay
          ];
        };
      in
      {
        packages = {
          inherit (pkgs) grammars-and-semantic-actions;
          default = pkgs.grammars-and-semantic-actions;
        };

        # Development shell: Agda with cubical + cubical-categorical-logic
        # plus fix-whitespace. Activate via `nix develop` or direnv.
        #
        # To use a local checkout of one of the dependencies, run e.g.:
        #   nix develop --override-input cubical path:../Cubical
        #   nix develop --override-input cubical-categorical-logic \
        #                path:../cubical-categorical-logic
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.agdaWithCubicalCategoricalLogic
            pkgs.haskellPackages.fix-whitespace
          ];

          shellHook = ''
            echo "grammars-and-semantic-actions dev shell"
            echo "  agda: $(agda --version 2>/dev/null | head -n1)"
          '';
        };
      }
    );
}
