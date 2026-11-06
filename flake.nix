{
  description = "Marxian economics formalised in Lean 4 (labour values, prices, class distribution)";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          name = "lean-marx";
          packages = with pkgs; [ lean4 git cacert curl ];
          shellHook = ''
            echo "lean-marx — Lean $(lean --version | cut -d' ' -f4) from nixpkgs"
            echo "  lake build        build the library and examples"
            echo "  (the first build fetches Mathlib at the revision pinned in lakefile.toml)"
          '';
        };
      });
    };
}
