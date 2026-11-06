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
          # `elan` provides the `lean`/`lake` shims and resolves the toolchain
          # named by `lean-toolchain`.  Using the official release (rather than
          # nixpkgs' own Lean build) matters: oleans are tied to the compiler
          # build, so a differently linked Lean cannot load the Mathlib cache.
          packages = with pkgs; [ elan git cacert curl gmp zlib ];
          shellHook = ''
            echo "lean-marx — $(lean --version 2>/dev/null | head -1)"
            echo "  lake exe cache get   fetch prebuilt Mathlib oleans"
            echo "  lake build           build the library and examples"
          '';
        };
      });
    };
}
