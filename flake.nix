{
  description = "A Nix flake for Coq with Coq ExtLib";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      pkgs = import nixpkgs {
        system = "x86_64-linux";  # Adjust for your system if necessary
      };
    in
    {
      devShells."x86_64-linux".default = pkgs.mkShell {
        buildInputs = [
          pkgs.coq
          pkgs.coqPackages.hierarchy-builder
          pkgs.coqPackages.mathcomp
        ];
      };
    };
}
