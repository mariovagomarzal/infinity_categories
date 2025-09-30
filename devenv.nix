{pkgs, ...}: {
  env.GREET = "Lean 4 Development Environment";

  packages = with pkgs; [
    git
  ];

  languages.lean4.enable = true;

  git-hooks = {
    hooks = {
      gitlint = {
        enable = true;
        description = "Run gitlint to check commit messages";
      };

      markdownlint = {
        enable = true;
        description = "Run markdownlint to check Markdown files";
      };

      alejandra = {
        enable = true;
        description = "Run the Alejandra formatter on Nix files";
      };
    };
  };

  enterShell = ''
    echo $GREET
  '';
}
