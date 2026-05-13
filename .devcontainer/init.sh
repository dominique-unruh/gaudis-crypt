# For things that needs the mounts in place (i.e., that can't be in the Dockerfile)
echo "Running init script"
claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4
if ! claude mcp get lean-lsp >/dev/null 2>&1; then
  claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp
fi
