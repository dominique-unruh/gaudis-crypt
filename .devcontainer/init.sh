# For things that needs the mounts in place (i.e., that can't be in the Dockerfile)
echo "Running init script"

claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4
if ! claude mcp get lean-lsp >/dev/null 2>&1; then
  claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp
fi

# OpenCode setup
echo "Setting up lean4 skill for OpenCode..."
LEAN4_PLUGIN_ROOT="$HOME/.claude/plugins/lean4-skills/plugins/lean4"
if [ -d "$LEAN4_PLUGIN_ROOT" ]; then
  mkdir -p .opencode/skills
  cp -r "$LEAN4_PLUGIN_ROOT/skills/lean4" .opencode/skills/
fi
mkdir -p .opencode
if [ ! -f .opencode/opencode.json ]; then
  echo '{"$schema": "https://opencode.ai/config.json"}' > .opencode/opencode.json
fi
jq '.mcp["lean-lsp"] //= {"type":"local","command":["uvx","lean-lsp-mcp"],"enabled":true}' .opencode/opencode.json > .opencode/opencode.tmp && mv .opencode/opencode.tmp .opencode/opencode.json
