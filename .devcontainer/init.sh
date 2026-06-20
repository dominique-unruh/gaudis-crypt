# For things that needs the mounts in place (i.e., that can't be in the Dockerfile)
echo "Running init script"

set -ex

claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4
if ! claude mcp get lean-lsp >/dev/null 2>&1; then
  claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp
fi

# OpenCode setup
echo "Setting up lean4 skill for OpenCode..."
OPENCODE_CFG_DIR="$HOME/.config/opencode"
mkdir -p "$OPENCODE_CFG_DIR/skills"
cp -r ~/.claude/plugins/marketplaces/lean4-skills/plugins/lean4/skills/lean4 "$OPENCODE_CFG_DIR/skills/"

echo 'export LEAN4_SCRIPTS="$HOME/.claude/plugins/marketplaces/lean4-skills/plugins/lean4/scripts"' >> ~/.bashrc

# MCP config
if [ ! -f "$OPENCODE_CFG_DIR/opencode.json" ]; then
  echo '{"$schema": "https://opencode.ai/config.json"}' > "$OPENCODE_CFG_DIR/opencode.json"
fi
jq '.mcp["lean-lsp"] //= {"type":"local","command":["uvx","lean-lsp-mcp"],"enabled":true}' "$OPENCODE_CFG_DIR/opencode.json" > "$OPENCODE_CFG_DIR/opencode.tmp" && mv "$OPENCODE_CFG_DIR/opencode.tmp" "$OPENCODE_CFG_DIR/opencode.json"
