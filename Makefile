
.PHONY: update build clean

ELAN ?= elan
LAKE ?= lake
TOOLCHAIN := $(shell cat lean-toolchain)

# One-stop refresh after changing `lean-toolchain` or `lakefile.toml` deps.
# Installs the Lean toolchain, updates deps, fetches mathlib caches, then builds.
update:
	$(ELAN) self update
	($(ELAN) toolchain list | grep -Fx "$(TOOLCHAIN)") ||$(ELAN) toolchain install "$(TOOLCHAIN)"
	$(LAKE) update
	$(LAKE) exe cache get
	make build

build:
	$(LAKE) build

# Publishes updated docs to server. Very slow!
publish-docs : 
	scripts/build-gh-pages.py --verbose --push

clean:
	$(LAKE) clean