#!/usr/bin/env bash
set -euo pipefail
mkdir -p out/finite/C20MatchingFinite
cp C20.lean C20Gaps.lean C20Boundary.lean BoundarySearch.lean \
  C20BoundaryMatching.lean C20MatchingSmall.lean C20MatchingFinite.lean lean-toolchain out/finite/
cp C20MatchingFinite/Head*.lean out/finite/C20MatchingFinite/
cat > out/finite/lakefile.toml <<'LAKE'
name = "C20FiniteStandalone"
precompileModules = true
defaultTargets = ["C20BoundaryMatching"]
[[lean_lib]]
name = "C20"
[[lean_lib]]
name = "C20Gaps"
[[lean_lib]]
name = "C20Boundary"
[[lean_lib]]
name = "BoundarySearch"
[[lean_lib]]
name = "C20BoundaryMatching"
[[lean_lib]]
name = "C20MatchingSmall"
[[lean_lib]]
name = "C20MatchingFinite"
LAKE
