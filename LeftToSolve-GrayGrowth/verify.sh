#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "Usage: bash verify.sh OPEN_MATH_AGENTS_CHECKOUT FORMAL_CONJECTURES_CHECKOUT" >&2
  exit 2
fi

package_dir="$(cd "$(dirname "$0")" && pwd)"
oma_checkout="$(cd "$1" && pwd)"
fc_checkout="$(cd "$2" && pwd)"
expected_oma=e3a3ffa65b55f913a963a6625588bdceedc6d6d9
expected_fc=9097e2f90e66d2f6244209cb1c07f7120d17ec53

[ "$(git -C "$oma_checkout" rev-parse HEAD)" = "$expected_oma" ] || {
  echo "Use the open-math-agents revision recorded in README.md." >&2; exit 2;
}
[ "$(git -C "$fc_checkout" rev-parse HEAD)" = "$expected_fc" ] || {
  echo "Use the formal-conjectures revision recorded in README.md." >&2; exit 2;
}

for kind in statements proofs; do
  for id in oeis-a265385 oeis-a265386; do
    src="$package_dir/$kind/$id.lean"
    dest="$oma_checkout/$kind/$id.lean"
    if [ -e "$dest" ] && ! cmp -s "$src" "$dest"; then
      echo "Refusing to replace different existing source: $dest" >&2
      exit 2
    fi
  done
done

for kind in statements proofs; do
  mkdir -p "$oma_checkout/$kind"
  for id in oeis-a265385 oeis-a265386; do
    cp "$package_dir/$kind/$id.lean" "$oma_checkout/$kind/$id.lean"
  done
done

mkdir -p "$package_dir/local-verification"
cd "$oma_checkout"
for id in oeis-a265385 oeis-a265386; do
  for kind in statements proofs; do
    OMA_FC="$fc_checkout" bash tools/check.sh "$kind/$id.lean" \
      "$package_dir/local-verification/$id-$kind.json"
  done
done

python3 - "$package_dir/local-verification" <<'PY'
import json
import pathlib
import sys
for path in sorted(pathlib.Path(sys.argv[1]).glob('*.json')):
    result = json.loads(path.read_text())
    print(path.name, result['verdict'], result['reason'])
    if result['verdict'] != 'accepted':
        raise SystemExit(1)
PY
