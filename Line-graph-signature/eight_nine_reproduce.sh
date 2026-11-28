#!/usr/bin/env bash
# Reproduce the uniform bound, then cross-check the two sharp cases.
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work_dir=$(mktemp -d)
trap 'rm -rf -- "$work_dir"' EXIT
geng_bin=${GENG:-geng}
labelg_bin=${LABELG:-labelg}
compiler=${CXX:-c++}

"$compiler" -std=c++17 -O3 "$script_dir/eight_nine_verify.cpp" -lgmpxx -lgmp -o "$work_dir/checker"
python3 -B "$script_dir/eight_nine_paths.py"
for order in 6 7 8 9 10 11 12; do
    "$geng_bin" -q -c -d1 -D3 "$order"
done > "$work_dir/compressed.g6"

for order in 14 16 18 20 22 24 26; do
    "$work_dir/checker" "$order" --compressed < "$work_dir/compressed.g6"
done

for order in 14 16; do
    "$geng_bin" -q -c -d1 -D3 "$order" > "$work_dir/direct.g6"
    "$work_dir/checker" "$order" --all-inertias < "$work_dir/direct.g6"
    "$work_dir/checker" "$order" --emit-kernels < "$work_dir/direct.g6" |
        "$labelg_bin" -q -g | LC_ALL=C sort -u > "$work_dir/direct-canonical.g6"
    "$work_dir/checker" "$order" --compressed --emit-kernels < "$work_dir/compressed.g6" |
        "$labelg_bin" -q -g | LC_ALL=C sort -u > "$work_dir/compressed-canonical.g6"
    cmp "$work_dir/direct-canonical.g6" "$work_dir/compressed-canonical.g6"
    echo "Identical canonical exceptional kernel sets at cubic order $order: $(wc -l < "$work_dir/direct-canonical.g6")"
done
