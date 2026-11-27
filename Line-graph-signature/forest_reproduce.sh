#!/usr/bin/env bash
# Build the catalog twice and run the exact signed-form tests on each distinct type.
set -euo pipefail
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
compiler=${CXX:-c++}
geng_bin=${GENG:-geng}
label_bin=${LABELG:-labelg}
level=${FOREST_LEVEL:-4}
case "$level" in 3|4) ;; *) echo 'FOREST_LEVEL must be 3 or 4.' >&2; exit 1 ;; esac
"$compiler" -O3 -std=c++17 "$source_dir/forest_verify.cpp" -lgmpxx -lgmp -o "$work/check"
"$compiler" -O3 -std=c++17 "$source_dir/forest_matching_audit.cpp" -lgmpxx -lgmp -o "$work/audit"
"$work/audit"
python3 -B "$source_dir/forest_witnesses.py"
for ((n=6; n<=4*level; ++n)); do
    "$geng_bin" -q -c -d1 -D3 "$n" > "$work/simple$n"
done
for ((n=6; n<=12; ++n)); do cat "$work/simple$n"; done | python3 -B "$source_dir/forest_coloring.py"
for ((d=3; d<=level; ++d)); do
    if ((d==3)); then
        orders=(18 20 22)
        amounts=(1040 324 52)
        stride=${FOREST_AUDIT_STRIDE:-211}
    else
        orders=(22 24 26 28 30)
        amounts=(27117 10308 2401 284 0)
        stride=${FOREST_AUDIT_STRIDE:-10000}
    fi
    for ((n=4; n<=orders[-1]; n+=2)); do
        {
            if ((n==4)); then
                "$geng_bin" -q -c -d1 -D3 4 | "$work/check" 4 --budget="$d" --direct --emit
            else
                "$work/check" "$n" --budget="$d" --augment < "$work/direct$((n-2))"
                if ((n<=4*d || n==6)); then
                    "$geng_bin" -q -c -d3 -D3 "$n" | "$work/check" "$n" --budget="$d" --direct --emit
                fi
            fi
        } | "$label_bin" -q -g | LC_ALL=C sort -u > "$work/direct$n"
    done
    for i in "${!orders[@]}"; do
        n=${orders[$i]}
        for ((k=n/2-1; k<=4*d; ++k)); do cat "$work/simple$k"; done |
            "$work/check" "$n" --budget="$d" --emit |
            "$label_bin" -q -g | LC_ALL=C sort -u > "$work/compressed$n"
        cmp "$work/direct$n" "$work/compressed$n"
        count=$(wc -l < "$work/direct$n")
        test "$count" -eq "${amounts[$i]}"
        echo "Canonical cubic types at order $n with matching size at most $d: $count"
        if ((d==4 && n==22)); then
            "$work/check" "$n" --budget="$d" --direct --reconstruct --audit="$stride" < "$work/direct$n"
        else
            "$work/check" "$n" --budget="$d" --direct --audit="$stride" < "$work/direct$n"
        fi
        if [[ ${FOREST_RECONSTRUCT:-0} == 1 ]] && ((d==4 && n==24)); then
            echo "Inverse reconstruction at order $n"
            "$work/check" "$n" --budget="$d" --direct --reconstruct --audit="$stride" < "$work/direct$n"
        fi
    done
done
