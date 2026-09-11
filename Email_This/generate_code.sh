#!/usr/bin/env bash
set -euo pipefail

# Source-process the complete cap from HOL and copy its Isabelle/HOL code
# exports into generated/.  No Lemmon_Fitch session image is selected.

PROJECT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ISABELLE_BIN="${ISABELLE_BIN:-/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle}"
CODEGEN_TMP="$(mktemp -d /tmp/lemmon_fitch_codegen.XXXXXX)"

cleanup_codegen_tmp() {
  rm -rf -- "$CODEGEN_TMP"
}
trap cleanup_codegen_tmp EXIT

# Discovered rather than listed: the hand-maintained list had gone stale
# (three files that no longer exist, sixteen maintained theories missing), which
# left this script unable to run at all.
SOURCES=()
while IFS= read -r source_file; do
  SOURCES+=("$(basename -- "$source_file")")
done < <(find "$PROJECT_DIR" -maxdepth 1 \( -name 'LF_*.thy' -o -name 'Lemmon_Fitch.thy' \) | sort)

if [ "${#SOURCES[@]}" -eq 0 ]; then
  echo "no theory sources found in $PROJECT_DIR" >&2
  exit 1
fi


SOURCE_ARGUMENTS=()
for source_file in "${SOURCES[@]}"; do
  SOURCE_ARGUMENTS+=("-f" "$PROJECT_DIR/$source_file")
done

(
  cd "$CODEGEN_TMP"
  "$ISABELLE_BIN" process_theories -v -l HOL \
    -E '[2] "*:code/**"' \
    "${SOURCE_ARGUMENTS[@]}" \
    HOL-Library.Code_Target_Nat
)

mkdir -p "$PROJECT_DIR/generated/haskell"
cp "$CODEGEN_TMP/export/haskell/LemmonFitch.hs" \
  "$PROJECT_DIR/generated/haskell/LemmonFitch.hs"
cp "$CODEGEN_TMP/export/haskell/Str_Literal.hs" \
  "$PROJECT_DIR/generated/haskell/Str_Literal.hs"
cp "$CODEGEN_TMP/export/sml.ML" "$PROJECT_DIR/generated/sml.ML"

echo "Generated Haskell and SML from Lemmon_Fitch.thy in $PROJECT_DIR/generated"
