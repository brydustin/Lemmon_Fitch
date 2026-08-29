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

SOURCES=(
  LF_Formula.thy
  LF_Lemmon.thy
  LF_Fitch.thy
  LF_Fitch_Structure.thy
  LF_Semantics.thy
  LF_DNF.thy
  LF_Direct.thy
  LF_Unfold.thy
  LF_Examples.thy
  LF_Span.thy
  LF_Positional.thy
  LF_Conjecture27.thy
  LF_Theorem10.thy
  LF_Conjecture26.thy
  LF_All.thy
)

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

echo "Generated Haskell and SML from LF_All.thy in $PROJECT_DIR/generated"
