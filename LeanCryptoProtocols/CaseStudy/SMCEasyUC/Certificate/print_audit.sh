#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"

usage() {
  cat <<'USAGE'
Usage:
  ./print_audit.sh [all|static]

Commands:
  all     Print the static audit report. This is default.
  static  Print only the static audit report.
USAGE
}

run_eval() {
  local expr="$1"
  local tmp_dir
  local tmp
  tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/smc_audit.XXXXXX")"
  tmp="$tmp_dir/audit.lean"
  trap 'rm -rf "$tmp_dir"' RETURN
  cat > "$tmp" <<LEAN
import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Audit

#eval IO.println $expr
LEAN
  (cd "$PROJECT_ROOT" && lake env lean "$tmp")
}

cmd="${1:-all}"

case "$cmd" in
  all)
    run_eval "LeanCryptoProtocols.CaseStudy.SMCEasyUC.static_report"
    ;;
  static)
    run_eval "LeanCryptoProtocols.CaseStudy.SMCEasyUC.static_report"
    ;;
  -h|--help|help)
    usage
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac
