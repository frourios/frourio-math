#!/usr/bin/env bash
# Lean API signature extractor (deduped; robust + portable)
# - lake build 失敗→ログを表示して終了（api.mdは変更しない）
# - 警告 "declaration uses ... sorry|admit" を抽出（ANSI除去・Windowsパス正規化・末尾一致）
# - 全 .lean を走査し、各宣言ブロック [start, nextStart) を := sorry / := proven（二択）
#   * := sorry … (file,line) がブロック内にある / もしくは本文に sorry|admit が実在
# - 署名はトップレベル ':=' 左側のみを出力、namespace の end のみ出力
# - マーカーは**行番号でユニーク化**して重複出力を防止
set -euo pipefail
export LC_ALL=C.UTF-8

OUTPUT_FILE="api.md"
: "${SORRY_DEBUG:=0}"

canonical_path() {
  local p="$1"
  p="$(printf '%s' "$p" | sed -E 's/\x1b\[[0-9;]*[mK]//g')"
  p="${p//\\//}"
  if [[ "$p" =~ ^([A-Za-z]):/(.*)$ ]]; then
    local d; d="$(printf '%s' "${BASH_REMATCH[1]}" | tr 'A-Z' 'a-z')"
    p="/$d/${BASH_REMATCH[2]}"
  fi
  p="$(printf '%s' "$p" | sed -E 's#/+#/#g')"
  while [[ "$p" == ./* ]]; do p="${p#./}"; done
  local pwd_can; pwd_can="$(pwd | sed -E 's#/+#/#g')"
  if [[ "$p" == "$pwd_can/"* ]]; then p="${p#$pwd_can/}"; fi
  printf '%s\n' "$p"
}

# 1) lake build
BUILD_LOG="$(mktemp)"
if ! lake build 2>&1 | tee "$BUILD_LOG" >/dev/null; then
  cat "$BUILD_LOG"
  rm -f "$BUILD_LOG"
  exit 1
fi

# 2) extract warnings
SAN_LOG="$(mktemp)"
sed -E 's/\x1b\[[0-9;]*[mK]//g' "$BUILD_LOG" | tr -d '\r' > "$SAN_LOG"
rm -f "$BUILD_LOG"

WARN_CAN="$(mktemp)"
RAW="$(mktemp)"
awk 'BEGIN{IGNORECASE=1}
     /warning:/ && /declaration[[:space:]]+uses/ && ( /sorry/ || /admit/ ) {
       if (match($0, /([^\t ]+\.lean):([0-9]+):([0-9]+):/, m)) {
         printf "%s\t%s\n", m[1], m[2];
       }
     }' "$SAN_LOG" | sort -u > "$RAW"

: > "$WARN_CAN"
while IFS=$'\t' read -r p l; do
  [[ -z "${p:-}" || -z "${l:-}" ]] && continue
  if [[ "$p" == *"/.lake/"* || "$p" == *"\\.lake\\"* ]]; then continue; fi
  printf '%s\t%s\n' "$(canonical_path "$p")" "$l" >> "$WARN_CAN"
done < "$RAW"
rm -f "$SAN_LOG" "$RAW"

(( SORRY_DEBUG )) && { echo "[DEBUG] warnings=$(wc -l < "$WARN_CAN" | tr -d ' ')"; sed -E 's/\t/:/' "$WARN_CAN" || true; }

# 3) start api.md
[[ -f "$OUTPUT_FILE" ]] && rm -f "$OUTPUT_FILE"
{
  echo "# Lean API"
  echo ""
  if [[ -f "./lean-toolchain" ]]; then
    echo "## ./lean-toolchain"
    cat "./lean-toolchain"
    echo ""
  fi
} > "$OUTPUT_FILE"

# helpers
count_brackets_awk='
function bal(c){if(c=="("||c=="{"||c=="["||c=="⟨"||c=="⦃"||c=="‹")return 1;
                 if(c==")"||c=="}"||c=="]"||c=="⟩"||c=="⦄"||c=="›")return -1; return 0}
BEGIN{d=0;str=0;esc=0;blk=0}
{
  s=$0
  for(i=1;i<=length(s);i++){
    c=substr(s,i,1); c2=(i<length(s)?substr(s,i,2):"")
    if(blk>0){ if(c2=="-/"){blk--; i++}; continue }
    if(!str && c2=="--"){break}
    if(!str && c2=="/-"){blk++; i++; continue}
    if(c=="\"" && !esc){str=!str; continue}
    if(str){ esc=(c=="\\" && !esc); if(c!="\\")esc=0; continue }
    d+=bal(c)
  }
}
END{print d}
'
find_toplevel_assign_awk='
function bal(c){if(c=="("||c=="{"||c=="["||c=="⟨"||c=="⦃"||c=="‹")return 1;
                 if(c==")"||c=="}"||c=="]"||c=="⟩"||c=="⦄"||c=="›")return -1; return 0}
BEGIN{d=initDepth;str=0;esc=0;blk=0}
{
  s=$0
  for(i=1;i<=length(s);i++){
    c=substr(s,i,1); c2=(i<length(s)?substr(s,i,2):"")
    if(blk>0){ if(c2=="-/"){blk--; i++}; continue }
    if(!str && c2=="--"){break}
    if(!str && c2=="/-"){blk++; i++; continue}
    if(c=="\"" && !esc){str=!str; continue}
    if(str){ esc=(c=="\\" && !esc); if(c!="\\")esc=0; continue }
    if(c==":" && i<length(s) && substr(s,i+1,1)=="=" && d==0){ print i; exit }
    d+=bal(c)
  }
}
END{print 0}
'
count_brackets() { awk "$count_brackets_awk"; }
find_toplevel_assign_col() { awk -v initDepth="$1" "$find_toplevel_assign_awk"; }

declare -a BLOCK_STACK=()
push_block(){ BLOCK_STACK+=("$1:$2"); }
top_entry(){ local n=${#BLOCK_STACK[@]}; (( n>0 )) && echo "${BLOCK_STACK[$((n-1))]}" || echo ""; }
pop_top(){ local n=${#BLOCK_STACK[@]}; (( n>0 )) && unset "BLOCK_STACK[$((n-1))]"; }
top_type(){ local e; e="$(top_entry)"; [[ -n "$e" ]] && echo "${e%%:*}" || echo ""; }
top_name(){ local e; e="$(top_entry)"; [[ -n "$e" ]] && echo "${e#*:}" || echo ""; }
print_end_if_ns(){ local t n; t="$(top_type)"; n="$(top_name)"; pop_top; [[ "$t" == "ns" ]] && { echo "end $n" >> "$OUTPUT_FILE"; echo "" >> "$OUTPUT_FILE"; }; }

_last_line()     { awk 'NR{last=$0} END{print last}'; }
_all_but_last()  { awk 'NR>1{print prev} {prev=$0}'; }

extract_with_attributes_upwards(){
  local f="$1" ln="$2" out="" cur k=$((ln-1))
  while (( k>0 )); do
    cur="$(sed -n "${k}p" "$f" || true)"
    if [[ "$cur" =~ ^[[:space:]]*@\[.*\][[:space:]]*$ ]] || [[ "$cur" =~ ^[[:space:]]*$ ]]; then
      out="${cur}"$'\n'"${out}"; k=$((k-1))
    else break; fi
  done
  cur="$(sed -n "${ln}p" "$f" || true)"
  printf '%s' "${out}${cur}"
}
extract_signature_block(){
  local f="$1" ln="$2" max_lines=200 read=0
  local buf; buf="$(extract_with_attributes_upwards "$f" "$ln")"
  while (( read < max_lines )); do
    local total last_line bal_before col
    total=$(printf "%s\n" "$buf" | count_brackets)
    last_line="$(printf "%s\n" "$buf" | _last_line)"
    bal_before=$(printf "%s\n" "$buf" | _all_but_last | count_brackets)
    col=$(printf "%s" "$last_line" | find_toplevel_assign_col "$bal_before")
    if [[ "$col" != "0" && "$total" == "0" ]]; then
      local trimmed head
      trimmed="$(printf "%s" "$last_line" | awk -v pos="$col" '{print substr($0,1,pos-1)}')"
      head="$(printf "%s\n" "$buf" | _all_but_last)"
      if [[ -n "$head" ]]; then printf "%s\n%s" "$head" "$trimmed"; else printf "%s" "$trimmed"; fi
      return 0
    fi
    read=$((read+1)); ln=$((ln+1))
    local nxt; nxt="$(sed -n "${ln}p" "$f" || true)"
    [[ -z "$nxt" ]] && { printf "%s" "$buf"; return 0; }
    buf="${buf}"$'\n'"${nxt}"
  done
  printf "%s" "$buf"
}

collect_warn_lines_for_file() {
  local warn_file="$1" canon_file="$2" out="$3"
  awk -F'\t' -v cf="$canon_file" '
    function lower(s){return tolower(s)}
    function endswith_ci(s, suf){
      s=lower(s); suf=lower(suf)
      n=length(s); m=length(suf)
      return (n>=m && substr(s, n-m+1)==suf)
    }
    BEGIN{ cf_l=lower(cf) }
    {
      p_l=lower($1)
      if (p_l==cf_l || endswith_ci(p_l, cf_l)) print $2
    }
  ' "$warn_file" | sort -n > "$out"
}

block_has_sorry() {
  local file="$1" start="$2" end="$3"
  local to=$((end-1))
  sed -n "${start},${to}p" "$file" | awk '
    BEGIN{str=0;esc=0;blk=0;has=0}
    {
      s=$0; t=""
      for(i=1;i<=length(s);i++){
        c=substr(s,i,1); c2=(i<length(s)?substr(s,i,2):"")
        if(blk>0){ if(c2=="-/"){blk--; i++}; continue }
        if(!str && c2=="--"){break}
        if(!str && c2=="/-"){blk++; i++; continue}
        if(c=="\"" && !esc){str=!str; continue}
        if(str){ esc=(c=="\\" && !esc); if(c!="\\")esc=0; continue }
        t=t c
      }
      if (t ~ /(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)/) has=1
    }
    END{ if(has) print "has"; else print "none" }
  ' | grep -qx 'has'
}

process_lean_file(){
  local file="$1"
  {
    echo ""
    echo "## $file"
    echo ""
  } >> "$OUTPUT_FILE"

  # マーカー候補を集めて「行番号でユニーク化」
  local MARKERS; MARKERS="$(mktemp)"
  {
    grep -n -E '^[[:space:]]*(section|namespace)[[:space:]]' "$file" 2>/dev/null || true
    grep -n -E '^[[:space:]]*(lemma|theorem|def|abbrev|example|structure|axiom|class|instance|inductive)[[:space:]]' "$file" 2>/dev/null || true
    grep -n -E '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|scoped|noncomputable|unsafe|partial|local)[[:space:]]+)*(lemma|theorem|def|abbrev|example|structure|axiom|class|instance|inductive)[[:space:]]' "$file" 2>/dev/null || true
    grep -n -E '^[[:space:]]*end([[:space:]]+[A-Za-z0-9_.]+)?[[:space:]]*$' "$file" 2>/dev/null || true
  } \
  | sort -t: -k1,1n \
  | awk -F: '!seen[$1]++' > "$MARKERS"   # ← ★ ここで重複除去（行番号キー）

  if [[ ! -s "$MARKERS" ]]; then
    { echo "No definitions found"; echo ""; } >> "$OUTPUT_FILE"
    rm -f "$MARKERS"
    return 0
  fi

  local CAN_FILE; CAN_FILE="$(canonical_path "$file")"
  local WARN_LINES_FILE; WARN_LINES_FILE="$(mktemp)"
  collect_warn_lines_for_file "$WARN_CAN" "$CAN_FILE" "$WARN_LINES_FILE"
  (( SORRY_DEBUG )) && echo "[DEBUG] file=$CAN_FILE warned_lines=$(wc -l < "$WARN_LINES_FILE" | tr -d ' ')"

  local LINES_ONLY; LINES_ONLY="$(mktemp)"
  cut -d: -f1 "$MARKERS" > "$LINES_ONLY"

  exec 7< "$MARKERS"
  local idx=0 total_markers
  total_markers=$(wc -l < "$LINES_ONLY" | tr -d ' ')
  BLOCK_STACK=()

  while IFS=: read -r lno _rest <&7; do
    local line; line="$(sed -n "${lno}p" "$file" || true)"
    local next_lno
    if (( idx+1 < total_markers )); then
      next_lno="$(sed -n "$((idx+2))p" "$LINES_ONLY" || true)"
    else
      next_lno=2000000000
    fi

    if [[ "$line" =~ ^[[:space:]]*section([[:space:]]+[A-Za-z0-9_.]+)?[[:space:]]*$ ]]; then
      BLOCK_STACK+=("sec:")
    elif [[ "$line" =~ ^[[:space:]]*namespace[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$ ]]; then
      local ns="${BASH_REMATCH[1]}"
      echo "namespace $ns" >> "$OUTPUT_FILE"; echo "" >> "$OUTPUT_FILE"
      BLOCK_STACK+=("ns:$ns")
    elif [[ "$line" =~ ^[[:space:]]*end([[:space:]]+([A-Za-z0-9_.]+))?[[:space:]]*$ ]]; then
      local name="${BASH_REMATCH[2]:-}"
      if [[ -n "$name" ]]; then
        while :; do
          local e t n; e="$(top_entry)"; [[ -z "$e" ]] && break
          t="${e%%:*}"; n="${e#*:}"
          if [[ "$n" == "$name" ]]; then print_end_if_ns; break; fi
          [[ "$t" == "sec" ]] && { pop_top; continue; }
          break
        done
      else
        [[ -n "$(top_entry)" ]] && print_end_if_ns
      fi
    elif [[ "$line" =~ ^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|scoped|noncomputable|unsafe|partial|local)[[:space:]]+)*(lemma|theorem|def|abbrev|example|structure|axiom|class|instance|inductive)[[:space:]] ]]; then
      local status=":= proven"
      if awk -v s="$lno" -v e="$next_lno" '($1>=s && $1<e){exit 0} END{exit 1}' "$WARN_LINES_FILE"; then
        status=":= sorry"
      else
        if block_has_sorry "$file" "$lno" "$next_lno"; then
          status=":= sorry"
        fi
      fi
      local sig; sig="$(extract_signature_block "$file" "$lno")"
      printf "%s %s\n\n" "$sig" "$status" >> "$OUTPUT_FILE"
    else
      local hdr; hdr="$(extract_signature_block "$file" "$lno")"
      printf "%s\n\n" "$hdr" >> "$OUTPUT_FILE"
    fi

    idx=$((idx+1))
  done
  exec 7<&-

  rm -f "$MARKERS" "$LINES_ONLY" "$WARN_LINES_FILE"
  return 0
}

# enumerate & process
echo "Scanning Lean files..."
LIST="$(mktemp)"
find . -type f -name "*.lean" \
  -not -path "./.lake/*" \
  -not -name "lakefile.lean" \
  -not -name "lean-toolchain" \
  | sort > "$LIST"

found=$(wc -l < "$LIST" | tr -d ' ')
echo "Found Lean files: $found"

exec 9< "$LIST"
processed=0
while IFS= read -r f <&9; do
  echo "Processing: $f"
  set +e
  process_lean_file "$f"
  rc=$?
  set -e
  if (( rc != 0 )); then
    echo "[WARN] process_lean_file failed for: $f (rc=$rc)" >&2
  fi
  processed=$((processed+1))
done
exec 9<&-

{
  echo ""
  echo "Total files processed: $processed"
} >> "$OUTPUT_FILE"

rm -f "$LIST" "$WARN_CAN"

echo ""
echo "API documentation generated successfully!"
echo "Output file: $OUTPUT_FILE"
echo "Total files processed: $processed"
