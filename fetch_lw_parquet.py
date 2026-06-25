#!/usr/bin/env python3
"""
Grab the ENTIRE internlm/Lean-Workbook as one parquet (no per-window rate limit) and emit the
{"rows":[{"row":{...}}]} envelope the scan reads. Run with Python (has pyarrow).
"""
import json
import os
import urllib.request

import pyarrow.parquet as pq

HERE = os.path.dirname(os.path.abspath(__file__))
PARQUET_URL = ("https://huggingface.co/datasets/internlm/Lean-Workbook/resolve/"
               "refs%2Fconvert%2Fparquet/default/train/0000.parquet")
PQ = os.path.join(HERE, "examples", "_lw_full.parquet")
OUT = os.path.join(HERE, "examples", "_lw_full.json")
KEEP = ("id", "formal_statement", "natural_language_statement", "status")

req = urllib.request.Request(PARQUET_URL, headers={"User-Agent": "trust-lane/1.0"})
with urllib.request.urlopen(req, timeout=120) as r, open(PQ, "wb") as f:
    f.write(r.read())

t = pq.read_table(PQ, columns=list(KEEP))
cols = {k: t.column(k).to_pylist() for k in KEEP}
n = t.num_rows
rows = [{"row": {k: cols[k][i] for k in KEEP}} for i in range(n)]
json.dump({"rows": rows, "num_rows_total": n}, open(OUT, "w"))
print(f"wrote {n} rows -> {OUT}")
