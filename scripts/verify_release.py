"""Check this release without Lean: file hashes, replay verdicts, and fragment reassembly.

Usage: python scripts/verify_release.py
"""
import hashlib, json, subprocess, sys, tempfile, shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    # 1. every file listed in SHA256SUMS.txt matches
    n = 0
    for line in (ROOT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        digest, rel = line.split("  ", 1)
        assert sha(ROOT / rel) == digest, f"hash mismatch: {rel}"
        n += 1
    print(f"PASS hashes: {n} files")
    # 2. replay logs: PASS, no partial/unsafe, standard axioms only
    std = {"propext", "Classical.choice", "Quot.sound"}
    for name, count in [("Verified", 3325), ("CoherentEnergyMeasure", 168), ("CoherentEnergyRHBridge", 9)]:
        d = json.loads((ROOT / "verification" / f"strict436_{name}.log").read_text(encoding="utf-8"))
        assert d["verdict"] == "PASS" and d["auditedConstants"] == count
        assert d["partialConstants"] == 0 and d["unsafeConstants"] == 0
        assert all(set(x["axioms"]) <= std for x in d["declarations"])
        print(f"PASS replay log: {name} ({count} constants, standard axioms)")
    # 3. reassembling the fragments reproduces Verified.lean (line endings normalized)
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t) / "fragments"
        shutil.copytree(ROOT / "fragments", tmp)
        subprocess.run([sys.executable, "-I", str(tmp / "assemble.py")], check=True, cwd=tmp,
                       stdout=subprocess.DEVNULL)
        a = (tmp / "Verified.lean").read_bytes().replace(b"\r\n", b"\n")
        b = (ROOT / "Verified.lean").read_bytes().replace(b"\r\n", b"\n")
        assert a == b, "reassembled Verified.lean differs"
    print("PASS reassembly: fragments rebuild Verified.lean exactly")

if __name__ == "__main__":
    main()
