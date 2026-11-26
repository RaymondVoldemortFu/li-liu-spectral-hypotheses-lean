"""Check the R proof's named dependencies in a canonical joint lean4export file."""
from pathlib import Path
import runpy
import sys

# The interface checker already indexes export expressions and qualified names.
Export = runpy.run_path(str(Path(__file__).with_name("compare-interface.py")))["Export"]

G = "GoldbachSpectral435."
B = "GoldbachSpectral.BandSieve."
JOINT = {
    G+"Unconditional.not_R": [G+"refute_R", G+"Unconditional.local_GRH"],
    G+"Unconditional.local_GRH": [G+"all_local_of_primitive", "LFunction_eq_zero_re_of_isPrimitive"],
    G+"refute_R": [G+"cofinal_growth", G+"actual_R_failure_of_growth"],
    G+"actual_R_failure_of_growth": ["ConditionalGoldbach.theorem_6_1", "GoldbachSpectral.eventually_small_series", G+"eligibleNorm_spec"],
    G+"cofinal_growth": [G+"growth_from_shift_transfer", G+"shiftTransfer_original"],
    G+"growth_from_shift_transfer": [G+"large_shift"],
    G+"shiftTransfer_original": [G+"actual_transfer"],
    G+"actual_transfer": [G+"opposite_entry_bound"],
    G+"opposite_entry_bound": [G+"half_cross_vanish"],
    G+"large_shift": [B+"growing_rows", G+"mean_lower", G+"modulus_witness"],
    G+"mean_lower": [G+"shifted_estimate"],
    G+"shifted_estimate": [G+"physical_AP"],
    G+"physical_AP": [G+"smooth_character_bound"],
    B+"growing_rows": [B+"row_signal"],
    B+"row_signal": [B+"signed_matrix_lower"],
    B+"signed_matrix_lower": [B+"top_divisor_mass", B+"signed_column"],
    B+"top_divisor_mass": [B+"prime_mass_windows"],
    B+"prime_mass_windows": ["spectral_band_prime_number_theorem"],
    B+"extra_layer": [B+"inclusion_exclusion"],
}
SPECTRAL = {
    G+"norm_lower_on_original": [G+"cofinal_growth", G+"eligibleNorm_spec"],
    G+"common_zero_sequence": [G+"cofinal_original_zeros"],
    G+"cofinal_original_zeros": [G+"prescribed_failure", "ConditionalGoldbach.spectralQuaternion_eq_zero_iff",
                                 "ConditionalGoldbach.quaternion_quadratic_real_of_off_critical"],
    G+"prescribed_failure": [G+"refute_S"],
    G+"refute_S": [G+"actual_S_failure_of_growth", G+"cofinal_growth"],
}

def constants(export, root):
    todo = [root]
    seen, names = set(), set()
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        tag, n = export.node(b"ie", i)
        if tag == "const":
            names.add(n["name"])
        elif tag == "app":
            todo.extend([n["fn"], n["arg"]])
        elif tag in ("lam", "forallE"):
            todo.extend([n["type"], n["body"]])
        elif tag == "letE":
            todo.extend([n["type"], n["value"], n["body"]])
        elif tag == "proj":
            todo.append(n["struct"])
        elif tag not in ("sort", "bvar", "lit", "natVal", "strVal"):
            raise ValueError(f"unhandled expression record: {tag}")
    return names

def check(path, edges):
    export = Export(path)
    try:
        decls = {".".join(map(str, export.name(i))): decl for i, decl in export.declarations.items()}
        for parent, children in edges.items():
            refs = constants(export, decls[parent]["value"])
            for child in children:
                if decls[child]["name"] not in refs:
                    raise ValueError(f"missing proof-body reference: {parent} -> {child}")
                print(f"{parent} -> {child}")
    finally:
        export.data.close()
        export.stream.close()

if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: check-r-dependencies.py JOINT.ndjson SPECTRAL.ndjson")
    check(sys.argv[1], JOINT)
    check(sys.argv[2], SPECTRAL)
