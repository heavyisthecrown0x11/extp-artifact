# EXTp — artifact for "EXTp: A Soundness Theorem for Counterfactual Exploit Replay on Formally Verified Microkernels"

Utku Erol, Independent Researcher — utkuerol71@gmail.com

This repository accompanies the paper (preprint PDF in `paper/`). It contains the
Isabelle/HOL mechanization of the Counterfactual Soundness Theorem's conditional
core, the measurement summaries behind the evaluation section, the seL4/EXTp VMM
boot images used for the bare-metal runs, and the paper figures.

## Contents

| Path | What it is |
|---|---|
| `isabelle/CST_Model.thy` | Isabelle/HOL development: 115 facts, no unproved obligations (`sorry`-free). Session `EXTp_CST`, built against Isabelle2025-1 + HOL-Library. |
| `isabelle/ROOT` | Session definition. |
| `isabelle/build_log.txt` | Output of the last `isabelle build` run (`Finished EXTp_CST`). |
| `measurements/section6_summary.txt` | Numerical summary of the synthetic demonstration (σ̂ baselines, χ² CIs, Δ*, sweep results). |
| `measurements/cross_boot_BOOT_INSTRUCTIONS.txt` | Cross-boot stability collection protocol and hardware identity (N=34 reported in the paper). |
| `measurements/demo_BOOT_INSTRUCTIONS.txt` | Counterfactual fuzzing sweep protocol (r8 varied across 33 curated values). |
| `binaries/demo/` | `kernel-x86_64-pc99` (seL4 microkernel ELF) and `extp-vmm-image-x86_64-pc99` (EXTp VMM rootserver) for the demonstration build (`EXTP_DEMO_BOOT=ON`, `EXTP_NUM_RUNS_OVERRIDE=222`). |
| `binaries/cross-boot/` | Same pair for the cross-boot stability build, plus `extp-vmm-image-x86_64-pc99.reset`, the state-reset utility image swapped in between collection rounds (see the cross-boot instructions). |
| `figures/` | The three evaluation figures as shipped in the paper. |
| `paper/extp.pdf` | Preprint. |

## Reproducing the Isabelle check

```
isabelle build -d isabelle -v EXTp_CST
```

Expected final line: `Finished EXTp_CST`. The theory states A1–A4 as locale
hypotheses (`cst_assumptions`, `sel4_lifting`); the conditional theorem
(`cst_conditional`), the Halpern–Pearl AC2 witnesses, the composition axiom in
its W/K_fwk form, scope-completeness, and Proposition 1 (sequential, trace-threaded,
and parallel-ensemble) are proved from them. Consistency of the locales is
witnessed by explicit models (`cst_withinboot`, `cst_crossboot`). The paper's
Table "Correspondence between the proof of Appendix D and the Isabelle/HOL
development" maps each proof component to a fact name in this file.

## Running the boot images

Bare metal only: Intel 12th Gen Core (Alder Lake), microcode 0x3e, ASUS Z690,
UEFI, P-state locked at 4.9 GHz, serial console at 115200 8N1. Boot
`kernel-x86_64-pc99` with `extp-vmm-image-x86_64-pc99` as the rootserver via a
multiboot-capable loader; see the `*_BOOT_INSTRUCTIONS.txt` files for the exact
build flags and the collection protocol. The images are the ones the reported
numbers were collected with; the VMM source tree is not part of this release.

## Status and limitations

- The cross-boot bound rests on N=34 trials (Clopper–Pearson one-sided 95% upper
  bound on per-run failure ≤ 10.4%). Larger N requires the hardware above, which
  is not currently available to the author; the paper states the bound as is.
- The mechanization covers the conditional core only. The seL4 abstract-machine
  lifting and the calibration-to-HOL interface are open, as discussed in the
  paper's Discussion section.

## Citation

```
@misc{erol2026extp,
  author = {Utku Erol},
  title  = {{EXTp}: A Soundness Theorem for Counterfactual Exploit Replay on Formally Verified Microkernels},
  year   = {2026},
  note   = {Preprint. Artifact: https://github.com/GITHUB-USER/extp-artifact}
}
```

## License

Isabelle sources, instructions and measurement data: MIT (see `LICENSE`).
The paper PDF is © 2026 Utku Erol, all rights reserved; the seL4 kernel ELF is
subject to the seL4 license (GPLv2) of the seL4 project.
