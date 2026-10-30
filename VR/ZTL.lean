-- VR/ZTL.lean
-- VR Part II: the operational set universe (SetsOp) raised onto ZTL —
-- witnessed identity as zero-trust atoms. Step (а) of the programme;
-- the measured Python twin is ZTL/zopsets.py (E21), the vendored
-- kernel pin is in ZTL/Kernel.lean. Dependency direction: VR never
-- depends on ZTL (the kernel is a pinned copy); ZTL, since 2026-10-10,
-- depends on VR's numbers (VR.Numbers.RealsOp) — see ZTL/Kernel.lean.

import VR.ZTL.Kernel
import VR.ZTL.Atoms
import VR.ZTL.Stages
import VR.ZTL.Survival
