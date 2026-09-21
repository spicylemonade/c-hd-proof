import Frontier.CHD.WinScanE

/-!
# WinScanG — (moved)

The canonical-stop and prefix-monotonicity lemmas (`ScanStop.unique`, `ScanStop.exists`,
`stopOf`, `stopOf_spec`, `ScanStop.eq_stopOf`, `foldl_c_mono`, `foldl_c_prefix`) now live in
`WinScanE` (they are needed by the use-budget version of the scans).  This module is kept only so
that existing imports of `Frontier.CHD.WinScanG` keep working.
-/
