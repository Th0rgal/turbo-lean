import Batteries.Data.HashMap.Basic
import Batteries.Data.UnionFind.Basic
import Batteries.Data.UInt
import Batteries.Data.BitVec
import C2BatteriesDriver.Scan
import C2BatteriesDriver.Fold

@[export c2_batteries_scan_mix]
def c2_batteries_scan_mix (x0 : UInt64) : UInt64 :=
  c2bScanMix x0

@[export c2_batteries_fold_rank]
def c2_batteries_fold_rank (x0 : UInt64) : UInt64 :=
  c2bFoldRank (c2bScanStep x0 0x5851F42D4C957F2D)
