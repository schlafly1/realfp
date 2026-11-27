import ManyBoxCert
/-! Cost split for the largest certificates: reading the literal, decoding it (precompiled)
and the leaf count walk. -/
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 1
def s1 : String := mb_cert% "../certs/p1_d1024.cert"
def s2 : String := mb_cert% "../certs/p2_d16.cert"
#eval s1.length
#eval RealFP.IntervalTactic.certLeaves (decodeCertC 2 s1)
#eval RealFP.IntervalTactic.certLeaves (decodeCertC 4 s2)
