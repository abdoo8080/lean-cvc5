import Test.Init

namespace cvc5.Safe.Test

open cvc5.Test (check!)
open cvc5.Logic

section logics

notation "smt! " => Logic.toSmtLib

#eval do
  check! "LIA"  lia.toSmtLib
  check! "LRA"  lra.toSmtLib
  check! "LIRA" lira.toSmtLib
  check! "NIA"  nia.toSmtLib
  check! "NRA"  nra.toSmtLib
  check! "NIRA" nira.toSmtLib

  check! "QF_LIA"  qf_lia.toSmtLib
  check! "QF_LRA"  qf_lra.toSmtLib
  check! "QF_LIRA" qf_lira.toSmtLib
  check! "QF_NIA"  qf_nia.toSmtLib
  check! "QF_NRA"  qf_nra.toSmtLib
  check! "QF_NIRA" qf_nira.toSmtLib

  check! "QF_ALIA"  qf_lia.array.toSmtLib
  check! "QF_ANIRA" qf_nira.array.toSmtLib

  check! "QF_UFLIA"  qf_lia.uf.toSmtLib
  check! "QF_UFNIRA" qf_nira.uf.toSmtLib

  check! "QF_AUFLIA"  qf_lia.uf.array.toSmtLib
  check! "QF_AUFNIRA" qf_nira.uf.array.toSmtLib

  check! "QF_AUFLIA"  qf_lia.array.uf.toSmtLib
  check! "QF_AUFNIRA" qf_nira.array.uf.toSmtLib

  check! "QF_AFPLIA"  qf_lia.array.float.toSmtLib
  check! "QF_AFPNIRA" qf_nira.array.float.toSmtLib

  check! "QF_UFFPLIA"  qf_lia.uf.float.toSmtLib
  check! "QF_UFFPNIRA" qf_nira.uf.float.toSmtLib

  check! "QF_UFFFLIA"  qf_lia.uf.ff.toSmtLib
  check! "QF_UFFFNIRA" qf_nira.uf.ff.toSmtLib

  check! "QF_UFFFFPLIA"  qf_lia.uf.ff.float.toSmtLib
  check! "QF_UFFFFPNIRA" qf_nira.uf.ff.float.toSmtLib

  check! "IDL" idl.toSmtLib
  check! "RDL" rdl.toSmtLib

  check! "LIRAT" lirat.toSmtLib
  check! "NIAT" niat.toSmtLib

  check! "QF_AIDL" idl.qf.array.toSmtLib
  check! "QF_ARDL" rdl.qf.array.toSmtLib

  check! "QF_ALIRAT" lirat.qf.array.toSmtLib
  check! "QF_ANIAT" niat.qf.array.toSmtLib

end logics
