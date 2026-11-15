import GaudisCrypt.Logic.AbstractCallTest
import GaudisCrypt.Logic.ECAliasTest
import GaudisCrypt.Logic.ECAutoTest
import GaudisCrypt.Logic.ECCallsTest
import GaudisCrypt.Logic.ECCloseTest
import GaudisCrypt.Logic.ECConseqTest
import GaudisCrypt.Logic.ECGoalsTest
import GaudisCrypt.Logic.ECIfTest
import GaudisCrypt.Logic.ECLoopTest
import GaudisCrypt.Logic.ECProgressTest
import GaudisCrypt.Logic.ECRulesTest
import GaudisCrypt.Logic.ECSpTest
import GaudisCrypt.Logic.ECTransTest
import GaudisCrypt.Logic.ECConseqHoareTest
import GaudisCrypt.Logic.ECProcInvTest
import GaudisCrypt.Syntax.CloneTest
import GaudisCrypt.Logic.ECWhileRelTest
import GaudisCrypt.Logic.GlobWritesTest
import GaudisCrypt.Logic.InlineTest
import GaudisCrypt.Logic.PHoareSeqTest
import GaudisCrypt.Logic.ByPrTest
import GaudisCrypt.Logic.PHoareRndTest
import GaudisCrypt.Logic.ECRndTest
import GaudisCrypt.Logic.PHoareWhileRevTest
import GaudisCrypt.Logic.ECCallTrueTest
import GaudisCrypt.Logic.ECCallMultiProcTest
import GaudisCrypt.Syntax.ModuleVarTest
import GaudisCrypt.Logic.ECInlineParamsTest
import GaudisCrypt.Logic.PHoareWpTest
import GaudisCrypt.Logic.PRHLWpTest
import GaudisCrypt.Logic.ReadNormTest
import GaudisCrypt.Logic.StmtSwapTest
import GaudisCrypt.Examples.SHA3.SmartCounter.ConcreteF
import GaudisCrypt.Examples.SHA3.SmartCounter.Gcol
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list
import GaudisCrypt.Examples.SHA3.SmartCounter.Gext
import GaudisCrypt.Examples.SHA3.SmartCounter.Handle
import GaudisCrypt.Examples.SHA3.IRO
import GaudisCrypt.Examples.SHA3.IndifRO_is_secure
import GaudisCrypt.Examples.SHA3.Indifferentiability
import GaudisCrypt.Examples.SHA3.OptionIndifferentiability
import GaudisCrypt.Examples.SHA3.SHA3Indiff
import GaudisCrypt.Examples.SHA3.SHA3Security
import GaudisCrypt.Examples.SHA3.SHA3OSecurity
import GaudisCrypt.Examples.SHA3.SHA3_OIndiff
import GaudisCrypt.Examples.SHA3.SmartCounter.SLCommon
import GaudisCrypt.Examples.SHA3.SecureHash
import GaudisCrypt.Examples.SHA3.SecureORO
import GaudisCrypt.Examples.SHA3.SecureRO
import GaudisCrypt.Examples.SHA3.Sponge

/-!
# The day-to-day check: the tactic tests and the SHA-3 port

    lake build GaudisCrypt.PilotCheck

builds the tests of the tactic layer (`Logic/*Test.lean`, the golden tests among them) and the
SHA-3 port (`Examples/SHA3/`, the EC-fidelity port: the former `Examples/SHA3/Pilot/`, hence the
name), with what they import, and nothing else: about 70% of the project.  Use it after a change
of a tactic.  The full `lake build` (every module) is for before a push; a file outside this check
that an intended tactic change breaks is taken out of the barrel and retired, not repaired
(2026-11-13).

A new tactic test is added here and to `GaudisCrypt.lean`.
-/
