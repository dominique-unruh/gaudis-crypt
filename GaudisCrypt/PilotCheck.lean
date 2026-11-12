import GaudisCrypt.Logic.AbstractCallTest
import GaudisCrypt.Logic.ECAliasTest
import GaudisCrypt.Logic.ECAutoTest
import GaudisCrypt.Logic.ECCallsTest
import GaudisCrypt.Logic.ECCloseTest
import GaudisCrypt.Logic.ECConseqTest
import GaudisCrypt.Logic.ECGoalsTest
import GaudisCrypt.Logic.ECIfTest
import GaudisCrypt.Logic.ECLoopTest
import GaudisCrypt.Logic.ECRulesTest
import GaudisCrypt.Logic.ECSpTest
import GaudisCrypt.Logic.ECTransTest
import GaudisCrypt.Logic.ECWhileRelTest
import GaudisCrypt.Logic.GlobWritesTest
import GaudisCrypt.Logic.InlineTest
import GaudisCrypt.Logic.PHoareSeqTest
import GaudisCrypt.Logic.PHoareWpTest
import GaudisCrypt.Logic.PRHLWpTest
import GaudisCrypt.Logic.ReadNormTest
import GaudisCrypt.Logic.StmtSwapTest
import GaudisCrypt.Examples.SHA3.Pilot.ConcreteF
import GaudisCrypt.Examples.SHA3.Pilot.Gcol
import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.Pilot.Gconcl_list
import GaudisCrypt.Examples.SHA3.Pilot.Gext
import GaudisCrypt.Examples.SHA3.Pilot.Handle
import GaudisCrypt.Examples.SHA3.Pilot.IRO
import GaudisCrypt.Examples.SHA3.Pilot.IndifRO_is_secure
import GaudisCrypt.Examples.SHA3.Pilot.Indifferentiability
import GaudisCrypt.Examples.SHA3.Pilot.OptionIndifferentiability
import GaudisCrypt.Examples.SHA3.Pilot.SHA3Indiff
import GaudisCrypt.Examples.SHA3.Pilot.SLCommon
import GaudisCrypt.Examples.SHA3.Pilot.SecureHash
import GaudisCrypt.Examples.SHA3.Pilot.SecureORO
import GaudisCrypt.Examples.SHA3.Pilot.SecureRO
import GaudisCrypt.Examples.SHA3.Pilot.Sponge

/-!
# The day-to-day check: the tactic tests and the EC-fidelity pilots

    lake build GaudisCrypt.PilotCheck

builds the tests of the tactic layer (`Logic/*Test.lean`, the golden tests among them) and every
pilot (`Examples/SHA3/Pilot/`), with what they import, and nothing else: about 70% of the
project.  Use it after a change of a tactic.  The full `lake build` (every module, the first
SHA-3 port included) is for before a push; a file outside this check that an intended tactic
change breaks is taken out of the barrel and retired, not repaired (2026-11-13).

A new pilot or tactic test is added here and to `GaudisCrypt.lean`.
-/
