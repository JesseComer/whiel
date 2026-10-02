-- Author: Jesse Comer
import Whiel.Tests.SupplyFreePreproc
import Whiel.Synthesis.Tests.FrameworkIIFixedAmbient
import
  Whiel.Synthesis.Tests.FrameworkIIFixedAmbientAdmission
import
  Whiel.Synthesis.Tests.FrameworkIIFixedAmbientAxiomAudit
import Whiel.Synthesis.Tests.FixedAmbientRegistry
import
  Whiel.Synthesis.Tests.FixedAmbientRegistryAxiomAudit
import Whiel.Synthesis.Tests.FixedAmbientWorker
import
  Whiel.Synthesis.Tests.CounterexampleInstance
import Whiel.Synthesis.Tests.ExactReconstruction
import
  Whiel.Synthesis.Tests.FrameworkIIFixedAmbientClauseNotation
import
  Whiel.Synthesis.Tests.FrameworkIIFixedAmbientCertificate
import
  Whiel.Synthesis.Tests.FixedAmbientCertificateAxiomAudit
import
  Whiel.Synthesis.Tests.FrameworkIIDictionarySoundness
import Whiel.Synthesis.Tests.KernelLratHelper

/-
  Active fixed-ambient Framework-II test aggregate.

  Legacy V4 and finite-validity research tests remain
  explicit opt-in roots outside this product-path aggregate.
-/
