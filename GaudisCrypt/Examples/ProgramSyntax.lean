import GaudisCrypt.Language.Syntax

open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Syntax

instance : ProgramSpec where
  state := Unit

structure args where
  x : Nat
  y : String

def sig : ProcedureSignature where
  params := []
  ret := Unit

def testProc : Procedure sig where
  locals := []
  return_val := Getter.mk fun _ => ()
  body := sorry
