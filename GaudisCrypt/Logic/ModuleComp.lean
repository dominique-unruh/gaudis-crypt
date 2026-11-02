import GaudisCrypt.Language.Modules

/-!
# Applying a composite functor module

`Module.comp f g` is EasyCrypt's alias `module F (X) = f(g(X))`; applied, it is the nested
application (one β-step of the module calculus).
-/

namespace GaudisCrypt

/-- `Module.comp f g` applied to `x` is `f` applied to `g x`. -/
theorem Module.app_comp {A B C : Type 1} [IsModule A] [IsModule B] [IsModule C]
    (f : Module.Arr B C) (g : Module.Arr A B) (x : A) :
    Module.app (Module.comp f g) x = Module.app f (Module.app g x) := by
  have hinj : ∀ u v : C, Module.cast C u = Module.cast C v → u = v := by
    intro u v h
    have := congrArg (Module.cast' C) h
    simp only [Module.cast', Module.cast, eqRec_eq_cast, cast_cast, cast_eq] at this
    exact this
  apply hinj
  apply Module.ext
  rw [Module.cast_app, Module.cast_app]
  rw [Module.cast_app g x]
  simp only [Module.app', Module.comp, Module.toModule_expression]
  change ((ModuleExpression.abs _).reduce.app _).reduce =
    (ModuleExpression.app _ (ModuleExpression.reduce _)).reduce
  rw [ModuleExpression.reduce_app_left, ModuleExpression.reduce_beta,
    ModuleExpression.reduce_app_right]
  simp [ModuleExpression.substitute, ModuleExpression.substituteSimultaneously,
    ModuleExpression.variableSubstitution]
  rfl
end GaudisCrypt
