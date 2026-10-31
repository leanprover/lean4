module
import Test.Module.AutoParamVariable.A
import Test.Module.AutoParamVariable.B

/-! Regression test for #14708: run exported autoParam tactics without importing private declarations. -/

example : True.intro = True.intro := AutoParamVariableA.explicitPublic
example : True.intro = True.intro := AutoParamVariableA.sectionPublic
example : True.intro = True.intro := AutoParamVariableB.explicitPublic
example : True.intro = True.intro := AutoParamVariableB.sectionPublic
