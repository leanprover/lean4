// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Eqns
// Imports: public import Lean.Elab.PreDefinition.FixedParams import Lean.Elab.PreDefinition.EqnsUtils import Lean.Meta.Tactic.CasesOnStuckLHS import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.Simp.Main import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.CasesOnStuckLHS import Lean.Meta.Tactic.Split
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static const lean_string_object l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3;
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
static lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_toArray___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "could not find `.brecOn` application in"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__4_value;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "goal not an equality"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " step:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1;
lean_object* l_Lean_exceptEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__1_value;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__3;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0_value;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 150, 182, 177, 14, 34, 156, 192)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "whnfReducibleLHS succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpMatch\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpIf\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "simpTargetStar closed the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deltaRHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "casesOnStuckLHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "splitTarget\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no progress at goal\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "simpTargetStar modified the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tryContadiction succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tryURefl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38;
static double l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "theorem `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not an equality\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "abstracting"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " from"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "no theorem `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_define(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " goUnfold:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " proving:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "failed to generate equational theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2_value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_;
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 221, 148, 2, 30, 47, 242, 74)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 216, 81, 142, 241, 75, 113, 77)}};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_eqnInfoExt;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__0;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__1;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 19, 250, 232, 19, 103, 59, 84)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 64, 85, 238, 73, 235, 224, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 241, 197, 13, 174, 23, 186, 239)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 117, 235, 94, 194, 72, 147, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 13, 135, 45, 158, 59, 107)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 222, 70, 43, 201, 77, 119, 184)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 51, 79, 28, 160, 228, 197, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 131, 204, 33, 154, 17, 78, 114)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 169, 96, 182, 175, 131, 16, 69)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 31, 30, 186, 131, 197, 38, 7)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_instInhabitedFixedParamPerms_default;
x_2 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_3);
lean_ctor_set(x_7, 5, x_2);
lean_ctor_set(x_7, 6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Subarray_toArray___redArg(x_1);
lean_inc_ref(x_4);
x_11 = l_Lean_mkAppN(x_4, x_10);
lean_dec_ref(x_10);
x_12 = lean_apply_8(x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_mkProj(x_1, x_2, x_7);
x_14 = l_Lean_mkAppN(x_13, x_3);
x_15 = lean_apply_8(x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_3);
x_23 = lean_array_set(x_4, x_5, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_5, x_24);
lean_dec(x_5);
x_3 = x_21;
x_4 = x_23;
x_5 = x_25;
goto _start;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_3);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_28);
lean_closure_set(x_30, 2, x_4);
lean_closure_set(x_30, 3, x_2);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(x_29, x_30, x_6, x_7, x_8, x_9);
return x_31;
}
else
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_st_ref_get(x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec(x_33);
lean_inc(x_32);
x_35 = l_Lean_isBRecOnRecursor(x_34, x_32);
if (x_35 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_36; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
x_36 = lean_infer_type(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__2));
x_39 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_40 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(x_37, x_38, x_39, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_get_size(x_4);
x_43 = lean_nat_dec_le(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_1);
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_41);
lean_inc_ref(x_4);
x_45 = l_Array_toSubarray___redArg(x_4, x_44, x_41);
x_46 = l_Subarray_toArray___redArg(x_45);
x_47 = l_Lean_mkAppN(x_3, x_46);
lean_dec_ref(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_47);
x_48 = lean_infer_type(x_47, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Array_toSubarray___redArg(x_4, x_41, x_42);
x_51 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_47);
x_52 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__4));
x_53 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(x_52, x_49, x_51, x_6, x_7, x_8, x_9);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec_ref(x_47);
lean_dec(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
lean_dec(x_36);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1;
x_17 = l_Lean_indentExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_18, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_3);
x_23 = lean_array_set(x_4, x_5, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_5, x_24);
x_26 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg(x_1, x_2, x_21, x_23, x_25, x_6, x_7, x_8, x_9);
return x_26;
}
else
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_3);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_28);
lean_closure_set(x_30, 2, x_4);
lean_closure_set(x_30, 3, x_2);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(x_29, x_30, x_6, x_7, x_8, x_9);
return x_31;
}
else
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_st_ref_get(x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec(x_33);
lean_inc(x_32);
x_35 = l_Lean_isBRecOnRecursor(x_34, x_32);
if (x_35 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_36; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
x_36 = lean_infer_type(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__2));
x_39 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_40 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(x_37, x_38, x_39, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_get_size(x_4);
x_43 = lean_nat_dec_le(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_1);
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_41);
lean_inc_ref(x_4);
x_45 = l_Array_toSubarray___redArg(x_4, x_44, x_41);
x_46 = l_Subarray_toArray___redArg(x_45);
x_47 = l_Lean_mkAppN(x_3, x_46);
lean_dec_ref(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_47);
x_48 = lean_infer_type(x_47, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Array_toSubarray___redArg(x_4, x_41, x_42);
x_51 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_47);
x_52 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__4));
x_53 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(x_52, x_49, x_51, x_6, x_7, x_8, x_9);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec_ref(x_47);
lean_dec(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
lean_dec(x_36);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = lean_box(0);
goto block_20;
}
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1;
x_17 = l_Lean_indentExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_18, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0;
x_9 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_9);
x_10 = lean_mk_array(x_9, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_9, x_11);
lean_dec(x_9);
lean_inc_ref(x_1);
x_13 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(x_1, x_2, x_1, x_10, x_12, x_3, x_4, x_5, x_6);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_mkEq(x_5, x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0;
x_14 = lean_array_push(x_13, x_4);
x_15 = 0;
x_16 = 1;
x_17 = l_Lean_Meta_mkLambdaFVars(x_14, x_12, x_15, x_2, x_15, x_2, x_16, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_3);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3;
x_11 = l_Lean_indentExpr(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_12, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_17 = lean_box(x_9);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed), 10, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(x_15, x_18, x_2, x_3, x_4, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_10, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
x_15 = l_Lean_Expr_appArg_x21(x_10);
x_16 = l_Lean_Expr_consumeMData(x_15);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_delta_x3f(x_16, x_2, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
uint8_t x_20; 
lean_free_object(x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Expr_appFn_x21(x_10);
lean_dec(x_10);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec_ref(x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_24 = l_Lean_Meta_mkEq(x_23, x_21, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_25, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_19, 0, x_28);
lean_ctor_set(x_26, 0, x_19);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_19, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_19);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
x_38 = l_Lean_Expr_appFn_x21(x_10);
lean_dec(x_10);
x_39 = l_Lean_Expr_appArg_x21(x_38);
lean_dec_ref(x_38);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_mkEq(x_39, x_37, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_41, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_53 = lean_box(0);
lean_ctor_set(x_17, 0, x_53);
return x_17;
}
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_17, 0);
lean_inc(x_54);
lean_dec(x_17);
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Expr_appFn_x21(x_10);
lean_dec(x_10);
x_58 = l_Lean_Expr_appArg_x21(x_57);
lean_dec_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_59 = l_Lean_Meta_mkEq(x_58, x_55, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_60, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_56);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_54);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_17, 0);
lean_inc(x_75);
lean_dec(x_17);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_8, 0);
lean_inc(x_77);
lean_dec(x_8);
x_78 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Expr_isAppOfArity(x_77, x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = l_Lean_Expr_appArg_x21(x_77);
x_84 = l_Lean_Expr_consumeMData(x_83);
lean_dec_ref(x_83);
x_85 = l_Lean_Meta_delta_x3f(x_84, x_2, x_5, x_6);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_obj_tag(x_86) == 1)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Expr_appFn_x21(x_77);
lean_dec(x_77);
x_91 = l_Lean_Expr_appArg_x21(x_90);
lean_dec_ref(x_90);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_92 = l_Lean_Meta_mkEq(x_91, x_88, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_93, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_89;
}
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_89);
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_100 = x_94;
} else {
 lean_dec_ref(x_94);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_89);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_105 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_106 = lean_alloc_ctor(0, 1, 0);
} else {
 x_106 = x_87;
}
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_108 = x_85;
} else {
 lean_dec_ref(x_85);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
return x_8;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
lean_dec(x_8);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_1, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_exceptEmoji___redArg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_st_ref_get(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_replaceRef(x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(x_20, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_st_ref_take(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Lean_PersistentArray_push___redArg(x_1, x_29);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_8, x_24);
x_32 = lean_box(0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_23);
x_35 = l_Lean_PersistentArray_push___redArg(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_33);
lean_ctor_set(x_24, 4, x_36);
x_37 = lean_st_ref_set(x_8, x_24);
x_38 = lean_box(0);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 5);
x_45 = lean_ctor_get(x_24, 6);
x_46 = lean_ctor_get(x_24, 7);
x_47 = lean_ctor_get(x_24, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_48 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_23);
x_51 = l_Lean_PersistentArray_push___redArg(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 8);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint64(x_52, sizeof(void*)*1, x_48);
x_53 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_44);
lean_ctor_set(x_53, 6, x_45);
lean_ctor_set(x_53, 7, x_46);
lean_ctor_set(x_53, 8, x_47);
x_54 = lean_st_ref_set(x_8, x_53);
x_55 = lean_box(0);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
lean_dec(x_21);
x_57 = lean_st_ref_take(x_8);
x_58 = lean_ctor_get(x_57, 4);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_57, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_57, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_57, 8);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get_uint64(x_58, sizeof(void*)*1);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_56);
x_71 = l_Lean_PersistentArray_push___redArg(x_1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 9, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_63);
lean_ctor_set(x_73, 6, x_64);
lean_ctor_set(x_73, 7, x_65);
lean_ctor_set(x_73, 8, x_66);
x_74 = lean_st_ref_set(x_8, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
x_79 = lean_ctor_get(x_7, 2);
x_80 = lean_ctor_get(x_7, 3);
x_81 = lean_ctor_get(x_7, 4);
x_82 = lean_ctor_get(x_7, 5);
x_83 = lean_ctor_get(x_7, 6);
x_84 = lean_ctor_get(x_7, 7);
x_85 = lean_ctor_get(x_7, 8);
x_86 = lean_ctor_get(x_7, 9);
x_87 = lean_ctor_get(x_7, 10);
x_88 = lean_ctor_get(x_7, 11);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_90 = lean_ctor_get(x_7, 12);
x_91 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_92 = lean_ctor_get(x_7, 13);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_93 = lean_st_ref_get(x_8);
x_94 = lean_ctor_get(x_93, 4);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_replaceRef(x_3, x_82);
lean_dec(x_82);
x_97 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
lean_ctor_set(x_97, 9, x_86);
lean_ctor_set(x_97, 10, x_87);
lean_ctor_set(x_97, 11, x_88);
lean_ctor_set(x_97, 12, x_90);
lean_ctor_set(x_97, 13, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*14, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*14 + 1, x_91);
x_98 = l_Lean_PersistentArray_toArray___redArg(x_95);
lean_dec_ref(x_95);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6_spec__7(x_99, x_100, x_98);
x_102 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_4);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(x_102, x_5, x_6, x_97, x_8);
lean_dec_ref(x_97);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_st_ref_take(x_8);
x_107 = lean_ctor_get(x_106, 4);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_106, 5);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_106, 6);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_106, 7);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_106, 8);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get_uint64(x_107, sizeof(void*)*1);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_104);
x_120 = l_Lean_PersistentArray_push___redArg(x_1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint64(x_121, sizeof(void*)*1, x_117);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_109);
lean_ctor_set(x_122, 2, x_110);
lean_ctor_set(x_122, 3, x_111);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_112);
lean_ctor_set(x_122, 6, x_113);
lean_ctor_set(x_122, 7, x_114);
lean_ctor_set(x_122, 8, x_115);
x_123 = lean_st_ref_set(x_8, x_122);
x_124 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_105;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_48; double x_81; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lean_trace_profiler;
x_33 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_4, x_32);
if (x_33 == 0)
{
x_48 = x_33;
goto block_80;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_trace_profiler_useHeartbeats;
x_88 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_4, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; double x_91; double x_92; double x_93; 
x_89 = l_Lean_trace_profiler_threshold;
x_90 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(x_4, x_89);
x_91 = lean_float_of_nat(x_90);
x_92 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__3;
x_93 = lean_float_div(x_91, x_92);
x_81 = x_93;
goto block_86;
}
else
{
lean_object* x_94; lean_object* x_95; double x_96; 
x_94 = l_Lean_trace_profiler_threshold;
x_95 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(x_4, x_94);
x_96 = lean_float_of_nat(x_95);
x_81 = x_96;
goto block_86;
}
}
block_29:
{
lean_object* x_24; 
x_24 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(x_6, x_18, x_16, x_17, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_14);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
block_42:
{
double x_37; lean_object* x_38; 
x_37 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
lean_inc_ref(x_3);
lean_inc(x_1);
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_2);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_34;
x_17 = x_35;
x_18 = x_38;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_39; double x_40; double x_41; 
lean_dec_ref(x_38);
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_unbox_float(x_30);
lean_dec(x_30);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_40);
x_41 = lean_unbox_float(x_31);
lean_dec(x_31);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_41);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_2);
x_16 = x_34;
x_17 = x_35;
x_18 = x_39;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_44 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_43);
x_34 = x_43;
x_35 = x_45;
x_36 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_44);
x_46 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2;
lean_inc(x_43);
x_34 = x_43;
x_35 = x_46;
x_36 = lean_box(0);
goto block_42;
}
}
block_80:
{
if (x_5 == 0)
{
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_49 = lean_st_ref_take(x_12);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = l_Lean_PersistentArray_append___redArg(x_6, x_53);
lean_dec_ref(x_53);
lean_ctor_set(x_51, 0, x_54);
x_55 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_56 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_14);
return x_56;
}
else
{
uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get_uint64(x_51, sizeof(void*)*1);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_PersistentArray_append___redArg(x_6, x_58);
lean_dec_ref(x_58);
x_60 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_57);
lean_ctor_set(x_49, 4, x_60);
x_61 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_62 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_14);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
x_66 = lean_ctor_get(x_49, 2);
x_67 = lean_ctor_get(x_49, 3);
x_68 = lean_ctor_get(x_49, 5);
x_69 = lean_ctor_get(x_49, 6);
x_70 = lean_ctor_get(x_49, 7);
x_71 = lean_ctor_get(x_49, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_63);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_72 = lean_ctor_get_uint64(x_63, sizeof(void*)*1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = l_Lean_PersistentArray_append___redArg(x_6, x_73);
lean_dec_ref(x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 8);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint64(x_76, sizeof(void*)*1, x_72);
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_68);
lean_ctor_set(x_77, 6, x_69);
lean_ctor_set(x_77, 7, x_70);
lean_ctor_set(x_77, 8, x_71);
x_78 = lean_st_ref_set(x_12, x_77);
lean_dec(x_12);
x_79 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_14);
return x_79;
}
}
else
{
goto block_47;
}
}
else
{
goto block_47;
}
}
block_86:
{
double x_82; double x_83; double x_84; uint8_t x_85; 
x_82 = lean_unbox_float(x_31);
x_83 = lean_unbox_float(x_30);
x_84 = lean_float_sub(x_82, x_83);
x_85 = lean_float_decLt(x_81, x_84);
x_48 = x_85;
goto block_80;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18;
x_4 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_2, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(x_3, x_1, x_16, x_17, x_11, x_5, x_6, x_7, x_8);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_10);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(x_3, x_1, x_19, x_20, x_11, x_5, x_6, x_7, x_8);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_5, 2);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
x_38 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
if (x_37 == 0)
{
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = lean_box(0);
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_822; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec_ref(x_303);
lean_inc(x_2);
x_305 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(x_305, 0, x_2);
x_306 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_822 = lean_unbox(x_304);
if (x_822 == 0)
{
lean_object* x_823; uint8_t x_824; 
x_823 = l_Lean_trace_profiler;
x_824 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_36, x_823);
if (x_824 == 0)
{
lean_dec_ref(x_305);
lean_dec(x_304);
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = lean_box(0);
goto block_302;
}
else
{
lean_inc_ref(x_36);
goto block_821;
}
}
else
{
lean_inc_ref(x_36);
goto block_821;
}
block_320:
{
lean_object* x_311; double x_312; double x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_311 = lean_io_get_num_heartbeats();
x_312 = lean_float_of_nat(x_307);
x_313 = lean_float_of_nat(x_311);
x_314 = lean_box_float(x_312);
x_315 = lean_box_float(x_313);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_unbox(x_304);
lean_dec(x_304);
x_319 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_38, x_37, x_306, x_36, x_318, x_308, x_305, x_317, x_3, x_4, x_5, x_6);
lean_dec_ref(x_36);
return x_319;
}
block_326:
{
lean_object* x_325; 
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_323);
x_307 = x_321;
x_308 = x_322;
x_309 = x_325;
x_310 = lean_box(0);
goto block_320;
}
block_332:
{
lean_object* x_331; 
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_329);
x_307 = x_327;
x_308 = x_328;
x_309 = x_331;
x_310 = lean_box(0);
goto block_320;
}
block_338:
{
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
x_321 = x_333;
x_322 = x_334;
x_323 = x_336;
x_324 = lean_box(0);
goto block_326;
}
else
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
lean_dec_ref(x_335);
x_327 = x_333;
x_328 = x_334;
x_329 = x_337;
x_330 = lean_box(0);
goto block_332;
}
}
block_355:
{
lean_object* x_343; double x_344; double x_345; double x_346; double x_347; double x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; 
x_343 = lean_io_mono_nanos_now();
x_344 = lean_float_of_nat(x_339);
x_345 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39;
x_346 = lean_float_div(x_344, x_345);
x_347 = lean_float_of_nat(x_343);
x_348 = lean_float_div(x_347, x_345);
x_349 = lean_box_float(x_346);
x_350 = lean_box_float(x_348);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_unbox(x_304);
lean_dec(x_304);
x_354 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_38, x_37, x_306, x_36, x_353, x_340, x_305, x_352, x_3, x_4, x_5, x_6);
lean_dec_ref(x_36);
return x_354;
}
block_361:
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_360, 0, x_358);
x_339 = x_356;
x_340 = x_357;
x_341 = x_360;
x_342 = lean_box(0);
goto block_355;
}
block_367:
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_364);
x_339 = x_362;
x_340 = x_363;
x_341 = x_366;
x_342 = lean_box(0);
goto block_355;
}
block_373:
{
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
lean_dec_ref(x_370);
x_362 = x_368;
x_363 = x_369;
x_364 = x_371;
x_365 = lean_box(0);
goto block_367;
}
else
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
lean_dec_ref(x_370);
x_356 = x_368;
x_357 = x_369;
x_358 = x_372;
x_359 = lean_box(0);
goto block_361;
}
}
block_821:
{
lean_object* x_374; 
x_374 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(x_6);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec_ref(x_374);
x_376 = l_Lean_trace_profiler_useHeartbeats;
x_377 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_36, x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_io_mono_nanos_now();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_379 = l_Lean_Elab_Eqns_tryURefl(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
x_381 = lean_unbox(x_380);
lean_dec(x_380);
if (x_381 == 0)
{
lean_object* x_382; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_382 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_385 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec_ref(x_385);
if (lean_obj_tag(x_386) == 1)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_2);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec_ref(x_386);
x_388 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
x_390 = lean_unbox(x_389);
lean_dec(x_389);
if (x_390 == 0)
{
lean_object* x_391; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_391 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_387, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_391;
goto block_373;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
x_393 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_392, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
lean_dec_ref(x_393);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_394 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_387, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_394;
goto block_373;
}
else
{
lean_dec(x_387);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_393;
goto block_373;
}
}
}
else
{
lean_object* x_395; 
lean_dec(x_387);
lean_dec(x_1);
x_395 = lean_ctor_get(x_388, 0);
lean_inc(x_395);
lean_dec_ref(x_388);
x_356 = x_378;
x_357 = x_375;
x_358 = x_395;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_396; 
lean_dec(x_386);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_396 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
if (lean_obj_tag(x_397) == 1)
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_2);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_399 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
x_401 = lean_unbox(x_400);
lean_dec(x_400);
if (x_401 == 0)
{
lean_object* x_402; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_402 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_398, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_402;
goto block_373;
}
else
{
lean_object* x_403; lean_object* x_404; 
x_403 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
x_404 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_403, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
lean_dec_ref(x_404);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_405 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_398, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_405;
goto block_373;
}
else
{
lean_dec(x_398);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_404;
goto block_373;
}
}
}
else
{
lean_object* x_406; 
lean_dec(x_398);
lean_dec(x_1);
x_406 = lean_ctor_get(x_399, 0);
lean_inc(x_406);
lean_dec_ref(x_399);
x_356 = x_378;
x_357 = x_375;
x_358 = x_406;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_407; 
lean_dec(x_397);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_407 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_37, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec_ref(x_407);
if (lean_obj_tag(x_408) == 1)
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_2);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
lean_dec_ref(x_408);
x_410 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; uint8_t x_412; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
x_412 = lean_unbox(x_411);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_413 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_409, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_413;
goto block_373;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
x_415 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_414, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
lean_dec_ref(x_415);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_416 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_409, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_416;
goto block_373;
}
else
{
lean_dec(x_409);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_415;
goto block_373;
}
}
}
else
{
lean_object* x_417; 
lean_dec(x_409);
lean_dec(x_1);
x_417 = lean_ctor_get(x_410, 0);
lean_inc(x_417);
lean_dec_ref(x_410);
x_356 = x_378;
x_357 = x_375;
x_358 = x_417;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_408);
x_418 = lean_unsigned_to_nat(100000u);
x_419 = lean_unsigned_to_nat(2u);
x_420 = 0;
x_421 = lean_alloc_ctor(0, 2, 28);
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*2, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 2, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 3, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 4, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 5, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 6, x_420);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 7, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 8, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 9, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 10, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 11, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 12, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 13, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 14, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 15, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 16, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 17, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 18, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 19, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 20, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 21, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 22, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 23, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 24, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 25, x_37);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 26, x_377);
lean_ctor_set_uint8(x_421, sizeof(void*)*2 + 27, x_377);
x_422 = lean_unsigned_to_nat(0u);
x_423 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11;
x_424 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13;
x_425 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
x_426 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set_uint8(x_426, sizeof(void*)*2, x_37);
x_427 = l_Lean_Meta_Simp_mkContext___redArg(x_421, x_423, x_426, x_3, x_6);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
x_429 = lean_box(0);
x_430 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_431 = l_Lean_Meta_simpTargetStar(x_2, x_428, x_423, x_429, x_430, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
x_433 = !lean_is_exclusive(x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_432, 0);
x_435 = lean_ctor_get(x_432, 1);
lean_dec(x_435);
switch (lean_obj_tag(x_434)) {
case 0:
{
lean_object* x_436; 
lean_free_object(x_432);
lean_dec(x_2);
lean_dec(x_1);
x_436 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; uint8_t x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = lean_unbox(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
x_439 = lean_box(0);
x_362 = x_378;
x_363 = x_375;
x_364 = x_439;
x_365 = lean_box(0);
goto block_367;
}
else
{
lean_object* x_440; lean_object* x_441; 
x_440 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_441 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_440, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_441;
goto block_373;
}
}
else
{
lean_object* x_442; 
x_442 = lean_ctor_get(x_436, 0);
lean_inc(x_442);
lean_dec_ref(x_436);
x_356 = x_378;
x_357 = x_375;
x_358 = x_442;
x_359 = lean_box(0);
goto block_361;
}
}
case 1:
{
lean_object* x_443; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_443 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
lean_dec_ref(x_443);
if (lean_obj_tag(x_444) == 1)
{
lean_object* x_445; lean_object* x_446; 
lean_free_object(x_432);
lean_dec(x_2);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
lean_dec_ref(x_444);
x_446 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; uint8_t x_448; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_448 = lean_unbox(x_447);
lean_dec(x_447);
if (x_448 == 0)
{
lean_object* x_449; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_449 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_445, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_449;
goto block_373;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_451 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_450, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
lean_dec_ref(x_451);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_452 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_445, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_452;
goto block_373;
}
else
{
lean_dec(x_445);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_451;
goto block_373;
}
}
}
else
{
lean_object* x_453; 
lean_dec(x_445);
lean_dec(x_1);
x_453 = lean_ctor_get(x_446, 0);
lean_inc(x_453);
lean_dec_ref(x_446);
x_356 = x_378;
x_357 = x_375;
x_358 = x_453;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_454; 
lean_dec(x_444);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_454 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec_ref(x_454);
if (lean_obj_tag(x_455) == 1)
{
lean_object* x_456; lean_object* x_457; 
lean_free_object(x_432);
lean_dec(x_2);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
lean_dec_ref(x_455);
x_457 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; uint8_t x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
x_459 = lean_unbox(x_458);
lean_dec(x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_461 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_456, x_422, x_1, x_460, x_3, x_4, x_5, x_6);
lean_dec(x_456);
x_368 = x_378;
x_369 = x_375;
x_370 = x_461;
goto block_373;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_463 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_462, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_465 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_456, x_422, x_1, x_464, x_3, x_4, x_5, x_6);
lean_dec(x_456);
x_368 = x_378;
x_369 = x_375;
x_370 = x_465;
goto block_373;
}
else
{
lean_dec(x_456);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_463;
goto block_373;
}
}
}
else
{
lean_object* x_466; 
lean_dec(x_456);
lean_dec(x_1);
x_466 = lean_ctor_get(x_457, 0);
lean_inc(x_466);
lean_dec_ref(x_457);
x_356 = x_378;
x_357 = x_375;
x_358 = x_466;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_467; 
lean_dec(x_455);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_467 = l_Lean_Meta_splitTarget_x3f(x_2, x_37, x_37, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_467) == 0)
{
uint8_t x_468; 
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; 
x_469 = lean_ctor_get(x_467, 0);
if (lean_obj_tag(x_469) == 1)
{
lean_object* x_470; lean_object* x_471; 
lean_free_object(x_467);
lean_free_object(x_432);
lean_dec(x_2);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec_ref(x_469);
x_471 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; uint8_t x_473; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
lean_dec_ref(x_471);
x_473 = lean_unbox(x_472);
lean_dec(x_472);
if (x_473 == 0)
{
lean_object* x_474; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_474 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_470, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_474;
goto block_373;
}
else
{
lean_object* x_475; lean_object* x_476; 
x_475 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_476 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_475, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; 
lean_dec_ref(x_476);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_477 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_470, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_477;
goto block_373;
}
else
{
lean_dec(x_470);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_476;
goto block_373;
}
}
}
else
{
lean_object* x_478; 
lean_dec(x_470);
lean_dec(x_1);
x_478 = lean_ctor_get(x_471, 0);
lean_inc(x_478);
lean_dec_ref(x_471);
x_356 = x_378;
x_357 = x_375;
x_358 = x_478;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_469);
lean_dec(x_1);
x_479 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
lean_ctor_set_tag(x_467, 1);
lean_ctor_set(x_467, 0, x_2);
lean_ctor_set_tag(x_432, 7);
lean_ctor_set(x_432, 1, x_467);
lean_ctor_set(x_432, 0, x_479);
x_480 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_432, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_480;
goto block_373;
}
}
else
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_467, 0);
lean_inc(x_481);
lean_dec(x_467);
if (lean_obj_tag(x_481) == 1)
{
lean_object* x_482; lean_object* x_483; 
lean_free_object(x_432);
lean_dec(x_2);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
lean_dec_ref(x_481);
x_483 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; uint8_t x_485; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
lean_dec_ref(x_483);
x_485 = lean_unbox(x_484);
lean_dec(x_484);
if (x_485 == 0)
{
lean_object* x_486; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_486 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_482, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_486;
goto block_373;
}
else
{
lean_object* x_487; lean_object* x_488; 
x_487 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_488 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_487, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; 
lean_dec_ref(x_488);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_489 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_482, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_489;
goto block_373;
}
else
{
lean_dec(x_482);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_488;
goto block_373;
}
}
}
else
{
lean_object* x_490; 
lean_dec(x_482);
lean_dec(x_1);
x_490 = lean_ctor_get(x_483, 0);
lean_inc(x_490);
lean_dec_ref(x_483);
x_356 = x_378;
x_357 = x_375;
x_358 = x_490;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_481);
lean_dec(x_1);
x_491 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
x_492 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_492, 0, x_2);
lean_ctor_set_tag(x_432, 7);
lean_ctor_set(x_432, 1, x_492);
lean_ctor_set(x_432, 0, x_491);
x_493 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_432, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_493;
goto block_373;
}
}
}
else
{
lean_object* x_494; 
lean_free_object(x_432);
lean_dec(x_2);
lean_dec(x_1);
x_494 = lean_ctor_get(x_467, 0);
lean_inc(x_494);
lean_dec_ref(x_467);
x_356 = x_378;
x_357 = x_375;
x_358 = x_494;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_495; 
lean_free_object(x_432);
lean_dec(x_2);
lean_dec(x_1);
x_495 = lean_ctor_get(x_454, 0);
lean_inc(x_495);
lean_dec_ref(x_454);
x_356 = x_378;
x_357 = x_375;
x_358 = x_495;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_496; 
lean_free_object(x_432);
lean_dec(x_2);
lean_dec(x_1);
x_496 = lean_ctor_get(x_443, 0);
lean_inc(x_496);
lean_dec_ref(x_443);
x_356 = x_378;
x_357 = x_375;
x_358 = x_496;
x_359 = lean_box(0);
goto block_361;
}
}
default: 
{
lean_object* x_497; lean_object* x_498; 
lean_free_object(x_432);
lean_dec(x_2);
x_497 = lean_ctor_get(x_434, 0);
lean_inc(x_497);
lean_dec_ref(x_434);
x_498 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; uint8_t x_500; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
lean_dec_ref(x_498);
x_500 = lean_unbox(x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_501 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_497, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_501;
goto block_373;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_503 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_502, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
lean_dec_ref(x_503);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_504 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_497, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_504;
goto block_373;
}
else
{
lean_dec(x_497);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_503;
goto block_373;
}
}
}
else
{
lean_object* x_505; 
lean_dec(x_497);
lean_dec(x_1);
x_505 = lean_ctor_get(x_498, 0);
lean_inc(x_505);
lean_dec_ref(x_498);
x_356 = x_378;
x_357 = x_375;
x_358 = x_505;
x_359 = lean_box(0);
goto block_361;
}
}
}
}
else
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_432, 0);
lean_inc(x_506);
lean_dec(x_432);
switch (lean_obj_tag(x_506)) {
case 0:
{
lean_object* x_507; 
lean_dec(x_2);
lean_dec(x_1);
x_507 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; uint8_t x_509; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
x_509 = lean_unbox(x_508);
lean_dec(x_508);
if (x_509 == 0)
{
lean_object* x_510; 
x_510 = lean_box(0);
x_362 = x_378;
x_363 = x_375;
x_364 = x_510;
x_365 = lean_box(0);
goto block_367;
}
else
{
lean_object* x_511; lean_object* x_512; 
x_511 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_512 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_511, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_512;
goto block_373;
}
}
else
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_507, 0);
lean_inc(x_513);
lean_dec_ref(x_507);
x_356 = x_378;
x_357 = x_375;
x_358 = x_513;
x_359 = lean_box(0);
goto block_361;
}
}
case 1:
{
lean_object* x_514; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_514 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
lean_dec_ref(x_514);
if (lean_obj_tag(x_515) == 1)
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_2);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec_ref(x_515);
x_517 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; uint8_t x_519; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
lean_dec_ref(x_517);
x_519 = lean_unbox(x_518);
lean_dec(x_518);
if (x_519 == 0)
{
lean_object* x_520; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_520 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_516, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_520;
goto block_373;
}
else
{
lean_object* x_521; lean_object* x_522; 
x_521 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_522 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_521, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; 
lean_dec_ref(x_522);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_523 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_516, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_523;
goto block_373;
}
else
{
lean_dec(x_516);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_522;
goto block_373;
}
}
}
else
{
lean_object* x_524; 
lean_dec(x_516);
lean_dec(x_1);
x_524 = lean_ctor_get(x_517, 0);
lean_inc(x_524);
lean_dec_ref(x_517);
x_356 = x_378;
x_357 = x_375;
x_358 = x_524;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_525; 
lean_dec(x_515);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_525 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
lean_dec_ref(x_525);
if (lean_obj_tag(x_526) == 1)
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_2);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
lean_dec_ref(x_526);
x_528 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; uint8_t x_530; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
lean_dec_ref(x_528);
x_530 = lean_unbox(x_529);
lean_dec(x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_532 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_527, x_422, x_1, x_531, x_3, x_4, x_5, x_6);
lean_dec(x_527);
x_368 = x_378;
x_369 = x_375;
x_370 = x_532;
goto block_373;
}
else
{
lean_object* x_533; lean_object* x_534; 
x_533 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_534 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_533, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
lean_dec_ref(x_534);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_536 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_527, x_422, x_1, x_535, x_3, x_4, x_5, x_6);
lean_dec(x_527);
x_368 = x_378;
x_369 = x_375;
x_370 = x_536;
goto block_373;
}
else
{
lean_dec(x_527);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_534;
goto block_373;
}
}
}
else
{
lean_object* x_537; 
lean_dec(x_527);
lean_dec(x_1);
x_537 = lean_ctor_get(x_528, 0);
lean_inc(x_537);
lean_dec_ref(x_528);
x_356 = x_378;
x_357 = x_375;
x_358 = x_537;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_538; 
lean_dec(x_526);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_538 = l_Lean_Meta_splitTarget_x3f(x_2, x_37, x_37, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 x_540 = x_538;
} else {
 lean_dec_ref(x_538);
 x_540 = lean_box(0);
}
if (lean_obj_tag(x_539) == 1)
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_540);
lean_dec(x_2);
x_541 = lean_ctor_get(x_539, 0);
lean_inc(x_541);
lean_dec_ref(x_539);
x_542 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; uint8_t x_544; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
lean_dec_ref(x_542);
x_544 = lean_unbox(x_543);
lean_dec(x_543);
if (x_544 == 0)
{
lean_object* x_545; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_545 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_541, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_545;
goto block_373;
}
else
{
lean_object* x_546; lean_object* x_547; 
x_546 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_547 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_546, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; 
lean_dec_ref(x_547);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_548 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_541, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_548;
goto block_373;
}
else
{
lean_dec(x_541);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_547;
goto block_373;
}
}
}
else
{
lean_object* x_549; 
lean_dec(x_541);
lean_dec(x_1);
x_549 = lean_ctor_get(x_542, 0);
lean_inc(x_549);
lean_dec_ref(x_542);
x_356 = x_378;
x_357 = x_375;
x_358 = x_549;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_539);
lean_dec(x_1);
x_550 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
if (lean_is_scalar(x_540)) {
 x_551 = lean_alloc_ctor(1, 1, 0);
} else {
 x_551 = x_540;
 lean_ctor_set_tag(x_551, 1);
}
lean_ctor_set(x_551, 0, x_2);
x_552 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_552, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_553;
goto block_373;
}
}
else
{
lean_object* x_554; 
lean_dec(x_2);
lean_dec(x_1);
x_554 = lean_ctor_get(x_538, 0);
lean_inc(x_554);
lean_dec_ref(x_538);
x_356 = x_378;
x_357 = x_375;
x_358 = x_554;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_555; 
lean_dec(x_2);
lean_dec(x_1);
x_555 = lean_ctor_get(x_525, 0);
lean_inc(x_555);
lean_dec_ref(x_525);
x_356 = x_378;
x_357 = x_375;
x_358 = x_555;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_556; 
lean_dec(x_2);
lean_dec(x_1);
x_556 = lean_ctor_get(x_514, 0);
lean_inc(x_556);
lean_dec_ref(x_514);
x_356 = x_378;
x_357 = x_375;
x_358 = x_556;
x_359 = lean_box(0);
goto block_361;
}
}
default: 
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_2);
x_557 = lean_ctor_get(x_506, 0);
lean_inc(x_557);
lean_dec_ref(x_506);
x_558 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
lean_dec_ref(x_558);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_561 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_557, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_561;
goto block_373;
}
else
{
lean_object* x_562; lean_object* x_563; 
x_562 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_563 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_562, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; 
lean_dec_ref(x_563);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_564 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_557, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_564;
goto block_373;
}
else
{
lean_dec(x_557);
lean_dec(x_1);
x_368 = x_378;
x_369 = x_375;
x_370 = x_563;
goto block_373;
}
}
}
else
{
lean_object* x_565; 
lean_dec(x_557);
lean_dec(x_1);
x_565 = lean_ctor_get(x_558, 0);
lean_inc(x_565);
lean_dec_ref(x_558);
x_356 = x_378;
x_357 = x_375;
x_358 = x_565;
x_359 = lean_box(0);
goto block_361;
}
}
}
}
}
else
{
lean_object* x_566; 
lean_dec(x_2);
lean_dec(x_1);
x_566 = lean_ctor_get(x_431, 0);
lean_inc(x_566);
lean_dec_ref(x_431);
x_356 = x_378;
x_357 = x_375;
x_358 = x_566;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_567; 
lean_dec(x_2);
lean_dec(x_1);
x_567 = lean_ctor_get(x_427, 0);
lean_inc(x_567);
lean_dec_ref(x_427);
x_356 = x_378;
x_357 = x_375;
x_358 = x_567;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_568; 
lean_dec(x_2);
lean_dec(x_1);
x_568 = lean_ctor_get(x_407, 0);
lean_inc(x_568);
lean_dec_ref(x_407);
x_356 = x_378;
x_357 = x_375;
x_358 = x_568;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_569; 
lean_dec(x_2);
lean_dec(x_1);
x_569 = lean_ctor_get(x_396, 0);
lean_inc(x_569);
lean_dec_ref(x_396);
x_356 = x_378;
x_357 = x_375;
x_358 = x_569;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_570; 
lean_dec(x_2);
lean_dec(x_1);
x_570 = lean_ctor_get(x_385, 0);
lean_inc(x_570);
lean_dec_ref(x_385);
x_356 = x_378;
x_357 = x_375;
x_358 = x_570;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_571; 
lean_dec(x_2);
lean_dec(x_1);
x_571 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; uint8_t x_573; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_573 = lean_unbox(x_572);
lean_dec(x_572);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_box(0);
x_575 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_574, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_575;
goto block_373;
}
else
{
lean_object* x_576; lean_object* x_577; 
x_576 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36;
x_577 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_576, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
x_579 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_578, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_579;
goto block_373;
}
else
{
x_368 = x_378;
x_369 = x_375;
x_370 = x_577;
goto block_373;
}
}
}
else
{
lean_object* x_580; 
x_580 = lean_ctor_get(x_571, 0);
lean_inc(x_580);
lean_dec_ref(x_571);
x_356 = x_378;
x_357 = x_375;
x_358 = x_580;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_581; 
lean_dec(x_2);
lean_dec(x_1);
x_581 = lean_ctor_get(x_382, 0);
lean_inc(x_581);
lean_dec_ref(x_382);
x_356 = x_378;
x_357 = x_375;
x_358 = x_581;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_582; 
lean_dec(x_2);
lean_dec(x_1);
x_582 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; uint8_t x_584; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
lean_dec_ref(x_582);
x_584 = lean_unbox(x_583);
lean_dec(x_583);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_box(0);
x_586 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_585, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_586;
goto block_373;
}
else
{
lean_object* x_587; lean_object* x_588; 
x_587 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38;
x_588 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_587, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
lean_dec_ref(x_588);
x_590 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_589, x_3, x_4, x_5, x_6);
x_368 = x_378;
x_369 = x_375;
x_370 = x_590;
goto block_373;
}
else
{
x_368 = x_378;
x_369 = x_375;
x_370 = x_588;
goto block_373;
}
}
}
else
{
lean_object* x_591; 
x_591 = lean_ctor_get(x_582, 0);
lean_inc(x_591);
lean_dec_ref(x_582);
x_356 = x_378;
x_357 = x_375;
x_358 = x_591;
x_359 = lean_box(0);
goto block_361;
}
}
}
else
{
lean_object* x_592; 
lean_dec(x_2);
lean_dec(x_1);
x_592 = lean_ctor_get(x_379, 0);
lean_inc(x_592);
lean_dec_ref(x_379);
x_356 = x_378;
x_357 = x_375;
x_358 = x_592;
x_359 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_io_get_num_heartbeats();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_594 = l_Lean_Elab_Eqns_tryURefl(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; uint8_t x_596; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
lean_dec_ref(x_594);
x_596 = lean_unbox(x_595);
lean_dec(x_595);
if (x_596 == 0)
{
lean_object* x_597; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_597 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; uint8_t x_599; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
lean_dec_ref(x_597);
x_599 = lean_unbox(x_598);
if (x_599 == 0)
{
lean_object* x_600; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_600 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
lean_dec_ref(x_600);
if (lean_obj_tag(x_601) == 1)
{
lean_object* x_602; lean_object* x_603; 
lean_dec(x_598);
lean_dec(x_2);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
lean_dec_ref(x_601);
x_603 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; uint8_t x_605; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
lean_dec_ref(x_603);
x_605 = lean_unbox(x_604);
lean_dec(x_604);
if (x_605 == 0)
{
lean_object* x_606; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_606 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_602, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_606;
goto block_338;
}
else
{
lean_object* x_607; lean_object* x_608; 
x_607 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
x_608 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_607, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; 
lean_dec_ref(x_608);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_609 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_602, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_609;
goto block_338;
}
else
{
lean_dec(x_602);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_608;
goto block_338;
}
}
}
else
{
lean_object* x_610; 
lean_dec(x_602);
lean_dec(x_1);
x_610 = lean_ctor_get(x_603, 0);
lean_inc(x_610);
lean_dec_ref(x_603);
x_327 = x_593;
x_328 = x_375;
x_329 = x_610;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_611; 
lean_dec(x_601);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_611 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
lean_dec_ref(x_611);
if (lean_obj_tag(x_612) == 1)
{
lean_object* x_613; lean_object* x_614; 
lean_dec(x_598);
lean_dec(x_2);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
lean_dec_ref(x_612);
x_614 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; uint8_t x_616; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
lean_dec_ref(x_614);
x_616 = lean_unbox(x_615);
lean_dec(x_615);
if (x_616 == 0)
{
lean_object* x_617; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_617 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_613, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_617;
goto block_338;
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
x_619 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_618, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
lean_dec_ref(x_619);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_620 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_613, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_620;
goto block_338;
}
else
{
lean_dec(x_613);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_619;
goto block_338;
}
}
}
else
{
lean_object* x_621; 
lean_dec(x_613);
lean_dec(x_1);
x_621 = lean_ctor_get(x_614, 0);
lean_inc(x_621);
lean_dec_ref(x_614);
x_327 = x_593;
x_328 = x_375;
x_329 = x_621;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_622; 
lean_dec(x_612);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_622 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_377, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
lean_dec_ref(x_622);
if (lean_obj_tag(x_623) == 1)
{
lean_object* x_624; lean_object* x_625; 
lean_dec(x_598);
lean_dec(x_2);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
lean_dec_ref(x_623);
x_625 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; uint8_t x_627; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
lean_dec_ref(x_625);
x_627 = lean_unbox(x_626);
lean_dec(x_626);
if (x_627 == 0)
{
lean_object* x_628; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_628 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_624, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_628;
goto block_338;
}
else
{
lean_object* x_629; lean_object* x_630; 
x_629 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
x_630 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_629, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; 
lean_dec_ref(x_630);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_631 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_624, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_631;
goto block_338;
}
else
{
lean_dec(x_624);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_630;
goto block_338;
}
}
}
else
{
lean_object* x_632; 
lean_dec(x_624);
lean_dec(x_1);
x_632 = lean_ctor_get(x_625, 0);
lean_inc(x_632);
lean_dec_ref(x_625);
x_327 = x_593;
x_328 = x_375;
x_329 = x_632;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_633; lean_object* x_634; uint8_t x_635; lean_object* x_636; uint8_t x_637; uint8_t x_638; uint8_t x_639; uint8_t x_640; uint8_t x_641; uint8_t x_642; uint8_t x_643; uint8_t x_644; uint8_t x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_623);
x_633 = lean_unsigned_to_nat(100000u);
x_634 = lean_unsigned_to_nat(2u);
x_635 = 0;
x_636 = lean_alloc_ctor(0, 2, 28);
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
x_637 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2, x_637);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 1, x_377);
x_638 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 2, x_638);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 3, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 4, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 5, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 6, x_635);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 7, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 8, x_377);
x_639 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 9, x_639);
x_640 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 10, x_640);
x_641 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 11, x_641);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 12, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 13, x_377);
x_642 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 14, x_642);
x_643 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 15, x_643);
x_644 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 16, x_644);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 17, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 18, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 19, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 20, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 21, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 22, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 23, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 24, x_377);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 25, x_377);
x_645 = lean_unbox(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 26, x_645);
x_646 = lean_unbox(x_598);
lean_dec(x_598);
lean_ctor_set_uint8(x_636, sizeof(void*)*2 + 27, x_646);
x_647 = lean_unsigned_to_nat(0u);
x_648 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11;
x_649 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13;
x_650 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
x_651 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
lean_ctor_set_uint8(x_651, sizeof(void*)*2, x_377);
x_652 = l_Lean_Meta_Simp_mkContext___redArg(x_636, x_648, x_651, x_3, x_6);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
lean_dec_ref(x_652);
x_654 = lean_box(0);
x_655 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_656 = l_Lean_Meta_simpTargetStar(x_2, x_653, x_648, x_654, x_655, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; uint8_t x_658; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec_ref(x_656);
x_658 = !lean_is_exclusive(x_657);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_657, 0);
x_660 = lean_ctor_get(x_657, 1);
lean_dec(x_660);
switch (lean_obj_tag(x_659)) {
case 0:
{
lean_object* x_661; 
lean_free_object(x_657);
lean_dec(x_2);
lean_dec(x_1);
x_661 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
lean_dec_ref(x_661);
x_663 = lean_unbox(x_662);
lean_dec(x_662);
if (x_663 == 0)
{
lean_object* x_664; 
x_664 = lean_box(0);
x_321 = x_593;
x_322 = x_375;
x_323 = x_664;
x_324 = lean_box(0);
goto block_326;
}
else
{
lean_object* x_665; lean_object* x_666; 
x_665 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_666 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_665, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_666;
goto block_338;
}
}
else
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_661, 0);
lean_inc(x_667);
lean_dec_ref(x_661);
x_327 = x_593;
x_328 = x_375;
x_329 = x_667;
x_330 = lean_box(0);
goto block_332;
}
}
case 1:
{
lean_object* x_668; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_668 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
lean_dec_ref(x_668);
if (lean_obj_tag(x_669) == 1)
{
lean_object* x_670; lean_object* x_671; 
lean_free_object(x_657);
lean_dec(x_2);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
lean_dec_ref(x_669);
x_671 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; uint8_t x_673; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
lean_dec_ref(x_671);
x_673 = lean_unbox(x_672);
lean_dec(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_674 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_670, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_674;
goto block_338;
}
else
{
lean_object* x_675; lean_object* x_676; 
x_675 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_676 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_675, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; 
lean_dec_ref(x_676);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_677 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_670, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_677;
goto block_338;
}
else
{
lean_dec(x_670);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_676;
goto block_338;
}
}
}
else
{
lean_object* x_678; 
lean_dec(x_670);
lean_dec(x_1);
x_678 = lean_ctor_get(x_671, 0);
lean_inc(x_678);
lean_dec_ref(x_671);
x_327 = x_593;
x_328 = x_375;
x_329 = x_678;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_679; 
lean_dec(x_669);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_679 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec_ref(x_679);
if (lean_obj_tag(x_680) == 1)
{
lean_object* x_681; lean_object* x_682; 
lean_free_object(x_657);
lean_dec(x_2);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec_ref(x_680);
x_682 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; uint8_t x_684; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
lean_dec_ref(x_682);
x_684 = lean_unbox(x_683);
lean_dec(x_683);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; 
x_685 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_686 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_681, x_647, x_1, x_685, x_3, x_4, x_5, x_6);
lean_dec(x_681);
x_333 = x_593;
x_334 = x_375;
x_335 = x_686;
goto block_338;
}
else
{
lean_object* x_687; lean_object* x_688; 
x_687 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_688 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_687, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
lean_dec_ref(x_688);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_690 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_681, x_647, x_1, x_689, x_3, x_4, x_5, x_6);
lean_dec(x_681);
x_333 = x_593;
x_334 = x_375;
x_335 = x_690;
goto block_338;
}
else
{
lean_dec(x_681);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_688;
goto block_338;
}
}
}
else
{
lean_object* x_691; 
lean_dec(x_681);
lean_dec(x_1);
x_691 = lean_ctor_get(x_682, 0);
lean_inc(x_691);
lean_dec_ref(x_682);
x_327 = x_593;
x_328 = x_375;
x_329 = x_691;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_692; 
lean_dec(x_680);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_692 = l_Lean_Meta_splitTarget_x3f(x_2, x_377, x_377, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_692) == 0)
{
uint8_t x_693; 
x_693 = !lean_is_exclusive(x_692);
if (x_693 == 0)
{
lean_object* x_694; 
x_694 = lean_ctor_get(x_692, 0);
if (lean_obj_tag(x_694) == 1)
{
lean_object* x_695; lean_object* x_696; 
lean_free_object(x_692);
lean_free_object(x_657);
lean_dec(x_2);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
lean_dec_ref(x_694);
x_696 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; uint8_t x_698; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
lean_dec_ref(x_696);
x_698 = lean_unbox(x_697);
lean_dec(x_697);
if (x_698 == 0)
{
lean_object* x_699; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_699 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_695, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_699;
goto block_338;
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_701 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_700, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; 
lean_dec_ref(x_701);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_702 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_695, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_702;
goto block_338;
}
else
{
lean_dec(x_695);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_701;
goto block_338;
}
}
}
else
{
lean_object* x_703; 
lean_dec(x_695);
lean_dec(x_1);
x_703 = lean_ctor_get(x_696, 0);
lean_inc(x_703);
lean_dec_ref(x_696);
x_327 = x_593;
x_328 = x_375;
x_329 = x_703;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_694);
lean_dec(x_1);
x_704 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
lean_ctor_set_tag(x_692, 1);
lean_ctor_set(x_692, 0, x_2);
lean_ctor_set_tag(x_657, 7);
lean_ctor_set(x_657, 1, x_692);
lean_ctor_set(x_657, 0, x_704);
x_705 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_657, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_705;
goto block_338;
}
}
else
{
lean_object* x_706; 
x_706 = lean_ctor_get(x_692, 0);
lean_inc(x_706);
lean_dec(x_692);
if (lean_obj_tag(x_706) == 1)
{
lean_object* x_707; lean_object* x_708; 
lean_free_object(x_657);
lean_dec(x_2);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
lean_dec_ref(x_706);
x_708 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; uint8_t x_710; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec_ref(x_708);
x_710 = lean_unbox(x_709);
lean_dec(x_709);
if (x_710 == 0)
{
lean_object* x_711; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_711 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_707, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_711;
goto block_338;
}
else
{
lean_object* x_712; lean_object* x_713; 
x_712 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_713 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_712, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; 
lean_dec_ref(x_713);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_714 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_707, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_714;
goto block_338;
}
else
{
lean_dec(x_707);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_713;
goto block_338;
}
}
}
else
{
lean_object* x_715; 
lean_dec(x_707);
lean_dec(x_1);
x_715 = lean_ctor_get(x_708, 0);
lean_inc(x_715);
lean_dec_ref(x_708);
x_327 = x_593;
x_328 = x_375;
x_329 = x_715;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_706);
lean_dec(x_1);
x_716 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
x_717 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_717, 0, x_2);
lean_ctor_set_tag(x_657, 7);
lean_ctor_set(x_657, 1, x_717);
lean_ctor_set(x_657, 0, x_716);
x_718 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_657, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_718;
goto block_338;
}
}
}
else
{
lean_object* x_719; 
lean_free_object(x_657);
lean_dec(x_2);
lean_dec(x_1);
x_719 = lean_ctor_get(x_692, 0);
lean_inc(x_719);
lean_dec_ref(x_692);
x_327 = x_593;
x_328 = x_375;
x_329 = x_719;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_720; 
lean_free_object(x_657);
lean_dec(x_2);
lean_dec(x_1);
x_720 = lean_ctor_get(x_679, 0);
lean_inc(x_720);
lean_dec_ref(x_679);
x_327 = x_593;
x_328 = x_375;
x_329 = x_720;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_721; 
lean_free_object(x_657);
lean_dec(x_2);
lean_dec(x_1);
x_721 = lean_ctor_get(x_668, 0);
lean_inc(x_721);
lean_dec_ref(x_668);
x_327 = x_593;
x_328 = x_375;
x_329 = x_721;
x_330 = lean_box(0);
goto block_332;
}
}
default: 
{
lean_object* x_722; lean_object* x_723; 
lean_free_object(x_657);
lean_dec(x_2);
x_722 = lean_ctor_get(x_659, 0);
lean_inc(x_722);
lean_dec_ref(x_659);
x_723 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; uint8_t x_725; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
lean_dec_ref(x_723);
x_725 = lean_unbox(x_724);
lean_dec(x_724);
if (x_725 == 0)
{
lean_object* x_726; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_726 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_722, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_726;
goto block_338;
}
else
{
lean_object* x_727; lean_object* x_728; 
x_727 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_728 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_727, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
lean_dec_ref(x_728);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_729 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_722, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_729;
goto block_338;
}
else
{
lean_dec(x_722);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_728;
goto block_338;
}
}
}
else
{
lean_object* x_730; 
lean_dec(x_722);
lean_dec(x_1);
x_730 = lean_ctor_get(x_723, 0);
lean_inc(x_730);
lean_dec_ref(x_723);
x_327 = x_593;
x_328 = x_375;
x_329 = x_730;
x_330 = lean_box(0);
goto block_332;
}
}
}
}
else
{
lean_object* x_731; 
x_731 = lean_ctor_get(x_657, 0);
lean_inc(x_731);
lean_dec(x_657);
switch (lean_obj_tag(x_731)) {
case 0:
{
lean_object* x_732; 
lean_dec(x_2);
lean_dec(x_1);
x_732 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; uint8_t x_734; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
lean_dec_ref(x_732);
x_734 = lean_unbox(x_733);
lean_dec(x_733);
if (x_734 == 0)
{
lean_object* x_735; 
x_735 = lean_box(0);
x_321 = x_593;
x_322 = x_375;
x_323 = x_735;
x_324 = lean_box(0);
goto block_326;
}
else
{
lean_object* x_736; lean_object* x_737; 
x_736 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_737 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_736, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_737;
goto block_338;
}
}
else
{
lean_object* x_738; 
x_738 = lean_ctor_get(x_732, 0);
lean_inc(x_738);
lean_dec_ref(x_732);
x_327 = x_593;
x_328 = x_375;
x_329 = x_738;
x_330 = lean_box(0);
goto block_332;
}
}
case 1:
{
lean_object* x_739; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_739 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
lean_dec_ref(x_739);
if (lean_obj_tag(x_740) == 1)
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_2);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
lean_dec_ref(x_740);
x_742 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; uint8_t x_744; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
lean_dec_ref(x_742);
x_744 = lean_unbox(x_743);
lean_dec(x_743);
if (x_744 == 0)
{
lean_object* x_745; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_745 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_741, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_745;
goto block_338;
}
else
{
lean_object* x_746; lean_object* x_747; 
x_746 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_747 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_746, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; 
lean_dec_ref(x_747);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_748 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_741, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_748;
goto block_338;
}
else
{
lean_dec(x_741);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_747;
goto block_338;
}
}
}
else
{
lean_object* x_749; 
lean_dec(x_741);
lean_dec(x_1);
x_749 = lean_ctor_get(x_742, 0);
lean_inc(x_749);
lean_dec_ref(x_742);
x_327 = x_593;
x_328 = x_375;
x_329 = x_749;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_750; 
lean_dec(x_740);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_750 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
lean_dec_ref(x_750);
if (lean_obj_tag(x_751) == 1)
{
lean_object* x_752; lean_object* x_753; 
lean_dec(x_2);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
lean_dec_ref(x_751);
x_753 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; uint8_t x_755; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
lean_dec_ref(x_753);
x_755 = lean_unbox(x_754);
lean_dec(x_754);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; 
x_756 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_757 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_752, x_647, x_1, x_756, x_3, x_4, x_5, x_6);
lean_dec(x_752);
x_333 = x_593;
x_334 = x_375;
x_335 = x_757;
goto block_338;
}
else
{
lean_object* x_758; lean_object* x_759; 
x_758 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_759 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_758, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
lean_dec_ref(x_759);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_761 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_752, x_647, x_1, x_760, x_3, x_4, x_5, x_6);
lean_dec(x_752);
x_333 = x_593;
x_334 = x_375;
x_335 = x_761;
goto block_338;
}
else
{
lean_dec(x_752);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_759;
goto block_338;
}
}
}
else
{
lean_object* x_762; 
lean_dec(x_752);
lean_dec(x_1);
x_762 = lean_ctor_get(x_753, 0);
lean_inc(x_762);
lean_dec_ref(x_753);
x_327 = x_593;
x_328 = x_375;
x_329 = x_762;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_763; 
lean_dec(x_751);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_763 = l_Lean_Meta_splitTarget_x3f(x_2, x_377, x_377, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 x_765 = x_763;
} else {
 lean_dec_ref(x_763);
 x_765 = lean_box(0);
}
if (lean_obj_tag(x_764) == 1)
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_765);
lean_dec(x_2);
x_766 = lean_ctor_get(x_764, 0);
lean_inc(x_766);
lean_dec_ref(x_764);
x_767 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; uint8_t x_769; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
lean_dec_ref(x_767);
x_769 = lean_unbox(x_768);
lean_dec(x_768);
if (x_769 == 0)
{
lean_object* x_770; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_770 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_766, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_770;
goto block_338;
}
else
{
lean_object* x_771; lean_object* x_772; 
x_771 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_772 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_771, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; 
lean_dec_ref(x_772);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_773 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_766, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_773;
goto block_338;
}
else
{
lean_dec(x_766);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_772;
goto block_338;
}
}
}
else
{
lean_object* x_774; 
lean_dec(x_766);
lean_dec(x_1);
x_774 = lean_ctor_get(x_767, 0);
lean_inc(x_774);
lean_dec_ref(x_767);
x_327 = x_593;
x_328 = x_375;
x_329 = x_774;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_764);
lean_dec(x_1);
x_775 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
if (lean_is_scalar(x_765)) {
 x_776 = lean_alloc_ctor(1, 1, 0);
} else {
 x_776 = x_765;
 lean_ctor_set_tag(x_776, 1);
}
lean_ctor_set(x_776, 0, x_2);
x_777 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
x_778 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_777, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_778;
goto block_338;
}
}
else
{
lean_object* x_779; 
lean_dec(x_2);
lean_dec(x_1);
x_779 = lean_ctor_get(x_763, 0);
lean_inc(x_779);
lean_dec_ref(x_763);
x_327 = x_593;
x_328 = x_375;
x_329 = x_779;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_780; 
lean_dec(x_2);
lean_dec(x_1);
x_780 = lean_ctor_get(x_750, 0);
lean_inc(x_780);
lean_dec_ref(x_750);
x_327 = x_593;
x_328 = x_375;
x_329 = x_780;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_781; 
lean_dec(x_2);
lean_dec(x_1);
x_781 = lean_ctor_get(x_739, 0);
lean_inc(x_781);
lean_dec_ref(x_739);
x_327 = x_593;
x_328 = x_375;
x_329 = x_781;
x_330 = lean_box(0);
goto block_332;
}
}
default: 
{
lean_object* x_782; lean_object* x_783; 
lean_dec(x_2);
x_782 = lean_ctor_get(x_731, 0);
lean_inc(x_782);
lean_dec_ref(x_731);
x_783 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; uint8_t x_785; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
lean_dec_ref(x_783);
x_785 = lean_unbox(x_784);
lean_dec(x_784);
if (x_785 == 0)
{
lean_object* x_786; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_786 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_782, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_786;
goto block_338;
}
else
{
lean_object* x_787; lean_object* x_788; 
x_787 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_788 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_787, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; 
lean_dec_ref(x_788);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_789 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_782, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_789;
goto block_338;
}
else
{
lean_dec(x_782);
lean_dec(x_1);
x_333 = x_593;
x_334 = x_375;
x_335 = x_788;
goto block_338;
}
}
}
else
{
lean_object* x_790; 
lean_dec(x_782);
lean_dec(x_1);
x_790 = lean_ctor_get(x_783, 0);
lean_inc(x_790);
lean_dec_ref(x_783);
x_327 = x_593;
x_328 = x_375;
x_329 = x_790;
x_330 = lean_box(0);
goto block_332;
}
}
}
}
}
else
{
lean_object* x_791; 
lean_dec(x_2);
lean_dec(x_1);
x_791 = lean_ctor_get(x_656, 0);
lean_inc(x_791);
lean_dec_ref(x_656);
x_327 = x_593;
x_328 = x_375;
x_329 = x_791;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_792; 
lean_dec(x_2);
lean_dec(x_1);
x_792 = lean_ctor_get(x_652, 0);
lean_inc(x_792);
lean_dec_ref(x_652);
x_327 = x_593;
x_328 = x_375;
x_329 = x_792;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_793; 
lean_dec(x_598);
lean_dec(x_2);
lean_dec(x_1);
x_793 = lean_ctor_get(x_622, 0);
lean_inc(x_793);
lean_dec_ref(x_622);
x_327 = x_593;
x_328 = x_375;
x_329 = x_793;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_794; 
lean_dec(x_598);
lean_dec(x_2);
lean_dec(x_1);
x_794 = lean_ctor_get(x_611, 0);
lean_inc(x_794);
lean_dec_ref(x_611);
x_327 = x_593;
x_328 = x_375;
x_329 = x_794;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_795; 
lean_dec(x_598);
lean_dec(x_2);
lean_dec(x_1);
x_795 = lean_ctor_get(x_600, 0);
lean_inc(x_795);
lean_dec_ref(x_600);
x_327 = x_593;
x_328 = x_375;
x_329 = x_795;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_796; 
lean_dec(x_598);
lean_dec(x_2);
lean_dec(x_1);
x_796 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; uint8_t x_798; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
lean_dec_ref(x_796);
x_798 = lean_unbox(x_797);
lean_dec(x_797);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; 
x_799 = lean_box(0);
x_800 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_799, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_800;
goto block_338;
}
else
{
lean_object* x_801; lean_object* x_802; 
x_801 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36;
x_802 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_801, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
lean_dec_ref(x_802);
x_804 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_803, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_804;
goto block_338;
}
else
{
x_333 = x_593;
x_334 = x_375;
x_335 = x_802;
goto block_338;
}
}
}
else
{
lean_object* x_805; 
x_805 = lean_ctor_get(x_796, 0);
lean_inc(x_805);
lean_dec_ref(x_796);
x_327 = x_593;
x_328 = x_375;
x_329 = x_805;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_806; 
lean_dec(x_2);
lean_dec(x_1);
x_806 = lean_ctor_get(x_597, 0);
lean_inc(x_806);
lean_dec_ref(x_597);
x_327 = x_593;
x_328 = x_375;
x_329 = x_806;
x_330 = lean_box(0);
goto block_332;
}
}
else
{
lean_object* x_807; 
lean_dec(x_2);
lean_dec(x_1);
x_807 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_5);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; uint8_t x_809; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
lean_dec_ref(x_807);
x_809 = lean_unbox(x_808);
lean_dec(x_808);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_box(0);
x_811 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_810, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_811;
goto block_338;
}
else
{
lean_object* x_812; lean_object* x_813; 
x_812 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38;
x_813 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_812, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
lean_dec_ref(x_813);
x_815 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(x_814, x_3, x_4, x_5, x_6);
x_333 = x_593;
x_334 = x_375;
x_335 = x_815;
goto block_338;
}
else
{
x_333 = x_593;
x_334 = x_375;
x_335 = x_813;
goto block_338;
}
}
}
else
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_807, 0);
lean_inc(x_816);
lean_dec_ref(x_807);
x_327 = x_593;
x_328 = x_375;
x_329 = x_816;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
lean_object* x_817; 
lean_dec(x_2);
lean_dec(x_1);
x_817 = lean_ctor_get(x_594, 0);
lean_inc(x_817);
lean_dec_ref(x_594);
x_327 = x_593;
x_328 = x_375;
x_329 = x_817;
x_330 = lean_box(0);
goto block_332;
}
}
}
else
{
uint8_t x_818; 
lean_dec_ref(x_305);
lean_dec(x_304);
lean_dec_ref(x_36);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_818 = !lean_is_exclusive(x_374);
if (x_818 == 0)
{
return x_374;
}
else
{
lean_object* x_819; lean_object* x_820; 
x_819 = lean_ctor_get(x_374, 0);
lean_inc(x_819);
lean_dec(x_374);
x_820 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_820, 0, x_819);
return x_820;
}
}
}
}
else
{
uint8_t x_825; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_825 = !lean_is_exclusive(x_303);
if (x_825 == 0)
{
return x_303;
}
else
{
lean_object* x_826; lean_object* x_827; 
x_826 = lean_ctor_get(x_303, 0);
lean_inc(x_826);
lean_dec(x_303);
x_827 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_827, 0, x_826);
return x_827;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_35:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_array_get_size(x_16);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_17, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_23, x_23);
if (x_27 == 0)
{
if (x_25 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_23);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(x_1, x_16, x_29, x_30, x_24, x_18, x_19, x_20, x_21);
lean_dec_ref(x_16);
return x_31;
}
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_23);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(x_1, x_16, x_32, x_33, x_24, x_18, x_19, x_20, x_21);
lean_dec_ref(x_16);
return x_34;
}
}
}
block_302:
{
lean_object* x_44; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_44 = l_Lean_Elab_Eqns_tryURefl(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_47 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_50 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
x_2 = x_52;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
x_58 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_57, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_2 = x_52;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_58;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_51);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_63 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_48);
lean_dec(x_2);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
x_2 = x_65;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
x_71 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_70, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_2 = x_65;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_65);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_71;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_65);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; lean_object* x_77; 
lean_dec(x_64);
x_76 = 1;
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_77 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_76, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
if (lean_obj_tag(x_78) == 1)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_48);
lean_dec(x_2);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
x_2 = x_79;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
x_85 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_84, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_2 = x_79;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_79);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_85;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_80);
if (x_87 == 0)
{
return x_80;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
lean_dec(x_80);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_78);
x_90 = lean_unsigned_to_nat(100000u);
x_91 = lean_unsigned_to_nat(2u);
x_92 = 0;
x_93 = lean_alloc_ctor(0, 2, 28);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_94);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 1, x_76);
x_95 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 2, x_95);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 3, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 4, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 5, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 6, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 7, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 8, x_76);
x_96 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 9, x_96);
x_97 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 10, x_97);
x_98 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 11, x_98);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 12, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 13, x_76);
x_99 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 14, x_99);
x_100 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 15, x_100);
x_101 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 16, x_101);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 17, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 18, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 19, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 20, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 21, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 22, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 23, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 24, x_76);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 25, x_76);
x_102 = lean_unbox(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 26, x_102);
x_103 = lean_unbox(x_48);
lean_dec(x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 27, x_103);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11;
x_106 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16;
x_107 = l_Lean_Meta_Simp_mkContext___redArg(x_93, x_105, x_106, x_39, x_42);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_box(0);
x_110 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22;
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_111 = l_Lean_Meta_simpTargetStar(x_2, x_108, x_105, x_109, x_110, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
lean_dec(x_115);
switch (lean_obj_tag(x_114)) {
case 0:
{
lean_object* x_116; 
lean_free_object(x_112);
lean_dec(x_2);
lean_dec(x_1);
x_116 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_120 = lean_box(0);
lean_ctor_set(x_116, 0, x_120);
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_free_object(x_116);
x_121 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_122 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_121, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_122;
}
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_128 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_127, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_129 = !lean_is_exclusive(x_116);
if (x_129 == 0)
{
return x_116;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_116, 0);
lean_inc(x_130);
lean_dec(x_116);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
case 1:
{
lean_object* x_132; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_1);
lean_inc(x_2);
x_132 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; 
lean_free_object(x_112);
lean_dec(x_2);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
x_2 = x_134;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_140 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_139, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_140) == 0)
{
lean_dec_ref(x_140);
x_2 = x_134;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_134);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_140;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_134);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_135);
if (x_142 == 0)
{
return x_135;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
lean_dec(x_135);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_133);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_145 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
if (lean_obj_tag(x_146) == 1)
{
lean_object* x_147; lean_object* x_148; 
lean_free_object(x_112);
lean_dec(x_2);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
if (x_150 == 0)
{
x_16 = x_147;
x_17 = x_104;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_152 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_151, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_152) == 0)
{
lean_dec_ref(x_152);
x_16 = x_147;
x_17 = x_104;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = lean_box(0);
goto block_35;
}
else
{
lean_dec(x_147);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_147);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_148);
if (x_153 == 0)
{
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_146);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_156 = l_Lean_Meta_splitTarget_x3f(x_2, x_76, x_76, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
if (lean_obj_tag(x_157) == 1)
{
lean_object* x_158; lean_object* x_159; 
lean_free_object(x_112);
lean_dec(x_2);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_158, x_39, x_40, x_41, x_42);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_164 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_163, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec_ref(x_164);
x_165 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_158, x_39, x_40, x_41, x_42);
return x_165;
}
else
{
lean_dec(x_158);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_164;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_158);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_159);
if (x_166 == 0)
{
return x_159;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
lean_dec(x_159);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_157);
lean_dec(x_1);
x_169 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_2);
lean_ctor_set_tag(x_112, 7);
lean_ctor_set(x_112, 1, x_170);
lean_ctor_set(x_112, 0, x_169);
x_171 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_112, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_171;
}
}
else
{
uint8_t x_172; 
lean_free_object(x_112);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_156);
if (x_172 == 0)
{
return x_156;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_156, 0);
lean_inc(x_173);
lean_dec(x_156);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_free_object(x_112);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_145);
if (x_175 == 0)
{
return x_145;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_145, 0);
lean_inc(x_176);
lean_dec(x_145);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
}
else
{
uint8_t x_178; 
lean_free_object(x_112);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_132);
if (x_178 == 0)
{
return x_132;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_132, 0);
lean_inc(x_179);
lean_dec(x_132);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
}
default: 
{
lean_object* x_181; lean_object* x_182; 
lean_free_object(x_112);
lean_dec(x_2);
x_181 = lean_ctor_get(x_114, 0);
lean_inc(x_181);
lean_dec_ref(x_114);
x_182 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
x_2 = x_181;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_187 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_186, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_187) == 0)
{
lean_dec_ref(x_187);
x_2 = x_181;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_181);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_187;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_181);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
return x_182;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
lean_dec(x_182);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
}
}
else
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_112, 0);
lean_inc(x_192);
lean_dec(x_112);
switch (lean_obj_tag(x_192)) {
case 0:
{
lean_object* x_193; 
lean_dec(x_2);
lean_dec(x_1);
x_193 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = lean_unbox(x_194);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_197 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_195);
x_199 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
x_200 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_199, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_202 = x_193;
} else {
 lean_dec_ref(x_193);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
}
case 1:
{
lean_object* x_204; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_1);
lean_inc(x_2);
x_204 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(x_2, x_1, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
if (lean_obj_tag(x_205) == 1)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_2);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
x_2 = x_206;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26;
x_212 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_211, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_212);
x_2 = x_206;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_206);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_212;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_206);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_215 = x_207;
} else {
 lean_dec_ref(x_207);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
else
{
lean_object* x_217; 
lean_dec(x_205);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_217 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_2);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
x_16 = x_219;
x_17 = x_104;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28;
x_224 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_223, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_224) == 0)
{
lean_dec_ref(x_224);
x_16 = x_219;
x_17 = x_104;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = lean_box(0);
goto block_35;
}
else
{
lean_dec(x_219);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_219);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_226 = x_220;
} else {
 lean_dec_ref(x_220);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
return x_227;
}
}
else
{
lean_object* x_228; 
lean_dec(x_218);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_2);
x_228 = l_Lean_Meta_splitTarget_x3f(x_2, x_76, x_76, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
if (lean_obj_tag(x_229) == 1)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_2);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec_ref(x_229);
x_231 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_230, x_39, x_40, x_41, x_42);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30;
x_236 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_235, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
lean_dec_ref(x_236);
x_237 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_230, x_39, x_40, x_41, x_42);
return x_237;
}
else
{
lean_dec(x_230);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_236;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_230);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_238 = lean_ctor_get(x_231, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_239 = x_231;
} else {
 lean_dec_ref(x_231);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_229);
lean_dec(x_1);
x_241 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32;
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_2);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_243, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_228, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_246 = x_228;
} else {
 lean_dec_ref(x_228);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_217, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_249 = x_217;
} else {
 lean_dec_ref(x_217);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 1, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_ctor_get(x_204, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_252 = x_204;
} else {
 lean_dec_ref(x_204);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
}
default: 
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_2);
x_254 = lean_ctor_get(x_192, 0);
lean_inc(x_254);
lean_dec_ref(x_192);
x_255 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
x_2 = x_254;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34;
x_260 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_259, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_260) == 0)
{
lean_dec_ref(x_260);
x_2 = x_254;
x_3 = x_39;
x_4 = x_40;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
else
{
lean_dec(x_254);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
return x_260;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_254);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_1);
x_262 = lean_ctor_get(x_255, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_263 = x_255;
} else {
 lean_dec_ref(x_255);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_111);
if (x_265 == 0)
{
return x_111;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_111, 0);
lean_inc(x_266);
lean_dec(x_111);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_107);
if (x_268 == 0)
{
return x_107;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_107, 0);
lean_inc(x_269);
lean_dec(x_107);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
return x_270;
}
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_77);
if (x_271 == 0)
{
return x_77;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_77, 0);
lean_inc(x_272);
lean_dec(x_77);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_63);
if (x_274 == 0)
{
return x_63;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_63, 0);
lean_inc(x_275);
lean_dec(x_63);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_50);
if (x_277 == 0)
{
return x_50;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_50, 0);
lean_inc(x_278);
lean_dec(x_50);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; 
lean_dec(x_48);
lean_dec(x_2);
lean_dec(x_1);
x_280 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36;
x_284 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_283, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
if (lean_obj_tag(x_284) == 0)
{
lean_dec_ref(x_284);
x_8 = lean_box(0);
goto block_11;
}
else
{
return x_284;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_285 = !lean_is_exclusive(x_280);
if (x_285 == 0)
{
return x_280;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_280, 0);
lean_inc(x_286);
lean_dec(x_280);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_288 = !lean_is_exclusive(x_47);
if (x_288 == 0)
{
return x_47;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_47, 0);
lean_inc(x_289);
lean_dec(x_47);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; 
lean_dec(x_2);
lean_dec(x_1);
x_291 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_38, x_41);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38;
x_295 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_38, x_294, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
if (lean_obj_tag(x_295) == 0)
{
lean_dec_ref(x_295);
x_12 = lean_box(0);
goto block_15;
}
else
{
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_296 = !lean_is_exclusive(x_291);
if (x_296 == 0)
{
return x_291;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_291, 0);
lean_inc(x_297);
lean_dec(x_291);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_44);
if (x_299 == 0)
{
return x_44;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_44, 0);
lean_inc(x_300);
lean_dec(x_44);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_300);
return x_301;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Environment_contains(x_6, x_1, x_2);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(x_1, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(x_1, x_2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_mkCongrArg(x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Expr_app___override(x_1, x_3);
x_13 = l_Lean_MVarId_replaceTargetEq(x_4, x_12, x_11, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_111; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = l_Lean_Expr_getAppFn(x_13);
x_17 = l_Lean_Expr_constName_x21(x_16);
x_18 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = 1;
lean_inc(x_19);
x_21 = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(x_19, x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Expr_getAppNumArgs(x_13);
x_25 = l_Lean_Expr_constLevels_x21(x_16);
lean_dec_ref(x_16);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0;
lean_inc(x_24);
x_27 = lean_mk_array(x_24, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_24, x_28);
lean_dec(x_24);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_27, x_29);
x_111 = lean_unbox(x_22);
lean_dec(x_22);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec_ref(x_30);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_2);
x_112 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12;
x_113 = l_Lean_MessageData_ofName(x_19);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_1);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_118, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
return x_119;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = lean_box(0);
goto block_110;
}
block_61:
{
lean_object* x_40; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_33);
x_40 = lean_infer_type(x_33, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
x_43 = l_Lean_MVarId_define(x_1, x_42, x_41, x_33, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
x_45 = l_Lean_Meta_intro1Core(x_44, x_31, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_appFn_x21(x_34);
lean_dec_ref(x_34);
x_50 = l_Lean_mkFVar(x_47);
x_51 = l_Lean_Expr_app___override(x_49, x_50);
x_52 = l_Lean_mkAppN(x_32, x_30);
lean_dec_ref(x_30);
lean_inc(x_48);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(x_53, 0, x_14);
lean_closure_set(x_53, 1, x_52);
lean_closure_set(x_53, 2, x_51);
lean_closure_set(x_53, 3, x_48);
x_54 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_48, x_53, x_35, x_36, x_37, x_38);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_14);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_14);
return x_43;
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_14);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
block_110:
{
lean_object* x_67; lean_object* x_68; 
lean_inc(x_19);
x_67 = l_Lean_mkConst(x_19, x_25);
lean_inc(x_65);
lean_inc_ref(x_64);
lean_inc(x_63);
lean_inc_ref(x_62);
lean_inc_ref(x_67);
x_68 = lean_infer_type(x_67, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_65);
lean_inc_ref(x_64);
lean_inc(x_63);
lean_inc_ref(x_62);
x_70 = l_Lean_Meta_instantiateForall(x_69, x_30, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
x_73 = lean_unsigned_to_nat(3u);
x_74 = l_Lean_Expr_isAppOfArity(x_71, x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
lean_dec_ref(x_67);
lean_dec_ref(x_30);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_2);
x_75 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4;
x_76 = l_Lean_MessageData_ofName(x_19);
if (lean_is_scalar(x_15)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_15;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
if (lean_is_scalar(x_23)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_23;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_1);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(x_81, x_62, x_63, x_64, x_65);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_23);
lean_dec(x_19);
lean_inc(x_2);
x_83 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_2, x_64);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_Expr_appArg_x21(x_71);
lean_dec(x_71);
x_86 = l_Lean_Expr_getAppNumArgs(x_85);
lean_inc(x_86);
x_87 = lean_mk_array(x_86, x_26);
x_88 = lean_nat_sub(x_86, x_28);
lean_dec(x_86);
lean_inc_ref(x_85);
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_85, x_87, x_88);
x_90 = l_Array_back_x21___redArg(x_3, x_89);
lean_dec_ref(x_89);
x_91 = lean_unbox(x_84);
lean_dec(x_84);
if (x_91 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
x_31 = x_74;
x_32 = x_67;
x_33 = x_90;
x_34 = x_85;
x_35 = x_62;
x_36 = x_63;
x_37 = x_64;
x_38 = x_65;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8;
x_93 = lean_unsigned_to_nat(30u);
lean_inc(x_90);
x_94 = l_Lean_inlineExpr(x_90, x_93);
if (lean_is_scalar(x_15)) {
 x_95 = lean_alloc_ctor(7, 2, 0);
} else {
 x_95 = x_15;
 lean_ctor_set_tag(x_95, 7);
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_inc_ref(x_85);
x_98 = l_Lean_indentExpr(x_85);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_2, x_99, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_100);
x_31 = x_74;
x_32 = x_67;
x_33 = x_90;
x_34 = x_85;
x_35 = x_62;
x_36 = x_63;
x_37 = x_64;
x_38 = x_65;
x_39 = lean_box(0);
goto block_61;
}
else
{
uint8_t x_101; 
lean_dec(x_90);
lean_dec_ref(x_85);
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_30);
lean_dec(x_14);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_30);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_70);
if (x_104 == 0)
{
return x_70;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_70, 0);
lean_inc(x_105);
lean_dec(x_70);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec_ref(x_67);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_30);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_68);
if (x_107 == 0)
{
return x_68;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_68, 0);
lean_inc(x_108);
lean_dec(x_68);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_11);
if (x_123 == 0)
{
return x_11;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_11, 0);
lean_inc(x_124);
lean_dec(x_11);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_9);
if (x_126 == 0)
{
return x_9;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_9, 0);
lean_inc(x_127);
lean_dec(x_9);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_exceptEmoji___redArg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_10 = l_Lean_instInhabitedExpr;
x_11 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
if (x_9 == 0)
{
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_96; 
x_25 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_11, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(x_28, 0, x_2);
x_29 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_96 = lean_unbox(x_26);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_trace_profiler;
x_98 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_8, x_97);
if (x_98 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_24;
}
else
{
lean_inc_ref(x_8);
goto block_95;
}
}
else
{
lean_inc_ref(x_8);
goto block_95;
}
block_46:
{
lean_object* x_34; double x_35; double x_36; double x_37; double x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_34 = lean_io_mono_nanos_now();
x_35 = lean_float_of_nat(x_30);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39;
x_37 = lean_float_div(x_35, x_36);
x_38 = lean_float_of_nat(x_34);
x_39 = lean_float_div(x_38, x_36);
x_40 = lean_box_float(x_37);
x_41 = lean_box_float(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unbox(x_26);
lean_dec(x_26);
x_45 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_11, x_9, x_29, x_8, x_44, x_31, x_28, x_43, x_3, x_4, x_5, x_6);
lean_dec_ref(x_8);
return x_45;
}
block_52:
{
lean_object* x_51; 
if (lean_is_scalar(x_27)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_27;
}
lean_ctor_set(x_51, 0, x_49);
x_30 = x_47;
x_31 = x_48;
x_32 = x_51;
x_33 = lean_box(0);
goto block_46;
}
block_66:
{
lean_object* x_57; double x_58; double x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_57 = lean_io_get_num_heartbeats();
x_58 = lean_float_of_nat(x_53);
x_59 = lean_float_of_nat(x_57);
x_60 = lean_box_float(x_58);
x_61 = lean_box_float(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_unbox(x_26);
lean_dec(x_26);
x_65 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_11, x_9, x_29, x_8, x_64, x_54, x_28, x_63, x_3, x_4, x_5, x_6);
lean_dec_ref(x_8);
return x_65;
}
block_72:
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_69);
x_53 = x_67;
x_54 = x_68;
x_55 = x_71;
x_56 = lean_box(0);
goto block_66;
}
block_95:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_trace_profiler_useHeartbeats;
x_76 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_8, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_io_mono_nanos_now();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_78 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_2, x_12, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_80 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_79, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_27);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_ctor_set_tag(x_80, 1);
x_30 = x_77;
x_31 = x_74;
x_32 = x_80;
x_33 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_30 = x_77;
x_31 = x_74;
x_32 = x_83;
x_33 = lean_box(0);
goto block_46;
}
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec_ref(x_80);
x_47 = x_77;
x_48 = x_74;
x_49 = x_84;
x_50 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_85; 
lean_dec(x_1);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
lean_dec_ref(x_78);
x_47 = x_77;
x_48 = x_74;
x_49 = x_85;
x_50 = lean_box(0);
goto block_52;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_27);
x_86 = lean_io_get_num_heartbeats();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_87 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_2, x_12, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_89 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_88, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_ctor_set_tag(x_89, 1);
x_53 = x_86;
x_54 = x_74;
x_55 = x_89;
x_56 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_53 = x_86;
x_54 = x_74;
x_55 = x_92;
x_56 = lean_box(0);
goto block_66;
}
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec_ref(x_89);
x_67 = x_86;
x_68 = x_74;
x_69 = x_93;
x_70 = lean_box(0);
goto block_72;
}
}
else
{
lean_object* x_94; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
lean_dec_ref(x_87);
x_67 = x_86;
x_68 = x_74;
x_69 = x_94;
x_70 = lean_box(0);
goto block_72;
}
}
}
}
block_24:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_18 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(x_2, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_19, x_13, x_14, x_15, x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_indentD(x_2);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
x_9 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = l_Lean_MVarId_intros(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_14);
x_15 = l_Lean_Elab_Eqns_tryURefl(x_14, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_18 = l_Lean_Elab_Eqns_deltaLHS(x_14, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_5);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(x_3, x_19, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(x_10, x_5);
lean_dec(x_5);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_28 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(x_10, x_5);
lean_dec(x_5);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_exceptEmoji___redArg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_10 = 0;
lean_inc(x_1);
x_11 = l_Lean_MessageData_ofConstName(x_1, x_10);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_box(0);
lean_inc_ref(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_1);
x_19 = lean_box(x_10);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
if (x_9 == 0)
{
lean_dec_ref(x_2);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_91; 
x_34 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
x_35 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(x_34, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(x_37, 0, x_2);
x_38 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
x_91 = lean_unbox(x_36);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_trace_profiler;
x_93 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_8, x_92);
if (x_93 == 0)
{
lean_dec_ref(x_37);
lean_dec(x_36);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = lean_box(0);
goto block_33;
}
else
{
lean_inc_ref(x_8);
goto block_90;
}
}
else
{
lean_inc_ref(x_8);
goto block_90;
}
block_55:
{
lean_object* x_43; double x_44; double x_45; double x_46; double x_47; double x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_43 = lean_io_mono_nanos_now();
x_44 = lean_float_of_nat(x_39);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39;
x_46 = lean_float_div(x_44, x_45);
x_47 = lean_float_of_nat(x_43);
x_48 = lean_float_div(x_47, x_45);
x_49 = lean_box_float(x_46);
x_50 = lean_box_float(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unbox(x_36);
lean_dec(x_36);
x_54 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_34, x_9, x_38, x_8, x_53, x_40, x_37, x_52, x_3, x_4, x_5, x_6);
lean_dec_ref(x_8);
return x_54;
}
block_69:
{
lean_object* x_60; double x_61; double x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_60 = lean_io_get_num_heartbeats();
x_61 = lean_float_of_nat(x_57);
x_62 = lean_float_of_nat(x_60);
x_63 = lean_box_float(x_61);
x_64 = lean_box_float(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_unbox(x_36);
lean_dec(x_36);
x_68 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg(x_34, x_9, x_38, x_8, x_67, x_56, x_37, x_66, x_3, x_4, x_5, x_6);
lean_dec_ref(x_8);
return x_68;
}
block_90:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_trace_profiler_useHeartbeats;
x_73 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_8, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_io_mono_nanos_now();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_75 = l_Lean_Meta_mapErrorImp___redArg(x_20, x_16, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_ctor_set_tag(x_75, 1);
x_39 = x_74;
x_40 = x_71;
x_41 = x_75;
x_42 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_39 = x_74;
x_40 = x_71;
x_41 = x_78;
x_42 = lean_box(0);
goto block_55;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
lean_ctor_set_tag(x_75, 0);
x_39 = x_74;
x_40 = x_71;
x_41 = x_75;
x_42 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_39 = x_74;
x_40 = x_71;
x_41 = x_81;
x_42 = lean_box(0);
goto block_55;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_io_get_num_heartbeats();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_83 = l_Lean_Meta_mapErrorImp___redArg(x_20, x_16, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_ctor_set_tag(x_83, 1);
x_56 = x_71;
x_57 = x_82;
x_58 = x_83;
x_59 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_56 = x_71;
x_57 = x_82;
x_58 = x_86;
x_59 = lean_box(0);
goto block_69;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_ctor_set_tag(x_83, 0);
x_56 = x_71;
x_57 = x_82;
x_58 = x_83;
x_59 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_56 = x_71;
x_57 = x_82;
x_58 = x_89;
x_59 = lean_box(0);
goto block_69;
}
}
}
}
}
block_33:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_mapErrorImp___redArg(x_20, x_16, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Lean_Environment_find_x3f(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_ConstantInfo_hasValue(x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(x_4, x_2);
x_6 = l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_;
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
x_5 = l_Lean_mkMapDeclarationExtension___redArg(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_registerEqnsInfo___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
lean_inc(x_9);
x_12 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_9, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_st_ref_take(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 5);
lean_dec(x_18);
x_19 = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(x_9);
x_20 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_11);
lean_ctor_set(x_20, 4, x_3);
lean_ctor_set(x_20, 5, x_2);
lean_ctor_set(x_20, 6, x_4);
x_21 = l_Lean_MapDeclarationExtension_insert___redArg(x_19, x_17, x_9, x_20);
x_22 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
lean_ctor_set(x_15, 5, x_22);
lean_ctor_set(x_15, 0, x_21);
x_23 = lean_st_ref_set(x_6, x_15);
x_24 = lean_box(0);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 2);
x_28 = lean_ctor_get(x_15, 3);
x_29 = lean_ctor_get(x_15, 4);
x_30 = lean_ctor_get(x_15, 6);
x_31 = lean_ctor_get(x_15, 7);
x_32 = lean_ctor_get(x_15, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_33 = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(x_9);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_10);
lean_ctor_set(x_34, 3, x_11);
lean_ctor_set(x_34, 4, x_3);
lean_ctor_set(x_34, 5, x_2);
lean_ctor_set(x_34, 6, x_4);
x_35 = l_Lean_MapDeclarationExtension_insert___redArg(x_33, x_25, x_9, x_34);
x_36 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
x_38 = lean_st_ref_set(x_6, x_37);
x_39 = lean_box(0);
lean_ctor_set(x_12, 0, x_39);
return x_12;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
x_40 = lean_st_ref_take(x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_40, 3);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_40, 4);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_40, 6);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_40, 7);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_40, 8);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 lean_ctor_release(x_40, 7);
 lean_ctor_release(x_40, 8);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(x_9);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_8);
lean_ctor_set(x_51, 2, x_10);
lean_ctor_set(x_51, 3, x_11);
lean_ctor_set(x_51, 4, x_3);
lean_ctor_set(x_51, 5, x_2);
lean_ctor_set(x_51, 6, x_4);
x_52 = l_Lean_MapDeclarationExtension_insert___redArg(x_50, x_41, x_9, x_51);
x_53 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 9, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_44);
lean_ctor_set(x_54, 4, x_45);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_46);
lean_ctor_set(x_54, 7, x_47);
lean_ctor_set(x_54, 8, x_48);
x_55 = lean_st_ref_set(x_6, x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_registerEqnsInfo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 1;
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_10, x_11, x_10, x_11, x_12, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 5);
lean_dec(x_11);
x_12 = l_Lean_Environment_setExporting(x_10, x_2);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_1, x_8);
x_14 = lean_st_ref_take(x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_dec(x_16);
lean_ctor_set(x_14, 1, x_5);
x_17 = lean_st_ref_set(x_4, x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 2);
x_22 = lean_ctor_get(x_14, 3);
x_23 = lean_ctor_get(x_14, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_set(x_4, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 4);
x_33 = lean_ctor_get(x_8, 6);
x_34 = lean_ctor_get(x_8, 7);
x_35 = lean_ctor_get(x_8, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_36 = l_Lean_Environment_setExporting(x_28, x_2);
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_3);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_34);
lean_ctor_set(x_37, 8, x_35);
x_38 = lean_st_ref_set(x_1, x_37);
x_39 = lean_st_ref_take(x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_39, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 3);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_39, 4);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 x_44 = x_39;
} else {
 lean_dec_ref(x_39);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_5);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_st_ref_set(x_4, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_registerEqnsInfo___closed__1;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec_ref(x_9);
x_11 = lean_st_ref_take(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 5);
lean_dec(x_14);
x_15 = l_Lean_Environment_setExporting(x_13, x_2);
x_16 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
lean_ctor_set(x_11, 5, x_16);
lean_ctor_set(x_11, 0, x_15);
x_17 = lean_st_ref_set(x_6, x_11);
x_18 = lean_st_ref_take(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_dec(x_20);
x_21 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0;
lean_ctor_set(x_18, 1, x_21);
x_22 = lean_st_ref_set(x_4, x_18);
lean_inc(x_6);
lean_inc(x_4);
x_23 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_ctor_set_tag(x_23, 1);
x_26 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_16, x_4, x_21, x_23);
lean_dec_ref(x_23);
lean_dec(x_4);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_inc(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_16, x_4, x_21, x_31);
lean_dec_ref(x_31);
lean_dec(x_4);
lean_dec(x_6);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_33 = x_32;
} else {
 lean_dec_ref(x_32);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec_ref(x_23);
x_36 = lean_box(0);
x_37 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_16, x_4, x_21, x_36);
lean_dec(x_4);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 2);
x_43 = lean_ctor_get(x_18, 3);
x_44 = lean_ctor_get(x_18, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_45 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0;
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_44);
x_47 = lean_st_ref_set(x_4, x_46);
lean_inc(x_6);
lean_inc(x_4);
x_48 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
lean_inc(x_49);
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
x_52 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_16, x_4, x_45, x_51);
lean_dec_ref(x_51);
lean_dec(x_4);
lean_dec(x_6);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_53 = x_52;
} else {
 lean_dec_ref(x_52);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec_ref(x_48);
x_56 = lean_box(0);
x_57 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_16, x_4, x_45, x_56);
lean_dec(x_4);
lean_dec(x_6);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_58 = x_57;
} else {
 lean_dec_ref(x_57);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_55);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
x_62 = lean_ctor_get(x_11, 2);
x_63 = lean_ctor_get(x_11, 3);
x_64 = lean_ctor_get(x_11, 4);
x_65 = lean_ctor_get(x_11, 6);
x_66 = lean_ctor_get(x_11, 7);
x_67 = lean_ctor_get(x_11, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
x_68 = l_Lean_Environment_setExporting(x_60, x_2);
x_69 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_64);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_65);
lean_ctor_set(x_70, 7, x_66);
lean_ctor_set(x_70, 8, x_67);
x_71 = lean_st_ref_set(x_6, x_70);
x_72 = lean_st_ref_take(x_4);
x_73 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_72, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 3);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_72, 4);
lean_inc_ref(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
x_78 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 5, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_74);
lean_ctor_set(x_79, 3, x_75);
lean_ctor_set(x_79, 4, x_76);
x_80 = lean_st_ref_set(x_4, x_79);
lean_inc(x_6);
lean_inc(x_4);
x_81 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
lean_inc(x_82);
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_82);
x_85 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_69, x_4, x_78, x_84);
lean_dec_ref(x_84);
lean_dec(x_4);
lean_dec(x_6);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_86 = x_85;
} else {
 lean_dec_ref(x_85);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_82);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec_ref(x_81);
x_89 = lean_box(0);
x_90 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(x_6, x_10, x_69, x_4, x_78, x_89);
lean_dec(x_4);
lean_dec(x_6);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_91 = x_90;
} else {
 lean_dec_ref(x_90);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
 lean_ctor_set_tag(x_92, 1);
}
lean_ctor_set(x_92, 0, x_88);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_2 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_mkLevelParam(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_mkLevelParam(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
lean_inc(x_1);
x_12 = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(x_1, x_11);
lean_inc(x_2);
x_13 = l_Lean_mkConst(x_2, x_12);
x_14 = l_Lean_mkAppN(x_13, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_mkEq(x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
x_18 = 1;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_19 = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(x_17, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = 0;
x_22 = 1;
x_23 = l_Lean_Meta_mkForallFVars(x_4, x_16, x_21, x_18, x_18, x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_25 = l_Lean_Meta_letToHave(x_24, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Meta_mkLambdaFVars(x_4, x_20, x_21, x_18, x_21, x_18, x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_3);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_26);
lean_inc(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_11);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_9);
lean_inc_ref(x_8);
x_33 = l_Lean_addDecl(x_32, x_21, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec_ref(x_33);
x_34 = l_Lean_inferDefEqAttr(x_3, x_6, x_7, x_8, x_9);
return x_34;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
return x_33;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_7, x_5);
if (x_6 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_10);
return x_1;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_3);
lean_inc(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_13, x_11);
if (x_12 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
x_16 = l_Lean_Name_isPrefixOf(x_15, x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_54; uint8_t x_75; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 12);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_6, 13);
lean_inc_ref(x_25);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 lean_ctor_release(x_6, 12);
 lean_ctor_release(x_6, 13);
 x_26 = x_6;
} else {
 lean_dec_ref(x_6);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_27);
lean_dec(x_9);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(x_28, 0, x_10);
lean_closure_set(x_28, 1, x_1);
lean_closure_set(x_28, 2, x_3);
x_29 = 0;
x_30 = l_Lean_Meta_tactic_hygienic;
x_31 = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(x_14, x_30, x_29);
x_32 = l_Lean_diagnostics;
x_33 = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(x_31, x_32);
x_75 = l_Lean_Kernel_isDiagnosticsEnabled(x_27);
lean_dec_ref(x_27);
if (x_75 == 0)
{
if (x_33 == 0)
{
x_34 = x_12;
x_35 = x_13;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_24;
x_46 = x_25;
x_47 = x_7;
x_48 = lean_box(0);
goto block_53;
}
else
{
x_54 = x_75;
goto block_74;
}
}
else
{
x_54 = x_33;
goto block_74;
}
block_53:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_maxRecDepth;
x_50 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(x_31, x_49);
if (lean_is_scalar(x_26)) {
 x_51 = lean_alloc_ctor(0, 14, 2);
} else {
 x_51 = x_26;
}
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_35);
lean_ctor_set(x_51, 2, x_31);
lean_ctor_set(x_51, 3, x_36);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_37);
lean_ctor_set(x_51, 6, x_38);
lean_ctor_set(x_51, 7, x_39);
lean_ctor_set(x_51, 8, x_40);
lean_ctor_set(x_51, 9, x_41);
lean_ctor_set(x_51, 10, x_42);
lean_ctor_set(x_51, 11, x_43);
lean_ctor_set(x_51, 12, x_44);
lean_ctor_set(x_51, 13, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_51, sizeof(void*)*14 + 1, x_45);
x_52 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(x_11, x_28, x_29, x_4, x_5, x_51, x_47);
return x_52;
}
block_74:
{
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_st_ref_take(x_7);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 5);
lean_dec(x_58);
x_59 = l_Lean_Kernel_enableDiag(x_57, x_33);
x_60 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
lean_ctor_set(x_55, 5, x_60);
lean_ctor_set(x_55, 0, x_59);
x_61 = lean_st_ref_set(x_7, x_55);
x_34 = x_12;
x_35 = x_13;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_24;
x_46 = x_25;
x_47 = x_7;
x_48 = lean_box(0);
goto block_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
x_64 = lean_ctor_get(x_55, 2);
x_65 = lean_ctor_get(x_55, 3);
x_66 = lean_ctor_get(x_55, 4);
x_67 = lean_ctor_get(x_55, 6);
x_68 = lean_ctor_get(x_55, 7);
x_69 = lean_ctor_get(x_55, 8);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_70 = l_Lean_Kernel_enableDiag(x_62, x_33);
x_71 = l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
x_72 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_67);
lean_ctor_set(x_72, 7, x_68);
lean_ctor_set(x_72, 8, x_69);
x_73 = lean_st_ref_set(x_7, x_72);
x_34 = x_12;
x_35 = x_13;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_24;
x_46 = x_25;
x_47 = x_7;
x_48 = lean_box(0);
goto block_53;
}
}
else
{
x_34 = x_12;
x_35 = x_13;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_24;
x_46 = x_25;
x_47 = x_7;
x_48 = lean_box(0);
goto block_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_10);
x_14 = l_Lean_Meta_mkEqLikeNameFor(x_9, x_10, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_12, x_11, x_15);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_14);
lean_inc(x_14);
x_18 = l_Lean_Meta_realizeConst(x_16, x_14, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Structural_eqnInfoExt;
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_12, x_9, x_8, x_1, x_11, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 1)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(x_1, x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_14);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(x_1, x_25, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_32 = x_26;
} else {
 lean_dec_ref(x_26);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Structural_eqnInfoExt;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
x_10 = 0;
x_11 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_9, x_6, x_5, x_1, x_8, x_10);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 1)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_dec_ref(x_2);
x_5 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(x_1, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_get_structural_rec_arg_pos(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2295916746u);
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
x_3 = l_Lean_Meta_registerGetUnfoldEqnFn(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_3);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
x_5 = 0;
x_6 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
x_7 = l_Lean_registerTraceClass(x_4, x_5, x_6);
return x_7;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2 = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2);
l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3 = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3);
l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4 = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4);
l_Lean_Elab_Structural_instInhabitedEqnInfo_default = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo_default);
l_Lean_Elab_Structural_instInhabitedEqnInfo = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1 = _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_spec__5___redArg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___closed__0);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__0();
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__2);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___redArg___closed__3();
l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1 = _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39();
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = _init_l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Structural_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Structural_eqnInfoExt);
lean_dec_ref(res);
}l_Lean_Elab_Structural_registerEqnsInfo___closed__0 = _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
l_Lean_Elab_Structural_registerEqnsInfo___closed__1 = _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
l_Lean_Elab_Structural_registerEqnsInfo___closed__2 = _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
