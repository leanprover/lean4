// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Entails
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.EPost public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache public import Lean.Elab.Tactic.Do.Internal.VCGen.Util public import Lean.Meta.Sym.Util import Lean.Meta.Sym.InferType
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeSplits;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Failed to unfold the Triple target of "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to apply precondition intro rule to "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to intro the lifted precondition of "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_3),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value_aux_4),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 41, 155, 61, 92, 197, 165, 144)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 37, .m_data = "Failed to strip the `⊤ ⊑` wrapper of "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(lean_object* v_goal_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_backwardRules_63_; lean_object* v_tripleIntro_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_backwardRules_63_ = lean_ctor_get(v_a_51_, 0);
v_tripleIntro_64_ = lean_ctor_get(v_backwardRules_63_, 0);
v___x_65_ = lean_box(0);
lean_inc(v_goal_50_);
lean_inc_ref(v_tripleIntro_64_);
v___x_66_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_tripleIntro_64_, v_goal_50_, v___x_65_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_93_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_93_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_93_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_93_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; 
if (lean_obj_tag(v_a_67_) == 1)
{
lean_object* v_mvarIds_87_; 
v_mvarIds_87_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_mvarIds_87_);
lean_dec_ref_known(v_a_67_, 1);
if (lean_obj_tag(v_mvarIds_87_) == 1)
{
lean_object* v_tail_88_; 
v_tail_88_ = lean_ctor_get(v_mvarIds_87_, 1);
if (lean_obj_tag(v_tail_88_) == 0)
{
lean_object* v_head_89_; lean_object* v___x_91_; 
lean_dec(v_goal_50_);
v_head_89_ = lean_ctor_get(v_mvarIds_87_, 0);
lean_inc(v_head_89_);
lean_dec_ref_known(v_mvarIds_87_, 2);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v_head_89_);
v___x_91_ = v___x_69_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_head_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_87_, 2);
lean_del_object(v___x_69_);
v___y_72_ = v_a_51_;
v___y_73_ = v_a_52_;
v___y_74_ = v_a_53_;
v___y_75_ = v_a_54_;
v___y_76_ = v_a_55_;
v___y_77_ = v_a_56_;
v___y_78_ = v_a_57_;
v___y_79_ = v_a_58_;
v___y_80_ = v_a_59_;
v___y_81_ = v_a_60_;
v___y_82_ = v_a_61_;
goto v___jp_71_;
}
}
else
{
lean_dec(v_mvarIds_87_);
lean_del_object(v___x_69_);
v___y_72_ = v_a_51_;
v___y_73_ = v_a_52_;
v___y_74_ = v_a_53_;
v___y_75_ = v_a_54_;
v___y_76_ = v_a_55_;
v___y_77_ = v_a_56_;
v___y_78_ = v_a_57_;
v___y_79_ = v_a_58_;
v___y_80_ = v_a_59_;
v___y_81_ = v_a_60_;
v___y_82_ = v_a_61_;
goto v___jp_71_;
}
}
else
{
lean_del_object(v___x_69_);
lean_dec(v_a_67_);
v___y_72_ = v_a_51_;
v___y_73_ = v_a_52_;
v___y_74_ = v_a_53_;
v___y_75_ = v_a_54_;
v___y_76_ = v_a_55_;
v___y_77_ = v_a_56_;
v___y_78_ = v_a_57_;
v___y_79_ = v_a_58_;
v___y_80_ = v_a_59_;
v___y_81_ = v_a_60_;
v___y_82_ = v_a_61_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___closed__1);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v_goal_50_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v___x_85_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_86_;
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_goal_50_);
v_a_94_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_66_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_66_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple___boxed(lean_object* v_goal_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(v_goal_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0(lean_object* v_00_u03b1_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v_msg_117_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___boxed(lean_object* v_00_u03b1_131_, lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0(v_00_u03b1_131_, v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0(lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
v___x_159_ = lean_apply_12(v_x_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, lean_box(0));
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0(v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg(lean_object* v_mvarId_174_, lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; 
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc_ref(v___y_179_);
lean_inc(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_188_, 0, v_x_175_);
lean_closure_set(v___f_188_, 1, v___y_176_);
lean_closure_set(v___f_188_, 2, v___y_177_);
lean_closure_set(v___f_188_, 3, v___y_178_);
lean_closure_set(v___f_188_, 4, v___y_179_);
lean_closure_set(v___f_188_, 5, v___y_180_);
lean_closure_set(v___f_188_, 6, v___y_181_);
lean_closure_set(v___f_188_, 7, v___y_182_);
v___x_189_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_174_, v___f_188_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
return v___x_189_;
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg___boxed(lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg(v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0(lean_object* v_00_u03b1_213_, lean_object* v_mvarId_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg(v_mvarId_214_, v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___boxed(lean_object* v_00_u03b1_229_, lean_object* v_mvarId_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0(v_00_u03b1_229_, v_mvarId_230_, v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0(lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_lctx_257_; lean_object* v___x_258_; 
v_lctx_257_ = lean_ctor_get(v___y_252_, 2);
lean_inc_ref(v_lctx_257_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_lctx_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0___boxed(lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___lam__0(v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_271_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__0));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__4));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(lean_object* v_rule_281_, lean_object* v_goal_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
lean_inc(v_goal_282_);
v___x_296_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_281_, v_goal_282_, v___x_295_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
if (lean_obj_tag(v_a_297_) == 1)
{
lean_object* v_mvarIds_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_361_; 
v_mvarIds_307_ = lean_ctor_get(v_a_297_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_297_);
if (v_isSharedCheck_361_ == 0)
{
v___x_309_ = v_a_297_;
v_isShared_310_ = v_isSharedCheck_361_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_mvarIds_307_);
lean_dec(v_a_297_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_361_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
if (lean_obj_tag(v_mvarIds_307_) == 1)
{
lean_object* v_tail_311_; 
v_tail_311_ = lean_ctor_get(v_mvarIds_307_, 1);
if (lean_obj_tag(v_tail_311_) == 0)
{
lean_object* v_head_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_goal_282_);
v_head_312_ = lean_ctor_get(v_mvarIds_307_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_mvarIds_307_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_mvarIds_307_, 1);
lean_dec(v_unused_360_);
v___x_314_ = v_mvarIds_307_;
v_isShared_315_ = v_isSharedCheck_359_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_head_312_);
lean_dec(v_mvarIds_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_359_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__2));
v___x_317_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_head_312_, v___x_316_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___f_319_; lean_object* v___x_320_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_n(v_a_318_, 2);
lean_dec_ref_known(v___x_317_, 1);
v___f_319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__3));
v___x_320_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introPre_spec__0___redArg(v_a_318_, v___f_319_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_342_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_342_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_LocalContext_lastDecl(v_a_321_);
lean_dec(v_a_321_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_del_object(v___x_309_);
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = l_Lean_LocalDecl_fvarId(v_val_326_);
lean_dec(v_val_326_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 0);
lean_ctor_set(v___x_314_, 1, v___x_327_);
lean_ctor_set(v___x_314_, 0, v_a_318_);
v___x_329_ = v___x_314_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_329_);
v___x_331_ = v___x_323_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_dec(v___x_325_);
lean_del_object(v___x_323_);
v___x_334_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__5);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v_a_318_);
v___x_336_ = v___x_309_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_318_);
v___x_336_ = v_reuseFailAlloc_341_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 7);
lean_ctor_set(v___x_314_, 1, v___x_336_);
lean_ctor_set(v___x_314_, 0, v___x_334_);
v___x_338_ = v___x_314_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v___x_338_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_339_;
}
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_318_);
lean_del_object(v___x_314_);
lean_del_object(v___x_309_);
v_a_343_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_320_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_320_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_del_object(v___x_314_);
lean_del_object(v___x_309_);
v_a_351_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_317_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_317_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_307_, 2);
lean_del_object(v___x_309_);
v___y_299_ = v_a_290_;
v___y_300_ = v_a_291_;
v___y_301_ = v_a_292_;
v___y_302_ = v_a_293_;
goto v___jp_298_;
}
}
else
{
lean_del_object(v___x_309_);
lean_dec(v_mvarIds_307_);
v___y_299_ = v_a_290_;
v___y_300_ = v_a_291_;
v___y_301_ = v_a_292_;
v___y_302_ = v_a_293_;
goto v___jp_298_;
}
}
}
else
{
lean_dec(v_a_297_);
v___y_299_ = v_a_290_;
v___y_300_ = v_a_291_;
v___y_301_ = v_a_292_;
v___y_302_ = v_a_293_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___closed__1);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_goal_282_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v___x_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_306_;
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_goal_282_);
v_a_362_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_296_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_296_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre___boxed(lean_object* v_rule_370_, lean_object* v_goal_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_rule_370_, v_goal_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_385_, lean_object* v_a_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___y_395_; lean_object* v___x_398_; uint8_t v_debug_399_; 
v___x_398_ = lean_st_ref_get(v___y_388_);
v_debug_399_ = lean_ctor_get_uint8(v___x_398_, sizeof(void*)*11);
lean_dec(v___x_398_);
if (v_debug_399_ == 0)
{
v___y_395_ = v___y_388_;
goto v___jp_394_;
}
else
{
lean_object* v___x_400_; 
lean_inc_ref(v_f_385_);
v___x_400_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref_known(v___x_400_, 1);
lean_inc_ref(v_a_386_);
v___x_401_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_dec_ref_known(v___x_401_, 1);
v___y_395_ = v___y_388_;
goto v___jp_394_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v_a_386_);
lean_dec_ref(v_f_385_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_a_386_);
lean_dec_ref(v_f_385_);
v_a_410_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_400_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_Lean_Expr_app___override(v_f_385_, v_a_386_);
v___x_397_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_396_, v___y_395_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_418_, lean_object* v_a_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_f_418_, v_a_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0(lean_object* v_args_428_, lean_object* v_endIdx_429_, lean_object* v_b_430_, lean_object* v_i_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v_endIdx_429_, v_i_431_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = l_Lean_instInhabitedExpr;
v___x_446_ = lean_array_get_borrowed(v___x_445_, v_args_428_, v_i_431_);
lean_inc(v___x_446_);
v___x_447_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_b_430_, v___x_446_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_i_431_, v___x_449_);
lean_dec(v_i_431_);
v_b_430_ = v_a_448_;
v_i_431_ = v___x_450_;
goto _start;
}
else
{
lean_dec(v_i_431_);
return v___x_447_;
}
}
else
{
lean_object* v___x_452_; 
lean_dec(v_i_431_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_b_430_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0___boxed(lean_object* v_args_453_, lean_object* v_endIdx_454_, lean_object* v_b_455_, lean_object* v_i_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0(v_args_453_, v_endIdx_454_, v_b_455_, v_i_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_endIdx_454_);
lean_dec_ref(v_args_453_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0(lean_object* v_f_470_, lean_object* v_args_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_array_get_size(v_args_471_);
v___x_486_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0(v_args_471_, v___x_485_, v_f_470_, v___x_484_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0___boxed(lean_object* v_f_487_, lean_object* v_args_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0(v_f_487_, v_args_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_args_488_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1(lean_object* v_target_522_, lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_pre_525_, lean_object* v_goal_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
if (lean_obj_tag(v_x_527_) == 5)
{
lean_object* v_fn_542_; lean_object* v_arg_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_fn_542_ = lean_ctor_get(v_x_527_, 0);
lean_inc_ref(v_fn_542_);
v_arg_543_ = lean_ctor_get(v_x_527_, 1);
lean_inc_ref(v_arg_543_);
lean_dec_ref_known(v_x_527_, 2);
v___x_544_ = lean_array_set(v_x_528_, v_x_529_, v_arg_543_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_sub(v_x_529_, v___x_545_);
lean_dec(v_x_529_);
v_x_527_ = v_fn_542_;
v_x_528_ = v___x_544_;
v_x_529_ = v___x_546_;
goto _start;
}
else
{
lean_object* v___x_548_; uint8_t v___x_549_; 
lean_dec(v_x_529_);
v___x_548_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__6));
v___x_549_ = l_Lean_Expr_isConstOf(v_x_527_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_x_528_);
lean_dec_ref(v_x_527_);
lean_dec(v_goal_526_);
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
lean_dec_ref(v_target_522_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(2u);
v___x_553_ = lean_array_get_size(v_x_528_);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_x_528_);
lean_dec_ref(v_x_527_);
lean_dec(v_goal_526_);
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
lean_dec_ref(v_target_522_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_array_fget_borrowed(v_x_528_, v___x_552_);
v___x_558_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___closed__10));
v___x_559_ = l_Lean_Expr_isAppOf(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_564_; 
lean_dec_ref(v_x_527_);
v___x_560_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_557_);
v___x_561_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_peelEPostTailChain(v___x_557_, v___x_560_);
v_fst_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_fst_562_);
v_snd_563_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_snd_563_);
lean_dec_ref(v___x_561_);
v___x_564_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkEPostAtIndex(v_fst_562_, v_snd_563_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_627_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_627_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_627_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_627_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 1)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_622_; 
lean_del_object(v___x_567_);
v_val_569_ = lean_ctor_get(v_a_565_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_622_ == 0)
{
v___x_571_ = v_a_565_;
v_isShared_572_ = v_isSharedCheck_622_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_a_565_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_622_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = l_Array_extract___redArg(v_x_528_, v___x_573_, v___x_553_);
lean_dec_ref(v_x_528_);
v___x_575_ = l_Lean_Meta_Sym_betaS(v_val_569_, v___x_574_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = l_Lean_Expr_getAppFn(v_target_522_);
lean_dec_ref(v_target_522_);
v___x_578_ = lean_unsigned_to_nat(4u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_array_push(v___x_579_, v_00_u03b1_523_);
v___x_581_ = lean_array_push(v___x_580_, v_inst_524_);
v___x_582_ = lean_array_push(v___x_581_, v_pre_525_);
v___x_583_ = lean_array_push(v___x_582_, v_a_576_);
v___x_584_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0(v___x_577_, v___x_583_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec_ref(v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_526_, v_a_585_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_a_587_);
v___x_592_ = v___x_571_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_571_);
v_a_598_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_586_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_586_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_571_);
lean_dec(v_goal_526_);
v_a_606_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_584_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_584_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_571_);
lean_dec(v_goal_526_);
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
lean_dec_ref(v_target_522_);
v_a_614_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_575_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_575_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_625_; 
lean_dec(v_a_565_);
lean_dec_ref(v_x_528_);
lean_dec(v_goal_526_);
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
lean_dec_ref(v_target_522_);
v___x_623_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_623_);
v___x_625_ = v___x_567_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_x_528_);
lean_dec(v_goal_526_);
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
lean_dec_ref(v_target_522_);
v_a_628_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_564_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_564_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v___x_636_; 
lean_dec_ref(v_pre_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_00_u03b1_523_);
v___x_636_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_replaceEPostHeadBot_x3f(v_goal_526_, v_target_522_, v_x_527_, v_x_528_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec_ref(v_x_528_);
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_target_637_ = _args[0];
lean_object* v_00_u03b1_638_ = _args[1];
lean_object* v_inst_639_ = _args[2];
lean_object* v_pre_640_ = _args[3];
lean_object* v_goal_641_ = _args[4];
lean_object* v_x_642_ = _args[5];
lean_object* v_x_643_ = _args[6];
lean_object* v_x_644_ = _args[7];
lean_object* v___y_645_ = _args[8];
lean_object* v___y_646_ = _args[9];
lean_object* v___y_647_ = _args[10];
lean_object* v___y_648_ = _args[11];
lean_object* v___y_649_ = _args[12];
lean_object* v___y_650_ = _args[13];
lean_object* v___y_651_ = _args[14];
lean_object* v___y_652_ = _args[15];
lean_object* v___y_653_ = _args[16];
lean_object* v___y_654_ = _args[17];
lean_object* v___y_655_ = _args[18];
lean_object* v___y_656_ = _args[19];
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1(v_target_637_, v_00_u03b1_638_, v_inst_639_, v_pre_640_, v_goal_641_, v_x_642_, v_x_643_, v_x_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_657_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0(void){
_start:
{
lean_object* v___x_658_; lean_object* v_dummy_659_; 
v___x_658_ = lean_box(0);
v_dummy_659_ = l_Lean_Expr_sort___override(v___x_658_);
return v_dummy_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(lean_object* v_goal_660_, lean_object* v_target_661_, lean_object* v_00_u03b1_662_, lean_object* v_inst_663_, lean_object* v_pre_664_, lean_object* v_rhs_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_dummy_678_; lean_object* v_nargs_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_dummy_678_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_679_ = l_Lean_Expr_getAppNumArgs(v_rhs_665_);
lean_inc(v_nargs_679_);
v___x_680_ = lean_mk_array(v_nargs_679_, v_dummy_678_);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_sub(v_nargs_679_, v___x_681_);
lean_dec(v_nargs_679_);
v___x_683_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__1(v_target_661_, v_00_u03b1_662_, v_inst_663_, v_pre_664_, v_goal_660_, v_rhs_665_, v___x_680_, v___x_682_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___boxed(lean_object** _args){
lean_object* v_goal_684_ = _args[0];
lean_object* v_target_685_ = _args[1];
lean_object* v_00_u03b1_686_ = _args[2];
lean_object* v_inst_687_ = _args[3];
lean_object* v_pre_688_ = _args[4];
lean_object* v_rhs_689_ = _args[5];
lean_object* v_a_690_ = _args[6];
lean_object* v_a_691_ = _args[7];
lean_object* v_a_692_ = _args[8];
lean_object* v_a_693_ = _args[9];
lean_object* v_a_694_ = _args[10];
lean_object* v_a_695_ = _args[11];
lean_object* v_a_696_ = _args[12];
lean_object* v_a_697_ = _args[13];
lean_object* v_a_698_ = _args[14];
lean_object* v_a_699_ = _args[15];
lean_object* v_a_700_ = _args[16];
lean_object* v_a_701_ = _args[17];
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_684_, v_target_685_, v_00_u03b1_686_, v_inst_687_, v_pre_688_, v_rhs_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(lean_object* v_f_703_, lean_object* v_a_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_f_703_, v_a_704_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_718_, lean_object* v_a_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(v_f_718_, v_a_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object* v_a_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
else
{
lean_object* v_key_736_; lean_object* v_value_737_; lean_object* v_tail_738_; uint8_t v___x_739_; 
v_key_736_ = lean_ctor_get(v_x_734_, 0);
v_value_737_ = lean_ctor_get(v_x_734_, 1);
v_tail_738_ = lean_ctor_get(v_x_734_, 2);
v___x_739_ = lean_name_eq(v_key_736_, v_a_733_);
if (v___x_739_ == 0)
{
v_x_734_ = v_tail_738_;
goto _start;
}
else
{
lean_object* v___x_741_; 
lean_inc(v_value_737_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_value_737_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_742_, v_x_743_);
lean_dec(v_x_743_);
lean_dec(v_a_742_);
return v_res_744_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_745_; uint64_t v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(1723u);
v___x_746_ = lean_uint64_of_nat(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_buckets_749_; lean_object* v___x_750_; uint64_t v___y_752_; 
v_buckets_749_ = lean_ctor_get(v_m_747_, 1);
v___x_750_ = lean_array_get_size(v_buckets_749_);
if (lean_obj_tag(v_a_748_) == 0)
{
uint64_t v___x_766_; 
v___x_766_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___closed__0);
v___y_752_ = v___x_766_;
goto v___jp_751_;
}
else
{
uint64_t v_hash_767_; 
v_hash_767_ = lean_ctor_get_uint64(v_a_748_, sizeof(void*)*2);
v___y_752_ = v_hash_767_;
goto v___jp_751_;
}
v___jp_751_:
{
uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v_fold_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_753_ = 32ULL;
v___x_754_ = lean_uint64_shift_right(v___y_752_, v___x_753_);
v_fold_755_ = lean_uint64_xor(v___y_752_, v___x_754_);
v___x_756_ = 16ULL;
v___x_757_ = lean_uint64_shift_right(v_fold_755_, v___x_756_);
v___x_758_ = lean_uint64_xor(v_fold_755_, v___x_757_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = lean_usize_of_nat(v___x_750_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_usize_land(v___x_759_, v___x_762_);
v___x_764_ = lean_array_uget_borrowed(v_buckets_749_, v___x_763_);
v___x_765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_748_, v___x_764_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_m_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1(lean_object* v_goal_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
if (lean_obj_tag(v_x_772_) == 5)
{
lean_object* v_fn_787_; lean_object* v_arg_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_fn_787_ = lean_ctor_get(v_x_772_, 0);
lean_inc_ref(v_fn_787_);
v_arg_788_ = lean_ctor_get(v_x_772_, 1);
lean_inc_ref(v_arg_788_);
lean_dec_ref_known(v_x_772_, 2);
v___x_789_ = lean_array_set(v_x_773_, v_x_774_, v_arg_788_);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_sub(v_x_774_, v___x_790_);
lean_dec(v_x_774_);
v_x_772_ = v_fn_787_;
v_x_773_ = v___x_789_;
v_x_774_ = v___x_791_;
goto _start;
}
else
{
lean_object* v___x_793_; 
lean_dec(v_x_774_);
v___x_793_ = l_Lean_Expr_constName_x3f(v_x_772_);
lean_dec_ref(v_x_772_);
if (lean_obj_tag(v___x_793_) == 1)
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_859_; 
v_val_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_859_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_859_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_859_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeSplits;
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg(v___x_798_, v_val_794_);
lean_dec(v_val_794_);
if (lean_obj_tag(v___x_799_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_856_; 
v_val_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_856_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_856_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_856_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
uint8_t v_needApplyArgs_804_; lean_object* v_numOperands_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_as_808_; lean_object* v___x_809_; lean_object* v_excessArgs_810_; lean_object* v___y_812_; 
v_needApplyArgs_804_ = lean_ctor_get_uint8(v_val_800_, sizeof(void*)*4);
v_numOperands_805_ = lean_ctor_get(v_val_800_, 3);
v___x_806_ = lean_unsigned_to_nat(2u);
v___x_807_ = lean_nat_add(v___x_806_, v_numOperands_805_);
lean_inc(v___x_807_);
v_as_808_ = l_Array_extract___redArg(v_x_773_, v___x_806_, v___x_807_);
v___x_809_ = lean_array_get_size(v_x_773_);
v_excessArgs_810_ = l_Array_extract___redArg(v_x_773_, v___x_807_, v___x_809_);
if (v_needApplyArgs_804_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_lt(v___x_848_, v___x_809_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_del_object(v___x_796_);
lean_dec_ref(v_x_773_);
v___x_850_ = lean_box(0);
v___y_812_ = v___x_850_;
goto v___jp_811_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_array_fget(v_x_773_, v___x_848_);
lean_dec_ref(v_x_773_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_851_);
v___x_853_ = v___x_796_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v___y_812_ = v___x_853_;
goto v___jp_811_;
}
}
}
else
{
lean_object* v___x_855_; 
lean_del_object(v___x_796_);
lean_dec_ref(v_x_773_);
v___x_855_ = lean_box(0);
v___y_812_ = v___x_855_;
goto v___jp_811_;
}
v___jp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_val_800_, v_as_808_, v_excessArgs_810_, v___y_812_, v___y_776_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = lean_box(0);
v___x_816_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_814_, v_goal_771_, v___x_815_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_831_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_831_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
if (lean_obj_tag(v_a_817_) == 0)
{
lean_object* v___x_822_; 
lean_del_object(v___x_802_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_815_);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_815_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_mvarIds_824_; lean_object* v___x_826_; 
v_mvarIds_824_ = lean_ctor_get(v_a_817_, 0);
lean_inc(v_mvarIds_824_);
lean_dec_ref_known(v_a_817_, 1);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_mvarIds_824_);
v___x_826_ = v___x_802_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_mvarIds_824_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_826_);
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_del_object(v___x_802_);
v_a_832_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_816_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_816_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_802_);
lean_dec(v_goal_771_);
v_a_840_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_813_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_813_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v___x_799_);
lean_del_object(v___x_796_);
lean_dec_ref(v_x_773_);
lean_dec(v_goal_771_);
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v___x_793_);
lean_dec_ref(v_x_773_);
lean_dec(v_goal_771_);
v___x_860_ = lean_box(0);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1___boxed(lean_object* v_goal_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1(v_goal_862_, v_x_863_, v_x_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(lean_object* v_goal_879_, lean_object* v_rhs_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_dummy_893_; lean_object* v_nargs_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_dummy_893_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_894_ = l_Lean_Expr_getAppNumArgs(v_rhs_880_);
lean_inc(v_nargs_894_);
v___x_895_ = lean_mk_array(v_nargs_894_, v_dummy_893_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_sub(v_nargs_894_, v___x_896_);
lean_dec(v_nargs_894_);
v___x_898_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__1(v_goal_879_, v_rhs_880_, v___x_895_, v___x_897_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f___boxed(lean_object* v_goal_899_, lean_object* v_rhs_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_899_, v_rhs_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0(lean_object* v_00_u03b2_914_, lean_object* v_m_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_915_, v_a_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0(v_00_u03b2_918_, v_m_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_m_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object* v_00_u03b2_922_, lean_object* v_a_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_923_, v_x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_926_, lean_object* v_a_927_, lean_object* v_x_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f_spec__0_spec__0(v_00_u03b2_926_, v_a_927_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_a_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object* v_as_955_, size_t v_sz_956_, size_t v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_lt(v_i_957_, v_sz_956_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_b_958_);
return v___x_967_;
}
else
{
lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1215_; 
v_snd_968_ = lean_ctor_get(v_b_958_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_b_958_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_b_958_, 0);
lean_dec(v_unused_1216_);
v___x_970_ = v_b_958_;
v_isShared_971_ = v_isSharedCheck_1215_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_dec(v_b_958_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1215_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_snd_972_; lean_object* v_snd_973_; lean_object* v_snd_974_; lean_object* v_fst_975_; 
v_snd_972_ = lean_ctor_get(v_snd_968_, 1);
lean_inc(v_snd_972_);
v_snd_973_ = lean_ctor_get(v_snd_972_, 1);
lean_inc(v_snd_973_);
v_snd_974_ = lean_ctor_get(v_snd_973_, 1);
lean_inc(v_snd_974_);
v_fst_975_ = lean_ctor_get(v_snd_974_, 0);
lean_inc(v_fst_975_);
if (lean_obj_tag(v_fst_975_) == 7)
{
lean_object* v_fst_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1172_; 
v_fst_976_ = lean_ctor_get(v_snd_968_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_snd_968_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_snd_968_, 1);
lean_dec(v_unused_1173_);
v___x_978_ = v_snd_968_;
v_isShared_979_ = v_isSharedCheck_1172_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_fst_976_);
lean_dec(v_snd_968_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1172_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_fst_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1170_; 
v_fst_980_ = lean_ctor_get(v_snd_972_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_snd_972_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_snd_972_, 1);
lean_dec(v_unused_1171_);
v___x_982_ = v_snd_972_;
v_isShared_983_ = v_isSharedCheck_1170_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_fst_980_);
lean_dec(v_snd_972_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1170_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_fst_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1168_; 
v_fst_984_ = lean_ctor_get(v_snd_973_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_snd_973_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_snd_973_, 1);
lean_dec(v_unused_1169_);
v___x_986_ = v_snd_973_;
v_isShared_987_ = v_isSharedCheck_1168_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_fst_984_);
lean_dec(v_snd_973_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1168_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_snd_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1166_; 
v_snd_988_ = lean_ctor_get(v_snd_974_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_snd_974_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_snd_974_, 0);
lean_dec(v_unused_1167_);
v___x_990_ = v_snd_974_;
v_isShared_991_ = v_isSharedCheck_1166_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snd_988_);
lean_dec(v_snd_974_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1166_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_binderType_992_; lean_object* v_body_993_; uint8_t v___x_994_; 
v_binderType_992_ = lean_ctor_get(v_fst_975_, 1);
v_body_993_ = lean_ctor_get(v_fst_975_, 2);
v___x_994_ = l_Lean_Expr_hasLooseBVars(v_body_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1));
v___x_996_ = l_Lean_Expr_isAppOf(v_snd_988_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_991_ == 0)
{
v___x_999_ = v___x_990_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_snd_988_);
v___x_999_ = v_reuseFailAlloc_1013_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_999_);
v___x_1001_ = v___x_986_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1001_);
v___x_1003_ = v___x_982_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_fst_980_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_1003_);
v___x_1005_ = v___x_978_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1005_);
lean_ctor_set(v___x_970_, 0, v___x_997_);
v___x_1007_ = v___x_970_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
}
}
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Expr_appArg_x21(v_snd_988_);
if (lean_obj_tag(v___x_1014_) == 6)
{
lean_object* v_body_1015_; lean_object* v___x_1016_; 
v_body_1015_ = lean_ctor_get(v___x_1014_, 2);
lean_inc_ref(v_body_1015_);
lean_dec_ref_known(v___x_1014_, 3);
lean_inc_ref(v_binderType_992_);
v___x_1016_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_992_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
lean_inc_ref(v_body_993_);
v___x_1018_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_993_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
lean_inc(v_a_1017_);
v___x_1020_ = l_Lean_Meta_decLevel(v_a_1017_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
lean_inc(v_a_1019_);
v___x_1022_ = l_Lean_Meta_decLevel(v_a_1019_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = lean_box(0);
v_a_1025_ = lean_array_uget_borrowed(v_as_955_, v_i_957_);
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4));
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1023_);
lean_ctor_set(v___x_1027_, 1, v___x_1024_);
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1021_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_mkConst(v___x_1026_, v___x_1028_);
lean_inc(v_a_1025_);
lean_inc_ref(v_body_1015_);
lean_inc_ref(v_body_993_);
lean_inc_ref(v_binderType_992_);
v___x_1030_ = l_Lean_mkApp4(v___x_1029_, v_binderType_992_, v_body_993_, v_body_1015_, v_a_1025_);
lean_inc_ref(v___x_1030_);
v___x_1031_ = l_Lean_Meta_Sym_inferType(v___x_1030_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1091_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1091_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1091_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6));
v___x_1037_ = lean_unsigned_to_nat(3u);
v___x_1038_ = l_Lean_Expr_isAppOfArity(v_a_1032_, v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v_a_1032_);
lean_dec_ref(v___x_1030_);
lean_dec(v_a_1019_);
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1015_);
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_991_ == 0)
{
v___x_1041_ = v___x_990_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_snd_988_);
v___x_1041_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1041_);
v___x_1043_ = v___x_986_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1043_);
v___x_1045_ = v___x_982_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_fst_980_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_1045_);
v___x_1047_ = v___x_978_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1047_);
lean_ctor_set(v___x_970_, 0, v___x_1039_);
v___x_1049_ = v___x_970_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1049_);
v___x_1051_ = v___x_1034_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_inc_ref_n(v_body_993_, 3);
lean_inc_ref_n(v_binderType_992_, 2);
lean_del_object(v___x_1034_);
lean_dec(v_snd_988_);
lean_dec_ref_known(v_fst_975_, 3);
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Lean_Expr_appArg_x21(v_a_1032_);
lean_dec(v_a_1032_);
v___x_1060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8));
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_a_1019_);
lean_ctor_set(v___x_1061_, 1, v___x_1024_);
lean_inc_ref(v___x_1061_);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1017_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_mkConst(v___x_1060_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10));
v___x_1065_ = 0;
v___x_1066_ = l_Lean_Expr_lam___override(v___x_1064_, v_binderType_992_, v_body_993_, v___x_1065_);
lean_inc_n(v_a_1025_, 3);
lean_inc(v_fst_984_);
lean_inc(v_fst_980_);
v___x_1067_ = l_Lean_mkApp6(v___x_1063_, v_binderType_992_, v___x_1066_, v_fst_980_, v_fst_984_, v_fst_976_, v_a_1025_);
v___x_1068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12));
v___x_1069_ = l_Lean_mkConst(v___x_1068_, v___x_1061_);
v___x_1070_ = l_Lean_Expr_app___override(v_fst_980_, v_a_1025_);
v___x_1071_ = l_Lean_Expr_app___override(v_fst_984_, v_a_1025_);
lean_inc_ref(v___x_1059_);
lean_inc_ref(v___x_1070_);
v___x_1072_ = l_Lean_mkApp6(v___x_1069_, v_body_993_, v___x_1070_, v___x_1071_, v___x_1059_, v___x_1067_, v___x_1030_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_body_1015_);
lean_ctor_set(v___x_990_, 0, v_body_993_);
v___x_1074_ = v___x_990_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_body_993_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_body_1015_);
v___x_1074_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1074_);
lean_ctor_set(v___x_986_, 0, v___x_1059_);
v___x_1076_ = v___x_986_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1076_);
lean_ctor_set(v___x_982_, 0, v___x_1070_);
v___x_1078_ = v___x_982_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_1078_);
lean_ctor_set(v___x_978_, 0, v___x_1072_);
v___x_1080_ = v___x_978_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1080_);
lean_ctor_set(v___x_970_, 0, v___x_1058_);
v___x_1082_ = v___x_970_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
size_t v___x_1083_; size_t v___x_1084_; 
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_957_, v___x_1083_);
v_i_957_ = v___x_1084_;
v_b_958_ = v___x_1082_;
goto _start;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v___x_1030_);
lean_dec(v_a_1019_);
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1015_);
lean_del_object(v___x_990_);
lean_dec(v_snd_988_);
lean_del_object(v___x_986_);
lean_dec(v_fst_984_);
lean_del_object(v___x_982_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_dec_ref_known(v_fst_975_, 3);
lean_dec(v_fst_976_);
lean_del_object(v___x_970_);
v_a_1092_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1031_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1031_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1021_);
lean_dec(v_a_1019_);
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1015_);
lean_del_object(v___x_990_);
lean_dec(v_snd_988_);
lean_del_object(v___x_986_);
lean_dec(v_fst_984_);
lean_del_object(v___x_982_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_dec_ref_known(v_fst_975_, 3);
lean_dec(v_fst_976_);
lean_del_object(v___x_970_);
v_a_1100_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1022_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1022_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1019_);
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1015_);
lean_del_object(v___x_990_);
lean_dec(v_snd_988_);
lean_del_object(v___x_986_);
lean_dec(v_fst_984_);
lean_del_object(v___x_982_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_dec_ref_known(v_fst_975_, 3);
lean_dec(v_fst_976_);
lean_del_object(v___x_970_);
v_a_1108_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1020_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1020_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1015_);
lean_del_object(v___x_990_);
lean_dec(v_snd_988_);
lean_del_object(v___x_986_);
lean_dec(v_fst_984_);
lean_del_object(v___x_982_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_dec_ref_known(v_fst_975_, 3);
lean_dec(v_fst_976_);
lean_del_object(v___x_970_);
v_a_1116_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1018_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1018_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_body_1015_);
lean_del_object(v___x_990_);
lean_dec(v_snd_988_);
lean_del_object(v___x_986_);
lean_dec(v_fst_984_);
lean_del_object(v___x_982_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_dec_ref_known(v_fst_975_, 3);
lean_dec(v_fst_976_);
lean_del_object(v___x_970_);
v_a_1124_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1016_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1016_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec_ref(v___x_1014_);
v___x_1132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_991_ == 0)
{
v___x_1134_ = v___x_990_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_988_);
v___x_1134_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1134_);
v___x_1136_ = v___x_986_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1136_);
v___x_1138_ = v___x_982_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_fst_980_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_1138_);
v___x_1140_ = v___x_978_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1140_);
lean_ctor_set(v___x_970_, 0, v___x_1132_);
v___x_1142_ = v___x_970_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_991_ == 0)
{
v___x_1151_ = v___x_990_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_snd_988_);
v___x_1151_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1151_);
v___x_1153_ = v___x_986_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1153_);
v___x_1155_ = v___x_982_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_fst_980_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_1155_);
v___x_1157_ = v___x_978_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1157_);
lean_ctor_set(v___x_970_, 0, v___x_1149_);
v___x_1159_ = v___x_970_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_fst_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1213_; 
v_fst_1174_ = lean_ctor_get(v_snd_968_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_snd_968_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_snd_968_, 1);
lean_dec(v_unused_1214_);
v___x_1176_ = v_snd_968_;
v_isShared_1177_ = v_isSharedCheck_1213_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_fst_1174_);
lean_dec(v_snd_968_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1213_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_fst_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1211_; 
v_fst_1178_ = lean_ctor_get(v_snd_972_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_snd_972_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_snd_972_, 1);
lean_dec(v_unused_1212_);
v___x_1180_ = v_snd_972_;
v_isShared_1181_ = v_isSharedCheck_1211_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_fst_1178_);
lean_dec(v_snd_972_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1211_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_fst_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1209_; 
v_fst_1182_ = lean_ctor_get(v_snd_973_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_snd_973_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_snd_973_, 1);
lean_dec(v_unused_1210_);
v___x_1184_ = v_snd_973_;
v_isShared_1185_ = v_isSharedCheck_1209_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_fst_1182_);
lean_dec(v_snd_973_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1209_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_snd_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1207_; 
v_snd_1186_ = lean_ctor_get(v_snd_974_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_snd_974_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_snd_974_, 0);
lean_dec(v_unused_1208_);
v___x_1188_ = v_snd_974_;
v_isShared_1189_ = v_isSharedCheck_1207_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snd_1186_);
lean_dec(v_snd_974_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1207_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1189_ == 0)
{
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_snd_1186_);
v___x_1192_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 1, v___x_1192_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_fst_1182_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1194_);
v___x_1196_ = v___x_1180_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_fst_1178_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1196_);
v___x_1198_ = v___x_1176_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1198_);
lean_ctor_set(v___x_970_, 0, v___x_1190_);
v___x_1200_ = v___x_970_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object* v_as_1217_, lean_object* v_sz_1218_, lean_object* v_i_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
size_t v_sz_boxed_1228_; size_t v_i_boxed_1229_; lean_object* v_res_1230_; 
v_sz_boxed_1228_ = lean_unbox_usize(v_sz_1218_);
lean_dec(v_sz_1218_);
v_i_boxed_1229_ = lean_unbox_usize(v_i_1219_);
lean_dec(v_i_1219_);
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0(v_as_1217_, v_sz_boxed_1228_, v_i_boxed_1229_, v_b_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v_as_1217_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = l_Lean_Expr_bvar___override(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = l_Lean_Level_succ___override(v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__7);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_mkSort(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(lean_object* v_goal_1255_, lean_object* v_target_1256_, lean_object* v_pre_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
uint8_t v___y_1266_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11));
v___x_1406_ = l_Lean_Expr_isAppOf(v_pre_1257_, v___x_1405_);
if (v___x_1406_ == 0)
{
v___y_1266_ = v___x_1406_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_unsigned_to_nat(2u);
v___x_1408_ = l_Lean_Expr_getAppNumArgs(v_pre_1257_);
v___x_1409_ = lean_nat_dec_lt(v___x_1407_, v___x_1408_);
lean_dec(v___x_1408_);
v___y_1266_ = v___x_1409_;
goto v___jp_1265_;
}
v___jp_1265_:
{
if (v___y_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
else
{
lean_object* v_dummy_1269_; lean_object* v_nargs_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_args_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_dummy_1269_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_1270_ = l_Lean_Expr_getAppNumArgs(v_pre_1257_);
lean_inc(v_nargs_1270_);
v___x_1271_ = lean_mk_array(v_nargs_1270_, v_dummy_1269_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_sub(v_nargs_1270_, v___x_1272_);
lean_dec(v_nargs_1270_);
lean_inc_ref(v_pre_1257_);
v_args_1274_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pre_1257_, v___x_1271_, v___x_1273_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_args_1274_);
v___x_1277_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref(v_args_1274_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_nat_dec_lt(v___x_1272_, v___x_1276_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v_args_1274_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_curTop_1286_; lean_object* v___x_1287_; 
v___x_1283_ = lean_array_fget(v_args_1274_, v___x_1275_);
v___x_1284_ = lean_array_fget(v_args_1274_, v___x_1272_);
v___x_1285_ = l_Lean_Expr_getAppFn(v_pre_1257_);
lean_inc(v___x_1284_);
lean_inc_n(v___x_1283_, 2);
v_curTop_1286_ = l_Lean_mkAppB(v___x_1285_, v___x_1283_, v___x_1284_);
v___x_1287_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_1283_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; size_t v_sz_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1288_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = l_Lean_mkConst(v___x_1289_, v___x_1291_);
lean_inc_ref_n(v_curTop_1286_, 2);
lean_inc(v___x_1283_);
v___x_1293_ = l_Lean_mkAppB(v___x_1292_, v___x_1283_, v_curTop_1286_);
v___x_1294_ = lean_unsigned_to_nat(2u);
v___x_1295_ = l_Array_extract___redArg(v_args_1274_, v___x_1294_, v___x_1276_);
lean_dec_ref(v_args_1274_);
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1283_);
lean_ctor_set(v___x_1297_, 1, v___x_1284_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_curTop_1286_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_curTop_1286_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1293_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1296_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v_sz_1302_ = lean_array_size(v___x_1295_);
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f_spec__0(v___x_1295_, v_sz_1302_, v___x_1303_, v___x_1301_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec_ref(v___x_1295_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1388_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1388_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1388_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_fst_1309_; 
v_fst_1309_ = lean_ctor_get(v_a_1305_, 0);
if (lean_obj_tag(v_fst_1309_) == 0)
{
lean_object* v_snd_1310_; lean_object* v_nargs_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_snd_1310_ = lean_ctor_get(v_a_1305_, 1);
lean_inc(v_snd_1310_);
lean_dec(v_a_1305_);
v_nargs_1311_ = l_Lean_Expr_getAppNumArgs(v_target_1256_);
lean_inc(v_nargs_1311_);
v___x_1312_ = lean_mk_array(v_nargs_1311_, v_dummy_1269_);
v___x_1313_ = lean_nat_sub(v_nargs_1311_, v___x_1272_);
lean_dec(v_nargs_1311_);
lean_inc_ref(v_target_1256_);
v___x_1314_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_1256_, v___x_1312_, v___x_1313_);
v___x_1315_ = lean_array_get_size(v___x_1314_);
v___x_1316_ = lean_nat_dec_lt(v___x_1275_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1314_);
lean_dec(v_snd_1310_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1296_);
v___x_1318_ = v___x_1307_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1296_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_nat_dec_lt(v___x_1272_, v___x_1315_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1322_; 
lean_dec_ref(v___x_1314_);
lean_dec(v_snd_1310_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1296_);
v___x_1322_ = v___x_1307_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1296_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_unsigned_to_nat(3u);
v___x_1325_ = lean_nat_dec_lt(v___x_1324_, v___x_1315_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1327_; 
lean_dec_ref(v___x_1314_);
lean_dec(v_snd_1310_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1296_);
v___x_1327_ = v___x_1307_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1296_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_del_object(v___x_1307_);
v___x_1329_ = lean_array_fget(v___x_1314_, v___x_1275_);
lean_inc(v___x_1329_);
v___x_1330_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_1329_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_snd_1331_; lean_object* v_snd_1332_; lean_object* v_a_1333_; lean_object* v_fst_1334_; lean_object* v_fst_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1374_; 
v_snd_1331_ = lean_ctor_get(v_snd_1310_, 1);
v_snd_1332_ = lean_ctor_get(v_snd_1331_, 1);
lean_inc(v_snd_1332_);
v_a_1333_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1330_, 1);
v_fst_1334_ = lean_ctor_get(v_snd_1310_, 0);
lean_inc(v_fst_1334_);
lean_dec(v_snd_1310_);
v_fst_1335_ = lean_ctor_get(v_snd_1332_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_snd_1332_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_snd_1332_, 1);
lean_dec(v_unused_1375_);
v___x_1337_ = v_snd_1332_;
v_isShared_1338_ = v_isSharedCheck_1374_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_fst_1335_);
lean_dec(v_snd_1332_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1374_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1339_ = lean_array_fget(v___x_1314_, v___x_1272_);
v___x_1340_ = lean_array_fget(v___x_1314_, v___x_1324_);
lean_dec_ref(v___x_1314_);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__3));
v___x_1342_ = l_Lean_Expr_getAppFn(v_target_1256_);
lean_dec_ref(v_target_1256_);
v___x_1343_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__4);
lean_inc(v___x_1340_);
lean_inc(v___x_1339_);
lean_inc_n(v___x_1329_, 2);
lean_inc_ref(v___x_1342_);
v___x_1344_ = l_Lean_mkApp4(v___x_1342_, v___x_1329_, v___x_1339_, v___x_1343_, v___x_1340_);
v___x_1345_ = 0;
v___x_1346_ = l_Lean_Expr_lam___override(v___x_1341_, v___x_1329_, v___x_1344_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__6));
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__8);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
lean_ctor_set(v___x_1337_, 1, v___x_1348_);
lean_ctor_set(v___x_1337_, 0, v_a_1333_);
v___x_1350_ = v___x_1337_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1333_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1351_ = l_Lean_mkConst(v___x_1347_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__9);
lean_inc(v_fst_1335_);
lean_inc(v___x_1329_);
v___x_1353_ = l_Lean_mkApp6(v___x_1351_, v___x_1329_, v___x_1352_, v_pre_1257_, v_fst_1335_, v___x_1346_, v_fst_1334_);
v___x_1354_ = l_Lean_mkApp4(v___x_1342_, v___x_1329_, v___x_1339_, v_fst_1335_, v___x_1340_);
v___x_1355_ = l_Lean_MVarId_replaceTargetEq(v_goal_1255_, v___x_1354_, v___x_1353_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1364_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1355_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1355_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1314_);
lean_dec(v_snd_1310_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v_a_1376_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1330_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1330_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; 
lean_inc_ref(v_fst_1309_);
lean_dec(v_a_1305_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v_val_1384_ = lean_ctor_get(v_fst_1309_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v_fst_1309_, 1);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_val_1384_);
v___x_1386_ = v___x_1307_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_val_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v_a_1389_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1304_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1304_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_curTop_1286_);
lean_dec(v___x_1284_);
lean_dec(v___x_1283_);
lean_dec_ref(v_args_1274_);
lean_dec_ref(v_pre_1257_);
lean_dec_ref(v_target_1256_);
lean_dec(v_goal_1255_);
v_a_1397_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1287_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1287_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object* v_goal_1410_, lean_object* v_target_1411_, lean_object* v_pre_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(v_goal_1410_, v_target_1411_, v_pre_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1420_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__3));
v___x_1430_ = l_Lean_stringToMessageData(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(lean_object* v_goal_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
lean_inc(v_goal_1431_);
v___x_1440_ = l_Lean_MVarId_getType(v_goal_1431_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1513_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1513_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1513_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__2));
v___x_1446_ = lean_unsigned_to_nat(4u);
v___x_1447_ = l_Lean_Expr_isAppOfArity(v_a_1441_, v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_a_1441_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_goal_1431_);
v___x_1449_ = v___x_1443_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_goal_1431_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = l_Lean_Expr_appFn_x21(v_a_1441_);
lean_dec(v_a_1441_);
v___x_1452_ = l_Lean_Expr_appFn_x21(v___x_1451_);
v___x_1453_ = l_Lean_Expr_appFn_x21(v___x_1452_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = l_Lean_Expr_appArg_x21(v___x_1453_);
lean_dec_ref(v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 3)
{
lean_object* v_u_1455_; 
v_u_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_u_1455_);
lean_dec_ref_known(v___x_1454_, 1);
if (lean_obj_tag(v_u_1455_) == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_del_object(v___x_1443_);
v___x_1456_ = l_Lean_Expr_appArg_x21(v___x_1451_);
lean_dec_ref(v___x_1451_);
v___x_1457_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1456_, v_a_1436_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1498_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1498_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1498_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f___closed__11));
v___x_1463_ = l_Lean_Expr_isAppOf(v_a_1458_, v___x_1462_);
lean_dec(v_a_1458_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1465_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_goal_1431_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_goal_1431_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
else
{
lean_object* v_backwardRules_1467_; lean_object* v_elimPre_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1460_);
v_backwardRules_1467_ = lean_ctor_get(v_a_1432_, 0);
v_elimPre_1468_ = lean_ctor_get(v_backwardRules_1467_, 5);
lean_inc_ref(v_elimPre_1468_);
lean_inc(v_goal_1431_);
v___x_1469_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1431_, v_elimPre_1468_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1489_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1489_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1489_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; 
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_mvarIds_1483_; 
v_mvarIds_1483_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_mvarIds_1483_);
lean_dec_ref_known(v_a_1470_, 1);
if (lean_obj_tag(v_mvarIds_1483_) == 1)
{
lean_object* v_tail_1484_; 
v_tail_1484_ = lean_ctor_get(v_mvarIds_1483_, 1);
if (lean_obj_tag(v_tail_1484_) == 0)
{
lean_object* v_head_1485_; lean_object* v___x_1487_; 
lean_dec(v_goal_1431_);
v_head_1485_ = lean_ctor_get(v_mvarIds_1483_, 0);
lean_inc(v_head_1485_);
lean_dec_ref_known(v_mvarIds_1483_, 2);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v_head_1485_);
v___x_1487_ = v___x_1472_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_head_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_1483_, 2);
lean_del_object(v___x_1472_);
v___y_1475_ = v_a_1435_;
v___y_1476_ = v_a_1436_;
v___y_1477_ = v_a_1437_;
v___y_1478_ = v_a_1438_;
goto v___jp_1474_;
}
}
else
{
lean_dec(v_mvarIds_1483_);
lean_del_object(v___x_1472_);
v___y_1475_ = v_a_1435_;
v___y_1476_ = v_a_1436_;
v___y_1477_ = v_a_1437_;
v___y_1478_ = v_a_1438_;
goto v___jp_1474_;
}
}
else
{
lean_del_object(v___x_1472_);
lean_dec(v_a_1470_);
v___y_1475_ = v_a_1435_;
v___y_1476_ = v_a_1436_;
v___y_1477_ = v_a_1437_;
v___y_1478_ = v_a_1438_;
goto v___jp_1474_;
}
v___jp_1474_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___closed__4);
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_goal_1431_);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple_spec__0___redArg(v___x_1481_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_goal_1431_);
v_a_1490_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1469_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1469_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_goal_1431_);
v_a_1499_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1457_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1457_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v___x_1508_; 
lean_dec(v_u_1455_);
lean_dec_ref(v___x_1451_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_goal_1431_);
v___x_1508_ = v___x_1443_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_goal_1431_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v___x_1511_; 
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___x_1451_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_goal_1431_);
v___x_1511_ = v___x_1443_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_goal_1431_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_goal_1431_);
v_a_1514_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1440_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1440_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg___boxed(lean_object* v_goal_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(v_goal_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre(lean_object* v_goal_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(v_goal_1532_, v_a_1533_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___boxed(lean_object* v_goal_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre(v_goal_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1559_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
}
#ifdef __cplusplus
}
#endif
