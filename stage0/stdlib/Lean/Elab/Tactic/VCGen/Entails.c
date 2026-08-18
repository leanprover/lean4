// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Entails
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.EPost public import Lean.Elab.Tactic.VCGen.RuleCache public import Lean.Elab.Tactic.VCGen.Util public import Lean.Meta.Sym.Util import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS
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
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps;
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_peelEPostTailChain(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Failed to unfold the Triple target of "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introPre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to apply precondition intro rule to "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__1;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_introPre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_introPre___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_introPre___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introPre___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to intro the lifted precondition of "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introPre___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 91, 36, 233, 42, 127, 239, 103)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 138, 171, 54, 136, 21, 182, 106)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value_aux_3),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 123, 42, 193, 46, 33, 120, 28)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 37, .m_data = "Failed to strip the `⊤ ⊑` wrapper of "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object* v_goal_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_backwardRules_63_; lean_object* v_tripleIntro_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_backwardRules_63_ = lean_ctor_get(v_a_51_, 0);
v_tripleIntro_64_ = lean_ctor_get(v_backwardRules_63_, 0);
v___x_65_ = lean_box(0);
lean_inc(v_goal_50_);
lean_inc_ref(v_tripleIntro_64_);
v___x_66_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_tripleIntro_64_, v_goal_50_, v___x_65_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
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
v___x_83_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1, &l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v_goal_50_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_85_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___boxed(lean_object* v_goal_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_Tactic_VCGen_unfoldTriple(v_goal_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(lean_object* v_00_u03b1_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v_msg_117_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___boxed(lean_object* v_00_u03b1_131_, lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(v_00_u03b1_131_, v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object* v_mvarId_174_, lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
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
v___f_188_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed), 13, 8);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object* v_00_u03b1_213_, lean_object* v_mvarId_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_214_, v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object* v_00_u03b1_229_, lean_object* v_mvarId_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(v_00_u03b1_229_, v_mvarId_230_, v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___lam__0(lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___lam__0___boxed(lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Elab_Tactic_VCGen_introPre___lam__0(v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
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
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__0));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__4));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object* v_rule_281_, lean_object* v_goal_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
lean_inc(v_goal_282_);
v___x_296_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_281_, v_goal_282_, v___x_295_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
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
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__2));
v___x_317_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_head_312_, v___x_316_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___f_319_; lean_object* v___x_320_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_n(v_a_318_, 2);
lean_dec_ref_known(v___x_317_, 1);
v___f_319_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__3));
v___x_320_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_a_318_, v___f_319_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
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
v___x_334_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introPre___closed__5, &l_Lean_Elab_Tactic_VCGen_introPre___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__5);
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
v___x_339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_338_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
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
v___x_303_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introPre___closed__1, &l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_goal_282_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object* v_rule_370_, lean_object* v_goal_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Tactic_VCGen_introPre(v_rule_370_, v_goal_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_385_, lean_object* v_a_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
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
v___x_400_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref_known(v___x_400_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_418_, lean_object* v_a_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_f_418_, v_a_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0(lean_object* v_args_428_, lean_object* v_endIdx_429_, lean_object* v_b_430_, lean_object* v_i_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
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
v___x_447_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_b_430_, v___x_446_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0___boxed(lean_object* v_args_453_, lean_object* v_endIdx_454_, lean_object* v_b_455_, lean_object* v_i_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0(v_args_453_, v_endIdx_454_, v_b_455_, v_i_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0(lean_object* v_f_470_, lean_object* v_args_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_array_get_size(v_args_471_);
v___x_486_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0(v_args_471_, v___x_485_, v_f_470_, v___x_484_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0___boxed(lean_object* v_f_487_, lean_object* v_args_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0(v_f_487_, v_args_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1(lean_object* v_target_520_, lean_object* v_00_u03b1_521_, lean_object* v_inst_522_, lean_object* v_pre_523_, lean_object* v_goal_524_, lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
if (lean_obj_tag(v_x_525_) == 5)
{
lean_object* v_fn_540_; lean_object* v_arg_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_fn_540_ = lean_ctor_get(v_x_525_, 0);
lean_inc_ref(v_fn_540_);
v_arg_541_ = lean_ctor_get(v_x_525_, 1);
lean_inc_ref(v_arg_541_);
lean_dec_ref_known(v_x_525_, 2);
v___x_542_ = lean_array_set(v_x_526_, v_x_527_, v_arg_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_sub(v_x_527_, v___x_543_);
lean_dec(v_x_527_);
v_x_525_ = v_fn_540_;
v_x_526_ = v___x_542_;
v_x_527_ = v___x_544_;
goto _start;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
lean_dec(v_x_527_);
v___x_546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__5));
v___x_547_ = l_Lean_Expr_isConstOf(v_x_525_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_x_526_);
lean_dec_ref(v_x_525_);
lean_dec(v_goal_524_);
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
lean_dec_ref(v_target_520_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_array_get_size(v_x_526_);
v___x_552_ = lean_nat_dec_lt(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v_x_526_);
lean_dec_ref(v_x_525_);
lean_dec(v_goal_524_);
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
lean_dec_ref(v_target_520_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_array_fget_borrowed(v_x_526_, v___x_550_);
v___x_556_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___closed__9));
v___x_557_ = l_Lean_Expr_isAppOf(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_562_; 
lean_dec_ref(v_x_525_);
v___x_558_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_555_);
v___x_559_ = l_Lean_Elab_Tactic_VCGen_peelEPostTailChain(v___x_555_, v___x_558_);
v_fst_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_fst_560_);
v_snd_561_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_561_);
lean_dec_ref(v___x_559_);
v___x_562_ = l_Lean_Elab_Tactic_VCGen_mkEPostAtIndex(v_fst_560_, v_snd_561_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_625_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_625_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_625_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_625_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_620_; 
lean_del_object(v___x_565_);
v_val_567_ = lean_ctor_get(v_a_563_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_620_ == 0)
{
v___x_569_ = v_a_563_;
v_isShared_570_ = v_isSharedCheck_620_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_val_567_);
lean_dec(v_a_563_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_620_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(3u);
v___x_572_ = l_Array_extract___redArg(v_x_526_, v___x_571_, v___x_551_);
lean_dec_ref(v_x_526_);
v___x_573_ = l_Lean_Meta_Sym_betaS(v_val_567_, v___x_572_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = l_Lean_Expr_getAppFn(v_target_520_);
lean_dec_ref(v_target_520_);
v___x_576_ = lean_unsigned_to_nat(4u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_array_push(v___x_577_, v_00_u03b1_521_);
v___x_579_ = lean_array_push(v___x_578_, v_inst_522_);
v___x_580_ = lean_array_push(v___x_579_, v_pre_523_);
v___x_581_ = lean_array_push(v___x_580_, v_a_574_);
v___x_582_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0(v___x_575_, v___x_581_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec_ref(v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_524_, v_a_583_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_595_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_595_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_a_585_);
v___x_590_ = v___x_569_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_del_object(v___x_569_);
v_a_596_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_584_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_584_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_569_);
lean_dec(v_goal_524_);
v_a_604_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_582_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_582_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_del_object(v___x_569_);
lean_dec(v_goal_524_);
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
lean_dec_ref(v_target_520_);
v_a_612_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_573_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_573_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_a_563_);
lean_dec_ref(v_x_526_);
lean_dec(v_goal_524_);
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
lean_dec_ref(v_target_520_);
v___x_621_ = lean_box(0);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_621_);
v___x_623_ = v___x_565_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_x_526_);
lean_dec(v_goal_524_);
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
lean_dec_ref(v_target_520_);
v_a_626_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_562_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_562_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_634_; 
lean_dec_ref(v_pre_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_00_u03b1_521_);
v___x_634_ = l_Lean_Elab_Tactic_VCGen_replaceEPostHeadBot_x3f(v_goal_524_, v_target_520_, v_x_525_, v_x_526_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec_ref(v_x_526_);
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_target_635_ = _args[0];
lean_object* v_00_u03b1_636_ = _args[1];
lean_object* v_inst_637_ = _args[2];
lean_object* v_pre_638_ = _args[3];
lean_object* v_goal_639_ = _args[4];
lean_object* v_x_640_ = _args[5];
lean_object* v_x_641_ = _args[6];
lean_object* v_x_642_ = _args[7];
lean_object* v___y_643_ = _args[8];
lean_object* v___y_644_ = _args[9];
lean_object* v___y_645_ = _args[10];
lean_object* v___y_646_ = _args[11];
lean_object* v___y_647_ = _args[12];
lean_object* v___y_648_ = _args[13];
lean_object* v___y_649_ = _args[14];
lean_object* v___y_650_ = _args[15];
lean_object* v___y_651_ = _args[16];
lean_object* v___y_652_ = _args[17];
lean_object* v___y_653_ = _args[18];
lean_object* v___y_654_ = _args[19];
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1(v_target_635_, v_00_u03b1_636_, v_inst_637_, v_pre_638_, v_goal_639_, v_x_640_, v_x_641_, v_x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_655_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0(void){
_start:
{
lean_object* v___x_656_; lean_object* v_dummy_657_; 
v___x_656_ = lean_box(0);
v_dummy_657_ = l_Lean_Expr_sort___override(v___x_656_);
return v_dummy_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(lean_object* v_goal_658_, lean_object* v_target_659_, lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_pre_662_, lean_object* v_rhs_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_dummy_676_; lean_object* v_nargs_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_dummy_676_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_677_ = l_Lean_Expr_getAppNumArgs(v_rhs_663_);
lean_inc(v_nargs_677_);
v___x_678_ = lean_mk_array(v_nargs_677_, v_dummy_676_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_sub(v_nargs_677_, v___x_679_);
lean_dec(v_nargs_677_);
v___x_681_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__1(v_target_659_, v_00_u03b1_660_, v_inst_661_, v_pre_662_, v_goal_658_, v_rhs_663_, v___x_678_, v___x_680_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___boxed(lean_object** _args){
lean_object* v_goal_682_ = _args[0];
lean_object* v_target_683_ = _args[1];
lean_object* v_00_u03b1_684_ = _args[2];
lean_object* v_inst_685_ = _args[3];
lean_object* v_pre_686_ = _args[4];
lean_object* v_rhs_687_ = _args[5];
lean_object* v_a_688_ = _args[6];
lean_object* v_a_689_ = _args[7];
lean_object* v_a_690_ = _args[8];
lean_object* v_a_691_ = _args[9];
lean_object* v_a_692_ = _args[10];
lean_object* v_a_693_ = _args[11];
lean_object* v_a_694_ = _args[12];
lean_object* v_a_695_ = _args[13];
lean_object* v_a_696_ = _args[14];
lean_object* v_a_697_ = _args[15];
lean_object* v_a_698_ = _args[16];
lean_object* v_a_699_ = _args[17];
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(v_goal_682_, v_target_683_, v_00_u03b1_684_, v_inst_685_, v_pre_686_, v_rhs_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(lean_object* v_f_701_, lean_object* v_a_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___redArg(v_f_701_, v_a_702_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_716_, lean_object* v_a_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f_spec__0_spec__0_spec__1(v_f_716_, v_a_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object* v_goal_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
if (lean_obj_tag(v_x_749_) == 5)
{
lean_object* v_fn_757_; lean_object* v_arg_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_fn_757_ = lean_ctor_get(v_x_749_, 0);
lean_inc_ref(v_fn_757_);
v_arg_758_ = lean_ctor_get(v_x_749_, 1);
lean_inc_ref(v_arg_758_);
lean_dec_ref_known(v_x_749_, 2);
v___x_759_ = lean_array_set(v_x_750_, v_x_751_, v_arg_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_sub(v_x_751_, v___x_760_);
lean_dec(v_x_751_);
v_x_749_ = v_fn_757_;
v_x_750_ = v___x_759_;
v_x_751_ = v___x_761_;
goto _start;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
lean_dec(v_x_751_);
v___x_763_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2));
v___x_764_ = l_Lean_Expr_isConstOf(v_x_749_, v___x_763_);
lean_dec_ref(v_x_749_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = lean_array_get_size(v_x_750_);
v___x_769_ = lean_nat_dec_lt(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_fget_borrowed(v_x_750_, v___x_767_);
v___x_773_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4));
v___x_774_ = l_Lean_Expr_isAppOf(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(3u);
v___x_778_ = lean_nat_dec_lt(v___x_777_, v___x_768_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_781_ = lean_array_fget_borrowed(v_x_750_, v___x_777_);
v___x_782_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6));
v___x_783_ = l_Lean_Expr_appArg_x21(v___x_772_);
v___x_784_ = lean_mk_empty_array_with_capacity(v___x_767_);
v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
lean_inc(v___x_781_);
v___x_786_ = lean_array_push(v___x_785_, v___x_781_);
v___x_787_ = l_Lean_Meta_mkAppM(v___x_782_, v___x_786_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
lean_inc(v_goal_748_);
v___x_789_ = l_Lean_MVarId_getType(v_goal_748_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_dummy_795_; lean_object* v_nargs_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unsigned_to_nat(4u);
v___x_792_ = l_Array_extract___redArg(v_x_750_, v___x_791_, v___x_768_);
lean_dec_ref(v_x_750_);
v___x_793_ = l_Lean_mkAppN(v_a_788_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = l_Lean_Expr_getAppFn(v_a_790_);
v_dummy_795_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_796_ = l_Lean_Expr_getAppNumArgs(v_a_790_);
lean_inc(v_nargs_796_);
v___x_797_ = lean_mk_array(v_nargs_796_, v_dummy_795_);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_sub(v_nargs_796_, v___x_798_);
lean_dec(v_nargs_796_);
v___x_800_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_790_, v___x_797_, v___x_799_);
lean_inc_ref(v___x_793_);
v___x_801_ = lean_array_set(v___x_800_, v___x_777_, v___x_793_);
v___x_802_ = l_Lean_mkAppN(v___x_794_, v___x_801_);
lean_dec_ref(v___x_801_);
v___x_803_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_748_, v___x_802_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_804_);
lean_ctor_set(v___x_808_, 1, v___x_793_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v___x_793_);
v_a_814_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_803_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_803_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_788_);
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v_a_822_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_789_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_789_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_x_750_);
lean_dec(v_goal_748_);
v_a_830_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_787_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_787_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object* v_goal_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_838_, v_x_839_, v_x_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object* v_goal_848_, lean_object* v_rhs_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_dummy_862_; lean_object* v_nargs_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_dummy_862_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_863_ = l_Lean_Expr_getAppNumArgs(v_rhs_849_);
lean_inc(v_nargs_863_);
v___x_864_ = lean_mk_array(v_nargs_863_, v_dummy_862_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_sub(v_nargs_863_, v___x_865_);
lean_dec(v_nargs_863_);
v___x_867_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_848_, v_rhs_849_, v___x_864_, v___x_866_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object* v_goal_868_, lean_object* v_rhs_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_868_, v_rhs_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object* v_goal_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_883_, v_x_884_, v_x_885_, v_x_886_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object* v_goal_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(v_goal_900_, v_x_901_, v_x_902_, v_x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_917_, lean_object* v_query_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_zero_922_; uint8_t v_isZero_923_; 
v_zero_922_ = lean_unsigned_to_nat(0u);
v_isZero_923_ = lean_nat_dec_eq(v_x_920_, v_zero_922_);
if (v_isZero_923_ == 1)
{
lean_dec(v_x_921_);
lean_dec(v_x_920_);
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v___x_924_; 
v___x_924_ = lean_box(2);
return v___x_924_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_val_925_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v_x_919_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v_x_919_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_keyArray_933_; lean_object* v_valueArray_934_; lean_object* v___x_935_; uint8_t v_isSome_936_; 
v_keyArray_933_ = lean_ctor_get(v_m_917_, 1);
v_valueArray_934_ = lean_ctor_get(v_m_917_, 2);
v___x_935_ = lean_array_fget_borrowed(v_keyArray_933_, v_x_921_);
v_isSome_936_ = lean_noption_is_some(v___x_935_);
if (v_isSome_936_ == 0)
{
lean_dec(v_x_920_);
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_x_921_);
return v___x_937_;
}
else
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_x_921_);
v_val_938_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v_x_919_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v_x_919_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_val_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_one_946_; lean_object* v_n_947_; lean_object* v___y_949_; 
v_one_946_ = lean_unsigned_to_nat(1u);
v_n_947_ = lean_nat_sub(v_x_920_, v_one_946_);
lean_dec(v_x_920_);
if (v_isSome_936_ == 0)
{
goto v___jp_955_;
}
else
{
lean_object* v___x_957_; uint8_t v_isSome_958_; 
v___x_957_ = lean_array_fget_borrowed(v_valueArray_934_, v_x_921_);
v_isSome_958_ = lean_noption_is_some(v___x_957_);
if (v_isSome_958_ == 0)
{
goto v___jp_955_;
}
else
{
lean_object* v_val_959_; uint8_t v___x_960_; 
lean_inc(v___x_935_);
v_val_959_ = lean_noption_get(v___x_935_);
v___x_960_ = lean_name_eq(v_val_959_, v_query_918_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_dec(v_val_959_);
v___x_961_ = lean_array_get_size(v_keyArray_933_);
v___x_962_ = lean_nat_add(v_x_921_, v_one_946_);
lean_dec(v_x_921_);
v___x_963_ = lean_nat_dec_lt(v___x_962_, v___x_961_);
if (v___x_963_ == 0)
{
lean_dec(v___x_962_);
v_x_920_ = v_n_947_;
v_x_921_ = v_zero_922_;
goto _start;
}
else
{
v_x_920_ = v_n_947_;
v_x_921_ = v___x_962_;
goto _start;
}
}
else
{
lean_object* v_val_966_; lean_object* v___x_967_; 
lean_dec(v_n_947_);
lean_dec(v_x_919_);
lean_inc(v___x_957_);
v_val_966_ = lean_noption_get(v___x_957_);
v___x_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_967_, 0, v_x_921_);
lean_ctor_set(v___x_967_, 1, v_val_959_);
lean_ctor_set(v___x_967_, 2, v_val_966_);
return v___x_967_;
}
}
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_array_get_size(v_keyArray_933_);
v___x_951_ = lean_nat_add(v_x_921_, v_one_946_);
lean_dec(v_x_921_);
v___x_952_ = lean_nat_dec_lt(v___x_951_, v___x_950_);
if (v___x_952_ == 0)
{
lean_dec(v___x_951_);
v_x_919_ = v___y_949_;
v_x_920_ = v_n_947_;
v_x_921_ = v_zero_922_;
goto _start;
}
else
{
v_x_919_ = v___y_949_;
v_x_920_ = v_n_947_;
v_x_921_ = v___x_951_;
goto _start;
}
}
v___jp_955_:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v___x_956_; 
lean_inc(v_x_921_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_x_921_);
v___y_949_ = v___x_956_;
goto v___jp_948_;
}
else
{
v___y_949_ = v_x_919_;
goto v___jp_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_968_, lean_object* v_query_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_m_968_, v_query_969_, v_x_970_, v_x_971_, v_x_972_);
lean_dec(v_query_969_);
lean_dec_ref(v_m_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_m_974_, lean_object* v_query_975_){
_start:
{
lean_object* v_keyArray_976_; lean_object* v___x_977_; uint64_t v___y_979_; 
v_keyArray_976_ = lean_ctor_get(v_m_974_, 1);
v___x_977_ = lean_array_get_size(v_keyArray_976_);
if (lean_obj_tag(v_query_975_) == 0)
{
uint64_t v___x_994_; 
v___x_994_ = 1723ULL;
v___y_979_ = v___x_994_;
goto v___jp_978_;
}
else
{
uint64_t v_hash_995_; 
v_hash_995_ = lean_ctor_get_uint64(v_query_975_, sizeof(void*)*2);
v___y_979_ = v_hash_995_;
goto v___jp_978_;
}
v___jp_978_:
{
uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v_fold_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; size_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_980_ = 32ULL;
v___x_981_ = lean_uint64_shift_right(v___y_979_, v___x_980_);
v_fold_982_ = lean_uint64_xor(v___y_979_, v___x_981_);
v___x_983_ = 16ULL;
v___x_984_ = lean_uint64_shift_right(v_fold_982_, v___x_983_);
v___x_985_ = lean_uint64_xor(v_fold_982_, v___x_984_);
v___x_986_ = lean_uint64_to_usize(v___x_985_);
v___x_987_ = lean_usize_of_nat(v___x_977_);
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_sub(v___x_987_, v___x_988_);
v___x_990_ = lean_usize_land(v___x_986_, v___x_989_);
v___x_991_ = lean_usize_to_nat(v___x_990_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_m_974_, v_query_975_, v___x_992_, v___x_977_, v___x_991_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_996_, lean_object* v_query_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg(v_m_996_, v_query_997_);
lean_dec(v_query_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object* v_m_999_, lean_object* v_query_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg(v_m_999_, v_query_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_index_1002_; lean_object* v_key_1003_; lean_object* v_value_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_index_1002_ = lean_ctor_get(v___x_1001_, 0);
v_key_1003_ = lean_ctor_get(v___x_1001_, 1);
v_value_1004_ = lean_ctor_get(v___x_1001_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1001_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_value_1004_);
lean_inc(v_key_1003_);
lean_inc(v_index_1002_);
lean_dec(v___x_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_index_1002_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_key_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_value_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v___x_1012_; 
lean_dec(v___x_1001_);
v___x_1012_ = lean_box(1);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_m_1013_, lean_object* v_query_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_m_1013_, v_query_1014_);
lean_dec(v_query_1014_);
lean_dec_ref(v_m_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object* v_m_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_m_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_value_1019_; lean_object* v___x_1020_; 
v_value_1019_ = lean_ctor_get(v___x_1018_, 2);
lean_inc(v_value_1019_);
lean_dec_ref_known(v___x_1018_, 3);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_value_1019_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object* v_m_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_m_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object* v_goal_1025_, lean_object* v_rhs_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
lean_inc_ref(v_rhs_1026_);
lean_inc(v_goal_1025_);
v___x_1039_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_1025_, v_rhs_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1103_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1103_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1103_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_fst_1045_; lean_object* v_snd_1046_; 
if (lean_obj_tag(v_a_1040_) == 0)
{
v_fst_1045_ = v_goal_1025_;
v_snd_1046_ = v_rhs_1026_;
goto v___jp_1044_;
}
else
{
lean_object* v_val_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; 
lean_dec_ref(v_rhs_1026_);
lean_dec(v_goal_1025_);
v_val_1100_ = lean_ctor_get(v_a_1040_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v_a_1040_, 1);
v_fst_1101_ = lean_ctor_get(v_val_1100_, 0);
lean_inc(v_fst_1101_);
v_snd_1102_ = lean_ctor_get(v_val_1100_, 1);
lean_inc(v_snd_1102_);
lean_dec(v_val_1100_);
v_fst_1045_ = v_fst_1101_;
v_snd_1046_ = v_snd_1102_;
goto v___jp_1044_;
}
v___jp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = l_Lean_Expr_getAppFn(v_snd_1046_);
v___x_1048_ = l_Lean_Expr_constName_x3f(v___x_1047_);
lean_dec_ref(v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 1)
{
lean_object* v_val_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Elab_Tactic_VCGen_latticeOps;
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v___x_1050_, v_val_1049_);
lean_dec(v_val_1049_);
if (lean_obj_tag(v___x_1051_) == 1)
{
lean_object* v_val_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_1042_);
v_val_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1091_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_val_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1091_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_snd_1046_, v_val_1052_, v_a_1028_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_1057_, v_fst_1045_, v___x_1058_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1074_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_object* v___x_1065_; 
lean_del_object(v___x_1054_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1058_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1058_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
else
{
lean_object* v_mvarIds_1067_; lean_object* v___x_1069_; 
v_mvarIds_1067_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_mvarIds_1067_);
lean_dec_ref_known(v_a_1060_, 1);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_mvarIds_1067_);
v___x_1069_ = v___x_1054_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_mvarIds_1067_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1069_);
v___x_1071_ = v___x_1062_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_del_object(v___x_1054_);
v_a_1075_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1059_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1059_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_del_object(v___x_1054_);
lean_dec(v_fst_1045_);
v_a_1083_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1056_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1056_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_dec(v___x_1051_);
lean_dec_ref(v_snd_1046_);
lean_dec(v_fst_1045_);
v___x_1092_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1092_);
v___x_1094_ = v___x_1042_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
lean_dec(v___x_1048_);
lean_dec_ref(v_snd_1046_);
lean_dec(v_fst_1045_);
v___x_1096_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1096_);
v___x_1098_ = v___x_1042_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_rhs_1026_);
lean_dec(v_goal_1025_);
v_a_1104_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1039_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1039_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object* v_goal_1112_, lean_object* v_rhs_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_1112_, v_rhs_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object* v_00_u03b2_1127_, lean_object* v_m_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_1128_, v_a_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object* v_00_u03b2_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(v_00_u03b2_1131_, v_m_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_m_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1135_, lean_object* v_m_1136_, lean_object* v_query_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_m_1136_, v_query_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_m_1140_, lean_object* v_query_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(v_00_u03b2_1139_, v_m_1140_, v_query_1141_);
lean_dec(v_query_1141_);
lean_dec_ref(v_m_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_query_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___redArg(v_m_1144_, v_query_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_m_1148_, lean_object* v_query_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1147_, v_m_1148_, v_query_1149_);
lean_dec(v_query_1149_);
lean_dec_ref(v_m_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_query_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_m_1152_, v_query_1153_, v_x_1154_, v_x_1155_, v_x_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1159_, lean_object* v_m_1160_, lean_object* v_query_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1159_, v_m_1160_, v_query_1161_, v_x_1162_, v_x_1163_, v_x_1164_, v_x_1165_);
lean_dec(v_query_1161_);
lean_dec_ref(v_m_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object* v_goal_1167_, lean_object* v_rhs_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = l_Lean_Expr_isForall(v_rhs_1168_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_goal_1167_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_backwardRules_1184_; lean_object* v_forallIntro_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_backwardRules_1184_ = lean_ctor_get(v_a_1169_, 0);
v_forallIntro_1185_ = lean_ctor_get(v_backwardRules_1184_, 11);
v___x_1186_ = lean_box(0);
lean_inc_ref(v_forallIntro_1185_);
v___x_1187_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_forallIntro_1185_, v_goal_1167_, v___x_1186_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1206_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
if (lean_obj_tag(v_a_1188_) == 0)
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1186_);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1186_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
else
{
lean_object* v_mvarIds_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v_mvarIds_1195_ = lean_ctor_get(v_a_1188_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1188_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1197_ = v_a_1188_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_mvarIds_1195_);
lean_dec(v_a_1188_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_mvarIds_1195_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1200_);
v___x_1202_ = v___x_1190_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1187_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1187_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object* v_goal_1215_, lean_object* v_rhs_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_1215_, v_rhs_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v_rhs_1216_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object* v_as_1255_, size_t v_sz_1256_, size_t v_i_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1258_);
return v___x_1267_;
}
else
{
lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1512_; 
v_snd_1268_ = lean_ctor_get(v_b_1258_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1258_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_b_1258_, 0);
lean_dec(v_unused_1513_);
v___x_1270_ = v_b_1258_;
v_isShared_1271_ = v_isSharedCheck_1512_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_dec(v_b_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1512_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_snd_1272_; lean_object* v_snd_1273_; lean_object* v_snd_1274_; lean_object* v_fst_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1510_; 
v_snd_1272_ = lean_ctor_get(v_snd_1268_, 1);
lean_inc(v_snd_1272_);
v_snd_1273_ = lean_ctor_get(v_snd_1272_, 1);
lean_inc(v_snd_1273_);
v_snd_1274_ = lean_ctor_get(v_snd_1273_, 1);
lean_inc(v_snd_1274_);
v_fst_1275_ = lean_ctor_get(v_snd_1268_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_snd_1268_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_snd_1268_, 1);
lean_dec(v_unused_1511_);
v___x_1277_ = v_snd_1268_;
v_isShared_1278_ = v_isSharedCheck_1510_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_fst_1275_);
lean_dec(v_snd_1268_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1510_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_fst_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1508_; 
v_fst_1279_ = lean_ctor_get(v_snd_1272_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_snd_1272_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_snd_1272_, 1);
lean_dec(v_unused_1509_);
v___x_1281_ = v_snd_1272_;
v_isShared_1282_ = v_isSharedCheck_1508_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_fst_1279_);
lean_dec(v_snd_1272_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1508_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1506_; 
v_fst_1283_ = lean_ctor_get(v_snd_1273_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_snd_1273_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_snd_1273_, 1);
lean_dec(v_unused_1507_);
v___x_1285_ = v_snd_1273_;
v_isShared_1286_ = v_isSharedCheck_1506_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_fst_1283_);
lean_dec(v_snd_1273_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1506_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1505_; 
v_fst_1287_ = lean_ctor_get(v_snd_1274_, 0);
v_snd_1288_ = lean_ctor_get(v_snd_1274_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_snd_1274_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1290_ = v_snd_1274_;
v_isShared_1291_ = v_isSharedCheck_1505_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1288_);
lean_inc(v_fst_1287_);
lean_dec(v_snd_1274_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1505_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; 
lean_inc(v_fst_1287_);
v___x_1292_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_fst_1287_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1496_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1496_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1496_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
if (lean_obj_tag(v_a_1293_) == 7)
{
lean_object* v_binderType_1297_; lean_object* v_body_1298_; uint8_t v___x_1299_; 
v_binderType_1297_ = lean_ctor_get(v_a_1293_, 1);
lean_inc_ref(v_binderType_1297_);
v_body_1298_ = lean_ctor_get(v_a_1293_, 2);
lean_inc_ref(v_body_1298_);
lean_dec_ref_known(v_a_1293_, 3);
v___x_1299_ = l_Lean_Expr_hasLooseBVars(v_body_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1));
v___x_1301_ = l_Lean_Expr_isAppOf(v_snd_1288_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1291_ == 0)
{
v___x_1304_ = v___x_1290_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_snd_1288_);
v___x_1304_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1304_);
v___x_1306_ = v___x_1285_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1306_);
v___x_1308_ = v___x_1281_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1310_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1308_);
v___x_1310_ = v___x_1277_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1310_);
lean_ctor_set(v___x_1270_, 0, v___x_1302_);
v___x_1312_ = v___x_1270_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1312_);
v___x_1314_ = v___x_1295_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Expr_appArg_x21(v_snd_1288_);
if (lean_obj_tag(v___x_1321_) == 6)
{
lean_object* v_body_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1295_);
v_body_1322_ = lean_ctor_get(v___x_1321_, 2);
lean_inc_ref(v_body_1322_);
lean_dec_ref_known(v___x_1321_, 3);
lean_inc_ref(v_binderType_1297_);
v___x_1323_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_1297_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
lean_inc_ref(v_body_1298_);
v___x_1325_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_1298_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
lean_inc(v_a_1324_);
v___x_1327_ = l_Lean_Meta_decLevel(v_a_1324_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
lean_inc(v_a_1326_);
v___x_1329_ = l_Lean_Meta_decLevel(v_a_1326_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = lean_box(0);
v_a_1332_ = lean_array_uget_borrowed(v_as_1255_, v_i_1257_);
v___x_1333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4));
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1330_);
lean_ctor_set(v___x_1334_, 1, v___x_1331_);
v___x_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1328_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = l_Lean_mkConst(v___x_1333_, v___x_1335_);
lean_inc(v_a_1332_);
lean_inc_ref(v_body_1322_);
lean_inc_ref(v_body_1298_);
lean_inc_ref(v_binderType_1297_);
v___x_1337_ = l_Lean_mkApp4(v___x_1336_, v_binderType_1297_, v_body_1298_, v_body_1322_, v_a_1332_);
lean_inc_ref(v___x_1337_);
v___x_1338_ = l_Lean_Meta_Sym_inferType(v___x_1337_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1398_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1398_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1398_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6));
v___x_1344_ = lean_unsigned_to_nat(3u);
v___x_1345_ = l_Lean_Expr_isAppOfArity(v_a_1339_, v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec(v_a_1339_);
lean_dec_ref(v___x_1337_);
lean_dec(v_a_1326_);
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1291_ == 0)
{
v___x_1348_ = v___x_1290_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_snd_1288_);
v___x_1348_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1348_);
v___x_1350_ = v___x_1285_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1350_);
v___x_1352_ = v___x_1281_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1352_);
v___x_1354_ = v___x_1277_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1354_);
lean_ctor_set(v___x_1270_, 0, v___x_1346_);
v___x_1356_ = v___x_1270_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1356_);
v___x_1358_ = v___x_1341_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_del_object(v___x_1341_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
v___x_1365_ = lean_box(0);
v___x_1366_ = l_Lean_Expr_appArg_x21(v_a_1339_);
lean_dec(v_a_1339_);
v___x_1367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8));
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1326_);
lean_ctor_set(v___x_1368_, 1, v___x_1331_);
lean_inc_ref(v___x_1368_);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1324_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = l_Lean_mkConst(v___x_1367_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10));
v___x_1372_ = 0;
lean_inc_ref_n(v_body_1298_, 2);
lean_inc_ref(v_binderType_1297_);
v___x_1373_ = l_Lean_Expr_lam___override(v___x_1371_, v_binderType_1297_, v_body_1298_, v___x_1372_);
lean_inc_n(v_a_1332_, 3);
lean_inc(v_fst_1283_);
lean_inc(v_fst_1279_);
v___x_1374_ = l_Lean_mkApp6(v___x_1370_, v_binderType_1297_, v___x_1373_, v_fst_1279_, v_fst_1283_, v_fst_1275_, v_a_1332_);
v___x_1375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__12));
v___x_1376_ = l_Lean_mkConst(v___x_1375_, v___x_1368_);
v___x_1377_ = l_Lean_Expr_app___override(v_fst_1279_, v_a_1332_);
v___x_1378_ = l_Lean_Expr_app___override(v_fst_1283_, v_a_1332_);
lean_inc_ref(v___x_1366_);
lean_inc_ref(v___x_1377_);
v___x_1379_ = l_Lean_mkApp6(v___x_1376_, v_body_1298_, v___x_1377_, v___x_1378_, v___x_1366_, v___x_1374_, v___x_1337_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_body_1322_);
lean_ctor_set(v___x_1290_, 0, v_body_1298_);
v___x_1381_ = v___x_1290_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_body_1298_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_body_1322_);
v___x_1381_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1381_);
lean_ctor_set(v___x_1285_, 0, v___x_1366_);
v___x_1383_ = v___x_1285_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1383_);
lean_ctor_set(v___x_1281_, 0, v___x_1377_);
v___x_1385_ = v___x_1281_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1385_);
lean_ctor_set(v___x_1277_, 0, v___x_1379_);
v___x_1387_ = v___x_1277_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1387_);
lean_ctor_set(v___x_1270_, 0, v___x_1365_);
v___x_1389_ = v___x_1270_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
size_t v___x_1390_; size_t v___x_1391_; 
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1257_, v___x_1390_);
v_i_1257_ = v___x_1391_;
v_b_1258_ = v___x_1389_;
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
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v___x_1337_);
lean_dec(v_a_1326_);
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1399_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1338_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1338_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_a_1328_);
lean_dec(v_a_1326_);
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1407_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1329_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1329_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_a_1326_);
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1415_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1327_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1327_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1423_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1325_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1325_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_body_1322_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1431_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1323_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1323_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1291_ == 0)
{
v___x_1441_ = v___x_1290_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1288_);
v___x_1441_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1441_);
v___x_1443_ = v___x_1285_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1443_);
v___x_1445_ = v___x_1281_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1445_);
v___x_1447_ = v___x_1277_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1447_);
lean_ctor_set(v___x_1270_, 0, v___x_1439_);
v___x_1449_ = v___x_1270_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1449_);
v___x_1451_ = v___x_1295_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
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
lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec_ref(v_body_1298_);
lean_dec_ref(v_binderType_1297_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1291_ == 0)
{
v___x_1460_ = v___x_1290_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_snd_1288_);
v___x_1460_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1460_);
v___x_1462_ = v___x_1285_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1462_);
v___x_1464_ = v___x_1281_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1464_);
v___x_1466_ = v___x_1277_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1466_);
lean_ctor_set(v___x_1270_, 0, v___x_1458_);
v___x_1468_ = v___x_1270_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1468_);
v___x_1470_ = v___x_1295_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
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
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v_a_1293_);
v___x_1477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_1291_ == 0)
{
v___x_1479_ = v___x_1290_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1288_);
v___x_1479_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1479_);
v___x_1481_ = v___x_1285_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1481_);
v___x_1483_ = v___x_1281_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1483_);
v___x_1485_ = v___x_1277_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1485_);
lean_ctor_set(v___x_1270_, 0, v___x_1477_);
v___x_1487_ = v___x_1270_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1487_);
v___x_1489_ = v___x_1295_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
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
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_fst_1283_);
lean_del_object(v___x_1281_);
lean_dec(v_fst_1279_);
lean_del_object(v___x_1277_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1270_);
v_a_1497_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1292_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1292_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object* v_as_1514_, lean_object* v_sz_1515_, lean_object* v_i_1516_, lean_object* v_b_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
size_t v_sz_boxed_1525_; size_t v_i_boxed_1526_; lean_object* v_res_1527_; 
v_sz_boxed_1525_ = lean_unbox_usize(v_sz_1515_);
lean_dec(v_sz_1515_);
v_i_boxed_1526_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v_as_1514_, v_sz_boxed_1525_, v_i_boxed_1526_, v_b_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_as_1514_);
return v_res_1527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Lean_Expr_bvar___override(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Lean_Level_succ___override(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___x_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = l_Lean_mkSort(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object* v_goal_1552_, lean_object* v_target_1553_, lean_object* v_pre_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
uint8_t v___y_1563_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11));
v___x_1703_ = l_Lean_Expr_isAppOf(v_pre_1554_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1563_ = v___x_1703_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_unsigned_to_nat(2u);
v___x_1705_ = l_Lean_Expr_getAppNumArgs(v_pre_1554_);
v___x_1706_ = lean_nat_dec_lt(v___x_1704_, v___x_1705_);
lean_dec(v___x_1705_);
v___y_1563_ = v___x_1706_;
goto v___jp_1562_;
}
v___jp_1562_:
{
if (v___y_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
else
{
lean_object* v_dummy_1566_; lean_object* v_nargs_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_args_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_dummy_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0, &l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f___closed__0);
v_nargs_1567_ = l_Lean_Expr_getAppNumArgs(v_pre_1554_);
lean_inc(v_nargs_1567_);
v___x_1568_ = lean_mk_array(v_nargs_1567_, v_dummy_1566_);
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_sub(v_nargs_1567_, v___x_1569_);
lean_dec(v_nargs_1567_);
lean_inc_ref(v_pre_1554_);
v_args_1571_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pre_1554_, v___x_1568_, v___x_1570_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v_args_1571_);
v___x_1574_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v_args_1571_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_lt(v___x_1569_, v___x_1573_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec_ref(v_args_1571_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_curTop_1583_; lean_object* v___x_1584_; 
v___x_1580_ = lean_array_fget(v_args_1571_, v___x_1572_);
v___x_1581_ = lean_array_fget(v_args_1571_, v___x_1569_);
v___x_1582_ = l_Lean_Expr_getAppFn(v_pre_1554_);
lean_inc(v___x_1581_);
lean_inc_n(v___x_1580_, 2);
v_curTop_1583_ = l_Lean_mkAppB(v___x_1582_, v___x_1580_, v___x_1581_);
v___x_1584_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_1580_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_a_1585_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_mkConst(v___x_1586_, v___x_1588_);
lean_inc_ref_n(v_curTop_1583_, 2);
lean_inc(v___x_1580_);
v___x_1590_ = l_Lean_mkAppB(v___x_1589_, v___x_1580_, v_curTop_1583_);
v___x_1591_ = lean_unsigned_to_nat(2u);
v___x_1592_ = l_Array_extract___redArg(v_args_1571_, v___x_1591_, v___x_1573_);
lean_dec_ref(v_args_1571_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1580_);
lean_ctor_set(v___x_1594_, 1, v___x_1581_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_curTop_1583_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_curTop_1583_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1590_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1593_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v_sz_1599_ = lean_array_size(v___x_1592_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v___x_1592_, v_sz_1599_, v___x_1600_, v___x_1598_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec_ref(v___x_1592_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1685_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1685_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1685_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_fst_1606_; 
v_fst_1606_ = lean_ctor_get(v_a_1602_, 0);
if (lean_obj_tag(v_fst_1606_) == 0)
{
lean_object* v_snd_1607_; lean_object* v_nargs_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_snd_1607_ = lean_ctor_get(v_a_1602_, 1);
lean_inc(v_snd_1607_);
lean_dec(v_a_1602_);
v_nargs_1608_ = l_Lean_Expr_getAppNumArgs(v_target_1553_);
lean_inc(v_nargs_1608_);
v___x_1609_ = lean_mk_array(v_nargs_1608_, v_dummy_1566_);
v___x_1610_ = lean_nat_sub(v_nargs_1608_, v___x_1569_);
lean_dec(v_nargs_1608_);
lean_inc_ref(v_target_1553_);
v___x_1611_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_1553_, v___x_1609_, v___x_1610_);
v___x_1612_ = lean_array_get_size(v___x_1611_);
v___x_1613_ = lean_nat_dec_lt(v___x_1572_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v___x_1611_);
lean_dec(v_snd_1607_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1593_);
v___x_1615_ = v___x_1604_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1593_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_nat_dec_lt(v___x_1569_, v___x_1612_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v___x_1611_);
lean_dec(v_snd_1607_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1593_);
v___x_1619_ = v___x_1604_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1593_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(3u);
v___x_1622_ = lean_nat_dec_lt(v___x_1621_, v___x_1612_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref(v___x_1611_);
lean_dec(v_snd_1607_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1593_);
v___x_1624_ = v___x_1604_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1593_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_del_object(v___x_1604_);
v___x_1626_ = lean_array_fget(v___x_1611_, v___x_1572_);
lean_inc(v___x_1626_);
v___x_1627_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_1626_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_snd_1628_; lean_object* v_snd_1629_; lean_object* v_a_1630_; lean_object* v_fst_1631_; lean_object* v_fst_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1671_; 
v_snd_1628_ = lean_ctor_get(v_snd_1607_, 1);
v_snd_1629_ = lean_ctor_get(v_snd_1628_, 1);
lean_inc(v_snd_1629_);
v_a_1630_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1627_, 1);
v_fst_1631_ = lean_ctor_get(v_snd_1607_, 0);
lean_inc(v_fst_1631_);
lean_dec(v_snd_1607_);
v_fst_1632_ = lean_ctor_get(v_snd_1629_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_snd_1629_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_snd_1629_, 1);
lean_dec(v_unused_1672_);
v___x_1634_ = v_snd_1629_;
v_isShared_1635_ = v_isSharedCheck_1671_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_fst_1632_);
lean_dec(v_snd_1629_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1671_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1636_ = lean_array_fget(v___x_1611_, v___x_1569_);
v___x_1637_ = lean_array_fget(v___x_1611_, v___x_1621_);
lean_dec_ref(v___x_1611_);
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3));
v___x_1639_ = l_Lean_Expr_getAppFn(v_target_1553_);
lean_dec_ref(v_target_1553_);
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4);
lean_inc(v___x_1637_);
lean_inc(v___x_1636_);
lean_inc_n(v___x_1626_, 2);
lean_inc_ref(v___x_1639_);
v___x_1641_ = l_Lean_mkApp4(v___x_1639_, v___x_1626_, v___x_1636_, v___x_1640_, v___x_1637_);
v___x_1642_ = 0;
v___x_1643_ = l_Lean_Expr_lam___override(v___x_1638_, v___x_1626_, v___x_1641_, v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6));
v___x_1645_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 1);
lean_ctor_set(v___x_1634_, 1, v___x_1645_);
lean_ctor_set(v___x_1634_, 0, v_a_1630_);
v___x_1647_ = v___x_1634_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1630_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = l_Lean_mkConst(v___x_1644_, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9);
lean_inc(v_fst_1632_);
lean_inc(v___x_1626_);
v___x_1650_ = l_Lean_mkApp6(v___x_1648_, v___x_1626_, v___x_1649_, v_pre_1554_, v_fst_1632_, v___x_1643_, v_fst_1631_);
v___x_1651_ = l_Lean_mkApp4(v___x_1639_, v___x_1626_, v___x_1636_, v_fst_1632_, v___x_1637_);
v___x_1652_ = l_Lean_MVarId_replaceTargetEq(v_goal_1552_, v___x_1651_, v___x_1650_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_a_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1652_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1652_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v___x_1626_);
lean_dec_ref(v___x_1611_);
lean_dec(v_snd_1607_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v_a_1673_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1627_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1627_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; 
lean_inc_ref(v_fst_1606_);
lean_dec(v_a_1602_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v_val_1681_ = lean_ctor_get(v_fst_1606_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_fst_1606_, 1);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v_val_1681_);
v___x_1683_ = v___x_1604_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_val_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v_a_1686_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1601_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1601_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_curTop_1583_);
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
lean_dec_ref(v_args_1571_);
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_target_1553_);
lean_dec(v_goal_1552_);
v_a_1694_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1584_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1584_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object* v_goal_1707_, lean_object* v_target_1708_, lean_object* v_pre_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_1707_, v_target_1708_, v_pre_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1717_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object* v_goal_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v___x_1737_; 
lean_inc(v_goal_1728_);
v___x_1737_ = l_Lean_MVarId_getType(v_goal_1728_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1810_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1810_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1810_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2));
v___x_1743_ = lean_unsigned_to_nat(4u);
v___x_1744_ = l_Lean_Expr_isAppOfArity(v_a_1738_, v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1746_; 
lean_dec(v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v_goal_1728_);
v___x_1746_ = v___x_1740_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_goal_1728_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = l_Lean_Expr_appFn_x21(v_a_1738_);
lean_dec(v_a_1738_);
v___x_1749_ = l_Lean_Expr_appFn_x21(v___x_1748_);
v___x_1750_ = l_Lean_Expr_appFn_x21(v___x_1749_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = l_Lean_Expr_appArg_x21(v___x_1750_);
lean_dec_ref(v___x_1750_);
if (lean_obj_tag(v___x_1751_) == 3)
{
lean_object* v_u_1752_; 
v_u_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_u_1752_);
lean_dec_ref_known(v___x_1751_, 1);
if (lean_obj_tag(v_u_1752_) == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_del_object(v___x_1740_);
v___x_1753_ = l_Lean_Expr_appArg_x21(v___x_1748_);
lean_dec_ref(v___x_1748_);
v___x_1754_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_1753_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1795_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11));
v___x_1760_ = l_Lean_Expr_isAppOf(v_a_1755_, v___x_1759_);
lean_dec(v_a_1755_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1762_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_goal_1728_);
v___x_1762_ = v___x_1757_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_goal_1728_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
else
{
lean_object* v_backwardRules_1764_; lean_object* v_elimPre_1765_; lean_object* v___x_1766_; 
lean_del_object(v___x_1757_);
v_backwardRules_1764_ = lean_ctor_get(v_a_1729_, 0);
v_elimPre_1765_ = lean_ctor_get(v_backwardRules_1764_, 7);
lean_inc_ref(v_elimPre_1765_);
lean_inc(v_goal_1728_);
v___x_1766_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1728_, v_elimPre_1765_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1786_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1786_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1786_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; 
if (lean_obj_tag(v_a_1767_) == 1)
{
lean_object* v_mvarIds_1780_; 
v_mvarIds_1780_ = lean_ctor_get(v_a_1767_, 0);
lean_inc(v_mvarIds_1780_);
lean_dec_ref_known(v_a_1767_, 1);
if (lean_obj_tag(v_mvarIds_1780_) == 1)
{
lean_object* v_tail_1781_; 
v_tail_1781_ = lean_ctor_get(v_mvarIds_1780_, 1);
if (lean_obj_tag(v_tail_1781_) == 0)
{
lean_object* v_head_1782_; lean_object* v___x_1784_; 
lean_dec(v_goal_1728_);
v_head_1782_ = lean_ctor_get(v_mvarIds_1780_, 0);
lean_inc(v_head_1782_);
lean_dec_ref_known(v_mvarIds_1780_, 2);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v_head_1782_);
v___x_1784_ = v___x_1769_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_head_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_1780_, 2);
lean_del_object(v___x_1769_);
v___y_1772_ = v_a_1732_;
v___y_1773_ = v_a_1733_;
v___y_1774_ = v_a_1734_;
v___y_1775_ = v_a_1735_;
goto v___jp_1771_;
}
}
else
{
lean_dec(v_mvarIds_1780_);
lean_del_object(v___x_1769_);
v___y_1772_ = v_a_1732_;
v___y_1773_ = v_a_1733_;
v___y_1774_ = v_a_1734_;
v___y_1775_ = v_a_1735_;
goto v___jp_1771_;
}
}
else
{
lean_del_object(v___x_1769_);
lean_dec(v_a_1767_);
v___y_1772_ = v_a_1732_;
v___y_1773_ = v_a_1733_;
v___y_1774_ = v_a_1734_;
v___y_1775_ = v_a_1735_;
goto v___jp_1771_;
}
v___jp_1771_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4, &l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_goal_1728_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_1778_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_goal_1728_);
v_a_1787_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1766_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1766_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_goal_1728_);
v_a_1796_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1754_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1754_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_u_1752_);
lean_dec_ref(v___x_1748_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v_goal_1728_);
v___x_1805_ = v___x_1740_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_goal_1728_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v___x_1751_);
lean_dec_ref(v___x_1748_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v_goal_1728_);
v___x_1808_ = v___x_1740_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_goal_1728_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_goal_1728_);
v_a_1811_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1737_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1737_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object* v_goal_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object* v_goal_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_1829_, v_a_1830_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object* v_goal_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Elab_Tactic_VCGen_elimTopPre(v_goal_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1856_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_EPost(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_EPost(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_EPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
}
#ifdef __cplusplus
}
#endif
