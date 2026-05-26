// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Util
// Imports: public import Lean.Meta.Tactic.Grind.Main public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce public import Lean.Meta.Sym.AlphaShareBuilder public import Lean.Meta.Sym.Intro public import Lean.Meta.Sym.Simp.Telescope public import Lean.Meta.Sym.Util
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_simpTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "[mvcgen' +debug] BackwardRule "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " failed to apply to:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "\nbut succeeded after `unfoldReducible`-normalization to:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "\nAn earlier step is missing a normalization. Re-run with `set_option pp.all true` to see the structural difference."};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "<rule constructed from expression>"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpTelescope___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Failed to intro on "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nContext: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "repeatAndRfl: failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_1_, lean_object* v_mctx_2_, lean_object* v_cache_3_, lean_object* v_a_x3f_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_zetaDeltaFVarIds_7_; lean_object* v_postponed_8_; lean_object* v_diag_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_19_; 
v___x_6_ = lean_st_ref_take(v___y_1_);
v_zetaDeltaFVarIds_7_ = lean_ctor_get(v___x_6_, 2);
v_postponed_8_ = lean_ctor_get(v___x_6_, 3);
v_diag_9_ = lean_ctor_get(v___x_6_, 4);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; lean_object* v_unused_21_; 
v_unused_20_ = lean_ctor_get(v___x_6_, 1);
lean_dec(v_unused_20_);
v_unused_21_ = lean_ctor_get(v___x_6_, 0);
lean_dec(v_unused_21_);
v___x_11_ = v___x_6_;
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_diag_9_);
lean_inc(v_postponed_8_);
lean_inc(v_zetaDeltaFVarIds_7_);
lean_dec(v___x_6_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v_cache_3_);
lean_ctor_set(v___x_11_, 0, v_mctx_2_);
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_mctx_2_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_cache_3_);
lean_ctor_set(v_reuseFailAlloc_18_, 2, v_zetaDeltaFVarIds_7_);
lean_ctor_set(v_reuseFailAlloc_18_, 3, v_postponed_8_);
lean_ctor_set(v_reuseFailAlloc_18_, 4, v_diag_9_);
v___x_14_ = v_reuseFailAlloc_18_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_st_ref_set(v___y_1_, v___x_14_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_22_, lean_object* v_mctx_23_, lean_object* v_cache_24_, lean_object* v_a_x3f_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_22_, v_mctx_23_, v_cache_24_, v_a_x3f_25_);
lean_dec(v_a_x3f_25_);
lean_dec(v___y_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_mctx_43_; lean_object* v_cache_44_; lean_object* v___x_45_; 
v___x_41_ = lean_st_ref_get(v___y_37_);
v___x_42_ = lean_st_ref_get(v___y_37_);
v_mctx_43_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_mctx_43_);
lean_dec(v___x_41_);
v_cache_44_ = lean_ctor_get(v___x_42_, 1);
lean_inc_ref(v_cache_44_);
lean_dec(v___x_42_);
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
v___x_45_ = lean_apply_12(v_x_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, lean_box(0));
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_62_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_62_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_62_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_62_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
lean_inc(v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_61_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v___x_52_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_37_, v_mctx_43_, v_cache_44_, v___x_51_);
lean_dec_ref(v___x_51_);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_60_);
v___x_54_ = v___x_52_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_dec(v___x_52_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v_a_46_);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_46_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_63_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_45_, 1);
v___x_64_ = lean_box(0);
v___x_65_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_37_, v_mctx_43_, v_cache_44_, v___x_64_);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_73_);
v___x_67_ = v___x_65_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_65_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
lean_ctor_set(v___x_67_, 0, v_a_63_);
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_63_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_103_, v_x_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_118_, lean_object* v___x_119_, lean_object* v_rule_120_, uint8_t v___x_121_, uint8_t v_debug_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_118_, v___x_119_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = l_Lean_Expr_mvarId_x21(v_a_136_);
lean_dec(v_a_136_);
v___x_138_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_137_, v_rule_120_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_box(v___x_121_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec_ref_known(v_a_139_, 1);
v___x_147_ = lean_box(v_debug_122_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_138_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_138_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_rule_120_);
v_a_160_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_135_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_135_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_168_ = _args[0];
lean_object* v___x_169_ = _args[1];
lean_object* v_rule_170_ = _args[2];
lean_object* v___x_171_ = _args[3];
lean_object* v_debug_172_ = _args[4];
lean_object* v___y_173_ = _args[5];
lean_object* v___y_174_ = _args[6];
lean_object* v___y_175_ = _args[7];
lean_object* v___y_176_ = _args[8];
lean_object* v___y_177_ = _args[9];
lean_object* v___y_178_ = _args[10];
lean_object* v___y_179_ = _args[11];
lean_object* v___y_180_ = _args[12];
lean_object* v___y_181_ = _args[13];
lean_object* v___y_182_ = _args[14];
lean_object* v___y_183_ = _args[15];
lean_object* v___y_184_ = _args[16];
_start:
{
uint8_t v___x_43892__boxed_185_; uint8_t v_debug_boxed_186_; lean_object* v_res_187_; 
v___x_43892__boxed_185_ = lean_unbox(v___x_171_);
v_debug_boxed_186_ = lean_unbox(v_debug_172_);
v_res_187_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_168_, v___x_169_, v_rule_170_, v___x_43892__boxed_185_, v_debug_boxed_186_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v_mctx_197_; lean_object* v_lctx_198_; lean_object* v_options_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_194_ = lean_st_ref_get(v___y_192_);
v_env_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_194_);
v___x_196_ = lean_st_ref_get(v___y_190_);
v_mctx_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_mctx_197_);
lean_dec(v___x_196_);
v_lctx_198_ = lean_ctor_get(v___y_189_, 2);
v_options_199_ = lean_ctor_get(v___y_191_, 2);
lean_inc_ref(v_options_199_);
lean_inc_ref(v_lctx_198_);
v___x_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_200_, 0, v_env_195_);
lean_ctor_set(v___x_200_, 1, v_mctx_197_);
lean_ctor_set(v___x_200_, 2, v_lctx_198_);
lean_ctor_set(v___x_200_, 3, v_options_199_);
v___x_201_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_msgData_188_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object* v_msgData_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_ref_216_ = lean_ctor_get(v___y_213_, 5);
v___x_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_ref_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_216_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_252_, lean_object* v_goal_253_, lean_object* v_ruleDesc_x3f_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
lean_inc_ref(v_rule_252_);
lean_inc(v_goal_253_);
v___x_267_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_253_, v_rule_252_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
if (lean_obj_tag(v_a_268_) == 0)
{
uint8_t v_debug_269_; 
v_debug_269_ = lean_ctor_get_uint8(v_a_255_, sizeof(void*)*20 + 3);
if (v_debug_269_ == 0)
{
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
else
{
lean_object* v___x_270_; 
lean_dec_ref_known(v___x_267_, 1);
v___x_270_ = l_Lean_MVarId_getType(v_goal_253_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_n(v_a_271_, 2);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l_Lean_Meta_Sym_unfoldReducible(v_a_271_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_335_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_335_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_335_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_335_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; 
v___x_277_ = lean_expr_eqv(v_a_273_, v_a_271_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; 
lean_del_object(v___x_275_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_box(v___x_277_);
v___x_280_ = lean_box(v_debug_269_);
lean_inc_ref(v_rule_252_);
lean_inc(v_a_273_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_281_, 0, v_a_273_);
lean_closure_set(v___f_281_, 1, v___x_278_);
lean_closure_set(v___f_281_, 2, v_rule_252_);
lean_closure_set(v___f_281_, 3, v___x_279_);
lean_closure_set(v___f_281_, 4, v___x_280_);
v___x_282_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_281_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_323_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_323_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_323_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_323_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___y_288_; uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_a_283_);
lean_dec(v_a_283_);
if (v___x_310_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_a_268_);
v___x_312_ = v___x_285_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_268_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_del_object(v___x_285_);
if (lean_obj_tag(v_ruleDesc_x3f_254_) == 0)
{
lean_object* v_expr_314_; lean_object* v___x_315_; 
v_expr_314_ = lean_ctor_get(v_rule_252_, 0);
lean_inc_ref(v_expr_314_);
lean_dec_ref(v_rule_252_);
v___x_315_ = l_Lean_Expr_getAppFn(v_expr_314_);
lean_dec_ref(v_expr_314_);
if (lean_obj_tag(v___x_315_) == 4)
{
lean_object* v_declName_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_declName_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_declName_316_);
lean_dec_ref_known(v___x_315_, 2);
v___x_317_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___x_318_ = l_Lean_MessageData_ofConstName(v_declName_316_, v___x_277_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_317_);
v___y_288_ = v___x_320_;
goto v___jp_287_;
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v___x_315_);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
v___y_288_ = v___x_321_;
goto v___jp_287_;
}
}
else
{
lean_object* v_val_322_; 
lean_dec_ref(v_rule_252_);
v_val_322_ = lean_ctor_get(v_ruleDesc_x3f_254_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_ruleDesc_x3f_254_, 1);
v___y_288_ = v_val_322_;
goto v___jp_287_;
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v___x_289_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___y_288_);
v___x_291_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_indentExpr(v_a_271_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_indentExpr(v_a_273_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_300_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_324_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_282_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_282_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v___x_333_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_a_268_);
v___x_333_ = v___x_275_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_268_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_336_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_272_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_272_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_344_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_270_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_270_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_268_, 1);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_352_, lean_object* v_goal_353_, lean_object* v_ruleDesc_x3f_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_352_, v_goal_353_, v_ruleDesc_x3f_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_369_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_383_, v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(lean_object* v_mvarId_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_hypSimpMethods_412_; 
v_hypSimpMethods_412_ = lean_ctor_get(v_a_403_, 17);
if (lean_obj_tag(v_hypSimpMethods_412_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_414_; 
v_val_413_ = lean_ctor_get(v_hypSimpMethods_412_, 0);
lean_inc(v_mvarId_402_);
v___x_414_ = l_Lean_MVarId_getType(v_mvarId_402_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v_simpState_417_; lean_object* v_post_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_st_ref_get(v_a_404_);
v_simpState_417_ = lean_ctor_get(v___x_416_, 4);
lean_inc_ref(v_simpState_417_);
lean_dec(v___x_416_);
v_post_418_ = lean_ctor_get(v_val_413_, 1);
v___x_419_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0));
lean_inc_ref(v_post_418_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_post_418_);
v___x_421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_421_, 0, v_a_415_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1));
v___x_423_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_421_, v___x_420_, v___x_422_, v_simpState_417_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_484_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_484_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_484_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_484_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_483_; 
v_fst_428_ = lean_ctor_get(v_a_424_, 0);
v_snd_429_ = lean_ctor_get(v_a_424_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_483_ == 0)
{
v___x_431_ = v_a_424_;
v_isShared_432_ = v_isSharedCheck_483_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
lean_dec(v_a_424_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_483_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_specBackwardRuleCache_434_; lean_object* v_splitBackwardRuleCache_435_; lean_object* v_invariants_436_; lean_object* v_vcs_437_; lean_object* v_jps_438_; lean_object* v_fuel_439_; lean_object* v_inlineHandledInvariants_440_; uint8_t v_preTacFailed_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_481_; 
v___x_433_ = lean_st_ref_take(v_a_404_);
v_specBackwardRuleCache_434_ = lean_ctor_get(v___x_433_, 0);
v_splitBackwardRuleCache_435_ = lean_ctor_get(v___x_433_, 1);
v_invariants_436_ = lean_ctor_get(v___x_433_, 2);
v_vcs_437_ = lean_ctor_get(v___x_433_, 3);
v_jps_438_ = lean_ctor_get(v___x_433_, 5);
v_fuel_439_ = lean_ctor_get(v___x_433_, 6);
v_inlineHandledInvariants_440_ = lean_ctor_get(v___x_433_, 7);
v_preTacFailed_441_ = lean_ctor_get_uint8(v___x_433_, sizeof(void*)*8);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v___x_433_, 4);
lean_dec(v_unused_482_);
v___x_443_ = v___x_433_;
v_isShared_444_ = v_isSharedCheck_481_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_inlineHandledInvariants_440_);
lean_inc(v_fuel_439_);
lean_inc(v_jps_438_);
lean_inc(v_vcs_437_);
lean_inc(v_invariants_436_);
lean_inc(v_splitBackwardRuleCache_435_);
lean_inc(v_specBackwardRuleCache_434_);
lean_dec(v___x_433_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_481_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 4, v_snd_429_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_specBackwardRuleCache_434_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_splitBackwardRuleCache_435_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_invariants_436_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_vcs_437_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_snd_429_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_jps_438_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_fuel_439_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_inlineHandledInvariants_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*8, v_preTacFailed_441_);
v___x_446_ = v_reuseFailAlloc_480_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; 
v___x_447_ = lean_st_ref_set(v_a_404_, v___x_446_);
if (lean_obj_tag(v_fst_428_) == 0)
{
uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec_ref_known(v_fst_428_, 0);
v___x_448_ = 0;
v___x_449_ = lean_box(v___x_448_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_449_);
lean_ctor_set(v___x_431_, 0, v_mvarId_402_);
v___x_451_ = v___x_431_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_mvarId_402_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_451_);
v___x_453_ = v___x_426_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_e_x27_456_; lean_object* v_proof_457_; lean_object* v___x_458_; 
lean_del_object(v___x_426_);
v_e_x27_456_ = lean_ctor_get(v_fst_428_, 0);
lean_inc_ref(v_e_x27_456_);
v_proof_457_ = lean_ctor_get(v_fst_428_, 1);
lean_inc_ref(v_proof_457_);
lean_dec_ref_known(v_fst_428_, 2);
v___x_458_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_402_, v_e_x27_456_, v_proof_457_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_471_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_471_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_471_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_471_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = 1;
v___x_464_ = lean_box(v___x_463_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_464_);
lean_ctor_set(v___x_431_, 0, v_a_459_);
v___x_466_ = v___x_431_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_459_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_466_);
v___x_468_ = v___x_461_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_431_);
v_a_472_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_458_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_458_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
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
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_mvarId_402_);
v_a_485_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_423_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_423_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_mvarId_402_);
v_a_493_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_414_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_414_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_501_ = 0;
v___x_502_ = lean_box(v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_mvarId_402_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___boxed(lean_object* v_mvarId_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(v_mvarId_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(lean_object* v_mvarId_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(v_mvarId_516_, v_a_517_, v_a_518_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___boxed(lean_object* v_mvarId_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(v_mvarId_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_543_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(lean_object* v_mvarId_555_, lean_object* v_errorMsg_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(v_mvarId_555_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_607_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v_fst_568_ = lean_ctor_get(v_a_567_, 0);
v_snd_569_ = lean_ctor_get(v_a_567_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_607_ == 0)
{
v___x_571_ = v_a_567_;
v_isShared_572_ = v_isSharedCheck_607_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_inc(v_fst_568_);
lean_dec(v_a_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_607_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0));
lean_inc(v_fst_568_);
v___x_574_ = l_Lean_Meta_Sym_intros(v_fst_568_, v___x_573_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_598_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_598_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_598_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_598_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
if (lean_obj_tag(v_a_575_) == 0)
{
uint8_t v___x_579_; 
v___x_579_ = lean_unbox(v_snd_569_);
lean_dec(v_snd_569_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_del_object(v___x_577_);
v___x_580_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_fst_568_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 7);
lean_ctor_set(v___x_571_, 1, v___x_581_);
lean_ctor_set(v___x_571_, 0, v___x_580_);
v___x_583_ = v___x_571_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_590_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_errorMsg_556_);
v___x_587_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_588_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_589_;
}
}
else
{
lean_object* v___x_592_; 
lean_del_object(v___x_571_);
lean_dec_ref(v_errorMsg_556_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_fst_568_);
v___x_592_ = v___x_577_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_fst_568_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_mvarId_594_; lean_object* v___x_596_; 
lean_del_object(v___x_571_);
lean_dec(v_snd_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v_errorMsg_556_);
v_mvarId_594_ = lean_ctor_get(v_a_575_, 1);
lean_inc(v_mvarId_594_);
lean_dec_ref_known(v_a_575_, 2);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_mvarId_594_);
v___x_596_ = v___x_577_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_mvarId_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_del_object(v___x_571_);
lean_dec(v_snd_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v_errorMsg_556_);
v_a_599_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_574_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_574_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_errorMsg_556_);
v_a_608_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_566_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_566_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___boxed(lean_object* v_mvarId_616_, lean_object* v_errorMsg_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_mvarId_616_, v_errorMsg_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(lean_object* v_mvarId_628_, lean_object* v_errorMsg_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_mvarId_628_, v_errorMsg_629_, v_a_630_, v_a_631_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___boxed(lean_object* v_mvarId_643_, lean_object* v_errorMsg_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(v_mvarId_643_, v_errorMsg_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(lean_object* v_preTac_658_, lean_object* v_goal_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_preTac_658_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_goal_659_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = l_Lean_Meta_Grind_processHypotheses(v_goal_659_, v___x_672_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg___boxed(lean_object* v_preTac_674_, lean_object* v_goal_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_674_, v_goal_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_preTac_674_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(lean_object* v_preTac_687_, lean_object* v_goal_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_687_, v_goal_688_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___boxed(lean_object* v_preTac_702_, lean_object* v_goal_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(v_preTac_702_, v_goal_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_preTac_702_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(lean_object* v_e_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Expr_hasMVar(v_e_717_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_e_717_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v_mctx_723_; lean_object* v___x_724_; lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_727_; lean_object* v_cache_728_; lean_object* v_zetaDeltaFVarIds_729_; lean_object* v_postponed_730_; lean_object* v_diag_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_740_; 
v___x_722_ = lean_st_ref_get(v___y_718_);
v_mctx_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_mctx_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_instantiateMVarsCore(v_mctx_723_, v_e_717_);
v_fst_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_fst_725_);
v_snd_726_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_snd_726_);
lean_dec_ref(v___x_724_);
v___x_727_ = lean_st_ref_take(v___y_718_);
v_cache_728_ = lean_ctor_get(v___x_727_, 1);
v_zetaDeltaFVarIds_729_ = lean_ctor_get(v___x_727_, 2);
v_postponed_730_ = lean_ctor_get(v___x_727_, 3);
v_diag_731_ = lean_ctor_get(v___x_727_, 4);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_741_);
v___x_733_ = v___x_727_;
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_diag_731_);
lean_inc(v_postponed_730_);
lean_inc(v_zetaDeltaFVarIds_729_);
lean_inc(v_cache_728_);
lean_dec(v___x_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_snd_726_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_snd_726_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_cache_728_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_zetaDeltaFVarIds_729_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_postponed_730_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_diag_731_);
v___x_736_ = v_reuseFailAlloc_739_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_st_ref_set(v___y_718_, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v_fst_725_);
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg___boxed(lean_object* v_e_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_742_, v___y_743_);
lean_dec(v___y_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(lean_object* v_e_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_746_, v___y_755_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___boxed(lean_object* v_e_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(v_e_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
v___x_787_ = lean_apply_12(v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, lean_box(0));
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed(lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(lean_object* v_mvarId_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___f_816_; lean_object* v___x_817_; 
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_816_, 0, v_x_803_);
lean_closure_set(v___f_816_, 1, v___y_804_);
lean_closure_set(v___f_816_, 2, v___y_805_);
lean_closure_set(v___f_816_, 3, v___y_806_);
lean_closure_set(v___f_816_, 4, v___y_807_);
lean_closure_set(v___f_816_, 5, v___y_808_);
lean_closure_set(v___f_816_, 6, v___y_809_);
lean_closure_set(v___f_816_, 7, v___y_810_);
v___x_817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_802_, v___f_816_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_817_) == 0)
{
return v___x_817_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___boxed(lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_826_, v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(lean_object* v_00_u03b1_841_, lean_object* v_mvarId_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___boxed(lean_object* v_00_u03b1_857_, lean_object* v_mvarId_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(v_00_u03b1_857_, v_mvarId_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_ks_877_; lean_object* v_vs_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_902_; 
v_ks_877_ = lean_ctor_get(v_x_873_, 0);
v_vs_878_ = lean_ctor_get(v_x_873_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_902_ == 0)
{
v___x_880_ = v_x_873_;
v_isShared_881_ = v_isSharedCheck_902_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_vs_878_);
lean_inc(v_ks_877_);
lean_dec(v_x_873_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_902_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_array_get_size(v_ks_877_);
v___x_883_ = lean_nat_dec_lt(v_x_874_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v_x_874_);
v___x_884_ = lean_array_push(v_ks_877_, v_x_875_);
v___x_885_ = lean_array_push(v_vs_878_, v_x_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_885_);
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_887_ = v___x_880_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v_k_x27_889_; uint8_t v___x_890_; 
v_k_x27_889_ = lean_array_fget_borrowed(v_ks_877_, v_x_874_);
v___x_890_ = l_Lean_instBEqMVarId_beq(v_x_875_, v_k_x27_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_892_; 
if (v_isShared_881_ == 0)
{
v___x_892_ = v___x_880_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_ks_877_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_vs_878_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_x_874_, v___x_893_);
lean_dec(v_x_874_);
v_x_873_ = v___x_892_;
v_x_874_ = v___x_894_;
goto _start;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = lean_array_fset(v_ks_877_, v_x_874_, v_x_875_);
v___x_898_ = lean_array_fset(v_vs_878_, v_x_874_, v_x_876_);
lean_dec(v_x_874_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_898_);
lean_ctor_set(v___x_880_, 0, v___x_897_);
v___x_900_ = v___x_880_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_903_, lean_object* v_k_904_, lean_object* v_v_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_903_, v___x_906_, v_k_904_, v_v_905_);
return v___x_907_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; 
v___x_908_ = ((size_t)5ULL);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_shift_left(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_913_ = lean_usize_sub(v___x_912_, v___x_911_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(lean_object* v_x_915_, size_t v_x_916_, size_t v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_es_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v_j_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_es_920_ = lean_ctor_get(v_x_915_, 0);
v___x_921_ = ((size_t)5ULL);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_924_ = lean_usize_land(v_x_916_, v___x_923_);
v_j_925_ = lean_usize_to_nat(v___x_924_);
v___x_926_ = lean_array_get_size(v_es_920_);
v___x_927_ = lean_nat_dec_lt(v_j_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_dec(v_j_925_);
lean_dec(v_x_919_);
lean_dec(v_x_918_);
return v_x_915_;
}
else
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_964_; 
lean_inc_ref(v_es_920_);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_x_915_, 0);
lean_dec(v_unused_965_);
v___x_929_ = v_x_915_;
v_isShared_930_ = v_isSharedCheck_964_;
goto v_resetjp_928_;
}
else
{
lean_dec(v_x_915_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_964_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_v_931_; lean_object* v___x_932_; lean_object* v_xs_x27_933_; lean_object* v___y_935_; 
v_v_931_ = lean_array_fget(v_es_920_, v_j_925_);
v___x_932_ = lean_box(0);
v_xs_x27_933_ = lean_array_fset(v_es_920_, v_j_925_, v___x_932_);
switch(lean_obj_tag(v_v_931_))
{
case 0:
{
lean_object* v_key_940_; lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_key_940_ = lean_ctor_get(v_v_931_, 0);
v_val_941_ = lean_ctor_get(v_v_931_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_v_931_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v_v_931_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_inc(v_key_940_);
lean_dec(v_v_931_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_instBEqMVarId_beq(v_x_918_, v_key_940_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_943_);
v___x_946_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_940_, v_val_941_, v_x_918_, v_x_919_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___y_935_ = v___x_947_;
goto v___jp_934_;
}
else
{
lean_object* v___x_949_; 
lean_dec(v_val_941_);
lean_dec(v_key_940_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_x_919_);
lean_ctor_set(v___x_943_, 0, v_x_918_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_x_918_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_x_919_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v___y_935_ = v___x_949_;
goto v___jp_934_;
}
}
}
}
case 1:
{
lean_object* v_node_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_962_; 
v_node_952_ = lean_ctor_get(v_v_931_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_v_931_);
if (v_isSharedCheck_962_ == 0)
{
v___x_954_ = v_v_931_;
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_node_952_);
lean_dec(v_v_931_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_956_ = lean_usize_shift_right(v_x_916_, v___x_921_);
v___x_957_ = lean_usize_add(v_x_917_, v___x_922_);
v___x_958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_node_952_, v___x_956_, v___x_957_, v_x_918_, v_x_919_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_958_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v___y_935_ = v___x_960_;
goto v___jp_934_;
}
}
}
default: 
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_x_918_);
lean_ctor_set(v___x_963_, 1, v_x_919_);
v___y_935_ = v___x_963_;
goto v___jp_934_;
}
}
v___jp_934_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_array_fset(v_xs_x27_933_, v_j_925_, v___y_935_);
lean_dec(v_j_925_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
else
{
lean_object* v_ks_966_; lean_object* v_vs_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_987_; 
v_ks_966_ = lean_ctor_get(v_x_915_, 0);
v_vs_967_ = lean_ctor_get(v_x_915_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_987_ == 0)
{
v___x_969_ = v_x_915_;
v_isShared_970_ = v_isSharedCheck_987_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_vs_967_);
lean_inc(v_ks_966_);
lean_dec(v_x_915_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_987_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_ks_966_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_vs_967_);
v___x_972_ = v_reuseFailAlloc_986_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v_newNode_973_; uint8_t v___y_975_; size_t v___x_981_; uint8_t v___x_982_; 
v_newNode_973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_972_, v_x_918_, v_x_919_);
v___x_981_ = ((size_t)7ULL);
v___x_982_ = lean_usize_dec_le(v___x_981_, v_x_917_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_973_);
v___x_984_ = lean_unsigned_to_nat(4u);
v___x_985_ = lean_nat_dec_lt(v___x_983_, v___x_984_);
lean_dec(v___x_983_);
v___y_975_ = v___x_985_;
goto v___jp_974_;
}
else
{
v___y_975_ = v___x_982_;
goto v___jp_974_;
}
v___jp_974_:
{
if (v___y_975_ == 0)
{
lean_object* v_ks_976_; lean_object* v_vs_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_ks_976_ = lean_ctor_get(v_newNode_973_, 0);
lean_inc_ref(v_ks_976_);
v_vs_977_ = lean_ctor_get(v_newNode_973_, 1);
lean_inc_ref(v_vs_977_);
lean_dec_ref(v_newNode_973_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_917_, v_ks_976_, v_vs_977_, v___x_978_, v___x_979_);
lean_dec_ref(v_vs_977_);
lean_dec_ref(v_ks_976_);
return v___x_980_;
}
else
{
return v_newNode_973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_i_991_, lean_object* v_entries_992_){
_start:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_keys_989_);
v___x_994_ = lean_nat_dec_lt(v_i_991_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_i_991_);
return v_entries_992_;
}
else
{
lean_object* v_k_995_; lean_object* v_v_996_; uint64_t v___x_997_; size_t v_h_998_; size_t v___x_999_; lean_object* v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v_h_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_k_995_ = lean_array_fget_borrowed(v_keys_989_, v_i_991_);
v_v_996_ = lean_array_fget_borrowed(v_vals_990_, v_i_991_);
v___x_997_ = l_Lean_instHashableMVarId_hash(v_k_995_);
v_h_998_ = lean_uint64_to_usize(v___x_997_);
v___x_999_ = ((size_t)5ULL);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_sub(v_depth_988_, v___x_1001_);
v___x_1003_ = lean_usize_mul(v___x_999_, v___x_1002_);
v_h_1004_ = lean_usize_shift_right(v_h_998_, v___x_1003_);
v___x_1005_ = lean_nat_add(v_i_991_, v___x_1000_);
lean_dec(v_i_991_);
lean_inc(v_v_996_);
lean_inc(v_k_995_);
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_entries_992_, v_h_1004_, v_depth_988_, v_k_995_, v_v_996_);
v_i_991_ = v___x_1005_;
v_entries_992_ = v___x_1006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1008_, lean_object* v_keys_1009_, lean_object* v_vals_1010_, lean_object* v_i_1011_, lean_object* v_entries_1012_){
_start:
{
size_t v_depth_boxed_1013_; lean_object* v_res_1014_; 
v_depth_boxed_1013_ = lean_unbox_usize(v_depth_1008_);
lean_dec(v_depth_1008_);
v_res_1014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1013_, v_keys_1009_, v_vals_1010_, v_i_1011_, v_entries_1012_);
lean_dec_ref(v_vals_1010_);
lean_dec_ref(v_keys_1009_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
size_t v_x_74839__boxed_1020_; size_t v_x_74840__boxed_1021_; lean_object* v_res_1022_; 
v_x_74839__boxed_1020_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_x_74840__boxed_1021_ = lean_unbox_usize(v_x_1017_);
lean_dec(v_x_1017_);
v_res_1022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_1015_, v_x_74839__boxed_1020_, v_x_74840__boxed_1021_, v_x_1018_, v_x_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
uint64_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = l_Lean_instHashableMVarId_hash(v_x_1024_);
v___x_1027_ = lean_uint64_to_usize(v___x_1026_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_1023_, v___x_1027_, v___x_1028_, v_x_1024_, v_x_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(lean_object* v_mvarId_1030_, lean_object* v_val_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_mctx_1035_; lean_object* v_cache_1036_; lean_object* v_zetaDeltaFVarIds_1037_; lean_object* v_postponed_1038_; lean_object* v_diag_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1067_; 
v___x_1034_ = lean_st_ref_take(v___y_1032_);
v_mctx_1035_ = lean_ctor_get(v___x_1034_, 0);
v_cache_1036_ = lean_ctor_get(v___x_1034_, 1);
v_zetaDeltaFVarIds_1037_ = lean_ctor_get(v___x_1034_, 2);
v_postponed_1038_ = lean_ctor_get(v___x_1034_, 3);
v_diag_1039_ = lean_ctor_get(v___x_1034_, 4);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1041_ = v___x_1034_;
v_isShared_1042_ = v_isSharedCheck_1067_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_diag_1039_);
lean_inc(v_postponed_1038_);
lean_inc(v_zetaDeltaFVarIds_1037_);
lean_inc(v_cache_1036_);
lean_inc(v_mctx_1035_);
lean_dec(v___x_1034_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1067_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_depth_1043_; lean_object* v_levelAssignDepth_1044_; lean_object* v_lmvarCounter_1045_; lean_object* v_mvarCounter_1046_; lean_object* v_lDecls_1047_; lean_object* v_decls_1048_; lean_object* v_userNames_1049_; lean_object* v_lAssignment_1050_; lean_object* v_eAssignment_1051_; lean_object* v_dAssignment_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1066_; 
v_depth_1043_ = lean_ctor_get(v_mctx_1035_, 0);
v_levelAssignDepth_1044_ = lean_ctor_get(v_mctx_1035_, 1);
v_lmvarCounter_1045_ = lean_ctor_get(v_mctx_1035_, 2);
v_mvarCounter_1046_ = lean_ctor_get(v_mctx_1035_, 3);
v_lDecls_1047_ = lean_ctor_get(v_mctx_1035_, 4);
v_decls_1048_ = lean_ctor_get(v_mctx_1035_, 5);
v_userNames_1049_ = lean_ctor_get(v_mctx_1035_, 6);
v_lAssignment_1050_ = lean_ctor_get(v_mctx_1035_, 7);
v_eAssignment_1051_ = lean_ctor_get(v_mctx_1035_, 8);
v_dAssignment_1052_ = lean_ctor_get(v_mctx_1035_, 9);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_mctx_1035_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1054_ = v_mctx_1035_;
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_dAssignment_1052_);
lean_inc(v_eAssignment_1051_);
lean_inc(v_lAssignment_1050_);
lean_inc(v_userNames_1049_);
lean_inc(v_decls_1048_);
lean_inc(v_lDecls_1047_);
lean_inc(v_mvarCounter_1046_);
lean_inc(v_lmvarCounter_1045_);
lean_inc(v_levelAssignDepth_1044_);
lean_inc(v_depth_1043_);
lean_dec(v_mctx_1035_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_eAssignment_1051_, v_mvarId_1030_, v_val_1031_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 8, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_depth_1043_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_levelAssignDepth_1044_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_lmvarCounter_1045_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_mvarCounter_1046_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_lDecls_1047_);
lean_ctor_set(v_reuseFailAlloc_1065_, 5, v_decls_1048_);
lean_ctor_set(v_reuseFailAlloc_1065_, 6, v_userNames_1049_);
lean_ctor_set(v_reuseFailAlloc_1065_, 7, v_lAssignment_1050_);
lean_ctor_set(v_reuseFailAlloc_1065_, 8, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 9, v_dAssignment_1052_);
v___x_1058_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1058_);
v___x_1060_ = v___x_1041_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_cache_1036_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_zetaDeltaFVarIds_1037_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_postponed_1038_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_diag_1039_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_st_ref_set(v___y_1032_, v___x_1060_);
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg___boxed(lean_object* v_mvarId_1068_, lean_object* v_val_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_1068_, v_val_1069_, v___y_1070_);
lean_dec(v___y_1070_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3));
v___x_1098_ = l_Lean_mkConst(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16));
v___x_1105_ = l_Lean_mkConst(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19));
v___x_1112_ = l_Lean_mkConst(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21));
v___x_1118_ = l_Lean_mkConst(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(lean_object* v_goal_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
lean_inc(v_goal_1119_);
v___x_1132_ = l_Lean_MVarId_getType(v_goal_1119_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_a_1133_, v___y_1128_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1439_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1439_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1439_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1));
v___x_1140_ = l_Lean_Expr_isAppOf(v_a_1135_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3));
v___x_1142_ = l_Lean_Expr_isAppOf(v_a_1135_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5));
v___x_1144_ = lean_unsigned_to_nat(3u);
v___x_1145_ = l_Lean_Expr_isAppOfArity(v_a_1135_, v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v_a_1135_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_goal_1119_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1146_);
v___x_1148_ = v___x_1137_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_del_object(v___x_1137_);
v___x_1150_ = l_Lean_Expr_appFn_x21(v_a_1135_);
v___x_1151_ = l_Lean_Expr_appArg_x21(v___x_1150_);
v___x_1152_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1151_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = l_Lean_Expr_appArg_x21(v_a_1135_);
lean_dec(v_a_1135_);
v___x_1155_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1154_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l_Lean_Expr_appFn_x21(v___x_1150_);
lean_dec_ref(v___x_1150_);
v___x_1158_ = l_Lean_Expr_appArg_x21(v___x_1157_);
lean_dec_ref(v___x_1157_);
lean_inc_ref(v___x_1158_);
v___x_1159_ = l_Lean_Meta_getLevel(v___x_1158_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_a_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_mkConst(v___x_1143_, v___x_1162_);
lean_inc(v_a_1156_);
lean_inc(v_a_1153_);
lean_inc_ref(v___x_1158_);
v___x_1164_ = l_Lean_mkApp3(v___x_1163_, v___x_1158_, v_a_1153_, v_a_1156_);
v___x_1165_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1119_, v___x_1164_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1261_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1261_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1261_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v_a_1171_; lean_object* v___x_1208_; uint8_t v_foApprox_1209_; uint8_t v_ctxApprox_1210_; uint8_t v_quasiPatternApprox_1211_; uint8_t v_constApprox_1212_; uint8_t v_isDefEqStuckEx_1213_; uint8_t v_unificationHints_1214_; uint8_t v_proofIrrelevance_1215_; uint8_t v_offsetCnstrs_1216_; uint8_t v_transparency_1217_; uint8_t v_etaStruct_1218_; uint8_t v_univApprox_1219_; uint8_t v_iota_1220_; uint8_t v_beta_1221_; uint8_t v_proj_1222_; uint8_t v_zeta_1223_; uint8_t v_zetaDelta_1224_; uint8_t v_zetaUnused_1225_; uint8_t v_zetaHave_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1260_; 
v___x_1208_ = l_Lean_Meta_Context_config(v___y_1127_);
v_foApprox_1209_ = lean_ctor_get_uint8(v___x_1208_, 0);
v_ctxApprox_1210_ = lean_ctor_get_uint8(v___x_1208_, 1);
v_quasiPatternApprox_1211_ = lean_ctor_get_uint8(v___x_1208_, 2);
v_constApprox_1212_ = lean_ctor_get_uint8(v___x_1208_, 3);
v_isDefEqStuckEx_1213_ = lean_ctor_get_uint8(v___x_1208_, 4);
v_unificationHints_1214_ = lean_ctor_get_uint8(v___x_1208_, 5);
v_proofIrrelevance_1215_ = lean_ctor_get_uint8(v___x_1208_, 6);
v_offsetCnstrs_1216_ = lean_ctor_get_uint8(v___x_1208_, 8);
v_transparency_1217_ = lean_ctor_get_uint8(v___x_1208_, 9);
v_etaStruct_1218_ = lean_ctor_get_uint8(v___x_1208_, 10);
v_univApprox_1219_ = lean_ctor_get_uint8(v___x_1208_, 11);
v_iota_1220_ = lean_ctor_get_uint8(v___x_1208_, 12);
v_beta_1221_ = lean_ctor_get_uint8(v___x_1208_, 13);
v_proj_1222_ = lean_ctor_get_uint8(v___x_1208_, 14);
v_zeta_1223_ = lean_ctor_get_uint8(v___x_1208_, 15);
v_zetaDelta_1224_ = lean_ctor_get_uint8(v___x_1208_, 16);
v_zetaUnused_1225_ = lean_ctor_get_uint8(v___x_1208_, 17);
v_zetaHave_1226_ = lean_ctor_get_uint8(v___x_1208_, 18);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1228_ = v___x_1208_;
v_isShared_1229_ = v_isSharedCheck_1260_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1208_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1260_;
goto v_resetjp_1227_;
}
v___jp_1170_:
{
if (v_a_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
lean_dec_ref(v___x_1158_);
lean_dec(v_a_1153_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1172_);
v___x_1174_ = v___x_1168_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
else
{
lean_object* v___x_1176_; 
lean_del_object(v___x_1168_);
lean_inc_ref(v___x_1158_);
v___x_1176_ = l_Lean_Meta_getLevel(v___x_1158_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7));
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_a_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1161_);
v___x_1180_ = l_Lean_mkConst(v___x_1178_, v___x_1179_);
v___x_1181_ = l_Lean_mkAppB(v___x_1180_, v___x_1158_, v_a_1153_);
v___x_1182_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_a_1166_, v___x_1181_, v___y_1128_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1190_; 
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v___x_1182_, 0);
lean_dec(v_unused_1191_);
v___x_1184_ = v___x_1182_;
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v___x_1182_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_box(0);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1182_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1182_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_a_1166_);
lean_dec_ref(v___x_1158_);
lean_dec(v_a_1153_);
v_a_1200_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1176_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1176_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
v_resetjp_1227_:
{
uint8_t v_trackZetaDelta_1230_; lean_object* v_zetaDeltaSet_1231_; lean_object* v_lctx_1232_; lean_object* v_localInstances_1233_; lean_object* v_defEqCtx_x3f_1234_; lean_object* v_synthPendingDepth_1235_; lean_object* v_canUnfold_x3f_1236_; uint8_t v_univApprox_1237_; uint8_t v_inTypeClassResolution_1238_; uint8_t v_cacheInferType_1239_; lean_object* v___x_1241_; 
v_trackZetaDelta_1230_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*7);
v_zetaDeltaSet_1231_ = lean_ctor_get(v___y_1127_, 1);
v_lctx_1232_ = lean_ctor_get(v___y_1127_, 2);
v_localInstances_1233_ = lean_ctor_get(v___y_1127_, 3);
v_defEqCtx_x3f_1234_ = lean_ctor_get(v___y_1127_, 4);
v_synthPendingDepth_1235_ = lean_ctor_get(v___y_1127_, 5);
v_canUnfold_x3f_1236_ = lean_ctor_get(v___y_1127_, 6);
v_univApprox_1237_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1238_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*7 + 2);
v_cacheInferType_1239_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*7 + 3);
if (v_isShared_1229_ == 0)
{
v___x_1241_ = v___x_1228_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 0, v_foApprox_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 1, v_ctxApprox_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 2, v_quasiPatternApprox_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 3, v_constApprox_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 4, v_isDefEqStuckEx_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 5, v_unificationHints_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 6, v_proofIrrelevance_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 8, v_offsetCnstrs_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 9, v_transparency_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 10, v_etaStruct_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 11, v_univApprox_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 12, v_iota_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 13, v_beta_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 14, v_proj_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 15, v_zeta_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 16, v_zetaDelta_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 17, v_zetaUnused_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, 18, v_zetaHave_1226_);
v___x_1241_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
uint64_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_ctor_set_uint8(v___x_1241_, 7, v___x_1145_);
v___x_1242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0));
v___x_1244_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1244_, 0, v___x_1241_);
lean_ctor_set_uint64(v___x_1244_, sizeof(void*)*1, v___x_1242_);
lean_inc(v_canUnfold_x3f_1236_);
lean_inc(v_synthPendingDepth_1235_);
lean_inc(v_defEqCtx_x3f_1234_);
lean_inc_ref(v_localInstances_1233_);
lean_inc_ref(v_lctx_1232_);
lean_inc(v_zetaDeltaSet_1231_);
v___x_1245_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_zetaDeltaSet_1231_);
lean_ctor_set(v___x_1245_, 2, v_lctx_1232_);
lean_ctor_set(v___x_1245_, 3, v_localInstances_1233_);
lean_ctor_set(v___x_1245_, 4, v_defEqCtx_x3f_1234_);
lean_ctor_set(v___x_1245_, 5, v_synthPendingDepth_1235_);
lean_ctor_set(v___x_1245_, 6, v_canUnfold_x3f_1236_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7, v_trackZetaDelta_1230_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 1, v_univApprox_1237_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1238_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 3, v_cacheInferType_1239_);
lean_inc(v_a_1153_);
v___x_1246_ = l_Lean_Meta_Sym_isDefEqS(v_a_1153_, v_a_1156_, v___x_1145_, v___x_1145_, v___x_1243_, v___x_1243_, v___y_1125_, v___y_1126_, v___x_1245_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec_ref_known(v___x_1245_, 7);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; uint8_t v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = lean_unbox(v_a_1247_);
lean_dec(v_a_1247_);
v_a_1171_ = v___x_1248_;
goto v___jp_1170_;
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1249_; uint8_t v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
v_a_1171_ = v___x_1250_;
goto v___jp_1170_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_del_object(v___x_1168_);
lean_dec(v_a_1166_);
lean_dec_ref(v___x_1158_);
lean_dec(v_a_1153_);
v_a_1251_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1246_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
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
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___x_1158_);
lean_dec(v_a_1156_);
lean_dec(v_a_1153_);
v_a_1262_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1165_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1165_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v___x_1158_);
lean_dec(v_a_1156_);
lean_dec(v_a_1153_);
lean_dec(v_goal_1119_);
v_a_1270_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1159_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1159_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1153_);
lean_dec_ref(v___x_1150_);
lean_dec(v_goal_1119_);
v_a_1278_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1155_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1155_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v___x_1150_);
lean_dec(v_a_1135_);
lean_dec(v_goal_1119_);
v_a_1286_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1152_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1152_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v_andIntroRule_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1137_);
v_andIntroRule_1294_ = lean_ctor_get(v___y_1120_, 16);
v___x_1295_ = lean_box(0);
lean_inc_ref(v_andIntroRule_1294_);
v___x_1296_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntroRule_1294_, v_goal_1119_, v___x_1295_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
if (lean_obj_tag(v_a_1297_) == 1)
{
lean_object* v_mvarIds_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1411_; 
v_mvarIds_1312_ = lean_ctor_get(v_a_1297_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1314_ = v_a_1297_;
v_isShared_1315_ = v_isSharedCheck_1411_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_mvarIds_1312_);
lean_dec(v_a_1297_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1411_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
if (lean_obj_tag(v_mvarIds_1312_) == 1)
{
lean_object* v_tail_1316_; 
v_tail_1316_ = lean_ctor_get(v_mvarIds_1312_, 1);
lean_inc(v_tail_1316_);
if (lean_obj_tag(v_tail_1316_) == 1)
{
lean_object* v_tail_1317_; 
v_tail_1317_ = lean_ctor_get(v_tail_1316_, 1);
if (lean_obj_tag(v_tail_1317_) == 0)
{
lean_object* v_head_1318_; lean_object* v_head_1319_; lean_object* v___x_1320_; 
lean_dec(v_a_1135_);
v_head_1318_ = lean_ctor_get(v_mvarIds_1312_, 0);
lean_inc(v_head_1318_);
lean_dec_ref_known(v_mvarIds_1312_, 2);
v_head_1319_ = lean_ctor_get(v_tail_1316_, 0);
lean_inc(v_head_1319_);
lean_dec_ref_known(v_tail_1316_, 2);
v___x_1320_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(v_head_1318_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1410_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1410_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1410_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(v_head_1319_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_g_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
if (lean_obj_tag(v_a_1321_) == 0)
{
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_del_object(v___x_1323_);
lean_del_object(v___x_1314_);
return v___x_1325_;
}
else
{
lean_object* v_val_1335_; 
lean_dec_ref_known(v___x_1325_, 1);
v_val_1335_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_a_1326_, 1);
v_g_1328_ = v_val_1335_;
goto v___jp_1327_;
}
}
else
{
lean_dec_ref_known(v___x_1325_, 1);
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_object* v_val_1336_; 
v_val_1336_ = lean_ctor_get(v_a_1321_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_a_1321_, 1);
v_g_1328_ = v_val_1336_;
goto v___jp_1327_;
}
else
{
lean_object* v_val_1337_; lean_object* v_val_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1323_);
lean_del_object(v___x_1314_);
v_val_1337_ = lean_ctor_get(v_a_1321_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v_a_1321_, 1);
v_val_1338_ = lean_ctor_get(v_a_1326_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1326_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1340_ = v_a_1326_;
v_isShared_1341_ = v_isSharedCheck_1409_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_val_1338_);
lean_dec(v_a_1326_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1409_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; 
lean_inc(v_val_1337_);
v___x_1342_ = l_Lean_MVarId_getType(v_val_1337_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
lean_inc(v_val_1338_);
v___x_1344_ = l_Lean_MVarId_getType(v_val_1338_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc_n(v_a_1345_, 2);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14);
lean_inc(v_a_1343_);
v___x_1347_ = l_Lean_mkAppB(v___x_1346_, v_a_1343_, v_a_1345_);
v___x_1348_ = lean_box(0);
v___x_1349_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1347_, v___x_1348_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_a_1350_, 2);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17);
lean_inc(v_a_1345_);
lean_inc(v_a_1343_);
v___x_1352_ = l_Lean_mkApp3(v___x_1351_, v_a_1343_, v_a_1345_, v_a_1350_);
v___x_1353_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_1337_, v___x_1352_, v___y_1128_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref_known(v___x_1353_, 1);
v___x_1354_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20);
lean_inc(v_a_1350_);
v___x_1355_ = l_Lean_mkApp3(v___x_1354_, v_a_1343_, v_a_1345_, v_a_1350_);
v___x_1356_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_1338_, v___x_1355_, v___y_1128_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1356_, 0);
lean_dec(v_unused_1368_);
v___x_1358_ = v___x_1356_;
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
else
{
lean_dec(v___x_1356_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_Expr_mvarId_x21(v_a_1350_);
lean_dec(v_a_1350_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1360_);
v___x_1362_ = v___x_1340_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1350_);
lean_del_object(v___x_1340_);
v_a_1369_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1356_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1356_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1350_);
lean_dec(v_a_1345_);
lean_dec(v_a_1343_);
lean_del_object(v___x_1340_);
lean_dec(v_val_1338_);
v_a_1377_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1353_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1353_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1345_);
lean_dec(v_a_1343_);
lean_del_object(v___x_1340_);
lean_dec(v_val_1338_);
lean_dec(v_val_1337_);
v_a_1385_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1349_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1349_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_a_1343_);
lean_del_object(v___x_1340_);
lean_dec(v_val_1338_);
lean_dec(v_val_1337_);
v_a_1393_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1344_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1344_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_del_object(v___x_1340_);
lean_dec(v_val_1338_);
lean_dec(v_val_1337_);
v_a_1401_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1342_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1342_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_g_1328_);
v___x_1330_ = v___x_1314_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_g_1328_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1330_);
v___x_1332_ = v___x_1323_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_del_object(v___x_1323_);
lean_dec(v_a_1321_);
lean_del_object(v___x_1314_);
return v___x_1325_;
}
}
}
else
{
lean_dec(v_head_1319_);
lean_del_object(v___x_1314_);
return v___x_1320_;
}
}
else
{
lean_dec_ref_known(v_tail_1316_, 2);
lean_dec_ref_known(v_mvarIds_1312_, 2);
lean_del_object(v___x_1314_);
v___y_1299_ = v___y_1127_;
v___y_1300_ = v___y_1128_;
v___y_1301_ = v___y_1129_;
v___y_1302_ = v___y_1130_;
goto v___jp_1298_;
}
}
else
{
lean_dec(v_tail_1316_);
lean_dec_ref_known(v_mvarIds_1312_, 2);
lean_del_object(v___x_1314_);
v___y_1299_ = v___y_1127_;
v___y_1300_ = v___y_1128_;
v___y_1301_ = v___y_1129_;
v___y_1302_ = v___y_1130_;
goto v___jp_1298_;
}
}
else
{
lean_del_object(v___x_1314_);
lean_dec(v_mvarIds_1312_);
v___y_1299_ = v___y_1127_;
v___y_1300_ = v___y_1128_;
v___y_1301_ = v___y_1129_;
v___y_1302_ = v___y_1130_;
goto v___jp_1298_;
}
}
}
else
{
lean_dec(v_a_1297_);
v___y_1299_ = v___y_1127_;
v___y_1300_ = v___y_1128_;
v___y_1301_ = v___y_1129_;
v___y_1302_ = v___y_1130_;
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9);
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11));
v___x_1305_ = l_Lean_MessageData_ofConstName(v___x_1304_, v___x_1140_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1303_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_indentExpr(v_a_1135_);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1310_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1311_;
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_a_1135_);
v_a_1412_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1296_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1296_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1420_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22);
v___x_1421_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_goal_1119_, v___x_1420_, v___y_1128_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1430_);
v___x_1423_ = v___x_1421_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(0);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1421_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1421_);
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
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_goal_1119_);
v_a_1440_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1134_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1134_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_goal_1119_);
v_a_1448_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1132_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1132_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed(lean_object* v_goal_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(v_goal_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(lean_object* v_goal_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___f_1483_; lean_object* v___x_1484_; 
lean_inc(v_goal_1470_);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1483_, 0, v_goal_1470_);
v___x_1484_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_goal_1470_, v___f_1483_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___boxed(lean_object* v_goal_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(v_goal_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(lean_object* v_mvarId_1499_, lean_object* v_val_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_1499_, v_val_1500_, v___y_1509_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___boxed(lean_object* v_mvarId_1514_, lean_object* v_val_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(v_mvarId_1514_, v_val_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1(lean_object* v_00_u03b2_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_x_1530_, v_x_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1534_, lean_object* v_x_1535_, size_t v_x_1536_, size_t v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_1535_, v_x_1536_, v_x_1537_, v_x_1538_, v_x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
size_t v_x_75883__boxed_1547_; size_t v_x_75884__boxed_1548_; lean_object* v_res_1549_; 
v_x_75883__boxed_1547_ = lean_unbox_usize(v_x_1543_);
lean_dec(v_x_1543_);
v_x_75884__boxed_1548_ = lean_unbox_usize(v_x_1544_);
lean_dec(v_x_1544_);
v_res_1549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(v_00_u03b2_1541_, v_x_1542_, v_x_75883__boxed_1547_, v_x_75884__boxed_1548_, v_x_1545_, v_x_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1550_, lean_object* v_n_1551_, lean_object* v_k_1552_, lean_object* v_v_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1551_, v_k_1552_, v_v_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1555_, size_t v_depth_1556_, lean_object* v_keys_1557_, lean_object* v_vals_1558_, lean_object* v_heq_1559_, lean_object* v_i_1560_, lean_object* v_entries_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1556_, v_keys_1557_, v_vals_1558_, v_i_1560_, v_entries_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1563_, lean_object* v_depth_1564_, lean_object* v_keys_1565_, lean_object* v_vals_1566_, lean_object* v_heq_1567_, lean_object* v_i_1568_, lean_object* v_entries_1569_){
_start:
{
size_t v_depth_boxed_1570_; lean_object* v_res_1571_; 
v_depth_boxed_1570_ = lean_unbox_usize(v_depth_1564_);
lean_dec(v_depth_1564_);
v_res_1571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1563_, v_depth_boxed_1570_, v_keys_1565_, v_vals_1566_, v_heq_1567_, v_i_1568_, v_entries_1569_);
lean_dec_ref(v_vals_1566_);
lean_dec_ref(v_keys_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1573_, v_x_1574_, v_x_1575_, v_x_1576_);
return v___x_1577_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
}
#ifdef __cplusplus
}
#endif
