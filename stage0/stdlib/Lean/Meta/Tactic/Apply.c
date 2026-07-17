// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: public import Lean.Meta.Tactic.Util public import Lean.PrettyPrinter import Lean.Meta.AppBuilder import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkUnfoldAxiomsNote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_getExpectedNumArgsAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_getExpectedNumArgsAux___closed__0 = (const lean_object*)&l_Lean_Meta_getExpectedNumArgsAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nwith the goal"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "could not unify the "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "the term"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "conclusion"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 239, 198, 100, 229, 128, 136, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " is"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "The full type of "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to assign synthesized instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_applyConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_MVarId_applyConst___closed__0 = (const lean_object*)&l_Lean_MVarId_applyConst___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_applyConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyConst___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Type mismatch: target is"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nbut applied expression has type"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__3;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "\nafter applying "};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__5;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " arguments."};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__7;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Applied type takes fewer than "};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__8 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__9;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " arguments:\n"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__10 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_splitAndCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "splitAnd"};
static const lean_object* l_Lean_MVarId_splitAndCore___closed__0 = (const lean_object*)&l_Lean_MVarId_splitAndCore___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_splitAndCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_splitAndCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 13, 24, 72, 20, 48, 2, 32)}};
static const lean_object* l_Lean_MVarId_splitAndCore___closed__1 = (const lean_object*)&l_Lean_MVarId_splitAndCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_exfalso___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_exfalso___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_exfalso___lam__0___closed__2;
static const lean_string_object l_Lean_MVarId_exfalso___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_exfalso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "exfalso"};
static const lean_object* l_Lean_MVarId_exfalso___closed__0 = (const lean_object*)&l_Lean_MVarId_exfalso___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 71, 194, 225, 45, 41, 69, 140)}};
static const lean_object* l_Lean_MVarId_exfalso___closed__1 = (const lean_object*)&l_Lean_MVarId_exfalso___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "target is not an inductive datatype"};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_nthConstructor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_nthConstructor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__2;
static lean_once_cell_t l_Lean_MVarId_nthConstructor___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__3;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__4_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " out of bounds, only "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__5 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__5_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " constructors"};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__6_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " tactic works for inductive types with exactly "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__7 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_iffOfEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_MVarId_iffOfEq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_iffOfEq___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_iffOfEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_iffOfEq___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_iffOfEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "iff_of_eq"};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__0 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_iffOfEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_iffOfEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 65, 13, 14, 191, 127, 32, 251)}};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__1 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_iffOfEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_iffOfEq___closed__2;
static const lean_ctor_object l_Lean_MVarId_iffOfEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__3 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_propext___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_propext___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_irrel_heq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(180, 105, 248, 247, 187, 48, 190, 226)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proofIrrelHeq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___closed__0 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 31, 69, 85, 58, 186, 233, 113)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l_Lean_MVarId_subsingletonElim___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 85, 152, 16, 239, 41, 62, 212)}};
static const lean_object* l_Lean_MVarId_subsingletonElim___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_subsingletonElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "subsingletonElim"};
static const lean_object* l_Lean_MVarId_subsingletonElim___closed__0 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_subsingletonElim___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 225, 81, 216, 132, 143, 62, 229)}};
static const lean_object* l_Lean_MVarId_subsingletonElim___closed__1 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, uint8_t v_whnfType_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_19_, v___f_28_, v_cleanupAnnotations_21_, v_whnfType_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(lean_object* v_type_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_49_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; uint8_t v_whnfType_boxed_80_; lean_object* v_res_81_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_80_ = lean_unbox(v_whnfType_73_);
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(v_00_u03b1_69_, v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_79_, v_whnfType_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0(lean_object* v_xs_82_, lean_object* v_body_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = lean_array_get_size(v_xs_82_);
v___x_90_ = l_Lean_Expr_getAppFn(v_body_83_);
v___x_91_ = l_Lean_Expr_isMVar(v___x_90_);
lean_dec_ref(v___x_90_);
v___x_92_ = lean_box(v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_89_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(lean_object* v_xs_95_, lean_object* v_body_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(v_xs_95_, v_body_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_body_96_);
lean_dec_ref(v_xs_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* v_e_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_keyedConfig_110_; uint8_t v_trackZetaDelta_111_; lean_object* v_zetaDeltaSet_112_; lean_object* v_lctx_113_; lean_object* v_localInstances_114_; lean_object* v_defEqCtx_x3f_115_; lean_object* v_synthPendingDepth_116_; lean_object* v_customCanUnfoldPredicate_x3f_117_; uint8_t v_univApprox_118_; uint8_t v_inTypeClassResolution_119_; uint8_t v_cacheInferType_120_; lean_object* v___f_121_; uint8_t v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_keyedConfig_110_ = lean_ctor_get(v_a_105_, 0);
v_trackZetaDelta_111_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7);
v_zetaDeltaSet_112_ = lean_ctor_get(v_a_105_, 1);
v_lctx_113_ = lean_ctor_get(v_a_105_, 2);
v_localInstances_114_ = lean_ctor_get(v_a_105_, 3);
v_defEqCtx_x3f_115_ = lean_ctor_get(v_a_105_, 4);
v_synthPendingDepth_116_ = lean_ctor_get(v_a_105_, 5);
v_customCanUnfoldPredicate_x3f_117_ = lean_ctor_get(v_a_105_, 6);
v_univApprox_118_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_119_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 2);
v_cacheInferType_120_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 3);
v___f_121_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_122_ = 0;
v___x_123_ = 1;
lean_inc_ref(v_keyedConfig_110_);
v___x_124_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_123_, v_keyedConfig_110_);
lean_inc(v_customCanUnfoldPredicate_x3f_117_);
lean_inc(v_synthPendingDepth_116_);
lean_inc(v_defEqCtx_x3f_115_);
lean_inc_ref(v_localInstances_114_);
lean_inc_ref(v_lctx_113_);
lean_inc(v_zetaDeltaSet_112_);
v___x_125_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_zetaDeltaSet_112_);
lean_ctor_set(v___x_125_, 2, v_lctx_113_);
lean_ctor_set(v___x_125_, 3, v_localInstances_114_);
lean_ctor_set(v___x_125_, 4, v_defEqCtx_x3f_115_);
lean_ctor_set(v___x_125_, 5, v_synthPendingDepth_116_);
lean_ctor_set(v___x_125_, 6, v_customCanUnfoldPredicate_x3f_117_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*7, v_trackZetaDelta_111_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*7 + 1, v_univApprox_118_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*7 + 2, v_inTypeClassResolution_119_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*7 + 3, v_cacheInferType_120_);
v___x_126_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_104_, v___f_121_, v___x_122_, v___x_122_, v___x_125_, v_a_106_, v_a_107_, v_a_108_);
lean_dec_ref_known(v___x_125_, 7);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_fst_145_; lean_object* v___x_147_; 
v_fst_145_ = lean_ctor_get(v_a_141_, 0);
lean_inc(v_fst_145_);
lean_dec(v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v_fst_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fst_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_140_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_140_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Meta_getExpectedNumArgs(v_e_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
return v_res_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_178_ = l_Lean_MessageData_ofFormat(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v___y_181_, lean_object* v_targetType_182_, lean_object* v___y_183_, lean_object* v_term_x3f_184_, lean_object* v_conclusionType_x3f_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_181_, v_targetType_182_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_233_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_233_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_233_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_233_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v_fst_196_; lean_object* v_snd_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_232_; 
v_fst_196_ = lean_ctor_get(v_a_192_, 0);
v_snd_197_ = lean_ctor_get(v_a_192_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_232_ == 0)
{
v___x_199_ = v_a_192_;
v_isShared_200_ = v_isSharedCheck_232_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_snd_197_);
lean_inc(v_fst_196_);
lean_dec(v_a_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_232_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_220_; 
if (lean_obj_tag(v_conclusionType_x3f_185_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_220_ = v___x_230_;
goto v___jp_219_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_220_ = v___x_231_;
goto v___jp_219_;
}
v___jp_201_:
{
lean_object* v___x_206_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 7);
lean_ctor_set(v___x_199_, 1, v___y_204_);
lean_ctor_set(v___x_199_, 0, v___y_203_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___y_203_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___y_204_);
v___x_206_ = v_reuseFailAlloc_218_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_207_ = l_Lean_indentExpr(v_fst_196_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = l_Lean_indentExpr(v_snd_197_);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___y_183_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___y_202_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_214_);
v___x_216_ = v___x_194_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
v___jp_219_:
{
lean_object* v___x_221_; 
lean_inc(v_snd_197_);
lean_inc(v_fst_196_);
v___x_221_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_196_, v_snd_197_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_220_);
v___x_224_ = l_Lean_stringToMessageData(v___y_220_);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
if (lean_obj_tag(v_term_x3f_184_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_202_ = v_a_222_;
v___y_203_ = v___x_227_;
v___y_204_ = v___x_228_;
goto v___jp_201_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v_term_x3f_184_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_term_x3f_184_, 1);
v___y_202_ = v_a_222_;
v___y_203_ = v___x_227_;
v___y_204_ = v_val_229_;
goto v___jp_201_;
}
}
else
{
lean_del_object(v___x_199_);
lean_dec(v_snd_197_);
lean_dec(v_fst_196_);
lean_del_object(v___x_194_);
lean_dec(v_term_x3f_184_);
lean_dec_ref(v___y_183_);
return v___x_221_;
}
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_term_x3f_184_);
lean_dec_ref(v___y_183_);
v_a_234_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_191_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_191_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v___y_242_, lean_object* v_targetType_243_, lean_object* v___y_244_, lean_object* v_term_x3f_245_, lean_object* v_conclusionType_x3f_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v___y_242_, v_targetType_243_, v___y_244_, v_term_x3f_245_, v_conclusionType_x3f_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v_conclusionType_x3f_246_);
return v_res_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_265_, lean_object* v_eType_266_, lean_object* v_conclusionType_x3f_267_, lean_object* v_targetType_268_, lean_object* v_term_x3f_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_298_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
if (lean_obj_tag(v_conclusionType_x3f_267_) == 0)
{
lean_inc_ref(v_eType_266_);
v___y_298_ = v_eType_266_;
goto v___jp_297_;
}
else
{
lean_object* v_val_303_; 
v_val_303_ = lean_ctor_get(v_conclusionType_x3f_267_, 0);
lean_inc(v_val_303_);
v___y_298_ = v_val_303_;
goto v___jp_297_;
}
v___jp_276_:
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc_ref(v_targetType_268_);
v___f_279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_279_, 0, v___y_277_);
lean_closure_set(v___f_279_, 1, v_targetType_268_);
lean_closure_set(v___f_279_, 2, v___y_278_);
lean_closure_set(v___f_279_, 3, v_term_x3f_269_);
lean_closure_set(v___f_279_, 4, v_conclusionType_x3f_267_);
v___x_280_ = lean_unsigned_to_nat(2u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_array_push(v___x_281_, v_eType_266_);
v___x_283_ = lean_array_push(v___x_282_, v_targetType_268_);
v___x_284_ = l_Lean_MessageData_ofLazyM(v___f_279_, v___x_283_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = l_Lean_Meta_throwTacticEx___redArg(v___x_275_, v_mvarId_265_, v___x_285_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_286_;
}
v___jp_287_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc_ref(v___y_289_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_289_);
lean_ctor_set(v___x_291_, 1, v___y_290_);
v___x_292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc_ref(v_eType_266_);
v___x_294_ = l_Lean_indentExpr(v_eType_266_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_MessageData_note(v___x_295_);
v___y_277_ = v___y_288_;
v___y_278_ = v___x_296_;
goto v___jp_276_;
}
v___jp_297_:
{
if (lean_obj_tag(v_conclusionType_x3f_267_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
v___y_277_ = v___y_298_;
v___y_278_ = v___x_299_;
goto v___jp_276_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
if (lean_obj_tag(v_term_x3f_269_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_288_ = v___y_298_;
v___y_289_ = v___x_300_;
v___y_290_ = v___x_301_;
goto v___jp_287_;
}
else
{
lean_object* v_val_302_; 
v_val_302_ = lean_ctor_get(v_term_x3f_269_, 0);
lean_inc(v_val_302_);
v___y_288_ = v___y_298_;
v___y_289_ = v___x_300_;
v___y_290_ = v_val_302_;
goto v___jp_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_304_, lean_object* v_eType_305_, lean_object* v_conclusionType_x3f_306_, lean_object* v_targetType_307_, lean_object* v_term_x3f_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_304_, v_eType_305_, v_conclusionType_x3f_306_, v_targetType_307_, v_term_x3f_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_315_, lean_object* v_mvarId_316_, lean_object* v_eType_317_, lean_object* v_conclusionType_x3f_318_, lean_object* v_targetType_319_, lean_object* v_term_x3f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_316_, v_eType_317_, v_conclusionType_x3f_318_, v_targetType_319_, v_term_x3f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_327_, lean_object* v_mvarId_328_, lean_object* v_eType_329_, lean_object* v_conclusionType_x3f_330_, lean_object* v_targetType_331_, lean_object* v_term_x3f_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_327_, v_mvarId_328_, v_eType_329_, v_conclusionType_x3f_330_, v_targetType_331_, v_term_x3f_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_339_, lean_object* v_snd_340_, lean_object* v_fst_341_, lean_object* v_____r_342_, uint8_t v_progressAfterEx_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_a_339_);
v___x_350_ = lean_box(v_progressAfterEx_343_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_snd_340_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_fst_341_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_355_, lean_object* v_snd_356_, lean_object* v_fst_357_, lean_object* v_____r_358_, lean_object* v_progressAfterEx_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_progressAfterEx_boxed_365_; lean_object* v_res_366_; 
v_progressAfterEx_boxed_365_ = lean_unbox(v_progressAfterEx_359_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_355_, v_snd_356_, v_fst_357_, v_____r_358_, v_progressAfterEx_boxed_365_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_366_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_371_ = l_Lean_MessageData_ofFormat(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_374_, lean_object* v_tacticName_375_, lean_object* v_mvarId_376_, lean_object* v_as_377_, size_t v_sz_378_, size_t v_i_379_, lean_object* v_b_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_a_387_; lean_object* v_fst_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_379_, v_sz_378_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec(v_mvarId_376_);
lean_dec(v_tacticName_375_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_380_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; 
v_a_399_ = lean_array_uget_borrowed(v_as_377_, v_i_379_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
lean_inc(v_a_399_);
v___x_400_ = lean_infer_type(v_a_399_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_snd_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_495_; 
v_snd_401_ = lean_ctor_get(v_b_380_, 1);
lean_inc(v_snd_401_);
v_a_402_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_495_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_495_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_495_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_fst_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___y_410_; uint8_t v___y_411_; lean_object* v_a_418_; lean_object* v___y_422_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_fst_406_ = lean_ctor_get(v_b_380_, 0);
lean_inc(v_fst_406_);
lean_dec_ref(v_b_380_);
v_fst_407_ = lean_ctor_get(v_snd_401_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v_snd_401_, 1);
lean_inc(v_snd_408_);
lean_dec(v_snd_401_);
v___x_483_ = lean_box(0);
v___x_484_ = l_Lean_Meta_synthInstance(v_a_402_, v___x_483_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = lean_array_get_size(v_snd_408_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
lean_inc(v_snd_408_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_485_, v_snd_408_, v_fst_406_, v___x_489_, v___x_397_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
v___y_422_ = v___x_490_;
goto v___jp_421_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_unbox(v_fst_407_);
lean_inc(v_snd_408_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_485_, v_snd_408_, v_fst_406_, v___x_491_, v___x_492_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
v___y_422_ = v___x_493_;
goto v___jp_421_;
}
}
else
{
lean_object* v_a_494_; 
lean_dec(v_fst_406_);
v_a_494_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_484_, 1);
v_a_418_ = v_a_494_;
goto v___jp_417_;
}
v___jp_409_:
{
if (v___y_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_del_object(v___x_404_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___y_410_);
lean_inc(v_a_399_);
v___x_413_ = lean_array_push(v_snd_408_, v_a_399_);
v_fst_392_ = v___x_412_;
v_fst_393_ = v_fst_407_;
v_snd_394_ = v___x_413_;
goto v___jp_391_;
}
else
{
lean_object* v___x_415_; 
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_dec(v_mvarId_376_);
lean_dec(v_tacticName_375_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___y_410_);
v___x_415_ = v___x_404_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___y_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v___jp_417_:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Exception_isInterrupt(v_a_418_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
lean_inc_ref(v_a_418_);
v___x_420_ = l_Lean_Exception_isRuntime(v_a_418_);
v___y_410_ = v_a_418_;
v___y_411_ = v___x_420_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_a_418_;
v___y_411_ = v___x_419_;
goto v___jp_409_;
}
}
v___jp_421_:
{
if (lean_obj_tag(v___y_422_) == 0)
{
lean_object* v_a_423_; lean_object* v_snd_424_; lean_object* v_snd_425_; lean_object* v_fst_426_; 
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_del_object(v___x_404_);
v_a_423_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___y_422_, 1);
v_snd_424_ = lean_ctor_get(v_a_423_, 1);
lean_inc(v_snd_424_);
v_snd_425_ = lean_ctor_get(v_snd_424_, 1);
lean_inc(v_snd_425_);
v_fst_426_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_fst_426_);
lean_dec(v_a_423_);
if (lean_obj_tag(v_fst_426_) == 1)
{
lean_object* v_fst_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_477_; 
v_fst_427_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_snd_424_, 1);
lean_dec(v_unused_478_);
v___x_429_ = v_snd_424_;
v_isShared_430_ = v_isSharedCheck_477_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_fst_427_);
lean_dec(v_snd_424_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_477_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_476_; 
v_fst_431_ = lean_ctor_get(v_snd_425_, 0);
v_snd_432_ = lean_ctor_get(v_snd_425_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_snd_425_);
if (v_isSharedCheck_476_ == 0)
{
v___x_434_ = v_snd_425_;
v_isShared_435_ = v_isSharedCheck_476_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_431_);
lean_dec(v_snd_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_476_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_val_436_; lean_object* v___x_437_; 
v_val_436_ = lean_ctor_get(v_fst_426_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v_fst_426_, 1);
lean_inc(v_a_399_);
v___x_437_ = l_Lean_Meta_isExprDefEq(v_a_399_, v_val_436_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; uint8_t v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_unbox(v_a_438_);
lean_dec(v_a_438_);
if (v___x_439_ == 0)
{
if (v_allowSynthFailures_374_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_376_);
lean_inc(v_tacticName_375_);
v___x_441_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_375_, v_mvarId_376_, v___x_440_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_443_; 
lean_dec_ref_known(v___x_441_, 1);
if (v_isShared_435_ == 0)
{
v___x_443_ = v___x_434_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_432_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_443_);
v___x_445_ = v___x_429_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v_a_387_ = v___x_445_;
goto v___jp_386_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_mvarId_376_);
lean_dec(v_tacticName_375_);
v_a_448_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_441_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_441_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v___x_457_; 
if (v_isShared_435_ == 0)
{
v___x_457_ = v___x_434_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_snd_432_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_457_);
v___x_459_ = v___x_429_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v_a_387_ = v___x_459_;
goto v___jp_386_;
}
}
}
}
else
{
lean_object* v___x_463_; 
if (v_isShared_435_ == 0)
{
v___x_463_ = v___x_434_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_snd_432_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_463_);
v___x_465_ = v___x_429_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
v_a_387_ = v___x_465_;
goto v___jp_386_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_mvarId_376_);
lean_dec(v_tacticName_375_);
v_a_468_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_437_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_437_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
else
{
lean_object* v_fst_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; 
lean_dec(v_fst_426_);
v_fst_479_ = lean_ctor_get(v_snd_424_, 0);
lean_inc(v_fst_479_);
lean_dec(v_snd_424_);
v_fst_480_ = lean_ctor_get(v_snd_425_, 0);
lean_inc(v_fst_480_);
v_snd_481_ = lean_ctor_get(v_snd_425_, 1);
lean_inc(v_snd_481_);
lean_dec(v_snd_425_);
v_fst_392_ = v_fst_479_;
v_fst_393_ = v_fst_480_;
v_snd_394_ = v_snd_481_;
goto v___jp_391_;
}
}
else
{
lean_object* v_a_482_; 
v_a_482_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___y_422_, 1);
v_a_418_ = v_a_482_;
goto v___jp_417_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_b_380_);
lean_dec(v_mvarId_376_);
lean_dec(v_tacticName_375_);
v_a_496_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_400_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_400_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
v___jp_386_:
{
size_t v___x_388_; size_t v___x_389_; 
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_379_, v___x_388_);
v_i_379_ = v___x_389_;
v_b_380_ = v_a_387_;
goto _start;
}
v___jp_391_:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_fst_393_);
lean_ctor_set(v___x_395_, 1, v_snd_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_fst_392_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v_a_387_ = v___x_396_;
goto v___jp_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_504_, lean_object* v_tacticName_505_, lean_object* v_mvarId_506_, lean_object* v_as_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_allowSynthFailures_boxed_516_; size_t v_sz_boxed_517_; size_t v_i_boxed_518_; lean_object* v_res_519_; 
v_allowSynthFailures_boxed_516_ = lean_unbox(v_allowSynthFailures_504_);
v_sz_boxed_517_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_518_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_516_, v_tacticName_505_, v_mvarId_506_, v_as_507_, v_sz_boxed_517_, v_i_boxed_518_, v_b_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_as_507_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_529_, lean_object* v_mvarId_530_, uint8_t v_allowSynthFailures_531_, lean_object* v_mvars_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_postponed_538_; lean_object* v___x_539_; size_t v_sz_540_; size_t v___x_541_; lean_object* v___x_542_; 
v_postponed_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_540_ = lean_array_size(v_mvars_532_);
v___x_541_ = ((size_t)0ULL);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_531_, v_tacticName_529_, v_mvarId_530_, v_mvars_532_, v_sz_540_, v___x_541_, v___x_539_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_565_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_565_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_fst_547_; 
v_fst_547_ = lean_ctor_get(v_a_543_, 0);
lean_inc(v_fst_547_);
if (lean_obj_tag(v_fst_547_) == 1)
{
lean_object* v_snd_548_; lean_object* v_fst_549_; uint8_t v___x_550_; 
v_snd_548_ = lean_ctor_get(v_a_543_, 1);
lean_inc(v_snd_548_);
lean_dec(v_a_543_);
v_fst_549_ = lean_ctor_get(v_snd_548_, 0);
v___x_550_ = lean_unbox(v_fst_549_);
if (v___x_550_ == 0)
{
lean_dec(v_snd_548_);
if (v_allowSynthFailures_531_ == 0)
{
lean_object* v_val_551_; lean_object* v___x_553_; 
v_val_551_ = lean_ctor_get(v_fst_547_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_fst_547_, 1);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 1);
lean_ctor_set(v___x_545_, 0, v_val_551_);
v___x_553_ = v___x_545_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref_known(v_fst_547_, 1);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_postponed_538_);
v___x_556_ = v___x_545_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_postponed_538_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_snd_558_; lean_object* v___x_560_; 
lean_dec_ref_known(v_fst_547_, 1);
v_snd_558_ = lean_ctor_get(v_snd_548_, 1);
lean_inc(v_snd_558_);
lean_dec(v_snd_548_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_snd_558_);
v___x_560_ = v___x_545_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_snd_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_fst_547_);
lean_dec(v_a_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_postponed_538_);
v___x_563_ = v___x_545_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_postponed_538_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_a_566_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_542_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_542_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_574_, lean_object* v_mvarId_575_, lean_object* v_allowSynthFailures_576_, lean_object* v_mvars_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
uint8_t v_allowSynthFailures_boxed_583_; lean_object* v_res_584_; 
v_allowSynthFailures_boxed_583_ = lean_unbox(v_allowSynthFailures_576_);
v_res_584_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_574_, v_mvarId_575_, v_allowSynthFailures_boxed_583_, v_mvars_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec_ref(v_mvars_577_);
return v_res_584_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_585_, lean_object* v_i_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_array_get_size(v_keys_585_);
v___x_589_ = lean_nat_dec_lt(v_i_586_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v_i_586_);
return v___x_589_;
}
else
{
lean_object* v_k_x27_590_; uint8_t v___x_591_; 
v_k_x27_590_ = lean_array_fget_borrowed(v_keys_585_, v_i_586_);
v___x_591_ = l_Lean_instBEqMVarId_beq(v_k_587_, v_k_x27_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_i_586_, v___x_592_);
lean_dec(v_i_586_);
v_i_586_ = v___x_593_;
goto _start;
}
else
{
lean_dec(v_i_586_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_595_, lean_object* v_i_596_, lean_object* v_k_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_595_, v_i_596_, v_k_597_);
lean_dec(v_k_597_);
lean_dec_ref(v_keys_595_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_600_, size_t v_x_601_, lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v_es_603_; lean_object* v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v_j_607_; lean_object* v___x_608_; 
v_es_603_ = lean_ctor_get(v_x_600_, 0);
v___x_604_ = lean_box(2);
v___x_605_ = ((size_t)31ULL);
v___x_606_ = lean_usize_land(v_x_601_, v___x_605_);
v_j_607_ = lean_usize_to_nat(v___x_606_);
v___x_608_ = lean_array_get_borrowed(v___x_604_, v_es_603_, v_j_607_);
lean_dec(v_j_607_);
switch(lean_obj_tag(v___x_608_))
{
case 0:
{
lean_object* v_key_609_; uint8_t v___x_610_; 
v_key_609_ = lean_ctor_get(v___x_608_, 0);
v___x_610_ = l_Lean_instBEqMVarId_beq(v_x_602_, v_key_609_);
return v___x_610_;
}
case 1:
{
lean_object* v_node_611_; size_t v___x_612_; size_t v___x_613_; 
v_node_611_ = lean_ctor_get(v___x_608_, 0);
v___x_612_ = ((size_t)5ULL);
v___x_613_ = lean_usize_shift_right(v_x_601_, v___x_612_);
v_x_600_ = v_node_611_;
v_x_601_ = v___x_613_;
goto _start;
}
default: 
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
}
}
else
{
lean_object* v_ks_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_ks_616_ = lean_ctor_get(v_x_600_, 0);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_616_, v___x_617_, v_x_602_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
size_t v_x_3014__boxed_622_; uint8_t v_res_623_; lean_object* v_r_624_; 
v_x_3014__boxed_622_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_res_623_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_619_, v_x_3014__boxed_622_, v_x_621_);
lean_dec(v_x_621_);
lean_dec_ref(v_x_619_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint64_t v___x_627_; size_t v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_instHashableMVarId_hash(v_x_626_);
v___x_628_ = lean_uint64_to_usize(v___x_627_);
v___x_629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_625_, v___x_628_, v_x_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec_ref(v_x_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_mctx_638_; lean_object* v_eAssignment_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_637_ = lean_st_ref_get(v___y_635_);
v_mctx_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_mctx_638_);
lean_dec(v___x_637_);
v_eAssignment_639_ = lean_ctor_get(v_mctx_638_, 8);
lean_inc_ref(v_eAssignment_639_);
lean_dec_ref(v_mctx_638_);
v___x_640_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_639_, v_mvarId_634_);
lean_dec_ref(v_eAssignment_639_);
v___x_641_ = lean_box(v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec(v_mvarId_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_647_, lean_object* v_as_648_, size_t v_sz_649_, size_t v_i_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_a_658_; uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_650_, v_sz_649_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v_b_651_);
return v___x_663_;
}
else
{
lean_object* v_snd_664_; lean_object* v_fst_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_715_; 
v_snd_664_ = lean_ctor_get(v_b_651_, 1);
v_fst_665_ = lean_ctor_get(v_b_651_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_b_651_);
if (v_isSharedCheck_715_ == 0)
{
v___x_667_ = v_b_651_;
v_isShared_668_ = v_isSharedCheck_715_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_snd_664_);
lean_inc(v_fst_665_);
lean_dec(v_b_651_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_715_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_array_669_; lean_object* v_start_670_; lean_object* v_stop_671_; uint8_t v___x_672_; 
v_array_669_ = lean_ctor_get(v_snd_664_, 0);
v_start_670_ = lean_ctor_get(v_snd_664_, 1);
v_stop_671_ = lean_ctor_get(v_snd_664_, 2);
v___x_672_ = lean_nat_dec_lt(v_start_670_, v_stop_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_674_; 
if (v_isShared_668_ == 0)
{
v___x_674_ = v___x_667_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_snd_664_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_stop_671_);
lean_inc(v_start_670_);
lean_inc_ref(v_array_669_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_snd_664_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_712_ = lean_ctor_get(v_snd_664_, 2);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_snd_664_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_snd_664_, 0);
lean_dec(v_unused_714_);
v___x_678_ = v_snd_664_;
v_isShared_679_ = v_isSharedCheck_711_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_snd_664_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_711_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_680_ = lean_array_fget(v_array_669_, v_start_670_);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_start_670_, v___x_681_);
lean_dec(v_start_670_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_682_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_array_669_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_stop_671_);
v___x_684_ = v_reuseFailAlloc_710_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_unbox(v___x_680_);
lean_dec(v___x_680_);
v___x_686_ = l_Lean_BinderInfo_isInstImplicit(v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_684_);
v___x_688_ = v___x_667_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_684_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_a_658_ = v___x_688_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_690_ = lean_array_uget_borrowed(v_as_648_, v_i_650_);
v___x_691_ = l_Lean_Expr_mvarId_x21(v_a_690_);
v___x_692_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_691_, v___y_653_);
lean_dec(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
if (v_synthAssignedInstances_647_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = lean_unbox(v_a_693_);
lean_dec(v_a_693_);
if (v___x_701_ == 0)
{
if (v___x_686_ == 0)
{
goto v___jp_694_;
}
else
{
lean_del_object(v___x_667_);
goto v___jp_698_;
}
}
else
{
goto v___jp_694_;
}
}
else
{
lean_dec(v_a_693_);
lean_del_object(v___x_667_);
goto v___jp_698_;
}
v___jp_694_:
{
lean_object* v___x_696_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_684_);
v___x_696_ = v___x_667_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_684_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_a_658_ = v___x_696_;
goto v___jp_657_;
}
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_inc(v_a_690_);
v___x_699_ = lean_array_push(v_fst_665_, v_a_690_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_684_);
v_a_658_ = v___x_700_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v___x_684_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
v_a_702_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
}
}
v___jp_657_:
{
size_t v___x_659_; size_t v___x_660_; 
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_650_, v___x_659_);
v_i_650_ = v___x_660_;
v_b_651_ = v_a_658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_716_, lean_object* v_as_717_, lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_726_; size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_synthAssignedInstances_boxed_726_ = lean_unbox(v_synthAssignedInstances_716_);
v_sz_boxed_727_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_728_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_726_, v_as_717_, v_sz_boxed_727_, v_i_boxed_728_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_as_717_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_730_, lean_object* v_mvarId_731_, uint8_t v_allowSynthFailures_732_, lean_object* v_a_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_array_get_size(v_a_733_);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_nat_dec_eq(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_inc(v_mvarId_731_);
lean_inc(v_tacticName_730_);
v___x_742_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_730_, v_mvarId_731_, v_allowSynthFailures_732_, v_a_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec_ref(v_a_733_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v_a_733_ = v_a_743_;
goto _start;
}
else
{
lean_dec(v_mvarId_731_);
lean_dec(v_tacticName_730_);
return v___x_742_;
}
}
else
{
lean_object* v___x_745_; 
lean_dec(v_mvarId_731_);
lean_dec(v_tacticName_730_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_a_733_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_746_, lean_object* v_mvarId_747_, lean_object* v_allowSynthFailures_748_, lean_object* v_a_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v_allowSynthFailures_boxed_755_; lean_object* v_res_756_; 
v_allowSynthFailures_boxed_755_ = lean_unbox(v_allowSynthFailures_748_);
v_res_756_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_746_, v_mvarId_747_, v_allowSynthFailures_boxed_755_, v_a_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_757_, lean_object* v_mvarId_758_, lean_object* v_mvarsNew_759_, lean_object* v_binderInfos_760_, uint8_t v_synthAssignedInstances_761_, uint8_t v_allowSynthFailures_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_todo_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v_todo_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_770_ = lean_array_get_size(v_binderInfos_760_);
v___x_771_ = l_Array_toSubarray___redArg(v_binderInfos_760_, v___x_768_, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_todo_769_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v_sz_773_ = lean_array_size(v_mvarsNew_759_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_761_, v_mvarsNew_759_, v_sz_773_, v___x_774_, v___x_772_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v_fst_777_; lean_object* v___x_778_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v_fst_777_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_fst_777_);
lean_dec(v_a_776_);
v___x_778_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_757_, v_mvarId_758_, v_allowSynthFailures_762_, v_fst_777_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_778_, 0);
lean_dec(v_unused_787_);
v___x_780_ = v___x_778_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_dec(v___x_778_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_778_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_778_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_mvarId_758_);
lean_dec(v_tacticName_757_);
v_a_796_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_775_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_775_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_804_, lean_object* v_mvarId_805_, lean_object* v_mvarsNew_806_, lean_object* v_binderInfos_807_, lean_object* v_synthAssignedInstances_808_, lean_object* v_allowSynthFailures_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_815_; uint8_t v_allowSynthFailures_boxed_816_; lean_object* v_res_817_; 
v_synthAssignedInstances_boxed_815_ = lean_unbox(v_synthAssignedInstances_808_);
v_allowSynthFailures_boxed_816_ = lean_unbox(v_allowSynthFailures_809_);
v_res_817_ = l_Lean_Meta_synthAppInstances(v_tacticName_804_, v_mvarId_805_, v_mvarsNew_806_, v_binderInfos_807_, v_synthAssignedInstances_boxed_815_, v_allowSynthFailures_boxed_816_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_mvarsNew_806_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_818_, v___y_820_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v_mvarId_825_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_832_, lean_object* v_mvarId_833_, uint8_t v_allowSynthFailures_834_, lean_object* v_inst_835_, lean_object* v_a_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_832_, v_mvarId_833_, v_allowSynthFailures_834_, v_a_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_843_, lean_object* v_mvarId_844_, lean_object* v_allowSynthFailures_845_, lean_object* v_inst_846_, lean_object* v_a_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_allowSynthFailures_boxed_853_; lean_object* v_res_854_; 
v_allowSynthFailures_boxed_853_ = lean_unbox(v_allowSynthFailures_845_);
v_res_854_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_843_, v_mvarId_844_, v_allowSynthFailures_boxed_853_, v_inst_846_, v_a_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_854_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_859_, v_x_860_, v_x_861_);
lean_dec(v_x_861_);
lean_dec_ref(v_x_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, size_t v_x_866_, lean_object* v_x_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_865_, v_x_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
size_t v_x_3348__boxed_873_; uint8_t v_res_874_; lean_object* v_r_875_; 
v_x_3348__boxed_873_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_res_874_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_869_, v_x_870_, v_x_3348__boxed_873_, v_x_872_);
lean_dec(v_x_872_);
lean_dec_ref(v_x_870_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_876_, lean_object* v_keys_877_, lean_object* v_vals_878_, lean_object* v_heq_879_, lean_object* v_i_880_, lean_object* v_k_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_877_, v_i_880_, v_k_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_883_, lean_object* v_keys_884_, lean_object* v_vals_885_, lean_object* v_heq_886_, lean_object* v_i_887_, lean_object* v_k_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_883_, v_keys_884_, v_vals_885_, v_heq_886_, v_i_887_, v_k_888_);
lean_dec(v_k_888_);
lean_dec_ref(v_vals_885_);
lean_dec_ref(v_keys_884_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_891_, lean_object* v_binderInfos_892_, lean_object* v_a_893_, lean_object* v_n_894_, lean_object* v_i_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_zero_901_; uint8_t v_isZero_902_; 
v_zero_901_ = lean_unsigned_to_nat(0u);
v_isZero_902_ = lean_nat_dec_eq(v_i_895_, v_zero_901_);
if (v_isZero_902_ == 1)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec(v_i_895_);
lean_dec(v_a_893_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v_one_905_; lean_object* v_n_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; uint8_t v___x_913_; 
v_one_905_ = lean_unsigned_to_nat(1u);
v_n_906_ = lean_nat_sub(v_i_895_, v_one_905_);
lean_dec(v_i_895_);
v___x_907_ = lean_nat_sub(v_n_894_, v_n_906_);
v___x_908_ = lean_nat_sub(v___x_907_, v_one_905_);
lean_dec(v___x_907_);
v___x_909_ = lean_array_fget_borrowed(v_newMVars_891_, v___x_908_);
v___x_910_ = l_Lean_Expr_mvarId_x21(v___x_909_);
v___x_911_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_910_, v___y_897_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; uint8_t v___x_918_; 
v___x_914_ = 0;
v___x_915_ = lean_box(v___x_914_);
v___x_916_ = lean_array_get(v___x_915_, v_binderInfos_892_, v___x_908_);
lean_dec(v___x_908_);
lean_dec(v___x_915_);
v___x_917_ = lean_unbox(v___x_916_);
lean_dec(v___x_916_);
v___x_918_ = l_Lean_BinderInfo_isInstImplicit(v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_inc(v___x_910_);
v___x_919_ = l_Lean_MVarId_getTag(v___x_910_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
lean_inc(v_a_893_);
v___x_921_ = l_Lean_Meta_appendTag(v_a_893_, v_a_920_);
lean_dec(v_a_920_);
v___x_922_ = l_Lean_MVarId_setTag___redArg(v___x_910_, v___x_921_, v___y_897_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref_known(v___x_922_, 1);
v_i_895_ = v_n_906_;
goto _start;
}
else
{
lean_dec(v_n_906_);
lean_dec(v_a_893_);
return v___x_922_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v___x_910_);
lean_dec(v_n_906_);
lean_dec(v_a_893_);
v_a_924_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_919_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_dec(v___x_910_);
v_i_895_ = v_n_906_;
goto _start;
}
}
else
{
lean_dec(v___x_910_);
lean_dec(v___x_908_);
v_i_895_ = v_n_906_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_934_, lean_object* v_binderInfos_935_, lean_object* v_a_936_, lean_object* v_n_937_, lean_object* v_i_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_934_, v_binderInfos_935_, v_a_936_, v_n_937_, v_i_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v_n_937_);
lean_dec_ref(v_binderInfos_935_);
lean_dec_ref(v_newMVars_934_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_945_, lean_object* v_newMVars_946_, lean_object* v_binderInfos_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_MVarId_getTag(v_mvarId_945_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_972_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_972_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_array_get_size(v_newMVars_946_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_Name_isAnonymous(v_a_954_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_del_object(v___x_956_);
v___x_962_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_946_, v_binderInfos_947_, v_a_954_, v___x_958_, v___x_958_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_dec(v_a_954_);
v___x_963_ = lean_box(0);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_963_);
v___x_965_ = v___x_956_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_del_object(v___x_956_);
v___x_967_ = l_Lean_instInhabitedExpr;
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_array_get_borrowed(v___x_967_, v_newMVars_946_, v___x_968_);
v___x_970_ = l_Lean_Expr_mvarId_x21(v___x_969_);
v___x_971_ = l_Lean_MVarId_setTag___redArg(v___x_970_, v_a_954_, v_a_949_);
return v___x_971_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_953_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_953_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_981_, lean_object* v_newMVars_982_, lean_object* v_binderInfos_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_appendParentTag(v_mvarId_981_, v_newMVars_982_, v_binderInfos_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec_ref(v_binderInfos_983_);
lean_dec_ref(v_newMVars_982_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_990_, lean_object* v_binderInfos_991_, lean_object* v_a_992_, lean_object* v_n_993_, lean_object* v_i_994_, lean_object* v_a_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_990_, v_binderInfos_991_, v_a_992_, v_n_993_, v_i_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1002_, lean_object* v_binderInfos_1003_, lean_object* v_a_1004_, lean_object* v_n_1005_, lean_object* v_i_1006_, lean_object* v_a_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1002_, v_binderInfos_1003_, v_a_1004_, v_n_1005_, v_i_1006_, v_a_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v_n_1005_);
lean_dec_ref(v_binderInfos_1003_);
lean_dec_ref(v_newMVars_1002_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1014_, lean_object* v_mvarId_1015_, lean_object* v_newMVars_1016_, lean_object* v_binderInfos_1017_, uint8_t v_synthAssignedInstances_1018_, uint8_t v_allowSynthFailures_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_synthAppInstances(v_tacticName_1014_, v_mvarId_1015_, v_newMVars_1016_, v_binderInfos_1017_, v_synthAssignedInstances_1018_, v_allowSynthFailures_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1026_, lean_object* v_mvarId_1027_, lean_object* v_newMVars_1028_, lean_object* v_binderInfos_1029_, lean_object* v_synthAssignedInstances_1030_, lean_object* v_allowSynthFailures_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1037_; uint8_t v_allowSynthFailures_boxed_1038_; lean_object* v_res_1039_; 
v_synthAssignedInstances_boxed_1037_ = lean_unbox(v_synthAssignedInstances_1030_);
v_allowSynthFailures_boxed_1038_ = lean_unbox(v_allowSynthFailures_1031_);
v_res_1039_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1026_, v_mvarId_1027_, v_newMVars_1028_, v_binderInfos_1029_, v_synthAssignedInstances_boxed_1037_, v_allowSynthFailures_boxed_1038_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec_ref(v_newMVars_1028_);
return v_res_1039_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1040_, lean_object* v_mvarId_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = l_Lean_Expr_mvarId_x21(v_mvar_1040_);
v___x_1043_ = l_Lean_instBEqMVarId_beq(v_mvarId_1041_, v___x_1042_);
lean_dec(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1044_, lean_object* v_mvarId_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1044_, v_mvarId_1045_);
lean_dec(v_mvarId_1045_);
lean_dec_ref(v_mvar_1044_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1048_, lean_object* v_as_1049_, size_t v_i_1050_, size_t v_stop_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_usize_dec_eq(v_i_1050_, v_stop_1051_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; uint8_t v_a_1060_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1058_ = 1;
v___x_1066_ = lean_array_uget_borrowed(v_as_1049_, v_i_1050_);
v___x_1067_ = lean_expr_eqv(v_mvar_1048_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___x_1066_);
v___x_1068_ = lean_infer_type(v___x_1066_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1080_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___f_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_inc_ref(v_mvar_1048_);
v___f_1073_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1073_, 0, v_mvar_1048_);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_FindMVar_main(v___f_1073_, v_a_1069_, v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_del_object(v___x_1071_);
v_a_1060_ = v___x_1067_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec_ref_known(v___x_1075_, 1);
lean_dec_ref(v_mvar_1048_);
v___x_1076_ = lean_box(v___x_1058_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1076_);
v___x_1078_ = v___x_1071_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_mvar_1048_);
v_a_1081_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1068_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1068_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
v_a_1060_ = v___x_1057_;
goto v___jp_1059_;
}
v___jp_1059_:
{
if (v_a_1060_ == 0)
{
size_t v___x_1061_; size_t v___x_1062_; 
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1050_, v___x_1061_);
v_i_1050_ = v___x_1062_;
goto _start;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v_mvar_1048_);
v___x_1064_ = lean_box(v___x_1058_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
else
{
uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v_mvar_1048_);
v___x_1089_ = 0;
v___x_1090_ = lean_box(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1092_, lean_object* v_as_1093_, lean_object* v_i_1094_, lean_object* v_stop_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
size_t v_i_boxed_1101_; size_t v_stop_boxed_1102_; lean_object* v_res_1103_; 
v_i_boxed_1101_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_stop_boxed_1102_ = lean_unbox_usize(v_stop_1095_);
lean_dec(v_stop_1095_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1092_, v_as_1093_, v_i_boxed_1101_, v_stop_boxed_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v_as_1093_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1104_, lean_object* v_otherMVars_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_array_get_size(v_otherMVars_1105_);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v_mvar_1104_);
v___x_1114_ = lean_box(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
else
{
if (v___x_1113_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_mvar_1104_);
v___x_1116_ = lean_box(v___x_1113_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
else
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = lean_usize_of_nat(v___x_1112_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1104_, v_otherMVars_1105_, v___x_1118_, v___x_1119_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1121_, lean_object* v_otherMVars_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1121_, v_otherMVars_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_otherMVars_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1129_, lean_object* v_as_1130_, size_t v_i_1131_, size_t v_stop_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_eq(v_i_1131_, v_stop_1132_);
if (v___x_1139_ == 0)
{
lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1171_; 
v_fst_1140_ = lean_ctor_get(v_b_1133_, 0);
v_snd_1141_ = lean_ctor_get(v_b_1133_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_b_1133_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1143_ = v_b_1133_;
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v_b_1133_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v_currMVarId_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_array_uget_borrowed(v_as_1130_, v_i_1131_);
v_currMVarId_1146_ = l_Lean_Expr_mvarId_x21(v___x_1145_);
lean_inc(v___x_1145_);
v___x_1147_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1145_, v_mvars_1129_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v_a_1150_; uint8_t v___x_1154_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1154_ = lean_unbox(v_a_1148_);
lean_dec(v_a_1148_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_array_push(v_fst_1140_, v_currMVarId_1146_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1155_);
v___x_1157_ = v___x_1143_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_snd_1141_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
v_a_1150_ = v___x_1157_;
goto v___jp_1149_;
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_array_push(v_snd_1141_, v_currMVarId_1146_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1159_);
v___x_1161_ = v___x_1143_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
v_a_1150_ = v___x_1161_;
goto v___jp_1149_;
}
}
v___jp_1149_:
{
size_t v___x_1151_; size_t v___x_1152_; 
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1131_, v___x_1151_);
v_i_1131_ = v___x_1152_;
v_b_1133_ = v_a_1150_;
goto _start;
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_currMVarId_1146_);
lean_del_object(v___x_1143_);
lean_dec(v_snd_1141_);
lean_dec(v_fst_1140_);
v_a_1163_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1147_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1147_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_b_1133_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1173_, lean_object* v_as_1174_, lean_object* v_i_1175_, lean_object* v_stop_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
size_t v_i_boxed_1183_; size_t v_stop_boxed_1184_; lean_object* v_res_1185_; 
v_i_boxed_1183_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_stop_boxed_1184_ = lean_unbox_usize(v_stop_1176_);
lean_dec(v_stop_1176_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1173_, v_as_1174_, v_i_boxed_1183_, v_stop_boxed_1184_, v_b_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_as_1174_);
lean_dec_ref(v_mvars_1173_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1198_ = lean_array_get_size(v_mvars_1190_);
v___x_1199_ = lean_nat_dec_lt(v___x_1196_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1197_);
return v___x_1200_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_le(v___x_1198_, v___x_1198_);
if (v___x_1201_ == 0)
{
if (v___x_1199_ == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1197_);
return v___x_1202_;
}
else
{
size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = lean_usize_of_nat(v___x_1198_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1190_, v_mvars_1190_, v___x_1203_, v___x_1204_, v___x_1197_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1205_;
}
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1198_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1190_, v_mvars_1190_, v___x_1206_, v___x_1207_, v___x_1197_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec_ref(v_mvars_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
if (lean_obj_tag(v_a_1216_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = l_List_reverse___redArg(v_a_1217_);
return v___x_1218_;
}
else
{
lean_object* v_head_1219_; lean_object* v_tail_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1229_; 
v_head_1219_ = lean_ctor_get(v_a_1216_, 0);
v_tail_1220_ = lean_ctor_get(v_a_1216_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1216_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1222_ = v_a_1216_;
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_tail_1220_);
lean_inc(v_head_1219_);
lean_dec(v_a_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = l_Lean_Expr_mvarId_x21(v_head_1219_);
lean_dec(v_head_1219_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_a_1217_);
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_a_1217_);
v___x_1226_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
v_a_1216_ = v_tail_1220_;
v_a_1217_ = v___x_1226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1230_, uint8_t v_x_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
switch(v_x_1231_)
{
case 0:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1230_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec_ref(v_mvars_1230_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1250_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_fst_1242_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_fst_1242_);
v_snd_1243_ = lean_ctor_get(v_a_1238_, 1);
lean_inc(v_snd_1243_);
lean_dec(v_a_1238_);
v___x_1244_ = lean_array_to_list(v_fst_1242_);
v___x_1245_ = lean_array_to_list(v_snd_1243_);
v___x_1246_ = l_List_appendTR___redArg(v___x_1244_, v___x_1245_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1246_);
v___x_1248_ = v___x_1240_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1237_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1237_);
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
case 1:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1230_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec_ref(v_mvars_1230_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1269_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_fst_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v_fst_1264_ = lean_ctor_get(v_a_1260_, 0);
lean_inc(v_fst_1264_);
lean_dec(v_a_1260_);
v___x_1265_ = lean_array_to_list(v_fst_1264_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1265_);
v___x_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1259_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1259_);
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
default: 
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_array_to_list(v_mvars_1230_);
v___x_1279_ = lean_box(0);
v___x_1280_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1282_, lean_object* v_x_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
uint8_t v_x_814__boxed_1289_; lean_object* v_res_1290_; 
v_x_814__boxed_1289_ = lean_unbox(v_x_1283_);
v_res_1290_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1282_, v_x_814__boxed_1289_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
if (v_approx_1291_ == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1292_, v_b_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; uint8_t v_constApprox_1301_; uint8_t v_isDefEqStuckEx_1302_; uint8_t v_unificationHints_1303_; uint8_t v_proofIrrelevance_1304_; uint8_t v_assignSyntheticOpaque_1305_; uint8_t v_offsetCnstrs_1306_; uint8_t v_transparency_1307_; uint8_t v_etaStruct_1308_; uint8_t v_univApprox_1309_; uint8_t v_iota_1310_; uint8_t v_beta_1311_; uint8_t v_proj_1312_; uint8_t v_zeta_1313_; uint8_t v_zetaDelta_1314_; uint8_t v_zetaUnused_1315_; uint8_t v_zetaHave_1316_; uint8_t v_canUnfoldPredicateConfig_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1338_; 
v___x_1300_ = l_Lean_Meta_Context_config(v_a_1294_);
v_constApprox_1301_ = lean_ctor_get_uint8(v___x_1300_, 3);
v_isDefEqStuckEx_1302_ = lean_ctor_get_uint8(v___x_1300_, 4);
v_unificationHints_1303_ = lean_ctor_get_uint8(v___x_1300_, 5);
v_proofIrrelevance_1304_ = lean_ctor_get_uint8(v___x_1300_, 6);
v_assignSyntheticOpaque_1305_ = lean_ctor_get_uint8(v___x_1300_, 7);
v_offsetCnstrs_1306_ = lean_ctor_get_uint8(v___x_1300_, 8);
v_transparency_1307_ = lean_ctor_get_uint8(v___x_1300_, 9);
v_etaStruct_1308_ = lean_ctor_get_uint8(v___x_1300_, 10);
v_univApprox_1309_ = lean_ctor_get_uint8(v___x_1300_, 11);
v_iota_1310_ = lean_ctor_get_uint8(v___x_1300_, 12);
v_beta_1311_ = lean_ctor_get_uint8(v___x_1300_, 13);
v_proj_1312_ = lean_ctor_get_uint8(v___x_1300_, 14);
v_zeta_1313_ = lean_ctor_get_uint8(v___x_1300_, 15);
v_zetaDelta_1314_ = lean_ctor_get_uint8(v___x_1300_, 16);
v_zetaUnused_1315_ = lean_ctor_get_uint8(v___x_1300_, 17);
v_zetaHave_1316_ = lean_ctor_get_uint8(v___x_1300_, 18);
v_canUnfoldPredicateConfig_1317_ = lean_ctor_get_uint8(v___x_1300_, 19);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1319_ = v___x_1300_;
v_isShared_1320_ = v_isSharedCheck_1338_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v___x_1300_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1338_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 3, v_constApprox_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 4, v_isDefEqStuckEx_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 5, v_unificationHints_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 6, v_proofIrrelevance_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 7, v_assignSyntheticOpaque_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 8, v_offsetCnstrs_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 9, v_transparency_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 10, v_etaStruct_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 11, v_univApprox_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 12, v_iota_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 13, v_beta_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 14, v_proj_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 15, v_zeta_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 16, v_zetaDelta_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 17, v_zetaUnused_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 18, v_zetaHave_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, 19, v_canUnfoldPredicateConfig_1317_);
v___x_1322_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
uint8_t v_trackZetaDelta_1323_; lean_object* v_zetaDeltaSet_1324_; lean_object* v_lctx_1325_; lean_object* v_localInstances_1326_; lean_object* v_defEqCtx_x3f_1327_; lean_object* v_synthPendingDepth_1328_; lean_object* v_customCanUnfoldPredicate_x3f_1329_; uint8_t v_univApprox_1330_; uint8_t v_inTypeClassResolution_1331_; uint8_t v_cacheInferType_1332_; uint64_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_ctor_set_uint8(v___x_1322_, 0, v_approx_1291_);
lean_ctor_set_uint8(v___x_1322_, 1, v_approx_1291_);
lean_ctor_set_uint8(v___x_1322_, 2, v_approx_1291_);
v_trackZetaDelta_1323_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*7);
v_zetaDeltaSet_1324_ = lean_ctor_get(v_a_1294_, 1);
v_lctx_1325_ = lean_ctor_get(v_a_1294_, 2);
v_localInstances_1326_ = lean_ctor_get(v_a_1294_, 3);
v_defEqCtx_x3f_1327_ = lean_ctor_get(v_a_1294_, 4);
v_synthPendingDepth_1328_ = lean_ctor_get(v_a_1294_, 5);
v_customCanUnfoldPredicate_x3f_1329_ = lean_ctor_get(v_a_1294_, 6);
v_univApprox_1330_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1331_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*7 + 2);
v_cacheInferType_1332_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*7 + 3);
v___x_1333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1322_);
v___x_1334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1334_, 0, v___x_1322_);
lean_ctor_set_uint64(v___x_1334_, sizeof(void*)*1, v___x_1333_);
lean_inc(v_customCanUnfoldPredicate_x3f_1329_);
lean_inc(v_synthPendingDepth_1328_);
lean_inc(v_defEqCtx_x3f_1327_);
lean_inc_ref(v_localInstances_1326_);
lean_inc_ref(v_lctx_1325_);
lean_inc(v_zetaDeltaSet_1324_);
v___x_1335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_zetaDeltaSet_1324_);
lean_ctor_set(v___x_1335_, 2, v_lctx_1325_);
lean_ctor_set(v___x_1335_, 3, v_localInstances_1326_);
lean_ctor_set(v___x_1335_, 4, v_defEqCtx_x3f_1327_);
lean_ctor_set(v___x_1335_, 5, v_synthPendingDepth_1328_);
lean_ctor_set(v___x_1335_, 6, v_customCanUnfoldPredicate_x3f_1329_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*7, v_trackZetaDelta_1323_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*7 + 1, v_univApprox_1330_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1331_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*7 + 3, v_cacheInferType_1332_);
v___x_1336_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1292_, v_b_1293_, v___x_1335_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec_ref_known(v___x_1335_, 7);
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1339_, lean_object* v_a_1340_, lean_object* v_b_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
uint8_t v_approx_boxed_1347_; lean_object* v_res_1348_; 
v_approx_boxed_1347_ = lean_unbox(v_approx_1339_);
v_res_1348_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1347_, v_a_1340_, v_b_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1349_, lean_object* v_cfg_1350_, lean_object* v_term_x3f_1351_, lean_object* v_targetType_1352_, lean_object* v_eType_1353_, lean_object* v_rangeNumArgs_1354_, lean_object* v_i_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_lower_1361_; lean_object* v_upper_1362_; uint8_t v___x_1363_; 
v_lower_1361_ = lean_ctor_get(v_rangeNumArgs_1354_, 0);
v_upper_1362_ = lean_ctor_get(v_rangeNumArgs_1354_, 1);
v___x_1363_ = lean_nat_dec_lt(v_i_1355_, v_upper_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
lean_dec(v_i_1355_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_eq(v_lower_1361_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; 
lean_inc(v_lower_1361_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_lower_1361_);
v___x_1367_ = 0;
lean_inc_ref(v_eType_1353_);
v___x_1368_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1353_, v___x_1366_, v___x_1367_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_snd_1370_; lean_object* v_snd_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_snd_1370_ = lean_ctor_get(v_a_1369_, 1);
lean_inc(v_snd_1370_);
lean_dec(v_a_1369_);
v_snd_1371_ = lean_ctor_get(v_snd_1370_, 1);
lean_inc(v_snd_1371_);
lean_dec(v_snd_1370_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_snd_1371_);
v___x_1373_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1349_, v_eType_1353_, v___x_1372_, v_targetType_1352_, v_term_x3f_1351_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1373_;
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
v_a_1374_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1368_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1368_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1349_, v_eType_1353_, v___x_1382_, v_targetType_1352_, v_term_x3f_1351_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1383_;
}
}
else
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Meta_saveState___redArg(v_a_1357_, v_a_1359_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
lean_inc(v_i_1355_);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_i_1355_);
v___x_1387_ = 0;
lean_inc_ref(v_eType_1353_);
v___x_1388_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1353_, v___x_1386_, v___x_1387_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v_snd_1390_; lean_object* v_fst_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1431_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v_snd_1390_ = lean_ctor_get(v_a_1389_, 1);
lean_inc(v_snd_1390_);
v_fst_1391_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_fst_1391_);
lean_dec(v_a_1389_);
v_fst_1392_ = lean_ctor_get(v_snd_1390_, 0);
v_snd_1393_ = lean_ctor_get(v_snd_1390_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_snd_1390_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1395_ = v_snd_1390_;
v_isShared_1396_ = v_isSharedCheck_1431_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1393_);
lean_inc(v_fst_1392_);
lean_dec(v_snd_1390_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1431_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
uint8_t v_approx_1397_; lean_object* v___x_1398_; 
v_approx_1397_ = lean_ctor_get_uint8(v_cfg_1350_, 3);
lean_inc_ref(v_targetType_1352_);
v___x_1398_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1397_, v_snd_1393_, v_targetType_1352_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1422_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1422_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1422_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_unbox(v_a_1399_);
lean_dec(v_a_1399_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1401_);
lean_del_object(v___x_1395_);
lean_dec(v_fst_1392_);
lean_dec(v_fst_1391_);
v___x_1404_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1385_, v_a_1357_, v_a_1359_);
lean_dec(v_a_1385_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref_known(v___x_1404_, 1);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_add(v_i_1355_, v___x_1405_);
lean_dec(v_i_1355_);
v_i_1355_ = v___x_1406_;
goto _start;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_i_1355_);
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
v_a_1408_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1404_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_a_1385_);
lean_dec(v_i_1355_);
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v_fst_1392_);
lean_ctor_set(v___x_1395_, 0, v_fst_1391_);
v___x_1417_ = v___x_1395_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fst_1391_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_fst_1392_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1417_);
v___x_1419_ = v___x_1401_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1395_);
lean_dec(v_fst_1392_);
lean_dec(v_fst_1391_);
lean_dec(v_a_1385_);
lean_dec(v_i_1355_);
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
v_a_1423_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1398_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1398_);
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
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_a_1385_);
lean_dec(v_i_1355_);
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
v_a_1432_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1388_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1388_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_i_1355_);
lean_dec_ref(v_eType_1353_);
lean_dec_ref(v_targetType_1352_);
lean_dec(v_term_x3f_1351_);
lean_dec(v_mvarId_1349_);
v_a_1440_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1384_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1384_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1448_, lean_object* v_cfg_1449_, lean_object* v_term_x3f_1450_, lean_object* v_targetType_1451_, lean_object* v_eType_1452_, lean_object* v_rangeNumArgs_1453_, lean_object* v_i_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1448_, v_cfg_1449_, v_term_x3f_1450_, v_targetType_1451_, v_eType_1452_, v_rangeNumArgs_1453_, v_i_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec_ref(v_rangeNumArgs_1453_);
lean_dec_ref(v_cfg_1449_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1461_, lean_object* v_h__1_1462_){
_start:
{
lean_object* v_snd_1463_; lean_object* v_fst_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; 
v_snd_1463_ = lean_ctor_get(v_x_1461_, 1);
lean_inc(v_snd_1463_);
v_fst_1464_ = lean_ctor_get(v_x_1461_, 0);
lean_inc(v_fst_1464_);
lean_dec_ref(v_x_1461_);
v_fst_1465_ = lean_ctor_get(v_snd_1463_, 0);
lean_inc(v_fst_1465_);
v_snd_1466_ = lean_ctor_get(v_snd_1463_, 1);
lean_inc(v_snd_1466_);
lean_dec(v_snd_1463_);
v___x_1467_ = lean_apply_3(v_h__1_1462_, v_fst_1464_, v_fst_1465_, v_snd_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1468_, lean_object* v_x_1469_, lean_object* v_h__1_1470_){
_start:
{
lean_object* v_snd_1471_; lean_object* v_fst_1472_; lean_object* v_fst_1473_; lean_object* v_snd_1474_; lean_object* v___x_1475_; 
v_snd_1471_ = lean_ctor_get(v_x_1469_, 1);
lean_inc(v_snd_1471_);
v_fst_1472_ = lean_ctor_get(v_x_1469_, 0);
lean_inc(v_fst_1472_);
lean_dec_ref(v_x_1469_);
v_fst_1473_ = lean_ctor_get(v_snd_1471_, 0);
lean_inc(v_fst_1473_);
v_snd_1474_ = lean_ctor_get(v_snd_1471_, 1);
lean_inc(v_snd_1474_);
lean_dec(v_snd_1471_);
v___x_1475_ = lean_apply_3(v_h__1_1470_, v_fst_1472_, v_fst_1473_, v_snd_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Expr_hasMVar(v_e_1476_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_e_1476_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; lean_object* v_mctx_1482_; lean_object* v___x_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1486_; lean_object* v_cache_1487_; lean_object* v_zetaDeltaFVarIds_1488_; lean_object* v_postponed_1489_; lean_object* v_diag_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1499_; 
v___x_1481_ = lean_st_ref_get(v___y_1477_);
v_mctx_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_mctx_1482_);
lean_dec(v___x_1481_);
v___x_1483_ = l_Lean_instantiateMVarsCore(v_mctx_1482_, v_e_1476_);
v_fst_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_fst_1484_);
v_snd_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_snd_1485_);
lean_dec_ref(v___x_1483_);
v___x_1486_ = lean_st_ref_take(v___y_1477_);
v_cache_1487_ = lean_ctor_get(v___x_1486_, 1);
v_zetaDeltaFVarIds_1488_ = lean_ctor_get(v___x_1486_, 2);
v_postponed_1489_ = lean_ctor_get(v___x_1486_, 3);
v_diag_1490_ = lean_ctor_get(v___x_1486_, 4);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1500_);
v___x_1492_ = v___x_1486_;
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_diag_1490_);
lean_inc(v_postponed_1489_);
lean_inc(v_zetaDeltaFVarIds_1488_);
lean_inc(v_cache_1487_);
lean_dec(v___x_1486_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_snd_1485_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_snd_1485_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_cache_1487_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_zetaDeltaFVarIds_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_postponed_1489_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_diag_1490_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_st_ref_set(v___y_1477_, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_fst_1484_);
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1501_, v___y_1502_);
lean_dec(v___y_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1505_, v___y_1507_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1519_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1526_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1543_, v_x_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1551_, lean_object* v_mvarId_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1552_, v_x_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_mvarId_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1560_, v_mvarId_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1569_, size_t v_i_1570_, size_t v_stop_1571_, lean_object* v_b_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_a_1576_; uint8_t v___x_1580_; 
v___x_1580_ = lean_usize_dec_eq(v_i_1570_, v_stop_1571_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1581_ = lean_array_uget_borrowed(v_as_1569_, v_i_1570_);
v___x_1584_ = l_Lean_Expr_mvarId_x21(v___x_1581_);
v___x_1585_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1584_, v___y_1573_);
lean_dec(v___x_1584_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_unbox(v_a_1586_);
lean_dec(v_a_1586_);
if (v___x_1587_ == 0)
{
goto v___jp_1582_;
}
else
{
v_a_1576_ = v_b_1572_;
goto v___jp_1575_;
}
}
else
{
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1588_; uint8_t v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1589_ = lean_unbox(v_a_1588_);
lean_dec(v_a_1588_);
if (v___x_1589_ == 0)
{
v_a_1576_ = v_b_1572_;
goto v___jp_1575_;
}
else
{
goto v___jp_1582_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_b_1572_);
v_a_1590_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1585_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1585_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
v___jp_1582_:
{
lean_object* v___x_1583_; 
lean_inc(v___x_1581_);
v___x_1583_ = lean_array_push(v_b_1572_, v___x_1581_);
v_a_1576_ = v___x_1583_;
goto v___jp_1575_;
}
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_b_1572_);
return v___x_1598_;
}
v___jp_1575_:
{
size_t v___x_1577_; size_t v___x_1578_; 
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1570_, v___x_1577_);
v_i_1570_ = v___x_1578_;
v_b_1572_ = v_a_1576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1599_, lean_object* v_i_1600_, lean_object* v_stop_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
size_t v_i_boxed_1605_; size_t v_stop_boxed_1606_; lean_object* v_res_1607_; 
v_i_boxed_1605_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_stop_boxed_1606_ = lean_unbox_usize(v_stop_1601_);
lean_dec(v_stop_1601_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1599_, v_i_boxed_1605_, v_stop_boxed_1606_, v_b_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v_as_1599_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
if (lean_obj_tag(v_as_1608_) == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
else
{
lean_object* v_head_1616_; lean_object* v_tail_1617_; lean_object* v___x_1618_; 
v_head_1616_ = lean_ctor_get(v_as_1608_, 0);
lean_inc(v_head_1616_);
v_tail_1617_ = lean_ctor_get(v_as_1608_, 1);
lean_inc(v_tail_1617_);
lean_dec_ref_known(v_as_1608_, 2);
v___x_1618_ = l_Lean_MVarId_headBetaType(v_head_1616_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
v_as_1608_ = v_tail_1617_;
goto _start;
}
else
{
lean_dec(v_tail_1617_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v_ks_1631_; lean_object* v_vs_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1656_; 
v_ks_1631_ = lean_ctor_get(v_x_1627_, 0);
v_vs_1632_ = lean_ctor_get(v_x_1627_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1634_ = v_x_1627_;
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_vs_1632_);
lean_inc(v_ks_1631_);
lean_dec(v_x_1627_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_array_get_size(v_ks_1631_);
v___x_1637_ = lean_nat_dec_lt(v_x_1628_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_x_1628_);
v___x_1638_ = lean_array_push(v_ks_1631_, v_x_1629_);
v___x_1639_ = lean_array_push(v_vs_1632_, v_x_1630_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v___x_1639_);
lean_ctor_set(v___x_1634_, 0, v___x_1638_);
v___x_1641_ = v___x_1634_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v_k_x27_1643_; uint8_t v___x_1644_; 
v_k_x27_1643_ = lean_array_fget_borrowed(v_ks_1631_, v_x_1628_);
v___x_1644_ = l_Lean_instBEqMVarId_beq(v_x_1629_, v_k_x27_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1646_; 
if (v_isShared_1635_ == 0)
{
v___x_1646_ = v___x_1634_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_ks_1631_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_vs_1632_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_x_1628_, v___x_1647_);
lean_dec(v_x_1628_);
v_x_1627_ = v___x_1646_;
v_x_1628_ = v___x_1648_;
goto _start;
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1651_ = lean_array_fset(v_ks_1631_, v_x_1628_, v_x_1629_);
v___x_1652_ = lean_array_fset(v_vs_1632_, v_x_1628_, v_x_1630_);
lean_dec(v_x_1628_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v___x_1652_);
lean_ctor_set(v___x_1634_, 0, v___x_1651_);
v___x_1654_ = v___x_1634_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1657_, lean_object* v_k_1658_, lean_object* v_v_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1657_, v___x_1660_, v_k_1658_, v_v_1659_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1663_, size_t v_x_1664_, size_t v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_es_1668_; size_t v___x_1669_; size_t v___x_1670_; lean_object* v_j_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_es_1668_ = lean_ctor_get(v_x_1663_, 0);
v___x_1669_ = ((size_t)31ULL);
v___x_1670_ = lean_usize_land(v_x_1664_, v___x_1669_);
v_j_1671_ = lean_usize_to_nat(v___x_1670_);
v___x_1672_ = lean_array_get_size(v_es_1668_);
v___x_1673_ = lean_nat_dec_lt(v_j_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec(v_j_1671_);
lean_dec(v_x_1667_);
lean_dec(v_x_1666_);
return v_x_1663_;
}
else
{
lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1712_; 
lean_inc_ref(v_es_1668_);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_x_1663_, 0);
lean_dec(v_unused_1713_);
v___x_1675_ = v_x_1663_;
v_isShared_1676_ = v_isSharedCheck_1712_;
goto v_resetjp_1674_;
}
else
{
lean_dec(v_x_1663_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1712_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_v_1677_; lean_object* v___x_1678_; lean_object* v_xs_x27_1679_; lean_object* v___y_1681_; 
v_v_1677_ = lean_array_fget(v_es_1668_, v_j_1671_);
v___x_1678_ = lean_box(0);
v_xs_x27_1679_ = lean_array_fset(v_es_1668_, v_j_1671_, v___x_1678_);
switch(lean_obj_tag(v_v_1677_))
{
case 0:
{
lean_object* v_key_1686_; lean_object* v_val_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1697_; 
v_key_1686_ = lean_ctor_get(v_v_1677_, 0);
v_val_1687_ = lean_ctor_get(v_v_1677_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_v_1677_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1689_ = v_v_1677_;
v_isShared_1690_ = v_isSharedCheck_1697_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_val_1687_);
lean_inc(v_key_1686_);
lean_dec(v_v_1677_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1697_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
uint8_t v___x_1691_; 
v___x_1691_ = l_Lean_instBEqMVarId_beq(v_x_1666_, v_key_1686_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_del_object(v___x_1689_);
v___x_1692_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1686_, v_val_1687_, v_x_1666_, v_x_1667_);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
v___y_1681_ = v___x_1693_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1695_; 
lean_dec(v_val_1687_);
lean_dec(v_key_1686_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v_x_1667_);
lean_ctor_set(v___x_1689_, 0, v_x_1666_);
v___x_1695_ = v___x_1689_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_x_1666_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_x_1667_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
v___y_1681_ = v___x_1695_;
goto v___jp_1680_;
}
}
}
}
case 1:
{
lean_object* v_node_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1710_; 
v_node_1698_ = lean_ctor_get(v_v_1677_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_v_1677_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1700_ = v_v_1677_;
v_isShared_1701_ = v_isSharedCheck_1710_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_node_1698_);
lean_dec(v_v_1677_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1710_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1702_ = ((size_t)5ULL);
v___x_1703_ = lean_usize_shift_right(v_x_1664_, v___x_1702_);
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_x_1665_, v___x_1704_);
v___x_1706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1698_, v___x_1703_, v___x_1705_, v_x_1666_, v_x_1667_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1706_);
v___x_1708_ = v___x_1700_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
v___y_1681_ = v___x_1708_;
goto v___jp_1680_;
}
}
}
default: 
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_x_1666_);
lean_ctor_set(v___x_1711_, 1, v_x_1667_);
v___y_1681_ = v___x_1711_;
goto v___jp_1680_;
}
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = lean_array_fset(v_xs_x27_1679_, v_j_1671_, v___y_1681_);
lean_dec(v_j_1671_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1682_);
v___x_1684_ = v___x_1675_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v_ks_1714_; lean_object* v_vs_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1735_; 
v_ks_1714_ = lean_ctor_get(v_x_1663_, 0);
v_vs_1715_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1717_ = v_x_1663_;
v_isShared_1718_ = v_isSharedCheck_1735_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_vs_1715_);
lean_inc(v_ks_1714_);
lean_dec(v_x_1663_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1735_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_ks_1714_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_vs_1715_);
v___x_1720_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v_newNode_1721_; uint8_t v___y_1723_; size_t v___x_1729_; uint8_t v___x_1730_; 
v_newNode_1721_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1720_, v_x_1666_, v_x_1667_);
v___x_1729_ = ((size_t)7ULL);
v___x_1730_ = lean_usize_dec_le(v___x_1729_, v_x_1665_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1721_);
v___x_1732_ = lean_unsigned_to_nat(4u);
v___x_1733_ = lean_nat_dec_lt(v___x_1731_, v___x_1732_);
lean_dec(v___x_1731_);
v___y_1723_ = v___x_1733_;
goto v___jp_1722_;
}
else
{
v___y_1723_ = v___x_1730_;
goto v___jp_1722_;
}
v___jp_1722_:
{
if (v___y_1723_ == 0)
{
lean_object* v_ks_1724_; lean_object* v_vs_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_ks_1724_ = lean_ctor_get(v_newNode_1721_, 0);
lean_inc_ref(v_ks_1724_);
v_vs_1725_ = lean_ctor_get(v_newNode_1721_, 1);
lean_inc_ref(v_vs_1725_);
lean_dec_ref(v_newNode_1721_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1665_, v_ks_1724_, v_vs_1725_, v___x_1726_, v___x_1727_);
lean_dec_ref(v_vs_1725_);
lean_dec_ref(v_ks_1724_);
return v___x_1728_;
}
else
{
return v_newNode_1721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1736_, lean_object* v_keys_1737_, lean_object* v_vals_1738_, lean_object* v_i_1739_, lean_object* v_entries_1740_){
_start:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_array_get_size(v_keys_1737_);
v___x_1742_ = lean_nat_dec_lt(v_i_1739_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_dec(v_i_1739_);
return v_entries_1740_;
}
else
{
lean_object* v_k_1743_; lean_object* v_v_1744_; uint64_t v___x_1745_; size_t v_h_1746_; size_t v___x_1747_; lean_object* v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; size_t v_h_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_k_1743_ = lean_array_fget_borrowed(v_keys_1737_, v_i_1739_);
v_v_1744_ = lean_array_fget_borrowed(v_vals_1738_, v_i_1739_);
v___x_1745_ = l_Lean_instHashableMVarId_hash(v_k_1743_);
v_h_1746_ = lean_uint64_to_usize(v___x_1745_);
v___x_1747_ = ((size_t)5ULL);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_sub(v_depth_1736_, v___x_1749_);
v___x_1751_ = lean_usize_mul(v___x_1747_, v___x_1750_);
v_h_1752_ = lean_usize_shift_right(v_h_1746_, v___x_1751_);
v___x_1753_ = lean_nat_add(v_i_1739_, v___x_1748_);
lean_dec(v_i_1739_);
lean_inc(v_v_1744_);
lean_inc(v_k_1743_);
v___x_1754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1740_, v_h_1752_, v_depth_1736_, v_k_1743_, v_v_1744_);
v_i_1739_ = v___x_1753_;
v_entries_1740_ = v___x_1754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1756_, lean_object* v_keys_1757_, lean_object* v_vals_1758_, lean_object* v_i_1759_, lean_object* v_entries_1760_){
_start:
{
size_t v_depth_boxed_1761_; lean_object* v_res_1762_; 
v_depth_boxed_1761_ = lean_unbox_usize(v_depth_1756_);
lean_dec(v_depth_1756_);
v_res_1762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1761_, v_keys_1757_, v_vals_1758_, v_i_1759_, v_entries_1760_);
lean_dec_ref(v_vals_1758_);
lean_dec_ref(v_keys_1757_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
size_t v_x_7234__boxed_1768_; size_t v_x_7235__boxed_1769_; lean_object* v_res_1770_; 
v_x_7234__boxed_1768_ = lean_unbox_usize(v_x_1764_);
lean_dec(v_x_1764_);
v_x_7235__boxed_1769_ = lean_unbox_usize(v_x_1765_);
lean_dec(v_x_1765_);
v_res_1770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1763_, v_x_7234__boxed_1768_, v_x_7235__boxed_1769_, v_x_1766_, v_x_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
uint64_t v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1774_ = l_Lean_instHashableMVarId_hash(v_x_1772_);
v___x_1775_ = lean_uint64_to_usize(v___x_1774_);
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1771_, v___x_1775_, v___x_1776_, v_x_1772_, v_x_1773_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1778_, lean_object* v_val_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v_mctx_1783_; lean_object* v_cache_1784_; lean_object* v_zetaDeltaFVarIds_1785_; lean_object* v_postponed_1786_; lean_object* v_diag_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1815_; 
v___x_1782_ = lean_st_ref_take(v___y_1780_);
v_mctx_1783_ = lean_ctor_get(v___x_1782_, 0);
v_cache_1784_ = lean_ctor_get(v___x_1782_, 1);
v_zetaDeltaFVarIds_1785_ = lean_ctor_get(v___x_1782_, 2);
v_postponed_1786_ = lean_ctor_get(v___x_1782_, 3);
v_diag_1787_ = lean_ctor_get(v___x_1782_, 4);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1789_ = v___x_1782_;
v_isShared_1790_ = v_isSharedCheck_1815_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_diag_1787_);
lean_inc(v_postponed_1786_);
lean_inc(v_zetaDeltaFVarIds_1785_);
lean_inc(v_cache_1784_);
lean_inc(v_mctx_1783_);
lean_dec(v___x_1782_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1815_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_depth_1791_; lean_object* v_levelAssignDepth_1792_; lean_object* v_lmvarCounter_1793_; lean_object* v_mvarCounter_1794_; lean_object* v_lDecls_1795_; lean_object* v_decls_1796_; lean_object* v_userNames_1797_; lean_object* v_lAssignment_1798_; lean_object* v_eAssignment_1799_; lean_object* v_dAssignment_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1814_; 
v_depth_1791_ = lean_ctor_get(v_mctx_1783_, 0);
v_levelAssignDepth_1792_ = lean_ctor_get(v_mctx_1783_, 1);
v_lmvarCounter_1793_ = lean_ctor_get(v_mctx_1783_, 2);
v_mvarCounter_1794_ = lean_ctor_get(v_mctx_1783_, 3);
v_lDecls_1795_ = lean_ctor_get(v_mctx_1783_, 4);
v_decls_1796_ = lean_ctor_get(v_mctx_1783_, 5);
v_userNames_1797_ = lean_ctor_get(v_mctx_1783_, 6);
v_lAssignment_1798_ = lean_ctor_get(v_mctx_1783_, 7);
v_eAssignment_1799_ = lean_ctor_get(v_mctx_1783_, 8);
v_dAssignment_1800_ = lean_ctor_get(v_mctx_1783_, 9);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_mctx_1783_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1802_ = v_mctx_1783_;
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_dAssignment_1800_);
lean_inc(v_eAssignment_1799_);
lean_inc(v_lAssignment_1798_);
lean_inc(v_userNames_1797_);
lean_inc(v_decls_1796_);
lean_inc(v_lDecls_1795_);
lean_inc(v_mvarCounter_1794_);
lean_inc(v_lmvarCounter_1793_);
lean_inc(v_levelAssignDepth_1792_);
lean_inc(v_depth_1791_);
lean_dec(v_mctx_1783_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1799_, v_mvarId_1778_, v_val_1779_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 8, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_depth_1791_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_levelAssignDepth_1792_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_lmvarCounter_1793_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_mvarCounter_1794_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_lDecls_1795_);
lean_ctor_set(v_reuseFailAlloc_1813_, 5, v_decls_1796_);
lean_ctor_set(v_reuseFailAlloc_1813_, 6, v_userNames_1797_);
lean_ctor_set(v_reuseFailAlloc_1813_, 7, v_lAssignment_1798_);
lean_ctor_set(v_reuseFailAlloc_1813_, 8, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 9, v_dAssignment_1800_);
v___x_1806_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1806_);
v___x_1808_ = v___x_1789_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_cache_1784_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_zetaDeltaFVarIds_1785_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_postponed_1786_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_diag_1787_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_st_ref_set(v___y_1780_, v___x_1808_);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1816_, lean_object* v_val_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1816_, v_val_1817_, v___y_1818_);
lean_dec(v___y_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = 0;
return v___x_1823_;
}
else
{
lean_object* v_head_1824_; lean_object* v_tail_1825_; uint8_t v___x_1826_; 
v_head_1824_ = lean_ctor_get(v_x_1822_, 0);
v_tail_1825_ = lean_ctor_get(v_x_1822_, 1);
v___x_1826_ = l_Lean_instBEqMVarId_beq(v_a_1821_, v_head_1824_);
if (v___x_1826_ == 0)
{
v_x_1822_ = v_tail_1825_;
goto _start;
}
else
{
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_res_1830_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1828_, v_x_1829_);
lean_dec(v_x_1829_);
lean_dec(v_a_1828_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1832_, lean_object* v_as_1833_, size_t v_i_1834_, size_t v_stop_1835_, lean_object* v_b_1836_){
_start:
{
lean_object* v___y_1838_; uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_eq(v_i_1834_, v_stop_1835_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_array_uget_borrowed(v_as_1833_, v_i_1834_);
v___x_1844_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1843_, v_a_1832_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_inc(v___x_1843_);
v___x_1845_ = lean_array_push(v_b_1836_, v___x_1843_);
v___y_1838_ = v___x_1845_;
goto v___jp_1837_;
}
else
{
v___y_1838_ = v_b_1836_;
goto v___jp_1837_;
}
}
else
{
return v_b_1836_;
}
v___jp_1837_:
{
size_t v___x_1839_; size_t v___x_1840_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1834_, v___x_1839_);
v_i_1834_ = v___x_1840_;
v_b_1836_ = v___y_1838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1846_, lean_object* v_as_1847_, lean_object* v_i_1848_, lean_object* v_stop_1849_, lean_object* v_b_1850_){
_start:
{
size_t v_i_boxed_1851_; size_t v_stop_boxed_1852_; lean_object* v_res_1853_; 
v_i_boxed_1851_ = lean_unbox_usize(v_i_1848_);
lean_dec(v_i_1848_);
v_stop_boxed_1852_ = lean_unbox_usize(v_stop_1849_);
lean_dec(v_stop_1849_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1846_, v_as_1847_, v_i_boxed_1851_, v_stop_boxed_1852_, v_b_1850_);
lean_dec_ref(v_as_1847_);
lean_dec(v_a_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1854_, lean_object* v___x_1855_, lean_object* v_e_1856_, lean_object* v_cfg_1857_, lean_object* v_term_x3f_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; uint8_t v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v_a_1899_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___x_1950_; 
lean_inc(v___x_1855_);
lean_inc(v_mvarId_1854_);
v___x_1950_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1854_, v___x_1855_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref_known(v___x_1950_, 1);
lean_inc(v_mvarId_1854_);
v___x_1951_ = l_Lean_MVarId_getType(v_mvarId_1854_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc_ref(v___y_1859_);
lean_inc_ref(v_e_1856_);
v___x_1953_ = lean_infer_type(v_e_1856_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_rangeNumArgs_1956_; lean_object* v_lower_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___x_2001_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc_n(v_a_1954_, 2);
lean_dec_ref_known(v___x_1953_, 1);
v___x_2001_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1954_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v_snd_2003_; uint8_t v___x_2004_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v_snd_2003_ = lean_ctor_get(v_a_2002_, 1);
v___x_2004_ = lean_unbox(v_snd_2003_);
if (v___x_2004_ == 0)
{
lean_object* v_fst_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2025_; 
v_fst_2005_ = lean_ctor_get(v_a_2002_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_a_2002_, 1);
lean_dec(v_unused_2026_);
v___x_2007_ = v_a_2002_;
v_isShared_2008_ = v_isSharedCheck_2025_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_fst_2005_);
lean_dec(v_a_2002_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2025_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; 
lean_inc(v_a_1952_);
v___x_2009_ = l_Lean_Meta_getExpectedNumArgs(v_a_1952_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_nat_sub(v_fst_2005_, v_a_2010_);
lean_dec(v_a_2010_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_fst_2005_, v___x_2012_);
lean_dec(v_fst_2005_);
lean_inc(v___x_2011_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2013_);
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2015_ = v___x_2007_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
v_rangeNumArgs_1956_ = v___x_2015_;
v_lower_1957_ = v___x_2011_;
v___y_1958_ = v___y_1859_;
v___y_1959_ = v___y_1860_;
v___y_1960_ = v___y_1861_;
v___y_1961_ = v___y_1862_;
goto v___jp_1955_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_2007_);
lean_dec(v_fst_2005_);
lean_dec(v_a_1954_);
lean_dec(v_a_1952_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_term_x3f_1858_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_2017_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2009_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2009_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v_fst_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2036_; 
v_fst_2027_ = lean_ctor_get(v_a_2002_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_a_2002_, 1);
lean_dec(v_unused_2037_);
v___x_2029_ = v_a_2002_;
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_fst_2027_);
lean_dec(v_a_2002_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_nat_add(v_fst_2027_, v___x_2031_);
lean_inc(v_fst_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_fst_2027_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
v_rangeNumArgs_1956_ = v___x_2034_;
v_lower_1957_ = v_fst_2027_;
v___y_1958_ = v___y_1859_;
v___y_1959_ = v___y_1860_;
v___y_1960_ = v___y_1861_;
v___y_1961_ = v___y_1862_;
goto v___jp_1955_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_1954_);
lean_dec(v_a_1952_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_term_x3f_1858_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_2038_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2001_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2001_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
v___jp_1955_:
{
lean_object* v___x_1962_; 
lean_inc(v_mvarId_1854_);
v___x_1962_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1854_, v_cfg_1857_, v_term_x3f_1858_, v_a_1952_, v_a_1954_, v_rangeNumArgs_1956_, v_lower_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec_ref(v_rangeNumArgs_1956_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_fst_1964_; lean_object* v_snd_1965_; uint8_t v_newGoals_1966_; uint8_t v_synthAssignedInstances_1967_; uint8_t v_allowSynthFailures_1968_; lean_object* v___x_1969_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v_fst_1964_ = lean_ctor_get(v_a_1963_, 0);
lean_inc(v_fst_1964_);
v_snd_1965_ = lean_ctor_get(v_a_1963_, 1);
lean_inc_n(v_snd_1965_, 2);
lean_dec(v_a_1963_);
v_newGoals_1966_ = lean_ctor_get_uint8(v_cfg_1857_, 0);
v_synthAssignedInstances_1967_ = lean_ctor_get_uint8(v_cfg_1857_, 1);
v_allowSynthFailures_1968_ = lean_ctor_get_uint8(v_cfg_1857_, 2);
lean_inc(v_mvarId_1854_);
v___x_1969_ = l_Lean_Meta_synthAppInstances(v___x_1855_, v_mvarId_1854_, v_fst_1964_, v_snd_1965_, v_synthAssignedInstances_1967_, v_allowSynthFailures_1968_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1970_; lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
lean_dec_ref_known(v___x_1969_, 1);
v___x_1970_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1856_, v___y_1959_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc_n(v_a_1971_, 2);
lean_dec_ref(v___x_1970_);
v___x_1972_ = l_Lean_mkAppN(v_a_1971_, v_fst_1964_);
lean_inc(v_mvarId_1854_);
v___x_1973_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1854_, v___x_1972_, v___y_1959_);
lean_dec_ref(v___x_1973_);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_fst_1964_);
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1977_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
if (v___x_1977_ == 0)
{
lean_dec(v_fst_1964_);
v___y_1891_ = v___x_1974_;
v___y_1892_ = v___y_1961_;
v___y_1893_ = v___y_1960_;
v___y_1894_ = v___y_1958_;
v___y_1895_ = v_newGoals_1966_;
v___y_1896_ = v_snd_1965_;
v___y_1897_ = v___y_1959_;
v___y_1898_ = v_a_1971_;
v_a_1899_ = v___x_1976_;
goto v___jp_1890_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_le(v___x_1975_, v___x_1975_);
if (v___x_1978_ == 0)
{
if (v___x_1977_ == 0)
{
lean_dec(v_fst_1964_);
v___y_1891_ = v___x_1974_;
v___y_1892_ = v___y_1961_;
v___y_1893_ = v___y_1960_;
v___y_1894_ = v___y_1958_;
v___y_1895_ = v_newGoals_1966_;
v___y_1896_ = v_snd_1965_;
v___y_1897_ = v___y_1959_;
v___y_1898_ = v_a_1971_;
v_a_1899_ = v___x_1976_;
goto v___jp_1890_;
}
else
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1975_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1964_, v___x_1979_, v___x_1980_, v___x_1976_, v___y_1959_);
lean_dec(v_fst_1964_);
v___y_1932_ = v___y_1958_;
v___y_1933_ = v___y_1960_;
v___y_1934_ = v___y_1961_;
v___y_1935_ = v___x_1974_;
v___y_1936_ = v_snd_1965_;
v___y_1937_ = v_newGoals_1966_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v_a_1971_;
v___y_1940_ = v___x_1981_;
goto v___jp_1931_;
}
}
else
{
size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = lean_usize_of_nat(v___x_1975_);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1964_, v___x_1982_, v___x_1983_, v___x_1976_, v___y_1959_);
lean_dec(v_fst_1964_);
v___y_1932_ = v___y_1958_;
v___y_1933_ = v___y_1960_;
v___y_1934_ = v___y_1961_;
v___y_1935_ = v___x_1974_;
v___y_1936_ = v_snd_1965_;
v___y_1937_ = v_newGoals_1966_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v_a_1971_;
v___y_1940_ = v___x_1984_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_snd_1965_);
lean_dec(v_fst_1964_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_e_1856_);
lean_dec(v_mvarId_1854_);
v_a_1985_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1969_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1969_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_1993_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1962_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1962_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_1952_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_term_x3f_1858_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_2046_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1953_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1953_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_term_x3f_1858_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_2054_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_1951_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_1951_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_term_x3f_1858_);
lean_dec_ref(v_e_1856_);
lean_dec(v___x_1855_);
lean_dec(v_mvarId_1854_);
v_a_2062_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1950_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1950_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
v___jp_1864_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_array_to_list(v___y_1870_);
v___x_1872_ = l_List_appendTR___redArg(v___y_1868_, v___x_1871_);
lean_inc(v___x_1872_);
v___x_1873_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1872_, v___y_1867_, v___y_1869_, v___y_1866_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1867_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1873_, 0);
lean_dec(v_unused_1881_);
v___x_1875_ = v___x_1873_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_dec(v___x_1873_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1872_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1872_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v___x_1872_);
v_a_1882_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1873_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1890_:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Meta_appendParentTag(v_mvarId_1854_, v_a_1899_, v___y_1896_, v___y_1894_, v___y_1897_, v___y_1893_, v___y_1892_);
lean_dec_ref(v___y_1896_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1901_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1898_, v___y_1894_, v___y_1897_, v___y_1893_, v___y_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1899_, v___y_1895_, v___y_1894_, v___y_1897_, v___y_1893_, v___y_1892_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = lean_array_get_size(v_a_1902_);
v___x_1906_ = lean_mk_empty_array_with_capacity(v___y_1891_);
v___x_1907_ = lean_nat_dec_lt(v___y_1891_, v___x_1905_);
if (v___x_1907_ == 0)
{
lean_dec(v_a_1902_);
v___y_1865_ = v___y_1892_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v_a_1904_;
v___y_1869_ = v___y_1897_;
v___y_1870_ = v___x_1906_;
goto v___jp_1864_;
}
else
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_le(v___x_1905_, v___x_1905_);
if (v___x_1908_ == 0)
{
if (v___x_1907_ == 0)
{
lean_dec(v_a_1902_);
v___y_1865_ = v___y_1892_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v_a_1904_;
v___y_1869_ = v___y_1897_;
v___y_1870_ = v___x_1906_;
goto v___jp_1864_;
}
else
{
size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = lean_usize_of_nat(v___x_1905_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1904_, v_a_1902_, v___x_1909_, v___x_1910_, v___x_1906_);
lean_dec(v_a_1902_);
v___y_1865_ = v___y_1892_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v_a_1904_;
v___y_1869_ = v___y_1897_;
v___y_1870_ = v___x_1911_;
goto v___jp_1864_;
}
}
else
{
size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = lean_usize_of_nat(v___x_1905_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1904_, v_a_1902_, v___x_1912_, v___x_1913_, v___x_1906_);
lean_dec(v_a_1902_);
v___y_1865_ = v___y_1892_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v_a_1904_;
v___y_1869_ = v___y_1897_;
v___y_1870_ = v___x_1914_;
goto v___jp_1864_;
}
}
}
else
{
lean_dec(v_a_1902_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
return v___x_1903_;
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v_a_1899_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
v_a_1915_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1901_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1901_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_a_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
v_a_1923_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1900_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1900_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
v___jp_1931_:
{
if (lean_obj_tag(v___y_1940_) == 0)
{
lean_object* v_a_1941_; 
v_a_1941_ = lean_ctor_get(v___y_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___y_1940_, 1);
v___y_1891_ = v___y_1935_;
v___y_1892_ = v___y_1934_;
v___y_1893_ = v___y_1933_;
v___y_1894_ = v___y_1932_;
v___y_1895_ = v___y_1937_;
v___y_1896_ = v___y_1936_;
v___y_1897_ = v___y_1938_;
v___y_1898_ = v___y_1939_;
v_a_1899_ = v_a_1941_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v_mvarId_1854_);
v_a_1942_ = lean_ctor_get(v___y_1940_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___y_1940_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___y_1940_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___y_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2070_, lean_object* v___x_2071_, lean_object* v_e_2072_, lean_object* v_cfg_2073_, lean_object* v_term_x3f_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2070_, v___x_2071_, v_e_2072_, v_cfg_2073_, v_term_x3f_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec_ref(v_cfg_2073_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2081_, lean_object* v_e_2082_, lean_object* v_cfg_2083_, lean_object* v_term_x3f_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2081_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2091_, 0, v_mvarId_2081_);
lean_closure_set(v___f_2091_, 1, v___x_2090_);
lean_closure_set(v___f_2091_, 2, v_e_2082_);
lean_closure_set(v___f_2091_, 3, v_cfg_2083_);
lean_closure_set(v___f_2091_, 4, v_term_x3f_2084_);
v___x_2092_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2081_, v___f_2091_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2093_, lean_object* v_e_2094_, lean_object* v_cfg_2095_, lean_object* v_term_x3f_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_MVarId_apply(v_mvarId_2093_, v_e_2094_, v_cfg_2095_, v_term_x3f_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2103_, lean_object* v_val_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2103_, v_val_2104_, v___y_2106_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2111_, lean_object* v_val_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2111_, v_val_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2119_, size_t v_i_2120_, size_t v_stop_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2119_, v_i_2120_, v_stop_2121_, v_b_2122_, v___y_2124_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2129_, lean_object* v_i_2130_, lean_object* v_stop_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
size_t v_i_boxed_2138_; size_t v_stop_boxed_2139_; lean_object* v_res_2140_; 
v_i_boxed_2138_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_stop_boxed_2139_ = lean_unbox_usize(v_stop_2131_);
lean_dec(v_stop_2131_);
v_res_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2129_, v_i_boxed_2138_, v_stop_boxed_2139_, v_b_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_as_2129_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2142_, v_x_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, size_t v_x_2148_, size_t v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2147_, v_x_2148_, v_x_2149_, v_x_2150_, v_x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
size_t v_x_7967__boxed_2159_; size_t v_x_7968__boxed_2160_; lean_object* v_res_2161_; 
v_x_7967__boxed_2159_ = lean_unbox_usize(v_x_2155_);
lean_dec(v_x_2155_);
v_x_7968__boxed_2160_ = lean_unbox_usize(v_x_2156_);
lean_dec(v_x_2156_);
v_res_2161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2153_, v_x_2154_, v_x_7967__boxed_2159_, v_x_7968__boxed_2160_, v_x_2157_, v_x_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2162_, lean_object* v_n_2163_, lean_object* v_k_2164_, lean_object* v_v_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2163_, v_k_2164_, v_v_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2167_, size_t v_depth_2168_, lean_object* v_keys_2169_, lean_object* v_vals_2170_, lean_object* v_heq_2171_, lean_object* v_i_2172_, lean_object* v_entries_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2168_, v_keys_2169_, v_vals_2170_, v_i_2172_, v_entries_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_depth_2176_, lean_object* v_keys_2177_, lean_object* v_vals_2178_, lean_object* v_heq_2179_, lean_object* v_i_2180_, lean_object* v_entries_2181_){
_start:
{
size_t v_depth_boxed_2182_; lean_object* v_res_2183_; 
v_depth_boxed_2182_ = lean_unbox_usize(v_depth_2176_);
lean_dec(v_depth_2176_);
v_res_2183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2175_, v_depth_boxed_2182_, v_keys_2177_, v_vals_2178_, v_heq_2179_, v_i_2180_, v_entries_2181_);
lean_dec_ref(v_vals_2178_);
lean_dec_ref(v_keys_2177_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2185_, v_x_2186_, v_x_2187_, v_x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2193_, lean_object* v_c_2194_, lean_object* v_cfg_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; 
lean_inc(v_c_2194_);
v___x_2201_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2194_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2204_ = 0;
v___x_2205_ = l_Lean_MessageData_ofConstName(v_c_2194_, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2203_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___x_2203_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = l_Lean_MVarId_apply(v_mvar_2193_, v_a_2202_, v_cfg_2195_, v___x_2208_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2209_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_cfg_2195_);
lean_dec(v_c_2194_);
lean_dec(v_mvar_2193_);
v_a_2210_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2201_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2201_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2218_, lean_object* v_c_2219_, lean_object* v_cfg_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_MVarId_applyConst(v_mvar_2218_, v_c_2219_, v_cfg_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v_env_2234_; lean_object* v___x_2235_; lean_object* v_mctx_2236_; lean_object* v_lctx_2237_; lean_object* v_options_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2233_ = lean_st_ref_get(v___y_2231_);
v_env_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_env_2234_);
lean_dec(v___x_2233_);
v___x_2235_ = lean_st_ref_get(v___y_2229_);
v_mctx_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_mctx_2236_);
lean_dec(v___x_2235_);
v_lctx_2237_ = lean_ctor_get(v___y_2228_, 2);
v_options_2238_ = lean_ctor_get(v___y_2230_, 2);
lean_inc_ref(v_options_2238_);
lean_inc_ref(v_lctx_2237_);
v___x_2239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2239_, 0, v_env_2234_);
lean_ctor_set(v___x_2239_, 1, v_mctx_2236_);
lean_ctor_set(v___x_2239_, 2, v_lctx_2237_);
lean_ctor_set(v___x_2239_, 3, v_options_2238_);
v___x_2240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v_msgData_2227_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_ref_2255_; lean_object* v___x_2256_; lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2265_; 
v_ref_2255_ = lean_ctor_get(v___y_2252_, 5);
v___x_2256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
lean_inc(v_ref_2255_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_ref_2255_);
lean_ctor_set(v___x_2261_, 1, v_a_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 0, v___x_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2276_ == 0)
{
return v_bs_2275_;
}
else
{
lean_object* v_v_2277_; lean_object* v___x_2278_; lean_object* v_bs_x27_2279_; lean_object* v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; lean_object* v___x_2283_; 
v_v_2277_ = lean_array_uget(v_bs_2275_, v_i_2274_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v_bs_x27_2279_ = lean_array_uset(v_bs_2275_, v_i_2274_, v___x_2278_);
v___x_2280_ = l_Lean_Expr_mvarId_x21(v_v_2277_);
lean_dec(v_v_2277_);
v___x_2281_ = ((size_t)1ULL);
v___x_2282_ = lean_usize_add(v_i_2274_, v___x_2281_);
v___x_2283_ = lean_array_uset(v_bs_x27_2279_, v_i_2274_, v___x_2280_);
v_i_2274_ = v___x_2282_;
v_bs_2275_ = v___x_2283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2285_, lean_object* v_i_2286_, lean_object* v_bs_2287_){
_start:
{
size_t v_sz_boxed_2288_; size_t v_i_boxed_2289_; lean_object* v_res_2290_; 
v_sz_boxed_2288_ = lean_unbox_usize(v_sz_2285_);
lean_dec(v_sz_2285_);
v_i_boxed_2289_ = lean_unbox_usize(v_i_2286_);
lean_dec(v_i_2286_);
v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2288_, v_i_boxed_2289_, v_bs_2287_);
return v_res_2290_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2308_ = l_Lean_stringToMessageData(v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2309_, lean_object* v___x_2310_, lean_object* v_e_2311_, lean_object* v_n_2312_, uint8_t v_useApproxDefEq_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc(v_mvarId_2309_);
v___x_2319_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2309_, v___x_2310_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; 
lean_dec_ref_known(v___x_2319_, 1);
lean_inc(v_mvarId_2309_);
v___x_2320_ = l_Lean_MVarId_getType(v_mvarId_2309_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc_ref(v_e_2311_);
v___x_2322_ = lean_infer_type(v_e_2311_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = 0;
lean_inc(v_n_2312_);
v___x_2325_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2323_, v_n_2312_, v___x_2324_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2418_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v_fst_2327_ = lean_ctor_get(v_a_2326_, 0);
v_snd_2328_ = lean_ctor_get(v_a_2326_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_a_2326_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2330_ = v_a_2326_;
v_isShared_2331_ = v_isSharedCheck_2418_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_inc(v_fst_2327_);
lean_dec(v_a_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2418_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___y_2333_; lean_object* v_snd_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2416_; 
v_snd_2348_ = lean_ctor_get(v_snd_2328_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_snd_2328_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v_snd_2328_, 0);
lean_dec(v_unused_2417_);
v___x_2350_ = v_snd_2328_;
v_isShared_2351_ = v_isSharedCheck_2416_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_snd_2348_);
lean_dec(v_snd_2328_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2416_;
goto v_resetjp_2349_;
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2346_; 
lean_inc(v_fst_2327_);
v___x_2334_ = l_Lean_Expr_beta(v_e_2311_, v_fst_2327_);
v___x_2335_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2309_, v___x_2334_, v___y_2333_);
lean_dec(v___y_2333_);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v___x_2335_, 0);
lean_dec(v_unused_2347_);
v___x_2337_ = v___x_2335_;
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v___x_2335_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
size_t v_sz_2339_; size_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v_sz_2339_ = lean_array_size(v_fst_2327_);
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2339_, v___x_2340_, v_fst_2327_);
v___x_2342_ = lean_array_to_list(v___x_2341_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2342_);
v___x_2344_ = v___x_2337_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
v_resetjp_2349_:
{
lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_array_get_size(v_fst_2327_);
v___x_2397_ = lean_nat_dec_eq(v___x_2396_, v_n_2312_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_del_object(v___x_2350_);
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
lean_dec(v_a_2321_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v___x_2398_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2399_ = l_Nat_reprFast(v_n_2312_);
v___x_2400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
v___x_2401_ = l_Lean_MessageData_ofFormat(v___x_2400_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2398_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_indentExpr(v_snd_2348_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2406_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
v___y_2353_ = v___y_2314_;
v___y_2354_ = v___y_2315_;
v___y_2355_ = v___y_2316_;
v___y_2356_ = v___y_2317_;
goto v___jp_2352_;
}
v___jp_2352_:
{
lean_object* v___x_2357_; 
lean_inc(v_a_2321_);
lean_inc(v_snd_2348_);
v___x_2357_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2313_, v_snd_2348_, v_a_2321_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = lean_unbox(v_a_2358_);
lean_dec(v_a_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_fst_2327_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v___x_2360_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2361_ = l_Lean_indentExpr(v_a_2321_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 7);
lean_ctor_set(v___x_2350_, 1, v___x_2361_);
lean_ctor_set(v___x_2350_, 0, v___x_2360_);
v___x_2363_ = v___x_2350_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 7);
lean_ctor_set(v___x_2330_, 1, v___x_2364_);
lean_ctor_set(v___x_2330_, 0, v___x_2363_);
v___x_2366_ = v___x_2330_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v___x_2367_ = l_Lean_indentExpr(v_snd_2348_);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = l_Nat_reprFast(v_n_2312_);
v___x_2372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
v___x_2373_ = l_Lean_MessageData_ofFormat(v___x_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2370_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2376_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v___y_2353_);
lean_del_object(v___x_2350_);
lean_dec(v_snd_2348_);
lean_del_object(v___x_2330_);
lean_dec(v_a_2321_);
lean_dec(v_n_2312_);
v___y_2333_ = v___y_2354_;
goto v___jp_2332_;
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_del_object(v___x_2350_);
lean_dec(v_snd_2348_);
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
lean_dec(v_a_2321_);
lean_dec(v_n_2312_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v_a_2388_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2357_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2357_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_a_2321_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v_n_2312_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v_a_2419_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2325_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2325_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_a_2321_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v_n_2312_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v_a_2427_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2322_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2322_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v_n_2312_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v_a_2435_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2320_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2320_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v_n_2312_);
lean_dec_ref(v_e_2311_);
lean_dec(v_mvarId_2309_);
v_a_2443_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2319_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2319_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2451_, lean_object* v___x_2452_, lean_object* v_e_2453_, lean_object* v_n_2454_, lean_object* v_useApproxDefEq_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2461_; lean_object* v_res_2462_; 
v_useApproxDefEq_boxed_2461_ = lean_unbox(v_useApproxDefEq_2455_);
v_res_2462_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2451_, v___x_2452_, v_e_2453_, v_n_2454_, v_useApproxDefEq_boxed_2461_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2463_, lean_object* v_e_2464_, lean_object* v_n_2465_, uint8_t v_useApproxDefEq_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2473_ = lean_box(v_useApproxDefEq_2466_);
lean_inc(v_mvarId_2463_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2474_, 0, v_mvarId_2463_);
lean_closure_set(v___f_2474_, 1, v___x_2472_);
lean_closure_set(v___f_2474_, 2, v_e_2464_);
lean_closure_set(v___f_2474_, 3, v_n_2465_);
lean_closure_set(v___f_2474_, 4, v___x_2473_);
v___x_2475_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2463_, v___f_2474_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2476_, lean_object* v_e_2477_, lean_object* v_n_2478_, lean_object* v_useApproxDefEq_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2485_; lean_object* v_res_2486_; 
v_useApproxDefEq_boxed_2485_ = lean_unbox(v_useApproxDefEq_2479_);
v_res_2486_ = l_Lean_MVarId_applyN(v_mvarId_2476_, v_e_2477_, v_n_2478_, v_useApproxDefEq_boxed_2485_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2487_, lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2495_, lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2495_, v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_box(0);
v___x_2514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2515_ = l_Lean_mkConst(v___x_2514_, v___x_2513_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2516_, lean_object* v_type_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; 
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
v___x_2524_ = lean_whnf(v_type_2517_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2527_ = lean_unsigned_to_nat(2u);
v___x_2528_ = l_Lean_Expr_isAppOfArity(v_a_2525_, v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2529_ = lean_st_ref_get(v_a_2518_);
v___x_2530_ = lean_array_get_size(v___x_2529_);
lean_dec(v___x_2529_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_add(v___x_2530_, v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2534_ = lean_name_append_index_after(v___x_2533_, v___x_2532_);
v___x_2535_ = l_Lean_Name_append(v_tag_2516_, v___x_2534_);
v___x_2536_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2525_, v___x_2535_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2548_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2541_ = lean_st_ref_take(v_a_2518_);
v___x_2542_ = l_Lean_Expr_mvarId_x21(v_a_2537_);
v___x_2543_ = lean_array_push(v___x_2541_, v___x_2542_);
v___x_2544_ = lean_st_ref_set(v_a_2518_, v___x_2543_);
if (v_isShared_2540_ == 0)
{
v___x_2546_ = v___x_2539_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2537_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
return v___x_2536_;
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = l_Lean_Expr_appFn_x21(v_a_2525_);
v___x_2550_ = l_Lean_Expr_appArg_x21(v___x_2549_);
lean_dec_ref(v___x_2549_);
lean_inc_ref(v___x_2550_);
lean_inc(v_tag_2516_);
v___x_2551_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2516_, v___x_2550_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = l_Lean_Expr_appArg_x21(v_a_2525_);
lean_dec(v_a_2525_);
lean_inc_ref(v___x_2553_);
v___x_2554_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2516_, v___x_2553_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2564_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2564_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2564_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2560_ = l_Lean_mkApp4(v___x_2559_, v___x_2550_, v___x_2553_, v_a_2552_, v_a_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2560_);
v___x_2562_ = v___x_2557_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_dec_ref(v___x_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v___x_2550_);
return v___x_2554_;
}
}
else
{
lean_dec_ref(v___x_2550_);
lean_dec(v_a_2525_);
lean_dec(v_tag_2516_);
return v___x_2551_;
}
}
}
else
{
lean_dec(v_tag_2516_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2565_, lean_object* v_type_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2565_, v_type_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2574_, lean_object* v___x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
lean_inc(v_mvarId_2574_);
v___x_2581_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2574_, v___x_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; 
lean_dec_ref_known(v___x_2581_, 1);
lean_inc(v_mvarId_2574_);
v___x_2582_ = l_Lean_MVarId_getType_x27(v_mvarId_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2628_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2628_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2628_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2588_ = lean_unsigned_to_nat(2u);
v___x_2589_ = l_Lean_Expr_isAppOfArity(v_a_2583_, v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec(v_a_2583_);
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_mvarId_2574_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2591_);
v___x_2593_ = v___x_2585_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
else
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2585_);
lean_inc(v_mvarId_2574_);
v___x_2595_ = l_Lean_MVarId_getTag(v_mvarId_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2598_ = lean_st_mk_ref(v___x_2597_);
v___x_2599_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2596_, v_a_2583_, v___x_2598_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = lean_st_ref_get(v___x_2598_);
lean_dec(v___x_2598_);
v___x_2602_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2574_, v_a_2600_, v___y_2577_);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; 
v_unused_2611_ = lean_ctor_get(v___x_2602_, 0);
lean_dec(v_unused_2611_);
v___x_2604_ = v___x_2602_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v___x_2602_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_array_to_list(v___x_2601_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v___x_2598_);
lean_dec(v_mvarId_2574_);
v_a_2612_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2599_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2599_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_a_2583_);
lean_dec(v_mvarId_2574_);
v_a_2620_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2595_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2595_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_mvarId_2574_);
v_a_2629_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2582_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2582_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_mvarId_2574_);
v_a_2637_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2581_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2581_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2645_, lean_object* v___x_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2645_, v___x_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v___f_2663_; lean_object* v___x_2664_; 
v___x_2662_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2656_);
v___f_2663_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2663_, 0, v_mvarId_2656_);
lean_closure_set(v___f_2663_, 1, v___x_2662_);
v___x_2664_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2656_, v___f_2663_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_MVarId_splitAndCore(v_mvarId_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_MVarId_splitAndCore(v_mvarId_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_MVarId_splitAnd(v_mvarId_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2685_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2691_ = l_Lean_mkConst(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2696_, lean_object* v___x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
lean_inc(v_mvarId_2696_);
v___x_2703_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2696_, v___x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___x_2704_; 
lean_dec_ref_known(v___x_2703_, 1);
lean_inc(v_mvarId_2696_);
v___x_2704_ = l_Lean_MVarId_getType(v_mvarId_2696_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; lean_object* v_a_2707_; lean_object* v___x_2708_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2706_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2705_, v___y_2699_);
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc_n(v_a_2707_, 2);
lean_dec_ref(v___x_2706_);
v___x_2708_ = l_Lean_Meta_getLevel(v_a_2707_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
lean_inc(v_mvarId_2696_);
v___x_2710_ = l_Lean_MVarId_getTag(v_mvarId_2696_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2714_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2713_, v_a_2711_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc_n(v_a_2715_, 2);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2709_);
lean_ctor_set(v___x_2717_, 1, v___x_2712_);
v___x_2718_ = l_Lean_mkConst(v___x_2716_, v___x_2717_);
v___x_2719_ = l_Lean_mkAppB(v___x_2718_, v_a_2707_, v_a_2715_);
v___x_2720_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2696_, v___x_2719_, v___y_2699_);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2720_, 0);
lean_dec(v_unused_2729_);
v___x_2722_ = v___x_2720_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v___x_2720_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = l_Lean_Expr_mvarId_x21(v_a_2715_);
lean_dec(v_a_2715_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_a_2709_);
lean_dec(v_a_2707_);
lean_dec(v_mvarId_2696_);
v_a_2730_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2714_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2714_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2709_);
lean_dec(v_a_2707_);
lean_dec(v_mvarId_2696_);
v_a_2738_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2710_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2710_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2707_);
lean_dec(v_mvarId_2696_);
v_a_2746_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2708_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2708_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_mvarId_2696_);
v_a_2754_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2704_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2704_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_mvarId_2696_);
v_a_2762_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2703_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2703_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2770_, lean_object* v___x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2770_, v___x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v___f_2788_; lean_object* v___x_2789_; 
v___x_2787_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2781_);
v___f_2788_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2788_, 0, v_mvarId_2781_);
lean_closure_set(v___f_2788_, 1, v___x_2787_);
v___x_2789_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2781_, v___f_2788_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_MVarId_exfalso(v_mvarId_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
return v_res_2796_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2801_ = l_Lean_MessageData_ofFormat(v___x_2800_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2808_, lean_object* v_name_2809_, lean_object* v_idx_2810_, lean_object* v_expected_x3f_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___x_2824_; 
lean_inc(v_name_2809_);
lean_inc(v_goal_2808_);
v___x_2824_ = l_Lean_MVarId_checkNotAssigned(v_goal_2808_, v_name_2809_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2824_, 1);
lean_inc(v_goal_2808_);
v___x_2825_ = l_Lean_MVarId_getType_x27(v_goal_2808_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l_Lean_Expr_getAppFn(v_a_2826_);
lean_dec(v_a_2826_);
if (lean_obj_tag(v___x_2827_) == 4)
{
lean_object* v_declName_2828_; lean_object* v_us_2829_; lean_object* v___x_2830_; lean_object* v_env_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; 
v_declName_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_declName_2828_);
v_us_2829_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_us_2829_);
lean_dec_ref_known(v___x_2827_, 2);
v___x_2830_ = lean_st_ref_get(v___y_2815_);
v_env_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc_ref(v_env_2831_);
lean_dec(v___x_2830_);
v___x_2832_ = 0;
v___x_2833_ = l_Lean_Environment_find_x3f(v_env_2831_, v_declName_2828_, v___x_2832_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_dec(v_us_2829_);
lean_dec(v_expected_x3f_2811_);
lean_dec(v_idx_2810_);
v___y_2818_ = v___y_2812_;
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
goto v___jp_2817_;
}
else
{
lean_object* v_val_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2904_; 
v_val_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2904_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_val_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2904_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_val_2834_) == 5)
{
lean_object* v_val_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2903_; 
v_val_2838_ = lean_ctor_get(v_val_2834_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_val_2834_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2840_ = v_val_2834_;
v_isShared_2841_ = v_isSharedCheck_2903_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_val_2838_);
lean_dec(v_val_2834_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2903_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; 
if (lean_obj_tag(v_expected_x3f_2811_) == 1)
{
lean_object* v_val_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2902_; 
v_val_2873_ = lean_ctor_get(v_expected_x3f_2811_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_expected_x3f_2811_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2875_ = v_expected_x3f_2811_;
v_isShared_2876_ = v_isSharedCheck_2902_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_val_2873_);
lean_dec(v_expected_x3f_2811_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2902_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_ctors_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v_ctors_2877_ = lean_ctor_get(v_val_2838_, 4);
v___x_2878_ = l_List_lengthTR___redArg(v_ctors_2877_);
v___x_2879_ = lean_nat_dec_eq(v___x_2878_, v_val_2873_);
lean_dec(v___x_2878_);
if (v___x_2879_ == 0)
{
uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2880_ = 1;
lean_inc(v_name_2809_);
v___x_2881_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2809_, v___x_2880_);
v___x_2882_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2883_ = lean_string_append(v___x_2881_, v___x_2882_);
v___x_2884_ = l_Nat_reprFast(v_val_2873_);
v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2887_ = lean_string_append(v___x_2885_, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
v___x_2889_ = l_Lean_MessageData_ofFormat(v___x_2888_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2889_);
v___x_2891_ = v___x_2875_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; 
lean_inc(v_goal_2808_);
lean_inc(v_name_2809_);
v___x_2892_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2809_, v_goal_2808_, v___x_2891_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref_known(v___x_2892_, 1);
v___y_2843_ = v___y_2812_;
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_del_object(v___x_2840_);
lean_dec_ref(v_val_2838_);
lean_del_object(v___x_2836_);
lean_dec(v_us_2829_);
lean_dec(v_idx_2810_);
lean_dec(v_name_2809_);
lean_dec(v_goal_2808_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
else
{
lean_del_object(v___x_2875_);
lean_dec(v_val_2873_);
v___y_2843_ = v___y_2812_;
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
goto v___jp_2842_;
}
}
}
else
{
lean_dec(v_expected_x3f_2811_);
v___y_2843_ = v___y_2812_;
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
goto v___jp_2842_;
}
v___jp_2842_:
{
lean_object* v_ctors_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_ctors_2847_ = lean_ctor_get(v_val_2838_, 4);
lean_inc(v_ctors_2847_);
lean_dec_ref(v_val_2838_);
v___x_2848_ = l_List_lengthTR___redArg(v_ctors_2847_);
v___x_2849_ = lean_nat_dec_lt(v_idx_2810_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_dec(v_ctors_2847_);
lean_dec(v_us_2829_);
v___x_2850_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2851_ = l_Nat_reprFast(v_idx_2810_);
v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2854_ = lean_string_append(v___x_2852_, v___x_2853_);
v___x_2855_ = l_Nat_reprFast(v___x_2848_);
v___x_2856_ = lean_string_append(v___x_2854_, v___x_2855_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2858_ = lean_string_append(v___x_2856_, v___x_2857_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 3);
lean_ctor_set(v___x_2840_, 0, v___x_2858_);
v___x_2860_ = v___x_2840_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = l_Lean_MessageData_ofFormat(v___x_2860_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2861_);
v___x_2863_ = v___x_2836_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2809_, v_goal_2808_, v___x_2863_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2864_;
}
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec(v___x_2848_);
lean_del_object(v___x_2840_);
lean_del_object(v___x_2836_);
lean_dec(v_name_2809_);
v___x_2867_ = l_List_get___redArg(v_ctors_2847_, v_idx_2810_);
lean_dec(v_ctors_2847_);
v___x_2868_ = l_Lean_mkConst(v___x_2867_, v_us_2829_);
v___x_2869_ = 0;
v___x_2870_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2870_, 0, v___x_2869_);
lean_ctor_set_uint8(v___x_2870_, 1, v___x_2849_);
lean_ctor_set_uint8(v___x_2870_, 2, v___x_2832_);
lean_ctor_set_uint8(v___x_2870_, 3, v___x_2849_);
v___x_2871_ = lean_box(0);
v___x_2872_ = l_Lean_MVarId_apply(v_goal_2808_, v___x_2868_, v___x_2870_, v___x_2871_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2872_;
}
}
}
}
else
{
lean_del_object(v___x_2836_);
lean_dec(v_val_2834_);
lean_dec(v_us_2829_);
lean_dec(v_expected_x3f_2811_);
lean_dec(v_idx_2810_);
v___y_2818_ = v___y_2812_;
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
goto v___jp_2817_;
}
}
}
}
else
{
lean_dec_ref(v___x_2827_);
lean_dec(v_expected_x3f_2811_);
lean_dec(v_idx_2810_);
v___y_2818_ = v___y_2812_;
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
goto v___jp_2817_;
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_expected_x3f_2811_);
lean_dec(v_idx_2810_);
lean_dec(v_name_2809_);
lean_dec(v_goal_2808_);
v_a_2905_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2825_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2825_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_expected_x3f_2811_);
lean_dec(v_idx_2810_);
lean_dec(v_name_2809_);
lean_dec(v_goal_2808_);
v_a_2913_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2824_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2824_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
v___jp_2817_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2823_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2809_, v_goal_2808_, v___x_2822_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2921_, lean_object* v_name_2922_, lean_object* v_idx_2923_, lean_object* v_expected_x3f_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2921_, v_name_2922_, v_idx_2923_, v_expected_x3f_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2931_, lean_object* v_idx_2932_, lean_object* v_expected_x3f_2933_, lean_object* v_goal_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___f_2940_; lean_object* v___x_2941_; 
lean_inc(v_goal_2934_);
v___f_2940_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2940_, 0, v_goal_2934_);
lean_closure_set(v___f_2940_, 1, v_name_2931_);
lean_closure_set(v___f_2940_, 2, v_idx_2932_);
lean_closure_set(v___f_2940_, 3, v_expected_x3f_2933_);
v___x_2941_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2934_, v___f_2940_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2942_, lean_object* v_idx_2943_, lean_object* v_expected_x3f_2944_, lean_object* v_goal_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_MVarId_nthConstructor(v_name_2942_, v_idx_2943_, v_expected_x3f_2944_, v_goal_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Meta_saveState___redArg(v___y_2954_, v___y_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
v___x_2960_ = lean_apply_5(v_x_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, lean_box(0));
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_a_2959_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_a_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2999_; 
v_a_2970_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2972_ = v___x_2960_;
v_isShared_2973_ = v_isSharedCheck_2999_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2960_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2999_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
uint8_t v___y_2975_; uint8_t v___x_2997_; 
v___x_2997_ = l_Lean_Exception_isInterrupt(v_a_2970_);
if (v___x_2997_ == 0)
{
uint8_t v___x_2998_; 
lean_inc(v_a_2970_);
v___x_2998_ = l_Lean_Exception_isRuntime(v_a_2970_);
v___y_2975_ = v___x_2998_;
goto v___jp_2974_;
}
else
{
v___y_2975_ = v___x_2997_;
goto v___jp_2974_;
}
v___jp_2974_:
{
if (v___y_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_del_object(v___x_2972_);
lean_dec(v_a_2970_);
v___x_2976_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2959_, v___y_2954_, v___y_2956_);
lean_dec(v_a_2959_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2984_; 
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v___x_2976_, 0);
lean_dec(v_unused_2985_);
v___x_2978_ = v___x_2976_;
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v___x_2976_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_box(0);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2980_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v_a_2986_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2976_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2976_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v___x_2995_; 
lean_dec(v_a_2959_);
if (v_isShared_2973_ == 0)
{
v___x_2995_ = v___x_2972_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2970_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_x_2952_);
v_a_3000_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2958_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2958_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3023_, lean_object* v_x_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3023_, v_x_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3030_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3034_, lean_object* v___x_3035_, lean_object* v___x_3036_, lean_object* v___x_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_MVarId_apply(v_mvarId_3034_, v___x_3035_, v___x_3036_, v___x_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3060_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3060_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3060_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; 
if (lean_obj_tag(v_a_3044_) == 1)
{
lean_object* v_tail_3055_; 
v_tail_3055_ = lean_ctor_get(v_a_3044_, 1);
if (lean_obj_tag(v_tail_3055_) == 0)
{
lean_object* v_head_3056_; lean_object* v___x_3058_; 
v_head_3056_ = lean_ctor_get(v_a_3044_, 0);
lean_inc(v_head_3056_);
lean_dec_ref_known(v_a_3044_, 2);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_head_3056_);
v___x_3058_ = v___x_3046_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_head_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_dec_ref_known(v_a_3044_, 2);
lean_del_object(v___x_3046_);
v___y_3049_ = v___y_3038_;
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
goto v___jp_3048_;
}
}
else
{
lean_del_object(v___x_3046_);
lean_dec(v_a_3044_);
v___y_3049_ = v___y_3038_;
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
goto v___jp_3048_;
}
v___jp_3048_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3054_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3053_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3043_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3043_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3069_, lean_object* v___x_3070_, lean_object* v___x_3071_, lean_object* v___x_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3069_, v___x_3070_, v___x_3071_, v___x_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
return v_res_3078_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3084_ = l_Lean_mkConst(v___x_3083_, v___x_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; 
v___x_3095_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3096_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3097_ = lean_box(0);
lean_inc(v_mvarId_3089_);
v___f_3098_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3098_, 0, v_mvarId_3089_);
lean_closure_set(v___f_3098_, 1, v___x_3095_);
lean_closure_set(v___f_3098_, 2, v___x_3096_);
lean_closure_set(v___f_3098_, 3, v___x_3097_);
v___x_3099_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3098_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3111_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3111_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3111_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
if (lean_obj_tag(v_a_3100_) == 0)
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_mvarId_3089_);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_mvarId_3089_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3109_; 
lean_dec(v_mvarId_3089_);
v_val_3107_ = lean_ctor_get(v_a_3100_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v_a_3100_, 1);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_val_3107_);
v___x_3109_ = v___x_3102_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_val_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_mvarId_3089_);
v_a_3112_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3099_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3099_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_MVarId_iffOfEq(v_mvarId_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
return v_res_3126_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_box(0);
v___x_3134_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3135_ = l_Lean_mkConst(v___x_3134_, v___x_3133_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3136_, lean_object* v_mvarId_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v_keyedConfig_3150_; uint8_t v_trackZetaDelta_3151_; lean_object* v_zetaDeltaSet_3152_; lean_object* v_lctx_3153_; lean_object* v_localInstances_3154_; lean_object* v_defEqCtx_x3f_3155_; lean_object* v_synthPendingDepth_3156_; lean_object* v_customCanUnfoldPredicate_x3f_3157_; uint8_t v_univApprox_3158_; uint8_t v_inTypeClassResolution_3159_; uint8_t v_cacheInferType_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_keyedConfig_3150_ = lean_ctor_get(v___y_3138_, 0);
v_trackZetaDelta_3151_ = lean_ctor_get_uint8(v___y_3138_, sizeof(void*)*7);
v_zetaDeltaSet_3152_ = lean_ctor_get(v___y_3138_, 1);
v_lctx_3153_ = lean_ctor_get(v___y_3138_, 2);
v_localInstances_3154_ = lean_ctor_get(v___y_3138_, 3);
v_defEqCtx_x3f_3155_ = lean_ctor_get(v___y_3138_, 4);
v_synthPendingDepth_3156_ = lean_ctor_get(v___y_3138_, 5);
v_customCanUnfoldPredicate_x3f_3157_ = lean_ctor_get(v___y_3138_, 6);
v_univApprox_3158_ = lean_ctor_get_uint8(v___y_3138_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3159_ = lean_ctor_get_uint8(v___y_3138_, sizeof(void*)*7 + 2);
v_cacheInferType_3160_ = lean_ctor_get_uint8(v___y_3138_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3150_);
v___x_3161_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3136_, v_keyedConfig_3150_);
lean_inc(v_customCanUnfoldPredicate_x3f_3157_);
lean_inc(v_synthPendingDepth_3156_);
lean_inc(v_defEqCtx_x3f_3155_);
lean_inc_ref(v_localInstances_3154_);
lean_inc_ref(v_lctx_3153_);
lean_inc(v_zetaDeltaSet_3152_);
v___x_3162_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v_zetaDeltaSet_3152_);
lean_ctor_set(v___x_3162_, 2, v_lctx_3153_);
lean_ctor_set(v___x_3162_, 3, v_localInstances_3154_);
lean_ctor_set(v___x_3162_, 4, v_defEqCtx_x3f_3155_);
lean_ctor_set(v___x_3162_, 5, v_synthPendingDepth_3156_);
lean_ctor_set(v___x_3162_, 6, v_customCanUnfoldPredicate_x3f_3157_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*7, v_trackZetaDelta_3151_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*7 + 1, v_univApprox_3158_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3159_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*7 + 3, v_cacheInferType_3160_);
lean_inc(v_mvarId_3137_);
v___x_3163_ = l_Lean_MVarId_getType_x27(v_mvarId_3137_, v___x_3162_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec_ref_known(v___x_3162_, 7);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3166_ = lean_unsigned_to_nat(3u);
v___x_3167_ = l_Lean_Expr_isAppOfArity(v_a_3164_, v___x_3165_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_dec(v_a_3164_);
lean_dec(v_mvarId_3137_);
v___x_3193_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3194_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3193_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec_ref(v___y_3138_);
return v___x_3194_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = l_Lean_Expr_appFn_x21(v_a_3164_);
lean_dec(v_a_3164_);
v___x_3196_ = l_Lean_Expr_appArg_x21(v___x_3195_);
lean_dec_ref(v___x_3195_);
v___x_3197_ = l_Lean_Meta_isProp(v___x_3196_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; uint8_t v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = lean_unbox(v_a_3198_);
lean_dec(v_a_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_mvarId_3137_);
v___x_3200_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3201_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3200_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec_ref(v___y_3138_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
else
{
goto v___jp_3168_;
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v___y_3138_);
lean_dec(v_mvarId_3137_);
v_a_3210_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3197_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3197_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3169_; uint8_t v___x_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3169_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3170_ = 0;
v___x_3171_ = 0;
v___x_3172_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3172_, 0, v___x_3170_);
lean_ctor_set_uint8(v___x_3172_, 1, v___x_3167_);
lean_ctor_set_uint8(v___x_3172_, 2, v___x_3171_);
lean_ctor_set_uint8(v___x_3172_, 3, v___x_3167_);
v___x_3173_ = lean_box(0);
v___x_3174_ = l_Lean_MVarId_apply(v_mvarId_3137_, v___x_3169_, v___x_3172_, v___x_3173_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3184_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
if (lean_obj_tag(v_a_3175_) == 1)
{
lean_object* v_tail_3179_; 
v_tail_3179_ = lean_ctor_get(v_a_3175_, 1);
if (lean_obj_tag(v_tail_3179_) == 0)
{
lean_object* v_head_3180_; lean_object* v___x_3182_; 
lean_dec_ref(v___y_3138_);
v_head_3180_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_head_3180_);
lean_dec_ref_known(v_a_3175_, 2);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v_head_3180_);
v___x_3182_ = v___x_3177_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_head_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
else
{
lean_dec_ref_known(v_a_3175_, 2);
lean_del_object(v___x_3177_);
v___y_3144_ = v___y_3138_;
v___y_3145_ = v___y_3139_;
v___y_3146_ = v___y_3140_;
v___y_3147_ = v___y_3141_;
goto v___jp_3143_;
}
}
else
{
lean_del_object(v___x_3177_);
lean_dec(v_a_3175_);
v___y_3144_ = v___y_3138_;
v___y_3145_ = v___y_3139_;
v___y_3146_ = v___y_3140_;
v___y_3147_ = v___y_3141_;
goto v___jp_3143_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v___y_3138_);
v_a_3185_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3174_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3174_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v___y_3138_);
lean_dec(v_mvarId_3137_);
v_a_3218_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3163_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3163_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
v___jp_3143_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3149_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3148_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec_ref(v___y_3144_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3226_, lean_object* v_mvarId_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_2337__boxed_3233_; lean_object* v_res_3234_; 
v___x_2337__boxed_3233_ = lean_unbox(v___x_3226_);
v_res_3234_ = l_Lean_MVarId_propext___lam__0(v___x_2337__boxed_3233_, v_mvarId_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
uint8_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; 
v___x_3241_ = 2;
v___x_3242_ = lean_box(v___x_3241_);
lean_inc(v_mvarId_3235_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3243_, 0, v___x_3242_);
lean_closure_set(v___f_3243_, 1, v_mvarId_3235_);
v___x_3244_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3243_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3256_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3256_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3256_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
if (lean_obj_tag(v_a_3245_) == 0)
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v_mvarId_3235_);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_mvarId_3235_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
else
{
lean_object* v_val_3252_; lean_object* v___x_3254_; 
lean_dec(v_mvarId_3235_);
v_val_3252_ = lean_ctor_get(v_a_3245_, 0);
lean_inc(v_val_3252_);
lean_dec_ref_known(v_a_3245_, 1);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v_val_3252_);
v___x_3254_ = v___x_3247_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_val_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v_mvarId_3235_);
v_a_3257_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3244_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3244_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_MVarId_propext(v_mvarId_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3278_, lean_object* v___x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
lean_inc(v_mvarId_3278_);
v___x_3285_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3278_, v___x_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_keyedConfig_3286_; uint8_t v_trackZetaDelta_3287_; lean_object* v_zetaDeltaSet_3288_; lean_object* v_lctx_3289_; lean_object* v_localInstances_3290_; lean_object* v_defEqCtx_x3f_3291_; lean_object* v_synthPendingDepth_3292_; lean_object* v_customCanUnfoldPredicate_x3f_3293_; uint8_t v_univApprox_3294_; uint8_t v_inTypeClassResolution_3295_; uint8_t v_cacheInferType_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec_ref_known(v___x_3285_, 1);
v_keyedConfig_3286_ = lean_ctor_get(v___y_3280_, 0);
v_trackZetaDelta_3287_ = lean_ctor_get_uint8(v___y_3280_, sizeof(void*)*7);
v_zetaDeltaSet_3288_ = lean_ctor_get(v___y_3280_, 1);
v_lctx_3289_ = lean_ctor_get(v___y_3280_, 2);
v_localInstances_3290_ = lean_ctor_get(v___y_3280_, 3);
v_defEqCtx_x3f_3291_ = lean_ctor_get(v___y_3280_, 4);
v_synthPendingDepth_3292_ = lean_ctor_get(v___y_3280_, 5);
v_customCanUnfoldPredicate_x3f_3293_ = lean_ctor_get(v___y_3280_, 6);
v_univApprox_3294_ = lean_ctor_get_uint8(v___y_3280_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3295_ = lean_ctor_get_uint8(v___y_3280_, sizeof(void*)*7 + 2);
v_cacheInferType_3296_ = lean_ctor_get_uint8(v___y_3280_, sizeof(void*)*7 + 3);
v___x_3297_ = 2;
lean_inc_ref(v_keyedConfig_3286_);
v___x_3298_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3297_, v_keyedConfig_3286_);
lean_inc(v_customCanUnfoldPredicate_x3f_3293_);
lean_inc(v_synthPendingDepth_3292_);
lean_inc(v_defEqCtx_x3f_3291_);
lean_inc_ref(v_localInstances_3290_);
lean_inc_ref(v_lctx_3289_);
lean_inc(v_zetaDeltaSet_3288_);
v___x_3299_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v_zetaDeltaSet_3288_);
lean_ctor_set(v___x_3299_, 2, v_lctx_3289_);
lean_ctor_set(v___x_3299_, 3, v_localInstances_3290_);
lean_ctor_set(v___x_3299_, 4, v_defEqCtx_x3f_3291_);
lean_ctor_set(v___x_3299_, 5, v_synthPendingDepth_3292_);
lean_ctor_set(v___x_3299_, 6, v_customCanUnfoldPredicate_x3f_3293_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7, v_trackZetaDelta_3287_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 1, v_univApprox_3294_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3295_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 3, v_cacheInferType_3296_);
lean_inc(v_mvarId_3278_);
v___x_3300_ = l_Lean_MVarId_getType_x27(v_mvarId_3278_, v___x_3299_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec_ref_known(v___x_3299_, 7);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v___x_3302_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3303_ = lean_unsigned_to_nat(4u);
v___x_3304_ = l_Lean_Expr_isAppOfArity(v_a_3301_, v___x_3302_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_a_3301_);
lean_dec(v_mvarId_3278_);
v___x_3305_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3306_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3305_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec_ref(v___y_3280_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3307_ = l_Lean_Expr_appFn_x21(v_a_3301_);
v___x_3308_ = l_Lean_Expr_appFn_x21(v___x_3307_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = l_Lean_Expr_appArg_x21(v___x_3308_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = l_Lean_Expr_appArg_x21(v_a_3301_);
lean_dec(v_a_3301_);
v___x_3311_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3312_ = lean_unsigned_to_nat(2u);
v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_3312_);
v___x_3314_ = lean_array_push(v___x_3313_, v___x_3309_);
v___x_3315_ = lean_array_push(v___x_3314_, v___x_3310_);
v___x_3316_ = l_Lean_Meta_mkAppM(v___x_3311_, v___x_3315_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec_ref(v___y_3280_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3278_, v_a_3317_, v___y_3281_);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v___x_3318_, 0);
lean_dec(v_unused_3327_);
v___x_3320_ = v___x_3318_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_dec(v___x_3318_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3322_ = lean_box(v___x_3304_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v___x_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_mvarId_3278_);
v_a_3328_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3316_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3316_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___y_3280_);
lean_dec(v_mvarId_3278_);
v_a_3336_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3300_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3300_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v___y_3280_);
lean_dec(v_mvarId_3278_);
v_a_3344_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3285_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3285_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3352_, lean_object* v___x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3352_, v___x_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3380_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3380_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3380_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
if (lean_obj_tag(v_a_3367_) == 0)
{
uint8_t v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3371_ = 0;
v___x_3372_ = lean_box(v___x_3371_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3372_);
v___x_3374_ = v___x_3369_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3378_; 
v_val_3376_ = lean_ctor_get(v_a_3367_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_a_3367_, 1);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_val_3376_);
v___x_3378_ = v___x_3369_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_val_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_a_3381_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3366_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3366_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___f_3407_; lean_object* v___x_3408_; 
v___x_3405_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3399_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3406_, 0, v_mvarId_3399_);
lean_closure_set(v___f_3406_, 1, v___x_3405_);
v___f_3407_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3407_, 0, v___f_3406_);
v___x_3408_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3399_, v___f_3407_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3420_, lean_object* v___x_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
lean_inc(v_mvarId_3420_);
v___x_3427_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3420_, v___x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_keyedConfig_3428_; uint8_t v_trackZetaDelta_3429_; lean_object* v_zetaDeltaSet_3430_; lean_object* v_lctx_3431_; lean_object* v_localInstances_3432_; lean_object* v_defEqCtx_x3f_3433_; lean_object* v_synthPendingDepth_3434_; lean_object* v_customCanUnfoldPredicate_x3f_3435_; uint8_t v_univApprox_3436_; uint8_t v_inTypeClassResolution_3437_; uint8_t v_cacheInferType_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_dec_ref_known(v___x_3427_, 1);
v_keyedConfig_3428_ = lean_ctor_get(v___y_3422_, 0);
v_trackZetaDelta_3429_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*7);
v_zetaDeltaSet_3430_ = lean_ctor_get(v___y_3422_, 1);
v_lctx_3431_ = lean_ctor_get(v___y_3422_, 2);
v_localInstances_3432_ = lean_ctor_get(v___y_3422_, 3);
v_defEqCtx_x3f_3433_ = lean_ctor_get(v___y_3422_, 4);
v_synthPendingDepth_3434_ = lean_ctor_get(v___y_3422_, 5);
v_customCanUnfoldPredicate_x3f_3435_ = lean_ctor_get(v___y_3422_, 6);
v_univApprox_3436_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3437_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*7 + 2);
v_cacheInferType_3438_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*7 + 3);
v___x_3439_ = 2;
lean_inc_ref(v_keyedConfig_3428_);
v___x_3440_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3439_, v_keyedConfig_3428_);
lean_inc(v_customCanUnfoldPredicate_x3f_3435_);
lean_inc(v_synthPendingDepth_3434_);
lean_inc(v_defEqCtx_x3f_3433_);
lean_inc_ref(v_localInstances_3432_);
lean_inc_ref(v_lctx_3431_);
lean_inc(v_zetaDeltaSet_3430_);
v___x_3441_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v_zetaDeltaSet_3430_);
lean_ctor_set(v___x_3441_, 2, v_lctx_3431_);
lean_ctor_set(v___x_3441_, 3, v_localInstances_3432_);
lean_ctor_set(v___x_3441_, 4, v_defEqCtx_x3f_3433_);
lean_ctor_set(v___x_3441_, 5, v_synthPendingDepth_3434_);
lean_ctor_set(v___x_3441_, 6, v_customCanUnfoldPredicate_x3f_3435_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7, v_trackZetaDelta_3429_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 1, v_univApprox_3436_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3437_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 3, v_cacheInferType_3438_);
lean_inc(v_mvarId_3420_);
v___x_3442_ = l_Lean_MVarId_getType_x27(v_mvarId_3420_, v___x_3441_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec_ref_known(v___x_3441_, 7);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v___x_3444_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3445_ = lean_unsigned_to_nat(3u);
v___x_3446_ = l_Lean_Expr_isAppOfArity(v_a_3443_, v___x_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v_a_3443_);
lean_dec(v_mvarId_3420_);
v___x_3447_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3448_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3447_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec_ref(v___y_3422_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3449_ = l_Lean_Expr_appFn_x21(v_a_3443_);
v___x_3450_ = l_Lean_Expr_appArg_x21(v___x_3449_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = l_Lean_Expr_appArg_x21(v_a_3443_);
lean_dec(v_a_3443_);
v___x_3452_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3453_ = lean_unsigned_to_nat(2u);
v___x_3454_ = lean_mk_empty_array_with_capacity(v___x_3453_);
v___x_3455_ = lean_array_push(v___x_3454_, v___x_3450_);
v___x_3456_ = lean_array_push(v___x_3455_, v___x_3451_);
v___x_3457_ = l_Lean_Meta_mkAppM(v___x_3452_, v___x_3456_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec_ref(v___y_3422_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3467_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3420_, v_a_3458_, v___y_3423_);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3468_);
v___x_3461_ = v___x_3459_;
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
else
{
lean_dec(v___x_3459_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(v___x_3446_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_mvarId_3420_);
v_a_3469_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3457_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3457_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v___y_3422_);
lean_dec(v_mvarId_3420_);
v_a_3477_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3442_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3442_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___y_3422_);
lean_dec(v_mvarId_3420_);
v_a_3485_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3427_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3427_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3493_, lean_object* v___x_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3493_, v___x_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; 
v___x_3510_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3504_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3511_, 0, v_mvarId_3504_);
lean_closure_set(v___f_3511_, 1, v___x_3510_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3512_, 0, v___f_3511_);
v___x_3513_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3504_, v___f_3512_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3520_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Apply(builtin);
}
#ifdef __cplusplus
}
#endif
