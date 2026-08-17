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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_ctor_set(v___x_199_, 0, v___y_202_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___y_202_);
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
lean_ctor_set(v___x_214_, 1, v___y_203_);
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
v___y_202_ = v___x_227_;
v___y_203_ = v_a_222_;
v___y_204_ = v___x_228_;
goto v___jp_201_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v_term_x3f_184_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_term_x3f_184_, 1);
v___y_202_ = v___x_227_;
v___y_203_ = v_a_222_;
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
v___x_1496_ = lean_st_ref_put(v___y_1477_, v___x_1495_);
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
size_t v_x_7238__boxed_1768_; size_t v_x_7239__boxed_1769_; lean_object* v_res_1770_; 
v_x_7238__boxed_1768_ = lean_unbox_usize(v_x_1764_);
lean_dec(v_x_1764_);
v_x_7239__boxed_1769_ = lean_unbox_usize(v_x_1765_);
lean_dec(v_x_1765_);
v_res_1770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1763_, v_x_7238__boxed_1768_, v_x_7239__boxed_1769_, v_x_1766_, v_x_1767_);
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
lean_object* v___x_1782_; lean_object* v_mctx_1783_; lean_object* v_cache_1784_; lean_object* v_zetaDeltaFVarIds_1785_; lean_object* v_postponed_1786_; lean_object* v_diag_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1816_; 
v___x_1782_ = lean_st_ref_take(v___y_1780_);
v_mctx_1783_ = lean_ctor_get(v___x_1782_, 0);
v_cache_1784_ = lean_ctor_get(v___x_1782_, 1);
v_zetaDeltaFVarIds_1785_ = lean_ctor_get(v___x_1782_, 2);
v_postponed_1786_ = lean_ctor_get(v___x_1782_, 3);
v_diag_1787_ = lean_ctor_get(v___x_1782_, 4);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1789_ = v___x_1782_;
v_isShared_1790_ = v_isSharedCheck_1816_;
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
v_isShared_1790_ = v_isSharedCheck_1816_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_depth_1791_; lean_object* v_levelAssignDepth_1792_; lean_object* v_lmvarCounter_1793_; lean_object* v_mvarCounter_1794_; lean_object* v_lDecls_1795_; lean_object* v_decls_1796_; lean_object* v_userNames_1797_; lean_object* v_lAssignment_1798_; lean_object* v_eAssignment_1799_; lean_object* v_dAssignment_1800_; lean_object* v_instanceTypedMVars_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1815_; 
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
v_instanceTypedMVars_1801_ = lean_ctor_get(v_mctx_1783_, 10);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_mctx_1783_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1803_ = v_mctx_1783_;
v_isShared_1804_ = v_isSharedCheck_1815_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_instanceTypedMVars_1801_);
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
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1815_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1799_, v_mvarId_1778_, v_val_1779_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 8, v___x_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_depth_1791_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_levelAssignDepth_1792_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_lmvarCounter_1793_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_mvarCounter_1794_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_lDecls_1795_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v_decls_1796_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_userNames_1797_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_lAssignment_1798_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1814_, 9, v_dAssignment_1800_);
lean_ctor_set(v_reuseFailAlloc_1814_, 10, v_instanceTypedMVars_1801_);
v___x_1807_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1807_);
v___x_1809_ = v___x_1789_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_cache_1784_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_zetaDeltaFVarIds_1785_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_postponed_1786_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_diag_1787_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_st_ref_put(v___y_1780_, v___x_1809_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1817_, lean_object* v_val_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1817_, v_val_1818_, v___y_1819_);
lean_dec(v___y_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1822_, lean_object* v_x_1823_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
uint8_t v___x_1824_; 
v___x_1824_ = 0;
return v___x_1824_;
}
else
{
lean_object* v_head_1825_; lean_object* v_tail_1826_; uint8_t v___x_1827_; 
v_head_1825_ = lean_ctor_get(v_x_1823_, 0);
v_tail_1826_ = lean_ctor_get(v_x_1823_, 1);
v___x_1827_ = l_Lean_instBEqMVarId_beq(v_a_1822_, v_head_1825_);
if (v___x_1827_ == 0)
{
v_x_1823_ = v_tail_1826_;
goto _start;
}
else
{
return v___x_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1829_, lean_object* v_x_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1829_, v_x_1830_);
lean_dec(v_x_1830_);
lean_dec(v_a_1829_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1833_, lean_object* v_as_1834_, size_t v_i_1835_, size_t v_stop_1836_, lean_object* v_b_1837_){
_start:
{
lean_object* v___y_1839_; uint8_t v___x_1843_; 
v___x_1843_ = lean_usize_dec_eq(v_i_1835_, v_stop_1836_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_array_uget_borrowed(v_as_1834_, v_i_1835_);
v___x_1845_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1844_, v_a_1833_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_inc(v___x_1844_);
v___x_1846_ = lean_array_push(v_b_1837_, v___x_1844_);
v___y_1839_ = v___x_1846_;
goto v___jp_1838_;
}
else
{
v___y_1839_ = v_b_1837_;
goto v___jp_1838_;
}
}
else
{
return v_b_1837_;
}
v___jp_1838_:
{
size_t v___x_1840_; size_t v___x_1841_; 
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1835_, v___x_1840_);
v_i_1835_ = v___x_1841_;
v_b_1837_ = v___y_1839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1847_, lean_object* v_as_1848_, lean_object* v_i_1849_, lean_object* v_stop_1850_, lean_object* v_b_1851_){
_start:
{
size_t v_i_boxed_1852_; size_t v_stop_boxed_1853_; lean_object* v_res_1854_; 
v_i_boxed_1852_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_stop_boxed_1853_ = lean_unbox_usize(v_stop_1850_);
lean_dec(v_stop_1850_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1847_, v_as_1848_, v_i_boxed_1852_, v_stop_boxed_1853_, v_b_1851_);
lean_dec_ref(v_as_1848_);
lean_dec(v_a_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1855_, lean_object* v___x_1856_, lean_object* v_e_1857_, lean_object* v_cfg_1858_, lean_object* v_term_x3f_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; uint8_t v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v_a_1900_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___x_1951_; 
lean_inc(v___x_1856_);
lean_inc(v_mvarId_1855_);
v___x_1951_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1855_, v___x_1856_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref_known(v___x_1951_, 1);
lean_inc(v_mvarId_1855_);
v___x_1952_ = l_Lean_MVarId_getType(v_mvarId_1855_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
lean_inc_ref(v_e_1857_);
v___x_1954_ = lean_infer_type(v_e_1857_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v_rangeNumArgs_1957_; lean_object* v_lower_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___x_2002_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc_n(v_a_1955_, 2);
lean_dec_ref_known(v___x_1954_, 1);
v___x_2002_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1955_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_snd_2004_; uint8_t v___x_2005_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v_snd_2004_ = lean_ctor_get(v_a_2003_, 1);
v___x_2005_ = lean_unbox(v_snd_2004_);
if (v___x_2005_ == 0)
{
lean_object* v_fst_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2026_; 
v_fst_2006_ = lean_ctor_get(v_a_2003_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v_a_2003_, 1);
lean_dec(v_unused_2027_);
v___x_2008_ = v_a_2003_;
v_isShared_2009_ = v_isSharedCheck_2026_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_fst_2006_);
lean_dec(v_a_2003_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2026_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; 
lean_inc(v_a_1953_);
v___x_2010_ = l_Lean_Meta_getExpectedNumArgs(v_a_1953_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = lean_nat_sub(v_fst_2006_, v_a_2011_);
lean_dec(v_a_2011_);
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = lean_nat_add(v_fst_2006_, v___x_2013_);
lean_dec(v_fst_2006_);
lean_inc(v___x_2012_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2014_);
lean_ctor_set(v___x_2008_, 0, v___x_2012_);
v___x_2016_ = v___x_2008_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v_rangeNumArgs_1957_ = v___x_2016_;
v_lower_1958_ = v___x_2012_;
v___y_1959_ = v___y_1860_;
v___y_1960_ = v___y_1861_;
v___y_1961_ = v___y_1862_;
v___y_1962_ = v___y_1863_;
goto v___jp_1956_;
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_2008_);
lean_dec(v_fst_2006_);
lean_dec(v_a_1955_);
lean_dec(v_a_1953_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_term_x3f_1859_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_2018_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2010_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2010_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_fst_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2037_; 
v_fst_2028_ = lean_ctor_get(v_a_2003_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_a_2003_, 1);
lean_dec(v_unused_2038_);
v___x_2030_ = v_a_2003_;
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_fst_2028_);
lean_dec(v_a_2003_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_fst_2028_, v___x_2032_);
lean_inc(v_fst_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_fst_2028_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
v_rangeNumArgs_1957_ = v___x_2035_;
v_lower_1958_ = v_fst_2028_;
v___y_1959_ = v___y_1860_;
v___y_1960_ = v___y_1861_;
v___y_1961_ = v___y_1862_;
v___y_1962_ = v___y_1863_;
goto v___jp_1956_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1953_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_term_x3f_1859_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_2039_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2002_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2002_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
v___jp_1956_:
{
lean_object* v___x_1963_; 
lean_inc(v_mvarId_1855_);
v___x_1963_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1855_, v_cfg_1858_, v_term_x3f_1859_, v_a_1953_, v_a_1955_, v_rangeNumArgs_1957_, v_lower_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec_ref(v_rangeNumArgs_1957_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v_fst_1965_; lean_object* v_snd_1966_; uint8_t v_newGoals_1967_; uint8_t v_synthAssignedInstances_1968_; uint8_t v_allowSynthFailures_1969_; lean_object* v___x_1970_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v_fst_1965_ = lean_ctor_get(v_a_1964_, 0);
lean_inc(v_fst_1965_);
v_snd_1966_ = lean_ctor_get(v_a_1964_, 1);
lean_inc_n(v_snd_1966_, 2);
lean_dec(v_a_1964_);
v_newGoals_1967_ = lean_ctor_get_uint8(v_cfg_1858_, 0);
v_synthAssignedInstances_1968_ = lean_ctor_get_uint8(v_cfg_1858_, 1);
v_allowSynthFailures_1969_ = lean_ctor_get_uint8(v_cfg_1858_, 2);
lean_inc(v_mvarId_1855_);
v___x_1970_ = l_Lean_Meta_synthAppInstances(v___x_1856_, v_mvarId_1855_, v_fst_1965_, v_snd_1966_, v_synthAssignedInstances_1968_, v_allowSynthFailures_1969_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
lean_dec_ref_known(v___x_1970_, 1);
v___x_1971_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1857_, v___y_1960_);
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc_n(v_a_1972_, 2);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l_Lean_mkAppN(v_a_1972_, v_fst_1965_);
lean_inc(v_mvarId_1855_);
v___x_1974_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1855_, v___x_1973_, v___y_1960_);
lean_dec_ref(v___x_1974_);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_array_get_size(v_fst_1965_);
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1978_ = lean_nat_dec_lt(v___x_1975_, v___x_1976_);
if (v___x_1978_ == 0)
{
lean_dec(v_fst_1965_);
v___y_1892_ = v_newGoals_1967_;
v___y_1893_ = v___y_1962_;
v___y_1894_ = v___y_1961_;
v___y_1895_ = v_snd_1966_;
v___y_1896_ = v___y_1960_;
v___y_1897_ = v_a_1972_;
v___y_1898_ = v___y_1959_;
v___y_1899_ = v___x_1975_;
v_a_1900_ = v___x_1977_;
goto v___jp_1891_;
}
else
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_le(v___x_1976_, v___x_1976_);
if (v___x_1979_ == 0)
{
if (v___x_1978_ == 0)
{
lean_dec(v_fst_1965_);
v___y_1892_ = v_newGoals_1967_;
v___y_1893_ = v___y_1962_;
v___y_1894_ = v___y_1961_;
v___y_1895_ = v_snd_1966_;
v___y_1896_ = v___y_1960_;
v___y_1897_ = v_a_1972_;
v___y_1898_ = v___y_1959_;
v___y_1899_ = v___x_1975_;
v_a_1900_ = v___x_1977_;
goto v___jp_1891_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_of_nat(v___x_1976_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1965_, v___x_1980_, v___x_1981_, v___x_1977_, v___y_1960_);
lean_dec(v_fst_1965_);
v___y_1933_ = v_newGoals_1967_;
v___y_1934_ = v___y_1962_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v_snd_1966_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v_a_1972_;
v___y_1940_ = v___x_1975_;
v___y_1941_ = v___x_1982_;
goto v___jp_1932_;
}
}
else
{
size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_of_nat(v___x_1976_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1965_, v___x_1983_, v___x_1984_, v___x_1977_, v___y_1960_);
lean_dec(v_fst_1965_);
v___y_1933_ = v_newGoals_1967_;
v___y_1934_ = v___y_1962_;
v___y_1935_ = v___y_1961_;
v___y_1936_ = v_snd_1966_;
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v_a_1972_;
v___y_1940_ = v___x_1975_;
v___y_1941_ = v___x_1985_;
goto v___jp_1932_;
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v_e_1857_);
lean_dec(v_mvarId_1855_);
v_a_1986_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1970_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1970_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_1994_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1963_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1963_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_1953_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_term_x3f_1859_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_2047_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_1954_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_1954_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_term_x3f_1859_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_2055_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_1952_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_1952_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_term_x3f_1859_);
lean_dec_ref(v_e_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
v_a_2063_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_1951_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_1951_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
v___jp_1865_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_array_to_list(v___y_1871_);
v___x_1873_ = l_List_appendTR___redArg(v___y_1870_, v___x_1872_);
lean_inc(v___x_1873_);
v___x_1874_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1873_, v___y_1869_, v___y_1868_, v___y_1867_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1869_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1874_, 0);
lean_dec(v_unused_1882_);
v___x_1876_ = v___x_1874_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v___x_1874_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1873_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v___x_1873_);
v_a_1883_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1874_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1874_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_appendParentTag(v_mvarId_1855_, v_a_1900_, v___y_1895_, v___y_1898_, v___y_1896_, v___y_1894_, v___y_1893_);
lean_dec_ref(v___y_1895_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref_known(v___x_1901_, 1);
v___x_1902_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1897_, v___y_1898_, v___y_1896_, v___y_1894_, v___y_1893_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1900_, v___y_1892_, v___y_1898_, v___y_1896_, v___y_1894_, v___y_1893_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = lean_array_get_size(v_a_1903_);
v___x_1907_ = lean_mk_empty_array_with_capacity(v___y_1899_);
v___x_1908_ = lean_nat_dec_lt(v___y_1899_, v___x_1906_);
if (v___x_1908_ == 0)
{
lean_dec(v_a_1903_);
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v___y_1896_;
v___y_1869_ = v___y_1898_;
v___y_1870_ = v_a_1905_;
v___y_1871_ = v___x_1907_;
goto v___jp_1865_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_le(v___x_1906_, v___x_1906_);
if (v___x_1909_ == 0)
{
if (v___x_1908_ == 0)
{
lean_dec(v_a_1903_);
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v___y_1896_;
v___y_1869_ = v___y_1898_;
v___y_1870_ = v_a_1905_;
v___y_1871_ = v___x_1907_;
goto v___jp_1865_;
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1906_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1905_, v_a_1903_, v___x_1910_, v___x_1911_, v___x_1907_);
lean_dec(v_a_1903_);
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v___y_1896_;
v___y_1869_ = v___y_1898_;
v___y_1870_ = v_a_1905_;
v___y_1871_ = v___x_1912_;
goto v___jp_1865_;
}
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((size_t)0ULL);
v___x_1914_ = lean_usize_of_nat(v___x_1906_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1905_, v_a_1903_, v___x_1913_, v___x_1914_, v___x_1907_);
lean_dec(v_a_1903_);
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v___y_1896_;
v___y_1869_ = v___y_1898_;
v___y_1870_ = v_a_1905_;
v___y_1871_ = v___x_1915_;
goto v___jp_1865_;
}
}
}
else
{
lean_dec(v_a_1903_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
return v___x_1904_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_a_1900_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
v_a_1916_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1902_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1902_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_a_1900_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
v_a_1924_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1901_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1901_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
v___jp_1932_:
{
if (lean_obj_tag(v___y_1941_) == 0)
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___y_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___y_1941_, 1);
v___y_1892_ = v___y_1933_;
v___y_1893_ = v___y_1934_;
v___y_1894_ = v___y_1935_;
v___y_1895_ = v___y_1936_;
v___y_1896_ = v___y_1937_;
v___y_1897_ = v___y_1939_;
v___y_1898_ = v___y_1938_;
v___y_1899_ = v___y_1940_;
v_a_1900_ = v_a_1942_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v_mvarId_1855_);
v_a_1943_ = lean_ctor_get(v___y_1941_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___y_1941_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___y_1941_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___y_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2071_, lean_object* v___x_2072_, lean_object* v_e_2073_, lean_object* v_cfg_2074_, lean_object* v_term_x3f_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2071_, v___x_2072_, v_e_2073_, v_cfg_2074_, v_term_x3f_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec_ref(v_cfg_2074_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2082_, lean_object* v_e_2083_, lean_object* v_cfg_2084_, lean_object* v_term_x3f_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2082_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2092_, 0, v_mvarId_2082_);
lean_closure_set(v___f_2092_, 1, v___x_2091_);
lean_closure_set(v___f_2092_, 2, v_e_2083_);
lean_closure_set(v___f_2092_, 3, v_cfg_2084_);
lean_closure_set(v___f_2092_, 4, v_term_x3f_2085_);
v___x_2093_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2082_, v___f_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2094_, lean_object* v_e_2095_, lean_object* v_cfg_2096_, lean_object* v_term_x3f_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_MVarId_apply(v_mvarId_2094_, v_e_2095_, v_cfg_2096_, v_term_x3f_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2104_, lean_object* v_val_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2104_, v_val_2105_, v___y_2107_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2112_, lean_object* v_val_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2112_, v_val_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2120_, size_t v_i_2121_, size_t v_stop_2122_, lean_object* v_b_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2120_, v_i_2121_, v_stop_2122_, v_b_2123_, v___y_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2130_, lean_object* v_i_2131_, lean_object* v_stop_2132_, lean_object* v_b_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
size_t v_i_boxed_2139_; size_t v_stop_boxed_2140_; lean_object* v_res_2141_; 
v_i_boxed_2139_ = lean_unbox_usize(v_i_2131_);
lean_dec(v_i_2131_);
v_stop_boxed_2140_ = lean_unbox_usize(v_stop_2132_);
lean_dec(v_stop_2132_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2130_, v_i_boxed_2139_, v_stop_boxed_2140_, v_b_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec_ref(v_as_2130_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2143_, v_x_2144_, v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2147_, lean_object* v_x_2148_, size_t v_x_2149_, size_t v_x_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2148_, v_x_2149_, v_x_2150_, v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
size_t v_x_7971__boxed_2160_; size_t v_x_7972__boxed_2161_; lean_object* v_res_2162_; 
v_x_7971__boxed_2160_ = lean_unbox_usize(v_x_2156_);
lean_dec(v_x_2156_);
v_x_7972__boxed_2161_ = lean_unbox_usize(v_x_2157_);
lean_dec(v_x_2157_);
v_res_2162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2154_, v_x_2155_, v_x_7971__boxed_2160_, v_x_7972__boxed_2161_, v_x_2158_, v_x_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2163_, lean_object* v_n_2164_, lean_object* v_k_2165_, lean_object* v_v_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2164_, v_k_2165_, v_v_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2168_, size_t v_depth_2169_, lean_object* v_keys_2170_, lean_object* v_vals_2171_, lean_object* v_heq_2172_, lean_object* v_i_2173_, lean_object* v_entries_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2169_, v_keys_2170_, v_vals_2171_, v_i_2173_, v_entries_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_depth_2177_, lean_object* v_keys_2178_, lean_object* v_vals_2179_, lean_object* v_heq_2180_, lean_object* v_i_2181_, lean_object* v_entries_2182_){
_start:
{
size_t v_depth_boxed_2183_; lean_object* v_res_2184_; 
v_depth_boxed_2183_ = lean_unbox_usize(v_depth_2177_);
lean_dec(v_depth_2177_);
v_res_2184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2176_, v_depth_boxed_2183_, v_keys_2178_, v_vals_2179_, v_heq_2180_, v_i_2181_, v_entries_2182_);
lean_dec_ref(v_vals_2179_);
lean_dec_ref(v_keys_2178_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2186_, v_x_2187_, v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2194_, lean_object* v_c_2195_, lean_object* v_cfg_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; 
lean_inc(v_c_2195_);
v___x_2202_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2195_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2205_ = 0;
v___x_2206_ = l_Lean_MessageData_ofConstName(v_c_2195_, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2204_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2204_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = l_Lean_MVarId_apply(v_mvar_2194_, v_a_2203_, v_cfg_2196_, v___x_2209_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
return v___x_2210_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v_cfg_2196_);
lean_dec(v_c_2195_);
lean_dec(v_mvar_2194_);
v_a_2211_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2202_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2202_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2219_, lean_object* v_c_2220_, lean_object* v_cfg_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_MVarId_applyConst(v_mvar_2219_, v_c_2220_, v_cfg_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v_env_2235_; lean_object* v___x_2236_; lean_object* v_mctx_2237_; lean_object* v_lctx_2238_; lean_object* v_options_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2234_ = lean_st_ref_get(v___y_2232_);
v_env_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_env_2235_);
lean_dec(v___x_2234_);
v___x_2236_ = lean_st_ref_get(v___y_2230_);
v_mctx_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc_ref(v_mctx_2237_);
lean_dec(v___x_2236_);
v_lctx_2238_ = lean_ctor_get(v___y_2229_, 2);
v_options_2239_ = lean_ctor_get(v___y_2231_, 2);
lean_inc_ref(v_options_2239_);
lean_inc_ref(v_lctx_2238_);
v___x_2240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2240_, 0, v_env_2235_);
lean_ctor_set(v___x_2240_, 1, v_mctx_2237_);
lean_ctor_set(v___x_2240_, 2, v_lctx_2238_);
lean_ctor_set(v___x_2240_, 3, v_options_2239_);
v___x_2241_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v_msgData_2228_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_ref_2256_; lean_object* v___x_2257_; lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2266_; 
v_ref_2256_ = lean_ctor_get(v___y_2253_, 5);
v___x_2257_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_inc(v_ref_2256_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_ref_2256_);
lean_ctor_set(v___x_2262_, 1, v_a_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 1);
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2274_, size_t v_i_2275_, lean_object* v_bs_2276_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_usize_dec_lt(v_i_2275_, v_sz_2274_);
if (v___x_2277_ == 0)
{
return v_bs_2276_;
}
else
{
lean_object* v_v_2278_; lean_object* v___x_2279_; lean_object* v_bs_x27_2280_; lean_object* v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v_v_2278_ = lean_array_uget(v_bs_2276_, v_i_2275_);
v___x_2279_ = lean_unsigned_to_nat(0u);
v_bs_x27_2280_ = lean_array_uset(v_bs_2276_, v_i_2275_, v___x_2279_);
v___x_2281_ = l_Lean_Expr_mvarId_x21(v_v_2278_);
lean_dec(v_v_2278_);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_add(v_i_2275_, v___x_2282_);
v___x_2284_ = lean_array_uset(v_bs_x27_2280_, v_i_2275_, v___x_2281_);
v_i_2275_ = v___x_2283_;
v_bs_2276_ = v___x_2284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2286_, lean_object* v_i_2287_, lean_object* v_bs_2288_){
_start:
{
size_t v_sz_boxed_2289_; size_t v_i_boxed_2290_; lean_object* v_res_2291_; 
v_sz_boxed_2289_ = lean_unbox_usize(v_sz_2286_);
lean_dec(v_sz_2286_);
v_i_boxed_2290_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2289_, v_i_boxed_2290_, v_bs_2288_);
return v_res_2291_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2294_ = l_Lean_stringToMessageData(v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2297_ = l_Lean_stringToMessageData(v___x_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2300_ = l_Lean_stringToMessageData(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2309_ = l_Lean_stringToMessageData(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2310_, lean_object* v___x_2311_, lean_object* v_e_2312_, lean_object* v_n_2313_, uint8_t v_useApproxDefEq_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
lean_inc(v_mvarId_2310_);
v___x_2320_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2310_, v___x_2311_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref_known(v___x_2320_, 1);
lean_inc(v_mvarId_2310_);
v___x_2321_ = l_Lean_MVarId_getType(v_mvarId_2310_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
lean_inc(v___y_2318_);
lean_inc_ref(v___y_2317_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc_ref(v_e_2312_);
v___x_2323_ = lean_infer_type(v_e_2312_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = 0;
lean_inc(v_n_2313_);
v___x_2326_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2324_, v_n_2313_, v___x_2325_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_fst_2328_; lean_object* v_snd_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2419_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_fst_2328_ = lean_ctor_get(v_a_2327_, 0);
v_snd_2329_ = lean_ctor_get(v_a_2327_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_a_2327_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2331_ = v_a_2327_;
v_isShared_2332_ = v_isSharedCheck_2419_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snd_2329_);
lean_inc(v_fst_2328_);
lean_dec(v_a_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2419_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___y_2334_; lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2417_; 
v_snd_2349_ = lean_ctor_get(v_snd_2329_, 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_snd_2329_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v_snd_2329_, 0);
lean_dec(v_unused_2418_);
v___x_2351_ = v_snd_2329_;
v_isShared_2352_ = v_isSharedCheck_2417_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v_snd_2329_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2417_;
goto v_resetjp_2350_;
}
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2347_; 
lean_inc(v_fst_2328_);
v___x_2335_ = l_Lean_Expr_beta(v_e_2312_, v_fst_2328_);
v___x_2336_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2310_, v___x_2335_, v___y_2334_);
lean_dec(v___y_2334_);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2336_, 0);
lean_dec(v_unused_2348_);
v___x_2338_ = v___x_2336_;
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
else
{
lean_dec(v___x_2336_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v_sz_2340_ = lean_array_size(v_fst_2328_);
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2340_, v___x_2341_, v_fst_2328_);
v___x_2343_ = lean_array_to_list(v___x_2342_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2343_);
v___x_2345_ = v___x_2338_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
v_resetjp_2350_:
{
lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = lean_array_get_size(v_fst_2328_);
v___x_2398_ = lean_nat_dec_eq(v___x_2397_, v_n_2313_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_del_object(v___x_2351_);
lean_del_object(v___x_2331_);
lean_dec(v_fst_2328_);
lean_dec(v_a_2322_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v___x_2399_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2400_ = l_Nat_reprFast(v_n_2313_);
v___x_2401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
v___x_2402_ = l_Lean_MessageData_ofFormat(v___x_2401_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2399_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_indentExpr(v_snd_2349_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2407_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
v___y_2354_ = v___y_2315_;
v___y_2355_ = v___y_2316_;
v___y_2356_ = v___y_2317_;
v___y_2357_ = v___y_2318_;
goto v___jp_2353_;
}
v___jp_2353_:
{
lean_object* v___x_2358_; 
lean_inc(v_a_2322_);
lean_inc(v_snd_2349_);
v___x_2358_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2314_, v_snd_2349_, v_a_2322_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; uint8_t v___x_2360_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = lean_unbox(v_a_2359_);
lean_dec(v_a_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec(v_fst_2328_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v___x_2361_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2362_ = l_Lean_indentExpr(v_a_2322_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 7);
lean_ctor_set(v___x_2351_, 1, v___x_2362_);
lean_ctor_set(v___x_2351_, 0, v___x_2361_);
v___x_2364_ = v___x_2351_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2332_ == 0)
{
lean_ctor_set_tag(v___x_2331_, 7);
lean_ctor_set(v___x_2331_, 1, v___x_2365_);
lean_ctor_set(v___x_2331_, 0, v___x_2364_);
v___x_2367_ = v___x_2331_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v___x_2368_ = l_Lean_indentExpr(v_snd_2349_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Nat_reprFast(v_n_2313_);
v___x_2373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
v___x_2374_ = l_Lean_MessageData_ofFormat(v___x_2373_);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2371_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2377_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2354_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
lean_del_object(v___x_2331_);
lean_dec(v_a_2322_);
lean_dec(v_n_2313_);
v___y_2334_ = v___y_2355_;
goto v___jp_2333_;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
lean_del_object(v___x_2331_);
lean_dec(v_fst_2328_);
lean_dec(v_a_2322_);
lean_dec(v_n_2313_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v_a_2389_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2358_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2358_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_a_2322_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_n_2313_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v_a_2420_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2326_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2326_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2322_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_n_2313_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v_a_2428_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2323_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2323_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_n_2313_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v_a_2436_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2321_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2321_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_n_2313_);
lean_dec_ref(v_e_2312_);
lean_dec(v_mvarId_2310_);
v_a_2444_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2320_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2320_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2452_, lean_object* v___x_2453_, lean_object* v_e_2454_, lean_object* v_n_2455_, lean_object* v_useApproxDefEq_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2462_; lean_object* v_res_2463_; 
v_useApproxDefEq_boxed_2462_ = lean_unbox(v_useApproxDefEq_2456_);
v_res_2463_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2452_, v___x_2453_, v_e_2454_, v_n_2455_, v_useApproxDefEq_boxed_2462_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2464_, lean_object* v_e_2465_, lean_object* v_n_2466_, uint8_t v_useApproxDefEq_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2474_ = lean_box(v_useApproxDefEq_2467_);
lean_inc(v_mvarId_2464_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2475_, 0, v_mvarId_2464_);
lean_closure_set(v___f_2475_, 1, v___x_2473_);
lean_closure_set(v___f_2475_, 2, v_e_2465_);
lean_closure_set(v___f_2475_, 3, v_n_2466_);
lean_closure_set(v___f_2475_, 4, v___x_2474_);
v___x_2476_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2464_, v___f_2475_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2477_, lean_object* v_e_2478_, lean_object* v_n_2479_, lean_object* v_useApproxDefEq_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2486_; lean_object* v_res_2487_; 
v_useApproxDefEq_boxed_2486_ = lean_unbox(v_useApproxDefEq_2480_);
v_res_2487_ = l_Lean_MVarId_applyN(v_mvarId_2477_, v_e_2478_, v_n_2479_, v_useApproxDefEq_boxed_2486_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2488_, lean_object* v_msg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2496_, lean_object* v_msg_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2496_, v_msg_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_box(0);
v___x_2515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2516_ = l_Lean_mkConst(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2517_, lean_object* v_type_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2525_; 
lean_inc(v_a_2523_);
lean_inc_ref(v_a_2522_);
lean_inc(v_a_2521_);
lean_inc_ref(v_a_2520_);
v___x_2525_ = lean_whnf(v_type_2518_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2528_ = lean_unsigned_to_nat(2u);
v___x_2529_ = l_Lean_Expr_isAppOfArity(v_a_2526_, v___x_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2530_ = lean_st_ref_get(v_a_2519_);
v___x_2531_ = lean_array_get_size(v___x_2530_);
lean_dec(v___x_2530_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v___x_2531_, v___x_2532_);
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2535_ = lean_name_append_index_after(v___x_2534_, v___x_2533_);
v___x_2536_ = l_Lean_Name_append(v_tag_2517_, v___x_2535_);
v___x_2537_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2526_, v___x_2536_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2549_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2549_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2549_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2542_ = lean_st_ref_take(v_a_2519_);
v___x_2543_ = l_Lean_Expr_mvarId_x21(v_a_2538_);
v___x_2544_ = lean_array_push(v___x_2542_, v___x_2543_);
v___x_2545_ = lean_st_ref_put(v_a_2519_, v___x_2544_);
if (v_isShared_2541_ == 0)
{
v___x_2547_ = v___x_2540_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2538_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
return v___x_2537_;
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = l_Lean_Expr_appFn_x21(v_a_2526_);
v___x_2551_ = l_Lean_Expr_appArg_x21(v___x_2550_);
lean_dec_ref(v___x_2550_);
lean_inc_ref(v___x_2551_);
lean_inc(v_tag_2517_);
v___x_2552_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2517_, v___x_2551_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l_Lean_Expr_appArg_x21(v_a_2526_);
lean_dec(v_a_2526_);
lean_inc_ref(v___x_2554_);
v___x_2555_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2517_, v___x_2554_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2565_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2561_ = l_Lean_mkApp4(v___x_2560_, v___x_2551_, v___x_2554_, v_a_2553_, v_a_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2561_);
v___x_2563_ = v___x_2558_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_dec_ref(v___x_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v___x_2551_);
return v___x_2555_;
}
}
else
{
lean_dec_ref(v___x_2551_);
lean_dec(v_a_2526_);
lean_dec(v_tag_2517_);
return v___x_2552_;
}
}
}
else
{
lean_dec(v_tag_2517_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2566_, lean_object* v_type_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2566_, v_type_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2575_, lean_object* v___x_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
lean_inc(v_mvarId_2575_);
v___x_2582_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2575_, v___x_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2582_, 1);
lean_inc(v_mvarId_2575_);
v___x_2583_ = l_Lean_MVarId_getType_x27(v_mvarId_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2629_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2629_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2629_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2589_ = lean_unsigned_to_nat(2u);
v___x_2590_ = l_Lean_Expr_isAppOfArity(v_a_2584_, v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_dec(v_a_2584_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2592_, 0, v_mvarId_2575_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2592_);
v___x_2594_ = v___x_2586_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2596_; 
lean_del_object(v___x_2586_);
lean_inc(v_mvarId_2575_);
v___x_2596_ = l_Lean_MVarId_getTag(v_mvarId_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2599_ = lean_st_mk_ref(v___x_2598_);
v___x_2600_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2597_, v_a_2584_, v___x_2599_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = lean_st_ref_get(v___x_2599_);
lean_dec(v___x_2599_);
v___x_2603_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2575_, v_a_2601_, v___y_2578_);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2603_, 0);
lean_dec(v_unused_2612_);
v___x_2605_ = v___x_2603_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v___x_2603_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = lean_array_to_list(v___x_2602_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___x_2599_);
lean_dec(v_mvarId_2575_);
v_a_2613_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2600_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2600_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2584_);
lean_dec(v_mvarId_2575_);
v_a_2621_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2596_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2596_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_mvarId_2575_);
v_a_2630_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2583_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2583_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_mvarId_2575_);
v_a_2638_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2582_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2582_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2646_, lean_object* v___x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2646_, v___x_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; 
v___x_2663_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2657_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2664_, 0, v_mvarId_2657_);
lean_closure_set(v___f_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2657_, v___f_2664_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_MVarId_splitAndCore(v_mvarId_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_MVarId_splitAndCore(v_mvarId_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_MVarId_splitAnd(v_mvarId_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2686_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2692_ = l_Lean_mkConst(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2697_, lean_object* v___x_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
lean_inc(v_mvarId_2697_);
v___x_2704_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2697_, v___x_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2705_; 
lean_dec_ref_known(v___x_2704_, 1);
lean_inc(v_mvarId_2697_);
v___x_2705_ = l_Lean_MVarId_getType(v_mvarId_2697_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v_a_2708_; lean_object* v___x_2709_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2706_, v___y_2700_);
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc_n(v_a_2708_, 2);
lean_dec_ref(v___x_2707_);
v___x_2709_ = l_Lean_Meta_getLevel(v_a_2708_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
lean_inc(v_mvarId_2697_);
v___x_2711_ = l_Lean_MVarId_getTag(v_mvarId_2697_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2715_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2714_, v_a_2712_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2729_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_n(v_a_2716_, 2);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2710_);
lean_ctor_set(v___x_2718_, 1, v___x_2713_);
v___x_2719_ = l_Lean_mkConst(v___x_2717_, v___x_2718_);
v___x_2720_ = l_Lean_mkAppB(v___x_2719_, v_a_2708_, v_a_2716_);
v___x_2721_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2697_, v___x_2720_, v___y_2700_);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2721_, 0);
lean_dec(v_unused_2730_);
v___x_2723_ = v___x_2721_;
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
else
{
lean_dec(v___x_2721_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = l_Lean_Expr_mvarId_x21(v_a_2716_);
lean_dec(v_a_2716_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2710_);
lean_dec(v_a_2708_);
lean_dec(v_mvarId_2697_);
v_a_2731_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2715_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2715_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2710_);
lean_dec(v_a_2708_);
lean_dec(v_mvarId_2697_);
v_a_2739_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2711_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2711_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2708_);
lean_dec(v_mvarId_2697_);
v_a_2747_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2709_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2709_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_mvarId_2697_);
v_a_2755_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2705_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2705_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_mvarId_2697_);
v_a_2763_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2704_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2704_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2771_, lean_object* v___x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2771_, v___x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; 
v___x_2788_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2782_);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2789_, 0, v_mvarId_2782_);
lean_closure_set(v___f_2789_, 1, v___x_2788_);
v___x_2790_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2782_, v___f_2789_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_MVarId_exfalso(v_mvarId_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
return v_res_2797_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2802_ = l_Lean_MessageData_ofFormat(v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2809_, lean_object* v_name_2810_, lean_object* v_idx_2811_, lean_object* v_expected_x3f_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___x_2825_; 
lean_inc(v_name_2810_);
lean_inc(v_goal_2809_);
v___x_2825_ = l_Lean_MVarId_checkNotAssigned(v_goal_2809_, v_name_2810_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; 
lean_dec_ref_known(v___x_2825_, 1);
lean_inc(v_goal_2809_);
v___x_2826_ = l_Lean_MVarId_getType_x27(v_goal_2809_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = l_Lean_Expr_getAppFn(v_a_2827_);
lean_dec(v_a_2827_);
if (lean_obj_tag(v___x_2828_) == 4)
{
lean_object* v_declName_2829_; lean_object* v_us_2830_; lean_object* v___x_2831_; lean_object* v_env_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
v_declName_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_declName_2829_);
v_us_2830_ = lean_ctor_get(v___x_2828_, 1);
lean_inc(v_us_2830_);
lean_dec_ref_known(v___x_2828_, 2);
v___x_2831_ = lean_st_ref_get(v___y_2816_);
v_env_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_ref(v_env_2832_);
lean_dec(v___x_2831_);
v___x_2833_ = 0;
v___x_2834_ = l_Lean_Environment_find_x3f(v_env_2832_, v_declName_2829_, v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_dec(v_us_2830_);
lean_dec(v_expected_x3f_2812_);
lean_dec(v_idx_2811_);
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
v___y_2822_ = v___y_2816_;
goto v___jp_2818_;
}
else
{
lean_object* v_val_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2905_; 
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2905_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_val_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2905_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
if (lean_obj_tag(v_val_2835_) == 5)
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2904_; 
v_val_2839_ = lean_ctor_get(v_val_2835_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_val_2835_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2841_ = v_val_2835_;
v_isShared_2842_ = v_isSharedCheck_2904_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v_val_2835_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2904_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; 
if (lean_obj_tag(v_expected_x3f_2812_) == 1)
{
lean_object* v_val_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2903_; 
v_val_2874_ = lean_ctor_get(v_expected_x3f_2812_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_expected_x3f_2812_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2876_ = v_expected_x3f_2812_;
v_isShared_2877_ = v_isSharedCheck_2903_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_val_2874_);
lean_dec(v_expected_x3f_2812_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2903_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v_ctors_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v_ctors_2878_ = lean_ctor_get(v_val_2839_, 4);
v___x_2879_ = l_List_lengthTR___redArg(v_ctors_2878_);
v___x_2880_ = lean_nat_dec_eq(v___x_2879_, v_val_2874_);
lean_dec(v___x_2879_);
if (v___x_2880_ == 0)
{
uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2881_ = 1;
lean_inc(v_name_2810_);
v___x_2882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2810_, v___x_2881_);
v___x_2883_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2884_ = lean_string_append(v___x_2882_, v___x_2883_);
v___x_2885_ = l_Nat_reprFast(v_val_2874_);
v___x_2886_ = lean_string_append(v___x_2884_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
v___x_2890_ = l_Lean_MessageData_ofFormat(v___x_2889_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2890_);
v___x_2892_ = v___x_2876_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; 
lean_inc(v_goal_2809_);
lean_inc(v_name_2810_);
v___x_2893_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2810_, v_goal_2809_, v___x_2892_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref_known(v___x_2893_, 1);
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
v___y_2847_ = v___y_2816_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_del_object(v___x_2841_);
lean_dec_ref(v_val_2839_);
lean_del_object(v___x_2837_);
lean_dec(v_us_2830_);
lean_dec(v_idx_2811_);
lean_dec(v_name_2810_);
lean_dec(v_goal_2809_);
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
else
{
lean_del_object(v___x_2876_);
lean_dec(v_val_2874_);
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
v___y_2847_ = v___y_2816_;
goto v___jp_2843_;
}
}
}
else
{
lean_dec(v_expected_x3f_2812_);
v___y_2844_ = v___y_2813_;
v___y_2845_ = v___y_2814_;
v___y_2846_ = v___y_2815_;
v___y_2847_ = v___y_2816_;
goto v___jp_2843_;
}
v___jp_2843_:
{
lean_object* v_ctors_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_ctors_2848_ = lean_ctor_get(v_val_2839_, 4);
lean_inc(v_ctors_2848_);
lean_dec_ref(v_val_2839_);
v___x_2849_ = l_List_lengthTR___redArg(v_ctors_2848_);
v___x_2850_ = lean_nat_dec_lt(v_idx_2811_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
lean_dec(v_ctors_2848_);
lean_dec(v_us_2830_);
v___x_2851_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2852_ = l_Nat_reprFast(v_idx_2811_);
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
v___x_2856_ = l_Nat_reprFast(v___x_2849_);
v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2859_ = lean_string_append(v___x_2857_, v___x_2858_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 3);
lean_ctor_set(v___x_2841_, 0, v___x_2859_);
v___x_2861_ = v___x_2841_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = l_Lean_MessageData_ofFormat(v___x_2861_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2862_);
v___x_2864_ = v___x_2837_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2810_, v_goal_2809_, v___x_2864_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2865_;
}
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v___x_2849_);
lean_del_object(v___x_2841_);
lean_del_object(v___x_2837_);
lean_dec(v_name_2810_);
v___x_2868_ = l_List_get___redArg(v_ctors_2848_, v_idx_2811_);
lean_dec(v_ctors_2848_);
v___x_2869_ = l_Lean_mkConst(v___x_2868_, v_us_2830_);
v___x_2870_ = 0;
v___x_2871_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2871_, 0, v___x_2870_);
lean_ctor_set_uint8(v___x_2871_, 1, v___x_2850_);
lean_ctor_set_uint8(v___x_2871_, 2, v___x_2833_);
lean_ctor_set_uint8(v___x_2871_, 3, v___x_2850_);
v___x_2872_ = lean_box(0);
v___x_2873_ = l_Lean_MVarId_apply(v_goal_2809_, v___x_2869_, v___x_2871_, v___x_2872_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2873_;
}
}
}
}
else
{
lean_del_object(v___x_2837_);
lean_dec(v_val_2835_);
lean_dec(v_us_2830_);
lean_dec(v_expected_x3f_2812_);
lean_dec(v_idx_2811_);
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
v___y_2822_ = v___y_2816_;
goto v___jp_2818_;
}
}
}
}
else
{
lean_dec_ref(v___x_2828_);
lean_dec(v_expected_x3f_2812_);
lean_dec(v_idx_2811_);
v___y_2819_ = v___y_2813_;
v___y_2820_ = v___y_2814_;
v___y_2821_ = v___y_2815_;
v___y_2822_ = v___y_2816_;
goto v___jp_2818_;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_expected_x3f_2812_);
lean_dec(v_idx_2811_);
lean_dec(v_name_2810_);
lean_dec(v_goal_2809_);
v_a_2906_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2826_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2826_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_expected_x3f_2812_);
lean_dec(v_idx_2811_);
lean_dec(v_name_2810_);
lean_dec(v_goal_2809_);
v_a_2914_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2825_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2825_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
v___jp_2818_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2824_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2810_, v_goal_2809_, v___x_2823_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2922_, lean_object* v_name_2923_, lean_object* v_idx_2924_, lean_object* v_expected_x3f_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2922_, v_name_2923_, v_idx_2924_, v_expected_x3f_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2932_, lean_object* v_idx_2933_, lean_object* v_expected_x3f_2934_, lean_object* v_goal_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v___f_2941_; lean_object* v___x_2942_; 
lean_inc(v_goal_2935_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2941_, 0, v_goal_2935_);
lean_closure_set(v___f_2941_, 1, v_name_2932_);
lean_closure_set(v___f_2941_, 2, v_idx_2933_);
lean_closure_set(v___f_2941_, 3, v_expected_x3f_2934_);
v___x_2942_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2935_, v___f_2941_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2943_, lean_object* v_idx_2944_, lean_object* v_expected_x3f_2945_, lean_object* v_goal_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_MVarId_nthConstructor(v_name_2943_, v_idx_2944_, v_expected_x3f_2945_, v_goal_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Meta_saveState___redArg(v___y_2955_, v___y_2957_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc_ref(v___y_2954_);
v___x_2961_ = lean_apply_5(v_x_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, lean_box(0));
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_a_2960_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2962_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3000_; 
v_a_2971_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2973_ = v___x_2961_;
v_isShared_2974_ = v_isSharedCheck_3000_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2961_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3000_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
uint8_t v___y_2976_; uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_Exception_isInterrupt(v_a_2971_);
if (v___x_2998_ == 0)
{
uint8_t v___x_2999_; 
lean_inc(v_a_2971_);
v___x_2999_ = l_Lean_Exception_isRuntime(v_a_2971_);
v___y_2976_ = v___x_2999_;
goto v___jp_2975_;
}
else
{
v___y_2976_ = v___x_2998_;
goto v___jp_2975_;
}
v___jp_2975_:
{
if (v___y_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_del_object(v___x_2973_);
lean_dec(v_a_2971_);
v___x_2977_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2960_, v___y_2955_, v___y_2957_);
lean_dec(v_a_2960_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2985_; 
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2977_, 0);
lean_dec(v_unused_2986_);
v___x_2979_ = v___x_2977_;
v_isShared_2980_ = v_isSharedCheck_2985_;
goto v_resetjp_2978_;
}
else
{
lean_dec(v___x_2977_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2985_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2981_ = lean_box(0);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2987_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2977_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2977_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v___x_2996_; 
lean_dec(v_a_2960_);
if (v_isShared_2974_ == 0)
{
v___x_2996_ = v___x_2973_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2971_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref(v_x_2953_);
v_a_3001_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2959_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2959_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3016_, lean_object* v_x_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_x_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3024_, v_x_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3031_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3034_ = l_Lean_stringToMessageData(v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3035_, lean_object* v___x_3036_, lean_object* v___x_3037_, lean_object* v___x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_MVarId_apply(v_mvarId_3035_, v___x_3036_, v___x_3037_, v___x_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3061_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3061_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3061_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; 
if (lean_obj_tag(v_a_3045_) == 1)
{
lean_object* v_tail_3056_; 
v_tail_3056_ = lean_ctor_get(v_a_3045_, 1);
if (lean_obj_tag(v_tail_3056_) == 0)
{
lean_object* v_head_3057_; lean_object* v___x_3059_; 
v_head_3057_ = lean_ctor_get(v_a_3045_, 0);
lean_inc(v_head_3057_);
lean_dec_ref_known(v_a_3045_, 2);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_head_3057_);
v___x_3059_ = v___x_3047_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_head_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
else
{
lean_dec_ref_known(v_a_3045_, 2);
lean_del_object(v___x_3047_);
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
v___y_3053_ = v___y_3042_;
goto v___jp_3049_;
}
}
else
{
lean_del_object(v___x_3047_);
lean_dec(v_a_3045_);
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
v___y_3053_ = v___y_3042_;
goto v___jp_3049_;
}
v___jp_3049_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3055_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3054_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
return v___x_3055_;
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
v_a_3062_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3044_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3044_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3070_, lean_object* v___x_3071_, lean_object* v___x_3072_, lean_object* v___x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3070_, v___x_3071_, v___x_3072_, v___x_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3079_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3085_ = l_Lean_mkConst(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; 
v___x_3096_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3097_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3098_ = lean_box(0);
lean_inc(v_mvarId_3090_);
v___f_3099_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3099_, 0, v_mvarId_3090_);
lean_closure_set(v___f_3099_, 1, v___x_3096_);
lean_closure_set(v___f_3099_, 2, v___x_3097_);
lean_closure_set(v___f_3099_, 3, v___x_3098_);
v___x_3100_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3099_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3112_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
if (lean_obj_tag(v_a_3101_) == 0)
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v_mvarId_3090_);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_mvarId_3090_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
else
{
lean_object* v_val_3108_; lean_object* v___x_3110_; 
lean_dec(v_mvarId_3090_);
v_val_3108_ = lean_ctor_get(v_a_3101_, 0);
lean_inc(v_val_3108_);
lean_dec_ref_known(v_a_3101_, 1);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v_val_3108_);
v___x_3110_ = v___x_3103_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_val_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_mvarId_3090_);
v_a_3113_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3100_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3100_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_MVarId_iffOfEq(v_mvarId_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
return v_res_3127_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3136_ = l_Lean_mkConst(v___x_3135_, v___x_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3137_, lean_object* v_mvarId_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v_keyedConfig_3151_; uint8_t v_trackZetaDelta_3152_; lean_object* v_zetaDeltaSet_3153_; lean_object* v_lctx_3154_; lean_object* v_localInstances_3155_; lean_object* v_defEqCtx_x3f_3156_; lean_object* v_synthPendingDepth_3157_; lean_object* v_customCanUnfoldPredicate_x3f_3158_; uint8_t v_univApprox_3159_; uint8_t v_inTypeClassResolution_3160_; uint8_t v_cacheInferType_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_keyedConfig_3151_ = lean_ctor_get(v___y_3139_, 0);
v_trackZetaDelta_3152_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*7);
v_zetaDeltaSet_3153_ = lean_ctor_get(v___y_3139_, 1);
v_lctx_3154_ = lean_ctor_get(v___y_3139_, 2);
v_localInstances_3155_ = lean_ctor_get(v___y_3139_, 3);
v_defEqCtx_x3f_3156_ = lean_ctor_get(v___y_3139_, 4);
v_synthPendingDepth_3157_ = lean_ctor_get(v___y_3139_, 5);
v_customCanUnfoldPredicate_x3f_3158_ = lean_ctor_get(v___y_3139_, 6);
v_univApprox_3159_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3160_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*7 + 2);
v_cacheInferType_3161_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3151_);
v___x_3162_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3137_, v_keyedConfig_3151_);
lean_inc(v_customCanUnfoldPredicate_x3f_3158_);
lean_inc(v_synthPendingDepth_3157_);
lean_inc(v_defEqCtx_x3f_3156_);
lean_inc_ref(v_localInstances_3155_);
lean_inc_ref(v_lctx_3154_);
lean_inc(v_zetaDeltaSet_3153_);
v___x_3163_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v_zetaDeltaSet_3153_);
lean_ctor_set(v___x_3163_, 2, v_lctx_3154_);
lean_ctor_set(v___x_3163_, 3, v_localInstances_3155_);
lean_ctor_set(v___x_3163_, 4, v_defEqCtx_x3f_3156_);
lean_ctor_set(v___x_3163_, 5, v_synthPendingDepth_3157_);
lean_ctor_set(v___x_3163_, 6, v_customCanUnfoldPredicate_x3f_3158_);
lean_ctor_set_uint8(v___x_3163_, sizeof(void*)*7, v_trackZetaDelta_3152_);
lean_ctor_set_uint8(v___x_3163_, sizeof(void*)*7 + 1, v_univApprox_3159_);
lean_ctor_set_uint8(v___x_3163_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3160_);
lean_ctor_set_uint8(v___x_3163_, sizeof(void*)*7 + 3, v_cacheInferType_3161_);
lean_inc(v_mvarId_3138_);
v___x_3164_ = l_Lean_MVarId_getType_x27(v_mvarId_3138_, v___x_3163_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref_known(v___x_3163_, 7);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3167_ = lean_unsigned_to_nat(3u);
v___x_3168_ = l_Lean_Expr_isAppOfArity(v_a_3165_, v___x_3166_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v_a_3165_);
lean_dec(v_mvarId_3138_);
v___x_3194_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3195_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3194_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref(v___y_3139_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = l_Lean_Expr_appFn_x21(v_a_3165_);
lean_dec(v_a_3165_);
v___x_3197_ = l_Lean_Expr_appArg_x21(v___x_3196_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = l_Lean_Meta_isProp(v___x_3197_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; uint8_t v___x_3200_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3200_ = lean_unbox(v_a_3199_);
lean_dec(v_a_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_mvarId_3138_);
v___x_3201_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3202_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3201_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref(v___y_3139_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
goto v___jp_3169_;
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v___y_3139_);
lean_dec(v_mvarId_3138_);
v_a_3211_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3198_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3198_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
v___jp_3169_:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3170_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3171_ = 0;
v___x_3172_ = 0;
v___x_3173_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3173_, 0, v___x_3171_);
lean_ctor_set_uint8(v___x_3173_, 1, v___x_3168_);
lean_ctor_set_uint8(v___x_3173_, 2, v___x_3172_);
lean_ctor_set_uint8(v___x_3173_, 3, v___x_3168_);
v___x_3174_ = lean_box(0);
v___x_3175_ = l_Lean_MVarId_apply(v_mvarId_3138_, v___x_3170_, v___x_3173_, v___x_3174_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3185_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3185_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3185_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
if (lean_obj_tag(v_a_3176_) == 1)
{
lean_object* v_tail_3180_; 
v_tail_3180_ = lean_ctor_get(v_a_3176_, 1);
if (lean_obj_tag(v_tail_3180_) == 0)
{
lean_object* v_head_3181_; lean_object* v___x_3183_; 
lean_dec_ref(v___y_3139_);
v_head_3181_ = lean_ctor_get(v_a_3176_, 0);
lean_inc(v_head_3181_);
lean_dec_ref_known(v_a_3176_, 2);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v_head_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_head_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
else
{
lean_dec_ref_known(v_a_3176_, 2);
lean_del_object(v___x_3178_);
v___y_3145_ = v___y_3139_;
v___y_3146_ = v___y_3140_;
v___y_3147_ = v___y_3141_;
v___y_3148_ = v___y_3142_;
goto v___jp_3144_;
}
}
else
{
lean_del_object(v___x_3178_);
lean_dec(v_a_3176_);
v___y_3145_ = v___y_3139_;
v___y_3146_ = v___y_3140_;
v___y_3147_ = v___y_3141_;
v___y_3148_ = v___y_3142_;
goto v___jp_3144_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v___y_3139_);
v_a_3186_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3175_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3175_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v___y_3139_);
lean_dec(v_mvarId_3138_);
v_a_3219_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3164_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3164_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
v___jp_3144_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3150_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3149_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec_ref(v___y_3145_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3227_, lean_object* v_mvarId_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
uint8_t v___x_2337__boxed_3234_; lean_object* v_res_3235_; 
v___x_2337__boxed_3234_ = lean_unbox(v___x_3227_);
v_res_3235_ = l_Lean_MVarId_propext___lam__0(v___x_2337__boxed_3234_, v_mvarId_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
uint8_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; 
v___x_3242_ = 2;
v___x_3243_ = lean_box(v___x_3242_);
lean_inc(v_mvarId_3236_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3244_, 0, v___x_3243_);
lean_closure_set(v___f_3244_, 1, v_mvarId_3236_);
v___x_3245_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3244_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3257_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3257_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3257_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
if (lean_obj_tag(v_a_3246_) == 0)
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v_mvarId_3236_);
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_mvarId_3236_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
else
{
lean_object* v_val_3253_; lean_object* v___x_3255_; 
lean_dec(v_mvarId_3236_);
v_val_3253_ = lean_ctor_get(v_a_3246_, 0);
lean_inc(v_val_3253_);
lean_dec_ref_known(v_a_3246_, 1);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v_val_3253_);
v___x_3255_ = v___x_3248_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_val_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_mvarId_3236_);
v_a_3258_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3245_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3245_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_MVarId_propext(v_mvarId_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3279_, lean_object* v___x_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
lean_inc(v_mvarId_3279_);
v___x_3286_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3279_, v___x_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_keyedConfig_3287_; uint8_t v_trackZetaDelta_3288_; lean_object* v_zetaDeltaSet_3289_; lean_object* v_lctx_3290_; lean_object* v_localInstances_3291_; lean_object* v_defEqCtx_x3f_3292_; lean_object* v_synthPendingDepth_3293_; lean_object* v_customCanUnfoldPredicate_x3f_3294_; uint8_t v_univApprox_3295_; uint8_t v_inTypeClassResolution_3296_; uint8_t v_cacheInferType_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec_ref_known(v___x_3286_, 1);
v_keyedConfig_3287_ = lean_ctor_get(v___y_3281_, 0);
v_trackZetaDelta_3288_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*7);
v_zetaDeltaSet_3289_ = lean_ctor_get(v___y_3281_, 1);
v_lctx_3290_ = lean_ctor_get(v___y_3281_, 2);
v_localInstances_3291_ = lean_ctor_get(v___y_3281_, 3);
v_defEqCtx_x3f_3292_ = lean_ctor_get(v___y_3281_, 4);
v_synthPendingDepth_3293_ = lean_ctor_get(v___y_3281_, 5);
v_customCanUnfoldPredicate_x3f_3294_ = lean_ctor_get(v___y_3281_, 6);
v_univApprox_3295_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3296_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*7 + 2);
v_cacheInferType_3297_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*7 + 3);
v___x_3298_ = 2;
lean_inc_ref(v_keyedConfig_3287_);
v___x_3299_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3298_, v_keyedConfig_3287_);
lean_inc(v_customCanUnfoldPredicate_x3f_3294_);
lean_inc(v_synthPendingDepth_3293_);
lean_inc(v_defEqCtx_x3f_3292_);
lean_inc_ref(v_localInstances_3291_);
lean_inc_ref(v_lctx_3290_);
lean_inc(v_zetaDeltaSet_3289_);
v___x_3300_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v_zetaDeltaSet_3289_);
lean_ctor_set(v___x_3300_, 2, v_lctx_3290_);
lean_ctor_set(v___x_3300_, 3, v_localInstances_3291_);
lean_ctor_set(v___x_3300_, 4, v_defEqCtx_x3f_3292_);
lean_ctor_set(v___x_3300_, 5, v_synthPendingDepth_3293_);
lean_ctor_set(v___x_3300_, 6, v_customCanUnfoldPredicate_x3f_3294_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7, v_trackZetaDelta_3288_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 1, v_univApprox_3295_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3296_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 3, v_cacheInferType_3297_);
lean_inc(v_mvarId_3279_);
v___x_3301_ = l_Lean_MVarId_getType_x27(v_mvarId_3279_, v___x_3300_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec_ref_known(v___x_3300_, 7);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3304_ = lean_unsigned_to_nat(4u);
v___x_3305_ = l_Lean_Expr_isAppOfArity(v_a_3302_, v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_a_3302_);
lean_dec(v_mvarId_3279_);
v___x_3306_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3307_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3306_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec_ref(v___y_3281_);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3308_ = l_Lean_Expr_appFn_x21(v_a_3302_);
v___x_3309_ = l_Lean_Expr_appFn_x21(v___x_3308_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = l_Lean_Expr_appArg_x21(v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = l_Lean_Expr_appArg_x21(v_a_3302_);
lean_dec(v_a_3302_);
v___x_3312_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3313_ = lean_unsigned_to_nat(2u);
v___x_3314_ = lean_mk_empty_array_with_capacity(v___x_3313_);
v___x_3315_ = lean_array_push(v___x_3314_, v___x_3310_);
v___x_3316_ = lean_array_push(v___x_3315_, v___x_3311_);
v___x_3317_ = l_Lean_Meta_mkAppM(v___x_3312_, v___x_3316_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec_ref(v___y_3281_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3327_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3279_, v_a_3318_, v___y_3282_);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3328_);
v___x_3321_ = v___x_3319_;
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
else
{
lean_dec(v___x_3319_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = lean_box(v___x_3305_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v_mvarId_3279_);
v_a_3329_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3317_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3317_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v___y_3281_);
lean_dec(v_mvarId_3279_);
v_a_3337_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3301_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3301_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v___y_3281_);
lean_dec(v_mvarId_3279_);
v_a_3345_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3286_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3286_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3353_, lean_object* v___x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3353_, v___x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3381_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3381_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3381_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
if (lean_obj_tag(v_a_3368_) == 0)
{
uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3372_ = 0;
v___x_3373_ = lean_box(v___x_3372_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3373_);
v___x_3375_ = v___x_3370_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
else
{
lean_object* v_val_3377_; lean_object* v___x_3379_; 
v_val_3377_ = lean_ctor_get(v_a_3368_, 0);
lean_inc(v_val_3377_);
lean_dec_ref_known(v_a_3368_, 1);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v_val_3377_);
v___x_3379_ = v___x_3370_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_val_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3382_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3367_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3367_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v___f_3407_; lean_object* v___f_3408_; lean_object* v___x_3409_; 
v___x_3406_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3400_);
v___f_3407_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3407_, 0, v_mvarId_3400_);
lean_closure_set(v___f_3407_, 1, v___x_3406_);
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3408_, 0, v___f_3407_);
v___x_3409_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3400_, v___f_3408_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3421_, lean_object* v___x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
lean_inc(v_mvarId_3421_);
v___x_3428_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3421_, v___x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_keyedConfig_3429_; uint8_t v_trackZetaDelta_3430_; lean_object* v_zetaDeltaSet_3431_; lean_object* v_lctx_3432_; lean_object* v_localInstances_3433_; lean_object* v_defEqCtx_x3f_3434_; lean_object* v_synthPendingDepth_3435_; lean_object* v_customCanUnfoldPredicate_x3f_3436_; uint8_t v_univApprox_3437_; uint8_t v_inTypeClassResolution_3438_; uint8_t v_cacheInferType_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref_known(v___x_3428_, 1);
v_keyedConfig_3429_ = lean_ctor_get(v___y_3423_, 0);
v_trackZetaDelta_3430_ = lean_ctor_get_uint8(v___y_3423_, sizeof(void*)*7);
v_zetaDeltaSet_3431_ = lean_ctor_get(v___y_3423_, 1);
v_lctx_3432_ = lean_ctor_get(v___y_3423_, 2);
v_localInstances_3433_ = lean_ctor_get(v___y_3423_, 3);
v_defEqCtx_x3f_3434_ = lean_ctor_get(v___y_3423_, 4);
v_synthPendingDepth_3435_ = lean_ctor_get(v___y_3423_, 5);
v_customCanUnfoldPredicate_x3f_3436_ = lean_ctor_get(v___y_3423_, 6);
v_univApprox_3437_ = lean_ctor_get_uint8(v___y_3423_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3438_ = lean_ctor_get_uint8(v___y_3423_, sizeof(void*)*7 + 2);
v_cacheInferType_3439_ = lean_ctor_get_uint8(v___y_3423_, sizeof(void*)*7 + 3);
v___x_3440_ = 2;
lean_inc_ref(v_keyedConfig_3429_);
v___x_3441_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3440_, v_keyedConfig_3429_);
lean_inc(v_customCanUnfoldPredicate_x3f_3436_);
lean_inc(v_synthPendingDepth_3435_);
lean_inc(v_defEqCtx_x3f_3434_);
lean_inc_ref(v_localInstances_3433_);
lean_inc_ref(v_lctx_3432_);
lean_inc(v_zetaDeltaSet_3431_);
v___x_3442_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
lean_ctor_set(v___x_3442_, 1, v_zetaDeltaSet_3431_);
lean_ctor_set(v___x_3442_, 2, v_lctx_3432_);
lean_ctor_set(v___x_3442_, 3, v_localInstances_3433_);
lean_ctor_set(v___x_3442_, 4, v_defEqCtx_x3f_3434_);
lean_ctor_set(v___x_3442_, 5, v_synthPendingDepth_3435_);
lean_ctor_set(v___x_3442_, 6, v_customCanUnfoldPredicate_x3f_3436_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7, v_trackZetaDelta_3430_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 1, v_univApprox_3437_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3438_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 3, v_cacheInferType_3439_);
lean_inc(v_mvarId_3421_);
v___x_3443_ = l_Lean_MVarId_getType_x27(v_mvarId_3421_, v___x_3442_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref_known(v___x_3442_, 7);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v___x_3445_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3446_ = lean_unsigned_to_nat(3u);
v___x_3447_ = l_Lean_Expr_isAppOfArity(v_a_3444_, v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec(v_a_3444_);
lean_dec(v_mvarId_3421_);
v___x_3448_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3449_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3448_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___y_3423_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3450_ = l_Lean_Expr_appFn_x21(v_a_3444_);
v___x_3451_ = l_Lean_Expr_appArg_x21(v___x_3450_);
lean_dec_ref(v___x_3450_);
v___x_3452_ = l_Lean_Expr_appArg_x21(v_a_3444_);
lean_dec(v_a_3444_);
v___x_3453_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3454_ = lean_unsigned_to_nat(2u);
v___x_3455_ = lean_mk_empty_array_with_capacity(v___x_3454_);
v___x_3456_ = lean_array_push(v___x_3455_, v___x_3451_);
v___x_3457_ = lean_array_push(v___x_3456_, v___x_3452_);
v___x_3458_ = l_Lean_Meta_mkAppM(v___x_3453_, v___x_3457_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___y_3423_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3468_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3421_, v_a_3459_, v___y_3424_);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3469_);
v___x_3462_ = v___x_3460_;
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v___x_3460_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(v___x_3447_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v___x_3464_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v_mvarId_3421_);
v_a_3470_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3458_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3458_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v___y_3423_);
lean_dec(v_mvarId_3421_);
v_a_3478_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3443_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3443_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___y_3423_);
lean_dec(v_mvarId_3421_);
v_a_3486_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3428_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3428_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3494_, lean_object* v___x_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3494_, v___x_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; 
v___x_3511_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3505_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3512_, 0, v_mvarId_3505_);
lean_closure_set(v___f_3512_, 1, v___x_3511_);
v___f_3513_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3513_, 0, v___f_3512_);
v___x_3514_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3505_, v___f_3513_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
return v_res_3521_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
