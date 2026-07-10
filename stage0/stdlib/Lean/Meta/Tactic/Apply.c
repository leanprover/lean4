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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
uint8_t lean_bool_not(uint8_t);
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
static lean_once_cell_t l_Lean_Meta_getExpectedNumArgsAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_getExpectedNumArgsAux___closed__1;
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
static lean_once_cell_t l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_irrel_heq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 105, 248, 247, 187, 48, 190, 226)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value;
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
static uint64_t _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1(void){
_start:
{
uint8_t v___x_104_; uint64_t v___x_105_; 
v___x_104_ = 1;
v___x_105_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; uint8_t v_foApprox_113_; uint8_t v_ctxApprox_114_; uint8_t v_quasiPatternApprox_115_; uint8_t v_constApprox_116_; uint8_t v_isDefEqStuckEx_117_; uint8_t v_unificationHints_118_; uint8_t v_proofIrrelevance_119_; uint8_t v_assignSyntheticOpaque_120_; uint8_t v_offsetCnstrs_121_; uint8_t v_etaStruct_122_; uint8_t v_univApprox_123_; uint8_t v_iota_124_; uint8_t v_beta_125_; uint8_t v_proj_126_; uint8_t v_zeta_127_; uint8_t v_zetaDelta_128_; uint8_t v_zetaUnused_129_; uint8_t v_zetaHave_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_159_; 
v___x_112_ = l_Lean_Meta_Context_config(v_a_107_);
v_foApprox_113_ = lean_ctor_get_uint8(v___x_112_, 0);
v_ctxApprox_114_ = lean_ctor_get_uint8(v___x_112_, 1);
v_quasiPatternApprox_115_ = lean_ctor_get_uint8(v___x_112_, 2);
v_constApprox_116_ = lean_ctor_get_uint8(v___x_112_, 3);
v_isDefEqStuckEx_117_ = lean_ctor_get_uint8(v___x_112_, 4);
v_unificationHints_118_ = lean_ctor_get_uint8(v___x_112_, 5);
v_proofIrrelevance_119_ = lean_ctor_get_uint8(v___x_112_, 6);
v_assignSyntheticOpaque_120_ = lean_ctor_get_uint8(v___x_112_, 7);
v_offsetCnstrs_121_ = lean_ctor_get_uint8(v___x_112_, 8);
v_etaStruct_122_ = lean_ctor_get_uint8(v___x_112_, 10);
v_univApprox_123_ = lean_ctor_get_uint8(v___x_112_, 11);
v_iota_124_ = lean_ctor_get_uint8(v___x_112_, 12);
v_beta_125_ = lean_ctor_get_uint8(v___x_112_, 13);
v_proj_126_ = lean_ctor_get_uint8(v___x_112_, 14);
v_zeta_127_ = lean_ctor_get_uint8(v___x_112_, 15);
v_zetaDelta_128_ = lean_ctor_get_uint8(v___x_112_, 16);
v_zetaUnused_129_ = lean_ctor_get_uint8(v___x_112_, 17);
v_zetaHave_130_ = lean_ctor_get_uint8(v___x_112_, 18);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_159_ == 0)
{
v___x_132_ = v___x_112_;
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
else
{
lean_dec(v___x_112_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v_trackZetaDelta_134_; lean_object* v_zetaDeltaSet_135_; lean_object* v_lctx_136_; lean_object* v_localInstances_137_; lean_object* v_defEqCtx_x3f_138_; lean_object* v_synthPendingDepth_139_; lean_object* v_canUnfold_x3f_140_; uint8_t v_univApprox_141_; uint8_t v_inTypeClassResolution_142_; uint8_t v_cacheInferType_143_; uint8_t v___x_144_; lean_object* v_config_146_; 
v_trackZetaDelta_134_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7);
v_zetaDeltaSet_135_ = lean_ctor_get(v_a_107_, 1);
v_lctx_136_ = lean_ctor_get(v_a_107_, 2);
v_localInstances_137_ = lean_ctor_get(v_a_107_, 3);
v_defEqCtx_x3f_138_ = lean_ctor_get(v_a_107_, 4);
v_synthPendingDepth_139_ = lean_ctor_get(v_a_107_, 5);
v_canUnfold_x3f_140_ = lean_ctor_get(v_a_107_, 6);
v_univApprox_141_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_142_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 2);
v_cacheInferType_143_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 3);
v___x_144_ = 1;
if (v_isShared_133_ == 0)
{
v_config_146_ = v___x_132_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 0, v_foApprox_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 1, v_ctxApprox_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 2, v_quasiPatternApprox_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 3, v_constApprox_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 4, v_isDefEqStuckEx_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 5, v_unificationHints_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 6, v_proofIrrelevance_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 7, v_assignSyntheticOpaque_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 8, v_offsetCnstrs_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 10, v_etaStruct_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 11, v_univApprox_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 12, v_iota_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 13, v_beta_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 14, v_proj_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 15, v_zeta_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 16, v_zetaDelta_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 17, v_zetaUnused_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 18, v_zetaHave_130_);
v_config_146_ = v_reuseFailAlloc_158_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; lean_object* v___f_150_; uint8_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_key_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_ctor_set_uint8(v_config_146_, 9, v___x_144_);
v___x_147_ = l_Lean_Meta_Context_configKey(v_a_107_);
v___x_148_ = 3ULL;
v___x_149_ = lean_uint64_shift_right(v___x_147_, v___x_148_);
v___f_150_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_151_ = 0;
v___x_152_ = lean_uint64_shift_left(v___x_149_, v___x_148_);
v___x_153_ = lean_uint64_once(&l_Lean_Meta_getExpectedNumArgsAux___closed__1, &l_Lean_Meta_getExpectedNumArgsAux___closed__1_once, _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1);
v_key_154_ = lean_uint64_lor(v___x_152_, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_155_, 0, v_config_146_);
lean_ctor_set_uint64(v___x_155_, sizeof(void*)*1, v_key_154_);
lean_inc(v_canUnfold_x3f_140_);
lean_inc(v_synthPendingDepth_139_);
lean_inc(v_defEqCtx_x3f_138_);
lean_inc_ref(v_localInstances_137_);
lean_inc_ref(v_lctx_136_);
lean_inc(v_zetaDeltaSet_135_);
v___x_156_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_zetaDeltaSet_135_);
lean_ctor_set(v___x_156_, 2, v_lctx_136_);
lean_ctor_set(v___x_156_, 3, v_localInstances_137_);
lean_ctor_set(v___x_156_, 4, v_defEqCtx_x3f_138_);
lean_ctor_set(v___x_156_, 5, v_synthPendingDepth_139_);
lean_ctor_set(v___x_156_, 6, v_canUnfold_x3f_140_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7, v_trackZetaDelta_134_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 1, v_univApprox_141_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 2, v_inTypeClassResolution_142_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 3, v_cacheInferType_143_);
v___x_157_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_106_, v___f_150_, v___x_151_, v___x_151_, v___x_156_, v_a_108_, v_a_109_, v_a_110_);
lean_dec_ref_known(v___x_156_, 7);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v___x_180_; 
v_fst_178_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_178_);
lean_dec(v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v_fst_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_173_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_173_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_getExpectedNumArgs(v_e_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v___y_214_, lean_object* v_targetType_215_, lean_object* v___y_216_, lean_object* v_term_x3f_217_, lean_object* v_conclusionType_x3f_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_214_, v_targetType_215_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_266_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_266_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_266_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_266_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_265_; 
v_fst_229_ = lean_ctor_get(v_a_225_, 0);
v_snd_230_ = lean_ctor_get(v_a_225_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_225_);
if (v_isSharedCheck_265_ == 0)
{
v___x_232_ = v_a_225_;
v_isShared_233_ = v_isSharedCheck_265_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v_a_225_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_265_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_253_; 
if (lean_obj_tag(v_conclusionType_x3f_218_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_253_ = v___x_263_;
goto v___jp_252_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_253_ = v___x_264_;
goto v___jp_252_;
}
v___jp_234_:
{
lean_object* v___x_239_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 7);
lean_ctor_set(v___x_232_, 1, v___y_237_);
lean_ctor_set(v___x_232_, 0, v___y_236_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___y_236_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___y_237_);
v___x_239_ = v_reuseFailAlloc_251_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_240_ = l_Lean_indentExpr(v_fst_229_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_indentExpr(v_snd_230_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_216_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_235_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_247_);
v___x_249_ = v___x_227_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
v___jp_252_:
{
lean_object* v___x_254_; 
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
v___x_254_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_229_, v_snd_230_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_253_);
v___x_257_ = l_Lean_stringToMessageData(v___y_253_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
if (lean_obj_tag(v_term_x3f_217_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_235_ = v_a_255_;
v___y_236_ = v___x_260_;
v___y_237_ = v___x_261_;
goto v___jp_234_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_term_x3f_217_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_term_x3f_217_, 1);
v___y_235_ = v_a_255_;
v___y_236_ = v___x_260_;
v___y_237_ = v_val_262_;
goto v___jp_234_;
}
}
else
{
lean_del_object(v___x_232_);
lean_dec(v_snd_230_);
lean_dec(v_fst_229_);
lean_del_object(v___x_227_);
lean_dec(v_term_x3f_217_);
lean_dec_ref(v___y_216_);
return v___x_254_;
}
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_term_x3f_217_);
lean_dec_ref(v___y_216_);
v_a_267_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_224_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_224_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v___y_275_, lean_object* v_targetType_276_, lean_object* v___y_277_, lean_object* v_term_x3f_278_, lean_object* v_conclusionType_x3f_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v___y_275_, v_targetType_276_, v___y_277_, v_term_x3f_278_, v_conclusionType_x3f_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_conclusionType_x3f_279_);
return v_res_285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_298_, lean_object* v_eType_299_, lean_object* v_conclusionType_x3f_300_, lean_object* v_targetType_301_, lean_object* v_term_x3f_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_331_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
if (lean_obj_tag(v_conclusionType_x3f_300_) == 0)
{
lean_inc_ref(v_eType_299_);
v___y_331_ = v_eType_299_;
goto v___jp_330_;
}
else
{
lean_object* v_val_336_; 
v_val_336_ = lean_ctor_get(v_conclusionType_x3f_300_, 0);
lean_inc(v_val_336_);
v___y_331_ = v_val_336_;
goto v___jp_330_;
}
v___jp_309_:
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc_ref(v_targetType_301_);
v___f_312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_312_, 0, v___y_310_);
lean_closure_set(v___f_312_, 1, v_targetType_301_);
lean_closure_set(v___f_312_, 2, v___y_311_);
lean_closure_set(v___f_312_, 3, v_term_x3f_302_);
lean_closure_set(v___f_312_, 4, v_conclusionType_x3f_300_);
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_mk_empty_array_with_capacity(v___x_313_);
v___x_315_ = lean_array_push(v___x_314_, v_eType_299_);
v___x_316_ = lean_array_push(v___x_315_, v_targetType_301_);
v___x_317_ = l_Lean_MessageData_ofLazyM(v___f_312_, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = l_Lean_Meta_throwTacticEx___redArg(v___x_308_, v_mvarId_298_, v___x_318_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_319_;
}
v___jp_320_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc_ref(v___y_322_);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_322_);
lean_ctor_set(v___x_324_, 1, v___y_323_);
v___x_325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_inc_ref(v_eType_299_);
v___x_327_ = l_Lean_indentExpr(v_eType_299_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_MessageData_note(v___x_328_);
v___y_310_ = v___y_321_;
v___y_311_ = v___x_329_;
goto v___jp_309_;
}
v___jp_330_:
{
if (lean_obj_tag(v_conclusionType_x3f_300_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
v___y_310_ = v___y_331_;
v___y_311_ = v___x_332_;
goto v___jp_309_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
if (lean_obj_tag(v_term_x3f_302_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_321_ = v___y_331_;
v___y_322_ = v___x_333_;
v___y_323_ = v___x_334_;
goto v___jp_320_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v_term_x3f_302_, 0);
lean_inc(v_val_335_);
v___y_321_ = v___y_331_;
v___y_322_ = v___x_333_;
v___y_323_ = v_val_335_;
goto v___jp_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_337_, lean_object* v_eType_338_, lean_object* v_conclusionType_x3f_339_, lean_object* v_targetType_340_, lean_object* v_term_x3f_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_337_, v_eType_338_, v_conclusionType_x3f_339_, v_targetType_340_, v_term_x3f_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_348_, lean_object* v_mvarId_349_, lean_object* v_eType_350_, lean_object* v_conclusionType_x3f_351_, lean_object* v_targetType_352_, lean_object* v_term_x3f_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_349_, v_eType_350_, v_conclusionType_x3f_351_, v_targetType_352_, v_term_x3f_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_360_, lean_object* v_mvarId_361_, lean_object* v_eType_362_, lean_object* v_conclusionType_x3f_363_, lean_object* v_targetType_364_, lean_object* v_term_x3f_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_360_, v_mvarId_361_, v_eType_362_, v_conclusionType_x3f_363_, v_targetType_364_, v_term_x3f_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_372_, lean_object* v_snd_373_, lean_object* v_fst_374_, lean_object* v_____r_375_, uint8_t v_progressAfterEx_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_a_372_);
v___x_383_ = lean_box(v_progressAfterEx_376_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_snd_373_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_fst_374_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_388_, lean_object* v_snd_389_, lean_object* v_fst_390_, lean_object* v_____r_391_, lean_object* v_progressAfterEx_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
uint8_t v_progressAfterEx_boxed_398_; lean_object* v_res_399_; 
v_progressAfterEx_boxed_398_ = lean_unbox(v_progressAfterEx_392_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_388_, v_snd_389_, v_fst_390_, v_____r_391_, v_progressAfterEx_boxed_398_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_399_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_404_ = l_Lean_MessageData_ofFormat(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_407_, lean_object* v_tacticName_408_, lean_object* v_mvarId_409_, lean_object* v_as_410_, size_t v_sz_411_, size_t v_i_412_, lean_object* v_b_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_a_420_; lean_object* v_fst_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_412_, v_sz_411_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_413_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; 
v_a_432_ = lean_array_uget_borrowed(v_as_410_, v_i_412_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
lean_inc(v_a_432_);
v___x_433_ = lean_infer_type(v_a_432_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_snd_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_528_; 
v_snd_434_ = lean_ctor_get(v_b_413_, 1);
lean_inc(v_snd_434_);
v_a_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_528_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_528_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_528_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_fst_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___y_443_; uint8_t v___y_444_; lean_object* v_a_451_; lean_object* v___y_455_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_fst_439_ = lean_ctor_get(v_b_413_, 0);
lean_inc(v_fst_439_);
lean_dec_ref(v_b_413_);
v_fst_440_ = lean_ctor_get(v_snd_434_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v_snd_434_, 1);
lean_inc(v_snd_441_);
lean_dec(v_snd_434_);
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_Meta_synthInstance(v_a_435_, v___x_516_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_array_get_size(v_snd_441_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
lean_inc(v_snd_441_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_518_, v_snd_441_, v_fst_439_, v___x_522_, v___x_430_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_455_ = v___x_523_;
goto v___jp_454_;
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_unbox(v_fst_440_);
lean_inc(v_snd_441_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_518_, v_snd_441_, v_fst_439_, v___x_524_, v___x_525_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_455_ = v___x_526_;
goto v___jp_454_;
}
}
else
{
lean_object* v_a_527_; 
lean_dec(v_fst_439_);
v_a_527_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_517_, 1);
v_a_451_ = v_a_527_;
goto v___jp_450_;
}
v___jp_442_:
{
if (v___y_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_del_object(v___x_437_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___y_443_);
lean_inc(v_a_432_);
v___x_446_ = lean_array_push(v_snd_441_, v_a_432_);
v_fst_425_ = v___x_445_;
v_fst_426_ = v_fst_440_;
v_snd_427_ = v___x_446_;
goto v___jp_424_;
}
else
{
lean_object* v___x_448_; 
lean_dec(v_snd_441_);
lean_dec(v_fst_440_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
lean_ctor_set(v___x_437_, 0, v___y_443_);
v___x_448_ = v___x_437_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___y_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
v___jp_450_:
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Exception_isInterrupt(v_a_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
lean_inc_ref(v_a_451_);
v___x_453_ = l_Lean_Exception_isRuntime(v_a_451_);
v___y_443_ = v_a_451_;
v___y_444_ = v___x_453_;
goto v___jp_442_;
}
else
{
v___y_443_ = v_a_451_;
v___y_444_ = v___x_452_;
goto v___jp_442_;
}
}
v___jp_454_:
{
if (lean_obj_tag(v___y_455_) == 0)
{
lean_object* v_a_456_; lean_object* v_snd_457_; lean_object* v_snd_458_; lean_object* v_fst_459_; 
lean_dec(v_snd_441_);
lean_dec(v_fst_440_);
lean_del_object(v___x_437_);
v_a_456_ = lean_ctor_get(v___y_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___y_455_, 1);
v_snd_457_ = lean_ctor_get(v_a_456_, 1);
lean_inc(v_snd_457_);
v_snd_458_ = lean_ctor_get(v_snd_457_, 1);
lean_inc(v_snd_458_);
v_fst_459_ = lean_ctor_get(v_a_456_, 0);
lean_inc(v_fst_459_);
lean_dec(v_a_456_);
if (lean_obj_tag(v_fst_459_) == 1)
{
lean_object* v_fst_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_510_; 
v_fst_460_ = lean_ctor_get(v_snd_457_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_snd_457_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_snd_457_, 1);
lean_dec(v_unused_511_);
v___x_462_ = v_snd_457_;
v_isShared_463_ = v_isSharedCheck_510_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fst_460_);
lean_dec(v_snd_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_510_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_509_; 
v_fst_464_ = lean_ctor_get(v_snd_458_, 0);
v_snd_465_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_509_ == 0)
{
v___x_467_ = v_snd_458_;
v_isShared_468_ = v_isSharedCheck_509_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snd_465_);
lean_inc(v_fst_464_);
lean_dec(v_snd_458_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_509_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_val_469_; lean_object* v___x_470_; 
v_val_469_ = lean_ctor_get(v_fst_459_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v_fst_459_, 1);
lean_inc(v_a_432_);
v___x_470_ = l_Lean_Meta_isExprDefEq(v_a_432_, v_val_469_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_unbox(v_a_471_);
lean_dec(v_a_471_);
if (v___x_472_ == 0)
{
if (v_allowSynthFailures_407_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_409_);
lean_inc(v_tacticName_408_);
v___x_474_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_408_, v_mvarId_409_, v___x_473_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref_known(v___x_474_, 1);
if (v_isShared_468_ == 0)
{
v___x_476_ = v___x_467_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_465_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_476_);
v___x_478_ = v___x_462_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
v_a_420_ = v___x_478_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_467_);
lean_dec(v_snd_465_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_481_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_474_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_474_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v___x_490_; 
if (v_isShared_468_ == 0)
{
v___x_490_ = v___x_467_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_465_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_490_);
v___x_492_ = v___x_462_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v_a_420_ = v___x_492_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v___x_496_; 
if (v_isShared_468_ == 0)
{
v___x_496_ = v___x_467_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_snd_465_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_496_);
v___x_498_ = v___x_462_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v_a_420_ = v___x_498_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_467_);
lean_dec(v_snd_465_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_501_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_470_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_470_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_object* v_fst_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; 
lean_dec(v_fst_459_);
v_fst_512_ = lean_ctor_get(v_snd_457_, 0);
lean_inc(v_fst_512_);
lean_dec(v_snd_457_);
v_fst_513_ = lean_ctor_get(v_snd_458_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_snd_458_, 1);
lean_inc(v_snd_514_);
lean_dec(v_snd_458_);
v_fst_425_ = v_fst_512_;
v_fst_426_ = v_fst_513_;
v_snd_427_ = v_snd_514_;
goto v___jp_424_;
}
}
else
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___y_455_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___y_455_, 1);
v_a_451_ = v_a_515_;
goto v___jp_450_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_b_413_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_529_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_433_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_433_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_419_:
{
size_t v___x_421_; size_t v___x_422_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_412_, v___x_421_);
v_i_412_ = v___x_422_;
v_b_413_ = v_a_420_;
goto _start;
}
v___jp_424_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_fst_426_);
lean_ctor_set(v___x_428_, 1, v_snd_427_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_fst_425_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v_a_420_ = v___x_429_;
goto v___jp_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_537_, lean_object* v_tacticName_538_, lean_object* v_mvarId_539_, lean_object* v_as_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_allowSynthFailures_boxed_549_; size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_allowSynthFailures_boxed_549_ = lean_unbox(v_allowSynthFailures_537_);
v_sz_boxed_550_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_551_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_549_, v_tacticName_538_, v_mvarId_539_, v_as_540_, v_sz_boxed_550_, v_i_boxed_551_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_as_540_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_562_, lean_object* v_mvarId_563_, uint8_t v_allowSynthFailures_564_, lean_object* v_mvars_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_postponed_571_; lean_object* v___x_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_postponed_571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_573_ = lean_array_size(v_mvars_565_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_564_, v_tacticName_562_, v_mvarId_563_, v_mvars_565_, v_sz_573_, v___x_574_, v___x_572_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_598_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_598_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_fst_580_; 
v_fst_580_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_fst_580_);
if (lean_obj_tag(v_fst_580_) == 1)
{
lean_object* v_snd_581_; lean_object* v_fst_582_; uint8_t v___x_583_; 
v_snd_581_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_snd_581_);
lean_dec(v_a_576_);
v_fst_582_ = lean_ctor_get(v_snd_581_, 0);
v___x_583_ = lean_unbox(v_fst_582_);
if (v___x_583_ == 0)
{
lean_dec(v_snd_581_);
if (v_allowSynthFailures_564_ == 0)
{
lean_object* v_val_584_; lean_object* v___x_586_; 
v_val_584_ = lean_ctor_get(v_fst_580_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v_fst_580_, 1);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 1);
lean_ctor_set(v___x_578_, 0, v_val_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_val_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v___x_589_; 
lean_dec_ref_known(v_fst_580_, 1);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_postponed_571_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_postponed_571_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_snd_591_; lean_object* v___x_593_; 
lean_dec_ref_known(v_fst_580_, 1);
v_snd_591_ = lean_ctor_get(v_snd_581_, 1);
lean_inc(v_snd_591_);
lean_dec(v_snd_581_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_snd_591_);
v___x_593_ = v___x_578_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_snd_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v___x_596_; 
lean_dec(v_fst_580_);
lean_dec(v_a_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_postponed_571_);
v___x_596_ = v___x_578_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_postponed_571_);
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
v_a_599_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_575_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_575_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_607_, lean_object* v_mvarId_608_, lean_object* v_allowSynthFailures_609_, lean_object* v_mvars_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
uint8_t v_allowSynthFailures_boxed_616_; lean_object* v_res_617_; 
v_allowSynthFailures_boxed_616_ = lean_unbox(v_allowSynthFailures_609_);
v_res_617_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_607_, v_mvarId_608_, v_allowSynthFailures_boxed_616_, v_mvars_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_mvars_610_);
return v_res_617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_618_, lean_object* v_i_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_keys_618_);
v___x_622_ = lean_nat_dec_lt(v_i_619_, v___x_621_);
if (v___x_622_ == 0)
{
lean_dec(v_i_619_);
return v___x_622_;
}
else
{
lean_object* v_k_x27_623_; uint8_t v___x_624_; 
v_k_x27_623_ = lean_array_fget_borrowed(v_keys_618_, v_i_619_);
v___x_624_ = l_Lean_instBEqMVarId_beq(v_k_620_, v_k_x27_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_619_, v___x_625_);
lean_dec(v_i_619_);
v_i_619_ = v___x_626_;
goto _start;
}
else
{
lean_dec(v_i_619_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_628_, lean_object* v_i_629_, lean_object* v_k_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_628_, v_i_629_, v_k_630_);
lean_dec(v_k_630_);
lean_dec_ref(v_keys_628_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v_es_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v_j_640_; lean_object* v___x_641_; 
v_es_636_ = lean_ctor_get(v_x_633_, 0);
v___x_637_ = lean_box(2);
v___x_638_ = ((size_t)31ULL);
v___x_639_ = lean_usize_land(v_x_634_, v___x_638_);
v_j_640_ = lean_usize_to_nat(v___x_639_);
v___x_641_ = lean_array_get_borrowed(v___x_637_, v_es_636_, v_j_640_);
lean_dec(v_j_640_);
switch(lean_obj_tag(v___x_641_))
{
case 0:
{
lean_object* v_key_642_; uint8_t v___x_643_; 
v_key_642_ = lean_ctor_get(v___x_641_, 0);
v___x_643_ = l_Lean_instBEqMVarId_beq(v_x_635_, v_key_642_);
return v___x_643_;
}
case 1:
{
lean_object* v_node_644_; size_t v___x_645_; size_t v___x_646_; 
v_node_644_ = lean_ctor_get(v___x_641_, 0);
v___x_645_ = ((size_t)5ULL);
v___x_646_ = lean_usize_shift_right(v_x_634_, v___x_645_);
v_x_633_ = v_node_644_;
v_x_634_ = v___x_646_;
goto _start;
}
default: 
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
}
else
{
lean_object* v_ks_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_ks_649_ = lean_ctor_get(v_x_633_, 0);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_649_, v___x_650_, v_x_635_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_2964__boxed_655_; uint8_t v_res_656_; lean_object* v_r_657_; 
v_x_2964__boxed_655_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_656_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_652_, v_x_2964__boxed_655_, v_x_654_);
lean_dec(v_x_654_);
lean_dec_ref(v_x_652_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
uint64_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_instHashableMVarId_hash(v_x_659_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_658_, v___x_661_, v_x_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_663_, v_x_664_);
lean_dec(v_x_664_);
lean_dec_ref(v_x_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_mctx_671_; lean_object* v_eAssignment_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_mctx_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_mctx_671_);
lean_dec(v___x_670_);
v_eAssignment_672_ = lean_ctor_get(v_mctx_671_, 8);
lean_inc_ref(v_eAssignment_672_);
lean_dec_ref(v_mctx_671_);
v___x_673_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_672_, v_mvarId_667_);
lean_dec_ref(v_eAssignment_672_);
v___x_674_ = lean_box(v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec(v_mvarId_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_680_, lean_object* v_as_681_, size_t v_sz_682_, size_t v_i_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_a_691_; uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_lt(v_i_683_, v_sz_682_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_b_684_);
return v___x_696_;
}
else
{
lean_object* v_snd_697_; lean_object* v_fst_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_748_; 
v_snd_697_ = lean_ctor_get(v_b_684_, 1);
v_fst_698_ = lean_ctor_get(v_b_684_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_b_684_);
if (v_isSharedCheck_748_ == 0)
{
v___x_700_ = v_b_684_;
v_isShared_701_ = v_isSharedCheck_748_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_snd_697_);
lean_inc(v_fst_698_);
lean_dec(v_b_684_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_748_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_array_702_; lean_object* v_start_703_; lean_object* v_stop_704_; uint8_t v___x_705_; 
v_array_702_ = lean_ctor_get(v_snd_697_, 0);
v_start_703_ = lean_ctor_get(v_snd_697_, 1);
v_stop_704_ = lean_ctor_get(v_snd_697_, 2);
v___x_705_ = lean_nat_dec_lt(v_start_703_, v_stop_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_707_; 
if (v_isShared_701_ == 0)
{
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_snd_697_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_744_; 
lean_inc(v_stop_704_);
lean_inc(v_start_703_);
lean_inc_ref(v_array_702_);
v_isSharedCheck_744_ = !lean_is_exclusive(v_snd_697_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_745_ = lean_ctor_get(v_snd_697_, 2);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_snd_697_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_snd_697_, 0);
lean_dec(v_unused_747_);
v___x_711_ = v_snd_697_;
v_isShared_712_ = v_isSharedCheck_744_;
goto v_resetjp_710_;
}
else
{
lean_dec(v_snd_697_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_744_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_713_ = lean_array_fget(v_array_702_, v_start_703_);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_add(v_start_703_, v___x_714_);
lean_dec(v_start_703_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v___x_715_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_array_702_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_stop_704_);
v___x_717_ = v_reuseFailAlloc_743_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_unbox(v___x_713_);
lean_dec(v___x_713_);
v___x_719_ = l_Lean_BinderInfo_isInstImplicit(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_721_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_717_);
v___x_721_ = v___x_700_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_717_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_a_691_ = v___x_721_;
goto v___jp_690_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_723_ = lean_array_uget_borrowed(v_as_681_, v_i_683_);
v___x_724_ = l_Lean_Expr_mvarId_x21(v_a_723_);
v___x_725_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_724_, v___y_686_);
lean_dec(v___x_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
if (v_synthAssignedInstances_680_ == 0)
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
v___x_733_ = lean_bool_not(v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_del_object(v___x_700_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_fst_698_);
lean_ctor_set(v___x_734_, 1, v___x_717_);
v_a_691_ = v___x_734_;
goto v___jp_690_;
}
else
{
goto v___jp_727_;
}
}
else
{
lean_dec(v_a_726_);
goto v___jp_727_;
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc(v_a_723_);
v___x_728_ = lean_array_push(v_fst_698_, v_a_723_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_717_);
lean_ctor_set(v___x_700_, 0, v___x_728_);
v___x_730_ = v___x_700_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_717_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_691_ = v___x_730_;
goto v___jp_690_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___x_717_);
lean_del_object(v___x_700_);
lean_dec(v_fst_698_);
v_a_735_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_725_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_725_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
}
}
v___jp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_683_, v___x_692_);
v_i_683_ = v___x_693_;
v_b_684_ = v_a_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_749_, lean_object* v_as_750_, lean_object* v_sz_751_, lean_object* v_i_752_, lean_object* v_b_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_759_; size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_synthAssignedInstances_boxed_759_ = lean_unbox(v_synthAssignedInstances_749_);
v_sz_boxed_760_ = lean_unbox_usize(v_sz_751_);
lean_dec(v_sz_751_);
v_i_boxed_761_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_759_, v_as_750_, v_sz_boxed_760_, v_i_boxed_761_, v_b_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v_as_750_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_763_, lean_object* v_mvarId_764_, uint8_t v_allowSynthFailures_765_, lean_object* v_a_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_772_ = lean_array_get_size(v_a_766_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
v___x_775_ = lean_bool_not(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v_mvarId_764_);
lean_dec(v_tacticName_763_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_a_766_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; 
lean_inc(v_mvarId_764_);
lean_inc(v_tacticName_763_);
v___x_777_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_763_, v_mvarId_764_, v_allowSynthFailures_765_, v_a_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec_ref(v_a_766_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v_a_766_ = v_a_778_;
goto _start;
}
else
{
lean_dec(v_mvarId_764_);
lean_dec(v_tacticName_763_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_780_, lean_object* v_mvarId_781_, lean_object* v_allowSynthFailures_782_, lean_object* v_a_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_allowSynthFailures_boxed_789_; lean_object* v_res_790_; 
v_allowSynthFailures_boxed_789_ = lean_unbox(v_allowSynthFailures_782_);
v_res_790_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_780_, v_mvarId_781_, v_allowSynthFailures_boxed_789_, v_a_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_791_, lean_object* v_mvarId_792_, lean_object* v_mvarsNew_793_, lean_object* v_binderInfos_794_, uint8_t v_synthAssignedInstances_795_, uint8_t v_allowSynthFailures_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_todo_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v_todo_803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_804_ = lean_array_get_size(v_binderInfos_794_);
v___x_805_ = l_Array_toSubarray___redArg(v_binderInfos_794_, v___x_802_, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_todo_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v_sz_807_ = lean_array_size(v_mvarsNew_793_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_795_, v_mvarsNew_793_, v_sz_807_, v___x_808_, v___x_806_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_fst_811_; lean_object* v___x_812_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_fst_811_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_fst_811_);
lean_dec(v_a_810_);
v___x_812_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_791_, v_mvarId_792_, v_allowSynthFailures_796_, v_fst_811_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_820_; 
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_821_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_box(0);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_812_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_812_);
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
lean_dec(v_mvarId_792_);
lean_dec(v_tacticName_791_);
v_a_830_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_809_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_809_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_838_, lean_object* v_mvarId_839_, lean_object* v_mvarsNew_840_, lean_object* v_binderInfos_841_, lean_object* v_synthAssignedInstances_842_, lean_object* v_allowSynthFailures_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_849_; uint8_t v_allowSynthFailures_boxed_850_; lean_object* v_res_851_; 
v_synthAssignedInstances_boxed_849_ = lean_unbox(v_synthAssignedInstances_842_);
v_allowSynthFailures_boxed_850_ = lean_unbox(v_allowSynthFailures_843_);
v_res_851_ = l_Lean_Meta_synthAppInstances(v_tacticName_838_, v_mvarId_839_, v_mvarsNew_840_, v_binderInfos_841_, v_synthAssignedInstances_boxed_849_, v_allowSynthFailures_boxed_850_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec_ref(v_mvarsNew_840_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_852_, v___y_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v_mvarId_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_866_, lean_object* v_mvarId_867_, uint8_t v_allowSynthFailures_868_, lean_object* v_inst_869_, lean_object* v_a_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_866_, v_mvarId_867_, v_allowSynthFailures_868_, v_a_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_877_, lean_object* v_mvarId_878_, lean_object* v_allowSynthFailures_879_, lean_object* v_inst_880_, lean_object* v_a_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v_allowSynthFailures_boxed_887_; lean_object* v_res_888_; 
v_allowSynthFailures_boxed_887_ = lean_unbox(v_allowSynthFailures_879_);
v_res_888_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_877_, v_mvarId_878_, v_allowSynthFailures_boxed_887_, v_inst_880_, v_a_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_888_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_890_, v_x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_893_, v_x_894_, v_x_895_);
lean_dec(v_x_895_);
lean_dec_ref(v_x_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, size_t v_x_900_, lean_object* v_x_901_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_899_, v_x_900_, v_x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
size_t v_x_3300__boxed_907_; uint8_t v_res_908_; lean_object* v_r_909_; 
v_x_3300__boxed_907_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_res_908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_903_, v_x_904_, v_x_3300__boxed_907_, v_x_906_);
lean_dec(v_x_906_);
lean_dec_ref(v_x_904_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_heq_913_, lean_object* v_i_914_, lean_object* v_k_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_911_, v_i_914_, v_k_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_heq_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_917_, v_keys_918_, v_vals_919_, v_heq_920_, v_i_921_, v_k_922_);
lean_dec(v_k_922_);
lean_dec_ref(v_vals_919_);
lean_dec_ref(v_keys_918_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_925_, lean_object* v_binderInfos_926_, lean_object* v_a_927_, lean_object* v_n_928_, lean_object* v_i_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_zero_935_; uint8_t v_isZero_936_; 
v_zero_935_ = lean_unsigned_to_nat(0u);
v_isZero_936_ = lean_nat_dec_eq(v_i_929_, v_zero_935_);
if (v_isZero_936_ == 1)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_i_929_);
lean_dec(v_a_927_);
v___x_937_ = lean_box(0);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
else
{
lean_object* v_one_939_; lean_object* v_n_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_a_946_; uint8_t v___x_947_; 
v_one_939_ = lean_unsigned_to_nat(1u);
v_n_940_ = lean_nat_sub(v_i_929_, v_one_939_);
lean_dec(v_i_929_);
v___x_941_ = lean_nat_sub(v_n_928_, v_n_940_);
v___x_942_ = lean_nat_sub(v___x_941_, v_one_939_);
lean_dec(v___x_941_);
v___x_943_ = lean_array_fget_borrowed(v_newMVars_925_, v___x_942_);
v___x_944_ = l_Lean_Expr_mvarId_x21(v___x_943_);
v___x_945_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_944_, v___y_931_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = lean_unbox(v_a_946_);
lean_dec(v_a_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; 
v___x_948_ = 0;
v___x_949_ = lean_box(v___x_948_);
v___x_950_ = lean_array_get(v___x_949_, v_binderInfos_926_, v___x_942_);
lean_dec(v___x_942_);
lean_dec(v___x_949_);
v___x_951_ = lean_unbox(v___x_950_);
lean_dec(v___x_950_);
v___x_952_ = l_Lean_BinderInfo_isInstImplicit(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_inc(v___x_944_);
v___x_953_ = l_Lean_MVarId_getTag(v___x_944_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
lean_inc(v_a_927_);
v___x_955_ = l_Lean_Meta_appendTag(v_a_927_, v_a_954_);
lean_dec(v_a_954_);
v___x_956_ = l_Lean_MVarId_setTag___redArg(v___x_944_, v___x_955_, v___y_931_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref_known(v___x_956_, 1);
v_i_929_ = v_n_940_;
goto _start;
}
else
{
lean_dec(v_n_940_);
lean_dec(v_a_927_);
return v___x_956_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v___x_944_);
lean_dec(v_n_940_);
lean_dec(v_a_927_);
v_a_958_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_953_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_953_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_dec(v___x_944_);
v_i_929_ = v_n_940_;
goto _start;
}
}
else
{
lean_dec(v___x_944_);
lean_dec(v___x_942_);
v_i_929_ = v_n_940_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_968_, lean_object* v_binderInfos_969_, lean_object* v_a_970_, lean_object* v_n_971_, lean_object* v_i_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_968_, v_binderInfos_969_, v_a_970_, v_n_971_, v_i_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v_n_971_);
lean_dec_ref(v_binderInfos_969_);
lean_dec_ref(v_newMVars_968_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_979_, lean_object* v_newMVars_980_, lean_object* v_binderInfos_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_MVarId_getTag(v_mvarId_979_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1006_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1006_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1006_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_992_ = lean_array_get_size(v_newMVars_980_);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_dec_eq(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_Name_isAnonymous(v_a_988_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_del_object(v___x_990_);
v___x_996_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_980_, v_binderInfos_981_, v_a_988_, v___x_992_, v___x_992_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_a_988_);
v___x_997_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_997_);
v___x_999_ = v___x_990_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_del_object(v___x_990_);
v___x_1001_ = l_Lean_instInhabitedExpr;
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_borrowed(v___x_1001_, v_newMVars_980_, v___x_1002_);
v___x_1004_ = l_Lean_Expr_mvarId_x21(v___x_1003_);
v___x_1005_ = l_Lean_MVarId_setTag___redArg(v___x_1004_, v_a_988_, v_a_983_);
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_987_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_987_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1015_, lean_object* v_newMVars_1016_, lean_object* v_binderInfos_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_appendParentTag(v_mvarId_1015_, v_newMVars_1016_, v_binderInfos_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec_ref(v_binderInfos_1017_);
lean_dec_ref(v_newMVars_1016_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1024_, lean_object* v_binderInfos_1025_, lean_object* v_a_1026_, lean_object* v_n_1027_, lean_object* v_i_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1024_, v_binderInfos_1025_, v_a_1026_, v_n_1027_, v_i_1028_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1036_, lean_object* v_binderInfos_1037_, lean_object* v_a_1038_, lean_object* v_n_1039_, lean_object* v_i_1040_, lean_object* v_a_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1036_, v_binderInfos_1037_, v_a_1038_, v_n_1039_, v_i_1040_, v_a_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v_n_1039_);
lean_dec_ref(v_binderInfos_1037_);
lean_dec_ref(v_newMVars_1036_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1048_, lean_object* v_mvarId_1049_, lean_object* v_newMVars_1050_, lean_object* v_binderInfos_1051_, uint8_t v_synthAssignedInstances_1052_, uint8_t v_allowSynthFailures_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_synthAppInstances(v_tacticName_1048_, v_mvarId_1049_, v_newMVars_1050_, v_binderInfos_1051_, v_synthAssignedInstances_1052_, v_allowSynthFailures_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1060_, lean_object* v_mvarId_1061_, lean_object* v_newMVars_1062_, lean_object* v_binderInfos_1063_, lean_object* v_synthAssignedInstances_1064_, lean_object* v_allowSynthFailures_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1071_; uint8_t v_allowSynthFailures_boxed_1072_; lean_object* v_res_1073_; 
v_synthAssignedInstances_boxed_1071_ = lean_unbox(v_synthAssignedInstances_1064_);
v_allowSynthFailures_boxed_1072_ = lean_unbox(v_allowSynthFailures_1065_);
v_res_1073_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1060_, v_mvarId_1061_, v_newMVars_1062_, v_binderInfos_1063_, v_synthAssignedInstances_boxed_1071_, v_allowSynthFailures_boxed_1072_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec_ref(v_newMVars_1062_);
return v_res_1073_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1074_, lean_object* v_mvarId_1075_){
_start:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = l_Lean_Expr_mvarId_x21(v_mvar_1074_);
v___x_1077_ = l_Lean_instBEqMVarId_beq(v_mvarId_1075_, v___x_1076_);
lean_dec(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1078_, lean_object* v_mvarId_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1078_, v_mvarId_1079_);
lean_dec(v_mvarId_1079_);
lean_dec_ref(v_mvar_1078_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1082_, lean_object* v_as_1083_, size_t v_i_1084_, size_t v_stop_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_usize_dec_eq(v_i_1084_, v_stop_1085_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; uint8_t v_a_1094_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1092_ = 1;
v___x_1100_ = lean_array_uget_borrowed(v_as_1083_, v_i_1084_);
v___x_1101_ = lean_expr_eqv(v_mvar_1082_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___x_1100_);
v___x_1102_ = lean_infer_type(v___x_1100_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1114_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_mvar_1082_);
v___f_1107_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1107_, 0, v_mvar_1082_);
v___x_1108_ = lean_box(0);
v___x_1109_ = l_Lean_FindMVar_main(v___f_1107_, v_a_1103_, v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_del_object(v___x_1105_);
v_a_1094_ = v___x_1101_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1109_, 1);
lean_dec_ref(v_mvar_1082_);
v___x_1110_ = lean_box(v___x_1092_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1110_);
v___x_1112_ = v___x_1105_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_mvar_1082_);
v_a_1115_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1102_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1102_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
v_a_1094_ = v___x_1091_;
goto v___jp_1093_;
}
v___jp_1093_:
{
if (v_a_1094_ == 0)
{
size_t v___x_1095_; size_t v___x_1096_; 
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_add(v_i_1084_, v___x_1095_);
v_i_1084_ = v___x_1096_;
goto _start;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_mvar_1082_);
v___x_1098_ = lean_box(v___x_1092_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
else
{
uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v_mvar_1082_);
v___x_1123_ = 0;
v___x_1124_ = lean_box(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1126_, lean_object* v_as_1127_, lean_object* v_i_1128_, lean_object* v_stop_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
size_t v_i_boxed_1135_; size_t v_stop_boxed_1136_; lean_object* v_res_1137_; 
v_i_boxed_1135_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_stop_boxed_1136_ = lean_unbox_usize(v_stop_1129_);
lean_dec(v_stop_1129_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1126_, v_as_1127_, v_i_boxed_1135_, v_stop_boxed_1136_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_as_1127_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1138_, lean_object* v_otherMVars_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_array_get_size(v_otherMVars_1139_);
v___x_1147_ = lean_nat_dec_lt(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_mvar_1138_);
v___x_1148_ = lean_box(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
else
{
if (v___x_1147_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_mvar_1138_);
v___x_1150_ = lean_box(v___x_1147_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
else
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1146_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1138_, v_otherMVars_1139_, v___x_1152_, v___x_1153_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1155_, lean_object* v_otherMVars_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1155_, v_otherMVars_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec_ref(v_otherMVars_1156_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1163_, lean_object* v_as_1164_, size_t v_i_1165_, size_t v_stop_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_eq(v_i_1165_, v_stop_1166_);
if (v___x_1173_ == 0)
{
lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1205_; 
v_fst_1174_ = lean_ctor_get(v_b_1167_, 0);
v_snd_1175_ = lean_ctor_get(v_b_1167_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_b_1167_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1177_ = v_b_1167_;
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1175_);
lean_inc(v_fst_1174_);
lean_dec(v_b_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v_currMVarId_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_array_uget_borrowed(v_as_1164_, v_i_1165_);
v_currMVarId_1180_ = l_Lean_Expr_mvarId_x21(v___x_1179_);
lean_inc(v___x_1179_);
v___x_1181_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1179_, v_mvars_1163_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_a_1184_; uint8_t v___x_1188_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1188_ = lean_unbox(v_a_1182_);
lean_dec(v_a_1182_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_array_push(v_fst_1174_, v_currMVarId_1180_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1189_);
v___x_1191_ = v___x_1177_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_snd_1175_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_a_1184_ = v___x_1191_;
goto v___jp_1183_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_array_push(v_snd_1175_, v_currMVarId_1180_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1193_);
v___x_1195_ = v___x_1177_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
v_a_1184_ = v___x_1195_;
goto v___jp_1183_;
}
}
v___jp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1165_, v___x_1185_);
v_i_1165_ = v___x_1186_;
v_b_1167_ = v_a_1184_;
goto _start;
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_currMVarId_1180_);
lean_del_object(v___x_1177_);
lean_dec(v_snd_1175_);
lean_dec(v_fst_1174_);
v_a_1197_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1181_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1181_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
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
else
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_b_1167_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1207_, lean_object* v_as_1208_, lean_object* v_i_1209_, lean_object* v_stop_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
size_t v_i_boxed_1217_; size_t v_stop_boxed_1218_; lean_object* v_res_1219_; 
v_i_boxed_1217_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_stop_boxed_1218_ = lean_unbox_usize(v_stop_1210_);
lean_dec(v_stop_1210_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1207_, v_as_1208_, v_i_boxed_1217_, v_stop_boxed_1218_, v_b_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_as_1208_);
lean_dec_ref(v_mvars_1207_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1232_ = lean_array_get_size(v_mvars_1224_);
v___x_1233_ = lean_nat_dec_lt(v___x_1230_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1231_);
return v___x_1234_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_le(v___x_1232_, v___x_1232_);
if (v___x_1235_ == 0)
{
if (v___x_1233_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1231_);
return v___x_1236_;
}
else
{
size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = lean_usize_of_nat(v___x_1232_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1224_, v_mvars_1224_, v___x_1237_, v___x_1238_, v___x_1231_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1239_;
}
}
else
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = lean_usize_of_nat(v___x_1232_);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1224_, v_mvars_1224_, v___x_1240_, v___x_1241_, v___x_1231_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_mvars_1243_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
if (lean_obj_tag(v_a_1250_) == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = l_List_reverse___redArg(v_a_1251_);
return v___x_1252_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
v_head_1253_ = lean_ctor_get(v_a_1250_, 0);
v_tail_1254_ = lean_ctor_get(v_a_1250_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1250_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1256_ = v_a_1250_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_head_1253_);
lean_dec(v_a_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = l_Lean_Expr_mvarId_x21(v_head_1253_);
lean_dec(v_head_1253_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_a_1251_);
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_a_1251_);
v___x_1260_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v_a_1250_ = v_tail_1254_;
v_a_1251_ = v___x_1260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1264_, uint8_t v_x_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
switch(v_x_1265_)
{
case 0:
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1264_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec_ref(v_mvars_1264_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1284_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v_fst_1276_ = lean_ctor_get(v_a_1272_, 0);
lean_inc(v_fst_1276_);
v_snd_1277_ = lean_ctor_get(v_a_1272_, 1);
lean_inc(v_snd_1277_);
lean_dec(v_a_1272_);
v___x_1278_ = lean_array_to_list(v_fst_1276_);
v___x_1279_ = lean_array_to_list(v_snd_1277_);
v___x_1280_ = l_List_appendTR___redArg(v___x_1278_, v___x_1279_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1280_);
v___x_1282_ = v___x_1274_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1271_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1271_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
case 1:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1264_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec_ref(v_mvars_1264_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1303_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_fst_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v_fst_1298_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_fst_1298_);
lean_dec(v_a_1294_);
v___x_1299_ = lean_array_to_list(v_fst_1298_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1293_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1293_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
default: 
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_array_to_list(v_mvars_1264_);
v___x_1313_ = lean_box(0);
v___x_1314_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1316_, lean_object* v_x_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
uint8_t v_x_814__boxed_1323_; lean_object* v_res_1324_; 
v_x_814__boxed_1323_ = lean_unbox(v_x_1317_);
v_res_1324_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1316_, v_x_814__boxed_1323_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1325_, lean_object* v_a_1326_, lean_object* v_b_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
if (v_approx_1325_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1326_, v_b_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; uint8_t v_constApprox_1335_; uint8_t v_isDefEqStuckEx_1336_; uint8_t v_unificationHints_1337_; uint8_t v_proofIrrelevance_1338_; uint8_t v_assignSyntheticOpaque_1339_; uint8_t v_offsetCnstrs_1340_; uint8_t v_transparency_1341_; uint8_t v_etaStruct_1342_; uint8_t v_univApprox_1343_; uint8_t v_iota_1344_; uint8_t v_beta_1345_; uint8_t v_proj_1346_; uint8_t v_zeta_1347_; uint8_t v_zetaDelta_1348_; uint8_t v_zetaUnused_1349_; uint8_t v_zetaHave_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1371_; 
v___x_1334_ = l_Lean_Meta_Context_config(v_a_1328_);
v_constApprox_1335_ = lean_ctor_get_uint8(v___x_1334_, 3);
v_isDefEqStuckEx_1336_ = lean_ctor_get_uint8(v___x_1334_, 4);
v_unificationHints_1337_ = lean_ctor_get_uint8(v___x_1334_, 5);
v_proofIrrelevance_1338_ = lean_ctor_get_uint8(v___x_1334_, 6);
v_assignSyntheticOpaque_1339_ = lean_ctor_get_uint8(v___x_1334_, 7);
v_offsetCnstrs_1340_ = lean_ctor_get_uint8(v___x_1334_, 8);
v_transparency_1341_ = lean_ctor_get_uint8(v___x_1334_, 9);
v_etaStruct_1342_ = lean_ctor_get_uint8(v___x_1334_, 10);
v_univApprox_1343_ = lean_ctor_get_uint8(v___x_1334_, 11);
v_iota_1344_ = lean_ctor_get_uint8(v___x_1334_, 12);
v_beta_1345_ = lean_ctor_get_uint8(v___x_1334_, 13);
v_proj_1346_ = lean_ctor_get_uint8(v___x_1334_, 14);
v_zeta_1347_ = lean_ctor_get_uint8(v___x_1334_, 15);
v_zetaDelta_1348_ = lean_ctor_get_uint8(v___x_1334_, 16);
v_zetaUnused_1349_ = lean_ctor_get_uint8(v___x_1334_, 17);
v_zetaHave_1350_ = lean_ctor_get_uint8(v___x_1334_, 18);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1352_ = v___x_1334_;
v_isShared_1353_ = v_isSharedCheck_1371_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v___x_1334_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1371_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 3, v_constApprox_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 4, v_isDefEqStuckEx_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 5, v_unificationHints_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 6, v_proofIrrelevance_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 7, v_assignSyntheticOpaque_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 8, v_offsetCnstrs_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 9, v_transparency_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 10, v_etaStruct_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 11, v_univApprox_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 12, v_iota_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 13, v_beta_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 14, v_proj_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 15, v_zeta_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 16, v_zetaDelta_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 17, v_zetaUnused_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, 18, v_zetaHave_1350_);
v___x_1355_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
uint8_t v_trackZetaDelta_1356_; lean_object* v_zetaDeltaSet_1357_; lean_object* v_lctx_1358_; lean_object* v_localInstances_1359_; lean_object* v_defEqCtx_x3f_1360_; lean_object* v_synthPendingDepth_1361_; lean_object* v_canUnfold_x3f_1362_; uint8_t v_univApprox_1363_; uint8_t v_inTypeClassResolution_1364_; uint8_t v_cacheInferType_1365_; uint64_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_ctor_set_uint8(v___x_1355_, 0, v_approx_1325_);
lean_ctor_set_uint8(v___x_1355_, 1, v_approx_1325_);
lean_ctor_set_uint8(v___x_1355_, 2, v_approx_1325_);
v_trackZetaDelta_1356_ = lean_ctor_get_uint8(v_a_1328_, sizeof(void*)*7);
v_zetaDeltaSet_1357_ = lean_ctor_get(v_a_1328_, 1);
v_lctx_1358_ = lean_ctor_get(v_a_1328_, 2);
v_localInstances_1359_ = lean_ctor_get(v_a_1328_, 3);
v_defEqCtx_x3f_1360_ = lean_ctor_get(v_a_1328_, 4);
v_synthPendingDepth_1361_ = lean_ctor_get(v_a_1328_, 5);
v_canUnfold_x3f_1362_ = lean_ctor_get(v_a_1328_, 6);
v_univApprox_1363_ = lean_ctor_get_uint8(v_a_1328_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1364_ = lean_ctor_get_uint8(v_a_1328_, sizeof(void*)*7 + 2);
v_cacheInferType_1365_ = lean_ctor_get_uint8(v_a_1328_, sizeof(void*)*7 + 3);
v___x_1366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1355_);
v___x_1367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1367_, 0, v___x_1355_);
lean_ctor_set_uint64(v___x_1367_, sizeof(void*)*1, v___x_1366_);
lean_inc(v_canUnfold_x3f_1362_);
lean_inc(v_synthPendingDepth_1361_);
lean_inc(v_defEqCtx_x3f_1360_);
lean_inc_ref(v_localInstances_1359_);
lean_inc_ref(v_lctx_1358_);
lean_inc(v_zetaDeltaSet_1357_);
v___x_1368_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_zetaDeltaSet_1357_);
lean_ctor_set(v___x_1368_, 2, v_lctx_1358_);
lean_ctor_set(v___x_1368_, 3, v_localInstances_1359_);
lean_ctor_set(v___x_1368_, 4, v_defEqCtx_x3f_1360_);
lean_ctor_set(v___x_1368_, 5, v_synthPendingDepth_1361_);
lean_ctor_set(v___x_1368_, 6, v_canUnfold_x3f_1362_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*7, v_trackZetaDelta_1356_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*7 + 1, v_univApprox_1363_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1364_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*7 + 3, v_cacheInferType_1365_);
v___x_1369_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1326_, v_b_1327_, v___x_1368_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec_ref_known(v___x_1368_, 7);
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1372_, lean_object* v_a_1373_, lean_object* v_b_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
uint8_t v_approx_boxed_1380_; lean_object* v_res_1381_; 
v_approx_boxed_1380_ = lean_unbox(v_approx_1372_);
v_res_1381_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1380_, v_a_1373_, v_b_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1382_, lean_object* v_cfg_1383_, lean_object* v_term_x3f_1384_, lean_object* v_targetType_1385_, lean_object* v_eType_1386_, lean_object* v_rangeNumArgs_1387_, lean_object* v_i_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_lower_1394_; lean_object* v_upper_1395_; uint8_t v___x_1396_; 
v_lower_1394_ = lean_ctor_get(v_rangeNumArgs_1387_, 0);
v_upper_1395_ = lean_ctor_get(v_rangeNumArgs_1387_, 1);
v___x_1396_ = lean_nat_dec_lt(v_i_1388_, v_upper_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
lean_dec(v_i_1388_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_nat_dec_eq(v_lower_1394_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
lean_inc(v_lower_1394_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_lower_1394_);
v___x_1400_ = 0;
lean_inc_ref(v_eType_1386_);
v___x_1401_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1386_, v___x_1399_, v___x_1400_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_snd_1403_; lean_object* v_snd_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v_snd_1403_ = lean_ctor_get(v_a_1402_, 1);
lean_inc(v_snd_1403_);
lean_dec(v_a_1402_);
v_snd_1404_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc(v_snd_1404_);
lean_dec(v_snd_1403_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_snd_1404_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1382_, v_eType_1386_, v___x_1405_, v_targetType_1385_, v_term_x3f_1384_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1406_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
v_a_1407_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1401_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1401_);
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
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1382_, v_eType_1386_, v___x_1415_, v_targetType_1385_, v_term_x3f_1384_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1416_;
}
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Meta_saveState___redArg(v_a_1390_, v_a_1392_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
lean_inc(v_i_1388_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_i_1388_);
v___x_1420_ = 0;
lean_inc_ref(v_eType_1386_);
v___x_1421_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1386_, v___x_1419_, v___x_1420_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_snd_1423_; lean_object* v_fst_1424_; lean_object* v_fst_1425_; lean_object* v_snd_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1464_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_snd_1423_ = lean_ctor_get(v_a_1422_, 1);
lean_inc(v_snd_1423_);
v_fst_1424_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_fst_1424_);
lean_dec(v_a_1422_);
v_fst_1425_ = lean_ctor_get(v_snd_1423_, 0);
v_snd_1426_ = lean_ctor_get(v_snd_1423_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_snd_1423_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1428_ = v_snd_1423_;
v_isShared_1429_ = v_isSharedCheck_1464_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_snd_1426_);
lean_inc(v_fst_1425_);
lean_dec(v_snd_1423_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1464_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
uint8_t v_approx_1430_; lean_object* v___x_1431_; 
v_approx_1430_ = lean_ctor_get_uint8(v_cfg_1383_, 3);
lean_inc_ref(v_targetType_1385_);
v___x_1431_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1430_, v_snd_1426_, v_targetType_1385_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1455_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_del_object(v___x_1434_);
lean_del_object(v___x_1428_);
lean_dec(v_fst_1425_);
lean_dec(v_fst_1424_);
v___x_1437_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1418_, v_a_1390_, v_a_1392_);
lean_dec(v_a_1418_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1437_, 1);
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_i_1388_, v___x_1438_);
lean_dec(v_i_1388_);
v_i_1388_ = v___x_1439_;
goto _start;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_i_1388_);
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
v_a_1441_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1437_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1437_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_a_1418_);
lean_dec(v_i_1388_);
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v_fst_1425_);
lean_ctor_set(v___x_1428_, 0, v_fst_1424_);
v___x_1450_ = v___x_1428_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_fst_1424_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_fst_1425_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1450_);
v___x_1452_ = v___x_1434_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_del_object(v___x_1428_);
lean_dec(v_fst_1425_);
lean_dec(v_fst_1424_);
lean_dec(v_a_1418_);
lean_dec(v_i_1388_);
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
v_a_1456_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1431_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1431_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1418_);
lean_dec(v_i_1388_);
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
v_a_1465_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1421_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1421_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
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
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_i_1388_);
lean_dec_ref(v_eType_1386_);
lean_dec_ref(v_targetType_1385_);
lean_dec(v_term_x3f_1384_);
lean_dec(v_mvarId_1382_);
v_a_1473_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1417_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1417_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1481_, lean_object* v_cfg_1482_, lean_object* v_term_x3f_1483_, lean_object* v_targetType_1484_, lean_object* v_eType_1485_, lean_object* v_rangeNumArgs_1486_, lean_object* v_i_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1481_, v_cfg_1482_, v_term_x3f_1483_, v_targetType_1484_, v_eType_1485_, v_rangeNumArgs_1486_, v_i_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec_ref(v_rangeNumArgs_1486_);
lean_dec_ref(v_cfg_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1494_, lean_object* v_h__1_1495_){
_start:
{
lean_object* v_snd_1496_; lean_object* v_fst_1497_; lean_object* v_fst_1498_; lean_object* v_snd_1499_; lean_object* v___x_1500_; 
v_snd_1496_ = lean_ctor_get(v_x_1494_, 1);
lean_inc(v_snd_1496_);
v_fst_1497_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_fst_1497_);
lean_dec_ref(v_x_1494_);
v_fst_1498_ = lean_ctor_get(v_snd_1496_, 0);
lean_inc(v_fst_1498_);
v_snd_1499_ = lean_ctor_get(v_snd_1496_, 1);
lean_inc(v_snd_1499_);
lean_dec(v_snd_1496_);
v___x_1500_ = lean_apply_3(v_h__1_1495_, v_fst_1497_, v_fst_1498_, v_snd_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1501_, lean_object* v_x_1502_, lean_object* v_h__1_1503_){
_start:
{
lean_object* v_snd_1504_; lean_object* v_fst_1505_; lean_object* v_fst_1506_; lean_object* v_snd_1507_; lean_object* v___x_1508_; 
v_snd_1504_ = lean_ctor_get(v_x_1502_, 1);
lean_inc(v_snd_1504_);
v_fst_1505_ = lean_ctor_get(v_x_1502_, 0);
lean_inc(v_fst_1505_);
lean_dec_ref(v_x_1502_);
v_fst_1506_ = lean_ctor_get(v_snd_1504_, 0);
lean_inc(v_fst_1506_);
v_snd_1507_ = lean_ctor_get(v_snd_1504_, 1);
lean_inc(v_snd_1507_);
lean_dec(v_snd_1504_);
v___x_1508_ = lean_apply_3(v_h__1_1503_, v_fst_1505_, v_fst_1506_, v_snd_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = l_Lean_Expr_hasMVar(v_e_1509_);
v___x_1513_ = lean_bool_not(v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v_mctx_1515_; lean_object* v___x_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; lean_object* v_cache_1520_; lean_object* v_zetaDeltaFVarIds_1521_; lean_object* v_postponed_1522_; lean_object* v_diag_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v___x_1514_ = lean_st_ref_get(v___y_1510_);
v_mctx_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_ref(v_mctx_1515_);
lean_dec(v___x_1514_);
v___x_1516_ = l_Lean_instantiateMVarsCore(v_mctx_1515_, v_e_1509_);
v_fst_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_snd_1518_);
lean_dec_ref(v___x_1516_);
v___x_1519_ = lean_st_ref_take(v___y_1510_);
v_cache_1520_ = lean_ctor_get(v___x_1519_, 1);
v_zetaDeltaFVarIds_1521_ = lean_ctor_get(v___x_1519_, 2);
v_postponed_1522_ = lean_ctor_get(v___x_1519_, 3);
v_diag_1523_ = lean_ctor_get(v___x_1519_, 4);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1533_);
v___x_1525_ = v___x_1519_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_diag_1523_);
lean_inc(v_postponed_1522_);
lean_inc(v_zetaDeltaFVarIds_1521_);
lean_inc(v_cache_1520_);
lean_dec(v___x_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_snd_1518_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_snd_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_cache_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_zetaDeltaFVarIds_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_postponed_1522_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_diag_1523_);
v___x_1528_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_st_ref_set(v___y_1510_, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_fst_1517_);
return v___x_1530_;
}
}
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_e_1509_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1535_, v___y_1536_);
lean_dec(v___y_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1539_, v___y_1541_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1553_, v_x_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1560_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1560_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1577_, v_x_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1585_, lean_object* v_mvarId_1586_, lean_object* v_x_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1586_, v_x_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_mvarId_1595_, lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1594_, v_mvarId_1595_, v_x_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1603_, size_t v_i_1604_, size_t v_stop_1605_, lean_object* v_b_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_a_1610_; uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_eq(v_i_1604_, v_stop_1605_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v_a_1617_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = lean_array_uget_borrowed(v_as_1603_, v_i_1604_);
v___x_1619_ = l_Lean_Expr_mvarId_x21(v___x_1615_);
v___x_1620_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1619_, v___y_1607_);
lean_dec(v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; uint8_t v___x_1622_; uint8_t v___x_1623_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
v___x_1623_ = lean_bool_not(v___x_1622_);
v_a_1617_ = v___x_1623_;
goto v___jp_1616_;
}
else
{
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1624_; uint8_t v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1625_ = lean_unbox(v_a_1624_);
lean_dec(v_a_1624_);
v_a_1617_ = v___x_1625_;
goto v___jp_1616_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_b_1606_);
v_a_1626_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1620_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1620_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
v___jp_1616_:
{
if (v_a_1617_ == 0)
{
v_a_1610_ = v_b_1606_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1618_; 
lean_inc(v___x_1615_);
v___x_1618_ = lean_array_push(v_b_1606_, v___x_1615_);
v_a_1610_ = v___x_1618_;
goto v___jp_1609_;
}
}
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_b_1606_);
return v___x_1634_;
}
v___jp_1609_:
{
size_t v___x_1611_; size_t v___x_1612_; 
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1604_, v___x_1611_);
v_i_1604_ = v___x_1612_;
v_b_1606_ = v_a_1610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1635_, lean_object* v_i_1636_, lean_object* v_stop_1637_, lean_object* v_b_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
size_t v_i_boxed_1641_; size_t v_stop_boxed_1642_; lean_object* v_res_1643_; 
v_i_boxed_1641_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_stop_boxed_1642_ = lean_unbox_usize(v_stop_1637_);
lean_dec(v_stop_1637_);
v_res_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1635_, v_i_boxed_1641_, v_stop_boxed_1642_, v_b_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v_as_1635_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
if (lean_obj_tag(v_as_1644_) == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v_head_1652_; lean_object* v_tail_1653_; lean_object* v___x_1654_; 
v_head_1652_ = lean_ctor_get(v_as_1644_, 0);
lean_inc(v_head_1652_);
v_tail_1653_ = lean_ctor_get(v_as_1644_, 1);
lean_inc(v_tail_1653_);
lean_dec_ref_known(v_as_1644_, 2);
v___x_1654_ = l_Lean_MVarId_headBetaType(v_head_1652_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_dec_ref_known(v___x_1654_, 1);
v_as_1644_ = v_tail_1653_;
goto _start;
}
else
{
lean_dec(v_tail_1653_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_ks_1667_; lean_object* v_vs_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1692_; 
v_ks_1667_ = lean_ctor_get(v_x_1663_, 0);
v_vs_1668_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1670_ = v_x_1663_;
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_vs_1668_);
lean_inc(v_ks_1667_);
lean_dec(v_x_1663_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = lean_array_get_size(v_ks_1667_);
v___x_1673_ = lean_nat_dec_lt(v_x_1664_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec(v_x_1664_);
v___x_1674_ = lean_array_push(v_ks_1667_, v_x_1665_);
v___x_1675_ = lean_array_push(v_vs_1668_, v_x_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1675_);
lean_ctor_set(v___x_1670_, 0, v___x_1674_);
v___x_1677_ = v___x_1670_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
lean_object* v_k_x27_1679_; uint8_t v___x_1680_; 
v_k_x27_1679_ = lean_array_fget_borrowed(v_ks_1667_, v_x_1664_);
v___x_1680_ = l_Lean_instBEqMVarId_beq(v_x_1665_, v_k_x27_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1682_; 
if (v_isShared_1671_ == 0)
{
v___x_1682_ = v___x_1670_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_ks_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_vs_1668_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_x_1664_, v___x_1683_);
lean_dec(v_x_1664_);
v_x_1663_ = v___x_1682_;
v_x_1664_ = v___x_1684_;
goto _start;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1687_ = lean_array_fset(v_ks_1667_, v_x_1664_, v_x_1665_);
v___x_1688_ = lean_array_fset(v_vs_1668_, v_x_1664_, v_x_1666_);
lean_dec(v_x_1664_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1688_);
lean_ctor_set(v___x_1670_, 0, v___x_1687_);
v___x_1690_ = v___x_1670_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1693_, lean_object* v_k_1694_, lean_object* v_v_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1693_, v___x_1696_, v_k_1694_, v_v_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1699_, size_t v_x_1700_, size_t v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_es_1704_; size_t v___x_1705_; size_t v___x_1706_; lean_object* v_j_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_es_1704_ = lean_ctor_get(v_x_1699_, 0);
v___x_1705_ = ((size_t)31ULL);
v___x_1706_ = lean_usize_land(v_x_1700_, v___x_1705_);
v_j_1707_ = lean_usize_to_nat(v___x_1706_);
v___x_1708_ = lean_array_get_size(v_es_1704_);
v___x_1709_ = lean_nat_dec_lt(v_j_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v_j_1707_);
lean_dec(v_x_1703_);
lean_dec(v_x_1702_);
return v_x_1699_;
}
else
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1748_; 
lean_inc_ref(v_es_1704_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v_x_1699_, 0);
lean_dec(v_unused_1749_);
v___x_1711_ = v_x_1699_;
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v_x_1699_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_v_1713_; lean_object* v___x_1714_; lean_object* v_xs_x27_1715_; lean_object* v___y_1717_; 
v_v_1713_ = lean_array_fget(v_es_1704_, v_j_1707_);
v___x_1714_ = lean_box(0);
v_xs_x27_1715_ = lean_array_fset(v_es_1704_, v_j_1707_, v___x_1714_);
switch(lean_obj_tag(v_v_1713_))
{
case 0:
{
lean_object* v_key_1722_; lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1733_; 
v_key_1722_ = lean_ctor_get(v_v_1713_, 0);
v_val_1723_ = lean_ctor_get(v_v_1713_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_v_1713_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1725_ = v_v_1713_;
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_inc(v_key_1722_);
lean_dec(v_v_1713_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Lean_instBEqMVarId_beq(v_x_1702_, v_key_1722_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1725_);
v___x_1728_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1722_, v_val_1723_, v_x_1702_, v_x_1703_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___y_1717_ = v___x_1729_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_val_1723_);
lean_dec(v_key_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_x_1703_);
lean_ctor_set(v___x_1725_, 0, v_x_1702_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1702_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_x_1703_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v___y_1717_ = v___x_1731_;
goto v___jp_1716_;
}
}
}
}
case 1:
{
lean_object* v_node_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1746_; 
v_node_1734_ = lean_ctor_get(v_v_1713_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_v_1713_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1736_ = v_v_1713_;
v_isShared_1737_ = v_isSharedCheck_1746_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_node_1734_);
lean_dec(v_v_1713_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1746_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_usize_shift_right(v_x_1700_, v___x_1738_);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_x_1701_, v___x_1740_);
v___x_1742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1734_, v___x_1739_, v___x_1741_, v_x_1702_, v_x_1703_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1742_);
v___x_1744_ = v___x_1736_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v___y_1717_ = v___x_1744_;
goto v___jp_1716_;
}
}
}
default: 
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_x_1702_);
lean_ctor_set(v___x_1747_, 1, v_x_1703_);
v___y_1717_ = v___x_1747_;
goto v___jp_1716_;
}
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_array_fset(v_xs_x27_1715_, v_j_1707_, v___y_1717_);
lean_dec(v_j_1707_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1718_);
v___x_1720_ = v___x_1711_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v_ks_1750_; lean_object* v_vs_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1771_; 
v_ks_1750_ = lean_ctor_get(v_x_1699_, 0);
v_vs_1751_ = lean_ctor_get(v_x_1699_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1753_ = v_x_1699_;
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_vs_1751_);
lean_inc(v_ks_1750_);
lean_dec(v_x_1699_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_ks_1750_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_vs_1751_);
v___x_1756_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v_newNode_1757_; uint8_t v___y_1759_; size_t v___x_1765_; uint8_t v___x_1766_; 
v_newNode_1757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1756_, v_x_1702_, v_x_1703_);
v___x_1765_ = ((size_t)7ULL);
v___x_1766_ = lean_usize_dec_le(v___x_1765_, v_x_1701_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1757_);
v___x_1768_ = lean_unsigned_to_nat(4u);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
lean_dec(v___x_1767_);
v___y_1759_ = v___x_1769_;
goto v___jp_1758_;
}
else
{
v___y_1759_ = v___x_1766_;
goto v___jp_1758_;
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_ks_1760_ = lean_ctor_get(v_newNode_1757_, 0);
lean_inc_ref(v_ks_1760_);
v_vs_1761_ = lean_ctor_get(v_newNode_1757_, 1);
lean_inc_ref(v_vs_1761_);
lean_dec_ref(v_newNode_1757_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1701_, v_ks_1760_, v_vs_1761_, v___x_1762_, v___x_1763_);
lean_dec_ref(v_vs_1761_);
lean_dec_ref(v_ks_1760_);
return v___x_1764_;
}
else
{
return v_newNode_1757_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1772_, lean_object* v_keys_1773_, lean_object* v_vals_1774_, lean_object* v_i_1775_, lean_object* v_entries_1776_){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_get_size(v_keys_1773_);
v___x_1778_ = lean_nat_dec_lt(v_i_1775_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec(v_i_1775_);
return v_entries_1776_;
}
else
{
lean_object* v_k_1779_; lean_object* v_v_1780_; uint64_t v___x_1781_; size_t v_h_1782_; size_t v___x_1783_; lean_object* v___x_1784_; size_t v___x_1785_; size_t v___x_1786_; size_t v___x_1787_; size_t v_h_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_k_1779_ = lean_array_fget_borrowed(v_keys_1773_, v_i_1775_);
v_v_1780_ = lean_array_fget_borrowed(v_vals_1774_, v_i_1775_);
v___x_1781_ = l_Lean_instHashableMVarId_hash(v_k_1779_);
v_h_1782_ = lean_uint64_to_usize(v___x_1781_);
v___x_1783_ = ((size_t)5ULL);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_sub(v_depth_1772_, v___x_1785_);
v___x_1787_ = lean_usize_mul(v___x_1783_, v___x_1786_);
v_h_1788_ = lean_usize_shift_right(v_h_1782_, v___x_1787_);
v___x_1789_ = lean_nat_add(v_i_1775_, v___x_1784_);
lean_dec(v_i_1775_);
lean_inc(v_v_1780_);
lean_inc(v_k_1779_);
v___x_1790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1776_, v_h_1788_, v_depth_1772_, v_k_1779_, v_v_1780_);
v_i_1775_ = v___x_1789_;
v_entries_1776_ = v___x_1790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1792_, lean_object* v_keys_1793_, lean_object* v_vals_1794_, lean_object* v_i_1795_, lean_object* v_entries_1796_){
_start:
{
size_t v_depth_boxed_1797_; lean_object* v_res_1798_; 
v_depth_boxed_1797_ = lean_unbox_usize(v_depth_1792_);
lean_dec(v_depth_1792_);
v_res_1798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1797_, v_keys_1793_, v_vals_1794_, v_i_1795_, v_entries_1796_);
lean_dec_ref(v_vals_1794_);
lean_dec_ref(v_keys_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
size_t v_x_7097__boxed_1804_; size_t v_x_7098__boxed_1805_; lean_object* v_res_1806_; 
v_x_7097__boxed_1804_ = lean_unbox_usize(v_x_1800_);
lean_dec(v_x_1800_);
v_x_7098__boxed_1805_ = lean_unbox_usize(v_x_1801_);
lean_dec(v_x_1801_);
v_res_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1799_, v_x_7097__boxed_1804_, v_x_7098__boxed_1805_, v_x_1802_, v_x_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint64_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = l_Lean_instHashableMVarId_hash(v_x_1808_);
v___x_1811_ = lean_uint64_to_usize(v___x_1810_);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1807_, v___x_1811_, v___x_1812_, v_x_1808_, v_x_1809_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1814_, lean_object* v_val_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v_mctx_1819_; lean_object* v_cache_1820_; lean_object* v_zetaDeltaFVarIds_1821_; lean_object* v_postponed_1822_; lean_object* v_diag_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1851_; 
v___x_1818_ = lean_st_ref_take(v___y_1816_);
v_mctx_1819_ = lean_ctor_get(v___x_1818_, 0);
v_cache_1820_ = lean_ctor_get(v___x_1818_, 1);
v_zetaDeltaFVarIds_1821_ = lean_ctor_get(v___x_1818_, 2);
v_postponed_1822_ = lean_ctor_get(v___x_1818_, 3);
v_diag_1823_ = lean_ctor_get(v___x_1818_, 4);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1825_ = v___x_1818_;
v_isShared_1826_ = v_isSharedCheck_1851_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_diag_1823_);
lean_inc(v_postponed_1822_);
lean_inc(v_zetaDeltaFVarIds_1821_);
lean_inc(v_cache_1820_);
lean_inc(v_mctx_1819_);
lean_dec(v___x_1818_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1851_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_depth_1827_; lean_object* v_levelAssignDepth_1828_; lean_object* v_lmvarCounter_1829_; lean_object* v_mvarCounter_1830_; lean_object* v_lDecls_1831_; lean_object* v_decls_1832_; lean_object* v_userNames_1833_; lean_object* v_lAssignment_1834_; lean_object* v_eAssignment_1835_; lean_object* v_dAssignment_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1850_; 
v_depth_1827_ = lean_ctor_get(v_mctx_1819_, 0);
v_levelAssignDepth_1828_ = lean_ctor_get(v_mctx_1819_, 1);
v_lmvarCounter_1829_ = lean_ctor_get(v_mctx_1819_, 2);
v_mvarCounter_1830_ = lean_ctor_get(v_mctx_1819_, 3);
v_lDecls_1831_ = lean_ctor_get(v_mctx_1819_, 4);
v_decls_1832_ = lean_ctor_get(v_mctx_1819_, 5);
v_userNames_1833_ = lean_ctor_get(v_mctx_1819_, 6);
v_lAssignment_1834_ = lean_ctor_get(v_mctx_1819_, 7);
v_eAssignment_1835_ = lean_ctor_get(v_mctx_1819_, 8);
v_dAssignment_1836_ = lean_ctor_get(v_mctx_1819_, 9);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_mctx_1819_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1838_ = v_mctx_1819_;
v_isShared_1839_ = v_isSharedCheck_1850_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_dAssignment_1836_);
lean_inc(v_eAssignment_1835_);
lean_inc(v_lAssignment_1834_);
lean_inc(v_userNames_1833_);
lean_inc(v_decls_1832_);
lean_inc(v_lDecls_1831_);
lean_inc(v_mvarCounter_1830_);
lean_inc(v_lmvarCounter_1829_);
lean_inc(v_levelAssignDepth_1828_);
lean_inc(v_depth_1827_);
lean_dec(v_mctx_1819_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1850_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1835_, v_mvarId_1814_, v_val_1815_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 8, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_depth_1827_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_levelAssignDepth_1828_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_lmvarCounter_1829_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_mvarCounter_1830_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v_lDecls_1831_);
lean_ctor_set(v_reuseFailAlloc_1849_, 5, v_decls_1832_);
lean_ctor_set(v_reuseFailAlloc_1849_, 6, v_userNames_1833_);
lean_ctor_set(v_reuseFailAlloc_1849_, 7, v_lAssignment_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 8, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1849_, 9, v_dAssignment_1836_);
v___x_1842_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1842_);
v___x_1844_ = v___x_1825_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_cache_1820_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_zetaDeltaFVarIds_1821_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_postponed_1822_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_diag_1823_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_st_ref_set(v___y_1816_, v___x_1844_);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1852_, lean_object* v_val_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1852_, v_val_1853_, v___y_1854_);
lean_dec(v___y_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1857_, lean_object* v_x_1858_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = 0;
return v___x_1859_;
}
else
{
lean_object* v_head_1860_; lean_object* v_tail_1861_; uint8_t v___x_1862_; 
v_head_1860_ = lean_ctor_get(v_x_1858_, 0);
v_tail_1861_ = lean_ctor_get(v_x_1858_, 1);
v___x_1862_ = l_Lean_instBEqMVarId_beq(v_a_1857_, v_head_1860_);
if (v___x_1862_ == 0)
{
v_x_1858_ = v_tail_1861_;
goto _start;
}
else
{
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1864_, lean_object* v_x_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1864_, v_x_1865_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1868_, lean_object* v_as_1869_, size_t v_i_1870_, size_t v_stop_1871_, lean_object* v_b_1872_){
_start:
{
lean_object* v___y_1874_; uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_eq(v_i_1870_, v_stop_1871_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; uint8_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1879_ = lean_array_uget_borrowed(v_as_1869_, v_i_1870_);
v___x_1880_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1879_, v_a_1868_);
v___x_1881_ = lean_bool_not(v___x_1880_);
if (v___x_1881_ == 0)
{
v___y_1874_ = v_b_1872_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1882_; 
lean_inc(v___x_1879_);
v___x_1882_ = lean_array_push(v_b_1872_, v___x_1879_);
v___y_1874_ = v___x_1882_;
goto v___jp_1873_;
}
}
else
{
return v_b_1872_;
}
v___jp_1873_:
{
size_t v___x_1875_; size_t v___x_1876_; 
v___x_1875_ = ((size_t)1ULL);
v___x_1876_ = lean_usize_add(v_i_1870_, v___x_1875_);
v_i_1870_ = v___x_1876_;
v_b_1872_ = v___y_1874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1883_, lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v_stop_1886_, lean_object* v_b_1887_){
_start:
{
size_t v_i_boxed_1888_; size_t v_stop_boxed_1889_; lean_object* v_res_1890_; 
v_i_boxed_1888_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_stop_boxed_1889_ = lean_unbox_usize(v_stop_1886_);
lean_dec(v_stop_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1883_, v_as_1884_, v_i_boxed_1888_, v_stop_boxed_1889_, v_b_1887_);
lean_dec_ref(v_as_1884_);
lean_dec(v_a_1883_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1891_, lean_object* v___x_1892_, lean_object* v_e_1893_, lean_object* v_cfg_1894_, lean_object* v_term_x3f_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1928_; uint8_t v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v_a_1936_; lean_object* v___y_1969_; uint8_t v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___x_1987_; 
lean_inc(v___x_1892_);
lean_inc(v_mvarId_1891_);
v___x_1987_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1891_, v___x_1892_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref_known(v___x_1987_, 1);
lean_inc(v_mvarId_1891_);
v___x_1988_ = l_Lean_MVarId_getType(v_mvarId_1891_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc_ref(v_e_1893_);
v___x_1990_ = lean_infer_type(v_e_1893_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_rangeNumArgs_1993_; lean_object* v_lower_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2038_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_n(v_a_1991_, 2);
lean_dec_ref_known(v___x_1990_, 1);
v___x_2038_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1991_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_snd_2040_; uint8_t v___x_2041_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v_snd_2040_ = lean_ctor_get(v_a_2039_, 1);
v___x_2041_ = lean_unbox(v_snd_2040_);
if (v___x_2041_ == 0)
{
lean_object* v_fst_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2062_; 
v_fst_2042_ = lean_ctor_get(v_a_2039_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_a_2039_, 1);
lean_dec(v_unused_2063_);
v___x_2044_ = v_a_2039_;
v_isShared_2045_ = v_isSharedCheck_2062_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_fst_2042_);
lean_dec(v_a_2039_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2062_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; 
lean_inc(v_a_1989_);
v___x_2046_ = l_Lean_Meta_getExpectedNumArgs(v_a_1989_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = lean_nat_sub(v_fst_2042_, v_a_2047_);
lean_dec(v_a_2047_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_fst_2042_, v___x_2049_);
lean_dec(v_fst_2042_);
lean_inc(v___x_2048_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2050_);
lean_ctor_set(v___x_2044_, 0, v___x_2048_);
v___x_2052_ = v___x_2044_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
v_rangeNumArgs_1993_ = v___x_2052_;
v_lower_1994_ = v___x_2048_;
v___y_1995_ = v___y_1896_;
v___y_1996_ = v___y_1897_;
v___y_1997_ = v___y_1898_;
v___y_1998_ = v___y_1899_;
goto v___jp_1992_;
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_del_object(v___x_2044_);
lean_dec(v_fst_2042_);
lean_dec(v_a_1991_);
lean_dec(v_a_1989_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_term_x3f_1895_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2054_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2046_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2046_);
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
}
else
{
lean_object* v_fst_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2073_; 
v_fst_2064_ = lean_ctor_get(v_a_2039_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_a_2039_, 1);
lean_dec(v_unused_2074_);
v___x_2066_ = v_a_2039_;
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_fst_2064_);
lean_dec(v_a_2039_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_fst_2064_, v___x_2068_);
lean_inc(v_fst_2064_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_fst_2064_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_rangeNumArgs_1993_ = v___x_2071_;
v_lower_1994_ = v_fst_2064_;
v___y_1995_ = v___y_1896_;
v___y_1996_ = v___y_1897_;
v___y_1997_ = v___y_1898_;
v___y_1998_ = v___y_1899_;
goto v___jp_1992_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_1991_);
lean_dec(v_a_1989_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_term_x3f_1895_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2075_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2038_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2038_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
v___jp_1992_:
{
lean_object* v___x_1999_; 
lean_inc(v_mvarId_1891_);
v___x_1999_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1891_, v_cfg_1894_, v_term_x3f_1895_, v_a_1989_, v_a_1991_, v_rangeNumArgs_1993_, v_lower_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec_ref(v_rangeNumArgs_1993_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; uint8_t v_newGoals_2003_; uint8_t v_synthAssignedInstances_2004_; uint8_t v_allowSynthFailures_2005_; lean_object* v___x_2006_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v_fst_2001_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v_a_2000_, 1);
lean_inc_n(v_snd_2002_, 2);
lean_dec(v_a_2000_);
v_newGoals_2003_ = lean_ctor_get_uint8(v_cfg_1894_, 0);
v_synthAssignedInstances_2004_ = lean_ctor_get_uint8(v_cfg_1894_, 1);
v_allowSynthFailures_2005_ = lean_ctor_get_uint8(v_cfg_1894_, 2);
lean_inc(v_mvarId_1891_);
v___x_2006_ = l_Lean_Meta_synthAppInstances(v___x_1892_, v_mvarId_1891_, v_fst_2001_, v_snd_2002_, v_synthAssignedInstances_2004_, v_allowSynthFailures_2005_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
lean_dec_ref_known(v___x_2006_, 1);
v___x_2007_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1893_, v___y_1996_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc_n(v_a_2008_, 2);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l_Lean_mkAppN(v_a_2008_, v_fst_2001_);
lean_inc(v_mvarId_1891_);
v___x_2010_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1891_, v___x_2009_, v___y_1996_);
lean_dec_ref(v___x_2010_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_array_get_size(v_fst_2001_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2014_ = lean_nat_dec_lt(v___x_2011_, v___x_2012_);
if (v___x_2014_ == 0)
{
lean_dec(v_fst_2001_);
v___y_1928_ = v___y_1996_;
v___y_1929_ = v_newGoals_2003_;
v___y_1930_ = v___y_1995_;
v___y_1931_ = v___y_1998_;
v___y_1932_ = v___y_1997_;
v___y_1933_ = v_snd_2002_;
v___y_1934_ = v___x_2011_;
v___y_1935_ = v_a_2008_;
v_a_1936_ = v___x_2013_;
goto v___jp_1927_;
}
else
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_nat_dec_le(v___x_2012_, v___x_2012_);
if (v___x_2015_ == 0)
{
if (v___x_2014_ == 0)
{
lean_dec(v_fst_2001_);
v___y_1928_ = v___y_1996_;
v___y_1929_ = v_newGoals_2003_;
v___y_1930_ = v___y_1995_;
v___y_1931_ = v___y_1998_;
v___y_1932_ = v___y_1997_;
v___y_1933_ = v_snd_2002_;
v___y_1934_ = v___x_2011_;
v___y_1935_ = v_a_2008_;
v_a_1936_ = v___x_2013_;
goto v___jp_1927_;
}
else
{
size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = lean_usize_of_nat(v___x_2012_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2001_, v___x_2016_, v___x_2017_, v___x_2013_, v___y_1996_);
lean_dec(v_fst_2001_);
v___y_1969_ = v___y_1996_;
v___y_1970_ = v_newGoals_2003_;
v___y_1971_ = v___y_1995_;
v___y_1972_ = v___y_1997_;
v___y_1973_ = v___y_1998_;
v___y_1974_ = v_snd_2002_;
v___y_1975_ = v___x_2011_;
v___y_1976_ = v_a_2008_;
v___y_1977_ = v___x_2018_;
goto v___jp_1968_;
}
}
else
{
size_t v___x_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = lean_usize_of_nat(v___x_2012_);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2001_, v___x_2019_, v___x_2020_, v___x_2013_, v___y_1996_);
lean_dec(v_fst_2001_);
v___y_1969_ = v___y_1996_;
v___y_1970_ = v_newGoals_2003_;
v___y_1971_ = v___y_1995_;
v___y_1972_ = v___y_1997_;
v___y_1973_ = v___y_1998_;
v___y_1974_ = v_snd_2002_;
v___y_1975_ = v___x_2011_;
v___y_1976_ = v_a_2008_;
v___y_1977_ = v___x_2021_;
goto v___jp_1968_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_snd_2002_);
lean_dec(v_fst_2001_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec_ref(v_e_1893_);
lean_dec(v_mvarId_1891_);
v_a_2022_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2006_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2006_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2030_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1999_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1999_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_1989_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_term_x3f_1895_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2083_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_1990_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_1990_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_term_x3f_1895_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2091_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_1988_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_1988_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_term_x3f_1895_);
lean_dec_ref(v_e_1893_);
lean_dec(v___x_1892_);
lean_dec(v_mvarId_1891_);
v_a_2099_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_1987_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_1987_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
v___jp_1901_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_array_to_list(v___y_1907_);
v___x_1909_ = l_List_appendTR___redArg(v___y_1906_, v___x_1908_);
lean_inc(v___x_1909_);
v___x_1910_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1909_, v___y_1903_, v___y_1902_, v___y_1905_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1903_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v___x_1910_, 0);
lean_dec(v_unused_1918_);
v___x_1912_ = v___x_1910_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_dec(v___x_1910_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1909_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1909_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v___x_1909_);
v_a_1919_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
v___jp_1927_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Meta_appendParentTag(v_mvarId_1891_, v_a_1936_, v___y_1933_, v___y_1930_, v___y_1928_, v___y_1932_, v___y_1931_);
lean_dec_ref(v___y_1933_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; 
lean_dec_ref_known(v___x_1937_, 1);
v___x_1938_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1935_, v___y_1930_, v___y_1928_, v___y_1932_, v___y_1931_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1936_, v___y_1929_, v___y_1930_, v___y_1928_, v___y_1932_, v___y_1931_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = lean_array_get_size(v_a_1939_);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___y_1934_);
v___x_1944_ = lean_nat_dec_lt(v___y_1934_, v___x_1942_);
if (v___x_1944_ == 0)
{
lean_dec(v_a_1939_);
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1930_;
v___y_1904_ = v___y_1931_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v_a_1941_;
v___y_1907_ = v___x_1943_;
goto v___jp_1901_;
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_le(v___x_1942_, v___x_1942_);
if (v___x_1945_ == 0)
{
if (v___x_1944_ == 0)
{
lean_dec(v_a_1939_);
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1930_;
v___y_1904_ = v___y_1931_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v_a_1941_;
v___y_1907_ = v___x_1943_;
goto v___jp_1901_;
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = lean_usize_of_nat(v___x_1942_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1941_, v_a_1939_, v___x_1946_, v___x_1947_, v___x_1943_);
lean_dec(v_a_1939_);
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1930_;
v___y_1904_ = v___y_1931_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v_a_1941_;
v___y_1907_ = v___x_1948_;
goto v___jp_1901_;
}
}
else
{
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = lean_usize_of_nat(v___x_1942_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1941_, v_a_1939_, v___x_1949_, v___x_1950_, v___x_1943_);
lean_dec(v_a_1939_);
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1930_;
v___y_1904_ = v___y_1931_;
v___y_1905_ = v___y_1932_;
v___y_1906_ = v_a_1941_;
v___y_1907_ = v___x_1951_;
goto v___jp_1901_;
}
}
}
else
{
lean_dec(v_a_1939_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
return v___x_1940_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_a_1936_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
v_a_1952_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1938_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1938_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_a_1936_);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
v_a_1960_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1937_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1937_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
v___jp_1968_:
{
if (lean_obj_tag(v___y_1977_) == 0)
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___y_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___y_1977_, 1);
v___y_1928_ = v___y_1969_;
v___y_1929_ = v___y_1970_;
v___y_1930_ = v___y_1971_;
v___y_1931_ = v___y_1973_;
v___y_1932_ = v___y_1972_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
v___y_1935_ = v___y_1976_;
v_a_1936_ = v_a_1978_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v___y_1976_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1969_);
lean_dec(v_mvarId_1891_);
v_a_1979_ = lean_ctor_get(v___y_1977_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___y_1977_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___y_1977_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___y_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2107_, lean_object* v___x_2108_, lean_object* v_e_2109_, lean_object* v_cfg_2110_, lean_object* v_term_x3f_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2107_, v___x_2108_, v_e_2109_, v_cfg_2110_, v_term_x3f_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v_cfg_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2118_, lean_object* v_e_2119_, lean_object* v_cfg_2120_, lean_object* v_term_x3f_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2118_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2128_, 0, v_mvarId_2118_);
lean_closure_set(v___f_2128_, 1, v___x_2127_);
lean_closure_set(v___f_2128_, 2, v_e_2119_);
lean_closure_set(v___f_2128_, 3, v_cfg_2120_);
lean_closure_set(v___f_2128_, 4, v_term_x3f_2121_);
v___x_2129_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2118_, v___f_2128_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2130_, lean_object* v_e_2131_, lean_object* v_cfg_2132_, lean_object* v_term_x3f_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_MVarId_apply(v_mvarId_2130_, v_e_2131_, v_cfg_2132_, v_term_x3f_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2140_, lean_object* v_val_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2140_, v_val_2141_, v___y_2143_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2148_, lean_object* v_val_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2148_, v_val_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2156_, size_t v_i_2157_, size_t v_stop_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2156_, v_i_2157_, v_stop_2158_, v_b_2159_, v___y_2161_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2166_, lean_object* v_i_2167_, lean_object* v_stop_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
size_t v_i_boxed_2175_; size_t v_stop_boxed_2176_; lean_object* v_res_2177_; 
v_i_boxed_2175_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_stop_boxed_2176_ = lean_unbox_usize(v_stop_2168_);
lean_dec(v_stop_2168_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2166_, v_i_boxed_2175_, v_stop_boxed_2176_, v_b_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec_ref(v_as_2166_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2179_, v_x_2180_, v_x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2183_, lean_object* v_x_2184_, size_t v_x_2185_, size_t v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2184_, v_x_2185_, v_x_2186_, v_x_2187_, v_x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
size_t v_x_7832__boxed_2196_; size_t v_x_7833__boxed_2197_; lean_object* v_res_2198_; 
v_x_7832__boxed_2196_ = lean_unbox_usize(v_x_2192_);
lean_dec(v_x_2192_);
v_x_7833__boxed_2197_ = lean_unbox_usize(v_x_2193_);
lean_dec(v_x_2193_);
v_res_2198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2190_, v_x_2191_, v_x_7832__boxed_2196_, v_x_7833__boxed_2197_, v_x_2194_, v_x_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2199_, lean_object* v_n_2200_, lean_object* v_k_2201_, lean_object* v_v_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2200_, v_k_2201_, v_v_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2204_, size_t v_depth_2205_, lean_object* v_keys_2206_, lean_object* v_vals_2207_, lean_object* v_heq_2208_, lean_object* v_i_2209_, lean_object* v_entries_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2205_, v_keys_2206_, v_vals_2207_, v_i_2209_, v_entries_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2212_, lean_object* v_depth_2213_, lean_object* v_keys_2214_, lean_object* v_vals_2215_, lean_object* v_heq_2216_, lean_object* v_i_2217_, lean_object* v_entries_2218_){
_start:
{
size_t v_depth_boxed_2219_; lean_object* v_res_2220_; 
v_depth_boxed_2219_ = lean_unbox_usize(v_depth_2213_);
lean_dec(v_depth_2213_);
v_res_2220_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2212_, v_depth_boxed_2219_, v_keys_2214_, v_vals_2215_, v_heq_2216_, v_i_2217_, v_entries_2218_);
lean_dec_ref(v_vals_2215_);
lean_dec_ref(v_keys_2214_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2222_, v_x_2223_, v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2230_, lean_object* v_c_2231_, lean_object* v_cfg_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
lean_inc(v_c_2231_);
v___x_2238_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2231_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2241_ = 0;
v___x_2242_ = l_Lean_MessageData_ofConstName(v_c_2231_, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2240_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2240_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
v___x_2246_ = l_Lean_MVarId_apply(v_mvar_2230_, v_a_2239_, v_cfg_2232_, v___x_2245_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
return v___x_2246_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_cfg_2232_);
lean_dec(v_c_2231_);
lean_dec(v_mvar_2230_);
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2255_, lean_object* v_c_2256_, lean_object* v_cfg_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_MVarId_applyConst(v_mvar_2255_, v_c_2256_, v_cfg_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v_env_2271_; lean_object* v___x_2272_; lean_object* v_mctx_2273_; lean_object* v_lctx_2274_; lean_object* v_options_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2270_ = lean_st_ref_get(v___y_2268_);
v_env_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc_ref(v_env_2271_);
lean_dec(v___x_2270_);
v___x_2272_ = lean_st_ref_get(v___y_2266_);
v_mctx_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc_ref(v_mctx_2273_);
lean_dec(v___x_2272_);
v_lctx_2274_ = lean_ctor_get(v___y_2265_, 2);
v_options_2275_ = lean_ctor_get(v___y_2267_, 2);
lean_inc_ref(v_options_2275_);
lean_inc_ref(v_lctx_2274_);
v___x_2276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2276_, 0, v_env_2271_);
lean_ctor_set(v___x_2276_, 1, v_mctx_2273_);
lean_ctor_set(v___x_2276_, 2, v_lctx_2274_);
lean_ctor_set(v___x_2276_, 3, v_options_2275_);
v___x_2277_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_msgData_2264_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_ref_2292_; lean_object* v___x_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_ref_2292_ = lean_ctor_get(v___y_2289_, 5);
v___x_2293_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_inc(v_ref_2292_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_ref_2292_);
lean_ctor_set(v___x_2298_, 1, v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 1);
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2310_, size_t v_i_2311_, lean_object* v_bs_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_usize_dec_lt(v_i_2311_, v_sz_2310_);
if (v___x_2313_ == 0)
{
return v_bs_2312_;
}
else
{
lean_object* v_v_2314_; lean_object* v___x_2315_; lean_object* v_bs_x27_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v_v_2314_ = lean_array_uget(v_bs_2312_, v_i_2311_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v_bs_x27_2316_ = lean_array_uset(v_bs_2312_, v_i_2311_, v___x_2315_);
v___x_2317_ = l_Lean_Expr_mvarId_x21(v_v_2314_);
lean_dec(v_v_2314_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_add(v_i_2311_, v___x_2318_);
v___x_2320_ = lean_array_uset(v_bs_x27_2316_, v_i_2311_, v___x_2317_);
v_i_2311_ = v___x_2319_;
v_bs_2312_ = v___x_2320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_bs_2324_){
_start:
{
size_t v_sz_boxed_2325_; size_t v_i_boxed_2326_; lean_object* v_res_2327_; 
v_sz_boxed_2325_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2325_, v_i_boxed_2326_, v_bs_2324_);
return v_res_2327_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2346_, lean_object* v___x_2347_, lean_object* v_e_2348_, lean_object* v_n_2349_, uint8_t v_useApproxDefEq_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
lean_inc(v_mvarId_2346_);
v___x_2356_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2346_, v___x_2347_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref_known(v___x_2356_, 1);
lean_inc(v_mvarId_2346_);
v___x_2357_ = l_Lean_MVarId_getType(v_mvarId_2346_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
lean_inc(v___y_2354_);
lean_inc_ref(v___y_2353_);
lean_inc(v___y_2352_);
lean_inc_ref(v___y_2351_);
lean_inc_ref(v_e_2348_);
v___x_2359_ = lean_infer_type(v_e_2348_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = 0;
lean_inc(v_n_2349_);
v___x_2362_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2360_, v_n_2349_, v___x_2361_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_fst_2364_; lean_object* v_snd_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2455_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v_fst_2364_ = lean_ctor_get(v_a_2363_, 0);
v_snd_2365_ = lean_ctor_get(v_a_2363_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_a_2363_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2367_ = v_a_2363_;
v_isShared_2368_ = v_isSharedCheck_2455_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_snd_2365_);
lean_inc(v_fst_2364_);
lean_dec(v_a_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2455_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___y_2370_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2453_; 
v_snd_2385_ = lean_ctor_get(v_snd_2365_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_snd_2365_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v_snd_2365_, 0);
lean_dec(v_unused_2454_);
v___x_2387_ = v_snd_2365_;
v_isShared_2388_ = v_isSharedCheck_2453_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_dec(v_snd_2365_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2453_;
goto v_resetjp_2386_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2383_; 
lean_inc(v_fst_2364_);
v___x_2371_ = l_Lean_Expr_beta(v_e_2348_, v_fst_2364_);
v___x_2372_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2346_, v___x_2371_, v___y_2370_);
lean_dec(v___y_2370_);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v___x_2372_, 0);
lean_dec(v_unused_2384_);
v___x_2374_ = v___x_2372_;
v_isShared_2375_ = v_isSharedCheck_2383_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v___x_2372_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2383_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
v_sz_2376_ = lean_array_size(v_fst_2364_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2376_, v___x_2377_, v_fst_2364_);
v___x_2379_ = lean_array_to_list(v___x_2378_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2379_);
v___x_2381_ = v___x_2374_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
v_resetjp_2386_:
{
lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = lean_array_get_size(v_fst_2364_);
v___x_2434_ = lean_nat_dec_eq(v___x_2433_, v_n_2349_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_del_object(v___x_2387_);
lean_del_object(v___x_2367_);
lean_dec(v_fst_2364_);
lean_dec(v_a_2358_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v___x_2435_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2436_ = l_Nat_reprFast(v_n_2349_);
v___x_2437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
v___x_2438_ = l_Lean_MessageData_ofFormat(v___x_2437_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2435_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = l_Lean_indentExpr(v_snd_2385_);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2443_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
v___y_2390_ = v___y_2351_;
v___y_2391_ = v___y_2352_;
v___y_2392_ = v___y_2353_;
v___y_2393_ = v___y_2354_;
goto v___jp_2389_;
}
v___jp_2389_:
{
lean_object* v___x_2394_; 
lean_inc(v_a_2358_);
lean_inc(v_snd_2385_);
v___x_2394_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2350_, v_snd_2385_, v_a_2358_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; uint8_t v___x_2396_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = lean_unbox(v_a_2395_);
lean_dec(v_a_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_dec(v_fst_2364_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v___x_2397_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2398_ = l_Lean_indentExpr(v_a_2358_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 7);
lean_ctor_set(v___x_2387_, 1, v___x_2398_);
lean_ctor_set(v___x_2387_, 0, v___x_2397_);
v___x_2400_ = v___x_2387_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 7);
lean_ctor_set(v___x_2367_, 1, v___x_2401_);
lean_ctor_set(v___x_2367_, 0, v___x_2400_);
v___x_2403_ = v___x_2367_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
v___x_2404_ = l_Lean_indentExpr(v_snd_2385_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = l_Nat_reprFast(v_n_2349_);
v___x_2409_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
v___x_2410_ = l_Lean_MessageData_ofFormat(v___x_2409_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2407_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2413_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
else
{
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v___y_2390_);
lean_del_object(v___x_2387_);
lean_dec(v_snd_2385_);
lean_del_object(v___x_2367_);
lean_dec(v_a_2358_);
lean_dec(v_n_2349_);
v___y_2370_ = v___y_2391_;
goto v___jp_2369_;
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_del_object(v___x_2387_);
lean_dec(v_snd_2385_);
lean_del_object(v___x_2367_);
lean_dec(v_fst_2364_);
lean_dec(v_a_2358_);
lean_dec(v_n_2349_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v_a_2425_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2394_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2394_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2358_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_n_2349_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v_a_2456_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2362_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2362_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_a_2358_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_n_2349_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v_a_2464_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2359_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2359_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_n_2349_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v_a_2472_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2357_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2357_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_n_2349_);
lean_dec_ref(v_e_2348_);
lean_dec(v_mvarId_2346_);
v_a_2480_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2356_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2356_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2488_, lean_object* v___x_2489_, lean_object* v_e_2490_, lean_object* v_n_2491_, lean_object* v_useApproxDefEq_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2498_; lean_object* v_res_2499_; 
v_useApproxDefEq_boxed_2498_ = lean_unbox(v_useApproxDefEq_2492_);
v_res_2499_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2488_, v___x_2489_, v_e_2490_, v_n_2491_, v_useApproxDefEq_boxed_2498_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2500_, lean_object* v_e_2501_, lean_object* v_n_2502_, uint8_t v_useApproxDefEq_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2510_ = lean_box(v_useApproxDefEq_2503_);
lean_inc(v_mvarId_2500_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2511_, 0, v_mvarId_2500_);
lean_closure_set(v___f_2511_, 1, v___x_2509_);
lean_closure_set(v___f_2511_, 2, v_e_2501_);
lean_closure_set(v___f_2511_, 3, v_n_2502_);
lean_closure_set(v___f_2511_, 4, v___x_2510_);
v___x_2512_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2500_, v___f_2511_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2513_, lean_object* v_e_2514_, lean_object* v_n_2515_, lean_object* v_useApproxDefEq_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2522_; lean_object* v_res_2523_; 
v_useApproxDefEq_boxed_2522_ = lean_unbox(v_useApproxDefEq_2516_);
v_res_2523_ = l_Lean_MVarId_applyN(v_mvarId_2513_, v_e_2514_, v_n_2515_, v_useApproxDefEq_boxed_2522_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2524_, lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2532_, lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2532_, v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_box(0);
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2552_ = l_Lean_mkConst(v___x_2551_, v___x_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2553_, lean_object* v_type_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
lean_inc(v_a_2559_);
lean_inc_ref(v_a_2558_);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
v___x_2561_ = lean_whnf(v_type_2554_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2564_ = lean_unsigned_to_nat(2u);
v___x_2565_ = l_Lean_Expr_isAppOfArity(v_a_2562_, v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2566_ = lean_st_ref_get(v_a_2555_);
v___x_2567_ = lean_array_get_size(v___x_2566_);
lean_dec(v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = lean_nat_add(v___x_2567_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2571_ = lean_name_append_index_after(v___x_2570_, v___x_2569_);
v___x_2572_ = l_Lean_Name_append(v_tag_2553_, v___x_2571_);
v___x_2573_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2562_, v___x_2572_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2585_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2578_ = lean_st_ref_take(v_a_2555_);
v___x_2579_ = l_Lean_Expr_mvarId_x21(v_a_2574_);
v___x_2580_ = lean_array_push(v___x_2578_, v___x_2579_);
v___x_2581_ = lean_st_ref_set(v_a_2555_, v___x_2580_);
if (v_isShared_2577_ == 0)
{
v___x_2583_ = v___x_2576_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2574_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
return v___x_2573_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = l_Lean_Expr_appFn_x21(v_a_2562_);
v___x_2587_ = l_Lean_Expr_appArg_x21(v___x_2586_);
lean_dec_ref(v___x_2586_);
lean_inc_ref(v___x_2587_);
lean_inc(v_tag_2553_);
v___x_2588_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2553_, v___x_2587_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l_Lean_Expr_appArg_x21(v_a_2562_);
lean_dec(v_a_2562_);
lean_inc_ref(v___x_2590_);
v___x_2591_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2553_, v___x_2590_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2601_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2597_ = l_Lean_mkApp4(v___x_2596_, v___x_2587_, v___x_2590_, v_a_2589_, v_a_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2597_);
v___x_2599_ = v___x_2594_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_dec_ref(v___x_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v___x_2587_);
return v___x_2591_;
}
}
else
{
lean_dec_ref(v___x_2587_);
lean_dec(v_a_2562_);
lean_dec(v_tag_2553_);
return v___x_2588_;
}
}
}
else
{
lean_dec(v_tag_2553_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2602_, lean_object* v_type_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2602_, v_type_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2611_, lean_object* v___x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
lean_inc(v_mvarId_2611_);
v___x_2618_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2611_, v___x_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2618_, 1);
lean_inc(v_mvarId_2611_);
v___x_2619_ = l_Lean_MVarId_getType_x27(v_mvarId_2611_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2666_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2666_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2666_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2625_ = lean_unsigned_to_nat(2u);
v___x_2626_ = l_Lean_Expr_isAppOfArity(v_a_2620_, v___x_2624_, v___x_2625_);
v___x_2627_ = lean_bool_not(v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_del_object(v___x_2622_);
lean_inc(v_mvarId_2611_);
v___x_2628_ = l_Lean_MVarId_getTag(v_mvarId_2611_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2631_ = lean_st_mk_ref(v___x_2630_);
v___x_2632_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2629_, v_a_2620_, v___x_2631_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = lean_st_ref_get(v___x_2631_);
lean_dec(v___x_2631_);
v___x_2635_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2611_, v_a_2633_, v___y_2614_);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2644_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_array_to_list(v___x_2634_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v___x_2631_);
lean_dec(v_mvarId_2611_);
v_a_2645_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2632_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2632_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2620_);
lean_dec(v_mvarId_2611_);
v_a_2653_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2628_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2628_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
lean_dec(v_a_2620_);
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2662_, 0, v_mvarId_2611_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2662_);
v___x_2664_ = v___x_2622_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_mvarId_2611_);
v_a_2667_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2619_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2619_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_mvarId_2611_);
v_a_2675_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2618_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2618_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2683_, lean_object* v___x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2683_, v___x_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; 
v___x_2700_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2694_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2701_, 0, v_mvarId_2694_);
lean_closure_set(v___f_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2694_, v___f_2701_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_MVarId_splitAndCore(v_mvarId_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_MVarId_splitAndCore(v_mvarId_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_MVarId_splitAnd(v_mvarId_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2723_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2729_ = l_Lean_mkConst(v___x_2728_, v___x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2734_, lean_object* v___x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
lean_inc(v_mvarId_2734_);
v___x_2741_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2734_, v___x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2741_, 1);
lean_inc(v_mvarId_2734_);
v___x_2742_ = l_Lean_MVarId_getType(v_mvarId_2734_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2743_, v___y_2737_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_n(v_a_2745_, 2);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_Meta_getLevel(v_a_2745_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
lean_inc(v_mvarId_2734_);
v___x_2748_ = l_Lean_MVarId_getTag(v_mvarId_2734_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2752_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2751_, v_a_2749_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2766_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2747_);
lean_ctor_set(v___x_2755_, 1, v___x_2750_);
v___x_2756_ = l_Lean_mkConst(v___x_2754_, v___x_2755_);
v___x_2757_ = l_Lean_mkAppB(v___x_2756_, v_a_2745_, v_a_2753_);
v___x_2758_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2734_, v___x_2757_, v___y_2737_);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v___x_2758_, 0);
lean_dec(v_unused_2767_);
v___x_2760_ = v___x_2758_;
v_isShared_2761_ = v_isSharedCheck_2766_;
goto v_resetjp_2759_;
}
else
{
lean_dec(v___x_2758_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2766_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = l_Lean_Expr_mvarId_x21(v_a_2753_);
lean_dec(v_a_2753_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2762_);
v___x_2764_ = v___x_2760_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2768_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2752_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2752_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2776_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2748_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2748_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2784_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2746_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2746_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_mvarId_2734_);
v_a_2792_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2742_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2742_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_mvarId_2734_);
v_a_2800_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2741_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2741_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2808_, lean_object* v___x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2808_, v___x_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; 
v___x_2825_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2819_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2826_, 0, v_mvarId_2819_);
lean_closure_set(v___f_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2819_, v___f_2826_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_MVarId_exfalso(v_mvarId_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2839_ = l_Lean_MessageData_ofFormat(v___x_2838_);
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2846_, lean_object* v_name_2847_, lean_object* v_idx_2848_, lean_object* v_expected_x3f_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___x_2862_; 
lean_inc(v_name_2847_);
lean_inc(v_goal_2846_);
v___x_2862_ = l_Lean_MVarId_checkNotAssigned(v_goal_2846_, v_name_2847_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref_known(v___x_2862_, 1);
lean_inc(v_goal_2846_);
v___x_2863_ = l_Lean_MVarId_getType_x27(v_goal_2846_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = l_Lean_Expr_getAppFn(v_a_2864_);
lean_dec(v_a_2864_);
if (lean_obj_tag(v___x_2865_) == 4)
{
lean_object* v_declName_2866_; lean_object* v_us_2867_; lean_object* v___x_2868_; lean_object* v_env_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_declName_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_declName_2866_);
v_us_2867_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_us_2867_);
lean_dec_ref_known(v___x_2865_, 2);
v___x_2868_ = lean_st_ref_get(v___y_2853_);
v_env_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_env_2869_);
lean_dec(v___x_2868_);
v___x_2870_ = 0;
v___x_2871_ = l_Lean_Environment_find_x3f(v_env_2869_, v_declName_2866_, v___x_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_dec(v_us_2867_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2942_; 
v_val_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2942_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_val_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2942_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
if (lean_obj_tag(v_val_2872_) == 5)
{
lean_object* v_val_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2941_; 
v_val_2876_ = lean_ctor_get(v_val_2872_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_val_2872_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2878_ = v_val_2872_;
v_isShared_2879_ = v_isSharedCheck_2941_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_val_2876_);
lean_dec(v_val_2872_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2941_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; 
if (lean_obj_tag(v_expected_x3f_2849_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2940_; 
v_val_2911_ = lean_ctor_get(v_expected_x3f_2849_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_expected_x3f_2849_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2913_ = v_expected_x3f_2849_;
v_isShared_2914_ = v_isSharedCheck_2940_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v_expected_x3f_2849_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2940_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_ctors_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_ctors_2915_ = lean_ctor_get(v_val_2876_, 4);
v___x_2916_ = l_List_lengthTR___redArg(v_ctors_2915_);
v___x_2917_ = lean_nat_dec_eq(v___x_2916_, v_val_2911_);
lean_dec(v___x_2916_);
if (v___x_2917_ == 0)
{
uint8_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2918_ = 1;
lean_inc(v_name_2847_);
v___x_2919_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2847_, v___x_2918_);
v___x_2920_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2921_ = lean_string_append(v___x_2919_, v___x_2920_);
v___x_2922_ = l_Nat_reprFast(v_val_2911_);
v___x_2923_ = lean_string_append(v___x_2921_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
v___x_2927_ = l_Lean_MessageData_ofFormat(v___x_2926_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2927_);
v___x_2929_ = v___x_2913_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; 
lean_inc(v_goal_2846_);
lean_inc(v_name_2847_);
v___x_2930_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2929_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_dec_ref_known(v___x_2930_, 1);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_del_object(v___x_2878_);
lean_dec_ref(v_val_2876_);
lean_del_object(v___x_2874_);
lean_dec(v_us_2867_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_val_2911_);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
}
}
else
{
lean_dec(v_expected_x3f_2849_);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
v___jp_2880_:
{
lean_object* v_ctors_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_ctors_2885_ = lean_ctor_get(v_val_2876_, 4);
lean_inc(v_ctors_2885_);
lean_dec_ref(v_val_2876_);
v___x_2886_ = l_List_lengthTR___redArg(v_ctors_2885_);
v___x_2887_ = lean_nat_dec_lt(v_idx_2848_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec(v_ctors_2885_);
lean_dec(v_us_2867_);
v___x_2888_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2889_ = l_Nat_reprFast(v_idx_2848_);
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
v___x_2893_ = l_Nat_reprFast(v___x_2886_);
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 3);
lean_ctor_set(v___x_2878_, 0, v___x_2896_);
v___x_2898_ = v___x_2878_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_MessageData_ofFormat(v___x_2898_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2899_);
v___x_2901_ = v___x_2874_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2901_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2902_;
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec(v___x_2886_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_name_2847_);
v___x_2905_ = l_List_get___redArg(v_ctors_2885_, v_idx_2848_);
lean_dec(v_ctors_2885_);
v___x_2906_ = l_Lean_mkConst(v___x_2905_, v_us_2867_);
v___x_2907_ = 0;
v___x_2908_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2908_, 0, v___x_2907_);
lean_ctor_set_uint8(v___x_2908_, 1, v___x_2887_);
lean_ctor_set_uint8(v___x_2908_, 2, v___x_2870_);
lean_ctor_set_uint8(v___x_2908_, 3, v___x_2887_);
v___x_2909_ = lean_box(0);
v___x_2910_ = l_Lean_MVarId_apply(v_goal_2846_, v___x_2906_, v___x_2908_, v___x_2909_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2910_;
}
}
}
}
else
{
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_us_2867_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
}
}
}
else
{
lean_dec_ref(v___x_2865_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2943_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2863_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2863_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2951_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2862_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2862_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
v___jp_2855_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2861_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2860_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2959_, lean_object* v_name_2960_, lean_object* v_idx_2961_, lean_object* v_expected_x3f_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2959_, v_name_2960_, v_idx_2961_, v_expected_x3f_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2969_, lean_object* v_idx_2970_, lean_object* v_expected_x3f_2971_, lean_object* v_goal_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___f_2978_; lean_object* v___x_2979_; 
lean_inc(v_goal_2972_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2978_, 0, v_goal_2972_);
lean_closure_set(v___f_2978_, 1, v_name_2969_);
lean_closure_set(v___f_2978_, 2, v_idx_2970_);
lean_closure_set(v___f_2978_, 3, v_expected_x3f_2971_);
v___x_2979_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2972_, v___f_2978_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2980_, lean_object* v_idx_2981_, lean_object* v_expected_x3f_2982_, lean_object* v_goal_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_MVarId_nthConstructor(v_name_2980_, v_idx_2981_, v_expected_x3f_2982_, v_goal_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Meta_saveState___redArg(v___y_2992_, v___y_2994_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
lean_inc(v___y_2994_);
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2992_);
lean_inc_ref(v___y_2991_);
v___x_2998_ = lean_apply_5(v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, lean_box(0));
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v_a_2997_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_a_2999_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3003_);
v___x_3005_ = v___x_3001_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3037_; 
v_a_3008_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3010_ = v___x_2998_;
v_isShared_3011_ = v_isSharedCheck_3037_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2998_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3037_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
uint8_t v___y_3013_; uint8_t v___x_3035_; 
v___x_3035_ = l_Lean_Exception_isInterrupt(v_a_3008_);
if (v___x_3035_ == 0)
{
uint8_t v___x_3036_; 
lean_inc(v_a_3008_);
v___x_3036_ = l_Lean_Exception_isRuntime(v_a_3008_);
v___y_3013_ = v___x_3036_;
goto v___jp_3012_;
}
else
{
v___y_3013_ = v___x_3035_;
goto v___jp_3012_;
}
v___jp_3012_:
{
if (v___y_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3010_);
lean_dec(v_a_3008_);
v___x_3014_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2997_, v___y_2992_, v___y_2994_);
lean_dec(v_a_2997_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3023_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = lean_box(0);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v_a_3024_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3014_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3014_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v_a_2997_);
if (v_isShared_3011_ == 0)
{
v___x_3033_ = v___x_3010_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3008_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_x_2990_);
v_a_3038_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2996_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2996_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3053_, lean_object* v_x_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3061_, v_x_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3072_, lean_object* v___x_3073_, lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_MVarId_apply(v_mvarId_3072_, v___x_3073_, v___x_3074_, v___x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3098_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3098_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3098_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; 
if (lean_obj_tag(v_a_3082_) == 1)
{
lean_object* v_tail_3093_; 
v_tail_3093_ = lean_ctor_get(v_a_3082_, 1);
if (lean_obj_tag(v_tail_3093_) == 0)
{
lean_object* v_head_3094_; lean_object* v___x_3096_; 
v_head_3094_ = lean_ctor_get(v_a_3082_, 0);
lean_inc(v_head_3094_);
lean_dec_ref_known(v_a_3082_, 2);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v_head_3094_);
v___x_3096_ = v___x_3084_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_head_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
else
{
lean_dec_ref_known(v_a_3082_, 2);
lean_del_object(v___x_3084_);
v___y_3087_ = v___y_3076_;
v___y_3088_ = v___y_3077_;
v___y_3089_ = v___y_3078_;
v___y_3090_ = v___y_3079_;
goto v___jp_3086_;
}
}
else
{
lean_del_object(v___x_3084_);
lean_dec(v_a_3082_);
v___y_3087_ = v___y_3076_;
v___y_3088_ = v___y_3077_;
v___y_3089_ = v___y_3078_;
v___y_3090_ = v___y_3079_;
goto v___jp_3086_;
}
v___jp_3086_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3092_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3091_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3092_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3081_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3081_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3107_, v___x_3108_, v___x_3109_, v___x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3116_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_box(0);
v___x_3121_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3122_ = l_Lean_mkConst(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; 
v___x_3133_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3134_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3135_ = lean_box(0);
lean_inc(v_mvarId_3127_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3136_, 0, v_mvarId_3127_);
lean_closure_set(v___f_3136_, 1, v___x_3133_);
lean_closure_set(v___f_3136_, 2, v___x_3134_);
lean_closure_set(v___f_3136_, 3, v___x_3135_);
v___x_3137_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3136_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3149_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
if (lean_obj_tag(v_a_3138_) == 0)
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_mvarId_3127_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_mvarId_3127_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3147_; 
lean_dec(v_mvarId_3127_);
v_val_3145_ = lean_ctor_get(v_a_3138_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v_a_3138_, 1);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_val_3145_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_val_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_mvarId_3127_);
v_a_3150_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3137_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_MVarId_iffOfEq(v_mvarId_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3173_ = l_Lean_mkConst(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3174_, lean_object* v_mvarId_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___x_3188_; uint8_t v_foApprox_3189_; uint8_t v_ctxApprox_3190_; uint8_t v_quasiPatternApprox_3191_; uint8_t v_constApprox_3192_; uint8_t v_isDefEqStuckEx_3193_; uint8_t v_unificationHints_3194_; uint8_t v_proofIrrelevance_3195_; uint8_t v_assignSyntheticOpaque_3196_; uint8_t v_offsetCnstrs_3197_; uint8_t v_etaStruct_3198_; uint8_t v_univApprox_3199_; uint8_t v_iota_3200_; uint8_t v_beta_3201_; uint8_t v_proj_3202_; uint8_t v_zeta_3203_; uint8_t v_zetaDelta_3204_; uint8_t v_zetaUnused_3205_; uint8_t v_zetaHave_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3294_; 
v___x_3188_ = l_Lean_Meta_Context_config(v___y_3176_);
v_foApprox_3189_ = lean_ctor_get_uint8(v___x_3188_, 0);
v_ctxApprox_3190_ = lean_ctor_get_uint8(v___x_3188_, 1);
v_quasiPatternApprox_3191_ = lean_ctor_get_uint8(v___x_3188_, 2);
v_constApprox_3192_ = lean_ctor_get_uint8(v___x_3188_, 3);
v_isDefEqStuckEx_3193_ = lean_ctor_get_uint8(v___x_3188_, 4);
v_unificationHints_3194_ = lean_ctor_get_uint8(v___x_3188_, 5);
v_proofIrrelevance_3195_ = lean_ctor_get_uint8(v___x_3188_, 6);
v_assignSyntheticOpaque_3196_ = lean_ctor_get_uint8(v___x_3188_, 7);
v_offsetCnstrs_3197_ = lean_ctor_get_uint8(v___x_3188_, 8);
v_etaStruct_3198_ = lean_ctor_get_uint8(v___x_3188_, 10);
v_univApprox_3199_ = lean_ctor_get_uint8(v___x_3188_, 11);
v_iota_3200_ = lean_ctor_get_uint8(v___x_3188_, 12);
v_beta_3201_ = lean_ctor_get_uint8(v___x_3188_, 13);
v_proj_3202_ = lean_ctor_get_uint8(v___x_3188_, 14);
v_zeta_3203_ = lean_ctor_get_uint8(v___x_3188_, 15);
v_zetaDelta_3204_ = lean_ctor_get_uint8(v___x_3188_, 16);
v_zetaUnused_3205_ = lean_ctor_get_uint8(v___x_3188_, 17);
v_zetaHave_3206_ = lean_ctor_get_uint8(v___x_3188_, 18);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3208_ = v___x_3188_;
v_isShared_3209_ = v_isSharedCheck_3294_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v___x_3188_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3294_;
goto v_resetjp_3207_;
}
v___jp_3181_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3187_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3186_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3187_;
}
v_resetjp_3207_:
{
uint8_t v_trackZetaDelta_3210_; lean_object* v_zetaDeltaSet_3211_; lean_object* v_lctx_3212_; lean_object* v_localInstances_3213_; lean_object* v_defEqCtx_x3f_3214_; lean_object* v_synthPendingDepth_3215_; lean_object* v_canUnfold_x3f_3216_; uint8_t v_univApprox_3217_; uint8_t v_inTypeClassResolution_3218_; uint8_t v_cacheInferType_3219_; lean_object* v_config_3221_; 
v_trackZetaDelta_3210_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7);
v_zetaDeltaSet_3211_ = lean_ctor_get(v___y_3176_, 1);
v_lctx_3212_ = lean_ctor_get(v___y_3176_, 2);
v_localInstances_3213_ = lean_ctor_get(v___y_3176_, 3);
v_defEqCtx_x3f_3214_ = lean_ctor_get(v___y_3176_, 4);
v_synthPendingDepth_3215_ = lean_ctor_get(v___y_3176_, 5);
v_canUnfold_x3f_3216_ = lean_ctor_get(v___y_3176_, 6);
v_univApprox_3217_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3218_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 2);
v_cacheInferType_3219_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 3);
if (v_isShared_3209_ == 0)
{
v_config_3221_ = v___x_3208_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 0, v_foApprox_3189_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 1, v_ctxApprox_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 2, v_quasiPatternApprox_3191_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 3, v_constApprox_3192_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 4, v_isDefEqStuckEx_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 5, v_unificationHints_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 6, v_proofIrrelevance_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 7, v_assignSyntheticOpaque_3196_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 8, v_offsetCnstrs_3197_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 10, v_etaStruct_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 11, v_univApprox_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 12, v_iota_3200_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 13, v_beta_3201_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 14, v_proj_3202_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 15, v_zeta_3203_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 16, v_zetaDelta_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 17, v_zetaUnused_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 18, v_zetaHave_3206_);
v_config_3221_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
uint64_t v___x_3222_; uint64_t v___x_3223_; uint64_t v___x_3224_; uint64_t v___x_3225_; uint64_t v___x_3226_; uint64_t v_key_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_ctor_set_uint8(v_config_3221_, 9, v___x_3174_);
v___x_3222_ = l_Lean_Meta_Context_configKey(v___y_3176_);
v___x_3223_ = 3ULL;
v___x_3224_ = lean_uint64_shift_right(v___x_3222_, v___x_3223_);
v___x_3225_ = lean_uint64_shift_left(v___x_3224_, v___x_3223_);
v___x_3226_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3174_);
v_key_3227_ = lean_uint64_lor(v___x_3225_, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3228_, 0, v_config_3221_);
lean_ctor_set_uint64(v___x_3228_, sizeof(void*)*1, v_key_3227_);
lean_inc(v_canUnfold_x3f_3216_);
lean_inc(v_synthPendingDepth_3215_);
lean_inc(v_defEqCtx_x3f_3214_);
lean_inc_ref(v_localInstances_3213_);
lean_inc_ref(v_lctx_3212_);
lean_inc(v_zetaDeltaSet_3211_);
v___x_3229_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v_zetaDeltaSet_3211_);
lean_ctor_set(v___x_3229_, 2, v_lctx_3212_);
lean_ctor_set(v___x_3229_, 3, v_localInstances_3213_);
lean_ctor_set(v___x_3229_, 4, v_defEqCtx_x3f_3214_);
lean_ctor_set(v___x_3229_, 5, v_synthPendingDepth_3215_);
lean_ctor_set(v___x_3229_, 6, v_canUnfold_x3f_3216_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7, v_trackZetaDelta_3210_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 1, v_univApprox_3217_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3218_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 3, v_cacheInferType_3219_);
lean_inc(v_mvarId_3175_);
v___x_3230_ = l_Lean_MVarId_getType_x27(v_mvarId_3175_, v___x_3229_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec_ref_known(v___x_3229_, 7);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3233_ = lean_unsigned_to_nat(3u);
v___x_3234_ = l_Lean_Expr_isAppOfArity(v_a_3231_, v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_a_3231_);
lean_dec(v_mvarId_3175_);
v___x_3260_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3261_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3260_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = l_Lean_Expr_appFn_x21(v_a_3231_);
lean_dec(v_a_3231_);
v___x_3263_ = l_Lean_Expr_appArg_x21(v___x_3262_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = l_Lean_Meta_isProp(v___x_3263_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; uint8_t v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = lean_unbox(v_a_3265_);
lean_dec(v_a_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec(v_mvarId_3175_);
v___x_3267_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3268_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3267_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
goto v___jp_3235_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_mvarId_3175_);
v_a_3277_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3264_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3264_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3236_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3237_ = 0;
v___x_3238_ = 0;
v___x_3239_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3239_, 0, v___x_3237_);
lean_ctor_set_uint8(v___x_3239_, 1, v___x_3234_);
lean_ctor_set_uint8(v___x_3239_, 2, v___x_3238_);
lean_ctor_set_uint8(v___x_3239_, 3, v___x_3234_);
v___x_3240_ = lean_box(0);
v___x_3241_ = l_Lean_MVarId_apply(v_mvarId_3175_, v___x_3236_, v___x_3239_, v___x_3240_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3251_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3251_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3251_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
if (lean_obj_tag(v_a_3242_) == 1)
{
lean_object* v_tail_3246_; 
v_tail_3246_ = lean_ctor_get(v_a_3242_, 1);
if (lean_obj_tag(v_tail_3246_) == 0)
{
lean_object* v_head_3247_; lean_object* v___x_3249_; 
v_head_3247_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_head_3247_);
lean_dec_ref_known(v_a_3242_, 2);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v_head_3247_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_head_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
else
{
lean_dec_ref_known(v_a_3242_, 2);
lean_del_object(v___x_3244_);
v___y_3182_ = v___y_3176_;
v___y_3183_ = v___y_3177_;
v___y_3184_ = v___y_3178_;
v___y_3185_ = v___y_3179_;
goto v___jp_3181_;
}
}
else
{
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
v___y_3182_ = v___y_3176_;
v___y_3183_ = v___y_3177_;
v___y_3184_ = v___y_3178_;
v___y_3185_ = v___y_3179_;
goto v___jp_3181_;
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
v_a_3252_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3241_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3241_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_mvarId_3175_);
v_a_3285_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3230_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3230_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3295_, lean_object* v_mvarId_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v___x_2435__boxed_3302_; lean_object* v_res_3303_; 
v___x_2435__boxed_3302_ = lean_unbox(v___x_3295_);
v_res_3303_ = l_Lean_MVarId_propext___lam__0(v___x_2435__boxed_3302_, v_mvarId_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___f_3312_; lean_object* v___x_3313_; 
v___x_3310_ = 2;
v___x_3311_ = lean_box(v___x_3310_);
lean_inc(v_mvarId_3304_);
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3312_, 0, v___x_3311_);
lean_closure_set(v___f_3312_, 1, v_mvarId_3304_);
v___x_3313_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3312_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3325_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3325_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3325_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
if (lean_obj_tag(v_a_3314_) == 0)
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_mvarId_3304_);
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_mvarId_3304_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3323_; 
lean_dec(v_mvarId_3304_);
v_val_3321_ = lean_ctor_get(v_a_3314_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v_a_3314_, 1);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_val_3321_);
v___x_3323_ = v___x_3316_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_mvarId_3304_);
v_a_3326_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3313_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3313_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_MVarId_propext(v_mvarId_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3340_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3341_; uint64_t v___x_3342_; 
v___x_3341_ = 2;
v___x_3342_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3349_, lean_object* v___x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
lean_inc(v_mvarId_3349_);
v___x_3356_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3349_, v___x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; uint8_t v_foApprox_3358_; uint8_t v_ctxApprox_3359_; uint8_t v_quasiPatternApprox_3360_; uint8_t v_constApprox_3361_; uint8_t v_isDefEqStuckEx_3362_; uint8_t v_unificationHints_3363_; uint8_t v_proofIrrelevance_3364_; uint8_t v_assignSyntheticOpaque_3365_; uint8_t v_offsetCnstrs_3366_; uint8_t v_etaStruct_3367_; uint8_t v_univApprox_3368_; uint8_t v_iota_3369_; uint8_t v_beta_3370_; uint8_t v_proj_3371_; uint8_t v_zeta_3372_; uint8_t v_zetaDelta_3373_; uint8_t v_zetaUnused_3374_; uint8_t v_zetaHave_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref_known(v___x_3356_, 1);
v___x_3357_ = l_Lean_Meta_Context_config(v___y_3351_);
v_foApprox_3358_ = lean_ctor_get_uint8(v___x_3357_, 0);
v_ctxApprox_3359_ = lean_ctor_get_uint8(v___x_3357_, 1);
v_quasiPatternApprox_3360_ = lean_ctor_get_uint8(v___x_3357_, 2);
v_constApprox_3361_ = lean_ctor_get_uint8(v___x_3357_, 3);
v_isDefEqStuckEx_3362_ = lean_ctor_get_uint8(v___x_3357_, 4);
v_unificationHints_3363_ = lean_ctor_get_uint8(v___x_3357_, 5);
v_proofIrrelevance_3364_ = lean_ctor_get_uint8(v___x_3357_, 6);
v_assignSyntheticOpaque_3365_ = lean_ctor_get_uint8(v___x_3357_, 7);
v_offsetCnstrs_3366_ = lean_ctor_get_uint8(v___x_3357_, 8);
v_etaStruct_3367_ = lean_ctor_get_uint8(v___x_3357_, 10);
v_univApprox_3368_ = lean_ctor_get_uint8(v___x_3357_, 11);
v_iota_3369_ = lean_ctor_get_uint8(v___x_3357_, 12);
v_beta_3370_ = lean_ctor_get_uint8(v___x_3357_, 13);
v_proj_3371_ = lean_ctor_get_uint8(v___x_3357_, 14);
v_zeta_3372_ = lean_ctor_get_uint8(v___x_3357_, 15);
v_zetaDelta_3373_ = lean_ctor_get_uint8(v___x_3357_, 16);
v_zetaUnused_3374_ = lean_ctor_get_uint8(v___x_3357_, 17);
v_zetaHave_3375_ = lean_ctor_get_uint8(v___x_3357_, 18);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3377_ = v___x_3357_;
v_isShared_3378_ = v_isSharedCheck_3445_;
goto v_resetjp_3376_;
}
else
{
lean_dec(v___x_3357_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3445_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v_trackZetaDelta_3379_; lean_object* v_zetaDeltaSet_3380_; lean_object* v_lctx_3381_; lean_object* v_localInstances_3382_; lean_object* v_defEqCtx_x3f_3383_; lean_object* v_synthPendingDepth_3384_; lean_object* v_canUnfold_x3f_3385_; uint8_t v_univApprox_3386_; uint8_t v_inTypeClassResolution_3387_; uint8_t v_cacheInferType_3388_; uint8_t v___x_3389_; lean_object* v_config_3391_; 
v_trackZetaDelta_3379_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7);
v_zetaDeltaSet_3380_ = lean_ctor_get(v___y_3351_, 1);
v_lctx_3381_ = lean_ctor_get(v___y_3351_, 2);
v_localInstances_3382_ = lean_ctor_get(v___y_3351_, 3);
v_defEqCtx_x3f_3383_ = lean_ctor_get(v___y_3351_, 4);
v_synthPendingDepth_3384_ = lean_ctor_get(v___y_3351_, 5);
v_canUnfold_x3f_3385_ = lean_ctor_get(v___y_3351_, 6);
v_univApprox_3386_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3387_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 2);
v_cacheInferType_3388_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 3);
v___x_3389_ = 2;
if (v_isShared_3378_ == 0)
{
v_config_3391_ = v___x_3377_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 0, v_foApprox_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 1, v_ctxApprox_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 2, v_quasiPatternApprox_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 3, v_constApprox_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 4, v_isDefEqStuckEx_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 5, v_unificationHints_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 6, v_proofIrrelevance_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 7, v_assignSyntheticOpaque_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 8, v_offsetCnstrs_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 10, v_etaStruct_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 11, v_univApprox_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 12, v_iota_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 13, v_beta_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 14, v_proj_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 15, v_zeta_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 16, v_zetaDelta_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 17, v_zetaUnused_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 18, v_zetaHave_3375_);
v_config_3391_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
uint64_t v___x_3392_; uint64_t v___x_3393_; uint64_t v___x_3394_; uint64_t v___x_3395_; uint64_t v___x_3396_; uint64_t v_key_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_ctor_set_uint8(v_config_3391_, 9, v___x_3389_);
v___x_3392_ = l_Lean_Meta_Context_configKey(v___y_3351_);
v___x_3393_ = 3ULL;
v___x_3394_ = lean_uint64_shift_right(v___x_3392_, v___x_3393_);
v___x_3395_ = lean_uint64_shift_left(v___x_3394_, v___x_3393_);
v___x_3396_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3397_ = lean_uint64_lor(v___x_3395_, v___x_3396_);
v___x_3398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3398_, 0, v_config_3391_);
lean_ctor_set_uint64(v___x_3398_, sizeof(void*)*1, v_key_3397_);
lean_inc(v_canUnfold_x3f_3385_);
lean_inc(v_synthPendingDepth_3384_);
lean_inc(v_defEqCtx_x3f_3383_);
lean_inc_ref(v_localInstances_3382_);
lean_inc_ref(v_lctx_3381_);
lean_inc(v_zetaDeltaSet_3380_);
v___x_3399_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_zetaDeltaSet_3380_);
lean_ctor_set(v___x_3399_, 2, v_lctx_3381_);
lean_ctor_set(v___x_3399_, 3, v_localInstances_3382_);
lean_ctor_set(v___x_3399_, 4, v_defEqCtx_x3f_3383_);
lean_ctor_set(v___x_3399_, 5, v_synthPendingDepth_3384_);
lean_ctor_set(v___x_3399_, 6, v_canUnfold_x3f_3385_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7, v_trackZetaDelta_3379_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 1, v_univApprox_3386_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3387_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 3, v_cacheInferType_3388_);
lean_inc(v_mvarId_3349_);
v___x_3400_ = l_Lean_MVarId_getType_x27(v_mvarId_3349_, v___x_3399_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec_ref_known(v___x_3399_, 7);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3403_ = lean_unsigned_to_nat(4u);
v___x_3404_ = l_Lean_Expr_isAppOfArity(v_a_3401_, v___x_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_a_3401_);
lean_dec(v_mvarId_3349_);
v___x_3405_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3406_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3405_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3407_ = l_Lean_Expr_appFn_x21(v_a_3401_);
v___x_3408_ = l_Lean_Expr_appFn_x21(v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = l_Lean_Expr_appArg_x21(v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = l_Lean_Expr_appArg_x21(v_a_3401_);
lean_dec(v_a_3401_);
v___x_3411_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3412_ = lean_unsigned_to_nat(2u);
v___x_3413_ = lean_mk_empty_array_with_capacity(v___x_3412_);
v___x_3414_ = lean_array_push(v___x_3413_, v___x_3409_);
v___x_3415_ = lean_array_push(v___x_3414_, v___x_3410_);
v___x_3416_ = l_Lean_Meta_mkAppM(v___x_3411_, v___x_3415_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3426_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v___x_3418_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3349_, v_a_3417_, v___y_3352_);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___x_3418_, 0);
lean_dec(v_unused_3427_);
v___x_3420_ = v___x_3418_;
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3418_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3422_ = lean_box(v___x_3404_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_mvarId_3349_);
v_a_3428_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3416_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3416_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_mvarId_3349_);
v_a_3436_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3400_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3400_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_mvarId_3349_);
v_a_3446_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3356_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3356_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3454_, lean_object* v___x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3454_, v___x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3482_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 0)
{
uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3473_ = 0;
v___x_3474_ = lean_box(v___x_3473_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3474_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; 
v_val_3478_ = lean_ctor_get(v_a_3469_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v_a_3469_, 1);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v_val_3478_);
v___x_3480_ = v___x_3471_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_val_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_a_3483_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3468_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3468_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___f_3509_; lean_object* v___x_3510_; 
v___x_3507_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3501_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3508_, 0, v_mvarId_3501_);
lean_closure_set(v___f_3508_, 1, v___x_3507_);
v___f_3509_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3509_, 0, v___f_3508_);
v___x_3510_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3501_, v___f_3509_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3522_, lean_object* v___x_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; 
lean_inc(v_mvarId_3522_);
v___x_3529_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3522_, v___x_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v___x_3530_; uint8_t v_foApprox_3531_; uint8_t v_ctxApprox_3532_; uint8_t v_quasiPatternApprox_3533_; uint8_t v_constApprox_3534_; uint8_t v_isDefEqStuckEx_3535_; uint8_t v_unificationHints_3536_; uint8_t v_proofIrrelevance_3537_; uint8_t v_assignSyntheticOpaque_3538_; uint8_t v_offsetCnstrs_3539_; uint8_t v_etaStruct_3540_; uint8_t v_univApprox_3541_; uint8_t v_iota_3542_; uint8_t v_beta_3543_; uint8_t v_proj_3544_; uint8_t v_zeta_3545_; uint8_t v_zetaDelta_3546_; uint8_t v_zetaUnused_3547_; uint8_t v_zetaHave_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref_known(v___x_3529_, 1);
v___x_3530_ = l_Lean_Meta_Context_config(v___y_3524_);
v_foApprox_3531_ = lean_ctor_get_uint8(v___x_3530_, 0);
v_ctxApprox_3532_ = lean_ctor_get_uint8(v___x_3530_, 1);
v_quasiPatternApprox_3533_ = lean_ctor_get_uint8(v___x_3530_, 2);
v_constApprox_3534_ = lean_ctor_get_uint8(v___x_3530_, 3);
v_isDefEqStuckEx_3535_ = lean_ctor_get_uint8(v___x_3530_, 4);
v_unificationHints_3536_ = lean_ctor_get_uint8(v___x_3530_, 5);
v_proofIrrelevance_3537_ = lean_ctor_get_uint8(v___x_3530_, 6);
v_assignSyntheticOpaque_3538_ = lean_ctor_get_uint8(v___x_3530_, 7);
v_offsetCnstrs_3539_ = lean_ctor_get_uint8(v___x_3530_, 8);
v_etaStruct_3540_ = lean_ctor_get_uint8(v___x_3530_, 10);
v_univApprox_3541_ = lean_ctor_get_uint8(v___x_3530_, 11);
v_iota_3542_ = lean_ctor_get_uint8(v___x_3530_, 12);
v_beta_3543_ = lean_ctor_get_uint8(v___x_3530_, 13);
v_proj_3544_ = lean_ctor_get_uint8(v___x_3530_, 14);
v_zeta_3545_ = lean_ctor_get_uint8(v___x_3530_, 15);
v_zetaDelta_3546_ = lean_ctor_get_uint8(v___x_3530_, 16);
v_zetaUnused_3547_ = lean_ctor_get_uint8(v___x_3530_, 17);
v_zetaHave_3548_ = lean_ctor_get_uint8(v___x_3530_, 18);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3550_ = v___x_3530_;
v_isShared_3551_ = v_isSharedCheck_3617_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v___x_3530_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3617_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
uint8_t v_trackZetaDelta_3552_; lean_object* v_zetaDeltaSet_3553_; lean_object* v_lctx_3554_; lean_object* v_localInstances_3555_; lean_object* v_defEqCtx_x3f_3556_; lean_object* v_synthPendingDepth_3557_; lean_object* v_canUnfold_x3f_3558_; uint8_t v_univApprox_3559_; uint8_t v_inTypeClassResolution_3560_; uint8_t v_cacheInferType_3561_; uint8_t v___x_3562_; lean_object* v_config_3564_; 
v_trackZetaDelta_3552_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7);
v_zetaDeltaSet_3553_ = lean_ctor_get(v___y_3524_, 1);
v_lctx_3554_ = lean_ctor_get(v___y_3524_, 2);
v_localInstances_3555_ = lean_ctor_get(v___y_3524_, 3);
v_defEqCtx_x3f_3556_ = lean_ctor_get(v___y_3524_, 4);
v_synthPendingDepth_3557_ = lean_ctor_get(v___y_3524_, 5);
v_canUnfold_x3f_3558_ = lean_ctor_get(v___y_3524_, 6);
v_univApprox_3559_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3560_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 2);
v_cacheInferType_3561_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 3);
v___x_3562_ = 2;
if (v_isShared_3551_ == 0)
{
v_config_3564_ = v___x_3550_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 0, v_foApprox_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 1, v_ctxApprox_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 2, v_quasiPatternApprox_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 3, v_constApprox_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 4, v_isDefEqStuckEx_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 5, v_unificationHints_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 6, v_proofIrrelevance_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 7, v_assignSyntheticOpaque_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 8, v_offsetCnstrs_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 10, v_etaStruct_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 11, v_univApprox_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 12, v_iota_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 13, v_beta_3543_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 14, v_proj_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 15, v_zeta_3545_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 16, v_zetaDelta_3546_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 17, v_zetaUnused_3547_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 18, v_zetaHave_3548_);
v_config_3564_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
uint64_t v___x_3565_; uint64_t v___x_3566_; uint64_t v___x_3567_; uint64_t v___x_3568_; uint64_t v___x_3569_; uint64_t v_key_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_ctor_set_uint8(v_config_3564_, 9, v___x_3562_);
v___x_3565_ = l_Lean_Meta_Context_configKey(v___y_3524_);
v___x_3566_ = 3ULL;
v___x_3567_ = lean_uint64_shift_right(v___x_3565_, v___x_3566_);
v___x_3568_ = lean_uint64_shift_left(v___x_3567_, v___x_3566_);
v___x_3569_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3570_ = lean_uint64_lor(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3571_, 0, v_config_3564_);
lean_ctor_set_uint64(v___x_3571_, sizeof(void*)*1, v_key_3570_);
lean_inc(v_canUnfold_x3f_3558_);
lean_inc(v_synthPendingDepth_3557_);
lean_inc(v_defEqCtx_x3f_3556_);
lean_inc_ref(v_localInstances_3555_);
lean_inc_ref(v_lctx_3554_);
lean_inc(v_zetaDeltaSet_3553_);
v___x_3572_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v_zetaDeltaSet_3553_);
lean_ctor_set(v___x_3572_, 2, v_lctx_3554_);
lean_ctor_set(v___x_3572_, 3, v_localInstances_3555_);
lean_ctor_set(v___x_3572_, 4, v_defEqCtx_x3f_3556_);
lean_ctor_set(v___x_3572_, 5, v_synthPendingDepth_3557_);
lean_ctor_set(v___x_3572_, 6, v_canUnfold_x3f_3558_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7, v_trackZetaDelta_3552_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 1, v_univApprox_3559_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3560_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 3, v_cacheInferType_3561_);
lean_inc(v_mvarId_3522_);
v___x_3573_ = l_Lean_MVarId_getType_x27(v_mvarId_3522_, v___x_3572_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec_ref_known(v___x_3572_, 7);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3576_ = lean_unsigned_to_nat(3u);
v___x_3577_ = l_Lean_Expr_isAppOfArity(v_a_3574_, v___x_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec(v_a_3574_);
lean_dec(v_mvarId_3522_);
v___x_3578_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3579_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3578_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3580_ = l_Lean_Expr_appFn_x21(v_a_3574_);
v___x_3581_ = l_Lean_Expr_appArg_x21(v___x_3580_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l_Lean_Expr_appArg_x21(v_a_3574_);
lean_dec(v_a_3574_);
v___x_3583_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3584_ = lean_unsigned_to_nat(2u);
v___x_3585_ = lean_mk_empty_array_with_capacity(v___x_3584_);
v___x_3586_ = lean_array_push(v___x_3585_, v___x_3581_);
v___x_3587_ = lean_array_push(v___x_3586_, v___x_3582_);
v___x_3588_ = l_Lean_Meta_mkAppM(v___x_3583_, v___x_3587_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3598_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3522_, v_a_3589_, v___y_3525_);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3590_, 0);
lean_dec(v_unused_3599_);
v___x_3592_ = v___x_3590_;
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
else
{
lean_dec(v___x_3590_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_box(v___x_3577_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3594_);
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_mvarId_3522_);
v_a_3600_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3588_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3588_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v_mvarId_3522_);
v_a_3608_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3573_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3573_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v_mvarId_3522_);
v_a_3618_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3529_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3529_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3626_, lean_object* v___x_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3626_, v___x_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; 
v___x_3643_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3637_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3644_, 0, v_mvarId_3637_);
lean_closure_set(v___f_3644_, 1, v___x_3643_);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3645_, 0, v___f_3644_);
v___x_3646_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3637_, v___f_3645_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
return v_res_3653_;
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
