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
size_t v_x_3014__boxed_655_; uint8_t v_res_656_; lean_object* v_r_657_; 
v_x_3014__boxed_655_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_656_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_652_, v_x_3014__boxed_655_, v_x_654_);
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
uint8_t v___x_734_; 
v___x_734_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
if (v___x_734_ == 0)
{
if (v___x_719_ == 0)
{
goto v___jp_727_;
}
else
{
lean_del_object(v___x_700_);
goto v___jp_731_;
}
}
else
{
goto v___jp_727_;
}
}
else
{
lean_dec(v_a_726_);
lean_del_object(v___x_700_);
goto v___jp_731_;
}
v___jp_727_:
{
lean_object* v___x_729_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_717_);
v___x_729_ = v___x_700_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_717_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
v_a_691_ = v___x_729_;
goto v___jp_690_;
}
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc(v_a_723_);
v___x_732_ = lean_array_push(v_fst_698_, v_a_723_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_717_);
v_a_691_ = v___x_733_;
goto v___jp_690_;
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
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_get_size(v_a_766_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_inc(v_mvarId_764_);
lean_inc(v_tacticName_763_);
v___x_775_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_763_, v_mvarId_764_, v_allowSynthFailures_765_, v_a_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec_ref(v_a_766_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v_a_766_ = v_a_776_;
goto _start;
}
else
{
lean_dec(v_mvarId_764_);
lean_dec(v_tacticName_763_);
return v___x_775_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_mvarId_764_);
lean_dec(v_tacticName_763_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_a_766_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_779_, lean_object* v_mvarId_780_, lean_object* v_allowSynthFailures_781_, lean_object* v_a_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v_allowSynthFailures_boxed_788_; lean_object* v_res_789_; 
v_allowSynthFailures_boxed_788_ = lean_unbox(v_allowSynthFailures_781_);
v_res_789_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_779_, v_mvarId_780_, v_allowSynthFailures_boxed_788_, v_a_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_790_, lean_object* v_mvarId_791_, lean_object* v_mvarsNew_792_, lean_object* v_binderInfos_793_, uint8_t v_synthAssignedInstances_794_, uint8_t v_allowSynthFailures_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_todo_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v_todo_802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_803_ = lean_array_get_size(v_binderInfos_793_);
v___x_804_ = l_Array_toSubarray___redArg(v_binderInfos_793_, v___x_801_, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_todo_802_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v_sz_806_ = lean_array_size(v_mvarsNew_792_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_794_, v_mvarsNew_792_, v_sz_806_, v___x_807_, v___x_805_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_fst_810_; lean_object* v___x_811_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_fst_810_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_fst_810_);
lean_dec(v_a_809_);
v___x_811_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_790_, v_mvarId_791_, v_allowSynthFailures_795_, v_fst_810_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_811_, 0);
lean_dec(v_unused_820_);
v___x_813_ = v___x_811_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_dec(v___x_811_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_811_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_mvarId_791_);
lean_dec(v_tacticName_790_);
v_a_829_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_808_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_808_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_837_, lean_object* v_mvarId_838_, lean_object* v_mvarsNew_839_, lean_object* v_binderInfos_840_, lean_object* v_synthAssignedInstances_841_, lean_object* v_allowSynthFailures_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_848_; uint8_t v_allowSynthFailures_boxed_849_; lean_object* v_res_850_; 
v_synthAssignedInstances_boxed_848_ = lean_unbox(v_synthAssignedInstances_841_);
v_allowSynthFailures_boxed_849_ = lean_unbox(v_allowSynthFailures_842_);
v_res_850_ = l_Lean_Meta_synthAppInstances(v_tacticName_837_, v_mvarId_838_, v_mvarsNew_839_, v_binderInfos_840_, v_synthAssignedInstances_boxed_848_, v_allowSynthFailures_boxed_849_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec_ref(v_mvarsNew_839_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_851_, v___y_853_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v_mvarId_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_865_, lean_object* v_mvarId_866_, uint8_t v_allowSynthFailures_867_, lean_object* v_inst_868_, lean_object* v_a_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_865_, v_mvarId_866_, v_allowSynthFailures_867_, v_a_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_876_, lean_object* v_mvarId_877_, lean_object* v_allowSynthFailures_878_, lean_object* v_inst_879_, lean_object* v_a_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v_allowSynthFailures_boxed_886_; lean_object* v_res_887_; 
v_allowSynthFailures_boxed_886_ = lean_unbox(v_allowSynthFailures_878_);
v_res_887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_876_, v_mvarId_877_, v_allowSynthFailures_boxed_886_, v_inst_879_, v_a_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
uint8_t v_res_895_; lean_object* v_r_896_; 
v_res_895_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_892_, v_x_893_, v_x_894_);
lean_dec(v_x_894_);
lean_dec_ref(v_x_893_);
v_r_896_ = lean_box(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, size_t v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_898_, v_x_899_, v_x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_3348__boxed_906_; uint8_t v_res_907_; lean_object* v_r_908_; 
v_x_3348__boxed_906_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_907_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_902_, v_x_903_, v_x_3348__boxed_906_, v_x_905_);
lean_dec(v_x_905_);
lean_dec_ref(v_x_903_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_909_, lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_heq_912_, lean_object* v_i_913_, lean_object* v_k_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_910_, v_i_913_, v_k_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_heq_919_, lean_object* v_i_920_, lean_object* v_k_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_916_, v_keys_917_, v_vals_918_, v_heq_919_, v_i_920_, v_k_921_);
lean_dec(v_k_921_);
lean_dec_ref(v_vals_918_);
lean_dec_ref(v_keys_917_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_924_, lean_object* v_binderInfos_925_, lean_object* v_a_926_, lean_object* v_n_927_, lean_object* v_i_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_zero_934_; uint8_t v_isZero_935_; 
v_zero_934_ = lean_unsigned_to_nat(0u);
v_isZero_935_ = lean_nat_dec_eq(v_i_928_, v_zero_934_);
if (v_isZero_935_ == 1)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_i_928_);
lean_dec(v_a_926_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
else
{
lean_object* v_one_938_; lean_object* v_n_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_a_945_; uint8_t v___x_946_; 
v_one_938_ = lean_unsigned_to_nat(1u);
v_n_939_ = lean_nat_sub(v_i_928_, v_one_938_);
lean_dec(v_i_928_);
v___x_940_ = lean_nat_sub(v_n_927_, v_n_939_);
v___x_941_ = lean_nat_sub(v___x_940_, v_one_938_);
lean_dec(v___x_940_);
v___x_942_ = lean_array_fget_borrowed(v_newMVars_924_, v___x_941_);
v___x_943_ = l_Lean_Expr_mvarId_x21(v___x_942_);
v___x_944_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_943_, v___y_930_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v___x_944_);
v___x_946_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_947_ = 0;
v___x_948_ = lean_box(v___x_947_);
v___x_949_ = lean_array_get(v___x_948_, v_binderInfos_925_, v___x_941_);
lean_dec(v___x_941_);
lean_dec(v___x_948_);
v___x_950_ = lean_unbox(v___x_949_);
lean_dec(v___x_949_);
v___x_951_ = l_Lean_BinderInfo_isInstImplicit(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_inc(v___x_943_);
v___x_952_ = l_Lean_MVarId_getTag(v___x_943_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
lean_inc(v_a_926_);
v___x_954_ = l_Lean_Meta_appendTag(v_a_926_, v_a_953_);
v___x_955_ = l_Lean_MVarId_setTag___redArg(v___x_943_, v___x_954_, v___y_930_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref_known(v___x_955_, 1);
v_i_928_ = v_n_939_;
goto _start;
}
else
{
lean_dec(v_n_939_);
lean_dec(v_a_926_);
return v___x_955_;
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v___x_943_);
lean_dec(v_n_939_);
lean_dec(v_a_926_);
v_a_957_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_952_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_952_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_dec(v___x_943_);
v_i_928_ = v_n_939_;
goto _start;
}
}
else
{
lean_dec(v___x_943_);
lean_dec(v___x_941_);
v_i_928_ = v_n_939_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_967_, lean_object* v_binderInfos_968_, lean_object* v_a_969_, lean_object* v_n_970_, lean_object* v_i_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_967_, v_binderInfos_968_, v_a_969_, v_n_970_, v_i_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v_n_970_);
lean_dec_ref(v_binderInfos_968_);
lean_dec_ref(v_newMVars_967_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_978_, lean_object* v_newMVars_979_, lean_object* v_binderInfos_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_MVarId_getTag(v_mvarId_978_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1005_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_991_ = lean_array_get_size(v_newMVars_979_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_dec_eq(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_Name_isAnonymous(v_a_987_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_del_object(v___x_989_);
v___x_995_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_979_, v_binderInfos_980_, v_a_987_, v___x_991_, v___x_991_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v_a_987_);
v___x_996_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_996_);
v___x_998_ = v___x_989_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_del_object(v___x_989_);
v___x_1000_ = l_Lean_instInhabitedExpr;
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = lean_array_get_borrowed(v___x_1000_, v_newMVars_979_, v___x_1001_);
v___x_1003_ = l_Lean_Expr_mvarId_x21(v___x_1002_);
v___x_1004_ = l_Lean_MVarId_setTag___redArg(v___x_1003_, v_a_987_, v_a_982_);
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_986_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_986_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1014_, lean_object* v_newMVars_1015_, lean_object* v_binderInfos_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Meta_appendParentTag(v_mvarId_1014_, v_newMVars_1015_, v_binderInfos_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec_ref(v_binderInfos_1016_);
lean_dec_ref(v_newMVars_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1023_, lean_object* v_binderInfos_1024_, lean_object* v_a_1025_, lean_object* v_n_1026_, lean_object* v_i_1027_, lean_object* v_a_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1023_, v_binderInfos_1024_, v_a_1025_, v_n_1026_, v_i_1027_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1035_, lean_object* v_binderInfos_1036_, lean_object* v_a_1037_, lean_object* v_n_1038_, lean_object* v_i_1039_, lean_object* v_a_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1035_, v_binderInfos_1036_, v_a_1037_, v_n_1038_, v_i_1039_, v_a_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v_n_1038_);
lean_dec_ref(v_binderInfos_1036_);
lean_dec_ref(v_newMVars_1035_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1047_, lean_object* v_mvarId_1048_, lean_object* v_newMVars_1049_, lean_object* v_binderInfos_1050_, uint8_t v_synthAssignedInstances_1051_, uint8_t v_allowSynthFailures_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_synthAppInstances(v_tacticName_1047_, v_mvarId_1048_, v_newMVars_1049_, v_binderInfos_1050_, v_synthAssignedInstances_1051_, v_allowSynthFailures_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1059_, lean_object* v_mvarId_1060_, lean_object* v_newMVars_1061_, lean_object* v_binderInfos_1062_, lean_object* v_synthAssignedInstances_1063_, lean_object* v_allowSynthFailures_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1070_; uint8_t v_allowSynthFailures_boxed_1071_; lean_object* v_res_1072_; 
v_synthAssignedInstances_boxed_1070_ = lean_unbox(v_synthAssignedInstances_1063_);
v_allowSynthFailures_boxed_1071_ = lean_unbox(v_allowSynthFailures_1064_);
v_res_1072_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1059_, v_mvarId_1060_, v_newMVars_1061_, v_binderInfos_1062_, v_synthAssignedInstances_boxed_1070_, v_allowSynthFailures_boxed_1071_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec_ref(v_newMVars_1061_);
return v_res_1072_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1073_, lean_object* v_mvarId_1074_){
_start:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = l_Lean_Expr_mvarId_x21(v_mvar_1073_);
v___x_1076_ = l_Lean_instBEqMVarId_beq(v_mvarId_1074_, v___x_1075_);
lean_dec(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1077_, lean_object* v_mvarId_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1077_, v_mvarId_1078_);
lean_dec(v_mvarId_1078_);
lean_dec_ref(v_mvar_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1081_, lean_object* v_as_1082_, size_t v_i_1083_, size_t v_stop_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_usize_dec_eq(v_i_1083_, v_stop_1084_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; uint8_t v_a_1093_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1091_ = 1;
v___x_1099_ = lean_array_uget_borrowed(v_as_1082_, v_i_1083_);
v___x_1100_ = lean_expr_eqv(v_mvar_1081_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___x_1099_);
v___x_1101_ = lean_infer_type(v___x_1099_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1113_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc_ref(v_mvar_1081_);
v___f_1106_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1106_, 0, v_mvar_1081_);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Lean_FindMVar_main(v___f_1106_, v_a_1102_, v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_del_object(v___x_1104_);
v_a_1093_ = v___x_1100_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec_ref_known(v___x_1108_, 1);
lean_dec_ref(v_mvar_1081_);
v___x_1109_ = lean_box(v___x_1091_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1109_);
v___x_1111_ = v___x_1104_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_mvar_1081_);
v_a_1114_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1101_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1101_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
v_a_1093_ = v___x_1090_;
goto v___jp_1092_;
}
v___jp_1092_:
{
if (v_a_1093_ == 0)
{
size_t v___x_1094_; size_t v___x_1095_; 
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_add(v_i_1083_, v___x_1094_);
v_i_1083_ = v___x_1095_;
goto _start;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_mvar_1081_);
v___x_1097_ = lean_box(v___x_1091_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
else
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref(v_mvar_1081_);
v___x_1122_ = 0;
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1125_, lean_object* v_as_1126_, lean_object* v_i_1127_, lean_object* v_stop_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
size_t v_i_boxed_1134_; size_t v_stop_boxed_1135_; lean_object* v_res_1136_; 
v_i_boxed_1134_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_stop_boxed_1135_ = lean_unbox_usize(v_stop_1128_);
lean_dec(v_stop_1128_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1125_, v_as_1126_, v_i_boxed_1134_, v_stop_boxed_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1126_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1137_, lean_object* v_otherMVars_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_array_get_size(v_otherMVars_1138_);
v___x_1146_ = lean_nat_dec_lt(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_mvar_1137_);
v___x_1147_ = lean_box(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
else
{
if (v___x_1146_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_mvar_1137_);
v___x_1149_ = lean_box(v___x_1146_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
else
{
size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_of_nat(v___x_1145_);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1137_, v_otherMVars_1138_, v___x_1151_, v___x_1152_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1154_, lean_object* v_otherMVars_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1154_, v_otherMVars_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_otherMVars_1155_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1162_, lean_object* v_as_1163_, size_t v_i_1164_, size_t v_stop_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_eq(v_i_1164_, v_stop_1165_);
if (v___x_1172_ == 0)
{
lean_object* v_fst_1173_; lean_object* v_snd_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1204_; 
v_fst_1173_ = lean_ctor_get(v_b_1166_, 0);
v_snd_1174_ = lean_ctor_get(v_b_1166_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_b_1166_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1176_ = v_b_1166_;
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snd_1174_);
lean_inc(v_fst_1173_);
lean_dec(v_b_1166_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v_currMVarId_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_array_uget_borrowed(v_as_1163_, v_i_1164_);
v_currMVarId_1179_ = l_Lean_Expr_mvarId_x21(v___x_1178_);
lean_inc(v___x_1178_);
v___x_1180_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1178_, v_mvars_1162_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_a_1183_; uint8_t v___x_1187_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1187_ = lean_unbox(v_a_1181_);
lean_dec(v_a_1181_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_array_push(v_fst_1173_, v_currMVarId_1179_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1188_);
v___x_1190_ = v___x_1176_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1174_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_a_1183_ = v___x_1190_;
goto v___jp_1182_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_array_push(v_snd_1174_, v_currMVarId_1179_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1192_);
v___x_1194_ = v___x_1176_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_fst_1173_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
v_a_1183_ = v___x_1194_;
goto v___jp_1182_;
}
}
v___jp_1182_:
{
size_t v___x_1184_; size_t v___x_1185_; 
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1164_, v___x_1184_);
v_i_1164_ = v___x_1185_;
v_b_1166_ = v_a_1183_;
goto _start;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_currMVarId_1179_);
lean_del_object(v___x_1176_);
lean_dec(v_snd_1174_);
lean_dec(v_fst_1173_);
v_a_1196_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1180_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1180_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_b_1166_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1206_, lean_object* v_as_1207_, lean_object* v_i_1208_, lean_object* v_stop_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
size_t v_i_boxed_1216_; size_t v_stop_boxed_1217_; lean_object* v_res_1218_; 
v_i_boxed_1216_ = lean_unbox_usize(v_i_1208_);
lean_dec(v_i_1208_);
v_stop_boxed_1217_ = lean_unbox_usize(v_stop_1209_);
lean_dec(v_stop_1209_);
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1206_, v_as_1207_, v_i_boxed_1216_, v_stop_boxed_1217_, v_b_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v_as_1207_);
lean_dec_ref(v_mvars_1206_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1231_ = lean_array_get_size(v_mvars_1223_);
v___x_1232_ = lean_nat_dec_lt(v___x_1229_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1230_);
return v___x_1233_;
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_le(v___x_1231_, v___x_1231_);
if (v___x_1234_ == 0)
{
if (v___x_1232_ == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1230_);
return v___x_1235_;
}
else
{
size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = ((size_t)0ULL);
v___x_1237_ = lean_usize_of_nat(v___x_1231_);
v___x_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1223_, v_mvars_1223_, v___x_1236_, v___x_1237_, v___x_1230_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
return v___x_1238_;
}
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1231_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1223_, v_mvars_1223_, v___x_1239_, v___x_1240_, v___x_1230_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec_ref(v_mvars_1242_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
if (lean_obj_tag(v_a_1249_) == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = l_List_reverse___redArg(v_a_1250_);
return v___x_1251_;
}
else
{
lean_object* v_head_1252_; lean_object* v_tail_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1262_; 
v_head_1252_ = lean_ctor_get(v_a_1249_, 0);
v_tail_1253_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1255_ = v_a_1249_;
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_tail_1253_);
lean_inc(v_head_1252_);
lean_dec(v_a_1249_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l_Lean_Expr_mvarId_x21(v_head_1252_);
lean_dec(v_head_1252_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v_a_1250_);
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_a_1250_);
v___x_1259_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_a_1249_ = v_tail_1253_;
v_a_1250_ = v___x_1259_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1263_, uint8_t v_x_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
switch(v_x_1264_)
{
case 0:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_mvars_1263_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1283_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1283_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1283_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_fst_1275_ = lean_ctor_get(v_a_1271_, 0);
lean_inc(v_fst_1275_);
v_snd_1276_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_snd_1276_);
lean_dec(v_a_1271_);
v___x_1277_ = lean_array_to_list(v_fst_1275_);
v___x_1278_ = lean_array_to_list(v_snd_1276_);
v___x_1279_ = l_List_appendTR___redArg(v___x_1277_, v___x_1278_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1279_);
v___x_1281_ = v___x_1273_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1270_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1270_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
case 1:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_mvars_1263_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1302_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1302_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1302_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_fst_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_fst_1297_ = lean_ctor_get(v_a_1293_, 0);
lean_inc(v_fst_1297_);
lean_dec(v_a_1293_);
v___x_1298_ = lean_array_to_list(v_fst_1297_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1298_);
v___x_1300_ = v___x_1295_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1292_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1292_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
default: 
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_array_to_list(v_mvars_1263_);
v___x_1312_ = lean_box(0);
v___x_1313_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1311_, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1315_, lean_object* v_x_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
uint8_t v_x_814__boxed_1322_; lean_object* v_res_1323_; 
v_x_814__boxed_1322_ = lean_unbox(v_x_1316_);
v_res_1323_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1315_, v_x_814__boxed_1322_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
if (v_approx_1324_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1325_, v_b_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; uint8_t v_constApprox_1334_; uint8_t v_isDefEqStuckEx_1335_; uint8_t v_unificationHints_1336_; uint8_t v_proofIrrelevance_1337_; uint8_t v_assignSyntheticOpaque_1338_; uint8_t v_offsetCnstrs_1339_; uint8_t v_transparency_1340_; uint8_t v_etaStruct_1341_; uint8_t v_univApprox_1342_; uint8_t v_iota_1343_; uint8_t v_beta_1344_; uint8_t v_proj_1345_; uint8_t v_zeta_1346_; uint8_t v_zetaDelta_1347_; uint8_t v_zetaUnused_1348_; uint8_t v_zetaHave_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1370_; 
v___x_1333_ = l_Lean_Meta_Context_config(v_a_1327_);
v_constApprox_1334_ = lean_ctor_get_uint8(v___x_1333_, 3);
v_isDefEqStuckEx_1335_ = lean_ctor_get_uint8(v___x_1333_, 4);
v_unificationHints_1336_ = lean_ctor_get_uint8(v___x_1333_, 5);
v_proofIrrelevance_1337_ = lean_ctor_get_uint8(v___x_1333_, 6);
v_assignSyntheticOpaque_1338_ = lean_ctor_get_uint8(v___x_1333_, 7);
v_offsetCnstrs_1339_ = lean_ctor_get_uint8(v___x_1333_, 8);
v_transparency_1340_ = lean_ctor_get_uint8(v___x_1333_, 9);
v_etaStruct_1341_ = lean_ctor_get_uint8(v___x_1333_, 10);
v_univApprox_1342_ = lean_ctor_get_uint8(v___x_1333_, 11);
v_iota_1343_ = lean_ctor_get_uint8(v___x_1333_, 12);
v_beta_1344_ = lean_ctor_get_uint8(v___x_1333_, 13);
v_proj_1345_ = lean_ctor_get_uint8(v___x_1333_, 14);
v_zeta_1346_ = lean_ctor_get_uint8(v___x_1333_, 15);
v_zetaDelta_1347_ = lean_ctor_get_uint8(v___x_1333_, 16);
v_zetaUnused_1348_ = lean_ctor_get_uint8(v___x_1333_, 17);
v_zetaHave_1349_ = lean_ctor_get_uint8(v___x_1333_, 18);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1351_ = v___x_1333_;
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v___x_1333_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 3, v_constApprox_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 4, v_isDefEqStuckEx_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 5, v_unificationHints_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 6, v_proofIrrelevance_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 7, v_assignSyntheticOpaque_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 8, v_offsetCnstrs_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 9, v_transparency_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 10, v_etaStruct_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 11, v_univApprox_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 12, v_iota_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 13, v_beta_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 14, v_proj_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 15, v_zeta_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 16, v_zetaDelta_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 17, v_zetaUnused_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, 18, v_zetaHave_1349_);
v___x_1354_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
uint8_t v_trackZetaDelta_1355_; lean_object* v_zetaDeltaSet_1356_; lean_object* v_lctx_1357_; lean_object* v_localInstances_1358_; lean_object* v_defEqCtx_x3f_1359_; lean_object* v_synthPendingDepth_1360_; lean_object* v_canUnfold_x3f_1361_; uint8_t v_univApprox_1362_; uint8_t v_inTypeClassResolution_1363_; uint8_t v_cacheInferType_1364_; uint64_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_ctor_set_uint8(v___x_1354_, 0, v_approx_1324_);
lean_ctor_set_uint8(v___x_1354_, 1, v_approx_1324_);
lean_ctor_set_uint8(v___x_1354_, 2, v_approx_1324_);
v_trackZetaDelta_1355_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*7);
v_zetaDeltaSet_1356_ = lean_ctor_get(v_a_1327_, 1);
v_lctx_1357_ = lean_ctor_get(v_a_1327_, 2);
v_localInstances_1358_ = lean_ctor_get(v_a_1327_, 3);
v_defEqCtx_x3f_1359_ = lean_ctor_get(v_a_1327_, 4);
v_synthPendingDepth_1360_ = lean_ctor_get(v_a_1327_, 5);
v_canUnfold_x3f_1361_ = lean_ctor_get(v_a_1327_, 6);
v_univApprox_1362_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1363_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*7 + 2);
v_cacheInferType_1364_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*7 + 3);
v___x_1365_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1354_);
v___x_1366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1366_, 0, v___x_1354_);
lean_ctor_set_uint64(v___x_1366_, sizeof(void*)*1, v___x_1365_);
lean_inc(v_canUnfold_x3f_1361_);
lean_inc(v_synthPendingDepth_1360_);
lean_inc(v_defEqCtx_x3f_1359_);
lean_inc_ref(v_localInstances_1358_);
lean_inc_ref(v_lctx_1357_);
lean_inc(v_zetaDeltaSet_1356_);
v___x_1367_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v_zetaDeltaSet_1356_);
lean_ctor_set(v___x_1367_, 2, v_lctx_1357_);
lean_ctor_set(v___x_1367_, 3, v_localInstances_1358_);
lean_ctor_set(v___x_1367_, 4, v_defEqCtx_x3f_1359_);
lean_ctor_set(v___x_1367_, 5, v_synthPendingDepth_1360_);
lean_ctor_set(v___x_1367_, 6, v_canUnfold_x3f_1361_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*7, v_trackZetaDelta_1355_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*7 + 1, v_univApprox_1362_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1363_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*7 + 3, v_cacheInferType_1364_);
v___x_1368_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1325_, v_b_1326_, v___x_1367_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec_ref_known(v___x_1367_, 7);
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1371_, lean_object* v_a_1372_, lean_object* v_b_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
uint8_t v_approx_boxed_1379_; lean_object* v_res_1380_; 
v_approx_boxed_1379_ = lean_unbox(v_approx_1371_);
v_res_1380_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1379_, v_a_1372_, v_b_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1381_, lean_object* v_cfg_1382_, lean_object* v_term_x3f_1383_, lean_object* v_targetType_1384_, lean_object* v_eType_1385_, lean_object* v_rangeNumArgs_1386_, lean_object* v_i_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_lower_1393_; lean_object* v_upper_1394_; uint8_t v___x_1395_; 
v_lower_1393_ = lean_ctor_get(v_rangeNumArgs_1386_, 0);
v_upper_1394_ = lean_ctor_get(v_rangeNumArgs_1386_, 1);
v___x_1395_ = lean_nat_dec_lt(v_i_1387_, v_upper_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
lean_dec(v_i_1387_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_nat_dec_eq(v_lower_1393_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; 
lean_inc(v_lower_1393_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_lower_1393_);
v___x_1399_ = 0;
lean_inc_ref(v_eType_1385_);
v___x_1400_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1385_, v___x_1398_, v___x_1399_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_snd_1402_; lean_object* v_snd_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v_snd_1402_ = lean_ctor_get(v_a_1401_, 1);
lean_inc(v_snd_1402_);
lean_dec(v_a_1401_);
v_snd_1403_ = lean_ctor_get(v_snd_1402_, 1);
lean_inc(v_snd_1403_);
lean_dec(v_snd_1402_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_snd_1403_);
v___x_1405_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1381_, v_eType_1385_, v___x_1404_, v_targetType_1384_, v_term_x3f_1383_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
return v___x_1405_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
v_a_1406_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1400_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1400_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1381_, v_eType_1385_, v___x_1414_, v_targetType_1384_, v_term_x3f_1383_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
return v___x_1415_;
}
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Meta_saveState___redArg(v_a_1389_, v_a_1391_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
lean_inc(v_i_1387_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_i_1387_);
v___x_1419_ = 0;
lean_inc_ref(v_eType_1385_);
v___x_1420_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1385_, v___x_1418_, v___x_1419_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v_snd_1422_; lean_object* v_fst_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1463_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v_snd_1422_ = lean_ctor_get(v_a_1421_, 1);
lean_inc(v_snd_1422_);
v_fst_1423_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_fst_1423_);
lean_dec(v_a_1421_);
v_fst_1424_ = lean_ctor_get(v_snd_1422_, 0);
v_snd_1425_ = lean_ctor_get(v_snd_1422_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_snd_1422_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1427_ = v_snd_1422_;
v_isShared_1428_ = v_isSharedCheck_1463_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snd_1425_);
lean_inc(v_fst_1424_);
lean_dec(v_snd_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1463_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint8_t v_approx_1429_; lean_object* v___x_1430_; 
v_approx_1429_ = lean_ctor_get_uint8(v_cfg_1382_, 3);
lean_inc_ref(v_targetType_1384_);
v___x_1430_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1429_, v_snd_1425_, v_targetType_1384_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1454_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1454_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1454_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_del_object(v___x_1433_);
lean_del_object(v___x_1427_);
lean_dec(v_fst_1424_);
lean_dec(v_fst_1423_);
v___x_1436_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1417_, v_a_1389_, v_a_1391_);
lean_dec(v_a_1417_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref_known(v___x_1436_, 1);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_nat_add(v_i_1387_, v___x_1437_);
lean_dec(v_i_1387_);
v_i_1387_ = v___x_1438_;
goto _start;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_i_1387_);
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
v_a_1440_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1436_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1436_);
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
lean_object* v___x_1449_; 
lean_dec(v_a_1417_);
lean_dec(v_i_1387_);
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_fst_1424_);
lean_ctor_set(v___x_1427_, 0, v_fst_1423_);
v___x_1449_ = v___x_1427_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_fst_1423_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_fst_1424_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1449_);
v___x_1451_ = v___x_1433_;
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
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1427_);
lean_dec(v_fst_1424_);
lean_dec(v_fst_1423_);
lean_dec(v_a_1417_);
lean_dec(v_i_1387_);
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
v_a_1455_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1430_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1430_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1417_);
lean_dec(v_i_1387_);
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
v_a_1464_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1420_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1420_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_i_1387_);
lean_dec_ref(v_eType_1385_);
lean_dec_ref(v_targetType_1384_);
lean_dec(v_term_x3f_1383_);
lean_dec(v_mvarId_1381_);
v_a_1472_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1416_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1416_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1480_, lean_object* v_cfg_1481_, lean_object* v_term_x3f_1482_, lean_object* v_targetType_1483_, lean_object* v_eType_1484_, lean_object* v_rangeNumArgs_1485_, lean_object* v_i_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1480_, v_cfg_1481_, v_term_x3f_1482_, v_targetType_1483_, v_eType_1484_, v_rangeNumArgs_1485_, v_i_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec_ref(v_rangeNumArgs_1485_);
lean_dec_ref(v_cfg_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1493_, lean_object* v_h__1_1494_){
_start:
{
lean_object* v_snd_1495_; lean_object* v_fst_1496_; lean_object* v_fst_1497_; lean_object* v_snd_1498_; lean_object* v___x_1499_; 
v_snd_1495_ = lean_ctor_get(v_x_1493_, 1);
lean_inc(v_snd_1495_);
v_fst_1496_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_fst_1496_);
lean_dec_ref(v_x_1493_);
v_fst_1497_ = lean_ctor_get(v_snd_1495_, 0);
lean_inc(v_fst_1497_);
v_snd_1498_ = lean_ctor_get(v_snd_1495_, 1);
lean_inc(v_snd_1498_);
lean_dec(v_snd_1495_);
v___x_1499_ = lean_apply_3(v_h__1_1494_, v_fst_1496_, v_fst_1497_, v_snd_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1500_, lean_object* v_x_1501_, lean_object* v_h__1_1502_){
_start:
{
lean_object* v_snd_1503_; lean_object* v_fst_1504_; lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1507_; 
v_snd_1503_ = lean_ctor_get(v_x_1501_, 1);
lean_inc(v_snd_1503_);
v_fst_1504_ = lean_ctor_get(v_x_1501_, 0);
lean_inc(v_fst_1504_);
lean_dec_ref(v_x_1501_);
v_fst_1505_ = lean_ctor_get(v_snd_1503_, 0);
lean_inc(v_fst_1505_);
v_snd_1506_ = lean_ctor_get(v_snd_1503_, 1);
lean_inc(v_snd_1506_);
lean_dec(v_snd_1503_);
v___x_1507_ = lean_apply_3(v_h__1_1502_, v_fst_1504_, v_fst_1505_, v_snd_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Lean_Expr_hasMVar(v_e_1508_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_e_1508_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; lean_object* v_mctx_1514_; lean_object* v___x_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1518_; lean_object* v_cache_1519_; lean_object* v_zetaDeltaFVarIds_1520_; lean_object* v_postponed_1521_; lean_object* v_diag_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1531_; 
v___x_1513_ = lean_st_ref_get(v___y_1509_);
v_mctx_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_ref(v_mctx_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = l_Lean_instantiateMVarsCore(v_mctx_1514_, v_e_1508_);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_fst_1516_);
v_snd_1517_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_snd_1517_);
lean_dec_ref(v___x_1515_);
v___x_1518_ = lean_st_ref_take(v___y_1509_);
v_cache_1519_ = lean_ctor_get(v___x_1518_, 1);
v_zetaDeltaFVarIds_1520_ = lean_ctor_get(v___x_1518_, 2);
v_postponed_1521_ = lean_ctor_get(v___x_1518_, 3);
v_diag_1522_ = lean_ctor_get(v___x_1518_, 4);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1518_, 0);
lean_dec(v_unused_1532_);
v___x_1524_ = v___x_1518_;
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_diag_1522_);
lean_inc(v_postponed_1521_);
lean_inc(v_zetaDeltaFVarIds_1520_);
lean_inc(v_cache_1519_);
lean_dec(v___x_1518_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_snd_1517_);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_snd_1517_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_cache_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_zetaDeltaFVarIds_1520_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_postponed_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_diag_1522_);
v___x_1527_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_st_ref_set(v___y_1509_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_fst_1516_);
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1533_, v___y_1534_);
lean_dec(v___y_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1537_, v___y_1539_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1551_, v_x_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1558_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1558_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1575_, v_x_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1583_, lean_object* v_mvarId_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1584_, v_x_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_mvarId_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1592_, v_mvarId_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1601_, size_t v_i_1602_, size_t v_stop_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_a_1608_; uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_eq(v_i_1602_, v_stop_1603_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1613_ = lean_array_uget_borrowed(v_as_1601_, v_i_1602_);
v___x_1616_ = l_Lean_Expr_mvarId_x21(v___x_1613_);
v___x_1617_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1616_, v___y_1605_);
lean_dec(v___x_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
goto v___jp_1614_;
}
else
{
v_a_1608_ = v_b_1604_;
goto v___jp_1607_;
}
}
else
{
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1621_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
if (v___x_1621_ == 0)
{
v_a_1608_ = v_b_1604_;
goto v___jp_1607_;
}
else
{
goto v___jp_1614_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_b_1604_);
v_a_1622_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1617_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1617_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
v___jp_1614_:
{
lean_object* v___x_1615_; 
lean_inc(v___x_1613_);
v___x_1615_ = lean_array_push(v_b_1604_, v___x_1613_);
v_a_1608_ = v___x_1615_;
goto v___jp_1607_;
}
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_b_1604_);
return v___x_1630_;
}
v___jp_1607_:
{
size_t v___x_1609_; size_t v___x_1610_; 
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1602_, v___x_1609_);
v_i_1602_ = v___x_1610_;
v_b_1604_ = v_a_1608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1631_, lean_object* v_i_1632_, lean_object* v_stop_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_i_boxed_1637_; size_t v_stop_boxed_1638_; lean_object* v_res_1639_; 
v_i_boxed_1637_ = lean_unbox_usize(v_i_1632_);
lean_dec(v_i_1632_);
v_stop_boxed_1638_ = lean_unbox_usize(v_stop_1633_);
lean_dec(v_stop_1633_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1631_, v_i_boxed_1637_, v_stop_boxed_1638_, v_b_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v_as_1631_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
if (lean_obj_tag(v_as_1640_) == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
else
{
lean_object* v_head_1648_; lean_object* v_tail_1649_; lean_object* v___x_1650_; 
v_head_1648_ = lean_ctor_get(v_as_1640_, 0);
lean_inc(v_head_1648_);
v_tail_1649_ = lean_ctor_get(v_as_1640_, 1);
lean_inc(v_tail_1649_);
lean_dec_ref_known(v_as_1640_, 2);
v___x_1650_ = l_Lean_MVarId_headBetaType(v_head_1648_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_dec_ref_known(v___x_1650_, 1);
v_as_1640_ = v_tail_1649_;
goto _start;
}
else
{
lean_dec(v_tail_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_){
_start:
{
lean_object* v_ks_1663_; lean_object* v_vs_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1688_; 
v_ks_1663_ = lean_ctor_get(v_x_1659_, 0);
v_vs_1664_ = lean_ctor_get(v_x_1659_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1666_ = v_x_1659_;
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_vs_1664_);
lean_inc(v_ks_1663_);
lean_dec(v_x_1659_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_array_get_size(v_ks_1663_);
v___x_1669_ = lean_nat_dec_lt(v_x_1660_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_dec(v_x_1660_);
v___x_1670_ = lean_array_push(v_ks_1663_, v_x_1661_);
v___x_1671_ = lean_array_push(v_vs_1664_, v_x_1662_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1671_);
lean_ctor_set(v___x_1666_, 0, v___x_1670_);
v___x_1673_ = v___x_1666_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v_k_x27_1675_; uint8_t v___x_1676_; 
v_k_x27_1675_ = lean_array_fget_borrowed(v_ks_1663_, v_x_1660_);
v___x_1676_ = l_Lean_instBEqMVarId_beq(v_x_1661_, v_k_x27_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1678_; 
if (v_isShared_1667_ == 0)
{
v___x_1678_ = v___x_1666_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_ks_1663_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_vs_1664_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_nat_add(v_x_1660_, v___x_1679_);
lean_dec(v_x_1660_);
v_x_1659_ = v___x_1678_;
v_x_1660_ = v___x_1680_;
goto _start;
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = lean_array_fset(v_ks_1663_, v_x_1660_, v_x_1661_);
v___x_1684_ = lean_array_fset(v_vs_1664_, v_x_1660_, v_x_1662_);
lean_dec(v_x_1660_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1684_);
lean_ctor_set(v___x_1666_, 0, v___x_1683_);
v___x_1686_ = v___x_1666_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1689_, lean_object* v_k_1690_, lean_object* v_v_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1689_, v___x_1692_, v_k_1690_, v_v_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1695_, size_t v_x_1696_, size_t v_x_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v_es_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v_j_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_es_1700_ = lean_ctor_get(v_x_1695_, 0);
v___x_1701_ = ((size_t)31ULL);
v___x_1702_ = lean_usize_land(v_x_1696_, v___x_1701_);
v_j_1703_ = lean_usize_to_nat(v___x_1702_);
v___x_1704_ = lean_array_get_size(v_es_1700_);
v___x_1705_ = lean_nat_dec_lt(v_j_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec(v_j_1703_);
lean_dec(v_x_1699_);
lean_dec(v_x_1698_);
return v_x_1695_;
}
else
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1744_; 
lean_inc_ref(v_es_1700_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_x_1695_, 0);
lean_dec(v_unused_1745_);
v___x_1707_ = v_x_1695_;
v_isShared_1708_ = v_isSharedCheck_1744_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_x_1695_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1744_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_v_1709_; lean_object* v___x_1710_; lean_object* v_xs_x27_1711_; lean_object* v___y_1713_; 
v_v_1709_ = lean_array_fget(v_es_1700_, v_j_1703_);
v___x_1710_ = lean_box(0);
v_xs_x27_1711_ = lean_array_fset(v_es_1700_, v_j_1703_, v___x_1710_);
switch(lean_obj_tag(v_v_1709_))
{
case 0:
{
lean_object* v_key_1718_; lean_object* v_val_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1729_; 
v_key_1718_ = lean_ctor_get(v_v_1709_, 0);
v_val_1719_ = lean_ctor_get(v_v_1709_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_v_1709_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1721_ = v_v_1709_;
v_isShared_1722_ = v_isSharedCheck_1729_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_val_1719_);
lean_inc(v_key_1718_);
lean_dec(v_v_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1729_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lean_instBEqMVarId_beq(v_x_1698_, v_key_1718_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_del_object(v___x_1721_);
v___x_1724_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1718_, v_val_1719_, v_x_1698_, v_x_1699_);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
v___y_1713_ = v___x_1725_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1727_; 
lean_dec(v_val_1719_);
lean_dec(v_key_1718_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_x_1699_);
lean_ctor_set(v___x_1721_, 0, v_x_1698_);
v___x_1727_ = v___x_1721_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_x_1698_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_x_1699_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
v___y_1713_ = v___x_1727_;
goto v___jp_1712_;
}
}
}
}
case 1:
{
lean_object* v_node_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1742_; 
v_node_1730_ = lean_ctor_get(v_v_1709_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_v_1709_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1732_ = v_v_1709_;
v_isShared_1733_ = v_isSharedCheck_1742_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_node_1730_);
lean_dec(v_v_1709_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1742_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1734_ = ((size_t)5ULL);
v___x_1735_ = lean_usize_shift_right(v_x_1696_, v___x_1734_);
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_add(v_x_1697_, v___x_1736_);
v___x_1738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1730_, v___x_1735_, v___x_1737_, v_x_1698_, v_x_1699_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1738_);
v___x_1740_ = v___x_1732_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
v___y_1713_ = v___x_1740_;
goto v___jp_1712_;
}
}
}
default: 
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_x_1698_);
lean_ctor_set(v___x_1743_, 1, v_x_1699_);
v___y_1713_ = v___x_1743_;
goto v___jp_1712_;
}
}
v___jp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = lean_array_fset(v_xs_x27_1711_, v_j_1703_, v___y_1713_);
lean_dec(v_j_1703_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1714_);
v___x_1716_ = v___x_1707_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
else
{
lean_object* v_ks_1746_; lean_object* v_vs_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1767_; 
v_ks_1746_ = lean_ctor_get(v_x_1695_, 0);
v_vs_1747_ = lean_ctor_get(v_x_1695_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1749_ = v_x_1695_;
v_isShared_1750_ = v_isSharedCheck_1767_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_vs_1747_);
lean_inc(v_ks_1746_);
lean_dec(v_x_1695_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1767_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_ks_1746_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_vs_1747_);
v___x_1752_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v_newNode_1753_; uint8_t v___y_1755_; size_t v___x_1761_; uint8_t v___x_1762_; 
v_newNode_1753_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1752_, v_x_1698_, v_x_1699_);
v___x_1761_ = ((size_t)7ULL);
v___x_1762_ = lean_usize_dec_le(v___x_1761_, v_x_1697_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1753_);
v___x_1764_ = lean_unsigned_to_nat(4u);
v___x_1765_ = lean_nat_dec_lt(v___x_1763_, v___x_1764_);
lean_dec(v___x_1763_);
v___y_1755_ = v___x_1765_;
goto v___jp_1754_;
}
else
{
v___y_1755_ = v___x_1762_;
goto v___jp_1754_;
}
v___jp_1754_:
{
if (v___y_1755_ == 0)
{
lean_object* v_ks_1756_; lean_object* v_vs_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_ks_1756_ = lean_ctor_get(v_newNode_1753_, 0);
lean_inc_ref(v_ks_1756_);
v_vs_1757_ = lean_ctor_get(v_newNode_1753_, 1);
lean_inc_ref(v_vs_1757_);
lean_dec_ref(v_newNode_1753_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1697_, v_ks_1756_, v_vs_1757_, v___x_1758_, v___x_1759_);
lean_dec_ref(v_vs_1757_);
lean_dec_ref(v_ks_1756_);
return v___x_1760_;
}
else
{
return v_newNode_1753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1768_, lean_object* v_keys_1769_, lean_object* v_vals_1770_, lean_object* v_i_1771_, lean_object* v_entries_1772_){
_start:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_array_get_size(v_keys_1769_);
v___x_1774_ = lean_nat_dec_lt(v_i_1771_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec(v_i_1771_);
return v_entries_1772_;
}
else
{
lean_object* v_k_1775_; lean_object* v_v_1776_; uint64_t v___x_1777_; size_t v_h_1778_; size_t v___x_1779_; lean_object* v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; size_t v_h_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_k_1775_ = lean_array_fget_borrowed(v_keys_1769_, v_i_1771_);
v_v_1776_ = lean_array_fget_borrowed(v_vals_1770_, v_i_1771_);
v___x_1777_ = l_Lean_instHashableMVarId_hash(v_k_1775_);
v_h_1778_ = lean_uint64_to_usize(v___x_1777_);
v___x_1779_ = ((size_t)5ULL);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_sub(v_depth_1768_, v___x_1781_);
v___x_1783_ = lean_usize_mul(v___x_1779_, v___x_1782_);
v_h_1784_ = lean_usize_shift_right(v_h_1778_, v___x_1783_);
v___x_1785_ = lean_nat_add(v_i_1771_, v___x_1780_);
lean_dec(v_i_1771_);
lean_inc(v_v_1776_);
lean_inc(v_k_1775_);
v___x_1786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1772_, v_h_1784_, v_depth_1768_, v_k_1775_, v_v_1776_);
v_i_1771_ = v___x_1785_;
v_entries_1772_ = v___x_1786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1788_, lean_object* v_keys_1789_, lean_object* v_vals_1790_, lean_object* v_i_1791_, lean_object* v_entries_1792_){
_start:
{
size_t v_depth_boxed_1793_; lean_object* v_res_1794_; 
v_depth_boxed_1793_ = lean_unbox_usize(v_depth_1788_);
lean_dec(v_depth_1788_);
v_res_1794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1793_, v_keys_1789_, v_vals_1790_, v_i_1791_, v_entries_1792_);
lean_dec_ref(v_vals_1790_);
lean_dec_ref(v_keys_1789_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
size_t v_x_7234__boxed_1800_; size_t v_x_7235__boxed_1801_; lean_object* v_res_1802_; 
v_x_7234__boxed_1800_ = lean_unbox_usize(v_x_1796_);
lean_dec(v_x_1796_);
v_x_7235__boxed_1801_ = lean_unbox_usize(v_x_1797_);
lean_dec(v_x_1797_);
v_res_1802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1795_, v_x_7234__boxed_1800_, v_x_7235__boxed_1801_, v_x_1798_, v_x_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_){
_start:
{
uint64_t v___x_1806_; size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = l_Lean_instHashableMVarId_hash(v_x_1804_);
v___x_1807_ = lean_uint64_to_usize(v___x_1806_);
v___x_1808_ = ((size_t)1ULL);
v___x_1809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1803_, v___x_1807_, v___x_1808_, v_x_1804_, v_x_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1810_, lean_object* v_val_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v_mctx_1815_; lean_object* v_cache_1816_; lean_object* v_zetaDeltaFVarIds_1817_; lean_object* v_postponed_1818_; lean_object* v_diag_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1847_; 
v___x_1814_ = lean_st_ref_take(v___y_1812_);
v_mctx_1815_ = lean_ctor_get(v___x_1814_, 0);
v_cache_1816_ = lean_ctor_get(v___x_1814_, 1);
v_zetaDeltaFVarIds_1817_ = lean_ctor_get(v___x_1814_, 2);
v_postponed_1818_ = lean_ctor_get(v___x_1814_, 3);
v_diag_1819_ = lean_ctor_get(v___x_1814_, 4);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1821_ = v___x_1814_;
v_isShared_1822_ = v_isSharedCheck_1847_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_diag_1819_);
lean_inc(v_postponed_1818_);
lean_inc(v_zetaDeltaFVarIds_1817_);
lean_inc(v_cache_1816_);
lean_inc(v_mctx_1815_);
lean_dec(v___x_1814_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1847_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_depth_1823_; lean_object* v_levelAssignDepth_1824_; lean_object* v_lmvarCounter_1825_; lean_object* v_mvarCounter_1826_; lean_object* v_lDecls_1827_; lean_object* v_decls_1828_; lean_object* v_userNames_1829_; lean_object* v_lAssignment_1830_; lean_object* v_eAssignment_1831_; lean_object* v_dAssignment_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1846_; 
v_depth_1823_ = lean_ctor_get(v_mctx_1815_, 0);
v_levelAssignDepth_1824_ = lean_ctor_get(v_mctx_1815_, 1);
v_lmvarCounter_1825_ = lean_ctor_get(v_mctx_1815_, 2);
v_mvarCounter_1826_ = lean_ctor_get(v_mctx_1815_, 3);
v_lDecls_1827_ = lean_ctor_get(v_mctx_1815_, 4);
v_decls_1828_ = lean_ctor_get(v_mctx_1815_, 5);
v_userNames_1829_ = lean_ctor_get(v_mctx_1815_, 6);
v_lAssignment_1830_ = lean_ctor_get(v_mctx_1815_, 7);
v_eAssignment_1831_ = lean_ctor_get(v_mctx_1815_, 8);
v_dAssignment_1832_ = lean_ctor_get(v_mctx_1815_, 9);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_mctx_1815_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1834_ = v_mctx_1815_;
v_isShared_1835_ = v_isSharedCheck_1846_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_dAssignment_1832_);
lean_inc(v_eAssignment_1831_);
lean_inc(v_lAssignment_1830_);
lean_inc(v_userNames_1829_);
lean_inc(v_decls_1828_);
lean_inc(v_lDecls_1827_);
lean_inc(v_mvarCounter_1826_);
lean_inc(v_lmvarCounter_1825_);
lean_inc(v_levelAssignDepth_1824_);
lean_inc(v_depth_1823_);
lean_dec(v_mctx_1815_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1846_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1831_, v_mvarId_1810_, v_val_1811_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 8, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_depth_1823_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_levelAssignDepth_1824_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_lmvarCounter_1825_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_mvarCounter_1826_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_lDecls_1827_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_decls_1828_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_userNames_1829_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_lAssignment_1830_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_dAssignment_1832_);
v___x_1838_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1838_);
v___x_1840_ = v___x_1821_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_zetaDeltaFVarIds_1817_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_postponed_1818_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_diag_1819_);
v___x_1840_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_st_ref_set(v___y_1812_, v___x_1840_);
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1848_, lean_object* v_val_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1848_, v_val_1849_, v___y_1850_);
lean_dec(v___y_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
uint8_t v___x_1855_; 
v___x_1855_ = 0;
return v___x_1855_;
}
else
{
lean_object* v_head_1856_; lean_object* v_tail_1857_; uint8_t v___x_1858_; 
v_head_1856_ = lean_ctor_get(v_x_1854_, 0);
v_tail_1857_ = lean_ctor_get(v_x_1854_, 1);
v___x_1858_ = l_Lean_instBEqMVarId_beq(v_a_1853_, v_head_1856_);
if (v___x_1858_ == 0)
{
v_x_1854_ = v_tail_1857_;
goto _start;
}
else
{
return v___x_1858_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1860_, v_x_1861_);
lean_dec(v_x_1861_);
lean_dec(v_a_1860_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1864_, lean_object* v_as_1865_, size_t v_i_1866_, size_t v_stop_1867_, lean_object* v_b_1868_){
_start:
{
lean_object* v___y_1870_; uint8_t v___x_1874_; 
v___x_1874_ = lean_usize_dec_eq(v_i_1866_, v_stop_1867_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_array_uget_borrowed(v_as_1865_, v_i_1866_);
v___x_1876_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1875_, v_a_1864_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_inc(v___x_1875_);
v___x_1877_ = lean_array_push(v_b_1868_, v___x_1875_);
v___y_1870_ = v___x_1877_;
goto v___jp_1869_;
}
else
{
v___y_1870_ = v_b_1868_;
goto v___jp_1869_;
}
}
else
{
return v_b_1868_;
}
v___jp_1869_:
{
size_t v___x_1871_; size_t v___x_1872_; 
v___x_1871_ = ((size_t)1ULL);
v___x_1872_ = lean_usize_add(v_i_1866_, v___x_1871_);
v_i_1866_ = v___x_1872_;
v_b_1868_ = v___y_1870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1878_, lean_object* v_as_1879_, lean_object* v_i_1880_, lean_object* v_stop_1881_, lean_object* v_b_1882_){
_start:
{
size_t v_i_boxed_1883_; size_t v_stop_boxed_1884_; lean_object* v_res_1885_; 
v_i_boxed_1883_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_stop_boxed_1884_ = lean_unbox_usize(v_stop_1881_);
lean_dec(v_stop_1881_);
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1878_, v_as_1879_, v_i_boxed_1883_, v_stop_boxed_1884_, v_b_1882_);
lean_dec_ref(v_as_1879_);
lean_dec(v_a_1878_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1886_, lean_object* v___x_1887_, lean_object* v_e_1888_, lean_object* v_cfg_1889_, lean_object* v_term_x3f_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_a_1931_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___x_1982_; 
lean_inc(v___x_1887_);
lean_inc(v_mvarId_1886_);
v___x_1982_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1886_, v___x_1887_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v___x_1982_, 1);
lean_inc(v_mvarId_1886_);
v___x_1983_ = l_Lean_MVarId_getType(v_mvarId_1886_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v___y_1891_);
lean_inc_ref(v_e_1888_);
v___x_1985_ = lean_infer_type(v_e_1888_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v_rangeNumArgs_1988_; lean_object* v_lower_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___x_2033_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_n(v_a_1986_, 2);
lean_dec_ref_known(v___x_1985_, 1);
v___x_2033_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1986_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v_snd_2035_; uint8_t v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v_snd_2035_ = lean_ctor_get(v_a_2034_, 1);
v___x_2036_ = lean_unbox(v_snd_2035_);
if (v___x_2036_ == 0)
{
lean_object* v_fst_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2057_; 
v_fst_2037_ = lean_ctor_get(v_a_2034_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_2034_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_a_2034_, 1);
lean_dec(v_unused_2058_);
v___x_2039_ = v_a_2034_;
v_isShared_2040_ = v_isSharedCheck_2057_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_fst_2037_);
lean_dec(v_a_2034_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2057_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; 
lean_inc(v_a_1984_);
v___x_2041_ = l_Lean_Meta_getExpectedNumArgs(v_a_1984_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = lean_nat_sub(v_fst_2037_, v_a_2042_);
lean_dec(v_a_2042_);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_add(v_fst_2037_, v___x_2044_);
lean_dec(v_fst_2037_);
lean_inc(v___x_2043_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 1, v___x_2045_);
lean_ctor_set(v___x_2039_, 0, v___x_2043_);
v___x_2047_ = v___x_2039_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_rangeNumArgs_1988_ = v___x_2047_;
v_lower_1989_ = v___x_2043_;
v___y_1990_ = v___y_1891_;
v___y_1991_ = v___y_1892_;
v___y_1992_ = v___y_1893_;
v___y_1993_ = v___y_1894_;
goto v___jp_1987_;
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_2039_);
lean_dec(v_fst_2037_);
lean_dec(v_a_1986_);
lean_dec(v_a_1984_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_term_x3f_1890_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2049_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2041_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2041_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_fst_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2068_; 
v_fst_2059_ = lean_ctor_get(v_a_2034_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_a_2034_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_a_2034_, 1);
lean_dec(v_unused_2069_);
v___x_2061_ = v_a_2034_;
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_fst_2059_);
lean_dec(v_a_2034_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_add(v_fst_2059_, v___x_2063_);
lean_inc(v_fst_2059_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_fst_2059_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_rangeNumArgs_1988_ = v___x_2066_;
v_lower_1989_ = v_fst_2059_;
v___y_1990_ = v___y_1891_;
v___y_1991_ = v___y_1892_;
v___y_1992_ = v___y_1893_;
v___y_1993_ = v___y_1894_;
goto v___jp_1987_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_a_1986_);
lean_dec(v_a_1984_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_term_x3f_1890_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2070_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2033_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2033_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
v___jp_1987_:
{
lean_object* v___x_1994_; 
lean_inc(v_mvarId_1886_);
v___x_1994_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1886_, v_cfg_1889_, v_term_x3f_1890_, v_a_1984_, v_a_1986_, v_rangeNumArgs_1988_, v_lower_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec_ref(v_rangeNumArgs_1988_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; uint8_t v_newGoals_1998_; uint8_t v_synthAssignedInstances_1999_; uint8_t v_allowSynthFailures_2000_; lean_object* v___x_2001_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v_fst_1996_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_fst_1996_);
v_snd_1997_ = lean_ctor_get(v_a_1995_, 1);
lean_inc_n(v_snd_1997_, 2);
lean_dec(v_a_1995_);
v_newGoals_1998_ = lean_ctor_get_uint8(v_cfg_1889_, 0);
v_synthAssignedInstances_1999_ = lean_ctor_get_uint8(v_cfg_1889_, 1);
v_allowSynthFailures_2000_ = lean_ctor_get_uint8(v_cfg_1889_, 2);
lean_inc(v_mvarId_1886_);
v___x_2001_ = l_Lean_Meta_synthAppInstances(v___x_1887_, v_mvarId_1886_, v_fst_1996_, v_snd_1997_, v_synthAssignedInstances_1999_, v_allowSynthFailures_2000_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
lean_dec_ref_known(v___x_2001_, 1);
v___x_2002_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1888_, v___y_1991_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_n(v_a_2003_, 2);
lean_dec_ref(v___x_2002_);
v___x_2004_ = l_Lean_mkAppN(v_a_2003_, v_fst_1996_);
lean_inc(v_mvarId_1886_);
v___x_2005_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1886_, v___x_2004_, v___y_1991_);
lean_dec_ref(v___x_2005_);
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_array_get_size(v_fst_1996_);
v___x_2008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2009_ = lean_nat_dec_lt(v___x_2006_, v___x_2007_);
if (v___x_2009_ == 0)
{
lean_dec(v_fst_1996_);
v___y_1923_ = v___y_1993_;
v___y_1924_ = v___x_2006_;
v___y_1925_ = v_a_2003_;
v___y_1926_ = v___y_1992_;
v___y_1927_ = v_newGoals_1998_;
v___y_1928_ = v___y_1991_;
v___y_1929_ = v_snd_1997_;
v___y_1930_ = v___y_1990_;
v_a_1931_ = v___x_2008_;
goto v___jp_1922_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_nat_dec_le(v___x_2007_, v___x_2007_);
if (v___x_2010_ == 0)
{
if (v___x_2009_ == 0)
{
lean_dec(v_fst_1996_);
v___y_1923_ = v___y_1993_;
v___y_1924_ = v___x_2006_;
v___y_1925_ = v_a_2003_;
v___y_1926_ = v___y_1992_;
v___y_1927_ = v_newGoals_1998_;
v___y_1928_ = v___y_1991_;
v___y_1929_ = v_snd_1997_;
v___y_1930_ = v___y_1990_;
v_a_1931_ = v___x_2008_;
goto v___jp_1922_;
}
else
{
size_t v___x_2011_; size_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = lean_usize_of_nat(v___x_2007_);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1996_, v___x_2011_, v___x_2012_, v___x_2008_, v___y_1991_);
lean_dec(v_fst_1996_);
v___y_1964_ = v___y_1993_;
v___y_1965_ = v___x_2006_;
v___y_1966_ = v_a_2003_;
v___y_1967_ = v___y_1992_;
v___y_1968_ = v___y_1991_;
v___y_1969_ = v_newGoals_1998_;
v___y_1970_ = v_snd_1997_;
v___y_1971_ = v___y_1990_;
v___y_1972_ = v___x_2013_;
goto v___jp_1963_;
}
}
else
{
size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = ((size_t)0ULL);
v___x_2015_ = lean_usize_of_nat(v___x_2007_);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1996_, v___x_2014_, v___x_2015_, v___x_2008_, v___y_1991_);
lean_dec(v_fst_1996_);
v___y_1964_ = v___y_1993_;
v___y_1965_ = v___x_2006_;
v___y_1966_ = v_a_2003_;
v___y_1967_ = v___y_1992_;
v___y_1968_ = v___y_1991_;
v___y_1969_ = v_newGoals_1998_;
v___y_1970_ = v_snd_1997_;
v___y_1971_ = v___y_1990_;
v___y_1972_ = v___x_2016_;
goto v___jp_1963_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_snd_1997_);
lean_dec(v_fst_1996_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_e_1888_);
lean_dec(v_mvarId_1886_);
v_a_2017_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2001_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2001_);
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
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2025_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1994_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1994_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_1984_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_term_x3f_1890_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2078_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1985_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1985_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_term_x3f_1890_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2086_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1983_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1983_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_term_x3f_1890_);
lean_dec_ref(v_e_1888_);
lean_dec(v___x_1887_);
lean_dec(v_mvarId_1886_);
v_a_2094_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_1982_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_1982_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
v___jp_1896_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_array_to_list(v___y_1902_);
v___x_1904_ = l_List_appendTR___redArg(v___y_1900_, v___x_1903_);
lean_inc(v___x_1904_);
v___x_1905_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1904_, v___y_1901_, v___y_1899_, v___y_1898_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1901_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1913_);
v___x_1907_ = v___x_1905_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1905_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1904_);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___x_1904_);
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1905_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1905_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
v___jp_1922_:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_appendParentTag(v_mvarId_1886_, v_a_1931_, v___y_1929_, v___y_1930_, v___y_1928_, v___y_1926_, v___y_1923_);
lean_dec_ref(v___y_1929_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref_known(v___x_1932_, 1);
v___x_1933_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1925_, v___y_1930_, v___y_1928_, v___y_1926_, v___y_1923_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1931_, v___y_1927_, v___y_1930_, v___y_1928_, v___y_1926_, v___y_1923_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = lean_array_get_size(v_a_1934_);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___y_1924_);
v___x_1939_ = lean_nat_dec_lt(v___y_1924_, v___x_1937_);
if (v___x_1939_ == 0)
{
lean_dec(v_a_1934_);
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___y_1926_;
v___y_1899_ = v___y_1928_;
v___y_1900_ = v_a_1936_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___x_1938_;
goto v___jp_1896_;
}
else
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_nat_dec_le(v___x_1937_, v___x_1937_);
if (v___x_1940_ == 0)
{
if (v___x_1939_ == 0)
{
lean_dec(v_a_1934_);
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___y_1926_;
v___y_1899_ = v___y_1928_;
v___y_1900_ = v_a_1936_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___x_1938_;
goto v___jp_1896_;
}
else
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1937_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1936_, v_a_1934_, v___x_1941_, v___x_1942_, v___x_1938_);
lean_dec(v_a_1934_);
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___y_1926_;
v___y_1899_ = v___y_1928_;
v___y_1900_ = v_a_1936_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___x_1943_;
goto v___jp_1896_;
}
}
else
{
size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = lean_usize_of_nat(v___x_1937_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1936_, v_a_1934_, v___x_1944_, v___x_1945_, v___x_1938_);
lean_dec(v_a_1934_);
v___y_1897_ = v___y_1923_;
v___y_1898_ = v___y_1926_;
v___y_1899_ = v___y_1928_;
v___y_1900_ = v_a_1936_;
v___y_1901_ = v___y_1930_;
v___y_1902_ = v___x_1946_;
goto v___jp_1896_;
}
}
}
else
{
lean_dec(v_a_1934_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1923_);
return v___x_1935_;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_a_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1923_);
v_a_1947_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1933_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1933_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_a_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1923_);
v_a_1955_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1932_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1932_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
v___jp_1963_:
{
if (lean_obj_tag(v___y_1972_) == 0)
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___y_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___y_1972_, 1);
v___y_1923_ = v___y_1964_;
v___y_1924_ = v___y_1965_;
v___y_1925_ = v___y_1966_;
v___y_1926_ = v___y_1967_;
v___y_1927_ = v___y_1969_;
v___y_1928_ = v___y_1968_;
v___y_1929_ = v___y_1970_;
v___y_1930_ = v___y_1971_;
v_a_1931_ = v_a_1973_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1964_);
lean_dec(v_mvarId_1886_);
v_a_1974_ = lean_ctor_get(v___y_1972_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___y_1972_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___y_1972_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___y_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2102_, lean_object* v___x_2103_, lean_object* v_e_2104_, lean_object* v_cfg_2105_, lean_object* v_term_x3f_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2102_, v___x_2103_, v_e_2104_, v_cfg_2105_, v_term_x3f_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v_cfg_2105_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2113_, lean_object* v_e_2114_, lean_object* v_cfg_2115_, lean_object* v_term_x3f_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2113_);
v___f_2123_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2123_, 0, v_mvarId_2113_);
lean_closure_set(v___f_2123_, 1, v___x_2122_);
lean_closure_set(v___f_2123_, 2, v_e_2114_);
lean_closure_set(v___f_2123_, 3, v_cfg_2115_);
lean_closure_set(v___f_2123_, 4, v_term_x3f_2116_);
v___x_2124_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2113_, v___f_2123_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2125_, lean_object* v_e_2126_, lean_object* v_cfg_2127_, lean_object* v_term_x3f_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_MVarId_apply(v_mvarId_2125_, v_e_2126_, v_cfg_2127_, v_term_x3f_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2135_, lean_object* v_val_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2135_, v_val_2136_, v___y_2138_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2143_, lean_object* v_val_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2143_, v_val_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2151_, size_t v_i_2152_, size_t v_stop_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2151_, v_i_2152_, v_stop_2153_, v_b_2154_, v___y_2156_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2161_, lean_object* v_i_2162_, lean_object* v_stop_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_i_boxed_2170_; size_t v_stop_boxed_2171_; lean_object* v_res_2172_; 
v_i_boxed_2170_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_stop_boxed_2171_ = lean_unbox_usize(v_stop_2163_);
lean_dec(v_stop_2163_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2161_, v_i_boxed_2170_, v_stop_boxed_2171_, v_b_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_as_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2174_, v_x_2175_, v_x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, size_t v_x_2180_, size_t v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2179_, v_x_2180_, v_x_2181_, v_x_2182_, v_x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
size_t v_x_7967__boxed_2191_; size_t v_x_7968__boxed_2192_; lean_object* v_res_2193_; 
v_x_7967__boxed_2191_ = lean_unbox_usize(v_x_2187_);
lean_dec(v_x_2187_);
v_x_7968__boxed_2192_ = lean_unbox_usize(v_x_2188_);
lean_dec(v_x_2188_);
v_res_2193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2185_, v_x_2186_, v_x_7967__boxed_2191_, v_x_7968__boxed_2192_, v_x_2189_, v_x_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2194_, lean_object* v_n_2195_, lean_object* v_k_2196_, lean_object* v_v_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2195_, v_k_2196_, v_v_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2199_, size_t v_depth_2200_, lean_object* v_keys_2201_, lean_object* v_vals_2202_, lean_object* v_heq_2203_, lean_object* v_i_2204_, lean_object* v_entries_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2200_, v_keys_2201_, v_vals_2202_, v_i_2204_, v_entries_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2207_, lean_object* v_depth_2208_, lean_object* v_keys_2209_, lean_object* v_vals_2210_, lean_object* v_heq_2211_, lean_object* v_i_2212_, lean_object* v_entries_2213_){
_start:
{
size_t v_depth_boxed_2214_; lean_object* v_res_2215_; 
v_depth_boxed_2214_ = lean_unbox_usize(v_depth_2208_);
lean_dec(v_depth_2208_);
v_res_2215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2207_, v_depth_boxed_2214_, v_keys_2209_, v_vals_2210_, v_heq_2211_, v_i_2212_, v_entries_2213_);
lean_dec_ref(v_vals_2210_);
lean_dec_ref(v_keys_2209_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2217_, v_x_2218_, v_x_2219_, v_x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2225_, lean_object* v_c_2226_, lean_object* v_cfg_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2233_; 
lean_inc(v_c_2226_);
v___x_2233_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2226_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2236_ = 0;
v___x_2237_ = l_Lean_MessageData_ofConstName(v_c_2226_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2235_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2235_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
v___x_2241_ = l_Lean_MVarId_apply(v_mvar_2225_, v_a_2234_, v_cfg_2227_, v___x_2240_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
return v___x_2241_;
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec_ref(v_cfg_2227_);
lean_dec(v_c_2226_);
lean_dec(v_mvar_2225_);
v_a_2242_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2233_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2250_, lean_object* v_c_2251_, lean_object* v_cfg_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_MVarId_applyConst(v_mvar_2250_, v_c_2251_, v_cfg_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v_env_2266_; lean_object* v___x_2267_; lean_object* v_mctx_2268_; lean_object* v_lctx_2269_; lean_object* v_options_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2265_ = lean_st_ref_get(v___y_2263_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2265_);
v___x_2267_ = lean_st_ref_get(v___y_2261_);
v_mctx_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_mctx_2268_);
lean_dec(v___x_2267_);
v_lctx_2269_ = lean_ctor_get(v___y_2260_, 2);
v_options_2270_ = lean_ctor_get(v___y_2262_, 2);
lean_inc_ref(v_options_2270_);
lean_inc_ref(v_lctx_2269_);
v___x_2271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2271_, 0, v_env_2266_);
lean_ctor_set(v___x_2271_, 1, v_mctx_2268_);
lean_ctor_set(v___x_2271_, 2, v_lctx_2269_);
lean_ctor_set(v___x_2271_, 3, v_options_2270_);
v___x_2272_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v_msgData_2259_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_ref_2287_; lean_object* v___x_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
v_ref_2287_ = lean_ctor_get(v___y_2284_, 5);
v___x_2288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_inc(v_ref_2287_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_ref_2287_);
lean_ctor_set(v___x_2293_, 1, v_a_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set_tag(v___x_2291_, 1);
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2305_, size_t v_i_2306_, lean_object* v_bs_2307_){
_start:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_usize_dec_lt(v_i_2306_, v_sz_2305_);
if (v___x_2308_ == 0)
{
return v_bs_2307_;
}
else
{
lean_object* v_v_2309_; lean_object* v___x_2310_; lean_object* v_bs_x27_2311_; lean_object* v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; lean_object* v___x_2315_; 
v_v_2309_ = lean_array_uget(v_bs_2307_, v_i_2306_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v_bs_x27_2311_ = lean_array_uset(v_bs_2307_, v_i_2306_, v___x_2310_);
v___x_2312_ = l_Lean_Expr_mvarId_x21(v_v_2309_);
lean_dec(v_v_2309_);
v___x_2313_ = ((size_t)1ULL);
v___x_2314_ = lean_usize_add(v_i_2306_, v___x_2313_);
v___x_2315_ = lean_array_uset(v_bs_x27_2311_, v_i_2306_, v___x_2312_);
v_i_2306_ = v___x_2314_;
v_bs_2307_ = v___x_2315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2317_, lean_object* v_i_2318_, lean_object* v_bs_2319_){
_start:
{
size_t v_sz_boxed_2320_; size_t v_i_boxed_2321_; lean_object* v_res_2322_; 
v_sz_boxed_2320_ = lean_unbox_usize(v_sz_2317_);
lean_dec(v_sz_2317_);
v_i_boxed_2321_ = lean_unbox_usize(v_i_2318_);
lean_dec(v_i_2318_);
v_res_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2320_, v_i_boxed_2321_, v_bs_2319_);
return v_res_2322_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2341_, lean_object* v___x_2342_, lean_object* v_e_2343_, lean_object* v_n_2344_, uint8_t v_useApproxDefEq_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
lean_inc(v_mvarId_2341_);
v___x_2351_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2341_, v___x_2342_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref_known(v___x_2351_, 1);
lean_inc(v_mvarId_2341_);
v___x_2352_ = l_Lean_MVarId_getType(v_mvarId_2341_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc_ref(v_e_2343_);
v___x_2354_ = lean_infer_type(v_e_2343_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = 0;
lean_inc(v_n_2344_);
v___x_2357_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2355_, v_n_2344_, v___x_2356_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_fst_2359_; lean_object* v_snd_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2450_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v_fst_2359_ = lean_ctor_get(v_a_2358_, 0);
v_snd_2360_ = lean_ctor_get(v_a_2358_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_a_2358_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2362_ = v_a_2358_;
v_isShared_2363_ = v_isSharedCheck_2450_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_snd_2360_);
lean_inc(v_fst_2359_);
lean_dec(v_a_2358_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2450_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___y_2365_; lean_object* v_snd_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2448_; 
v_snd_2380_ = lean_ctor_get(v_snd_2360_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_snd_2360_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v_snd_2360_, 0);
lean_dec(v_unused_2449_);
v___x_2382_ = v_snd_2360_;
v_isShared_2383_ = v_isSharedCheck_2448_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snd_2380_);
lean_dec(v_snd_2360_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2448_;
goto v_resetjp_2381_;
}
v___jp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2378_; 
lean_inc(v_fst_2359_);
v___x_2366_ = l_Lean_Expr_beta(v_e_2343_, v_fst_2359_);
v___x_2367_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2341_, v___x_2366_, v___y_2365_);
lean_dec(v___y_2365_);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v___x_2367_, 0);
lean_dec(v_unused_2379_);
v___x_2369_ = v___x_2367_;
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v___x_2367_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
size_t v_sz_2371_; size_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v_sz_2371_ = lean_array_size(v_fst_2359_);
v___x_2372_ = ((size_t)0ULL);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2371_, v___x_2372_, v_fst_2359_);
v___x_2374_ = lean_array_to_list(v___x_2373_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2374_);
v___x_2376_ = v___x_2369_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
v_resetjp_2381_:
{
lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = lean_array_get_size(v_fst_2359_);
v___x_2429_ = lean_nat_dec_eq(v___x_2428_, v_n_2344_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2382_);
lean_del_object(v___x_2362_);
lean_dec(v_fst_2359_);
lean_dec(v_a_2353_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v___x_2430_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2431_ = l_Nat_reprFast(v_n_2344_);
v___x_2432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
v___x_2433_ = l_Lean_MessageData_ofFormat(v___x_2432_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2430_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_indentExpr(v_snd_2380_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2438_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
v___y_2385_ = v___y_2346_;
v___y_2386_ = v___y_2347_;
v___y_2387_ = v___y_2348_;
v___y_2388_ = v___y_2349_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2389_; 
lean_inc(v_a_2353_);
lean_inc(v_snd_2380_);
v___x_2389_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2345_, v_snd_2380_, v_a_2353_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; uint8_t v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = lean_unbox(v_a_2390_);
lean_dec(v_a_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec(v_fst_2359_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v___x_2392_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2393_ = l_Lean_indentExpr(v_a_2353_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 7);
lean_ctor_set(v___x_2382_, 1, v___x_2393_);
lean_ctor_set(v___x_2382_, 0, v___x_2392_);
v___x_2395_ = v___x_2382_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 7);
lean_ctor_set(v___x_2362_, 1, v___x_2396_);
lean_ctor_set(v___x_2362_, 0, v___x_2395_);
v___x_2398_ = v___x_2362_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v___x_2399_ = l_Lean_indentExpr(v_snd_2380_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Nat_reprFast(v_n_2344_);
v___x_2404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
v___x_2405_ = l_Lean_MessageData_ofFormat(v___x_2404_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2402_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2408_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
else
{
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v___y_2385_);
lean_del_object(v___x_2382_);
lean_dec(v_snd_2380_);
lean_del_object(v___x_2362_);
lean_dec(v_a_2353_);
lean_dec(v_n_2344_);
v___y_2365_ = v___y_2386_;
goto v___jp_2364_;
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_del_object(v___x_2382_);
lean_dec(v_snd_2380_);
lean_del_object(v___x_2362_);
lean_dec(v_fst_2359_);
lean_dec(v_a_2353_);
lean_dec(v_n_2344_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v_a_2420_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2389_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2389_);
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
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_a_2353_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_n_2344_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v_a_2451_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2357_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2357_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_a_2353_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_n_2344_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v_a_2459_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2354_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2354_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_n_2344_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v_a_2467_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2352_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2352_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_n_2344_);
lean_dec_ref(v_e_2343_);
lean_dec(v_mvarId_2341_);
v_a_2475_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2351_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2351_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2483_, lean_object* v___x_2484_, lean_object* v_e_2485_, lean_object* v_n_2486_, lean_object* v_useApproxDefEq_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2493_; lean_object* v_res_2494_; 
v_useApproxDefEq_boxed_2493_ = lean_unbox(v_useApproxDefEq_2487_);
v_res_2494_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2483_, v___x_2484_, v_e_2485_, v_n_2486_, v_useApproxDefEq_boxed_2493_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2495_, lean_object* v_e_2496_, lean_object* v_n_2497_, uint8_t v_useApproxDefEq_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2505_ = lean_box(v_useApproxDefEq_2498_);
lean_inc(v_mvarId_2495_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2506_, 0, v_mvarId_2495_);
lean_closure_set(v___f_2506_, 1, v___x_2504_);
lean_closure_set(v___f_2506_, 2, v_e_2496_);
lean_closure_set(v___f_2506_, 3, v_n_2497_);
lean_closure_set(v___f_2506_, 4, v___x_2505_);
v___x_2507_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2495_, v___f_2506_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2508_, lean_object* v_e_2509_, lean_object* v_n_2510_, lean_object* v_useApproxDefEq_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2517_; lean_object* v_res_2518_; 
v_useApproxDefEq_boxed_2517_ = lean_unbox(v_useApproxDefEq_2511_);
v_res_2518_ = l_Lean_MVarId_applyN(v_mvarId_2508_, v_e_2509_, v_n_2510_, v_useApproxDefEq_boxed_2517_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2527_, v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2547_ = l_Lean_mkConst(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2548_, lean_object* v_type_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
lean_inc(v_a_2554_);
lean_inc_ref(v_a_2553_);
lean_inc(v_a_2552_);
lean_inc_ref(v_a_2551_);
v___x_2556_ = lean_whnf(v_type_2549_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2559_ = lean_unsigned_to_nat(2u);
v___x_2560_ = l_Lean_Expr_isAppOfArity(v_a_2557_, v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2561_ = lean_st_ref_get(v_a_2550_);
v___x_2562_ = lean_array_get_size(v___x_2561_);
lean_dec(v___x_2561_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_add(v___x_2562_, v___x_2563_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2566_ = lean_name_append_index_after(v___x_2565_, v___x_2564_);
v___x_2567_ = l_Lean_Name_append(v_tag_2548_, v___x_2566_);
v___x_2568_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2557_, v___x_2567_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2580_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2573_ = lean_st_ref_take(v_a_2550_);
v___x_2574_ = l_Lean_Expr_mvarId_x21(v_a_2569_);
v___x_2575_ = lean_array_push(v___x_2573_, v___x_2574_);
v___x_2576_ = lean_st_ref_set(v_a_2550_, v___x_2575_);
if (v_isShared_2572_ == 0)
{
v___x_2578_ = v___x_2571_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2569_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = l_Lean_Expr_appFn_x21(v_a_2557_);
v___x_2582_ = l_Lean_Expr_appArg_x21(v___x_2581_);
lean_dec_ref(v___x_2581_);
lean_inc_ref(v___x_2582_);
lean_inc(v_tag_2548_);
v___x_2583_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2548_, v___x_2582_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = l_Lean_Expr_appArg_x21(v_a_2557_);
lean_dec(v_a_2557_);
lean_inc_ref(v___x_2585_);
v___x_2586_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2548_, v___x_2585_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2596_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2592_ = l_Lean_mkApp4(v___x_2591_, v___x_2582_, v___x_2585_, v_a_2584_, v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2592_);
v___x_2594_ = v___x_2589_;
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
}
else
{
lean_dec_ref(v___x_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v___x_2582_);
return v___x_2586_;
}
}
else
{
lean_dec_ref(v___x_2582_);
lean_dec(v_a_2557_);
lean_dec(v_tag_2548_);
return v___x_2583_;
}
}
}
else
{
lean_dec(v_tag_2548_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2597_, lean_object* v_type_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2597_, v_type_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2606_, lean_object* v___x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
lean_inc(v_mvarId_2606_);
v___x_2613_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2606_, v___x_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2613_, 1);
lean_inc(v_mvarId_2606_);
v___x_2614_ = l_Lean_MVarId_getType_x27(v_mvarId_2606_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2660_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2660_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2660_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2620_ = lean_unsigned_to_nat(2u);
v___x_2621_ = l_Lean_Expr_isAppOfArity(v_a_2615_, v___x_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec(v_a_2615_);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_mvarId_2606_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2623_);
v___x_2625_ = v___x_2617_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
lean_object* v___x_2627_; 
lean_del_object(v___x_2617_);
lean_inc(v_mvarId_2606_);
v___x_2627_ = l_Lean_MVarId_getTag(v_mvarId_2606_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2630_ = lean_st_mk_ref(v___x_2629_);
v___x_2631_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2628_, v_a_2615_, v___x_2630_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = lean_st_ref_get(v___x_2630_);
lean_dec(v___x_2630_);
v___x_2634_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2606_, v_a_2632_, v___y_2609_);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2634_, 0);
lean_dec(v_unused_2643_);
v___x_2636_ = v___x_2634_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v___x_2634_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_array_to_list(v___x_2633_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___x_2630_);
lean_dec(v_mvarId_2606_);
v_a_2644_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2631_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2631_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_a_2615_);
lean_dec(v_mvarId_2606_);
v_a_2652_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2627_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2627_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_mvarId_2606_);
v_a_2661_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2614_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2614_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_mvarId_2606_);
v_a_2669_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2613_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2613_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2677_, lean_object* v___x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2677_, v___x_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; 
v___x_2694_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2688_);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2695_, 0, v_mvarId_2688_);
lean_closure_set(v___f_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2688_, v___f_2695_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_MVarId_splitAndCore(v_mvarId_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_MVarId_splitAndCore(v_mvarId_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_MVarId_splitAnd(v_mvarId_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2717_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_box(0);
v___x_2722_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2723_ = l_Lean_mkConst(v___x_2722_, v___x_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2728_, lean_object* v___x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
lean_inc(v_mvarId_2728_);
v___x_2735_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2728_, v___x_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2736_; 
lean_dec_ref_known(v___x_2735_, 1);
lean_inc(v_mvarId_2728_);
v___x_2736_ = l_Lean_MVarId_getType(v_mvarId_2728_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2740_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2737_, v___y_2731_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_n(v_a_2739_, 2);
lean_dec_ref(v___x_2738_);
v___x_2740_ = l_Lean_Meta_getLevel(v_a_2739_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
lean_inc(v_mvarId_2728_);
v___x_2742_ = l_Lean_MVarId_getTag(v_mvarId_2728_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2746_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2745_, v_a_2743_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_n(v_a_2747_, 2);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2741_);
lean_ctor_set(v___x_2749_, 1, v___x_2744_);
v___x_2750_ = l_Lean_mkConst(v___x_2748_, v___x_2749_);
v___x_2751_ = l_Lean_mkAppB(v___x_2750_, v_a_2739_, v_a_2747_);
v___x_2752_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2728_, v___x_2751_, v___y_2731_);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v___x_2752_, 0);
lean_dec(v_unused_2761_);
v___x_2754_ = v___x_2752_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v___x_2752_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_Expr_mvarId_x21(v_a_2747_);
lean_dec(v_a_2747_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
lean_dec(v_mvarId_2728_);
v_a_2762_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2746_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2746_);
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
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
lean_dec(v_mvarId_2728_);
v_a_2770_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2742_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2742_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2739_);
lean_dec(v_mvarId_2728_);
v_a_2778_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2740_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2740_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_mvarId_2728_);
v_a_2786_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2736_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2736_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_mvarId_2728_);
v_a_2794_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2735_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2735_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2802_, lean_object* v___x_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2802_, v___x_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2813_);
v___f_2820_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2820_, 0, v_mvarId_2813_);
lean_closure_set(v___f_2820_, 1, v___x_2819_);
v___x_2821_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2813_, v___f_2820_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_MVarId_exfalso(v_mvarId_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2828_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2833_ = l_Lean_MessageData_ofFormat(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2840_, lean_object* v_name_2841_, lean_object* v_idx_2842_, lean_object* v_expected_x3f_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___x_2856_; 
lean_inc(v_name_2841_);
lean_inc(v_goal_2840_);
v___x_2856_ = l_Lean_MVarId_checkNotAssigned(v_goal_2840_, v_name_2841_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref_known(v___x_2856_, 1);
lean_inc(v_goal_2840_);
v___x_2857_ = l_Lean_MVarId_getType_x27(v_goal_2840_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l_Lean_Expr_getAppFn(v_a_2858_);
lean_dec(v_a_2858_);
if (lean_obj_tag(v___x_2859_) == 4)
{
lean_object* v_declName_2860_; lean_object* v_us_2861_; lean_object* v___x_2862_; lean_object* v_env_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; 
v_declName_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_declName_2860_);
v_us_2861_ = lean_ctor_get(v___x_2859_, 1);
lean_inc(v_us_2861_);
lean_dec_ref_known(v___x_2859_, 2);
v___x_2862_ = lean_st_ref_get(v___y_2847_);
v_env_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc_ref(v_env_2863_);
lean_dec(v___x_2862_);
v___x_2864_ = 0;
v___x_2865_ = l_Lean_Environment_find_x3f(v_env_2863_, v_declName_2860_, v___x_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec(v_us_2861_);
lean_dec(v_expected_x3f_2843_);
lean_dec(v_idx_2842_);
v___y_2850_ = v___y_2844_;
v___y_2851_ = v___y_2845_;
v___y_2852_ = v___y_2846_;
v___y_2853_ = v___y_2847_;
goto v___jp_2849_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2936_; 
v_val_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2936_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_val_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2936_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
if (lean_obj_tag(v_val_2866_) == 5)
{
lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2935_; 
v_val_2870_ = lean_ctor_get(v_val_2866_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_val_2866_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2872_ = v_val_2866_;
v_isShared_2873_ = v_isSharedCheck_2935_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v_val_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2935_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; 
if (lean_obj_tag(v_expected_x3f_2843_) == 1)
{
lean_object* v_val_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2934_; 
v_val_2905_ = lean_ctor_get(v_expected_x3f_2843_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_expected_x3f_2843_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2907_ = v_expected_x3f_2843_;
v_isShared_2908_ = v_isSharedCheck_2934_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_val_2905_);
lean_dec(v_expected_x3f_2843_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2934_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_ctors_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_ctors_2909_ = lean_ctor_get(v_val_2870_, 4);
v___x_2910_ = l_List_lengthTR___redArg(v_ctors_2909_);
v___x_2911_ = lean_nat_dec_eq(v___x_2910_, v_val_2905_);
lean_dec(v___x_2910_);
if (v___x_2911_ == 0)
{
uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2912_ = 1;
lean_inc(v_name_2841_);
v___x_2913_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2841_, v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2915_ = lean_string_append(v___x_2913_, v___x_2914_);
v___x_2916_ = l_Nat_reprFast(v_val_2905_);
v___x_2917_ = lean_string_append(v___x_2915_, v___x_2916_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2919_ = lean_string_append(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
v___x_2921_ = l_Lean_MessageData_ofFormat(v___x_2920_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2921_);
v___x_2923_ = v___x_2907_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; 
lean_inc(v_goal_2840_);
lean_inc(v_name_2841_);
v___x_2924_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2841_, v_goal_2840_, v___x_2923_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_dec_ref_known(v___x_2924_, 1);
v___y_2875_ = v___y_2844_;
v___y_2876_ = v___y_2845_;
v___y_2877_ = v___y_2846_;
v___y_2878_ = v___y_2847_;
goto v___jp_2874_;
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_del_object(v___x_2872_);
lean_dec_ref(v_val_2870_);
lean_del_object(v___x_2868_);
lean_dec(v_us_2861_);
lean_dec(v_idx_2842_);
lean_dec(v_name_2841_);
lean_dec(v_goal_2840_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_del_object(v___x_2907_);
lean_dec(v_val_2905_);
v___y_2875_ = v___y_2844_;
v___y_2876_ = v___y_2845_;
v___y_2877_ = v___y_2846_;
v___y_2878_ = v___y_2847_;
goto v___jp_2874_;
}
}
}
else
{
lean_dec(v_expected_x3f_2843_);
v___y_2875_ = v___y_2844_;
v___y_2876_ = v___y_2845_;
v___y_2877_ = v___y_2846_;
v___y_2878_ = v___y_2847_;
goto v___jp_2874_;
}
v___jp_2874_:
{
lean_object* v_ctors_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_ctors_2879_ = lean_ctor_get(v_val_2870_, 4);
lean_inc(v_ctors_2879_);
lean_dec_ref(v_val_2870_);
v___x_2880_ = l_List_lengthTR___redArg(v_ctors_2879_);
v___x_2881_ = lean_nat_dec_lt(v_idx_2842_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_dec(v_ctors_2879_);
lean_dec(v_us_2861_);
v___x_2882_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2883_ = l_Nat_reprFast(v_idx_2842_);
v___x_2884_ = lean_string_append(v___x_2882_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2886_ = lean_string_append(v___x_2884_, v___x_2885_);
v___x_2887_ = l_Nat_reprFast(v___x_2880_);
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 3);
lean_ctor_set(v___x_2872_, 0, v___x_2890_);
v___x_2892_ = v___x_2872_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = l_Lean_MessageData_ofFormat(v___x_2892_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2893_);
v___x_2895_ = v___x_2868_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2841_, v_goal_2840_, v___x_2895_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2896_;
}
}
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v___x_2880_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_name_2841_);
v___x_2899_ = l_List_get___redArg(v_ctors_2879_, v_idx_2842_);
lean_dec(v_ctors_2879_);
v___x_2900_ = l_Lean_mkConst(v___x_2899_, v_us_2861_);
v___x_2901_ = 0;
v___x_2902_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2902_, 0, v___x_2901_);
lean_ctor_set_uint8(v___x_2902_, 1, v___x_2881_);
lean_ctor_set_uint8(v___x_2902_, 2, v___x_2864_);
lean_ctor_set_uint8(v___x_2902_, 3, v___x_2881_);
v___x_2903_ = lean_box(0);
v___x_2904_ = l_Lean_MVarId_apply(v_goal_2840_, v___x_2900_, v___x_2902_, v___x_2903_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2904_;
}
}
}
}
else
{
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v_us_2861_);
lean_dec(v_expected_x3f_2843_);
lean_dec(v_idx_2842_);
v___y_2850_ = v___y_2844_;
v___y_2851_ = v___y_2845_;
v___y_2852_ = v___y_2846_;
v___y_2853_ = v___y_2847_;
goto v___jp_2849_;
}
}
}
}
else
{
lean_dec_ref(v___x_2859_);
lean_dec(v_expected_x3f_2843_);
lean_dec(v_idx_2842_);
v___y_2850_ = v___y_2844_;
v___y_2851_ = v___y_2845_;
v___y_2852_ = v___y_2846_;
v___y_2853_ = v___y_2847_;
goto v___jp_2849_;
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_expected_x3f_2843_);
lean_dec(v_idx_2842_);
lean_dec(v_name_2841_);
lean_dec(v_goal_2840_);
v_a_2937_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2857_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2857_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_expected_x3f_2843_);
lean_dec(v_idx_2842_);
lean_dec(v_name_2841_);
lean_dec(v_goal_2840_);
v_a_2945_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2856_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2856_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
v___jp_2849_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2855_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2841_, v_goal_2840_, v___x_2854_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2953_, lean_object* v_name_2954_, lean_object* v_idx_2955_, lean_object* v_expected_x3f_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2953_, v_name_2954_, v_idx_2955_, v_expected_x3f_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2963_, lean_object* v_idx_2964_, lean_object* v_expected_x3f_2965_, lean_object* v_goal_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; 
lean_inc(v_goal_2966_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2972_, 0, v_goal_2966_);
lean_closure_set(v___f_2972_, 1, v_name_2963_);
lean_closure_set(v___f_2972_, 2, v_idx_2964_);
lean_closure_set(v___f_2972_, 3, v_expected_x3f_2965_);
v___x_2973_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2966_, v___f_2972_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2974_, lean_object* v_idx_2975_, lean_object* v_expected_x3f_2976_, lean_object* v_goal_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_MVarId_nthConstructor(v_name_2974_, v_idx_2975_, v_expected_x3f_2976_, v_goal_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Meta_saveState___redArg(v___y_2986_, v___y_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
v___x_2992_ = lean_apply_5(v_x_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, lean_box(0));
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_a_2991_);
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2993_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3031_; 
v_a_3002_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3004_ = v___x_2992_;
v_isShared_3005_ = v_isSharedCheck_3031_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2992_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3031_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
uint8_t v___y_3007_; uint8_t v___x_3029_; 
v___x_3029_ = l_Lean_Exception_isInterrupt(v_a_3002_);
if (v___x_3029_ == 0)
{
uint8_t v___x_3030_; 
lean_inc(v_a_3002_);
v___x_3030_ = l_Lean_Exception_isRuntime(v_a_3002_);
v___y_3007_ = v___x_3030_;
goto v___jp_3006_;
}
else
{
v___y_3007_ = v___x_3029_;
goto v___jp_3006_;
}
v___jp_3006_:
{
if (v___y_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_del_object(v___x_3004_);
lean_dec(v_a_3002_);
v___x_3008_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2991_, v___y_2986_, v___y_2988_);
lean_dec(v_a_2991_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_3008_, 0);
lean_dec(v_unused_3017_);
v___x_3010_ = v___x_3008_;
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v___x_3008_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = lean_box(0);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_a_3018_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3008_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3008_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v___x_3027_; 
lean_dec(v_a_2991_);
if (v_isShared_3005_ == 0)
{
v___x_3027_ = v___x_3004_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3002_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_x_2984_);
v_a_3032_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2990_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2990_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3047_, lean_object* v_x_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3055_, v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
return v_res_3062_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3065_ = l_Lean_stringToMessageData(v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v___x_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_MVarId_apply(v_mvarId_3066_, v___x_3067_, v___x_3068_, v___x_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3092_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3092_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3092_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; 
if (lean_obj_tag(v_a_3076_) == 1)
{
lean_object* v_tail_3087_; 
v_tail_3087_ = lean_ctor_get(v_a_3076_, 1);
if (lean_obj_tag(v_tail_3087_) == 0)
{
lean_object* v_head_3088_; lean_object* v___x_3090_; 
v_head_3088_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_head_3088_);
lean_dec_ref_known(v_a_3076_, 2);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v_head_3088_);
v___x_3090_ = v___x_3078_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_head_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
else
{
lean_dec_ref_known(v_a_3076_, 2);
lean_del_object(v___x_3078_);
v___y_3081_ = v___y_3070_;
v___y_3082_ = v___y_3071_;
v___y_3083_ = v___y_3072_;
v___y_3084_ = v___y_3073_;
goto v___jp_3080_;
}
}
else
{
lean_del_object(v___x_3078_);
lean_dec(v_a_3076_);
v___y_3081_ = v___y_3070_;
v___y_3082_ = v___y_3071_;
v___y_3083_ = v___y_3072_;
v___y_3084_ = v___y_3073_;
goto v___jp_3080_;
}
v___jp_3080_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3086_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3085_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
return v___x_3086_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_a_3093_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3075_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3075_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3101_, lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v___x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3101_, v___x_3102_, v___x_3103_, v___x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3110_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3116_ = l_Lean_mkConst(v___x_3115_, v___x_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; 
v___x_3127_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3128_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3129_ = lean_box(0);
lean_inc(v_mvarId_3121_);
v___f_3130_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3130_, 0, v_mvarId_3121_);
lean_closure_set(v___f_3130_, 1, v___x_3127_);
lean_closure_set(v___f_3130_, 2, v___x_3128_);
lean_closure_set(v___f_3130_, 3, v___x_3129_);
v___x_3131_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3130_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3143_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3143_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3143_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
if (lean_obj_tag(v_a_3132_) == 0)
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_mvarId_3121_);
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_mvarId_3121_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3141_; 
lean_dec(v_mvarId_3121_);
v_val_3139_ = lean_ctor_get(v_a_3132_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_a_3132_, 1);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_val_3139_);
v___x_3141_ = v___x_3134_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_val_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_mvarId_3121_);
v_a_3144_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3131_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3131_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_MVarId_iffOfEq(v_mvarId_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
return v_res_3158_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_box(0);
v___x_3166_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3167_ = l_Lean_mkConst(v___x_3166_, v___x_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3168_, lean_object* v_mvarId_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___x_3182_; uint8_t v_foApprox_3183_; uint8_t v_ctxApprox_3184_; uint8_t v_quasiPatternApprox_3185_; uint8_t v_constApprox_3186_; uint8_t v_isDefEqStuckEx_3187_; uint8_t v_unificationHints_3188_; uint8_t v_proofIrrelevance_3189_; uint8_t v_assignSyntheticOpaque_3190_; uint8_t v_offsetCnstrs_3191_; uint8_t v_etaStruct_3192_; uint8_t v_univApprox_3193_; uint8_t v_iota_3194_; uint8_t v_beta_3195_; uint8_t v_proj_3196_; uint8_t v_zeta_3197_; uint8_t v_zetaDelta_3198_; uint8_t v_zetaUnused_3199_; uint8_t v_zetaHave_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3288_; 
v___x_3182_ = l_Lean_Meta_Context_config(v___y_3170_);
v_foApprox_3183_ = lean_ctor_get_uint8(v___x_3182_, 0);
v_ctxApprox_3184_ = lean_ctor_get_uint8(v___x_3182_, 1);
v_quasiPatternApprox_3185_ = lean_ctor_get_uint8(v___x_3182_, 2);
v_constApprox_3186_ = lean_ctor_get_uint8(v___x_3182_, 3);
v_isDefEqStuckEx_3187_ = lean_ctor_get_uint8(v___x_3182_, 4);
v_unificationHints_3188_ = lean_ctor_get_uint8(v___x_3182_, 5);
v_proofIrrelevance_3189_ = lean_ctor_get_uint8(v___x_3182_, 6);
v_assignSyntheticOpaque_3190_ = lean_ctor_get_uint8(v___x_3182_, 7);
v_offsetCnstrs_3191_ = lean_ctor_get_uint8(v___x_3182_, 8);
v_etaStruct_3192_ = lean_ctor_get_uint8(v___x_3182_, 10);
v_univApprox_3193_ = lean_ctor_get_uint8(v___x_3182_, 11);
v_iota_3194_ = lean_ctor_get_uint8(v___x_3182_, 12);
v_beta_3195_ = lean_ctor_get_uint8(v___x_3182_, 13);
v_proj_3196_ = lean_ctor_get_uint8(v___x_3182_, 14);
v_zeta_3197_ = lean_ctor_get_uint8(v___x_3182_, 15);
v_zetaDelta_3198_ = lean_ctor_get_uint8(v___x_3182_, 16);
v_zetaUnused_3199_ = lean_ctor_get_uint8(v___x_3182_, 17);
v_zetaHave_3200_ = lean_ctor_get_uint8(v___x_3182_, 18);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3202_ = v___x_3182_;
v_isShared_3203_ = v_isSharedCheck_3288_;
goto v_resetjp_3201_;
}
else
{
lean_dec(v___x_3182_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3288_;
goto v_resetjp_3201_;
}
v___jp_3175_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3181_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3180_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
v_resetjp_3201_:
{
uint8_t v_trackZetaDelta_3204_; lean_object* v_zetaDeltaSet_3205_; lean_object* v_lctx_3206_; lean_object* v_localInstances_3207_; lean_object* v_defEqCtx_x3f_3208_; lean_object* v_synthPendingDepth_3209_; lean_object* v_canUnfold_x3f_3210_; uint8_t v_univApprox_3211_; uint8_t v_inTypeClassResolution_3212_; uint8_t v_cacheInferType_3213_; lean_object* v_config_3215_; 
v_trackZetaDelta_3204_ = lean_ctor_get_uint8(v___y_3170_, sizeof(void*)*7);
v_zetaDeltaSet_3205_ = lean_ctor_get(v___y_3170_, 1);
v_lctx_3206_ = lean_ctor_get(v___y_3170_, 2);
v_localInstances_3207_ = lean_ctor_get(v___y_3170_, 3);
v_defEqCtx_x3f_3208_ = lean_ctor_get(v___y_3170_, 4);
v_synthPendingDepth_3209_ = lean_ctor_get(v___y_3170_, 5);
v_canUnfold_x3f_3210_ = lean_ctor_get(v___y_3170_, 6);
v_univApprox_3211_ = lean_ctor_get_uint8(v___y_3170_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3212_ = lean_ctor_get_uint8(v___y_3170_, sizeof(void*)*7 + 2);
v_cacheInferType_3213_ = lean_ctor_get_uint8(v___y_3170_, sizeof(void*)*7 + 3);
if (v_isShared_3203_ == 0)
{
v_config_3215_ = v___x_3202_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 0, v_foApprox_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 1, v_ctxApprox_3184_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 2, v_quasiPatternApprox_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 3, v_constApprox_3186_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 4, v_isDefEqStuckEx_3187_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 5, v_unificationHints_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 6, v_proofIrrelevance_3189_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 7, v_assignSyntheticOpaque_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 8, v_offsetCnstrs_3191_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 10, v_etaStruct_3192_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 11, v_univApprox_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 12, v_iota_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 13, v_beta_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 14, v_proj_3196_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 15, v_zeta_3197_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 16, v_zetaDelta_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 17, v_zetaUnused_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, 18, v_zetaHave_3200_);
v_config_3215_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
uint64_t v___x_3216_; uint64_t v___x_3217_; uint64_t v___x_3218_; uint64_t v___x_3219_; uint64_t v___x_3220_; uint64_t v_key_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_ctor_set_uint8(v_config_3215_, 9, v___x_3168_);
v___x_3216_ = l_Lean_Meta_Context_configKey(v___y_3170_);
v___x_3217_ = 3ULL;
v___x_3218_ = lean_uint64_shift_right(v___x_3216_, v___x_3217_);
v___x_3219_ = lean_uint64_shift_left(v___x_3218_, v___x_3217_);
v___x_3220_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3168_);
v_key_3221_ = lean_uint64_lor(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3222_, 0, v_config_3215_);
lean_ctor_set_uint64(v___x_3222_, sizeof(void*)*1, v_key_3221_);
lean_inc(v_canUnfold_x3f_3210_);
lean_inc(v_synthPendingDepth_3209_);
lean_inc(v_defEqCtx_x3f_3208_);
lean_inc_ref(v_localInstances_3207_);
lean_inc_ref(v_lctx_3206_);
lean_inc(v_zetaDeltaSet_3205_);
v___x_3223_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v_zetaDeltaSet_3205_);
lean_ctor_set(v___x_3223_, 2, v_lctx_3206_);
lean_ctor_set(v___x_3223_, 3, v_localInstances_3207_);
lean_ctor_set(v___x_3223_, 4, v_defEqCtx_x3f_3208_);
lean_ctor_set(v___x_3223_, 5, v_synthPendingDepth_3209_);
lean_ctor_set(v___x_3223_, 6, v_canUnfold_x3f_3210_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*7, v_trackZetaDelta_3204_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*7 + 1, v_univApprox_3211_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3212_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*7 + 3, v_cacheInferType_3213_);
lean_inc(v_mvarId_3169_);
v___x_3224_ = l_Lean_MVarId_getType_x27(v_mvarId_3169_, v___x_3223_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec_ref_known(v___x_3223_, 7);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3227_ = lean_unsigned_to_nat(3u);
v___x_3228_ = l_Lean_Expr_isAppOfArity(v_a_3225_, v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_dec(v_a_3225_);
lean_dec(v_mvarId_3169_);
v___x_3254_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3255_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3254_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3255_;
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = l_Lean_Expr_appFn_x21(v_a_3225_);
lean_dec(v_a_3225_);
v___x_3257_ = l_Lean_Expr_appArg_x21(v___x_3256_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = l_Lean_Meta_isProp(v___x_3257_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; uint8_t v___x_3260_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = lean_unbox(v_a_3259_);
lean_dec(v_a_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v_mvarId_3169_);
v___x_3261_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3262_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3261_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
else
{
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_mvarId_3169_);
v_a_3271_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3258_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3258_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
v___jp_3229_:
{
lean_object* v___x_3230_; uint8_t v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3230_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3231_ = 0;
v___x_3232_ = 0;
v___x_3233_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3233_, 0, v___x_3231_);
lean_ctor_set_uint8(v___x_3233_, 1, v___x_3228_);
lean_ctor_set_uint8(v___x_3233_, 2, v___x_3232_);
lean_ctor_set_uint8(v___x_3233_, 3, v___x_3228_);
v___x_3234_ = lean_box(0);
v___x_3235_ = l_Lean_MVarId_apply(v_mvarId_3169_, v___x_3230_, v___x_3233_, v___x_3234_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3245_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3245_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3245_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
if (lean_obj_tag(v_a_3236_) == 1)
{
lean_object* v_tail_3240_; 
v_tail_3240_ = lean_ctor_get(v_a_3236_, 1);
if (lean_obj_tag(v_tail_3240_) == 0)
{
lean_object* v_head_3241_; lean_object* v___x_3243_; 
v_head_3241_ = lean_ctor_get(v_a_3236_, 0);
lean_inc(v_head_3241_);
lean_dec_ref_known(v_a_3236_, 2);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v_head_3241_);
v___x_3243_ = v___x_3238_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_head_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
else
{
lean_dec_ref_known(v_a_3236_, 2);
lean_del_object(v___x_3238_);
v___y_3176_ = v___y_3170_;
v___y_3177_ = v___y_3171_;
v___y_3178_ = v___y_3172_;
v___y_3179_ = v___y_3173_;
goto v___jp_3175_;
}
}
else
{
lean_del_object(v___x_3238_);
lean_dec(v_a_3236_);
v___y_3176_ = v___y_3170_;
v___y_3177_ = v___y_3171_;
v___y_3178_ = v___y_3172_;
v___y_3179_ = v___y_3173_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
v_a_3246_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3235_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3235_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec(v_mvarId_3169_);
v_a_3279_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3224_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3224_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3289_, lean_object* v_mvarId_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_2435__boxed_3296_; lean_object* v_res_3297_; 
v___x_2435__boxed_3296_ = lean_unbox(v___x_3289_);
v_res_3297_ = l_Lean_MVarId_propext___lam__0(v___x_2435__boxed_3296_, v_mvarId_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; 
v___x_3304_ = 2;
v___x_3305_ = lean_box(v___x_3304_);
lean_inc(v_mvarId_3298_);
v___f_3306_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3306_, 0, v___x_3305_);
lean_closure_set(v___f_3306_, 1, v_mvarId_3298_);
v___x_3307_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3306_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3319_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3319_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3319_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
if (lean_obj_tag(v_a_3308_) == 0)
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v_mvarId_3298_);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_mvarId_3298_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3317_; 
lean_dec(v_mvarId_3298_);
v_val_3315_ = lean_ctor_get(v_a_3308_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v_a_3308_, 1);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v_val_3315_);
v___x_3317_ = v___x_3310_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_val_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_mvarId_3298_);
v_a_3320_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3307_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3307_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_MVarId_propext(v_mvarId_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3334_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3335_; uint64_t v___x_3336_; 
v___x_3335_ = 2;
v___x_3336_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3343_, lean_object* v___x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
lean_inc(v_mvarId_3343_);
v___x_3350_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3343_, v___x_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v___x_3351_; uint8_t v_foApprox_3352_; uint8_t v_ctxApprox_3353_; uint8_t v_quasiPatternApprox_3354_; uint8_t v_constApprox_3355_; uint8_t v_isDefEqStuckEx_3356_; uint8_t v_unificationHints_3357_; uint8_t v_proofIrrelevance_3358_; uint8_t v_assignSyntheticOpaque_3359_; uint8_t v_offsetCnstrs_3360_; uint8_t v_etaStruct_3361_; uint8_t v_univApprox_3362_; uint8_t v_iota_3363_; uint8_t v_beta_3364_; uint8_t v_proj_3365_; uint8_t v_zeta_3366_; uint8_t v_zetaDelta_3367_; uint8_t v_zetaUnused_3368_; uint8_t v_zetaHave_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref_known(v___x_3350_, 1);
v___x_3351_ = l_Lean_Meta_Context_config(v___y_3345_);
v_foApprox_3352_ = lean_ctor_get_uint8(v___x_3351_, 0);
v_ctxApprox_3353_ = lean_ctor_get_uint8(v___x_3351_, 1);
v_quasiPatternApprox_3354_ = lean_ctor_get_uint8(v___x_3351_, 2);
v_constApprox_3355_ = lean_ctor_get_uint8(v___x_3351_, 3);
v_isDefEqStuckEx_3356_ = lean_ctor_get_uint8(v___x_3351_, 4);
v_unificationHints_3357_ = lean_ctor_get_uint8(v___x_3351_, 5);
v_proofIrrelevance_3358_ = lean_ctor_get_uint8(v___x_3351_, 6);
v_assignSyntheticOpaque_3359_ = lean_ctor_get_uint8(v___x_3351_, 7);
v_offsetCnstrs_3360_ = lean_ctor_get_uint8(v___x_3351_, 8);
v_etaStruct_3361_ = lean_ctor_get_uint8(v___x_3351_, 10);
v_univApprox_3362_ = lean_ctor_get_uint8(v___x_3351_, 11);
v_iota_3363_ = lean_ctor_get_uint8(v___x_3351_, 12);
v_beta_3364_ = lean_ctor_get_uint8(v___x_3351_, 13);
v_proj_3365_ = lean_ctor_get_uint8(v___x_3351_, 14);
v_zeta_3366_ = lean_ctor_get_uint8(v___x_3351_, 15);
v_zetaDelta_3367_ = lean_ctor_get_uint8(v___x_3351_, 16);
v_zetaUnused_3368_ = lean_ctor_get_uint8(v___x_3351_, 17);
v_zetaHave_3369_ = lean_ctor_get_uint8(v___x_3351_, 18);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3371_ = v___x_3351_;
v_isShared_3372_ = v_isSharedCheck_3439_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3351_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3439_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v_trackZetaDelta_3373_; lean_object* v_zetaDeltaSet_3374_; lean_object* v_lctx_3375_; lean_object* v_localInstances_3376_; lean_object* v_defEqCtx_x3f_3377_; lean_object* v_synthPendingDepth_3378_; lean_object* v_canUnfold_x3f_3379_; uint8_t v_univApprox_3380_; uint8_t v_inTypeClassResolution_3381_; uint8_t v_cacheInferType_3382_; uint8_t v___x_3383_; lean_object* v_config_3385_; 
v_trackZetaDelta_3373_ = lean_ctor_get_uint8(v___y_3345_, sizeof(void*)*7);
v_zetaDeltaSet_3374_ = lean_ctor_get(v___y_3345_, 1);
v_lctx_3375_ = lean_ctor_get(v___y_3345_, 2);
v_localInstances_3376_ = lean_ctor_get(v___y_3345_, 3);
v_defEqCtx_x3f_3377_ = lean_ctor_get(v___y_3345_, 4);
v_synthPendingDepth_3378_ = lean_ctor_get(v___y_3345_, 5);
v_canUnfold_x3f_3379_ = lean_ctor_get(v___y_3345_, 6);
v_univApprox_3380_ = lean_ctor_get_uint8(v___y_3345_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3381_ = lean_ctor_get_uint8(v___y_3345_, sizeof(void*)*7 + 2);
v_cacheInferType_3382_ = lean_ctor_get_uint8(v___y_3345_, sizeof(void*)*7 + 3);
v___x_3383_ = 2;
if (v_isShared_3372_ == 0)
{
v_config_3385_ = v___x_3371_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 0, v_foApprox_3352_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 1, v_ctxApprox_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 2, v_quasiPatternApprox_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 3, v_constApprox_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 4, v_isDefEqStuckEx_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 5, v_unificationHints_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 6, v_proofIrrelevance_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 7, v_assignSyntheticOpaque_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 8, v_offsetCnstrs_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 10, v_etaStruct_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 11, v_univApprox_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 12, v_iota_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 13, v_beta_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 14, v_proj_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 15, v_zeta_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 16, v_zetaDelta_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 17, v_zetaUnused_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3438_, 18, v_zetaHave_3369_);
v_config_3385_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
uint64_t v___x_3386_; uint64_t v___x_3387_; uint64_t v___x_3388_; uint64_t v___x_3389_; uint64_t v___x_3390_; uint64_t v_key_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_ctor_set_uint8(v_config_3385_, 9, v___x_3383_);
v___x_3386_ = l_Lean_Meta_Context_configKey(v___y_3345_);
v___x_3387_ = 3ULL;
v___x_3388_ = lean_uint64_shift_right(v___x_3386_, v___x_3387_);
v___x_3389_ = lean_uint64_shift_left(v___x_3388_, v___x_3387_);
v___x_3390_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3391_ = lean_uint64_lor(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3392_, 0, v_config_3385_);
lean_ctor_set_uint64(v___x_3392_, sizeof(void*)*1, v_key_3391_);
lean_inc(v_canUnfold_x3f_3379_);
lean_inc(v_synthPendingDepth_3378_);
lean_inc(v_defEqCtx_x3f_3377_);
lean_inc_ref(v_localInstances_3376_);
lean_inc_ref(v_lctx_3375_);
lean_inc(v_zetaDeltaSet_3374_);
v___x_3393_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v_zetaDeltaSet_3374_);
lean_ctor_set(v___x_3393_, 2, v_lctx_3375_);
lean_ctor_set(v___x_3393_, 3, v_localInstances_3376_);
lean_ctor_set(v___x_3393_, 4, v_defEqCtx_x3f_3377_);
lean_ctor_set(v___x_3393_, 5, v_synthPendingDepth_3378_);
lean_ctor_set(v___x_3393_, 6, v_canUnfold_x3f_3379_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*7, v_trackZetaDelta_3373_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*7 + 1, v_univApprox_3380_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3381_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*7 + 3, v_cacheInferType_3382_);
lean_inc(v_mvarId_3343_);
v___x_3394_ = l_Lean_MVarId_getType_x27(v_mvarId_3343_, v___x_3393_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec_ref_known(v___x_3393_, 7);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3397_ = lean_unsigned_to_nat(4u);
v___x_3398_ = l_Lean_Expr_isAppOfArity(v_a_3395_, v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v_a_3395_);
lean_dec(v_mvarId_3343_);
v___x_3399_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3400_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3399_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3401_ = l_Lean_Expr_appFn_x21(v_a_3395_);
v___x_3402_ = l_Lean_Expr_appFn_x21(v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = l_Lean_Expr_appArg_x21(v___x_3402_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = l_Lean_Expr_appArg_x21(v_a_3395_);
lean_dec(v_a_3395_);
v___x_3405_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3406_ = lean_unsigned_to_nat(2u);
v___x_3407_ = lean_mk_empty_array_with_capacity(v___x_3406_);
v___x_3408_ = lean_array_push(v___x_3407_, v___x_3403_);
v___x_3409_ = lean_array_push(v___x_3408_, v___x_3404_);
v___x_3410_ = l_Lean_Meta_mkAppM(v___x_3405_, v___x_3409_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3343_, v_a_3411_, v___y_3346_);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v___x_3412_, 0);
lean_dec(v_unused_3421_);
v___x_3414_ = v___x_3412_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v___x_3412_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(v___x_3398_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_mvarId_3343_);
v_a_3422_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3410_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3410_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_mvarId_3343_);
v_a_3430_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3394_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3394_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_mvarId_3343_);
v_a_3440_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3350_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3350_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3448_, lean_object* v___x_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3448_, v___x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
if (lean_obj_tag(v_a_3463_) == 0)
{
uint8_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3467_ = 0;
v___x_3468_ = lean_box(v___x_3467_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3468_);
v___x_3470_ = v___x_3465_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
else
{
lean_object* v_val_3472_; lean_object* v___x_3474_; 
v_val_3472_ = lean_ctor_get(v_a_3463_, 0);
lean_inc(v_val_3472_);
lean_dec_ref_known(v_a_3463_, 1);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_val_3472_);
v___x_3474_ = v___x_3465_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_val_3472_);
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
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_a_3477_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3462_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3462_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; 
v___x_3501_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3495_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3502_, 0, v_mvarId_3495_);
lean_closure_set(v___f_3502_, 1, v___x_3501_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3503_, 0, v___f_3502_);
v___x_3504_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3495_, v___f_3503_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3516_, lean_object* v___x_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; 
lean_inc(v_mvarId_3516_);
v___x_3523_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3516_, v___x_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; uint8_t v_foApprox_3525_; uint8_t v_ctxApprox_3526_; uint8_t v_quasiPatternApprox_3527_; uint8_t v_constApprox_3528_; uint8_t v_isDefEqStuckEx_3529_; uint8_t v_unificationHints_3530_; uint8_t v_proofIrrelevance_3531_; uint8_t v_assignSyntheticOpaque_3532_; uint8_t v_offsetCnstrs_3533_; uint8_t v_etaStruct_3534_; uint8_t v_univApprox_3535_; uint8_t v_iota_3536_; uint8_t v_beta_3537_; uint8_t v_proj_3538_; uint8_t v_zeta_3539_; uint8_t v_zetaDelta_3540_; uint8_t v_zetaUnused_3541_; uint8_t v_zetaHave_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref_known(v___x_3523_, 1);
v___x_3524_ = l_Lean_Meta_Context_config(v___y_3518_);
v_foApprox_3525_ = lean_ctor_get_uint8(v___x_3524_, 0);
v_ctxApprox_3526_ = lean_ctor_get_uint8(v___x_3524_, 1);
v_quasiPatternApprox_3527_ = lean_ctor_get_uint8(v___x_3524_, 2);
v_constApprox_3528_ = lean_ctor_get_uint8(v___x_3524_, 3);
v_isDefEqStuckEx_3529_ = lean_ctor_get_uint8(v___x_3524_, 4);
v_unificationHints_3530_ = lean_ctor_get_uint8(v___x_3524_, 5);
v_proofIrrelevance_3531_ = lean_ctor_get_uint8(v___x_3524_, 6);
v_assignSyntheticOpaque_3532_ = lean_ctor_get_uint8(v___x_3524_, 7);
v_offsetCnstrs_3533_ = lean_ctor_get_uint8(v___x_3524_, 8);
v_etaStruct_3534_ = lean_ctor_get_uint8(v___x_3524_, 10);
v_univApprox_3535_ = lean_ctor_get_uint8(v___x_3524_, 11);
v_iota_3536_ = lean_ctor_get_uint8(v___x_3524_, 12);
v_beta_3537_ = lean_ctor_get_uint8(v___x_3524_, 13);
v_proj_3538_ = lean_ctor_get_uint8(v___x_3524_, 14);
v_zeta_3539_ = lean_ctor_get_uint8(v___x_3524_, 15);
v_zetaDelta_3540_ = lean_ctor_get_uint8(v___x_3524_, 16);
v_zetaUnused_3541_ = lean_ctor_get_uint8(v___x_3524_, 17);
v_zetaHave_3542_ = lean_ctor_get_uint8(v___x_3524_, 18);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3544_ = v___x_3524_;
v_isShared_3545_ = v_isSharedCheck_3611_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v___x_3524_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3611_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
uint8_t v_trackZetaDelta_3546_; lean_object* v_zetaDeltaSet_3547_; lean_object* v_lctx_3548_; lean_object* v_localInstances_3549_; lean_object* v_defEqCtx_x3f_3550_; lean_object* v_synthPendingDepth_3551_; lean_object* v_canUnfold_x3f_3552_; uint8_t v_univApprox_3553_; uint8_t v_inTypeClassResolution_3554_; uint8_t v_cacheInferType_3555_; uint8_t v___x_3556_; lean_object* v_config_3558_; 
v_trackZetaDelta_3546_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*7);
v_zetaDeltaSet_3547_ = lean_ctor_get(v___y_3518_, 1);
v_lctx_3548_ = lean_ctor_get(v___y_3518_, 2);
v_localInstances_3549_ = lean_ctor_get(v___y_3518_, 3);
v_defEqCtx_x3f_3550_ = lean_ctor_get(v___y_3518_, 4);
v_synthPendingDepth_3551_ = lean_ctor_get(v___y_3518_, 5);
v_canUnfold_x3f_3552_ = lean_ctor_get(v___y_3518_, 6);
v_univApprox_3553_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3554_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*7 + 2);
v_cacheInferType_3555_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*7 + 3);
v___x_3556_ = 2;
if (v_isShared_3545_ == 0)
{
v_config_3558_ = v___x_3544_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 0, v_foApprox_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 1, v_ctxApprox_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 2, v_quasiPatternApprox_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 3, v_constApprox_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 4, v_isDefEqStuckEx_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 5, v_unificationHints_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 6, v_proofIrrelevance_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 7, v_assignSyntheticOpaque_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 8, v_offsetCnstrs_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 10, v_etaStruct_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 11, v_univApprox_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 12, v_iota_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 13, v_beta_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 14, v_proj_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 15, v_zeta_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 16, v_zetaDelta_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 17, v_zetaUnused_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, 18, v_zetaHave_3542_);
v_config_3558_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
uint64_t v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; uint64_t v___x_3562_; uint64_t v___x_3563_; uint64_t v_key_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_ctor_set_uint8(v_config_3558_, 9, v___x_3556_);
v___x_3559_ = l_Lean_Meta_Context_configKey(v___y_3518_);
v___x_3560_ = 3ULL;
v___x_3561_ = lean_uint64_shift_right(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_uint64_shift_left(v___x_3561_, v___x_3560_);
v___x_3563_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3564_ = lean_uint64_lor(v___x_3562_, v___x_3563_);
v___x_3565_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3565_, 0, v_config_3558_);
lean_ctor_set_uint64(v___x_3565_, sizeof(void*)*1, v_key_3564_);
lean_inc(v_canUnfold_x3f_3552_);
lean_inc(v_synthPendingDepth_3551_);
lean_inc(v_defEqCtx_x3f_3550_);
lean_inc_ref(v_localInstances_3549_);
lean_inc_ref(v_lctx_3548_);
lean_inc(v_zetaDeltaSet_3547_);
v___x_3566_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
lean_ctor_set(v___x_3566_, 1, v_zetaDeltaSet_3547_);
lean_ctor_set(v___x_3566_, 2, v_lctx_3548_);
lean_ctor_set(v___x_3566_, 3, v_localInstances_3549_);
lean_ctor_set(v___x_3566_, 4, v_defEqCtx_x3f_3550_);
lean_ctor_set(v___x_3566_, 5, v_synthPendingDepth_3551_);
lean_ctor_set(v___x_3566_, 6, v_canUnfold_x3f_3552_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7, v_trackZetaDelta_3546_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 1, v_univApprox_3553_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3554_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*7 + 3, v_cacheInferType_3555_);
lean_inc(v_mvarId_3516_);
v___x_3567_ = l_Lean_MVarId_getType_x27(v_mvarId_3516_, v___x_3566_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec_ref_known(v___x_3566_, 7);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3570_ = lean_unsigned_to_nat(3u);
v___x_3571_ = l_Lean_Expr_isAppOfArity(v_a_3568_, v___x_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v_a_3568_);
lean_dec(v_mvarId_3516_);
v___x_3572_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3573_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3572_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
return v___x_3573_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3574_ = l_Lean_Expr_appFn_x21(v_a_3568_);
v___x_3575_ = l_Lean_Expr_appArg_x21(v___x_3574_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = l_Lean_Expr_appArg_x21(v_a_3568_);
lean_dec(v_a_3568_);
v___x_3577_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3578_ = lean_unsigned_to_nat(2u);
v___x_3579_ = lean_mk_empty_array_with_capacity(v___x_3578_);
v___x_3580_ = lean_array_push(v___x_3579_, v___x_3575_);
v___x_3581_ = lean_array_push(v___x_3580_, v___x_3576_);
v___x_3582_ = l_Lean_Meta_mkAppM(v___x_3577_, v___x_3581_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3592_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3516_, v_a_3583_, v___y_3519_);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v___x_3584_, 0);
lean_dec(v_unused_3593_);
v___x_3586_ = v___x_3584_;
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v___x_3584_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3588_ = lean_box(v___x_3571_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3588_);
v___x_3590_ = v___x_3586_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_mvarId_3516_);
v_a_3594_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3582_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3582_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_mvarId_3516_);
v_a_3602_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3567_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3567_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_mvarId_3516_);
v_a_3612_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3523_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3523_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3620_, lean_object* v___x_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3620_, v___x_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; 
v___x_3637_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3631_);
v___f_3638_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3638_, 0, v_mvarId_3631_);
lean_closure_set(v___f_3638_, 1, v___x_3637_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3639_, 0, v___f_3638_);
v___x_3640_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3631_, v___f_3639_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
return v_res_3647_;
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
