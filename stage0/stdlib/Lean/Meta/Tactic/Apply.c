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
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
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
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
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
lean_object* v___x_112_; uint8_t v_foApprox_113_; uint8_t v_ctxApprox_114_; uint8_t v_quasiPatternApprox_115_; uint8_t v_constApprox_116_; uint8_t v_isDefEqStuckEx_117_; uint8_t v_unificationHints_118_; uint8_t v_proofIrrelevance_119_; uint8_t v_assignSyntheticOpaque_120_; uint8_t v_offsetCnstrs_121_; uint8_t v_etaStruct_122_; uint8_t v_univApprox_123_; uint8_t v_iota_124_; uint8_t v_beta_125_; uint8_t v_proj_126_; uint8_t v_zeta_127_; uint8_t v_zetaDelta_128_; uint8_t v_zetaUnused_129_; uint8_t v_zetaHave_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_172_; 
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
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_172_ == 0)
{
v___x_132_ = v___x_112_;
v_isShared_133_ = v_isSharedCheck_172_;
goto v_resetjp_131_;
}
else
{
lean_dec(v___x_112_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_172_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v_trackZetaDelta_134_; lean_object* v_zetaDeltaSet_135_; lean_object* v_lctx_136_; lean_object* v_localInstances_137_; lean_object* v_defEqCtx_x3f_138_; lean_object* v_synthPendingDepth_139_; lean_object* v_canUnfold_x3f_140_; uint8_t v_univApprox_141_; uint8_t v_inTypeClassResolution_142_; uint8_t v_cacheInferType_143_; uint8_t v___x_144_; lean_object* v_config_146_; 
v_trackZetaDelta_134_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7);
v_zetaDeltaSet_135_ = lean_ctor_get(v_a_107_, 1);
lean_inc(v_zetaDeltaSet_135_);
v_lctx_136_ = lean_ctor_get(v_a_107_, 2);
lean_inc_ref(v_lctx_136_);
v_localInstances_137_ = lean_ctor_get(v_a_107_, 3);
lean_inc_ref(v_localInstances_137_);
v_defEqCtx_x3f_138_ = lean_ctor_get(v_a_107_, 4);
lean_inc(v_defEqCtx_x3f_138_);
v_synthPendingDepth_139_ = lean_ctor_get(v_a_107_, 5);
lean_inc(v_synthPendingDepth_139_);
v_canUnfold_x3f_140_ = lean_ctor_get(v_a_107_, 6);
lean_inc(v_canUnfold_x3f_140_);
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
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 0, v_foApprox_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 1, v_ctxApprox_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 2, v_quasiPatternApprox_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 3, v_constApprox_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 4, v_isDefEqStuckEx_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 5, v_unificationHints_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 6, v_proofIrrelevance_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 7, v_assignSyntheticOpaque_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 8, v_offsetCnstrs_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 10, v_etaStruct_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 11, v_univApprox_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 12, v_iota_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 13, v_beta_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 14, v_proj_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 15, v_zeta_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 16, v_zetaDelta_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 17, v_zetaUnused_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, 18, v_zetaHave_130_);
v_config_146_ = v_reuseFailAlloc_171_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
uint64_t v___x_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_163_; 
lean_ctor_set_uint8(v_config_146_, 9, v___x_144_);
v___x_147_ = l_Lean_Meta_Context_configKey(v_a_107_);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; lean_object* v_unused_165_; lean_object* v_unused_166_; lean_object* v_unused_167_; lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; 
v_unused_164_ = lean_ctor_get(v_a_107_, 6);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_a_107_, 5);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_a_107_, 4);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_a_107_, 3);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_a_107_, 2);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_a_107_, 1);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_a_107_, 0);
lean_dec(v_unused_170_);
v___x_149_ = v_a_107_;
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_a_107_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint64_t v___x_151_; uint64_t v___x_152_; lean_object* v___f_153_; uint8_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v_key_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_151_ = 2ULL;
v___x_152_ = lean_uint64_shift_right(v___x_147_, v___x_151_);
v___f_153_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_154_ = 0;
v___x_155_ = lean_uint64_shift_left(v___x_152_, v___x_151_);
v___x_156_ = lean_uint64_once(&l_Lean_Meta_getExpectedNumArgsAux___closed__1, &l_Lean_Meta_getExpectedNumArgsAux___closed__1_once, _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1);
v_key_157_ = lean_uint64_lor(v___x_155_, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_158_, 0, v_config_146_);
lean_ctor_set_uint64(v___x_158_, sizeof(void*)*1, v_key_157_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_158_);
v___x_160_ = v___x_149_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_zetaDeltaSet_135_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_lctx_136_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_localInstances_137_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_defEqCtx_x3f_138_);
lean_ctor_set(v_reuseFailAlloc_162_, 5, v_synthPendingDepth_139_);
lean_ctor_set(v_reuseFailAlloc_162_, 6, v_canUnfold_x3f_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*7, v_trackZetaDelta_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*7 + 1, v_univApprox_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*7 + 2, v_inTypeClassResolution_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*7 + 3, v_cacheInferType_143_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_106_, v___f_153_, v___x_154_, v___x_154_, v___x_160_, v_a_108_, v_a_109_, v_a_110_);
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_fst_191_; lean_object* v___x_193_; 
v_fst_191_ = lean_ctor_get(v_a_187_, 0);
lean_inc(v_fst_191_);
lean_dec(v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_fst_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_fst_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_186_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_186_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_getExpectedNumArgs(v_e_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v_res_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_224_ = l_Lean_MessageData_ofFormat(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v___y_227_, lean_object* v_targetType_228_, lean_object* v___y_229_, lean_object* v_term_x3f_230_, lean_object* v_conclusionType_x3f_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
lean_inc(v___y_235_);
lean_inc_ref(v___y_234_);
lean_inc(v___y_233_);
lean_inc_ref(v___y_232_);
v___x_237_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_227_, v_targetType_228_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_279_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_279_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_279_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_279_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_278_; 
v_fst_242_ = lean_ctor_get(v_a_238_, 0);
v_snd_243_ = lean_ctor_get(v_a_238_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_278_ == 0)
{
v___x_245_ = v_a_238_;
v_isShared_246_ = v_isSharedCheck_278_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
lean_dec(v_a_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_278_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_266_; 
if (lean_obj_tag(v_conclusionType_x3f_231_) == 0)
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_266_ = v___x_277_;
goto v___jp_265_;
}
v___jp_247_:
{
lean_object* v___x_252_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 7);
lean_ctor_set(v___x_245_, 1, v___y_250_);
lean_ctor_set(v___x_245_, 0, v___y_248_);
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___y_248_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___y_250_);
v___x_252_ = v_reuseFailAlloc_264_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_253_ = l_Lean_indentExpr(v_fst_242_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_indentExpr(v_snd_243_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___y_229_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___y_249_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_260_);
v___x_262_ = v___x_240_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; 
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
v___x_267_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_242_, v_snd_243_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
v___x_270_ = l_Lean_stringToMessageData(v___y_266_);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
if (lean_obj_tag(v_term_x3f_230_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_248_ = v___x_273_;
v___y_249_ = v_a_268_;
v___y_250_ = v___x_274_;
goto v___jp_247_;
}
else
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v_term_x3f_230_, 0);
lean_inc(v_val_275_);
lean_dec_ref(v_term_x3f_230_);
v___y_248_ = v___x_273_;
v___y_249_ = v_a_268_;
v___y_250_ = v_val_275_;
goto v___jp_247_;
}
}
else
{
lean_dec_ref(v___y_266_);
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_dec(v_fst_242_);
lean_del_object(v___x_240_);
lean_dec(v_term_x3f_230_);
lean_dec_ref(v___y_229_);
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v_term_x3f_230_);
lean_dec_ref(v___y_229_);
v_a_280_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_237_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_237_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v___y_288_, lean_object* v_targetType_289_, lean_object* v___y_290_, lean_object* v_term_x3f_291_, lean_object* v_conclusionType_x3f_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v___y_288_, v_targetType_289_, v___y_290_, v_term_x3f_291_, v_conclusionType_x3f_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v_conclusionType_x3f_292_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_311_, lean_object* v_eType_312_, lean_object* v_conclusionType_x3f_313_, lean_object* v_targetType_314_, lean_object* v_term_x3f_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_344_; 
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
if (lean_obj_tag(v_conclusionType_x3f_313_) == 0)
{
lean_inc_ref(v_eType_312_);
v___y_344_ = v_eType_312_;
goto v___jp_343_;
}
else
{
lean_object* v_val_349_; 
v_val_349_ = lean_ctor_get(v_conclusionType_x3f_313_, 0);
lean_inc(v_val_349_);
v___y_344_ = v_val_349_;
goto v___jp_343_;
}
v___jp_322_:
{
lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc_ref(v_targetType_314_);
v___f_325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_325_, 0, v___y_323_);
lean_closure_set(v___f_325_, 1, v_targetType_314_);
lean_closure_set(v___f_325_, 2, v___y_324_);
lean_closure_set(v___f_325_, 3, v_term_x3f_315_);
lean_closure_set(v___f_325_, 4, v_conclusionType_x3f_313_);
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_array_push(v___x_327_, v_eType_312_);
v___x_329_ = lean_array_push(v___x_328_, v_targetType_314_);
v___x_330_ = l_Lean_MessageData_ofLazyM(v___f_325_, v___x_329_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = l_Lean_Meta_throwTacticEx___redArg(v___x_321_, v_mvarId_311_, v___x_331_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_335_);
lean_ctor_set(v___x_337_, 1, v___y_336_);
v___x_338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_inc_ref(v_eType_312_);
v___x_340_ = l_Lean_indentExpr(v_eType_312_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = l_Lean_MessageData_note(v___x_341_);
v___y_323_ = v___y_334_;
v___y_324_ = v___x_342_;
goto v___jp_322_;
}
v___jp_343_:
{
if (lean_obj_tag(v_conclusionType_x3f_313_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
v___y_323_ = v___y_344_;
v___y_324_ = v___x_345_;
goto v___jp_322_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
if (lean_obj_tag(v_term_x3f_315_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_334_ = v___y_344_;
v___y_335_ = v___x_346_;
v___y_336_ = v___x_347_;
goto v___jp_333_;
}
else
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v_term_x3f_315_, 0);
lean_inc(v_val_348_);
v___y_334_ = v___y_344_;
v___y_335_ = v___x_346_;
v___y_336_ = v_val_348_;
goto v___jp_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_350_, lean_object* v_eType_351_, lean_object* v_conclusionType_x3f_352_, lean_object* v_targetType_353_, lean_object* v_term_x3f_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_350_, v_eType_351_, v_conclusionType_x3f_352_, v_targetType_353_, v_term_x3f_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_361_, lean_object* v_mvarId_362_, lean_object* v_eType_363_, lean_object* v_conclusionType_x3f_364_, lean_object* v_targetType_365_, lean_object* v_term_x3f_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_362_, v_eType_363_, v_conclusionType_x3f_364_, v_targetType_365_, v_term_x3f_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_373_, lean_object* v_mvarId_374_, lean_object* v_eType_375_, lean_object* v_conclusionType_x3f_376_, lean_object* v_targetType_377_, lean_object* v_term_x3f_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_373_, v_mvarId_374_, v_eType_375_, v_conclusionType_x3f_376_, v_targetType_377_, v_term_x3f_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_385_, lean_object* v_snd_386_, lean_object* v_fst_387_, lean_object* v_____r_388_, uint8_t v_progressAfterEx_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_a_385_);
v___x_396_ = lean_box(v_progressAfterEx_389_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_snd_386_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_fst_387_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_401_, lean_object* v_snd_402_, lean_object* v_fst_403_, lean_object* v_____r_404_, lean_object* v_progressAfterEx_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v_progressAfterEx_boxed_411_; lean_object* v_res_412_; 
v_progressAfterEx_boxed_411_ = lean_unbox(v_progressAfterEx_405_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_401_, v_snd_402_, v_fst_403_, v_____r_404_, v_progressAfterEx_boxed_411_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_412_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_417_ = l_Lean_MessageData_ofFormat(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_420_, lean_object* v_tacticName_421_, lean_object* v_mvarId_422_, lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_a_433_; lean_object* v_fst_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_mvarId_422_);
lean_dec(v_tacticName_421_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_b_426_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v_a_445_);
v___x_446_ = lean_infer_type(v_a_445_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_snd_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_541_; 
v_snd_447_ = lean_ctor_get(v_b_426_, 1);
lean_inc(v_snd_447_);
v_a_448_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_541_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_541_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_541_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_fst_452_; lean_object* v_fst_453_; lean_object* v_snd_454_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v_a_464_; lean_object* v___y_468_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_fst_452_ = lean_ctor_get(v_b_426_, 0);
lean_inc(v_fst_452_);
lean_dec_ref(v_b_426_);
v_fst_453_ = lean_ctor_get(v_snd_447_, 0);
lean_inc(v_fst_453_);
v_snd_454_ = lean_ctor_get(v_snd_447_, 1);
lean_inc(v_snd_454_);
lean_dec(v_snd_447_);
v___x_529_ = lean_box(0);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_530_ = l_Lean_Meta_synthInstance(v_a_448_, v___x_529_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = lean_array_get_size(v_snd_454_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
lean_inc(v_snd_454_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_531_, v_snd_454_, v_fst_452_, v___x_535_, v___x_443_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
v___y_468_ = v___x_536_;
goto v___jp_467_;
}
else
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = lean_unbox(v_fst_453_);
lean_inc(v_snd_454_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_531_, v_snd_454_, v_fst_452_, v___x_537_, v___x_538_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
v___y_468_ = v___x_539_;
goto v___jp_467_;
}
}
else
{
lean_object* v_a_540_; 
lean_dec(v_fst_452_);
v_a_540_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_530_);
v_a_464_ = v_a_540_;
goto v___jp_463_;
}
v___jp_455_:
{
if (v___y_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_del_object(v___x_450_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___y_456_);
lean_inc(v_a_445_);
v___x_459_ = lean_array_push(v_snd_454_, v_a_445_);
v_fst_438_ = v___x_458_;
v_fst_439_ = v_fst_453_;
v_snd_440_ = v___x_459_;
goto v___jp_437_;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_snd_454_);
lean_dec(v_fst_453_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_mvarId_422_);
lean_dec(v_tacticName_421_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___y_456_);
v___x_461_ = v___x_450_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___y_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
v___jp_463_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Exception_isInterrupt(v_a_464_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
lean_inc_ref(v_a_464_);
v___x_466_ = l_Lean_Exception_isRuntime(v_a_464_);
v___y_456_ = v_a_464_;
v___y_457_ = v___x_466_;
goto v___jp_455_;
}
else
{
v___y_456_ = v_a_464_;
v___y_457_ = v___x_465_;
goto v___jp_455_;
}
}
v___jp_467_:
{
if (lean_obj_tag(v___y_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_snd_470_; lean_object* v_snd_471_; lean_object* v_fst_472_; 
lean_dec(v_snd_454_);
lean_dec(v_fst_453_);
lean_del_object(v___x_450_);
v_a_469_ = lean_ctor_get(v___y_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___y_468_);
v_snd_470_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_snd_470_);
v_snd_471_ = lean_ctor_get(v_snd_470_, 1);
lean_inc(v_snd_471_);
v_fst_472_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_472_);
lean_dec(v_a_469_);
if (lean_obj_tag(v_fst_472_) == 1)
{
lean_object* v_fst_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_523_; 
v_fst_473_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_snd_470_, 1);
lean_dec(v_unused_524_);
v___x_475_ = v_snd_470_;
v_isShared_476_ = v_isSharedCheck_523_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_fst_473_);
lean_dec(v_snd_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_523_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_522_; 
v_fst_477_ = lean_ctor_get(v_snd_471_, 0);
v_snd_478_ = lean_ctor_get(v_snd_471_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_snd_471_);
if (v_isSharedCheck_522_ == 0)
{
v___x_480_ = v_snd_471_;
v_isShared_481_ = v_isSharedCheck_522_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v_snd_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_522_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_val_482_; lean_object* v___x_483_; 
v_val_482_ = lean_ctor_get(v_fst_472_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v_fst_472_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v_a_445_);
v___x_483_ = l_Lean_Meta_isExprDefEq(v_a_445_, v_val_482_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; uint8_t v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v___x_485_ = lean_unbox(v_a_484_);
lean_dec(v_a_484_);
if (v___x_485_ == 0)
{
if (v_allowSynthFailures_420_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_422_);
lean_inc(v_tacticName_421_);
v___x_487_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_421_, v_mvarId_422_, v___x_486_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v___x_487_);
if (v_isShared_481_ == 0)
{
v___x_489_ = v___x_480_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_478_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_489_);
v___x_491_ = v___x_475_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_a_433_ = v___x_491_;
goto v___jp_432_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_480_);
lean_dec(v_snd_478_);
lean_dec(v_fst_477_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_mvarId_422_);
lean_dec(v_tacticName_421_);
v_a_494_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_487_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_487_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_503_; 
if (v_isShared_481_ == 0)
{
v___x_503_ = v___x_480_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_snd_478_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_503_);
v___x_505_ = v___x_475_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_a_433_ = v___x_505_;
goto v___jp_432_;
}
}
}
}
else
{
lean_object* v___x_509_; 
if (v_isShared_481_ == 0)
{
v___x_509_ = v___x_480_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_snd_478_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_509_);
v___x_511_ = v___x_475_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
v_a_433_ = v___x_511_;
goto v___jp_432_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_del_object(v___x_480_);
lean_dec(v_snd_478_);
lean_dec(v_fst_477_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_mvarId_422_);
lean_dec(v_tacticName_421_);
v_a_514_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_483_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_483_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
else
{
lean_object* v_fst_525_; lean_object* v_fst_526_; lean_object* v_snd_527_; 
lean_dec(v_fst_472_);
v_fst_525_ = lean_ctor_get(v_snd_470_, 0);
lean_inc(v_fst_525_);
lean_dec(v_snd_470_);
v_fst_526_ = lean_ctor_get(v_snd_471_, 0);
lean_inc(v_fst_526_);
v_snd_527_ = lean_ctor_get(v_snd_471_, 1);
lean_inc(v_snd_527_);
lean_dec(v_snd_471_);
v_fst_438_ = v_fst_525_;
v_fst_439_ = v_fst_526_;
v_snd_440_ = v_snd_527_;
goto v___jp_437_;
}
}
else
{
lean_object* v_a_528_; 
v_a_528_ = lean_ctor_get(v___y_468_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___y_468_);
v_a_464_ = v_a_528_;
goto v___jp_463_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec_ref(v_b_426_);
lean_dec(v_mvarId_422_);
lean_dec(v_tacticName_421_);
v_a_542_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_446_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_446_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
v___jp_432_:
{
size_t v___x_434_; size_t v___x_435_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_425_, v___x_434_);
v_i_425_ = v___x_435_;
v_b_426_ = v_a_433_;
goto _start;
}
v___jp_437_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_fst_439_);
lean_ctor_set(v___x_441_, 1, v_snd_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_fst_438_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v_a_433_ = v___x_442_;
goto v___jp_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_550_, lean_object* v_tacticName_551_, lean_object* v_mvarId_552_, lean_object* v_as_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_allowSynthFailures_boxed_562_; size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_allowSynthFailures_boxed_562_ = lean_unbox(v_allowSynthFailures_550_);
v_sz_boxed_563_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_564_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_562_, v_tacticName_551_, v_mvarId_552_, v_as_553_, v_sz_boxed_563_, v_i_boxed_564_, v_b_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec_ref(v_as_553_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_575_, lean_object* v_mvarId_576_, uint8_t v_allowSynthFailures_577_, lean_object* v_mvars_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_postponed_584_; lean_object* v___x_585_; size_t v_sz_586_; size_t v___x_587_; lean_object* v___x_588_; 
v_postponed_584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_586_ = lean_array_size(v_mvars_578_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_577_, v_tacticName_575_, v_mvarId_576_, v_mvars_578_, v_sz_586_, v___x_587_, v___x_585_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_611_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_611_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_fst_593_; 
v_fst_593_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_fst_593_);
if (lean_obj_tag(v_fst_593_) == 1)
{
lean_object* v_snd_594_; lean_object* v_fst_595_; uint8_t v___x_596_; 
v_snd_594_ = lean_ctor_get(v_a_589_, 1);
lean_inc(v_snd_594_);
lean_dec(v_a_589_);
v_fst_595_ = lean_ctor_get(v_snd_594_, 0);
v___x_596_ = lean_unbox(v_fst_595_);
if (v___x_596_ == 0)
{
lean_dec(v_snd_594_);
if (v_allowSynthFailures_577_ == 0)
{
lean_object* v_val_597_; lean_object* v___x_599_; 
v_val_597_ = lean_ctor_get(v_fst_593_, 0);
lean_inc(v_val_597_);
lean_dec_ref(v_fst_593_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
lean_ctor_set(v___x_591_, 0, v_val_597_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_val_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec_ref(v_fst_593_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_postponed_584_);
v___x_602_ = v___x_591_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_postponed_584_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_snd_604_; lean_object* v___x_606_; 
lean_dec_ref(v_fst_593_);
v_snd_604_ = lean_ctor_get(v_snd_594_, 1);
lean_inc(v_snd_604_);
lean_dec(v_snd_594_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_snd_604_);
v___x_606_ = v___x_591_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_snd_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
lean_object* v___x_609_; 
lean_dec(v_fst_593_);
lean_dec(v_a_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_postponed_584_);
v___x_609_ = v___x_591_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_postponed_584_);
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
v_a_612_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_588_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_588_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_620_, lean_object* v_mvarId_621_, lean_object* v_allowSynthFailures_622_, lean_object* v_mvars_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
uint8_t v_allowSynthFailures_boxed_629_; lean_object* v_res_630_; 
v_allowSynthFailures_boxed_629_ = lean_unbox(v_allowSynthFailures_622_);
v_res_630_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_620_, v_mvarId_621_, v_allowSynthFailures_boxed_629_, v_mvars_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec_ref(v_mvars_623_);
return v_res_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_keys_631_);
v___x_635_ = lean_nat_dec_lt(v_i_632_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec(v_i_632_);
return v___x_635_;
}
else
{
lean_object* v_k_x27_636_; uint8_t v___x_637_; 
v_k_x27_636_ = lean_array_fget_borrowed(v_keys_631_, v_i_632_);
v___x_637_ = l_Lean_instBEqMVarId_beq(v_k_633_, v_k_x27_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_632_, v___x_638_);
lean_dec(v_i_632_);
v_i_632_ = v___x_639_;
goto _start;
}
else
{
lean_dec(v_i_632_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_641_, lean_object* v_i_642_, lean_object* v_k_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_641_, v_i_642_, v_k_643_);
lean_dec(v_k_643_);
lean_dec_ref(v_keys_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; 
v___x_646_ = ((size_t)5ULL);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_shift_left(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_651_ = lean_usize_sub(v___x_650_, v___x_649_);
return v___x_651_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_652_, size_t v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v_es_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v_j_660_; lean_object* v___x_661_; 
v_es_655_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_es_655_);
lean_dec_ref(v_x_652_);
v___x_656_ = lean_box(2);
v___x_657_ = ((size_t)5ULL);
v___x_658_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_659_ = lean_usize_land(v_x_653_, v___x_658_);
v_j_660_ = lean_usize_to_nat(v___x_659_);
v___x_661_ = lean_array_get(v___x_656_, v_es_655_, v_j_660_);
lean_dec(v_j_660_);
lean_dec_ref(v_es_655_);
switch(lean_obj_tag(v___x_661_))
{
case 0:
{
lean_object* v_key_662_; uint8_t v___x_663_; 
v_key_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_key_662_);
lean_dec_ref(v___x_661_);
v___x_663_ = l_Lean_instBEqMVarId_beq(v_x_654_, v_key_662_);
lean_dec(v_key_662_);
return v___x_663_;
}
case 1:
{
lean_object* v_node_664_; size_t v___x_665_; 
v_node_664_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_node_664_);
lean_dec_ref(v___x_661_);
v___x_665_ = lean_usize_shift_right(v_x_653_, v___x_657_);
v_x_652_ = v_node_664_;
v_x_653_ = v___x_665_;
goto _start;
}
default: 
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
}
}
else
{
lean_object* v_ks_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_ks_668_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_ks_668_);
lean_dec_ref(v_x_652_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_668_, v___x_669_, v_x_654_);
lean_dec_ref(v_ks_668_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v_x_2898__boxed_674_; uint8_t v_res_675_; lean_object* v_r_676_; 
v_x_2898__boxed_674_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_res_675_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_671_, v_x_2898__boxed_674_, v_x_673_);
lean_dec(v_x_673_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint64_t v___x_679_; size_t v___x_680_; uint8_t v___x_681_; 
v___x_679_ = l_Lean_instHashableMVarId_hash(v_x_678_);
v___x_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_677_, v___x_680_, v_x_678_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_682_, v_x_683_);
lean_dec(v_x_683_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_mctx_690_; lean_object* v_eAssignment_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_st_ref_get(v___y_687_);
v_mctx_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref(v_mctx_690_);
lean_dec(v___x_689_);
v_eAssignment_691_ = lean_ctor_get(v_mctx_690_, 7);
lean_inc_ref(v_eAssignment_691_);
lean_dec_ref(v_mctx_690_);
v___x_692_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_691_, v_mvarId_686_);
v___x_693_ = lean_box(v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec(v_mvarId_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_699_, lean_object* v_as_700_, size_t v_sz_701_, size_t v_i_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_a_710_; uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_lt(v_i_702_, v_sz_701_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_b_703_);
return v___x_715_;
}
else
{
lean_object* v_snd_716_; lean_object* v_fst_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_767_; 
v_snd_716_ = lean_ctor_get(v_b_703_, 1);
v_fst_717_ = lean_ctor_get(v_b_703_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_b_703_);
if (v_isSharedCheck_767_ == 0)
{
v___x_719_ = v_b_703_;
v_isShared_720_ = v_isSharedCheck_767_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_717_);
lean_dec(v_b_703_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_767_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_array_721_; lean_object* v_start_722_; lean_object* v_stop_723_; uint8_t v___x_724_; 
v_array_721_ = lean_ctor_get(v_snd_716_, 0);
v_start_722_ = lean_ctor_get(v_snd_716_, 1);
v_stop_723_ = lean_ctor_get(v_snd_716_, 2);
v___x_724_ = lean_nat_dec_lt(v_start_722_, v_stop_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_726_; 
if (v_isShared_720_ == 0)
{
v___x_726_ = v___x_719_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_716_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_763_; 
lean_inc(v_stop_723_);
lean_inc(v_start_722_);
lean_inc_ref(v_array_721_);
v_isSharedCheck_763_ = !lean_is_exclusive(v_snd_716_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_764_ = lean_ctor_get(v_snd_716_, 2);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_snd_716_, 1);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_snd_716_, 0);
lean_dec(v_unused_766_);
v___x_730_ = v_snd_716_;
v_isShared_731_ = v_isSharedCheck_763_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_snd_716_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_763_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_732_ = lean_array_fget(v_array_721_, v_start_722_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_add(v_start_722_, v___x_733_);
lean_dec(v_start_722_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_array_721_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_stop_723_);
v___x_736_ = v_reuseFailAlloc_762_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
uint8_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_unbox(v___x_732_);
lean_dec(v___x_732_);
v___x_738_ = l_Lean_BinderInfo_isInstImplicit(v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_740_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_736_);
v___x_740_ = v___x_719_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_736_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v_a_710_ = v___x_740_;
goto v___jp_709_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_742_ = lean_array_uget_borrowed(v_as_700_, v_i_702_);
v___x_743_ = l_Lean_Expr_mvarId_x21(v_a_742_);
v___x_744_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_743_, v___y_705_);
lean_dec(v___x_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
if (v_synthAssignedInstances_699_ == 0)
{
uint8_t v___x_753_; 
v___x_753_ = lean_unbox(v_a_745_);
lean_dec(v_a_745_);
if (v___x_753_ == 0)
{
if (v___x_738_ == 0)
{
goto v___jp_746_;
}
else
{
lean_del_object(v___x_719_);
goto v___jp_750_;
}
}
else
{
goto v___jp_746_;
}
}
else
{
lean_dec(v_a_745_);
lean_del_object(v___x_719_);
goto v___jp_750_;
}
v___jp_746_:
{
lean_object* v___x_748_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_736_);
v___x_748_ = v___x_719_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_736_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v_a_710_ = v___x_748_;
goto v___jp_709_;
}
}
v___jp_750_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_inc(v_a_742_);
v___x_751_ = lean_array_push(v_fst_717_, v_a_742_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_736_);
v_a_710_ = v___x_752_;
goto v___jp_709_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_736_);
lean_del_object(v___x_719_);
lean_dec(v_fst_717_);
v_a_754_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_744_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_744_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
}
}
}
v___jp_709_:
{
size_t v___x_711_; size_t v___x_712_; 
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_702_, v___x_711_);
v_i_702_ = v___x_712_;
v_b_703_ = v_a_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_768_, lean_object* v_as_769_, lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_778_; size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_synthAssignedInstances_boxed_778_ = lean_unbox(v_synthAssignedInstances_768_);
v_sz_boxed_779_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_780_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_778_, v_as_769_, v_sz_boxed_779_, v_i_boxed_780_, v_b_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_as_769_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_782_, lean_object* v_mvarId_783_, uint8_t v_allowSynthFailures_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_array_get_size(v_b_785_);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_nat_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v_mvarId_783_);
lean_inc(v_tacticName_782_);
v___x_794_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_782_, v_mvarId_783_, v_allowSynthFailures_784_, v_b_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_b_785_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v_b_785_ = v_a_795_;
goto _start;
}
else
{
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v_mvarId_783_);
lean_dec(v_tacticName_782_);
return v___x_794_;
}
}
else
{
lean_object* v___x_797_; 
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v_mvarId_783_);
lean_dec(v_tacticName_782_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_b_785_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_798_, lean_object* v_mvarId_799_, lean_object* v_allowSynthFailures_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
uint8_t v_allowSynthFailures_boxed_807_; lean_object* v_res_808_; 
v_allowSynthFailures_boxed_807_ = lean_unbox(v_allowSynthFailures_800_);
v_res_808_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_798_, v_mvarId_799_, v_allowSynthFailures_boxed_807_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_809_, lean_object* v_mvarId_810_, lean_object* v_mvarsNew_811_, lean_object* v_binderInfos_812_, uint8_t v_synthAssignedInstances_813_, uint8_t v_allowSynthFailures_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_todo_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; size_t v_sz_825_; size_t v___x_826_; lean_object* v___x_827_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v_todo_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_822_ = lean_array_get_size(v_binderInfos_812_);
v___x_823_ = l_Array_toSubarray___redArg(v_binderInfos_812_, v___x_820_, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_todo_821_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v_sz_825_ = lean_array_size(v_mvarsNew_811_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_813_, v_mvarsNew_811_, v_sz_825_, v___x_826_, v___x_824_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_fst_829_; lean_object* v___x_830_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
v_fst_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_fst_829_);
lean_dec(v_a_828_);
v___x_830_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_809_, v_mvarId_810_, v_allowSynthFailures_814_, v_fst_829_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_830_, 0);
lean_dec(v_unused_839_);
v___x_832_ = v___x_830_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_dec(v___x_830_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_830_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_830_);
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
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_mvarId_810_);
lean_dec(v_tacticName_809_);
v_a_848_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_827_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_827_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_856_, lean_object* v_mvarId_857_, lean_object* v_mvarsNew_858_, lean_object* v_binderInfos_859_, lean_object* v_synthAssignedInstances_860_, lean_object* v_allowSynthFailures_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_867_; uint8_t v_allowSynthFailures_boxed_868_; lean_object* v_res_869_; 
v_synthAssignedInstances_boxed_867_ = lean_unbox(v_synthAssignedInstances_860_);
v_allowSynthFailures_boxed_868_ = lean_unbox(v_allowSynthFailures_861_);
v_res_869_ = l_Lean_Meta_synthAppInstances(v_tacticName_856_, v_mvarId_857_, v_mvarsNew_858_, v_binderInfos_859_, v_synthAssignedInstances_boxed_867_, v_allowSynthFailures_boxed_868_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_mvarsNew_858_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_870_, v___y_872_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_mvarId_877_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_888_, v_x_889_, v_x_890_);
lean_dec(v_x_890_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, size_t v_x_895_, lean_object* v_x_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_894_, v_x_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_3230__boxed_902_; uint8_t v_res_903_; lean_object* v_r_904_; 
v_x_3230__boxed_902_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_903_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_898_, v_x_899_, v_x_3230__boxed_902_, v_x_901_);
lean_dec(v_x_901_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_905_, lean_object* v_keys_906_, lean_object* v_vals_907_, lean_object* v_heq_908_, lean_object* v_i_909_, lean_object* v_k_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_906_, v_i_909_, v_k_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_912_, lean_object* v_keys_913_, lean_object* v_vals_914_, lean_object* v_heq_915_, lean_object* v_i_916_, lean_object* v_k_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_912_, v_keys_913_, v_vals_914_, v_heq_915_, v_i_916_, v_k_917_);
lean_dec(v_k_917_);
lean_dec_ref(v_vals_914_);
lean_dec_ref(v_keys_913_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_920_, lean_object* v_binderInfos_921_, lean_object* v_a_922_, lean_object* v_n_923_, lean_object* v_i_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_zero_930_; uint8_t v_isZero_931_; 
v_zero_930_ = lean_unsigned_to_nat(0u);
v_isZero_931_ = lean_nat_dec_eq(v_i_924_, v_zero_930_);
if (v_isZero_931_ == 1)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_i_924_);
lean_dec(v_a_922_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v_one_934_; lean_object* v_n_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_a_941_; uint8_t v___x_942_; 
v_one_934_ = lean_unsigned_to_nat(1u);
v_n_935_ = lean_nat_sub(v_i_924_, v_one_934_);
lean_dec(v_i_924_);
v___x_936_ = lean_nat_sub(v_n_923_, v_n_935_);
v___x_937_ = lean_nat_sub(v___x_936_, v_one_934_);
lean_dec(v___x_936_);
v___x_938_ = lean_array_fget_borrowed(v_newMVars_920_, v___x_937_);
v___x_939_ = l_Lean_Expr_mvarId_x21(v___x_938_);
v___x_940_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_939_, v___y_926_);
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref(v___x_940_);
v___x_942_ = lean_unbox(v_a_941_);
lean_dec(v_a_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_943_ = 0;
v___x_944_ = lean_box(v___x_943_);
v___x_945_ = lean_array_get_borrowed(v___x_944_, v_binderInfos_921_, v___x_937_);
lean_dec(v___x_937_);
v___x_946_ = lean_unbox(v___x_945_);
v___x_947_ = l_Lean_BinderInfo_isInstImplicit(v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_inc(v___x_939_);
v___x_948_ = l_Lean_MVarId_getTag(v___x_939_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
lean_inc(v_a_922_);
v___x_950_ = l_Lean_Meta_appendTag(v_a_922_, v_a_949_);
v___x_951_ = l_Lean_MVarId_setTag___redArg(v___x_939_, v___x_950_, v___y_926_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_dec_ref(v___x_951_);
v_i_924_ = v_n_935_;
goto _start;
}
else
{
lean_dec(v_n_935_);
lean_dec(v_a_922_);
return v___x_951_;
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v___x_939_);
lean_dec(v_n_935_);
lean_dec(v_a_922_);
v_a_953_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_948_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_948_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_dec(v___x_939_);
v_i_924_ = v_n_935_;
goto _start;
}
}
else
{
lean_dec(v___x_939_);
lean_dec(v___x_937_);
v_i_924_ = v_n_935_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_963_, lean_object* v_binderInfos_964_, lean_object* v_a_965_, lean_object* v_n_966_, lean_object* v_i_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_963_, v_binderInfos_964_, v_a_965_, v_n_966_, v_i_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_n_966_);
lean_dec_ref(v_binderInfos_964_);
lean_dec_ref(v_newMVars_963_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_974_, lean_object* v_newMVars_975_, lean_object* v_binderInfos_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_MVarId_getTag(v_mvarId_974_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1001_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1001_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1001_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = lean_array_get_size(v_newMVars_975_);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_nat_dec_eq(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Name_isAnonymous(v_a_983_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_del_object(v___x_985_);
v___x_991_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_975_, v_binderInfos_976_, v_a_983_, v___x_987_, v___x_987_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_994_; 
lean_dec(v_a_983_);
v___x_992_ = lean_box(0);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_992_);
v___x_994_ = v___x_985_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_del_object(v___x_985_);
v___x_996_ = l_Lean_instInhabitedExpr;
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_array_get_borrowed(v___x_996_, v_newMVars_975_, v___x_997_);
v___x_999_ = l_Lean_Expr_mvarId_x21(v___x_998_);
v___x_1000_ = l_Lean_MVarId_setTag___redArg(v___x_999_, v_a_983_, v_a_978_);
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_982_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_982_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1010_, lean_object* v_newMVars_1011_, lean_object* v_binderInfos_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_appendParentTag(v_mvarId_1010_, v_newMVars_1011_, v_binderInfos_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_binderInfos_1012_);
lean_dec_ref(v_newMVars_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1019_, lean_object* v_binderInfos_1020_, lean_object* v_a_1021_, lean_object* v_n_1022_, lean_object* v_i_1023_, lean_object* v_a_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1019_, v_binderInfos_1020_, v_a_1021_, v_n_1022_, v_i_1023_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1031_, lean_object* v_binderInfos_1032_, lean_object* v_a_1033_, lean_object* v_n_1034_, lean_object* v_i_1035_, lean_object* v_a_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1031_, v_binderInfos_1032_, v_a_1033_, v_n_1034_, v_i_1035_, v_a_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_n_1034_);
lean_dec_ref(v_binderInfos_1032_);
lean_dec_ref(v_newMVars_1031_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1043_, lean_object* v_mvarId_1044_, lean_object* v_newMVars_1045_, lean_object* v_binderInfos_1046_, uint8_t v_synthAssignedInstances_1047_, uint8_t v_allowSynthFailures_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
lean_inc(v_a_1052_);
lean_inc_ref(v_a_1051_);
lean_inc(v_a_1050_);
lean_inc_ref(v_a_1049_);
lean_inc_ref(v_binderInfos_1046_);
lean_inc(v_mvarId_1044_);
v___x_1054_ = l_Lean_Meta_synthAppInstances(v_tacticName_1043_, v_mvarId_1044_, v_newMVars_1045_, v_binderInfos_1046_, v_synthAssignedInstances_1047_, v_allowSynthFailures_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v___x_1054_);
v___x_1055_ = l_Lean_Meta_appendParentTag(v_mvarId_1044_, v_newMVars_1045_, v_binderInfos_1046_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_binderInfos_1046_);
return v___x_1055_;
}
else
{
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_binderInfos_1046_);
lean_dec(v_mvarId_1044_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1056_, lean_object* v_mvarId_1057_, lean_object* v_newMVars_1058_, lean_object* v_binderInfos_1059_, lean_object* v_synthAssignedInstances_1060_, lean_object* v_allowSynthFailures_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1067_; uint8_t v_allowSynthFailures_boxed_1068_; lean_object* v_res_1069_; 
v_synthAssignedInstances_boxed_1067_ = lean_unbox(v_synthAssignedInstances_1060_);
v_allowSynthFailures_boxed_1068_ = lean_unbox(v_allowSynthFailures_1061_);
v_res_1069_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1056_, v_mvarId_1057_, v_newMVars_1058_, v_binderInfos_1059_, v_synthAssignedInstances_boxed_1067_, v_allowSynthFailures_boxed_1068_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec_ref(v_newMVars_1058_);
return v_res_1069_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1070_, lean_object* v_mvarId_1071_){
_start:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = l_Lean_Expr_mvarId_x21(v_mvar_1070_);
v___x_1073_ = l_Lean_instBEqMVarId_beq(v_mvarId_1071_, v___x_1072_);
lean_dec(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1074_, lean_object* v_mvarId_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1074_, v_mvarId_1075_);
lean_dec(v_mvarId_1075_);
lean_dec_ref(v_mvar_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1078_, lean_object* v_as_1079_, size_t v_i_1080_, size_t v_stop_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_eq(v_i_1080_, v_stop_1081_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; uint8_t v_a_1090_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1088_ = 1;
v___x_1096_ = lean_array_uget_borrowed(v_as_1079_, v_i_1080_);
v___x_1097_ = lean_expr_eqv(v_mvar_1078_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___x_1096_);
v___x_1098_ = lean_infer_type(v___x_1096_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1110_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1110_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1110_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc_ref(v_mvar_1078_);
v___f_1103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1103_, 0, v_mvar_1078_);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_FindMVar_main(v___f_1103_, v_a_1099_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_del_object(v___x_1101_);
v_a_1090_ = v___x_1097_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec_ref(v___x_1105_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_mvar_1078_);
v___x_1106_ = lean_box(v___x_1088_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1106_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_mvar_1078_);
v_a_1111_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1098_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1098_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
v_a_1090_ = v___x_1087_;
goto v___jp_1089_;
}
v___jp_1089_:
{
if (v_a_1090_ == 0)
{
size_t v___x_1091_; size_t v___x_1092_; 
v___x_1091_ = ((size_t)1ULL);
v___x_1092_ = lean_usize_add(v_i_1080_, v___x_1091_);
v_i_1080_ = v___x_1092_;
goto _start;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_mvar_1078_);
v___x_1094_ = lean_box(v___x_1088_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
}
else
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_mvar_1078_);
v___x_1119_ = 0;
v___x_1120_ = lean_box(v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1122_, lean_object* v_as_1123_, lean_object* v_i_1124_, lean_object* v_stop_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1125_);
lean_dec(v_stop_1125_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1122_, v_as_1123_, v_i_boxed_1131_, v_stop_boxed_1132_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v_as_1123_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1134_, lean_object* v_otherMVars_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_array_get_size(v_otherMVars_1135_);
v___x_1143_ = lean_nat_dec_lt(v___x_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_mvar_1134_);
v___x_1144_ = lean_box(v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
else
{
if (v___x_1143_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_mvar_1134_);
v___x_1146_ = lean_box(v___x_1143_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
else
{
size_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = lean_usize_of_nat(v___x_1142_);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1134_, v_otherMVars_1135_, v___x_1148_, v___x_1149_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1151_, lean_object* v_otherMVars_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1151_, v_otherMVars_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec_ref(v_otherMVars_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1159_, lean_object* v_as_1160_, size_t v_i_1161_, size_t v_stop_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_eq(v_i_1161_, v_stop_1162_);
if (v___x_1169_ == 0)
{
lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1201_; 
v_fst_1170_ = lean_ctor_get(v_b_1163_, 0);
v_snd_1171_ = lean_ctor_get(v_b_1163_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_b_1163_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1173_ = v_b_1163_;
v_isShared_1174_ = v_isSharedCheck_1201_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_b_1163_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1201_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v_currMVarId_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_array_uget_borrowed(v_as_1160_, v_i_1161_);
v_currMVarId_1176_ = l_Lean_Expr_mvarId_x21(v___x_1175_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___x_1175_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1175_, v_mvars_1159_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_a_1180_; uint8_t v___x_1184_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v___x_1184_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_array_push(v_fst_1170_, v_currMVarId_1176_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1185_);
v___x_1187_ = v___x_1173_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_snd_1171_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
v_a_1180_ = v___x_1187_;
goto v___jp_1179_;
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_array_push(v_snd_1171_, v_currMVarId_1176_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1189_);
v___x_1191_ = v___x_1173_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_a_1180_ = v___x_1191_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
size_t v___x_1181_; size_t v___x_1182_; 
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1161_, v___x_1181_);
v_i_1161_ = v___x_1182_;
v_b_1163_ = v_a_1180_;
goto _start;
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_currMVarId_1176_);
lean_del_object(v___x_1173_);
lean_dec(v_snd_1171_);
lean_dec(v_fst_1170_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
v_a_1193_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1177_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1177_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_b_1163_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1203_, lean_object* v_as_1204_, lean_object* v_i_1205_, lean_object* v_stop_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
size_t v_i_boxed_1213_; size_t v_stop_boxed_1214_; lean_object* v_res_1215_; 
v_i_boxed_1213_ = lean_unbox_usize(v_i_1205_);
lean_dec(v_i_1205_);
v_stop_boxed_1214_ = lean_unbox_usize(v_stop_1206_);
lean_dec(v_stop_1206_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1203_, v_as_1204_, v_i_boxed_1213_, v_stop_boxed_1214_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec_ref(v_as_1204_);
lean_dec_ref(v_mvars_1203_);
return v_res_1215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1);
v___x_1228_ = lean_array_get_size(v_mvars_1220_);
v___x_1229_ = lean_nat_dec_lt(v___x_1226_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1227_);
return v___x_1230_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_nat_dec_le(v___x_1228_, v___x_1228_);
if (v___x_1231_ == 0)
{
if (v___x_1229_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1227_);
return v___x_1232_;
}
else
{
size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = lean_usize_of_nat(v___x_1228_);
v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1220_, v_mvars_1220_, v___x_1233_, v___x_1234_, v___x_1227_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
return v___x_1235_;
}
}
else
{
size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = ((size_t)0ULL);
v___x_1237_ = lean_usize_of_nat(v___x_1228_);
v___x_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1220_, v_mvars_1220_, v___x_1236_, v___x_1237_, v___x_1227_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec_ref(v_mvars_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = l_List_reverse___redArg(v_a_1247_);
return v___x_1248_;
}
else
{
lean_object* v_head_1249_; lean_object* v_tail_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v_head_1249_ = lean_ctor_get(v_a_1246_, 0);
v_tail_1250_ = lean_ctor_get(v_a_1246_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1252_ = v_a_1246_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_tail_1250_);
lean_inc(v_head_1249_);
lean_dec(v_a_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Lean_Expr_mvarId_x21(v_head_1249_);
lean_dec(v_head_1249_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_a_1247_);
lean_ctor_set(v___x_1252_, 0, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_a_1247_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_a_1246_ = v_tail_1250_;
v_a_1247_ = v___x_1256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1260_, uint8_t v_x_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
switch(v_x_1261_)
{
case 0:
{
lean_object* v___x_1267_; 
v___x_1267_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1260_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec_ref(v_mvars_1260_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1280_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1280_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1280_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_fst_1272_; lean_object* v_snd_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v_fst_1272_ = lean_ctor_get(v_a_1268_, 0);
lean_inc(v_fst_1272_);
v_snd_1273_ = lean_ctor_get(v_a_1268_, 1);
lean_inc(v_snd_1273_);
lean_dec(v_a_1268_);
v___x_1274_ = lean_array_to_list(v_fst_1272_);
v___x_1275_ = lean_array_to_list(v_snd_1273_);
v___x_1276_ = l_List_appendTR___redArg(v___x_1274_, v___x_1275_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1276_);
v___x_1278_ = v___x_1270_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1267_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1267_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
case 1:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1260_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec_ref(v_mvars_1260_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1299_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1299_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1299_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v_fst_1294_ = lean_ctor_get(v_a_1290_, 0);
lean_inc(v_fst_1294_);
lean_dec(v_a_1290_);
v___x_1295_ = lean_array_to_list(v_fst_1294_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1295_);
v___x_1297_ = v___x_1292_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1289_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1289_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
default: 
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
v___x_1308_ = lean_array_to_list(v_mvars_1260_);
v___x_1309_ = lean_box(0);
v___x_1310_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1308_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1312_, lean_object* v_x_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
uint8_t v_x_917__boxed_1319_; lean_object* v_res_1320_; 
v_x_917__boxed_1319_ = lean_unbox(v_x_1313_);
v_res_1320_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1312_, v_x_917__boxed_1319_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1321_, lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
if (v_approx_1321_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1322_, v_b_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; uint8_t v_constApprox_1331_; uint8_t v_isDefEqStuckEx_1332_; uint8_t v_unificationHints_1333_; uint8_t v_proofIrrelevance_1334_; uint8_t v_assignSyntheticOpaque_1335_; uint8_t v_offsetCnstrs_1336_; uint8_t v_transparency_1337_; uint8_t v_etaStruct_1338_; uint8_t v_univApprox_1339_; uint8_t v_iota_1340_; uint8_t v_beta_1341_; uint8_t v_proj_1342_; uint8_t v_zeta_1343_; uint8_t v_zetaDelta_1344_; uint8_t v_zetaUnused_1345_; uint8_t v_zetaHave_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1374_; 
v___x_1330_ = l_Lean_Meta_Context_config(v_a_1324_);
v_constApprox_1331_ = lean_ctor_get_uint8(v___x_1330_, 3);
v_isDefEqStuckEx_1332_ = lean_ctor_get_uint8(v___x_1330_, 4);
v_unificationHints_1333_ = lean_ctor_get_uint8(v___x_1330_, 5);
v_proofIrrelevance_1334_ = lean_ctor_get_uint8(v___x_1330_, 6);
v_assignSyntheticOpaque_1335_ = lean_ctor_get_uint8(v___x_1330_, 7);
v_offsetCnstrs_1336_ = lean_ctor_get_uint8(v___x_1330_, 8);
v_transparency_1337_ = lean_ctor_get_uint8(v___x_1330_, 9);
v_etaStruct_1338_ = lean_ctor_get_uint8(v___x_1330_, 10);
v_univApprox_1339_ = lean_ctor_get_uint8(v___x_1330_, 11);
v_iota_1340_ = lean_ctor_get_uint8(v___x_1330_, 12);
v_beta_1341_ = lean_ctor_get_uint8(v___x_1330_, 13);
v_proj_1342_ = lean_ctor_get_uint8(v___x_1330_, 14);
v_zeta_1343_ = lean_ctor_get_uint8(v___x_1330_, 15);
v_zetaDelta_1344_ = lean_ctor_get_uint8(v___x_1330_, 16);
v_zetaUnused_1345_ = lean_ctor_get_uint8(v___x_1330_, 17);
v_zetaHave_1346_ = lean_ctor_get_uint8(v___x_1330_, 18);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1348_ = v___x_1330_;
v_isShared_1349_ = v_isSharedCheck_1374_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v___x_1330_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1374_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 3, v_constApprox_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 4, v_isDefEqStuckEx_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 5, v_unificationHints_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 6, v_proofIrrelevance_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 7, v_assignSyntheticOpaque_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 8, v_offsetCnstrs_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 9, v_transparency_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 10, v_etaStruct_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 11, v_univApprox_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 12, v_iota_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 13, v_beta_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 14, v_proj_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 15, v_zeta_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 16, v_zetaDelta_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 17, v_zetaUnused_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, 18, v_zetaHave_1346_);
v___x_1351_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
uint8_t v_trackZetaDelta_1352_; lean_object* v_zetaDeltaSet_1353_; lean_object* v_lctx_1354_; lean_object* v_localInstances_1355_; lean_object* v_defEqCtx_x3f_1356_; lean_object* v_synthPendingDepth_1357_; lean_object* v_canUnfold_x3f_1358_; uint8_t v_univApprox_1359_; uint8_t v_inTypeClassResolution_1360_; uint8_t v_cacheInferType_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1371_; 
lean_ctor_set_uint8(v___x_1351_, 0, v_approx_1321_);
lean_ctor_set_uint8(v___x_1351_, 1, v_approx_1321_);
lean_ctor_set_uint8(v___x_1351_, 2, v_approx_1321_);
v_trackZetaDelta_1352_ = lean_ctor_get_uint8(v_a_1324_, sizeof(void*)*7);
v_zetaDeltaSet_1353_ = lean_ctor_get(v_a_1324_, 1);
v_lctx_1354_ = lean_ctor_get(v_a_1324_, 2);
v_localInstances_1355_ = lean_ctor_get(v_a_1324_, 3);
v_defEqCtx_x3f_1356_ = lean_ctor_get(v_a_1324_, 4);
v_synthPendingDepth_1357_ = lean_ctor_get(v_a_1324_, 5);
v_canUnfold_x3f_1358_ = lean_ctor_get(v_a_1324_, 6);
v_univApprox_1359_ = lean_ctor_get_uint8(v_a_1324_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1360_ = lean_ctor_get_uint8(v_a_1324_, sizeof(void*)*7 + 2);
v_cacheInferType_1361_ = lean_ctor_get_uint8(v_a_1324_, sizeof(void*)*7 + 3);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1324_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_a_1324_, 0);
lean_dec(v_unused_1372_);
v___x_1363_ = v_a_1324_;
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_canUnfold_x3f_1358_);
lean_inc(v_synthPendingDepth_1357_);
lean_inc(v_defEqCtx_x3f_1356_);
lean_inc(v_localInstances_1355_);
lean_inc(v_lctx_1354_);
lean_inc(v_zetaDeltaSet_1353_);
lean_dec(v_a_1324_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint64_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1351_);
v___x_1366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1366_, 0, v___x_1351_);
lean_ctor_set_uint64(v___x_1366_, sizeof(void*)*1, v___x_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_zetaDeltaSet_1353_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_lctx_1354_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_localInstances_1355_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_defEqCtx_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1370_, 5, v_synthPendingDepth_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 6, v_canUnfold_x3f_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*7, v_trackZetaDelta_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*7 + 1, v_univApprox_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*7 + 3, v_cacheInferType_1361_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1322_, v_b_1323_, v___x_1368_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1375_, lean_object* v_a_1376_, lean_object* v_b_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
uint8_t v_approx_boxed_1383_; lean_object* v_res_1384_; 
v_approx_boxed_1383_ = lean_unbox(v_approx_1375_);
v_res_1384_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1383_, v_a_1376_, v_b_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1385_, lean_object* v_cfg_1386_, lean_object* v_term_x3f_1387_, lean_object* v_targetType_1388_, lean_object* v_eType_1389_, lean_object* v_rangeNumArgs_1390_, lean_object* v_i_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_lower_1397_; lean_object* v_upper_1398_; uint8_t v___x_1399_; 
v_lower_1397_ = lean_ctor_get(v_rangeNumArgs_1390_, 0);
v_upper_1398_ = lean_ctor_get(v_rangeNumArgs_1390_, 1);
v___x_1399_ = lean_nat_dec_lt(v_i_1391_, v_upper_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
lean_dec(v_i_1391_);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_eq(v_lower_1397_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; 
lean_inc(v_lower_1397_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_lower_1397_);
v___x_1403_ = 0;
lean_inc(v_a_1395_);
lean_inc_ref(v_a_1394_);
lean_inc(v_a_1393_);
lean_inc_ref(v_a_1392_);
lean_inc_ref(v_eType_1389_);
v___x_1404_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1389_, v___x_1402_, v___x_1403_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_snd_1406_; lean_object* v_snd_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v_snd_1406_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1406_);
lean_dec(v_a_1405_);
v_snd_1407_ = lean_ctor_get(v_snd_1406_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_snd_1406_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_snd_1407_);
v___x_1409_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1385_, v_eType_1389_, v___x_1408_, v_targetType_1388_, v_term_x3f_1387_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v___x_1409_;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
v_a_1410_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1404_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1404_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_box(0);
v___x_1419_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1385_, v_eType_1389_, v___x_1418_, v_targetType_1388_, v_term_x3f_1387_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v___x_1419_;
}
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_saveState___redArg(v_a_1393_, v_a_1395_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v___x_1420_);
lean_inc(v_i_1391_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_i_1391_);
v___x_1423_ = 0;
lean_inc(v_a_1395_);
lean_inc_ref(v_a_1394_);
lean_inc(v_a_1393_);
lean_inc_ref(v_a_1392_);
lean_inc_ref(v_eType_1389_);
v___x_1424_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1389_, v___x_1422_, v___x_1423_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v_snd_1426_; lean_object* v_fst_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1467_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v_snd_1426_ = lean_ctor_get(v_a_1425_, 1);
lean_inc(v_snd_1426_);
v_fst_1427_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_fst_1427_);
lean_dec(v_a_1425_);
v_fst_1428_ = lean_ctor_get(v_snd_1426_, 0);
v_snd_1429_ = lean_ctor_get(v_snd_1426_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_snd_1426_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1431_ = v_snd_1426_;
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_inc(v_fst_1428_);
lean_dec(v_snd_1426_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
uint8_t v_approx_1433_; lean_object* v___x_1434_; 
v_approx_1433_ = lean_ctor_get_uint8(v_cfg_1386_, 3);
lean_inc(v_a_1395_);
lean_inc_ref(v_a_1394_);
lean_inc(v_a_1393_);
lean_inc_ref(v_a_1392_);
lean_inc_ref(v_targetType_1388_);
v___x_1434_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1433_, v_snd_1429_, v_targetType_1388_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1458_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_unbox(v_a_1435_);
lean_dec(v_a_1435_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_del_object(v___x_1437_);
lean_del_object(v___x_1431_);
lean_dec(v_fst_1428_);
lean_dec(v_fst_1427_);
v___x_1440_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1421_, v_a_1393_, v_a_1395_);
lean_dec(v_a_1421_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v___x_1440_);
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_add(v_i_1391_, v___x_1441_);
lean_dec(v_i_1391_);
v_i_1391_ = v___x_1442_;
goto _start;
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_i_1391_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
v_a_1444_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1440_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1440_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v___x_1453_; 
lean_dec(v_a_1421_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_i_1391_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_fst_1428_);
lean_ctor_set(v___x_1431_, 0, v_fst_1427_);
v___x_1453_ = v___x_1431_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_fst_1427_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_fst_1428_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1453_);
v___x_1455_ = v___x_1437_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_del_object(v___x_1431_);
lean_dec(v_fst_1428_);
lean_dec(v_fst_1427_);
lean_dec(v_a_1421_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_i_1391_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
v_a_1459_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1434_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1434_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1421_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_i_1391_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
v_a_1468_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1424_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1424_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_i_1391_);
lean_dec_ref(v_eType_1389_);
lean_dec_ref(v_targetType_1388_);
lean_dec(v_term_x3f_1387_);
lean_dec(v_mvarId_1385_);
v_a_1476_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1420_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1420_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1484_, lean_object* v_cfg_1485_, lean_object* v_term_x3f_1486_, lean_object* v_targetType_1487_, lean_object* v_eType_1488_, lean_object* v_rangeNumArgs_1489_, lean_object* v_i_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1484_, v_cfg_1485_, v_term_x3f_1486_, v_targetType_1487_, v_eType_1488_, v_rangeNumArgs_1489_, v_i_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec_ref(v_rangeNumArgs_1489_);
lean_dec_ref(v_cfg_1485_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1497_, lean_object* v_h__1_1498_){
_start:
{
lean_object* v_snd_1499_; lean_object* v_fst_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; 
v_snd_1499_ = lean_ctor_get(v_x_1497_, 1);
lean_inc(v_snd_1499_);
v_fst_1500_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_fst_1500_);
lean_dec_ref(v_x_1497_);
v_fst_1501_ = lean_ctor_get(v_snd_1499_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v_snd_1499_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_snd_1499_);
v___x_1503_ = lean_apply_3(v_h__1_1498_, v_fst_1500_, v_fst_1501_, v_snd_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1504_, lean_object* v_x_1505_, lean_object* v_h__1_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(v_x_1505_, v_h__1_1506_);
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
lean_dec_ref(v___x_1617_);
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
lean_dec_ref(v___x_1617_);
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
lean_dec_ref(v_as_1640_);
v___x_1650_ = l_Lean_MVarId_headBetaType(v_head_1648_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_dec_ref(v___x_1650_);
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
lean_object* v_es_1700_; size_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v_j_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_es_1700_ = lean_ctor_get(v_x_1695_, 0);
v___x_1701_ = ((size_t)5ULL);
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1704_ = lean_usize_land(v_x_1696_, v___x_1703_);
v_j_1705_ = lean_usize_to_nat(v___x_1704_);
v___x_1706_ = lean_array_get_size(v_es_1700_);
v___x_1707_ = lean_nat_dec_lt(v_j_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_dec(v_j_1705_);
lean_dec(v_x_1699_);
lean_dec(v_x_1698_);
return v_x_1695_;
}
else
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1744_; 
lean_inc_ref(v_es_1700_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_x_1695_, 0);
lean_dec(v_unused_1745_);
v___x_1709_ = v_x_1695_;
v_isShared_1710_ = v_isSharedCheck_1744_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v_x_1695_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1744_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_v_1711_; lean_object* v___x_1712_; lean_object* v_xs_x27_1713_; lean_object* v___y_1715_; 
v_v_1711_ = lean_array_fget(v_es_1700_, v_j_1705_);
v___x_1712_ = lean_box(0);
v_xs_x27_1713_ = lean_array_fset(v_es_1700_, v_j_1705_, v___x_1712_);
switch(lean_obj_tag(v_v_1711_))
{
case 0:
{
lean_object* v_key_1720_; lean_object* v_val_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1731_; 
v_key_1720_ = lean_ctor_get(v_v_1711_, 0);
v_val_1721_ = lean_ctor_get(v_v_1711_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1723_ = v_v_1711_;
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_val_1721_);
lean_inc(v_key_1720_);
lean_dec(v_v_1711_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
uint8_t v___x_1725_; 
v___x_1725_ = l_Lean_instBEqMVarId_beq(v_x_1698_, v_key_1720_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1723_);
v___x_1726_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1720_, v_val_1721_, v_x_1698_, v_x_1699_);
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___y_1715_ = v___x_1727_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1729_; 
lean_dec(v_val_1721_);
lean_dec(v_key_1720_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v_x_1699_);
lean_ctor_set(v___x_1723_, 0, v_x_1698_);
v___x_1729_ = v___x_1723_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_x_1698_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_x_1699_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1715_ = v___x_1729_;
goto v___jp_1714_;
}
}
}
}
case 1:
{
lean_object* v_node_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1742_; 
v_node_1732_ = lean_ctor_get(v_v_1711_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1734_ = v_v_1711_;
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_node_1732_);
lean_dec(v_v_1711_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1736_ = lean_usize_shift_right(v_x_1696_, v___x_1701_);
v___x_1737_ = lean_usize_add(v_x_1697_, v___x_1702_);
v___x_1738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1732_, v___x_1736_, v___x_1737_, v_x_1698_, v_x_1699_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1740_ = v___x_1734_;
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
v___y_1715_ = v___x_1740_;
goto v___jp_1714_;
}
}
}
default: 
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_x_1698_);
lean_ctor_set(v___x_1743_, 1, v_x_1699_);
v___y_1715_ = v___x_1743_;
goto v___jp_1714_;
}
}
v___jp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_array_fset(v_xs_x27_1713_, v_j_1705_, v___y_1715_);
lean_dec(v_j_1705_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1716_);
v___x_1718_ = v___x_1709_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
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
size_t v_x_7337__boxed_1800_; size_t v_x_7338__boxed_1801_; lean_object* v_res_1802_; 
v_x_7337__boxed_1800_ = lean_unbox_usize(v_x_1796_);
lean_dec(v_x_1796_);
v_x_7338__boxed_1801_ = lean_unbox_usize(v_x_1797_);
lean_dec(v_x_1797_);
v_res_1802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1795_, v_x_7337__boxed_1800_, v_x_7338__boxed_1801_, v_x_1798_, v_x_1799_);
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
lean_object* v___x_1814_; lean_object* v_mctx_1815_; lean_object* v_cache_1816_; lean_object* v_zetaDeltaFVarIds_1817_; lean_object* v_postponed_1818_; lean_object* v_diag_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1846_; 
v___x_1814_ = lean_st_ref_take(v___y_1812_);
v_mctx_1815_ = lean_ctor_get(v___x_1814_, 0);
v_cache_1816_ = lean_ctor_get(v___x_1814_, 1);
v_zetaDeltaFVarIds_1817_ = lean_ctor_get(v___x_1814_, 2);
v_postponed_1818_ = lean_ctor_get(v___x_1814_, 3);
v_diag_1819_ = lean_ctor_get(v___x_1814_, 4);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1821_ = v___x_1814_;
v_isShared_1822_ = v_isSharedCheck_1846_;
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
v_isShared_1822_ = v_isSharedCheck_1846_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_depth_1823_; lean_object* v_levelAssignDepth_1824_; lean_object* v_mvarCounter_1825_; lean_object* v_lDepth_1826_; lean_object* v_decls_1827_; lean_object* v_userNames_1828_; lean_object* v_lAssignment_1829_; lean_object* v_eAssignment_1830_; lean_object* v_dAssignment_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1845_; 
v_depth_1823_ = lean_ctor_get(v_mctx_1815_, 0);
v_levelAssignDepth_1824_ = lean_ctor_get(v_mctx_1815_, 1);
v_mvarCounter_1825_ = lean_ctor_get(v_mctx_1815_, 2);
v_lDepth_1826_ = lean_ctor_get(v_mctx_1815_, 3);
v_decls_1827_ = lean_ctor_get(v_mctx_1815_, 4);
v_userNames_1828_ = lean_ctor_get(v_mctx_1815_, 5);
v_lAssignment_1829_ = lean_ctor_get(v_mctx_1815_, 6);
v_eAssignment_1830_ = lean_ctor_get(v_mctx_1815_, 7);
v_dAssignment_1831_ = lean_ctor_get(v_mctx_1815_, 8);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_mctx_1815_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1833_ = v_mctx_1815_;
v_isShared_1834_ = v_isSharedCheck_1845_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_dAssignment_1831_);
lean_inc(v_eAssignment_1830_);
lean_inc(v_lAssignment_1829_);
lean_inc(v_userNames_1828_);
lean_inc(v_decls_1827_);
lean_inc(v_lDepth_1826_);
lean_inc(v_mvarCounter_1825_);
lean_inc(v_levelAssignDepth_1824_);
lean_inc(v_depth_1823_);
lean_dec(v_mctx_1815_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1845_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1830_, v_mvarId_1810_, v_val_1811_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 7, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_depth_1823_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_levelAssignDepth_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_mvarCounter_1825_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_lDepth_1826_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_decls_1827_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_userNames_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_lAssignment_1829_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_dAssignment_1831_);
v___x_1837_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1837_);
v___x_1839_ = v___x_1821_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_zetaDeltaFVarIds_1817_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_postponed_1818_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_diag_1819_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_st_ref_set(v___y_1812_, v___x_1839_);
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1847_, lean_object* v_val_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1847_, v_val_1848_, v___y_1849_);
lean_dec(v___y_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1852_, lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = 0;
return v___x_1854_;
}
else
{
lean_object* v_head_1855_; lean_object* v_tail_1856_; uint8_t v___x_1857_; 
v_head_1855_ = lean_ctor_get(v_x_1853_, 0);
v_tail_1856_ = lean_ctor_get(v_x_1853_, 1);
v___x_1857_ = l_Lean_instBEqMVarId_beq(v_a_1852_, v_head_1855_);
if (v___x_1857_ == 0)
{
v_x_1853_ = v_tail_1856_;
goto _start;
}
else
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1859_, v_x_1860_);
lean_dec(v_x_1860_);
lean_dec(v_a_1859_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1863_, lean_object* v_as_1864_, size_t v_i_1865_, size_t v_stop_1866_, lean_object* v_b_1867_){
_start:
{
lean_object* v___y_1869_; uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_eq(v_i_1865_, v_stop_1866_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1874_ = lean_array_uget_borrowed(v_as_1864_, v_i_1865_);
v___x_1875_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1874_, v_a_1863_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
lean_inc(v___x_1874_);
v___x_1876_ = lean_array_push(v_b_1867_, v___x_1874_);
v___y_1869_ = v___x_1876_;
goto v___jp_1868_;
}
else
{
v___y_1869_ = v_b_1867_;
goto v___jp_1868_;
}
}
else
{
return v_b_1867_;
}
v___jp_1868_:
{
size_t v___x_1870_; size_t v___x_1871_; 
v___x_1870_ = ((size_t)1ULL);
v___x_1871_ = lean_usize_add(v_i_1865_, v___x_1870_);
v_i_1865_ = v___x_1871_;
v_b_1867_ = v___y_1869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1877_, lean_object* v_as_1878_, lean_object* v_i_1879_, lean_object* v_stop_1880_, lean_object* v_b_1881_){
_start:
{
size_t v_i_boxed_1882_; size_t v_stop_boxed_1883_; lean_object* v_res_1884_; 
v_i_boxed_1882_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_stop_boxed_1883_ = lean_unbox_usize(v_stop_1880_);
lean_dec(v_stop_1880_);
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1877_, v_as_1878_, v_i_boxed_1882_, v_stop_boxed_1883_, v_b_1881_);
lean_dec_ref(v_as_1878_);
lean_dec(v_a_1877_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1885_, lean_object* v___x_1886_, lean_object* v_e_1887_, lean_object* v_cfg_1888_, lean_object* v_term_x3f_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v_a_1929_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___x_1970_; 
lean_inc(v___x_1886_);
lean_inc(v_mvarId_1885_);
v___x_1970_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1885_, v___x_1886_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref(v___x_1970_);
lean_inc(v_mvarId_1885_);
v___x_1971_ = l_Lean_MVarId_getType(v_mvarId_1885_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc_ref(v_e_1887_);
v___x_1973_ = lean_infer_type(v_e_1887_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_rangeNumArgs_1976_; lean_object* v_lower_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_2021_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v_a_1974_);
v___x_2021_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1974_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v_snd_2023_; uint8_t v___x_2024_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
v_snd_2023_ = lean_ctor_get(v_a_2022_, 1);
v___x_2024_ = lean_unbox(v_snd_2023_);
if (v___x_2024_ == 0)
{
lean_object* v_fst_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2045_; 
v_fst_2025_ = lean_ctor_get(v_a_2022_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_a_2022_, 1);
lean_dec(v_unused_2046_);
v___x_2027_ = v_a_2022_;
v_isShared_2028_ = v_isSharedCheck_2045_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_fst_2025_);
lean_dec(v_a_2022_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2045_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; 
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v_a_1972_);
v___x_2029_ = l_Lean_Meta_getExpectedNumArgs(v_a_1972_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = lean_nat_sub(v_fst_2025_, v_a_2030_);
lean_dec(v_a_2030_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_fst_2025_, v___x_2032_);
lean_dec(v_fst_2025_);
lean_inc(v___x_2031_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2033_);
lean_ctor_set(v___x_2027_, 0, v___x_2031_);
v___x_2035_ = v___x_2027_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
v_rangeNumArgs_1976_ = v___x_2035_;
v_lower_1977_ = v___x_2031_;
v___y_1978_ = v___y_1890_;
v___y_1979_ = v___y_1891_;
v___y_1980_ = v___y_1892_;
v___y_1981_ = v___y_1893_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_2027_);
lean_dec(v_fst_2025_);
lean_dec(v_a_1974_);
lean_dec(v_a_1972_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_term_x3f_1889_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2037_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2029_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2029_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v_fst_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2056_; 
v_fst_2047_ = lean_ctor_get(v_a_2022_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_a_2022_, 1);
lean_dec(v_unused_2057_);
v___x_2049_ = v_a_2022_;
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_fst_2047_);
lean_dec(v_a_2022_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_nat_add(v_fst_2047_, v___x_2051_);
lean_inc(v_fst_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_fst_2047_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v_rangeNumArgs_1976_ = v___x_2054_;
v_lower_1977_ = v_fst_2047_;
v___y_1978_ = v___y_1890_;
v___y_1979_ = v___y_1891_;
v___y_1980_ = v___y_1892_;
v___y_1981_ = v___y_1893_;
goto v___jp_1975_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_1974_);
lean_dec(v_a_1972_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_term_x3f_1889_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2058_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2021_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2021_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
v___jp_1975_:
{
lean_object* v___x_1982_; 
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v_mvarId_1885_);
v___x_1982_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1885_, v_cfg_1888_, v_term_x3f_1889_, v_a_1972_, v_a_1974_, v_rangeNumArgs_1976_, v_lower_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec_ref(v_rangeNumArgs_1976_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; uint8_t v_newGoals_1986_; uint8_t v_synthAssignedInstances_1987_; uint8_t v_allowSynthFailures_1988_; lean_object* v___x_1989_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v_fst_1984_ = lean_ctor_get(v_a_1983_, 0);
lean_inc(v_fst_1984_);
v_snd_1985_ = lean_ctor_get(v_a_1983_, 1);
lean_inc(v_snd_1985_);
lean_dec(v_a_1983_);
v_newGoals_1986_ = lean_ctor_get_uint8(v_cfg_1888_, 0);
v_synthAssignedInstances_1987_ = lean_ctor_get_uint8(v_cfg_1888_, 1);
v_allowSynthFailures_1988_ = lean_ctor_get_uint8(v_cfg_1888_, 2);
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v_mvarId_1885_);
v___x_1989_ = l_Lean_Meta_postprocessAppMVars(v___x_1886_, v_mvarId_1885_, v_fst_1984_, v_snd_1985_, v_synthAssignedInstances_1987_, v_allowSynthFailures_1988_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1990_; lean_object* v_a_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
lean_dec_ref(v___x_1989_);
v___x_1990_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1887_, v___y_1979_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1990_);
lean_inc(v_a_1991_);
v___x_1992_ = l_Lean_mkAppN(v_a_1991_, v_fst_1984_);
v___x_1993_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1885_, v___x_1992_, v___y_1979_);
lean_dec_ref(v___x_1993_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_array_get_size(v_fst_1984_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1997_ = lean_nat_dec_lt(v___x_1994_, v___x_1995_);
if (v___x_1997_ == 0)
{
lean_dec(v_fst_1984_);
v___y_1922_ = v___x_1994_;
v___y_1923_ = v___y_1978_;
v___y_1924_ = v___y_1979_;
v___y_1925_ = v_newGoals_1986_;
v___y_1926_ = v_a_1991_;
v___y_1927_ = v___y_1981_;
v___y_1928_ = v___y_1980_;
v_a_1929_ = v___x_1996_;
goto v___jp_1921_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_nat_dec_le(v___x_1995_, v___x_1995_);
if (v___x_1998_ == 0)
{
if (v___x_1997_ == 0)
{
lean_dec(v_fst_1984_);
v___y_1922_ = v___x_1994_;
v___y_1923_ = v___y_1978_;
v___y_1924_ = v___y_1979_;
v___y_1925_ = v_newGoals_1986_;
v___y_1926_ = v_a_1991_;
v___y_1927_ = v___y_1981_;
v___y_1928_ = v___y_1980_;
v_a_1929_ = v___x_1996_;
goto v___jp_1921_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = lean_usize_of_nat(v___x_1995_);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1984_, v___x_1999_, v___x_2000_, v___x_1996_, v___y_1979_);
lean_dec(v_fst_1984_);
v___y_1953_ = v___x_1994_;
v___y_1954_ = v___y_1978_;
v___y_1955_ = v___y_1979_;
v___y_1956_ = v_a_1991_;
v___y_1957_ = v_newGoals_1986_;
v___y_1958_ = v___y_1981_;
v___y_1959_ = v___y_1980_;
v___y_1960_ = v___x_2001_;
goto v___jp_1952_;
}
}
else
{
size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = lean_usize_of_nat(v___x_1995_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1984_, v___x_2002_, v___x_2003_, v___x_1996_, v___y_1979_);
lean_dec(v_fst_1984_);
v___y_1953_ = v___x_1994_;
v___y_1954_ = v___y_1978_;
v___y_1955_ = v___y_1979_;
v___y_1956_ = v_a_1991_;
v___y_1957_ = v_newGoals_1986_;
v___y_1958_ = v___y_1981_;
v___y_1959_ = v___y_1980_;
v___y_1960_ = v___x_2004_;
goto v___jp_1952_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_fst_1984_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_e_1887_);
lean_dec(v_mvarId_1885_);
v_a_2005_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1989_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1989_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2013_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1982_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1982_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_1972_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_term_x3f_1889_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2066_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1973_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1973_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_term_x3f_1889_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2074_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1971_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1971_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_term_x3f_1889_);
lean_dec_ref(v_e_1887_);
lean_dec(v___x_1886_);
lean_dec(v_mvarId_1885_);
v_a_2082_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_1970_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_1970_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
v___jp_1895_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_array_to_list(v___y_1901_);
v___x_1903_ = l_List_appendTR___redArg(v___y_1898_, v___x_1902_);
lean_inc(v___x_1903_);
v___x_1904_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1903_, v___y_1896_, v___y_1897_, v___y_1900_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1904_, 0);
lean_dec(v_unused_1912_);
v___x_1906_ = v___x_1904_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_dec(v___x_1904_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1903_);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1903_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v___x_1903_);
v_a_1913_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1904_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1904_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
v___jp_1921_:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1926_, v___y_1923_, v___y_1924_, v___y_1928_, v___y_1927_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
v___x_1932_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1929_, v___y_1925_, v___y_1923_, v___y_1924_, v___y_1928_, v___y_1927_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_array_get_size(v_a_1931_);
v___x_1935_ = lean_mk_empty_array_with_capacity(v___y_1922_);
v___x_1936_ = lean_nat_dec_lt(v___y_1922_, v___x_1934_);
if (v___x_1936_ == 0)
{
lean_dec(v_a_1931_);
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___y_1924_;
v___y_1898_ = v_a_1933_;
v___y_1899_ = v___y_1927_;
v___y_1900_ = v___y_1928_;
v___y_1901_ = v___x_1935_;
goto v___jp_1895_;
}
else
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_nat_dec_le(v___x_1934_, v___x_1934_);
if (v___x_1937_ == 0)
{
if (v___x_1936_ == 0)
{
lean_dec(v_a_1931_);
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___y_1924_;
v___y_1898_ = v_a_1933_;
v___y_1899_ = v___y_1927_;
v___y_1900_ = v___y_1928_;
v___y_1901_ = v___x_1935_;
goto v___jp_1895_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1934_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1933_, v_a_1931_, v___x_1938_, v___x_1939_, v___x_1935_);
lean_dec(v_a_1931_);
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___y_1924_;
v___y_1898_ = v_a_1933_;
v___y_1899_ = v___y_1927_;
v___y_1900_ = v___y_1928_;
v___y_1901_ = v___x_1940_;
goto v___jp_1895_;
}
}
else
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1934_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1933_, v_a_1931_, v___x_1941_, v___x_1942_, v___x_1935_);
lean_dec(v_a_1931_);
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___y_1924_;
v___y_1898_ = v_a_1933_;
v___y_1899_ = v___y_1927_;
v___y_1900_ = v___y_1928_;
v___y_1901_ = v___x_1943_;
goto v___jp_1895_;
}
}
}
else
{
lean_dec(v_a_1931_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v___x_1932_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_a_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
v_a_1944_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1930_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1930_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
v___jp_1952_:
{
if (lean_obj_tag(v___y_1960_) == 0)
{
lean_object* v_a_1961_; 
v_a_1961_ = lean_ctor_get(v___y_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___y_1960_);
v___y_1922_ = v___y_1953_;
v___y_1923_ = v___y_1954_;
v___y_1924_ = v___y_1955_;
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1958_;
v___y_1928_ = v___y_1959_;
v_a_1929_ = v_a_1961_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
v_a_1962_ = lean_ctor_get(v___y_1960_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___y_1960_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___y_1960_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___y_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2090_, lean_object* v___x_2091_, lean_object* v_e_2092_, lean_object* v_cfg_2093_, lean_object* v_term_x3f_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2090_, v___x_2091_, v_e_2092_, v_cfg_2093_, v_term_x3f_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec_ref(v_cfg_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2101_, lean_object* v_e_2102_, lean_object* v_cfg_2103_, lean_object* v_term_x3f_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2101_);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2111_, 0, v_mvarId_2101_);
lean_closure_set(v___f_2111_, 1, v___x_2110_);
lean_closure_set(v___f_2111_, 2, v_e_2102_);
lean_closure_set(v___f_2111_, 3, v_cfg_2103_);
lean_closure_set(v___f_2111_, 4, v_term_x3f_2104_);
v___x_2112_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2101_, v___f_2111_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2113_, lean_object* v_e_2114_, lean_object* v_cfg_2115_, lean_object* v_term_x3f_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_MVarId_apply(v_mvarId_2113_, v_e_2114_, v_cfg_2115_, v_term_x3f_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2123_, lean_object* v_val_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2123_, v_val_2124_, v___y_2126_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2131_, lean_object* v_val_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2131_, v_val_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2139_, size_t v_i_2140_, size_t v_stop_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2139_, v_i_2140_, v_stop_2141_, v_b_2142_, v___y_2144_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v_i_boxed_2158_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2149_, v_i_boxed_2158_, v_stop_boxed_2159_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2162_, v_x_2163_, v_x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2166_, lean_object* v_x_2167_, size_t v_x_2168_, size_t v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2167_, v_x_2168_, v_x_2169_, v_x_2170_, v_x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
size_t v_x_8059__boxed_2179_; size_t v_x_8060__boxed_2180_; lean_object* v_res_2181_; 
v_x_8059__boxed_2179_ = lean_unbox_usize(v_x_2175_);
lean_dec(v_x_2175_);
v_x_8060__boxed_2180_ = lean_unbox_usize(v_x_2176_);
lean_dec(v_x_2176_);
v_res_2181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2173_, v_x_2174_, v_x_8059__boxed_2179_, v_x_8060__boxed_2180_, v_x_2177_, v_x_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2182_, lean_object* v_n_2183_, lean_object* v_k_2184_, lean_object* v_v_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2183_, v_k_2184_, v_v_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2187_, size_t v_depth_2188_, lean_object* v_keys_2189_, lean_object* v_vals_2190_, lean_object* v_heq_2191_, lean_object* v_i_2192_, lean_object* v_entries_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2188_, v_keys_2189_, v_vals_2190_, v_i_2192_, v_entries_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2195_, lean_object* v_depth_2196_, lean_object* v_keys_2197_, lean_object* v_vals_2198_, lean_object* v_heq_2199_, lean_object* v_i_2200_, lean_object* v_entries_2201_){
_start:
{
size_t v_depth_boxed_2202_; lean_object* v_res_2203_; 
v_depth_boxed_2202_ = lean_unbox_usize(v_depth_2196_);
lean_dec(v_depth_2196_);
v_res_2203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2195_, v_depth_boxed_2202_, v_keys_2197_, v_vals_2198_, v_heq_2199_, v_i_2200_, v_entries_2201_);
lean_dec_ref(v_vals_2198_);
lean_dec_ref(v_keys_2197_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2205_, v_x_2206_, v_x_2207_, v_x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2213_, lean_object* v_c_2214_, lean_object* v_cfg_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2221_; 
lean_inc_ref(v_a_2218_);
lean_inc(v_c_2214_);
v___x_2221_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2214_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2224_ = 0;
v___x_2225_ = l_Lean_MessageData_ofConstName(v_c_2214_, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2223_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2223_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
v___x_2229_ = l_Lean_MVarId_apply(v_mvar_2213_, v_a_2222_, v_cfg_2215_, v___x_2228_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
return v___x_2229_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec_ref(v_cfg_2215_);
lean_dec(v_c_2214_);
lean_dec(v_mvar_2213_);
v_a_2230_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2221_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2221_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2238_, lean_object* v_c_2239_, lean_object* v_cfg_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_MVarId_applyConst(v_mvar_2238_, v_c_2239_, v_cfg_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v_env_2254_; lean_object* v___x_2255_; lean_object* v_mctx_2256_; lean_object* v_lctx_2257_; lean_object* v_options_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2253_ = lean_st_ref_get(v___y_2251_);
v_env_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc_ref(v_env_2254_);
lean_dec(v___x_2253_);
v___x_2255_ = lean_st_ref_get(v___y_2249_);
v_mctx_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_mctx_2256_);
lean_dec(v___x_2255_);
v_lctx_2257_ = lean_ctor_get(v___y_2248_, 2);
v_options_2258_ = lean_ctor_get(v___y_2250_, 2);
lean_inc_ref(v_options_2258_);
lean_inc_ref(v_lctx_2257_);
v___x_2259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2259_, 0, v_env_2254_);
lean_ctor_set(v___x_2259_, 1, v_mctx_2256_);
lean_ctor_set(v___x_2259_, 2, v_lctx_2257_);
lean_ctor_set(v___x_2259_, 3, v_options_2258_);
v___x_2260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v_msgData_2247_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_ref_2275_; lean_object* v___x_2276_; lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2285_; 
v_ref_2275_ = lean_ctor_get(v___y_2272_, 5);
v___x_2276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2285_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2285_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
lean_inc(v_ref_2275_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_ref_2275_);
lean_ctor_set(v___x_2281_, 1, v_a_2277_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set_tag(v___x_2279_, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2281_);
v___x_2283_ = v___x_2279_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_bs_2295_){
_start:
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2296_ == 0)
{
return v_bs_2295_;
}
else
{
lean_object* v_v_2297_; lean_object* v___x_2298_; lean_object* v_bs_x27_2299_; lean_object* v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v_v_2297_ = lean_array_uget(v_bs_2295_, v_i_2294_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v_bs_x27_2299_ = lean_array_uset(v_bs_2295_, v_i_2294_, v___x_2298_);
v___x_2300_ = l_Lean_Expr_mvarId_x21(v_v_2297_);
lean_dec(v_v_2297_);
v___x_2301_ = ((size_t)1ULL);
v___x_2302_ = lean_usize_add(v_i_2294_, v___x_2301_);
v___x_2303_ = lean_array_uset(v_bs_x27_2299_, v_i_2294_, v___x_2300_);
v_i_2294_ = v___x_2302_;
v_bs_2295_ = v___x_2303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2305_, lean_object* v_i_2306_, lean_object* v_bs_2307_){
_start:
{
size_t v_sz_boxed_2308_; size_t v_i_boxed_2309_; lean_object* v_res_2310_; 
v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2305_);
lean_dec(v_sz_2305_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2308_, v_i_boxed_2309_, v_bs_2307_);
return v_res_2310_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2329_, lean_object* v___x_2330_, lean_object* v_e_2331_, lean_object* v_n_2332_, uint8_t v_useApproxDefEq_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
lean_inc(v_mvarId_2329_);
v___x_2339_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2329_, v___x_2330_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; 
lean_dec_ref(v___x_2339_);
lean_inc(v_mvarId_2329_);
v___x_2340_ = l_Lean_MVarId_getType(v_mvarId_2329_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc_ref(v_e_2331_);
v___x_2342_ = lean_infer_type(v_e_2331_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = 0;
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v_n_2332_);
v___x_2345_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2343_, v_n_2332_, v___x_2344_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_fst_2347_; lean_object* v_snd_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2438_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v_fst_2347_ = lean_ctor_get(v_a_2346_, 0);
v_snd_2348_ = lean_ctor_get(v_a_2346_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2350_ = v_a_2346_;
v_isShared_2351_ = v_isSharedCheck_2438_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_snd_2348_);
lean_inc(v_fst_2347_);
lean_dec(v_a_2346_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2438_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___y_2353_; lean_object* v_snd_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2436_; 
v_snd_2368_ = lean_ctor_get(v_snd_2348_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_snd_2348_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; 
v_unused_2437_ = lean_ctor_get(v_snd_2348_, 0);
lean_dec(v_unused_2437_);
v___x_2370_ = v_snd_2348_;
v_isShared_2371_ = v_isSharedCheck_2436_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snd_2368_);
lean_dec(v_snd_2348_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2436_;
goto v_resetjp_2369_;
}
v___jp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2366_; 
lean_inc(v_fst_2347_);
v___x_2354_ = l_Lean_Expr_beta(v_e_2331_, v_fst_2347_);
v___x_2355_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2329_, v___x_2354_, v___y_2353_);
lean_dec(v___y_2353_);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v___x_2355_, 0);
lean_dec(v_unused_2367_);
v___x_2357_ = v___x_2355_;
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v___x_2355_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
size_t v_sz_2359_; size_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v_sz_2359_ = lean_array_size(v_fst_2347_);
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2359_, v___x_2360_, v_fst_2347_);
v___x_2362_ = lean_array_to_list(v___x_2361_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2362_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
v_resetjp_2369_:
{
lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = lean_array_get_size(v_fst_2347_);
v___x_2417_ = lean_nat_dec_eq(v___x_2416_, v_n_2332_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_del_object(v___x_2370_);
lean_del_object(v___x_2350_);
lean_dec(v_fst_2347_);
lean_dec(v_a_2341_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v___x_2418_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2419_ = l_Nat_reprFast(v_n_2332_);
v___x_2420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
v___x_2421_ = l_Lean_MessageData_ofFormat(v___x_2420_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2418_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_indentExpr(v_snd_2368_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2426_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
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
else
{
v___y_2373_ = v___y_2334_;
v___y_2374_ = v___y_2335_;
v___y_2375_ = v___y_2336_;
v___y_2376_ = v___y_2337_;
goto v___jp_2372_;
}
v___jp_2372_:
{
lean_object* v___x_2377_; 
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
lean_inc(v_a_2341_);
lean_inc(v_snd_2368_);
v___x_2377_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2333_, v_snd_2368_, v_a_2341_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; uint8_t v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_unbox(v_a_2378_);
lean_dec(v_a_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec(v_fst_2347_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v___x_2380_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2381_ = l_Lean_indentExpr(v_a_2341_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 7);
lean_ctor_set(v___x_2370_, 1, v___x_2381_);
lean_ctor_set(v___x_2370_, 0, v___x_2380_);
v___x_2383_ = v___x_2370_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 7);
lean_ctor_set(v___x_2350_, 1, v___x_2384_);
lean_ctor_set(v___x_2350_, 0, v___x_2383_);
v___x_2386_ = v___x_2350_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v___x_2387_ = l_Lean_indentExpr(v_snd_2368_);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l_Nat_reprFast(v_n_2332_);
v___x_2392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
v___x_2393_ = l_Lean_MessageData_ofFormat(v___x_2392_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2390_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2396_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
else
{
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v___y_2373_);
lean_del_object(v___x_2370_);
lean_dec(v_snd_2368_);
lean_del_object(v___x_2350_);
lean_dec(v_a_2341_);
lean_dec(v_n_2332_);
v___y_2353_ = v___y_2374_;
goto v___jp_2352_;
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_del_object(v___x_2370_);
lean_dec(v_snd_2368_);
lean_del_object(v___x_2350_);
lean_dec(v_fst_2347_);
lean_dec(v_a_2341_);
lean_dec(v_n_2332_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v_a_2408_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2377_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2377_);
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
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_a_2341_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_n_2332_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v_a_2439_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2345_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2345_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2341_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_n_2332_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v_a_2447_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2342_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2342_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_n_2332_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v_a_2455_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2340_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2340_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_n_2332_);
lean_dec_ref(v_e_2331_);
lean_dec(v_mvarId_2329_);
v_a_2463_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2339_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2339_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2471_, lean_object* v___x_2472_, lean_object* v_e_2473_, lean_object* v_n_2474_, lean_object* v_useApproxDefEq_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2481_; lean_object* v_res_2482_; 
v_useApproxDefEq_boxed_2481_ = lean_unbox(v_useApproxDefEq_2475_);
v_res_2482_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2471_, v___x_2472_, v_e_2473_, v_n_2474_, v_useApproxDefEq_boxed_2481_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2483_, lean_object* v_e_2484_, lean_object* v_n_2485_, uint8_t v_useApproxDefEq_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; 
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2493_ = lean_box(v_useApproxDefEq_2486_);
lean_inc(v_mvarId_2483_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2494_, 0, v_mvarId_2483_);
lean_closure_set(v___f_2494_, 1, v___x_2492_);
lean_closure_set(v___f_2494_, 2, v_e_2484_);
lean_closure_set(v___f_2494_, 3, v_n_2485_);
lean_closure_set(v___f_2494_, 4, v___x_2493_);
v___x_2495_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2483_, v___f_2494_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2496_, lean_object* v_e_2497_, lean_object* v_n_2498_, lean_object* v_useApproxDefEq_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2505_; lean_object* v_res_2506_; 
v_useApproxDefEq_boxed_2505_ = lean_unbox(v_useApproxDefEq_2499_);
v_res_2506_ = l_Lean_MVarId_applyN(v_mvarId_2496_, v_e_2497_, v_n_2498_, v_useApproxDefEq_boxed_2505_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2507_, lean_object* v_msg_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2515_, lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2515_, v_msg_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2535_ = l_Lean_mkConst(v___x_2534_, v___x_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2536_, lean_object* v_type_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2544_; 
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
v___x_2544_ = lean_whnf(v_type_2537_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2547_ = lean_unsigned_to_nat(2u);
v___x_2548_ = l_Lean_Expr_isAppOfArity(v_a_2545_, v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2549_ = lean_st_ref_get(v_a_2538_);
v___x_2550_ = lean_array_get_size(v___x_2549_);
lean_dec(v___x_2549_);
v___x_2551_ = lean_unsigned_to_nat(1u);
v___x_2552_ = lean_nat_add(v___x_2550_, v___x_2551_);
v___x_2553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2554_ = lean_name_append_index_after(v___x_2553_, v___x_2552_);
v___x_2555_ = l_Lean_Name_append(v_tag_2536_, v___x_2554_);
v___x_2556_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2545_, v___x_2555_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2568_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2561_ = lean_st_ref_take(v_a_2538_);
v___x_2562_ = l_Lean_Expr_mvarId_x21(v_a_2557_);
v___x_2563_ = lean_array_push(v___x_2561_, v___x_2562_);
v___x_2564_ = lean_st_ref_set(v_a_2538_, v___x_2563_);
if (v_isShared_2560_ == 0)
{
v___x_2566_ = v___x_2559_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2557_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = l_Lean_Expr_appFn_x21(v_a_2545_);
v___x_2570_ = l_Lean_Expr_appArg_x21(v___x_2569_);
lean_dec_ref(v___x_2569_);
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc_ref(v___x_2570_);
lean_inc(v_tag_2536_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2536_, v___x_2570_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = l_Lean_Expr_appArg_x21(v_a_2545_);
lean_dec(v_a_2545_);
lean_inc_ref(v___x_2573_);
v___x_2574_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2536_, v___x_2573_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2584_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2584_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2584_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2580_ = l_Lean_mkApp4(v___x_2579_, v___x_2570_, v___x_2573_, v_a_2572_, v_a_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2580_);
v___x_2582_ = v___x_2577_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_dec_ref(v___x_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v___x_2570_);
return v___x_2574_;
}
}
else
{
lean_dec_ref(v___x_2570_);
lean_dec(v_a_2545_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_tag_2536_);
return v___x_2571_;
}
}
}
else
{
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_tag_2536_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2585_, lean_object* v_type_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2585_, v_type_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2587_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2594_, lean_object* v___x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
lean_inc(v_mvarId_2594_);
v___x_2601_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2594_, v___x_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref(v___x_2601_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
lean_inc(v_mvarId_2594_);
v___x_2602_ = l_Lean_MVarId_getType_x27(v_mvarId_2594_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2648_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2648_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2648_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2608_ = lean_unsigned_to_nat(2u);
v___x_2609_ = l_Lean_Expr_isAppOfArity(v_a_2603_, v___x_2607_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_dec(v_a_2603_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
v___x_2610_ = lean_box(0);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_mvarId_2594_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2611_);
v___x_2613_ = v___x_2605_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
else
{
lean_object* v___x_2615_; 
lean_del_object(v___x_2605_);
lean_inc(v_mvarId_2594_);
v___x_2615_ = l_Lean_MVarId_getTag(v_mvarId_2594_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2618_ = lean_st_mk_ref(v___x_2617_);
lean_inc(v___y_2597_);
v___x_2619_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2616_, v_a_2603_, v___x_2618_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2630_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = lean_st_ref_get(v___x_2618_);
lean_dec(v___x_2618_);
v___x_2622_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2594_, v_a_2620_, v___y_2597_);
lean_dec(v___y_2597_);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2622_, 0);
lean_dec(v_unused_2631_);
v___x_2624_ = v___x_2622_;
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v___x_2622_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = lean_array_to_list(v___x_2621_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v___x_2618_);
lean_dec(v___y_2597_);
lean_dec(v_mvarId_2594_);
v_a_2632_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2619_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2619_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_a_2603_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_mvarId_2594_);
v_a_2640_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2615_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2615_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_mvarId_2594_);
v_a_2649_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2602_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2602_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_mvarId_2594_);
v_a_2657_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2601_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2601_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2665_, lean_object* v___x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2665_, v___x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; 
v___x_2682_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2676_);
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2683_, 0, v_mvarId_2676_);
lean_closure_set(v___f_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2676_, v___f_2683_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_MVarId_splitAndCore(v_mvarId_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_MVarId_splitAndCore(v_mvarId_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_MVarId_splitAnd(v_mvarId_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v_res_2705_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2711_ = l_Lean_mkConst(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2716_, lean_object* v___x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
lean_inc(v_mvarId_2716_);
v___x_2723_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2716_, v___x_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; 
lean_dec_ref(v___x_2723_);
lean_inc(v_mvarId_2716_);
v___x_2724_ = l_Lean_MVarId_getType(v_mvarId_2716_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v___x_2724_);
v___x_2726_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2725_, v___y_2719_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v_a_2727_);
v___x_2728_ = l_Lean_Meta_getLevel(v_a_2727_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref(v___x_2728_);
lean_inc(v_mvarId_2716_);
v___x_2730_ = l_Lean_MVarId_getTag(v_mvarId_2716_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2734_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2733_, v_a_2731_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2748_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
v___x_2736_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2729_);
lean_ctor_set(v___x_2737_, 1, v___x_2732_);
v___x_2738_ = l_Lean_mkConst(v___x_2736_, v___x_2737_);
lean_inc(v_a_2735_);
v___x_2739_ = l_Lean_mkAppB(v___x_2738_, v_a_2727_, v_a_2735_);
v___x_2740_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2716_, v___x_2739_, v___y_2719_);
lean_dec(v___y_2719_);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2740_, 0);
lean_dec(v_unused_2749_);
v___x_2742_ = v___x_2740_;
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
else
{
lean_dec(v___x_2740_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2744_ = l_Lean_Expr_mvarId_x21(v_a_2735_);
lean_dec(v_a_2735_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2744_);
v___x_2746_ = v___x_2742_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2729_);
lean_dec(v_a_2727_);
lean_dec(v___y_2719_);
lean_dec(v_mvarId_2716_);
v_a_2750_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2734_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2734_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2729_);
lean_dec(v_a_2727_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_mvarId_2716_);
v_a_2758_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2730_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2730_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2727_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_mvarId_2716_);
v_a_2766_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2728_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2728_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_mvarId_2716_);
v_a_2774_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2724_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2724_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_mvarId_2716_);
v_a_2782_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2723_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2723_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2790_, lean_object* v___x_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2790_, v___x_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v___x_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; 
v___x_2807_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2801_);
v___f_2808_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2808_, 0, v_mvarId_2801_);
lean_closure_set(v___f_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2801_, v___f_2808_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_MVarId_exfalso(v_mvarId_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
return v_res_2816_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2821_ = l_Lean_MessageData_ofFormat(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2828_, lean_object* v_name_2829_, lean_object* v_idx_2830_, lean_object* v_expected_x3f_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___x_2844_; 
lean_inc(v_name_2829_);
lean_inc(v_goal_2828_);
v___x_2844_ = l_Lean_MVarId_checkNotAssigned(v_goal_2828_, v_name_2829_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref(v___x_2844_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v_goal_2828_);
v___x_2845_ = l_Lean_MVarId_getType_x27(v_goal_2828_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = l_Lean_Expr_getAppFn(v_a_2846_);
lean_dec(v_a_2846_);
if (lean_obj_tag(v___x_2847_) == 4)
{
lean_object* v_declName_2848_; lean_object* v_us_2849_; lean_object* v___x_2850_; lean_object* v_env_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; 
v_declName_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_declName_2848_);
v_us_2849_ = lean_ctor_get(v___x_2847_, 1);
lean_inc(v_us_2849_);
lean_dec_ref(v___x_2847_);
v___x_2850_ = lean_st_ref_get(v___y_2835_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_env_2851_);
lean_dec(v___x_2850_);
v___x_2852_ = 0;
v___x_2853_ = l_Lean_Environment_find_x3f(v_env_2851_, v_declName_2848_, v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec(v_us_2849_);
lean_dec(v_expected_x3f_2831_);
lean_dec(v_idx_2830_);
v___y_2838_ = v___y_2832_;
v___y_2839_ = v___y_2833_;
v___y_2840_ = v___y_2834_;
v___y_2841_ = v___y_2835_;
goto v___jp_2837_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2924_; 
v_val_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2924_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_val_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2924_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
if (lean_obj_tag(v_val_2854_) == 5)
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2923_; 
v_val_2858_ = lean_ctor_get(v_val_2854_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_val_2854_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2860_ = v_val_2854_;
v_isShared_2861_ = v_isSharedCheck_2923_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v_val_2854_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2923_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; 
if (lean_obj_tag(v_expected_x3f_2831_) == 1)
{
lean_object* v_val_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2922_; 
v_val_2893_ = lean_ctor_get(v_expected_x3f_2831_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_expected_x3f_2831_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2895_ = v_expected_x3f_2831_;
v_isShared_2896_ = v_isSharedCheck_2922_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_val_2893_);
lean_dec(v_expected_x3f_2831_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2922_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v_ctors_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_ctors_2897_ = lean_ctor_get(v_val_2858_, 4);
v___x_2898_ = l_List_lengthTR___redArg(v_ctors_2897_);
v___x_2899_ = lean_nat_dec_eq(v___x_2898_, v_val_2893_);
lean_dec(v___x_2898_);
if (v___x_2899_ == 0)
{
uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2900_ = 1;
lean_inc(v_name_2829_);
v___x_2901_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2829_, v___x_2900_);
v___x_2902_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
v___x_2904_ = l_Nat_reprFast(v_val_2893_);
v___x_2905_ = lean_string_append(v___x_2903_, v___x_2904_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
v___x_2909_ = l_Lean_MessageData_ofFormat(v___x_2908_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2909_);
v___x_2911_ = v___x_2895_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; 
lean_inc(v_goal_2828_);
lean_inc(v_name_2829_);
v___x_2912_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2829_, v_goal_2828_, v___x_2911_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref(v___x_2912_);
v___y_2863_ = v___y_2832_;
v___y_2864_ = v___y_2833_;
v___y_2865_ = v___y_2834_;
v___y_2866_ = v___y_2835_;
goto v___jp_2862_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_del_object(v___x_2860_);
lean_dec_ref(v_val_2858_);
lean_del_object(v___x_2856_);
lean_dec(v_us_2849_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_idx_2830_);
lean_dec(v_name_2829_);
lean_dec(v_goal_2828_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
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
}
}
else
{
lean_del_object(v___x_2895_);
lean_dec(v_val_2893_);
v___y_2863_ = v___y_2832_;
v___y_2864_ = v___y_2833_;
v___y_2865_ = v___y_2834_;
v___y_2866_ = v___y_2835_;
goto v___jp_2862_;
}
}
}
else
{
lean_dec(v_expected_x3f_2831_);
v___y_2863_ = v___y_2832_;
v___y_2864_ = v___y_2833_;
v___y_2865_ = v___y_2834_;
v___y_2866_ = v___y_2835_;
goto v___jp_2862_;
}
v___jp_2862_:
{
lean_object* v_ctors_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_ctors_2867_ = lean_ctor_get(v_val_2858_, 4);
lean_inc(v_ctors_2867_);
lean_dec_ref(v_val_2858_);
v___x_2868_ = l_List_lengthTR___redArg(v_ctors_2867_);
v___x_2869_ = lean_nat_dec_lt(v_idx_2830_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
lean_dec(v_ctors_2867_);
lean_dec(v_us_2849_);
v___x_2870_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2871_ = l_Nat_reprFast(v_idx_2830_);
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
v___x_2875_ = l_Nat_reprFast(v___x_2868_);
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 3);
lean_ctor_set(v___x_2860_, 0, v___x_2878_);
v___x_2880_ = v___x_2860_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = l_Lean_MessageData_ofFormat(v___x_2880_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2881_);
v___x_2883_ = v___x_2856_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2829_, v_goal_2828_, v___x_2883_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v___x_2884_;
}
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec(v___x_2868_);
lean_del_object(v___x_2860_);
lean_del_object(v___x_2856_);
lean_dec(v_name_2829_);
v___x_2887_ = l_List_get___redArg(v_ctors_2867_, v_idx_2830_);
lean_dec(v_ctors_2867_);
v___x_2888_ = l_Lean_mkConst(v___x_2887_, v_us_2849_);
v___x_2889_ = 0;
v___x_2890_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2890_, 0, v___x_2889_);
lean_ctor_set_uint8(v___x_2890_, 1, v___x_2869_);
lean_ctor_set_uint8(v___x_2890_, 2, v___x_2852_);
lean_ctor_set_uint8(v___x_2890_, 3, v___x_2869_);
v___x_2891_ = lean_box(0);
v___x_2892_ = l_Lean_MVarId_apply(v_goal_2828_, v___x_2888_, v___x_2890_, v___x_2891_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2892_;
}
}
}
}
else
{
lean_del_object(v___x_2856_);
lean_dec(v_val_2854_);
lean_dec(v_us_2849_);
lean_dec(v_expected_x3f_2831_);
lean_dec(v_idx_2830_);
v___y_2838_ = v___y_2832_;
v___y_2839_ = v___y_2833_;
v___y_2840_ = v___y_2834_;
v___y_2841_ = v___y_2835_;
goto v___jp_2837_;
}
}
}
}
else
{
lean_dec_ref(v___x_2847_);
lean_dec(v_expected_x3f_2831_);
lean_dec(v_idx_2830_);
v___y_2838_ = v___y_2832_;
v___y_2839_ = v___y_2833_;
v___y_2840_ = v___y_2834_;
v___y_2841_ = v___y_2835_;
goto v___jp_2837_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_expected_x3f_2831_);
lean_dec(v_idx_2830_);
lean_dec(v_name_2829_);
lean_dec(v_goal_2828_);
v_a_2925_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2845_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2845_);
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
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_expected_x3f_2831_);
lean_dec(v_idx_2830_);
lean_dec(v_name_2829_);
lean_dec(v_goal_2828_);
v_a_2933_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2844_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2844_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
v___jp_2837_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2843_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2829_, v_goal_2828_, v___x_2842_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2941_, lean_object* v_name_2942_, lean_object* v_idx_2943_, lean_object* v_expected_x3f_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2941_, v_name_2942_, v_idx_2943_, v_expected_x3f_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2951_, lean_object* v_idx_2952_, lean_object* v_expected_x3f_2953_, lean_object* v_goal_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; 
lean_inc(v_goal_2954_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2960_, 0, v_goal_2954_);
lean_closure_set(v___f_2960_, 1, v_name_2951_);
lean_closure_set(v___f_2960_, 2, v_idx_2952_);
lean_closure_set(v___f_2960_, 3, v_expected_x3f_2953_);
v___x_2961_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2954_, v___f_2960_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2962_, lean_object* v_idx_2963_, lean_object* v_expected_x3f_2964_, lean_object* v_goal_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_MVarId_nthConstructor(v_name_2962_, v_idx_2963_, v_expected_x3f_2964_, v_goal_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Meta_saveState___redArg(v___y_2974_, v___y_2976_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref(v___x_2978_);
lean_inc(v___y_2976_);
lean_inc(v___y_2974_);
v___x_2980_ = lean_apply_5(v_x_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, lean_box(0));
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_a_2979_);
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2981_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3019_; 
v_a_2990_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2992_ = v___x_2980_;
v_isShared_2993_ = v_isSharedCheck_3019_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2980_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3019_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
uint8_t v___y_2995_; uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Exception_isInterrupt(v_a_2990_);
if (v___x_3017_ == 0)
{
uint8_t v___x_3018_; 
lean_inc(v_a_2990_);
v___x_3018_ = l_Lean_Exception_isRuntime(v_a_2990_);
v___y_2995_ = v___x_3018_;
goto v___jp_2994_;
}
else
{
v___y_2995_ = v___x_3017_;
goto v___jp_2994_;
}
v___jp_2994_:
{
if (v___y_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_del_object(v___x_2992_);
lean_dec(v_a_2990_);
v___x_2996_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2979_, v___y_2974_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
lean_dec(v_a_2979_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3004_; 
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v___x_2996_, 0);
lean_dec(v_unused_3005_);
v___x_2998_ = v___x_2996_;
v_isShared_2999_ = v_isSharedCheck_3004_;
goto v_resetjp_2997_;
}
else
{
lean_dec(v___x_2996_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3004_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_3000_ = lean_box(0);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3000_);
v___x_3002_ = v___x_2998_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
v_a_3006_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2996_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2996_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_a_2979_);
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
if (v_isShared_2993_ == 0)
{
v___x_3015_ = v___x_2992_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_2990_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_x_2972_);
v_a_3020_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_2978_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_2978_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3035_, lean_object* v_x_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3043_, lean_object* v_x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3043_, v_x_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
return v_res_3050_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3054_, lean_object* v___x_3055_, lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
lean_inc(v___y_3059_);
lean_inc_ref(v___y_3058_);
v___x_3063_ = l_Lean_MVarId_apply(v_mvarId_3054_, v___x_3055_, v___x_3056_, v___x_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3080_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3080_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3080_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; 
if (lean_obj_tag(v_a_3064_) == 1)
{
lean_object* v_tail_3075_; 
v_tail_3075_ = lean_ctor_get(v_a_3064_, 1);
if (lean_obj_tag(v_tail_3075_) == 0)
{
lean_object* v_head_3076_; lean_object* v___x_3078_; 
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
v_head_3076_ = lean_ctor_get(v_a_3064_, 0);
lean_inc(v_head_3076_);
lean_dec_ref(v_a_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_head_3076_);
v___x_3078_ = v___x_3066_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_head_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
else
{
lean_dec_ref(v_a_3064_);
lean_del_object(v___x_3066_);
v___y_3069_ = v___y_3058_;
v___y_3070_ = v___y_3059_;
v___y_3071_ = v___y_3060_;
v___y_3072_ = v___y_3061_;
goto v___jp_3068_;
}
}
else
{
lean_del_object(v___x_3066_);
lean_dec(v_a_3064_);
v___y_3069_ = v___y_3058_;
v___y_3070_ = v___y_3059_;
v___y_3071_ = v___y_3060_;
v___y_3072_ = v___y_3061_;
goto v___jp_3068_;
}
v___jp_3068_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3074_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3073_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
v_a_3081_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3063_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3063_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3089_, lean_object* v___x_3090_, lean_object* v___x_3091_, lean_object* v___x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
return v_res_3098_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3104_ = l_Lean_mkConst(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; 
v___x_3115_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3116_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3117_ = lean_box(0);
lean_inc(v_mvarId_3109_);
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3118_, 0, v_mvarId_3109_);
lean_closure_set(v___f_3118_, 1, v___x_3115_);
lean_closure_set(v___f_3118_, 2, v___x_3116_);
lean_closure_set(v___f_3118_, 3, v___x_3117_);
v___x_3119_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3118_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3131_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3131_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3131_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
if (lean_obj_tag(v_a_3120_) == 0)
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v_mvarId_3109_);
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_mvarId_3109_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
else
{
lean_object* v_val_3127_; lean_object* v___x_3129_; 
lean_dec(v_mvarId_3109_);
v_val_3127_ = lean_ctor_get(v_a_3120_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v_a_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v_val_3127_);
v___x_3129_ = v___x_3122_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_val_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_mvarId_3109_);
v_a_3132_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3119_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3119_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_MVarId_iffOfEq(v_mvarId_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
return v_res_3146_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3155_ = l_Lean_mkConst(v___x_3154_, v___x_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3156_, lean_object* v_mvarId_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___x_3170_; uint8_t v_foApprox_3171_; uint8_t v_ctxApprox_3172_; uint8_t v_quasiPatternApprox_3173_; uint8_t v_constApprox_3174_; uint8_t v_isDefEqStuckEx_3175_; uint8_t v_unificationHints_3176_; uint8_t v_proofIrrelevance_3177_; uint8_t v_assignSyntheticOpaque_3178_; uint8_t v_offsetCnstrs_3179_; uint8_t v_etaStruct_3180_; uint8_t v_univApprox_3181_; uint8_t v_iota_3182_; uint8_t v_beta_3183_; uint8_t v_proj_3184_; uint8_t v_zeta_3185_; uint8_t v_zetaDelta_3186_; uint8_t v_zetaUnused_3187_; uint8_t v_zetaHave_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3276_; 
v___x_3170_ = l_Lean_Meta_Context_config(v___y_3158_);
v_foApprox_3171_ = lean_ctor_get_uint8(v___x_3170_, 0);
v_ctxApprox_3172_ = lean_ctor_get_uint8(v___x_3170_, 1);
v_quasiPatternApprox_3173_ = lean_ctor_get_uint8(v___x_3170_, 2);
v_constApprox_3174_ = lean_ctor_get_uint8(v___x_3170_, 3);
v_isDefEqStuckEx_3175_ = lean_ctor_get_uint8(v___x_3170_, 4);
v_unificationHints_3176_ = lean_ctor_get_uint8(v___x_3170_, 5);
v_proofIrrelevance_3177_ = lean_ctor_get_uint8(v___x_3170_, 6);
v_assignSyntheticOpaque_3178_ = lean_ctor_get_uint8(v___x_3170_, 7);
v_offsetCnstrs_3179_ = lean_ctor_get_uint8(v___x_3170_, 8);
v_etaStruct_3180_ = lean_ctor_get_uint8(v___x_3170_, 10);
v_univApprox_3181_ = lean_ctor_get_uint8(v___x_3170_, 11);
v_iota_3182_ = lean_ctor_get_uint8(v___x_3170_, 12);
v_beta_3183_ = lean_ctor_get_uint8(v___x_3170_, 13);
v_proj_3184_ = lean_ctor_get_uint8(v___x_3170_, 14);
v_zeta_3185_ = lean_ctor_get_uint8(v___x_3170_, 15);
v_zetaDelta_3186_ = lean_ctor_get_uint8(v___x_3170_, 16);
v_zetaUnused_3187_ = lean_ctor_get_uint8(v___x_3170_, 17);
v_zetaHave_3188_ = lean_ctor_get_uint8(v___x_3170_, 18);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3190_ = v___x_3170_;
v_isShared_3191_ = v_isSharedCheck_3276_;
goto v_resetjp_3189_;
}
else
{
lean_dec(v___x_3170_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3276_;
goto v_resetjp_3189_;
}
v___jp_3163_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3169_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3168_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v___x_3169_;
}
v_resetjp_3189_:
{
uint8_t v_trackZetaDelta_3192_; lean_object* v_zetaDeltaSet_3193_; lean_object* v_lctx_3194_; lean_object* v_localInstances_3195_; lean_object* v_defEqCtx_x3f_3196_; lean_object* v_synthPendingDepth_3197_; lean_object* v_canUnfold_x3f_3198_; uint8_t v_univApprox_3199_; uint8_t v_inTypeClassResolution_3200_; uint8_t v_cacheInferType_3201_; lean_object* v_config_3203_; 
v_trackZetaDelta_3192_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*7);
v_zetaDeltaSet_3193_ = lean_ctor_get(v___y_3158_, 1);
v_lctx_3194_ = lean_ctor_get(v___y_3158_, 2);
v_localInstances_3195_ = lean_ctor_get(v___y_3158_, 3);
v_defEqCtx_x3f_3196_ = lean_ctor_get(v___y_3158_, 4);
v_synthPendingDepth_3197_ = lean_ctor_get(v___y_3158_, 5);
v_canUnfold_x3f_3198_ = lean_ctor_get(v___y_3158_, 6);
v_univApprox_3199_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3200_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*7 + 2);
v_cacheInferType_3201_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*7 + 3);
if (v_isShared_3191_ == 0)
{
v_config_3203_ = v___x_3190_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 0, v_foApprox_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 1, v_ctxApprox_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 2, v_quasiPatternApprox_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 3, v_constApprox_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 4, v_isDefEqStuckEx_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 5, v_unificationHints_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 6, v_proofIrrelevance_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 7, v_assignSyntheticOpaque_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 8, v_offsetCnstrs_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 10, v_etaStruct_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 11, v_univApprox_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 12, v_iota_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 13, v_beta_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 14, v_proj_3184_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 15, v_zeta_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 16, v_zetaDelta_3186_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 17, v_zetaUnused_3187_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, 18, v_zetaHave_3188_);
v_config_3203_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
uint64_t v___x_3204_; uint64_t v___x_3205_; uint64_t v___x_3206_; uint64_t v___x_3207_; uint64_t v___x_3208_; uint64_t v_key_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_ctor_set_uint8(v_config_3203_, 9, v___x_3156_);
v___x_3204_ = l_Lean_Meta_Context_configKey(v___y_3158_);
v___x_3205_ = 2ULL;
v___x_3206_ = lean_uint64_shift_right(v___x_3204_, v___x_3205_);
v___x_3207_ = lean_uint64_shift_left(v___x_3206_, v___x_3205_);
v___x_3208_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3156_);
v_key_3209_ = lean_uint64_lor(v___x_3207_, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3210_, 0, v_config_3203_);
lean_ctor_set_uint64(v___x_3210_, sizeof(void*)*1, v_key_3209_);
lean_inc(v_canUnfold_x3f_3198_);
lean_inc(v_synthPendingDepth_3197_);
lean_inc(v_defEqCtx_x3f_3196_);
lean_inc_ref(v_localInstances_3195_);
lean_inc_ref(v_lctx_3194_);
lean_inc(v_zetaDeltaSet_3193_);
v___x_3211_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v_zetaDeltaSet_3193_);
lean_ctor_set(v___x_3211_, 2, v_lctx_3194_);
lean_ctor_set(v___x_3211_, 3, v_localInstances_3195_);
lean_ctor_set(v___x_3211_, 4, v_defEqCtx_x3f_3196_);
lean_ctor_set(v___x_3211_, 5, v_synthPendingDepth_3197_);
lean_ctor_set(v___x_3211_, 6, v_canUnfold_x3f_3198_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7, v_trackZetaDelta_3192_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 1, v_univApprox_3199_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3200_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 3, v_cacheInferType_3201_);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3159_);
lean_inc(v_mvarId_3157_);
v___x_3212_ = l_Lean_MVarId_getType_x27(v_mvarId_3157_, v___x_3211_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref(v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3215_ = lean_unsigned_to_nat(3u);
v___x_3216_ = l_Lean_Expr_isAppOfArity(v_a_3213_, v___x_3214_, v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec(v_a_3213_);
lean_dec(v_mvarId_3157_);
v___x_3242_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3243_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3242_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = l_Lean_Expr_appFn_x21(v_a_3213_);
lean_dec(v_a_3213_);
v___x_3245_ = l_Lean_Expr_appArg_x21(v___x_3244_);
lean_dec_ref(v___x_3244_);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
v___x_3246_ = l_Lean_Meta_isProp(v___x_3245_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; uint8_t v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
v___x_3248_ = lean_unbox(v_a_3247_);
lean_dec(v_a_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_mvarId_3157_);
v___x_3249_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3250_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3249_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
else
{
goto v___jp_3217_;
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v_mvarId_3157_);
v_a_3259_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3246_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3246_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
v___jp_3217_:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3218_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3219_ = 0;
v___x_3220_ = 0;
v___x_3221_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3221_, 0, v___x_3219_);
lean_ctor_set_uint8(v___x_3221_, 1, v___x_3216_);
lean_ctor_set_uint8(v___x_3221_, 2, v___x_3220_);
lean_ctor_set_uint8(v___x_3221_, 3, v___x_3216_);
v___x_3222_ = lean_box(0);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
v___x_3223_ = l_Lean_MVarId_apply(v_mvarId_3157_, v___x_3218_, v___x_3221_, v___x_3222_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3233_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3233_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3233_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
if (lean_obj_tag(v_a_3224_) == 1)
{
lean_object* v_tail_3228_; 
v_tail_3228_ = lean_ctor_get(v_a_3224_, 1);
if (lean_obj_tag(v_tail_3228_) == 0)
{
lean_object* v_head_3229_; lean_object* v___x_3231_; 
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
v_head_3229_ = lean_ctor_get(v_a_3224_, 0);
lean_inc(v_head_3229_);
lean_dec_ref(v_a_3224_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v_head_3229_);
v___x_3231_ = v___x_3226_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_head_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
else
{
lean_dec_ref(v_a_3224_);
lean_del_object(v___x_3226_);
v___y_3164_ = v___y_3158_;
v___y_3165_ = v___y_3159_;
v___y_3166_ = v___y_3160_;
v___y_3167_ = v___y_3161_;
goto v___jp_3163_;
}
}
else
{
lean_del_object(v___x_3226_);
lean_dec(v_a_3224_);
v___y_3164_ = v___y_3158_;
v___y_3165_ = v___y_3159_;
v___y_3166_ = v___y_3160_;
v___y_3167_ = v___y_3161_;
goto v___jp_3163_;
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
v_a_3234_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3223_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3223_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v_mvarId_3157_);
v_a_3267_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3212_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3212_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3277_, lean_object* v_mvarId_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v___x_2563__boxed_3284_; lean_object* v_res_3285_; 
v___x_2563__boxed_3284_ = lean_unbox(v___x_3277_);
v_res_3285_ = l_Lean_MVarId_propext___lam__0(v___x_2563__boxed_3284_, v_mvarId_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
uint8_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___x_3295_; 
v___x_3292_ = 2;
v___x_3293_ = lean_box(v___x_3292_);
lean_inc(v_mvarId_3286_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3294_, 0, v___x_3293_);
lean_closure_set(v___f_3294_, 1, v_mvarId_3286_);
v___x_3295_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3294_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3307_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3307_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3307_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
if (lean_obj_tag(v_a_3296_) == 0)
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v_mvarId_3286_);
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_mvarId_3286_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
else
{
lean_object* v_val_3303_; lean_object* v___x_3305_; 
lean_dec(v_mvarId_3286_);
v_val_3303_ = lean_ctor_get(v_a_3296_, 0);
lean_inc(v_val_3303_);
lean_dec_ref(v_a_3296_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v_val_3303_);
v___x_3305_ = v___x_3298_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v_mvarId_3286_);
v_a_3308_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3295_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3295_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_MVarId_propext(v_mvarId_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
return v_res_3322_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3323_; uint64_t v___x_3324_; 
v___x_3323_ = 2;
v___x_3324_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3331_, lean_object* v___x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
lean_inc(v_mvarId_3331_);
v___x_3338_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3331_, v___x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; uint8_t v_foApprox_3340_; uint8_t v_ctxApprox_3341_; uint8_t v_quasiPatternApprox_3342_; uint8_t v_constApprox_3343_; uint8_t v_isDefEqStuckEx_3344_; uint8_t v_unificationHints_3345_; uint8_t v_proofIrrelevance_3346_; uint8_t v_assignSyntheticOpaque_3347_; uint8_t v_offsetCnstrs_3348_; uint8_t v_etaStruct_3349_; uint8_t v_univApprox_3350_; uint8_t v_iota_3351_; uint8_t v_beta_3352_; uint8_t v_proj_3353_; uint8_t v_zeta_3354_; uint8_t v_zetaDelta_3355_; uint8_t v_zetaUnused_3356_; uint8_t v_zetaHave_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v___x_3338_);
v___x_3339_ = l_Lean_Meta_Context_config(v___y_3333_);
v_foApprox_3340_ = lean_ctor_get_uint8(v___x_3339_, 0);
v_ctxApprox_3341_ = lean_ctor_get_uint8(v___x_3339_, 1);
v_quasiPatternApprox_3342_ = lean_ctor_get_uint8(v___x_3339_, 2);
v_constApprox_3343_ = lean_ctor_get_uint8(v___x_3339_, 3);
v_isDefEqStuckEx_3344_ = lean_ctor_get_uint8(v___x_3339_, 4);
v_unificationHints_3345_ = lean_ctor_get_uint8(v___x_3339_, 5);
v_proofIrrelevance_3346_ = lean_ctor_get_uint8(v___x_3339_, 6);
v_assignSyntheticOpaque_3347_ = lean_ctor_get_uint8(v___x_3339_, 7);
v_offsetCnstrs_3348_ = lean_ctor_get_uint8(v___x_3339_, 8);
v_etaStruct_3349_ = lean_ctor_get_uint8(v___x_3339_, 10);
v_univApprox_3350_ = lean_ctor_get_uint8(v___x_3339_, 11);
v_iota_3351_ = lean_ctor_get_uint8(v___x_3339_, 12);
v_beta_3352_ = lean_ctor_get_uint8(v___x_3339_, 13);
v_proj_3353_ = lean_ctor_get_uint8(v___x_3339_, 14);
v_zeta_3354_ = lean_ctor_get_uint8(v___x_3339_, 15);
v_zetaDelta_3355_ = lean_ctor_get_uint8(v___x_3339_, 16);
v_zetaUnused_3356_ = lean_ctor_get_uint8(v___x_3339_, 17);
v_zetaHave_3357_ = lean_ctor_get_uint8(v___x_3339_, 18);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3359_ = v___x_3339_;
v_isShared_3360_ = v_isSharedCheck_3427_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3339_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3427_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v_trackZetaDelta_3361_; lean_object* v_zetaDeltaSet_3362_; lean_object* v_lctx_3363_; lean_object* v_localInstances_3364_; lean_object* v_defEqCtx_x3f_3365_; lean_object* v_synthPendingDepth_3366_; lean_object* v_canUnfold_x3f_3367_; uint8_t v_univApprox_3368_; uint8_t v_inTypeClassResolution_3369_; uint8_t v_cacheInferType_3370_; uint8_t v___x_3371_; lean_object* v_config_3373_; 
v_trackZetaDelta_3361_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*7);
v_zetaDeltaSet_3362_ = lean_ctor_get(v___y_3333_, 1);
v_lctx_3363_ = lean_ctor_get(v___y_3333_, 2);
v_localInstances_3364_ = lean_ctor_get(v___y_3333_, 3);
v_defEqCtx_x3f_3365_ = lean_ctor_get(v___y_3333_, 4);
v_synthPendingDepth_3366_ = lean_ctor_get(v___y_3333_, 5);
v_canUnfold_x3f_3367_ = lean_ctor_get(v___y_3333_, 6);
v_univApprox_3368_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3369_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*7 + 2);
v_cacheInferType_3370_ = lean_ctor_get_uint8(v___y_3333_, sizeof(void*)*7 + 3);
v___x_3371_ = 2;
if (v_isShared_3360_ == 0)
{
v_config_3373_ = v___x_3359_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 0, v_foApprox_3340_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 1, v_ctxApprox_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 2, v_quasiPatternApprox_3342_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 3, v_constApprox_3343_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 4, v_isDefEqStuckEx_3344_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 5, v_unificationHints_3345_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 6, v_proofIrrelevance_3346_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 7, v_assignSyntheticOpaque_3347_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 8, v_offsetCnstrs_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 10, v_etaStruct_3349_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 11, v_univApprox_3350_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 12, v_iota_3351_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 13, v_beta_3352_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 14, v_proj_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 15, v_zeta_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 16, v_zetaDelta_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 17, v_zetaUnused_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, 18, v_zetaHave_3357_);
v_config_3373_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
uint64_t v___x_3374_; uint64_t v___x_3375_; uint64_t v___x_3376_; uint64_t v___x_3377_; uint64_t v___x_3378_; uint64_t v_key_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_ctor_set_uint8(v_config_3373_, 9, v___x_3371_);
v___x_3374_ = l_Lean_Meta_Context_configKey(v___y_3333_);
v___x_3375_ = 2ULL;
v___x_3376_ = lean_uint64_shift_right(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_uint64_shift_left(v___x_3376_, v___x_3375_);
v___x_3378_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3379_ = lean_uint64_lor(v___x_3377_, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3380_, 0, v_config_3373_);
lean_ctor_set_uint64(v___x_3380_, sizeof(void*)*1, v_key_3379_);
lean_inc(v_canUnfold_x3f_3367_);
lean_inc(v_synthPendingDepth_3366_);
lean_inc(v_defEqCtx_x3f_3365_);
lean_inc_ref(v_localInstances_3364_);
lean_inc_ref(v_lctx_3363_);
lean_inc(v_zetaDeltaSet_3362_);
v___x_3381_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v_zetaDeltaSet_3362_);
lean_ctor_set(v___x_3381_, 2, v_lctx_3363_);
lean_ctor_set(v___x_3381_, 3, v_localInstances_3364_);
lean_ctor_set(v___x_3381_, 4, v_defEqCtx_x3f_3365_);
lean_ctor_set(v___x_3381_, 5, v_synthPendingDepth_3366_);
lean_ctor_set(v___x_3381_, 6, v_canUnfold_x3f_3367_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*7, v_trackZetaDelta_3361_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*7 + 1, v_univApprox_3368_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3369_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*7 + 3, v_cacheInferType_3370_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc(v_mvarId_3331_);
v___x_3382_ = l_Lean_MVarId_getType_x27(v_mvarId_3331_, v___x_3381_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3385_ = lean_unsigned_to_nat(4u);
v___x_3386_ = l_Lean_Expr_isAppOfArity(v_a_3383_, v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v_a_3383_);
lean_dec(v_mvarId_3331_);
v___x_3387_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3388_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3387_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v___x_3388_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3389_ = l_Lean_Expr_appFn_x21(v_a_3383_);
v___x_3390_ = l_Lean_Expr_appFn_x21(v___x_3389_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = l_Lean_Expr_appArg_x21(v___x_3390_);
lean_dec_ref(v___x_3390_);
v___x_3392_ = l_Lean_Expr_appArg_x21(v_a_3383_);
lean_dec(v_a_3383_);
v___x_3393_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3394_ = lean_unsigned_to_nat(2u);
v___x_3395_ = lean_mk_empty_array_with_capacity(v___x_3394_);
v___x_3396_ = lean_array_push(v___x_3395_, v___x_3391_);
v___x_3397_ = lean_array_push(v___x_3396_, v___x_3392_);
lean_inc(v___y_3334_);
v___x_3398_ = l_Lean_Meta_mkAppM(v___x_3393_, v___x_3397_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3408_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3331_, v_a_3399_, v___y_3334_);
lean_dec(v___y_3334_);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v___x_3400_, 0);
lean_dec(v_unused_3409_);
v___x_3402_ = v___x_3400_;
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v___x_3400_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_box(v___x_3386_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v___y_3334_);
lean_dec(v_mvarId_3331_);
v_a_3410_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3398_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3398_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v_mvarId_3331_);
v_a_3418_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3382_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3382_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v_mvarId_3331_);
v_a_3428_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3338_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3338_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3436_, lean_object* v___x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3436_, v___x_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3464_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3464_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3464_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
if (lean_obj_tag(v_a_3451_) == 0)
{
uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3455_ = 0;
v___x_3456_ = lean_box(v___x_3455_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3456_);
v___x_3458_ = v___x_3453_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
else
{
lean_object* v_val_3460_; lean_object* v___x_3462_; 
v_val_3460_ = lean_ctor_get(v_a_3451_, 0);
lean_inc(v_val_3460_);
lean_dec_ref(v_a_3451_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v_val_3460_);
v___x_3462_ = v___x_3453_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_val_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
v_a_3465_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3450_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3450_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; 
v___x_3489_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3483_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3490_, 0, v_mvarId_3483_);
lean_closure_set(v___f_3490_, 1, v___x_3489_);
v___f_3491_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3491_, 0, v___f_3490_);
v___x_3492_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3483_, v___f_3491_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3504_, lean_object* v___x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
lean_inc(v_mvarId_3504_);
v___x_3511_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3504_, v___x_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v___x_3512_; uint8_t v_foApprox_3513_; uint8_t v_ctxApprox_3514_; uint8_t v_quasiPatternApprox_3515_; uint8_t v_constApprox_3516_; uint8_t v_isDefEqStuckEx_3517_; uint8_t v_unificationHints_3518_; uint8_t v_proofIrrelevance_3519_; uint8_t v_assignSyntheticOpaque_3520_; uint8_t v_offsetCnstrs_3521_; uint8_t v_etaStruct_3522_; uint8_t v_univApprox_3523_; uint8_t v_iota_3524_; uint8_t v_beta_3525_; uint8_t v_proj_3526_; uint8_t v_zeta_3527_; uint8_t v_zetaDelta_3528_; uint8_t v_zetaUnused_3529_; uint8_t v_zetaHave_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v___x_3511_);
v___x_3512_ = l_Lean_Meta_Context_config(v___y_3506_);
v_foApprox_3513_ = lean_ctor_get_uint8(v___x_3512_, 0);
v_ctxApprox_3514_ = lean_ctor_get_uint8(v___x_3512_, 1);
v_quasiPatternApprox_3515_ = lean_ctor_get_uint8(v___x_3512_, 2);
v_constApprox_3516_ = lean_ctor_get_uint8(v___x_3512_, 3);
v_isDefEqStuckEx_3517_ = lean_ctor_get_uint8(v___x_3512_, 4);
v_unificationHints_3518_ = lean_ctor_get_uint8(v___x_3512_, 5);
v_proofIrrelevance_3519_ = lean_ctor_get_uint8(v___x_3512_, 6);
v_assignSyntheticOpaque_3520_ = lean_ctor_get_uint8(v___x_3512_, 7);
v_offsetCnstrs_3521_ = lean_ctor_get_uint8(v___x_3512_, 8);
v_etaStruct_3522_ = lean_ctor_get_uint8(v___x_3512_, 10);
v_univApprox_3523_ = lean_ctor_get_uint8(v___x_3512_, 11);
v_iota_3524_ = lean_ctor_get_uint8(v___x_3512_, 12);
v_beta_3525_ = lean_ctor_get_uint8(v___x_3512_, 13);
v_proj_3526_ = lean_ctor_get_uint8(v___x_3512_, 14);
v_zeta_3527_ = lean_ctor_get_uint8(v___x_3512_, 15);
v_zetaDelta_3528_ = lean_ctor_get_uint8(v___x_3512_, 16);
v_zetaUnused_3529_ = lean_ctor_get_uint8(v___x_3512_, 17);
v_zetaHave_3530_ = lean_ctor_get_uint8(v___x_3512_, 18);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3532_ = v___x_3512_;
v_isShared_3533_ = v_isSharedCheck_3599_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v___x_3512_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3599_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
uint8_t v_trackZetaDelta_3534_; lean_object* v_zetaDeltaSet_3535_; lean_object* v_lctx_3536_; lean_object* v_localInstances_3537_; lean_object* v_defEqCtx_x3f_3538_; lean_object* v_synthPendingDepth_3539_; lean_object* v_canUnfold_x3f_3540_; uint8_t v_univApprox_3541_; uint8_t v_inTypeClassResolution_3542_; uint8_t v_cacheInferType_3543_; uint8_t v___x_3544_; lean_object* v_config_3546_; 
v_trackZetaDelta_3534_ = lean_ctor_get_uint8(v___y_3506_, sizeof(void*)*7);
v_zetaDeltaSet_3535_ = lean_ctor_get(v___y_3506_, 1);
v_lctx_3536_ = lean_ctor_get(v___y_3506_, 2);
v_localInstances_3537_ = lean_ctor_get(v___y_3506_, 3);
v_defEqCtx_x3f_3538_ = lean_ctor_get(v___y_3506_, 4);
v_synthPendingDepth_3539_ = lean_ctor_get(v___y_3506_, 5);
v_canUnfold_x3f_3540_ = lean_ctor_get(v___y_3506_, 6);
v_univApprox_3541_ = lean_ctor_get_uint8(v___y_3506_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3542_ = lean_ctor_get_uint8(v___y_3506_, sizeof(void*)*7 + 2);
v_cacheInferType_3543_ = lean_ctor_get_uint8(v___y_3506_, sizeof(void*)*7 + 3);
v___x_3544_ = 2;
if (v_isShared_3533_ == 0)
{
v_config_3546_ = v___x_3532_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 0, v_foApprox_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 1, v_ctxApprox_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 2, v_quasiPatternApprox_3515_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 3, v_constApprox_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 4, v_isDefEqStuckEx_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 5, v_unificationHints_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 6, v_proofIrrelevance_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 7, v_assignSyntheticOpaque_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 8, v_offsetCnstrs_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 10, v_etaStruct_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 11, v_univApprox_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 12, v_iota_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 13, v_beta_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 14, v_proj_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 15, v_zeta_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 16, v_zetaDelta_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 17, v_zetaUnused_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, 18, v_zetaHave_3530_);
v_config_3546_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
uint64_t v___x_3547_; uint64_t v___x_3548_; uint64_t v___x_3549_; uint64_t v___x_3550_; uint64_t v___x_3551_; uint64_t v_key_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_ctor_set_uint8(v_config_3546_, 9, v___x_3544_);
v___x_3547_ = l_Lean_Meta_Context_configKey(v___y_3506_);
v___x_3548_ = 2ULL;
v___x_3549_ = lean_uint64_shift_right(v___x_3547_, v___x_3548_);
v___x_3550_ = lean_uint64_shift_left(v___x_3549_, v___x_3548_);
v___x_3551_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3552_ = lean_uint64_lor(v___x_3550_, v___x_3551_);
v___x_3553_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3553_, 0, v_config_3546_);
lean_ctor_set_uint64(v___x_3553_, sizeof(void*)*1, v_key_3552_);
lean_inc(v_canUnfold_x3f_3540_);
lean_inc(v_synthPendingDepth_3539_);
lean_inc(v_defEqCtx_x3f_3538_);
lean_inc_ref(v_localInstances_3537_);
lean_inc_ref(v_lctx_3536_);
lean_inc(v_zetaDeltaSet_3535_);
v___x_3554_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
lean_ctor_set(v___x_3554_, 1, v_zetaDeltaSet_3535_);
lean_ctor_set(v___x_3554_, 2, v_lctx_3536_);
lean_ctor_set(v___x_3554_, 3, v_localInstances_3537_);
lean_ctor_set(v___x_3554_, 4, v_defEqCtx_x3f_3538_);
lean_ctor_set(v___x_3554_, 5, v_synthPendingDepth_3539_);
lean_ctor_set(v___x_3554_, 6, v_canUnfold_x3f_3540_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*7, v_trackZetaDelta_3534_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*7 + 1, v_univApprox_3541_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3542_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*7 + 3, v_cacheInferType_3543_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc(v_mvarId_3504_);
v___x_3555_ = l_Lean_MVarId_getType_x27(v_mvarId_3504_, v___x_3554_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3558_ = lean_unsigned_to_nat(3u);
v___x_3559_ = l_Lean_Expr_isAppOfArity(v_a_3556_, v___x_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v_a_3556_);
lean_dec(v_mvarId_3504_);
v___x_3560_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3561_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3560_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3562_ = l_Lean_Expr_appFn_x21(v_a_3556_);
v___x_3563_ = l_Lean_Expr_appArg_x21(v___x_3562_);
lean_dec_ref(v___x_3562_);
v___x_3564_ = l_Lean_Expr_appArg_x21(v_a_3556_);
lean_dec(v_a_3556_);
v___x_3565_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3566_ = lean_unsigned_to_nat(2u);
v___x_3567_ = lean_mk_empty_array_with_capacity(v___x_3566_);
v___x_3568_ = lean_array_push(v___x_3567_, v___x_3563_);
v___x_3569_ = lean_array_push(v___x_3568_, v___x_3564_);
lean_inc(v___y_3507_);
v___x_3570_ = l_Lean_Meta_mkAppM(v___x_3565_, v___x_3569_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3580_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3504_, v_a_3571_, v___y_3507_);
lean_dec(v___y_3507_);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3581_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3576_ = lean_box(v___x_3559_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3578_ = v___x_3574_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v___y_3507_);
lean_dec(v_mvarId_3504_);
v_a_3582_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3570_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3570_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v_mvarId_3504_);
v_a_3590_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3555_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3555_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v_mvarId_3504_);
v_a_3600_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3511_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3511_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3608_, lean_object* v___x_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3608_, v___x_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; 
v___x_3625_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3619_);
v___f_3626_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3626_, 0, v_mvarId_3619_);
lean_closure_set(v___f_3626_, 1, v___x_3625_);
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3627_, 0, v___f_3626_);
v___x_3628_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3619_, v___f_3627_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
return v_res_3635_;
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
