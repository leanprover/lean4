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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
v___x_148_ = 2ULL;
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
lean_dec_ref(v___x_156_);
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
lean_dec_ref(v___x_254_);
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
lean_dec_ref(v_term_x3f_217_);
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
lean_dec_ref(v___x_517_);
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
lean_dec_ref(v___x_517_);
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
lean_dec_ref(v___y_455_);
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
lean_dec_ref(v_fst_459_);
lean_inc(v_a_432_);
v___x_470_ = l_Lean_Meta_isExprDefEq(v_a_432_, v_val_469_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref(v___x_470_);
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
lean_dec_ref(v___x_474_);
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
lean_dec_ref(v___y_455_);
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
lean_dec_ref(v_fst_580_);
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
lean_dec_ref(v_fst_580_);
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
lean_dec_ref(v_fst_580_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; 
v___x_633_ = ((size_t)5ULL);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_shift_left(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_638_ = lean_usize_sub(v___x_637_, v___x_636_);
return v___x_638_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_639_, size_t v_x_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_object* v_es_642_; lean_object* v___x_643_; size_t v___x_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v_j_647_; lean_object* v___x_648_; 
v_es_642_ = lean_ctor_get(v_x_639_, 0);
v___x_643_ = lean_box(2);
v___x_644_ = ((size_t)5ULL);
v___x_645_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_646_ = lean_usize_land(v_x_640_, v___x_645_);
v_j_647_ = lean_usize_to_nat(v___x_646_);
v___x_648_ = lean_array_get_borrowed(v___x_643_, v_es_642_, v_j_647_);
lean_dec(v_j_647_);
switch(lean_obj_tag(v___x_648_))
{
case 0:
{
lean_object* v_key_649_; uint8_t v___x_650_; 
v_key_649_ = lean_ctor_get(v___x_648_, 0);
v___x_650_ = l_Lean_instBEqMVarId_beq(v_x_641_, v_key_649_);
return v___x_650_;
}
case 1:
{
lean_object* v_node_651_; size_t v___x_652_; 
v_node_651_ = lean_ctor_get(v___x_648_, 0);
v___x_652_ = lean_usize_shift_right(v_x_640_, v___x_644_);
v_x_639_ = v_node_651_;
v_x_640_ = v___x_652_;
goto _start;
}
default: 
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
}
else
{
lean_object* v_ks_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_ks_655_ = lean_ctor_get(v_x_639_, 0);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_655_, v___x_656_, v_x_641_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_2678__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v_x_2678__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_658_, v_x_2678__boxed_661_, v_x_660_);
lean_dec(v_x_660_);
lean_dec_ref(v_x_658_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint64_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Lean_instHashableMVarId_hash(v_x_665_);
v___x_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_664_, v___x_667_, v_x_665_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec_ref(v_x_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; lean_object* v_mctx_677_; lean_object* v_eAssignment_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_st_ref_get(v___y_674_);
v_mctx_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_mctx_677_);
lean_dec(v___x_676_);
v_eAssignment_678_ = lean_ctor_get(v_mctx_677_, 8);
lean_inc_ref(v_eAssignment_678_);
lean_dec_ref(v_mctx_677_);
v___x_679_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_678_, v_mvarId_673_);
lean_dec_ref(v_eAssignment_678_);
v___x_680_ = lean_box(v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec(v_mvarId_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_686_, lean_object* v_as_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_a_697_; uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v_b_690_);
return v___x_702_;
}
else
{
lean_object* v_snd_703_; lean_object* v_fst_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_754_; 
v_snd_703_ = lean_ctor_get(v_b_690_, 1);
v_fst_704_ = lean_ctor_get(v_b_690_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_754_ == 0)
{
v___x_706_ = v_b_690_;
v_isShared_707_ = v_isSharedCheck_754_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_703_);
lean_inc(v_fst_704_);
lean_dec(v_b_690_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_754_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_array_708_; lean_object* v_start_709_; lean_object* v_stop_710_; uint8_t v___x_711_; 
v_array_708_ = lean_ctor_get(v_snd_703_, 0);
v_start_709_ = lean_ctor_get(v_snd_703_, 1);
v_stop_710_ = lean_ctor_get(v_snd_703_, 2);
v___x_711_ = lean_nat_dec_lt(v_start_709_, v_stop_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
if (v_isShared_707_ == 0)
{
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_snd_703_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_stop_710_);
lean_inc(v_start_709_);
lean_inc_ref(v_array_708_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_snd_703_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_751_ = lean_ctor_get(v_snd_703_, 2);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_snd_703_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_snd_703_, 0);
lean_dec(v_unused_753_);
v___x_717_ = v_snd_703_;
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_snd_703_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_719_ = lean_array_fget(v_array_708_, v_start_709_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_start_709_, v___x_720_);
lean_dec(v_start_709_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_721_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_array_708_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_stop_710_);
v___x_723_ = v_reuseFailAlloc_749_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unbox(v___x_719_);
lean_dec(v___x_719_);
v___x_725_ = l_Lean_BinderInfo_isInstImplicit(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_723_);
v___x_727_ = v___x_706_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_723_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_a_697_ = v___x_727_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_array_uget_borrowed(v_as_687_, v_i_689_);
v___x_730_ = l_Lean_Expr_mvarId_x21(v_a_729_);
v___x_731_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_730_, v___y_692_);
lean_dec(v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
if (v_synthAssignedInstances_686_ == 0)
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_740_ == 0)
{
if (v___x_725_ == 0)
{
goto v___jp_733_;
}
else
{
lean_del_object(v___x_706_);
goto v___jp_737_;
}
}
else
{
goto v___jp_733_;
}
}
else
{
lean_dec(v_a_732_);
lean_del_object(v___x_706_);
goto v___jp_737_;
}
v___jp_733_:
{
lean_object* v___x_735_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_723_);
v___x_735_ = v___x_706_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_723_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_a_697_ = v___x_735_;
goto v___jp_696_;
}
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc(v_a_729_);
v___x_738_ = lean_array_push(v_fst_704_, v_a_729_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_723_);
v_a_697_ = v___x_739_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v___x_723_);
lean_del_object(v___x_706_);
lean_dec(v_fst_704_);
v_a_741_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_731_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
}
}
}
v___jp_696_:
{
size_t v___x_698_; size_t v___x_699_; 
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_689_, v___x_698_);
v_i_689_ = v___x_699_;
v_b_690_ = v_a_697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_755_, lean_object* v_as_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_765_; size_t v_sz_boxed_766_; size_t v_i_boxed_767_; lean_object* v_res_768_; 
v_synthAssignedInstances_boxed_765_ = lean_unbox(v_synthAssignedInstances_755_);
v_sz_boxed_766_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_767_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_765_, v_as_756_, v_sz_boxed_766_, v_i_boxed_767_, v_b_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_as_756_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_769_, lean_object* v_mvarId_770_, uint8_t v_allowSynthFailures_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_array_get_size(v_b_772_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_nat_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_inc(v_mvarId_770_);
lean_inc(v_tacticName_769_);
v___x_781_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_769_, v_mvarId_770_, v_allowSynthFailures_771_, v_b_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_b_772_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v_b_772_ = v_a_782_;
goto _start;
}
else
{
lean_dec(v_mvarId_770_);
lean_dec(v_tacticName_769_);
return v___x_781_;
}
}
else
{
lean_object* v___x_784_; 
lean_dec(v_mvarId_770_);
lean_dec(v_tacticName_769_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_b_772_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_785_, lean_object* v_mvarId_786_, lean_object* v_allowSynthFailures_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_allowSynthFailures_boxed_794_; lean_object* v_res_795_; 
v_allowSynthFailures_boxed_794_ = lean_unbox(v_allowSynthFailures_787_);
v_res_795_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_785_, v_mvarId_786_, v_allowSynthFailures_boxed_794_, v_b_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_796_, lean_object* v_mvarId_797_, lean_object* v_mvarsNew_798_, lean_object* v_binderInfos_799_, uint8_t v_synthAssignedInstances_800_, uint8_t v_allowSynthFailures_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; lean_object* v_todo_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; size_t v_sz_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v_todo_808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_809_ = lean_array_get_size(v_binderInfos_799_);
v___x_810_ = l_Array_toSubarray___redArg(v_binderInfos_799_, v___x_807_, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_todo_808_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v_sz_812_ = lean_array_size(v_mvarsNew_798_);
v___x_813_ = ((size_t)0ULL);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_800_, v_mvarsNew_798_, v_sz_812_, v___x_813_, v___x_811_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v_fst_816_; lean_object* v___x_817_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_fst_816_);
lean_dec(v_a_815_);
v___x_817_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_796_, v_mvarId_797_, v_allowSynthFailures_801_, v_fst_816_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_817_, 0);
lean_dec(v_unused_826_);
v___x_819_ = v___x_817_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_dec(v___x_817_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_817_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_mvarId_797_);
lean_dec(v_tacticName_796_);
v_a_835_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_814_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_814_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_843_, lean_object* v_mvarId_844_, lean_object* v_mvarsNew_845_, lean_object* v_binderInfos_846_, lean_object* v_synthAssignedInstances_847_, lean_object* v_allowSynthFailures_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_854_; uint8_t v_allowSynthFailures_boxed_855_; lean_object* v_res_856_; 
v_synthAssignedInstances_boxed_854_ = lean_unbox(v_synthAssignedInstances_847_);
v_allowSynthFailures_boxed_855_ = lean_unbox(v_allowSynthFailures_848_);
v_res_856_ = l_Lean_Meta_synthAppInstances(v_tacticName_843_, v_mvarId_844_, v_mvarsNew_845_, v_binderInfos_846_, v_synthAssignedInstances_boxed_854_, v_allowSynthFailures_boxed_855_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec_ref(v_mvarsNew_845_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_857_, v___y_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v_mvarId_864_);
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec(v_x_877_);
lean_dec_ref(v_x_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, size_t v_x_882_, lean_object* v_x_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_2998__boxed_889_; uint8_t v_res_890_; lean_object* v_r_891_; 
v_x_2998__boxed_889_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_res_890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_885_, v_x_886_, v_x_2998__boxed_889_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_886_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_heq_895_, lean_object* v_i_896_, lean_object* v_k_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_893_, v_i_896_, v_k_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_k_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_899_, v_keys_900_, v_vals_901_, v_heq_902_, v_i_903_, v_k_904_);
lean_dec(v_k_904_);
lean_dec_ref(v_vals_901_);
lean_dec_ref(v_keys_900_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_907_, lean_object* v_binderInfos_908_, lean_object* v_a_909_, lean_object* v_n_910_, lean_object* v_i_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_zero_917_; uint8_t v_isZero_918_; 
v_zero_917_ = lean_unsigned_to_nat(0u);
v_isZero_918_ = lean_nat_dec_eq(v_i_911_, v_zero_917_);
if (v_isZero_918_ == 1)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_i_911_);
lean_dec(v_a_909_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v_one_921_; lean_object* v_n_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_a_928_; uint8_t v___x_929_; 
v_one_921_ = lean_unsigned_to_nat(1u);
v_n_922_ = lean_nat_sub(v_i_911_, v_one_921_);
lean_dec(v_i_911_);
v___x_923_ = lean_nat_sub(v_n_910_, v_n_922_);
v___x_924_ = lean_nat_sub(v___x_923_, v_one_921_);
lean_dec(v___x_923_);
v___x_925_ = lean_array_fget_borrowed(v_newMVars_907_, v___x_924_);
v___x_926_ = l_Lean_Expr_mvarId_x21(v___x_925_);
v___x_927_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_926_, v___y_913_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
if (v___x_929_ == 0)
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_930_ = 0;
v___x_931_ = lean_box(v___x_930_);
v___x_932_ = lean_array_get(v___x_931_, v_binderInfos_908_, v___x_924_);
lean_dec(v___x_924_);
lean_dec(v___x_931_);
v___x_933_ = lean_unbox(v___x_932_);
lean_dec(v___x_932_);
v___x_934_ = l_Lean_BinderInfo_isInstImplicit(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_inc(v___x_926_);
v___x_935_ = l_Lean_MVarId_getTag(v___x_926_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
lean_inc(v_a_909_);
v___x_937_ = l_Lean_Meta_appendTag(v_a_909_, v_a_936_);
v___x_938_ = l_Lean_MVarId_setTag___redArg(v___x_926_, v___x_937_, v___y_913_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref(v___x_938_);
v_i_911_ = v_n_922_;
goto _start;
}
else
{
lean_dec(v_n_922_);
lean_dec(v_a_909_);
return v___x_938_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_926_);
lean_dec(v_n_922_);
lean_dec(v_a_909_);
v_a_940_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_935_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_dec(v___x_926_);
v_i_911_ = v_n_922_;
goto _start;
}
}
else
{
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_i_911_ = v_n_922_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_950_, lean_object* v_binderInfos_951_, lean_object* v_a_952_, lean_object* v_n_953_, lean_object* v_i_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_950_, v_binderInfos_951_, v_a_952_, v_n_953_, v_i_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_n_953_);
lean_dec_ref(v_binderInfos_951_);
lean_dec_ref(v_newMVars_950_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_961_, lean_object* v_newMVars_962_, lean_object* v_binderInfos_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_MVarId_getTag(v_mvarId_961_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_988_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_988_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_988_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_988_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_array_get_size(v_newMVars_962_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; 
v___x_977_ = l_Lean_Name_isAnonymous(v_a_970_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_del_object(v___x_972_);
v___x_978_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_962_, v_binderInfos_963_, v_a_970_, v___x_974_, v___x_974_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_a_970_);
v___x_979_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_979_);
v___x_981_ = v___x_972_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_del_object(v___x_972_);
v___x_983_ = l_Lean_instInhabitedExpr;
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_borrowed(v___x_983_, v_newMVars_962_, v___x_984_);
v___x_986_ = l_Lean_Expr_mvarId_x21(v___x_985_);
v___x_987_ = l_Lean_MVarId_setTag___redArg(v___x_986_, v_a_970_, v_a_965_);
return v___x_987_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_969_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_969_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_997_, lean_object* v_newMVars_998_, lean_object* v_binderInfos_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_appendParentTag(v_mvarId_997_, v_newMVars_998_, v_binderInfos_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_binderInfos_999_);
lean_dec_ref(v_newMVars_998_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1006_, lean_object* v_binderInfos_1007_, lean_object* v_a_1008_, lean_object* v_n_1009_, lean_object* v_i_1010_, lean_object* v_a_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1006_, v_binderInfos_1007_, v_a_1008_, v_n_1009_, v_i_1010_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1018_, lean_object* v_binderInfos_1019_, lean_object* v_a_1020_, lean_object* v_n_1021_, lean_object* v_i_1022_, lean_object* v_a_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1018_, v_binderInfos_1019_, v_a_1020_, v_n_1021_, v_i_1022_, v_a_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v_n_1021_);
lean_dec_ref(v_binderInfos_1019_);
lean_dec_ref(v_newMVars_1018_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1030_, lean_object* v_mvarId_1031_, lean_object* v_newMVars_1032_, lean_object* v_binderInfos_1033_, uint8_t v_synthAssignedInstances_1034_, uint8_t v_allowSynthFailures_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
lean_inc_ref(v_binderInfos_1033_);
lean_inc(v_mvarId_1031_);
v___x_1041_ = l_Lean_Meta_synthAppInstances(v_tacticName_1030_, v_mvarId_1031_, v_newMVars_1032_, v_binderInfos_1033_, v_synthAssignedInstances_1034_, v_allowSynthFailures_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v___x_1041_);
v___x_1042_ = l_Lean_Meta_appendParentTag(v_mvarId_1031_, v_newMVars_1032_, v_binderInfos_1033_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec_ref(v_binderInfos_1033_);
return v___x_1042_;
}
else
{
lean_dec_ref(v_binderInfos_1033_);
lean_dec(v_mvarId_1031_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1043_, lean_object* v_mvarId_1044_, lean_object* v_newMVars_1045_, lean_object* v_binderInfos_1046_, lean_object* v_synthAssignedInstances_1047_, lean_object* v_allowSynthFailures_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1054_; uint8_t v_allowSynthFailures_boxed_1055_; lean_object* v_res_1056_; 
v_synthAssignedInstances_boxed_1054_ = lean_unbox(v_synthAssignedInstances_1047_);
v_allowSynthFailures_boxed_1055_ = lean_unbox(v_allowSynthFailures_1048_);
v_res_1056_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1043_, v_mvarId_1044_, v_newMVars_1045_, v_binderInfos_1046_, v_synthAssignedInstances_boxed_1054_, v_allowSynthFailures_boxed_1055_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_newMVars_1045_);
return v_res_1056_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1057_, lean_object* v_mvarId_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_Expr_mvarId_x21(v_mvar_1057_);
v___x_1060_ = l_Lean_instBEqMVarId_beq(v_mvarId_1058_, v___x_1059_);
lean_dec(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1061_, lean_object* v_mvarId_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1061_, v_mvarId_1062_);
lean_dec(v_mvarId_1062_);
lean_dec_ref(v_mvar_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1065_, lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v_a_1077_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1075_ = 1;
v___x_1083_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
v___x_1084_ = lean_expr_eqv(v_mvar_1065_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___x_1083_);
v___x_1085_ = lean_infer_type(v___x_1083_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1097_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_inc_ref(v_mvar_1065_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1090_, 0, v_mvar_1065_);
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Lean_FindMVar_main(v___f_1090_, v_a_1086_, v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_del_object(v___x_1088_);
v_a_1077_ = v___x_1084_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec_ref(v___x_1092_);
lean_dec_ref(v_mvar_1065_);
v___x_1093_ = lean_box(v___x_1075_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1093_);
v___x_1095_ = v___x_1088_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_mvar_1065_);
v_a_1098_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1085_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1085_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
v_a_1077_ = v___x_1074_;
goto v___jp_1076_;
}
v___jp_1076_:
{
if (v_a_1077_ == 0)
{
size_t v___x_1078_; size_t v___x_1079_; 
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1067_, v___x_1078_);
v_i_1067_ = v___x_1079_;
goto _start;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_mvar_1065_);
v___x_1081_ = lean_box(v___x_1075_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
else
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_mvar_1065_);
v___x_1106_ = 0;
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1109_, lean_object* v_as_1110_, lean_object* v_i_1111_, lean_object* v_stop_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_i_boxed_1118_; size_t v_stop_boxed_1119_; lean_object* v_res_1120_; 
v_i_boxed_1118_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_stop_boxed_1119_ = lean_unbox_usize(v_stop_1112_);
lean_dec(v_stop_1112_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1109_, v_as_1110_, v_i_boxed_1118_, v_stop_boxed_1119_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1110_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1121_, lean_object* v_otherMVars_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_array_get_size(v_otherMVars_1122_);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v_mvar_1121_);
v___x_1131_ = lean_box(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
else
{
if (v___x_1130_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_mvar_1121_);
v___x_1133_ = lean_box(v___x_1130_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1129_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1121_, v_otherMVars_1122_, v___x_1135_, v___x_1136_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1138_, lean_object* v_otherMVars_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1138_, v_otherMVars_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_otherMVars_1139_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1146_, lean_object* v_as_1147_, size_t v_i_1148_, size_t v_stop_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_eq(v_i_1148_, v_stop_1149_);
if (v___x_1156_ == 0)
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1188_; 
v_fst_1157_ = lean_ctor_get(v_b_1150_, 0);
v_snd_1158_ = lean_ctor_get(v_b_1150_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_b_1150_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1160_ = v_b_1150_;
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v_b_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v_currMVarId_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_array_uget_borrowed(v_as_1147_, v_i_1148_);
v_currMVarId_1163_ = l_Lean_Expr_mvarId_x21(v___x_1162_);
lean_inc(v___x_1162_);
v___x_1164_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1162_, v_mvars_1146_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_a_1167_; uint8_t v___x_1171_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v___x_1171_ = lean_unbox(v_a_1165_);
lean_dec(v_a_1165_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_array_push(v_fst_1157_, v_currMVarId_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1172_);
v___x_1174_ = v___x_1160_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_snd_1158_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v_a_1167_ = v___x_1174_;
goto v___jp_1166_;
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_array_push(v_snd_1158_, v_currMVarId_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1176_);
v___x_1178_ = v___x_1160_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fst_1157_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v_a_1167_ = v___x_1178_;
goto v___jp_1166_;
}
}
v___jp_1166_:
{
size_t v___x_1168_; size_t v___x_1169_; 
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1148_, v___x_1168_);
v_i_1148_ = v___x_1169_;
v_b_1150_ = v_a_1167_;
goto _start;
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_currMVarId_1163_);
lean_del_object(v___x_1160_);
lean_dec(v_snd_1158_);
lean_dec(v_fst_1157_);
v_a_1180_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1164_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1164_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_b_1150_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_i_boxed_1200_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1190_, v_as_1191_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v_as_1191_);
lean_dec_ref(v_mvars_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1215_ = lean_array_get_size(v_mvars_1207_);
v___x_1216_ = lean_nat_dec_lt(v___x_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
return v___x_1217_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1215_, v___x_1215_);
if (v___x_1218_ == 0)
{
if (v___x_1216_ == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1214_);
return v___x_1219_;
}
else
{
size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = lean_usize_of_nat(v___x_1215_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1207_, v_mvars_1207_, v___x_1220_, v___x_1221_, v___x_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1222_;
}
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_of_nat(v___x_1215_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1207_, v_mvars_1207_, v___x_1223_, v___x_1224_, v___x_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_mvars_1226_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = l_List_reverse___redArg(v_a_1234_);
return v___x_1235_;
}
else
{
lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1246_; 
v_head_1236_ = lean_ctor_get(v_a_1233_, 0);
v_tail_1237_ = lean_ctor_get(v_a_1233_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1239_ = v_a_1233_;
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_head_1236_);
lean_dec(v_a_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Expr_mvarId_x21(v_head_1236_);
lean_dec(v_head_1236_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_a_1234_);
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1234_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
v_a_1233_ = v_tail_1237_;
v_a_1234_ = v___x_1243_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1247_, uint8_t v_x_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
switch(v_x_1248_)
{
case 0:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1247_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec_ref(v_mvars_1247_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1267_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_a_1255_);
v___x_1261_ = lean_array_to_list(v_fst_1259_);
v___x_1262_ = lean_array_to_list(v_snd_1260_);
v___x_1263_ = l_List_appendTR___redArg(v___x_1261_, v___x_1262_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1263_);
v___x_1265_ = v___x_1257_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1254_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1254_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
case 1:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1247_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec_ref(v_mvars_1247_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1286_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_fst_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v_fst_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_fst_1281_);
lean_dec(v_a_1277_);
v___x_1282_ = lean_array_to_list(v_fst_1281_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
default: 
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = lean_array_to_list(v_mvars_1247_);
v___x_1296_ = lean_box(0);
v___x_1297_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1295_, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1299_, lean_object* v_x_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_x_820__boxed_1306_; lean_object* v_res_1307_; 
v_x_820__boxed_1306_ = lean_unbox(v_x_1300_);
v_res_1307_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1299_, v_x_820__boxed_1306_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (v_approx_1308_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1309_, v_b_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; uint8_t v_constApprox_1318_; uint8_t v_isDefEqStuckEx_1319_; uint8_t v_unificationHints_1320_; uint8_t v_proofIrrelevance_1321_; uint8_t v_assignSyntheticOpaque_1322_; uint8_t v_offsetCnstrs_1323_; uint8_t v_transparency_1324_; uint8_t v_etaStruct_1325_; uint8_t v_univApprox_1326_; uint8_t v_iota_1327_; uint8_t v_beta_1328_; uint8_t v_proj_1329_; uint8_t v_zeta_1330_; uint8_t v_zetaDelta_1331_; uint8_t v_zetaUnused_1332_; uint8_t v_zetaHave_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1354_; 
v___x_1317_ = l_Lean_Meta_Context_config(v_a_1311_);
v_constApprox_1318_ = lean_ctor_get_uint8(v___x_1317_, 3);
v_isDefEqStuckEx_1319_ = lean_ctor_get_uint8(v___x_1317_, 4);
v_unificationHints_1320_ = lean_ctor_get_uint8(v___x_1317_, 5);
v_proofIrrelevance_1321_ = lean_ctor_get_uint8(v___x_1317_, 6);
v_assignSyntheticOpaque_1322_ = lean_ctor_get_uint8(v___x_1317_, 7);
v_offsetCnstrs_1323_ = lean_ctor_get_uint8(v___x_1317_, 8);
v_transparency_1324_ = lean_ctor_get_uint8(v___x_1317_, 9);
v_etaStruct_1325_ = lean_ctor_get_uint8(v___x_1317_, 10);
v_univApprox_1326_ = lean_ctor_get_uint8(v___x_1317_, 11);
v_iota_1327_ = lean_ctor_get_uint8(v___x_1317_, 12);
v_beta_1328_ = lean_ctor_get_uint8(v___x_1317_, 13);
v_proj_1329_ = lean_ctor_get_uint8(v___x_1317_, 14);
v_zeta_1330_ = lean_ctor_get_uint8(v___x_1317_, 15);
v_zetaDelta_1331_ = lean_ctor_get_uint8(v___x_1317_, 16);
v_zetaUnused_1332_ = lean_ctor_get_uint8(v___x_1317_, 17);
v_zetaHave_1333_ = lean_ctor_get_uint8(v___x_1317_, 18);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1335_ = v___x_1317_;
v_isShared_1336_ = v_isSharedCheck_1354_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v___x_1317_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1354_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 3, v_constApprox_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 4, v_isDefEqStuckEx_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 5, v_unificationHints_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 6, v_proofIrrelevance_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 7, v_assignSyntheticOpaque_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 8, v_offsetCnstrs_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 9, v_transparency_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 10, v_etaStruct_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 11, v_univApprox_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 12, v_iota_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 13, v_beta_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 14, v_proj_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 15, v_zeta_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 16, v_zetaDelta_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 17, v_zetaUnused_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 18, v_zetaHave_1333_);
v___x_1338_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
uint8_t v_trackZetaDelta_1339_; lean_object* v_zetaDeltaSet_1340_; lean_object* v_lctx_1341_; lean_object* v_localInstances_1342_; lean_object* v_defEqCtx_x3f_1343_; lean_object* v_synthPendingDepth_1344_; lean_object* v_canUnfold_x3f_1345_; uint8_t v_univApprox_1346_; uint8_t v_inTypeClassResolution_1347_; uint8_t v_cacheInferType_1348_; uint64_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_ctor_set_uint8(v___x_1338_, 0, v_approx_1308_);
lean_ctor_set_uint8(v___x_1338_, 1, v_approx_1308_);
lean_ctor_set_uint8(v___x_1338_, 2, v_approx_1308_);
v_trackZetaDelta_1339_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7);
v_zetaDeltaSet_1340_ = lean_ctor_get(v_a_1311_, 1);
v_lctx_1341_ = lean_ctor_get(v_a_1311_, 2);
v_localInstances_1342_ = lean_ctor_get(v_a_1311_, 3);
v_defEqCtx_x3f_1343_ = lean_ctor_get(v_a_1311_, 4);
v_synthPendingDepth_1344_ = lean_ctor_get(v_a_1311_, 5);
v_canUnfold_x3f_1345_ = lean_ctor_get(v_a_1311_, 6);
v_univApprox_1346_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1347_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 2);
v_cacheInferType_1348_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 3);
v___x_1349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1338_);
v___x_1350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1350_, 0, v___x_1338_);
lean_ctor_set_uint64(v___x_1350_, sizeof(void*)*1, v___x_1349_);
lean_inc(v_canUnfold_x3f_1345_);
lean_inc(v_synthPendingDepth_1344_);
lean_inc(v_defEqCtx_x3f_1343_);
lean_inc_ref(v_localInstances_1342_);
lean_inc_ref(v_lctx_1341_);
lean_inc(v_zetaDeltaSet_1340_);
v___x_1351_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v_zetaDeltaSet_1340_);
lean_ctor_set(v___x_1351_, 2, v_lctx_1341_);
lean_ctor_set(v___x_1351_, 3, v_localInstances_1342_);
lean_ctor_set(v___x_1351_, 4, v_defEqCtx_x3f_1343_);
lean_ctor_set(v___x_1351_, 5, v_synthPendingDepth_1344_);
lean_ctor_set(v___x_1351_, 6, v_canUnfold_x3f_1345_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7, v_trackZetaDelta_1339_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 1, v_univApprox_1346_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1347_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 3, v_cacheInferType_1348_);
v___x_1352_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1309_, v_b_1310_, v___x_1351_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref(v___x_1351_);
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1355_, lean_object* v_a_1356_, lean_object* v_b_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_approx_boxed_1363_; lean_object* v_res_1364_; 
v_approx_boxed_1363_ = lean_unbox(v_approx_1355_);
v_res_1364_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1363_, v_a_1356_, v_b_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1365_, lean_object* v_cfg_1366_, lean_object* v_term_x3f_1367_, lean_object* v_targetType_1368_, lean_object* v_eType_1369_, lean_object* v_rangeNumArgs_1370_, lean_object* v_i_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_lower_1377_; lean_object* v_upper_1378_; uint8_t v___x_1379_; 
v_lower_1377_ = lean_ctor_get(v_rangeNumArgs_1370_, 0);
v_upper_1378_ = lean_ctor_get(v_rangeNumArgs_1370_, 1);
v___x_1379_ = lean_nat_dec_lt(v_i_1371_, v_upper_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
lean_dec(v_i_1371_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_nat_dec_eq(v_lower_1377_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
lean_inc(v_lower_1377_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_lower_1377_);
v___x_1383_ = 0;
lean_inc_ref(v_eType_1369_);
v___x_1384_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1369_, v___x_1382_, v___x_1383_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v_snd_1386_; lean_object* v_snd_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v_snd_1386_ = lean_ctor_get(v_a_1385_, 1);
lean_inc(v_snd_1386_);
lean_dec(v_a_1385_);
v_snd_1387_ = lean_ctor_get(v_snd_1386_, 1);
lean_inc(v_snd_1387_);
lean_dec(v_snd_1386_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_snd_1387_);
v___x_1389_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1365_, v_eType_1369_, v___x_1388_, v_targetType_1368_, v_term_x3f_1367_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
v_a_1390_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1384_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1384_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1365_, v_eType_1369_, v___x_1398_, v_targetType_1368_, v_term_x3f_1367_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
return v___x_1399_;
}
}
else
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_saveState___redArg(v_a_1373_, v_a_1375_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
lean_inc(v_i_1371_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_i_1371_);
v___x_1403_ = 0;
lean_inc_ref(v_eType_1369_);
v___x_1404_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1369_, v___x_1402_, v___x_1403_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_snd_1406_; lean_object* v_fst_1407_; lean_object* v_fst_1408_; lean_object* v_snd_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1447_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v_snd_1406_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1406_);
v_fst_1407_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1407_);
lean_dec(v_a_1405_);
v_fst_1408_ = lean_ctor_get(v_snd_1406_, 0);
v_snd_1409_ = lean_ctor_get(v_snd_1406_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_snd_1406_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1411_ = v_snd_1406_;
v_isShared_1412_ = v_isSharedCheck_1447_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_snd_1409_);
lean_inc(v_fst_1408_);
lean_dec(v_snd_1406_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1447_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
uint8_t v_approx_1413_; lean_object* v___x_1414_; 
v_approx_1413_ = lean_ctor_get_uint8(v_cfg_1366_, 3);
lean_inc_ref(v_targetType_1368_);
v___x_1414_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1413_, v_snd_1409_, v_targetType_1368_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1438_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1438_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1438_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_unbox(v_a_1415_);
lean_dec(v_a_1415_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_del_object(v___x_1417_);
lean_del_object(v___x_1411_);
lean_dec(v_fst_1408_);
lean_dec(v_fst_1407_);
v___x_1420_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1401_, v_a_1373_, v_a_1375_);
lean_dec(v_a_1401_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v___x_1420_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_i_1371_, v___x_1421_);
lean_dec(v_i_1371_);
v_i_1371_ = v___x_1422_;
goto _start;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_i_1371_);
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
v_a_1424_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1420_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_a_1401_);
lean_dec(v_i_1371_);
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v_fst_1408_);
lean_ctor_set(v___x_1411_, 0, v_fst_1407_);
v___x_1433_ = v___x_1411_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_fst_1407_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_fst_1408_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1433_);
v___x_1435_ = v___x_1417_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1411_);
lean_dec(v_fst_1408_);
lean_dec(v_fst_1407_);
lean_dec(v_a_1401_);
lean_dec(v_i_1371_);
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
v_a_1439_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1414_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1414_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_a_1401_);
lean_dec(v_i_1371_);
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
v_a_1448_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1404_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1404_);
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
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_i_1371_);
lean_dec_ref(v_eType_1369_);
lean_dec_ref(v_targetType_1368_);
lean_dec(v_term_x3f_1367_);
lean_dec(v_mvarId_1365_);
v_a_1456_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1400_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1400_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1464_, lean_object* v_cfg_1465_, lean_object* v_term_x3f_1466_, lean_object* v_targetType_1467_, lean_object* v_eType_1468_, lean_object* v_rangeNumArgs_1469_, lean_object* v_i_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1464_, v_cfg_1465_, v_term_x3f_1466_, v_targetType_1467_, v_eType_1468_, v_rangeNumArgs_1469_, v_i_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec_ref(v_rangeNumArgs_1469_);
lean_dec_ref(v_cfg_1465_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1477_, lean_object* v_h__1_1478_){
_start:
{
lean_object* v_snd_1479_; lean_object* v_fst_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; lean_object* v___x_1483_; 
v_snd_1479_ = lean_ctor_get(v_x_1477_, 1);
lean_inc(v_snd_1479_);
v_fst_1480_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_fst_1480_);
lean_dec_ref(v_x_1477_);
v_fst_1481_ = lean_ctor_get(v_snd_1479_, 0);
lean_inc(v_fst_1481_);
v_snd_1482_ = lean_ctor_get(v_snd_1479_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_snd_1479_);
v___x_1483_ = lean_apply_3(v_h__1_1478_, v_fst_1480_, v_fst_1481_, v_snd_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1484_, lean_object* v_x_1485_, lean_object* v_h__1_1486_){
_start:
{
lean_object* v_snd_1487_; lean_object* v_fst_1488_; lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v___x_1491_; 
v_snd_1487_ = lean_ctor_get(v_x_1485_, 1);
lean_inc(v_snd_1487_);
v_fst_1488_ = lean_ctor_get(v_x_1485_, 0);
lean_inc(v_fst_1488_);
lean_dec_ref(v_x_1485_);
v_fst_1489_ = lean_ctor_get(v_snd_1487_, 0);
lean_inc(v_fst_1489_);
v_snd_1490_ = lean_ctor_get(v_snd_1487_, 1);
lean_inc(v_snd_1490_);
lean_dec(v_snd_1487_);
v___x_1491_ = lean_apply_3(v_h__1_1486_, v_fst_1488_, v_fst_1489_, v_snd_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = l_Lean_Expr_hasMVar(v_e_1492_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_e_1492_);
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v_mctx_1498_; lean_object* v___x_1499_; lean_object* v_fst_1500_; lean_object* v_snd_1501_; lean_object* v___x_1502_; lean_object* v_cache_1503_; lean_object* v_zetaDeltaFVarIds_1504_; lean_object* v_postponed_1505_; lean_object* v_diag_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
v___x_1497_ = lean_st_ref_get(v___y_1493_);
v_mctx_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_mctx_1498_);
lean_dec(v___x_1497_);
v___x_1499_ = l_Lean_instantiateMVarsCore(v_mctx_1498_, v_e_1492_);
v_fst_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_fst_1500_);
v_snd_1501_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_snd_1501_);
lean_dec_ref(v___x_1499_);
v___x_1502_ = lean_st_ref_take(v___y_1493_);
v_cache_1503_ = lean_ctor_get(v___x_1502_, 1);
v_zetaDeltaFVarIds_1504_ = lean_ctor_get(v___x_1502_, 2);
v_postponed_1505_ = lean_ctor_get(v___x_1502_, 3);
v_diag_1506_ = lean_ctor_get(v___x_1502_, 4);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v___x_1502_, 0);
lean_dec(v_unused_1516_);
v___x_1508_ = v___x_1502_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_diag_1506_);
lean_inc(v_postponed_1505_);
lean_inc(v_zetaDeltaFVarIds_1504_);
lean_inc(v_cache_1503_);
lean_dec(v___x_1502_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v_snd_1501_);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_snd_1501_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_cache_1503_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_zetaDeltaFVarIds_1504_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_postponed_1505_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_diag_1506_);
v___x_1511_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_st_ref_set(v___y_1493_, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_fst_1500_);
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1517_, v___y_1518_);
lean_dec(v___y_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1521_, v___y_1523_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1535_, lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1535_, v_x_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1542_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1559_, lean_object* v_x_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1559_, v_x_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1567_, lean_object* v_mvarId_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1568_, v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1576_, lean_object* v_mvarId_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1576_, v_mvarId_1577_, v_x_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1585_, size_t v_i_1586_, size_t v_stop_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_a_1592_; uint8_t v___x_1596_; 
v___x_1596_ = lean_usize_dec_eq(v_i_1586_, v_stop_1587_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1597_ = lean_array_uget_borrowed(v_as_1585_, v_i_1586_);
v___x_1600_ = l_Lean_Expr_mvarId_x21(v___x_1597_);
v___x_1601_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1600_, v___y_1589_);
lean_dec(v___x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; uint8_t v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_unbox(v_a_1602_);
lean_dec(v_a_1602_);
if (v___x_1603_ == 0)
{
goto v___jp_1598_;
}
else
{
v_a_1592_ = v_b_1588_;
goto v___jp_1591_;
}
}
else
{
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1604_; uint8_t v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1601_);
v___x_1605_ = lean_unbox(v_a_1604_);
lean_dec(v_a_1604_);
if (v___x_1605_ == 0)
{
v_a_1592_ = v_b_1588_;
goto v___jp_1591_;
}
else
{
goto v___jp_1598_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_b_1588_);
v_a_1606_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1601_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1601_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
v___jp_1598_:
{
lean_object* v___x_1599_; 
lean_inc(v___x_1597_);
v___x_1599_ = lean_array_push(v_b_1588_, v___x_1597_);
v_a_1592_ = v___x_1599_;
goto v___jp_1591_;
}
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_b_1588_);
return v___x_1614_;
}
v___jp_1591_:
{
size_t v___x_1593_; size_t v___x_1594_; 
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1586_, v___x_1593_);
v_i_1586_ = v___x_1594_;
v_b_1588_ = v_a_1592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1615_, lean_object* v_i_1616_, lean_object* v_stop_1617_, lean_object* v_b_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
size_t v_i_boxed_1621_; size_t v_stop_boxed_1622_; lean_object* v_res_1623_; 
v_i_boxed_1621_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_stop_boxed_1622_ = lean_unbox_usize(v_stop_1617_);
lean_dec(v_stop_1617_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1615_, v_i_boxed_1621_, v_stop_boxed_1622_, v_b_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v_as_1615_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
if (lean_obj_tag(v_as_1624_) == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
else
{
lean_object* v_head_1632_; lean_object* v_tail_1633_; lean_object* v___x_1634_; 
v_head_1632_ = lean_ctor_get(v_as_1624_, 0);
lean_inc(v_head_1632_);
v_tail_1633_ = lean_ctor_get(v_as_1624_, 1);
lean_inc(v_tail_1633_);
lean_dec_ref(v_as_1624_);
v___x_1634_ = l_Lean_MVarId_headBetaType(v_head_1632_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref(v___x_1634_);
v_as_1624_ = v_tail_1633_;
goto _start;
}
else
{
lean_dec(v_tail_1633_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_ks_1647_; lean_object* v_vs_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1672_; 
v_ks_1647_ = lean_ctor_get(v_x_1643_, 0);
v_vs_1648_ = lean_ctor_get(v_x_1643_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1650_ = v_x_1643_;
v_isShared_1651_ = v_isSharedCheck_1672_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_vs_1648_);
lean_inc(v_ks_1647_);
lean_dec(v_x_1643_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1672_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = lean_array_get_size(v_ks_1647_);
v___x_1653_ = lean_nat_dec_lt(v_x_1644_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_x_1644_);
v___x_1654_ = lean_array_push(v_ks_1647_, v_x_1645_);
v___x_1655_ = lean_array_push(v_vs_1648_, v_x_1646_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___x_1655_);
lean_ctor_set(v___x_1650_, 0, v___x_1654_);
v___x_1657_ = v___x_1650_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
else
{
lean_object* v_k_x27_1659_; uint8_t v___x_1660_; 
v_k_x27_1659_ = lean_array_fget_borrowed(v_ks_1647_, v_x_1644_);
v___x_1660_ = l_Lean_instBEqMVarId_beq(v_x_1645_, v_k_x27_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1662_; 
if (v_isShared_1651_ == 0)
{
v___x_1662_ = v___x_1650_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_ks_1647_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_vs_1648_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_nat_add(v_x_1644_, v___x_1663_);
lean_dec(v_x_1644_);
v_x_1643_ = v___x_1662_;
v_x_1644_ = v___x_1664_;
goto _start;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_array_fset(v_ks_1647_, v_x_1644_, v_x_1645_);
v___x_1668_ = lean_array_fset(v_vs_1648_, v_x_1644_, v_x_1646_);
lean_dec(v_x_1644_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___x_1668_);
lean_ctor_set(v___x_1650_, 0, v___x_1667_);
v___x_1670_ = v___x_1650_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1673_, lean_object* v_k_1674_, lean_object* v_v_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1673_, v___x_1676_, v_k_1674_, v_v_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1679_, size_t v_x_1680_, size_t v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 0)
{
lean_object* v_es_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v_j_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_es_1684_ = lean_ctor_get(v_x_1679_, 0);
v___x_1685_ = ((size_t)5ULL);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1688_ = lean_usize_land(v_x_1680_, v___x_1687_);
v_j_1689_ = lean_usize_to_nat(v___x_1688_);
v___x_1690_ = lean_array_get_size(v_es_1684_);
v___x_1691_ = lean_nat_dec_lt(v_j_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec(v_j_1689_);
lean_dec(v_x_1683_);
lean_dec(v_x_1682_);
return v_x_1679_;
}
else
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1728_; 
lean_inc_ref(v_es_1684_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x_1679_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_x_1679_, 0);
lean_dec(v_unused_1729_);
v___x_1693_ = v_x_1679_;
v_isShared_1694_ = v_isSharedCheck_1728_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v_x_1679_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1728_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_v_1695_; lean_object* v___x_1696_; lean_object* v_xs_x27_1697_; lean_object* v___y_1699_; 
v_v_1695_ = lean_array_fget(v_es_1684_, v_j_1689_);
v___x_1696_ = lean_box(0);
v_xs_x27_1697_ = lean_array_fset(v_es_1684_, v_j_1689_, v___x_1696_);
switch(lean_obj_tag(v_v_1695_))
{
case 0:
{
lean_object* v_key_1704_; lean_object* v_val_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1715_; 
v_key_1704_ = lean_ctor_get(v_v_1695_, 0);
v_val_1705_ = lean_ctor_get(v_v_1695_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_v_1695_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1707_ = v_v_1695_;
v_isShared_1708_ = v_isSharedCheck_1715_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_val_1705_);
lean_inc(v_key_1704_);
lean_dec(v_v_1695_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1715_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
uint8_t v___x_1709_; 
v___x_1709_ = l_Lean_instBEqMVarId_beq(v_x_1682_, v_key_1704_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_del_object(v___x_1707_);
v___x_1710_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1704_, v_val_1705_, v_x_1682_, v_x_1683_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
v___y_1699_ = v___x_1711_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1713_; 
lean_dec(v_val_1705_);
lean_dec(v_key_1704_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_x_1683_);
lean_ctor_set(v___x_1707_, 0, v_x_1682_);
v___x_1713_ = v___x_1707_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_x_1682_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_x_1683_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
v___y_1699_ = v___x_1713_;
goto v___jp_1698_;
}
}
}
}
case 1:
{
lean_object* v_node_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1726_; 
v_node_1716_ = lean_ctor_get(v_v_1695_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_v_1695_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1718_ = v_v_1695_;
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_node_1716_);
lean_dec(v_v_1695_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1720_ = lean_usize_shift_right(v_x_1680_, v___x_1685_);
v___x_1721_ = lean_usize_add(v_x_1681_, v___x_1686_);
v___x_1722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1716_, v___x_1720_, v___x_1721_, v_x_1682_, v_x_1683_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1722_);
v___x_1724_ = v___x_1718_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1699_ = v___x_1724_;
goto v___jp_1698_;
}
}
}
default: 
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_x_1682_);
lean_ctor_set(v___x_1727_, 1, v_x_1683_);
v___y_1699_ = v___x_1727_;
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_array_fset(v_xs_x27_1697_, v_j_1689_, v___y_1699_);
lean_dec(v_j_1689_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1700_);
v___x_1702_ = v___x_1693_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
else
{
lean_object* v_ks_1730_; lean_object* v_vs_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1751_; 
v_ks_1730_ = lean_ctor_get(v_x_1679_, 0);
v_vs_1731_ = lean_ctor_get(v_x_1679_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_x_1679_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1733_ = v_x_1679_;
v_isShared_1734_ = v_isSharedCheck_1751_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_vs_1731_);
lean_inc(v_ks_1730_);
lean_dec(v_x_1679_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1751_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_ks_1730_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_vs_1731_);
v___x_1736_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v_newNode_1737_; uint8_t v___y_1739_; size_t v___x_1745_; uint8_t v___x_1746_; 
v_newNode_1737_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1736_, v_x_1682_, v_x_1683_);
v___x_1745_ = ((size_t)7ULL);
v___x_1746_ = lean_usize_dec_le(v___x_1745_, v_x_1681_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1737_);
v___x_1748_ = lean_unsigned_to_nat(4u);
v___x_1749_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
lean_dec(v___x_1747_);
v___y_1739_ = v___x_1749_;
goto v___jp_1738_;
}
else
{
v___y_1739_ = v___x_1746_;
goto v___jp_1738_;
}
v___jp_1738_:
{
if (v___y_1739_ == 0)
{
lean_object* v_ks_1740_; lean_object* v_vs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_ks_1740_ = lean_ctor_get(v_newNode_1737_, 0);
lean_inc_ref(v_ks_1740_);
v_vs_1741_ = lean_ctor_get(v_newNode_1737_, 1);
lean_inc_ref(v_vs_1741_);
lean_dec_ref(v_newNode_1737_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1681_, v_ks_1740_, v_vs_1741_, v___x_1742_, v___x_1743_);
lean_dec_ref(v_vs_1741_);
lean_dec_ref(v_ks_1740_);
return v___x_1744_;
}
else
{
return v_newNode_1737_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1752_, lean_object* v_keys_1753_, lean_object* v_vals_1754_, lean_object* v_i_1755_, lean_object* v_entries_1756_){
_start:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = lean_array_get_size(v_keys_1753_);
v___x_1758_ = lean_nat_dec_lt(v_i_1755_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec(v_i_1755_);
return v_entries_1756_;
}
else
{
lean_object* v_k_1759_; lean_object* v_v_1760_; uint64_t v___x_1761_; size_t v_h_1762_; size_t v___x_1763_; lean_object* v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; size_t v___x_1767_; size_t v_h_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_k_1759_ = lean_array_fget_borrowed(v_keys_1753_, v_i_1755_);
v_v_1760_ = lean_array_fget_borrowed(v_vals_1754_, v_i_1755_);
v___x_1761_ = l_Lean_instHashableMVarId_hash(v_k_1759_);
v_h_1762_ = lean_uint64_to_usize(v___x_1761_);
v___x_1763_ = ((size_t)5ULL);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_sub(v_depth_1752_, v___x_1765_);
v___x_1767_ = lean_usize_mul(v___x_1763_, v___x_1766_);
v_h_1768_ = lean_usize_shift_right(v_h_1762_, v___x_1767_);
v___x_1769_ = lean_nat_add(v_i_1755_, v___x_1764_);
lean_dec(v_i_1755_);
lean_inc(v_v_1760_);
lean_inc(v_k_1759_);
v___x_1770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1756_, v_h_1768_, v_depth_1752_, v_k_1759_, v_v_1760_);
v_i_1755_ = v___x_1769_;
v_entries_1756_ = v___x_1770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1772_, lean_object* v_keys_1773_, lean_object* v_vals_1774_, lean_object* v_i_1775_, lean_object* v_entries_1776_){
_start:
{
size_t v_depth_boxed_1777_; lean_object* v_res_1778_; 
v_depth_boxed_1777_ = lean_unbox_usize(v_depth_1772_);
lean_dec(v_depth_1772_);
v_res_1778_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1777_, v_keys_1773_, v_vals_1774_, v_i_1775_, v_entries_1776_);
lean_dec_ref(v_vals_1774_);
lean_dec_ref(v_keys_1773_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
size_t v_x_6955__boxed_1784_; size_t v_x_6956__boxed_1785_; lean_object* v_res_1786_; 
v_x_6955__boxed_1784_ = lean_unbox_usize(v_x_1780_);
lean_dec(v_x_1780_);
v_x_6956__boxed_1785_ = lean_unbox_usize(v_x_1781_);
lean_dec(v_x_1781_);
v_res_1786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1779_, v_x_6955__boxed_1784_, v_x_6956__boxed_1785_, v_x_1782_, v_x_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
uint64_t v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = l_Lean_instHashableMVarId_hash(v_x_1788_);
v___x_1791_ = lean_uint64_to_usize(v___x_1790_);
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1787_, v___x_1791_, v___x_1792_, v_x_1788_, v_x_1789_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1794_, lean_object* v_val_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_mctx_1799_; lean_object* v_cache_1800_; lean_object* v_zetaDeltaFVarIds_1801_; lean_object* v_postponed_1802_; lean_object* v_diag_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1831_; 
v___x_1798_ = lean_st_ref_take(v___y_1796_);
v_mctx_1799_ = lean_ctor_get(v___x_1798_, 0);
v_cache_1800_ = lean_ctor_get(v___x_1798_, 1);
v_zetaDeltaFVarIds_1801_ = lean_ctor_get(v___x_1798_, 2);
v_postponed_1802_ = lean_ctor_get(v___x_1798_, 3);
v_diag_1803_ = lean_ctor_get(v___x_1798_, 4);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1805_ = v___x_1798_;
v_isShared_1806_ = v_isSharedCheck_1831_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_diag_1803_);
lean_inc(v_postponed_1802_);
lean_inc(v_zetaDeltaFVarIds_1801_);
lean_inc(v_cache_1800_);
lean_inc(v_mctx_1799_);
lean_dec(v___x_1798_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1831_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_depth_1807_; lean_object* v_levelAssignDepth_1808_; lean_object* v_lmvarCounter_1809_; lean_object* v_mvarCounter_1810_; lean_object* v_lDecls_1811_; lean_object* v_decls_1812_; lean_object* v_userNames_1813_; lean_object* v_lAssignment_1814_; lean_object* v_eAssignment_1815_; lean_object* v_dAssignment_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1830_; 
v_depth_1807_ = lean_ctor_get(v_mctx_1799_, 0);
v_levelAssignDepth_1808_ = lean_ctor_get(v_mctx_1799_, 1);
v_lmvarCounter_1809_ = lean_ctor_get(v_mctx_1799_, 2);
v_mvarCounter_1810_ = lean_ctor_get(v_mctx_1799_, 3);
v_lDecls_1811_ = lean_ctor_get(v_mctx_1799_, 4);
v_decls_1812_ = lean_ctor_get(v_mctx_1799_, 5);
v_userNames_1813_ = lean_ctor_get(v_mctx_1799_, 6);
v_lAssignment_1814_ = lean_ctor_get(v_mctx_1799_, 7);
v_eAssignment_1815_ = lean_ctor_get(v_mctx_1799_, 8);
v_dAssignment_1816_ = lean_ctor_get(v_mctx_1799_, 9);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_mctx_1799_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1818_ = v_mctx_1799_;
v_isShared_1819_ = v_isSharedCheck_1830_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_dAssignment_1816_);
lean_inc(v_eAssignment_1815_);
lean_inc(v_lAssignment_1814_);
lean_inc(v_userNames_1813_);
lean_inc(v_decls_1812_);
lean_inc(v_lDecls_1811_);
lean_inc(v_mvarCounter_1810_);
lean_inc(v_lmvarCounter_1809_);
lean_inc(v_levelAssignDepth_1808_);
lean_inc(v_depth_1807_);
lean_dec(v_mctx_1799_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1830_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1815_, v_mvarId_1794_, v_val_1795_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 8, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_depth_1807_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_levelAssignDepth_1808_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_lmvarCounter_1809_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_mvarCounter_1810_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_lDecls_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_decls_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 6, v_userNames_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 7, v_lAssignment_1814_);
lean_ctor_set(v_reuseFailAlloc_1829_, 8, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 9, v_dAssignment_1816_);
v___x_1822_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1822_);
v___x_1824_ = v___x_1805_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_cache_1800_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_zetaDeltaFVarIds_1801_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_postponed_1802_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_diag_1803_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_st_ref_set(v___y_1796_, v___x_1824_);
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1832_, lean_object* v_val_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1832_, v_val_1833_, v___y_1834_);
lean_dec(v___y_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = 0;
return v___x_1839_;
}
else
{
lean_object* v_head_1840_; lean_object* v_tail_1841_; uint8_t v___x_1842_; 
v_head_1840_ = lean_ctor_get(v_x_1838_, 0);
v_tail_1841_ = lean_ctor_get(v_x_1838_, 1);
v___x_1842_ = l_Lean_instBEqMVarId_beq(v_a_1837_, v_head_1840_);
if (v___x_1842_ == 0)
{
v_x_1838_ = v_tail_1841_;
goto _start;
}
else
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1844_, lean_object* v_x_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1844_, v_x_1845_);
lean_dec(v_x_1845_);
lean_dec(v_a_1844_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1848_, lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_){
_start:
{
lean_object* v___y_1854_; uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = lean_array_uget_borrowed(v_as_1849_, v_i_1850_);
v___x_1860_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1859_, v_a_1848_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v___x_1859_);
v___x_1861_ = lean_array_push(v_b_1852_, v___x_1859_);
v___y_1854_ = v___x_1861_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v_b_1852_;
goto v___jp_1853_;
}
}
else
{
return v_b_1852_;
}
v___jp_1853_:
{
size_t v___x_1855_; size_t v___x_1856_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1850_, v___x_1855_);
v_i_1850_ = v___x_1856_;
v_b_1852_ = v___y_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1862_, lean_object* v_as_1863_, lean_object* v_i_1864_, lean_object* v_stop_1865_, lean_object* v_b_1866_){
_start:
{
size_t v_i_boxed_1867_; size_t v_stop_boxed_1868_; lean_object* v_res_1869_; 
v_i_boxed_1867_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_stop_boxed_1868_ = lean_unbox_usize(v_stop_1865_);
lean_dec(v_stop_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1862_, v_as_1863_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1866_);
lean_dec_ref(v_as_1863_);
lean_dec(v_a_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1870_, lean_object* v___x_1871_, lean_object* v_e_1872_, lean_object* v_cfg_1873_, lean_object* v_term_x3f_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_a_1914_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; uint8_t v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___x_1955_; 
lean_inc(v___x_1871_);
lean_inc(v_mvarId_1870_);
v___x_1955_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1870_, v___x_1871_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1956_; 
lean_dec_ref(v___x_1955_);
lean_inc(v_mvarId_1870_);
v___x_1956_ = l_Lean_MVarId_getType(v_mvarId_1870_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
lean_inc(v___y_1878_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc_ref(v_e_1872_);
v___x_1958_ = lean_infer_type(v_e_1872_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_rangeNumArgs_1961_; lean_object* v_lower_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___x_2006_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_n(v_a_1959_, 2);
lean_dec_ref(v___x_1958_);
v___x_2006_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1959_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_snd_2008_; uint8_t v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v_snd_2008_ = lean_ctor_get(v_a_2007_, 1);
v___x_2009_ = lean_unbox(v_snd_2008_);
if (v___x_2009_ == 0)
{
lean_object* v_fst_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2030_; 
v_fst_2010_ = lean_ctor_get(v_a_2007_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_a_2007_, 1);
lean_dec(v_unused_2031_);
v___x_2012_ = v_a_2007_;
v_isShared_2013_ = v_isSharedCheck_2030_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_fst_2010_);
lean_dec(v_a_2007_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2030_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; 
lean_inc(v_a_1957_);
v___x_2014_ = l_Lean_Meta_getExpectedNumArgs(v_a_1957_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_nat_sub(v_fst_2010_, v_a_2015_);
lean_dec(v_a_2015_);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_add(v_fst_2010_, v___x_2017_);
lean_dec(v_fst_2010_);
lean_inc(v___x_2016_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2018_);
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2020_ = v___x_2012_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
v_rangeNumArgs_1961_ = v___x_2020_;
v_lower_1962_ = v___x_2016_;
v___y_1963_ = v___y_1875_;
v___y_1964_ = v___y_1876_;
v___y_1965_ = v___y_1877_;
v___y_1966_ = v___y_1878_;
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_2012_);
lean_dec(v_fst_2010_);
lean_dec(v_a_1959_);
lean_dec(v_a_1957_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2022_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2014_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2014_);
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
}
else
{
lean_object* v_fst_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2041_; 
v_fst_2032_ = lean_ctor_get(v_a_2007_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_a_2007_, 1);
lean_dec(v_unused_2042_);
v___x_2034_ = v_a_2007_;
v_isShared_2035_ = v_isSharedCheck_2041_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_fst_2032_);
lean_dec(v_a_2007_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2041_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_add(v_fst_2032_, v___x_2036_);
lean_inc(v_fst_2032_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2037_);
v___x_2039_ = v___x_2034_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_fst_2032_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
v_rangeNumArgs_1961_ = v___x_2039_;
v_lower_1962_ = v_fst_2032_;
v___y_1963_ = v___y_1875_;
v___y_1964_ = v___y_1876_;
v___y_1965_ = v___y_1877_;
v___y_1966_ = v___y_1878_;
goto v___jp_1960_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_1959_);
lean_dec(v_a_1957_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2043_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2006_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2006_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
v___jp_1960_:
{
lean_object* v___x_1967_; 
lean_inc(v_mvarId_1870_);
v___x_1967_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1870_, v_cfg_1873_, v_term_x3f_1874_, v_a_1957_, v_a_1959_, v_rangeNumArgs_1961_, v_lower_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec_ref(v_rangeNumArgs_1961_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; uint8_t v_newGoals_1971_; uint8_t v_synthAssignedInstances_1972_; uint8_t v_allowSynthFailures_1973_; lean_object* v___x_1974_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v_fst_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_fst_1969_);
v_snd_1970_ = lean_ctor_get(v_a_1968_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_a_1968_);
v_newGoals_1971_ = lean_ctor_get_uint8(v_cfg_1873_, 0);
v_synthAssignedInstances_1972_ = lean_ctor_get_uint8(v_cfg_1873_, 1);
v_allowSynthFailures_1973_ = lean_ctor_get_uint8(v_cfg_1873_, 2);
lean_inc(v_mvarId_1870_);
v___x_1974_ = l_Lean_Meta_postprocessAppMVars(v___x_1871_, v_mvarId_1870_, v_fst_1969_, v_snd_1970_, v_synthAssignedInstances_1972_, v_allowSynthFailures_1973_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; lean_object* v_a_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
lean_dec_ref(v___x_1974_);
v___x_1975_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1872_, v___y_1964_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_n(v_a_1976_, 2);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_mkAppN(v_a_1976_, v_fst_1969_);
v___x_1978_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1870_, v___x_1977_, v___y_1964_);
lean_dec_ref(v___x_1978_);
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_array_get_size(v_fst_1969_);
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1982_ = lean_nat_dec_lt(v___x_1979_, v___x_1980_);
if (v___x_1982_ == 0)
{
lean_dec(v_fst_1969_);
v___y_1907_ = v___y_1966_;
v___y_1908_ = v_a_1976_;
v___y_1909_ = v___y_1965_;
v___y_1910_ = v_newGoals_1971_;
v___y_1911_ = v___y_1963_;
v___y_1912_ = v___y_1964_;
v___y_1913_ = v___x_1979_;
v_a_1914_ = v___x_1981_;
goto v___jp_1906_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_nat_dec_le(v___x_1980_, v___x_1980_);
if (v___x_1983_ == 0)
{
if (v___x_1982_ == 0)
{
lean_dec(v_fst_1969_);
v___y_1907_ = v___y_1966_;
v___y_1908_ = v_a_1976_;
v___y_1909_ = v___y_1965_;
v___y_1910_ = v_newGoals_1971_;
v___y_1911_ = v___y_1963_;
v___y_1912_ = v___y_1964_;
v___y_1913_ = v___x_1979_;
v_a_1914_ = v___x_1981_;
goto v___jp_1906_;
}
else
{
size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = lean_usize_of_nat(v___x_1980_);
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1969_, v___x_1984_, v___x_1985_, v___x_1981_, v___y_1964_);
lean_dec(v_fst_1969_);
v___y_1938_ = v___y_1966_;
v___y_1939_ = v_a_1976_;
v___y_1940_ = v___y_1965_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v_newGoals_1971_;
v___y_1943_ = v___y_1964_;
v___y_1944_ = v___x_1979_;
v___y_1945_ = v___x_1986_;
goto v___jp_1937_;
}
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_of_nat(v___x_1980_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1969_, v___x_1987_, v___x_1988_, v___x_1981_, v___y_1964_);
lean_dec(v_fst_1969_);
v___y_1938_ = v___y_1966_;
v___y_1939_ = v_a_1976_;
v___y_1940_ = v___y_1965_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v_newGoals_1971_;
v___y_1943_ = v___y_1964_;
v___y_1944_ = v___x_1979_;
v___y_1945_ = v___x_1989_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_fst_1969_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v_e_1872_);
lean_dec(v_mvarId_1870_);
v_a_1990_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1974_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1974_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_1998_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1967_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1967_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_1957_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2051_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1958_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1958_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2059_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1956_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1956_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2067_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1955_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1955_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
v___jp_1880_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_array_to_list(v___y_1886_);
v___x_1888_ = l_List_appendTR___redArg(v___y_1882_, v___x_1887_);
lean_inc(v___x_1888_);
v___x_1889_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1888_, v___y_1884_, v___y_1885_, v___y_1883_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1897_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___x_1888_);
v_a_1898_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
v___jp_1906_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1908_, v___y_1911_, v___y_1912_, v___y_1909_, v___y_1907_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1914_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1909_, v___y_1907_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_array_get_size(v_a_1916_);
v___x_1920_ = lean_mk_empty_array_with_capacity(v___y_1913_);
v___x_1921_ = lean_nat_dec_lt(v___y_1913_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_dec(v_a_1916_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v_a_1918_;
v___y_1883_ = v___y_1909_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1920_;
goto v___jp_1880_;
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1922_ == 0)
{
if (v___x_1921_ == 0)
{
lean_dec(v_a_1916_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v_a_1918_;
v___y_1883_ = v___y_1909_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1920_;
goto v___jp_1880_;
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1919_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1918_, v_a_1916_, v___x_1923_, v___x_1924_, v___x_1920_);
lean_dec(v_a_1916_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v_a_1918_;
v___y_1883_ = v___y_1909_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1925_;
goto v___jp_1880_;
}
}
else
{
size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((size_t)0ULL);
v___x_1927_ = lean_usize_of_nat(v___x_1919_);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1918_, v_a_1916_, v___x_1926_, v___x_1927_, v___x_1920_);
lean_dec(v_a_1916_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v_a_1918_;
v___y_1883_ = v___y_1909_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1928_;
goto v___jp_1880_;
}
}
}
else
{
lean_dec(v_a_1916_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
return v___x_1917_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_a_1914_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
v_a_1929_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1915_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1915_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
v___jp_1937_:
{
if (lean_obj_tag(v___y_1945_) == 0)
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___y_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___y_1945_);
v___y_1907_ = v___y_1938_;
v___y_1908_ = v___y_1939_;
v___y_1909_ = v___y_1940_;
v___y_1910_ = v___y_1942_;
v___y_1911_ = v___y_1941_;
v___y_1912_ = v___y_1943_;
v___y_1913_ = v___y_1944_;
v_a_1914_ = v_a_1946_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
v_a_1947_ = lean_ctor_get(v___y_1945_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1945_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___y_1945_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___y_1945_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2075_, lean_object* v___x_2076_, lean_object* v_e_2077_, lean_object* v_cfg_2078_, lean_object* v_term_x3f_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2075_, v___x_2076_, v_e_2077_, v_cfg_2078_, v_term_x3f_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec_ref(v_cfg_2078_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2086_, lean_object* v_e_2087_, lean_object* v_cfg_2088_, lean_object* v_term_x3f_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2086_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2096_, 0, v_mvarId_2086_);
lean_closure_set(v___f_2096_, 1, v___x_2095_);
lean_closure_set(v___f_2096_, 2, v_e_2087_);
lean_closure_set(v___f_2096_, 3, v_cfg_2088_);
lean_closure_set(v___f_2096_, 4, v_term_x3f_2089_);
v___x_2097_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2086_, v___f_2096_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2098_, lean_object* v_e_2099_, lean_object* v_cfg_2100_, lean_object* v_term_x3f_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_MVarId_apply(v_mvarId_2098_, v_e_2099_, v_cfg_2100_, v_term_x3f_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2108_, lean_object* v_val_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2108_, v_val_2109_, v___y_2111_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2116_, lean_object* v_val_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2116_, v_val_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2124_, v_i_2125_, v_stop_2126_, v_b_2127_, v___y_2129_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
size_t v_i_boxed_2143_; size_t v_stop_boxed_2144_; lean_object* v_res_2145_; 
v_i_boxed_2143_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_stop_boxed_2144_ = lean_unbox_usize(v_stop_2136_);
lean_dec(v_stop_2136_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2134_, v_i_boxed_2143_, v_stop_boxed_2144_, v_b_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v_as_2134_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2147_, v_x_2148_, v_x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_, size_t v_x_2153_, size_t v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2152_, v_x_2153_, v_x_2154_, v_x_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
size_t v_x_7665__boxed_2164_; size_t v_x_7666__boxed_2165_; lean_object* v_res_2166_; 
v_x_7665__boxed_2164_ = lean_unbox_usize(v_x_2160_);
lean_dec(v_x_2160_);
v_x_7666__boxed_2165_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_res_2166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2158_, v_x_2159_, v_x_7665__boxed_2164_, v_x_7666__boxed_2165_, v_x_2162_, v_x_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2167_, lean_object* v_n_2168_, lean_object* v_k_2169_, lean_object* v_v_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2168_, v_k_2169_, v_v_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2172_, size_t v_depth_2173_, lean_object* v_keys_2174_, lean_object* v_vals_2175_, lean_object* v_heq_2176_, lean_object* v_i_2177_, lean_object* v_entries_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2173_, v_keys_2174_, v_vals_2175_, v_i_2177_, v_entries_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_depth_2181_, lean_object* v_keys_2182_, lean_object* v_vals_2183_, lean_object* v_heq_2184_, lean_object* v_i_2185_, lean_object* v_entries_2186_){
_start:
{
size_t v_depth_boxed_2187_; lean_object* v_res_2188_; 
v_depth_boxed_2187_ = lean_unbox_usize(v_depth_2181_);
lean_dec(v_depth_2181_);
v_res_2188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2180_, v_depth_boxed_2187_, v_keys_2182_, v_vals_2183_, v_heq_2184_, v_i_2185_, v_entries_2186_);
lean_dec_ref(v_vals_2183_);
lean_dec_ref(v_keys_2182_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2190_, v_x_2191_, v_x_2192_, v_x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2198_, lean_object* v_c_2199_, lean_object* v_cfg_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; 
lean_inc(v_c_2199_);
v___x_2206_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2199_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2209_ = 0;
v___x_2210_ = l_Lean_MessageData_ofConstName(v_c_2199_, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2208_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2208_);
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = l_Lean_MVarId_apply(v_mvar_2198_, v_a_2207_, v_cfg_2200_, v___x_2213_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2214_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_cfg_2200_);
lean_dec(v_c_2199_);
lean_dec(v_mvar_2198_);
v_a_2215_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2206_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2206_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2223_, lean_object* v_c_2224_, lean_object* v_cfg_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_MVarId_applyConst(v_mvar_2223_, v_c_2224_, v_cfg_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; lean_object* v_env_2239_; lean_object* v___x_2240_; lean_object* v_mctx_2241_; lean_object* v_lctx_2242_; lean_object* v_options_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2238_ = lean_st_ref_get(v___y_2236_);
v_env_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_ref(v_env_2239_);
lean_dec(v___x_2238_);
v___x_2240_ = lean_st_ref_get(v___y_2234_);
v_mctx_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_ref(v_mctx_2241_);
lean_dec(v___x_2240_);
v_lctx_2242_ = lean_ctor_get(v___y_2233_, 2);
v_options_2243_ = lean_ctor_get(v___y_2235_, 2);
lean_inc_ref(v_options_2243_);
lean_inc_ref(v_lctx_2242_);
v___x_2244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2244_, 0, v_env_2239_);
lean_ctor_set(v___x_2244_, 1, v_mctx_2241_);
lean_ctor_set(v___x_2244_, 2, v_lctx_2242_);
lean_ctor_set(v___x_2244_, 3, v_options_2243_);
v___x_2245_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v_msgData_2232_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_ref_2260_; lean_object* v___x_2261_; lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
v_ref_2260_ = lean_ctor_get(v___y_2257_, 5);
v___x_2261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_inc(v_ref_2260_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
lean_ctor_set(v___x_2266_, 1, v_a_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_bs_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
if (v___x_2281_ == 0)
{
return v_bs_2280_;
}
else
{
lean_object* v_v_2282_; lean_object* v___x_2283_; lean_object* v_bs_x27_2284_; lean_object* v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v_v_2282_ = lean_array_uget(v_bs_2280_, v_i_2279_);
v___x_2283_ = lean_unsigned_to_nat(0u);
v_bs_x27_2284_ = lean_array_uset(v_bs_2280_, v_i_2279_, v___x_2283_);
v___x_2285_ = l_Lean_Expr_mvarId_x21(v_v_2282_);
lean_dec(v_v_2282_);
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_add(v_i_2279_, v___x_2286_);
v___x_2288_ = lean_array_uset(v_bs_x27_2284_, v_i_2279_, v___x_2285_);
v_i_2279_ = v___x_2287_;
v_bs_2280_ = v___x_2288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_bs_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2293_, v_i_boxed_2294_, v_bs_2292_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2298_ = l_Lean_stringToMessageData(v___x_2297_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2307_ = l_Lean_stringToMessageData(v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2310_ = l_Lean_stringToMessageData(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2314_, lean_object* v___x_2315_, lean_object* v_e_2316_, lean_object* v_n_2317_, uint8_t v_useApproxDefEq_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
lean_inc(v_mvarId_2314_);
v___x_2324_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2314_, v___x_2315_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2325_; 
lean_dec_ref(v___x_2324_);
lean_inc(v_mvarId_2314_);
v___x_2325_ = l_Lean_MVarId_getType(v_mvarId_2314_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
lean_inc(v___y_2322_);
lean_inc_ref(v___y_2321_);
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc_ref(v_e_2316_);
v___x_2327_ = lean_infer_type(v_e_2316_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = 0;
lean_inc(v_n_2317_);
v___x_2330_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2328_, v_n_2317_, v___x_2329_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v_fst_2332_; lean_object* v_snd_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2423_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v_fst_2332_ = lean_ctor_get(v_a_2331_, 0);
v_snd_2333_ = lean_ctor_get(v_a_2331_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_a_2331_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2335_ = v_a_2331_;
v_isShared_2336_ = v_isSharedCheck_2423_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snd_2333_);
lean_inc(v_fst_2332_);
lean_dec(v_a_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2423_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___y_2338_; lean_object* v_snd_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2421_; 
v_snd_2353_ = lean_ctor_get(v_snd_2333_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_snd_2333_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v_snd_2333_, 0);
lean_dec(v_unused_2422_);
v___x_2355_ = v_snd_2333_;
v_isShared_2356_ = v_isSharedCheck_2421_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_snd_2353_);
lean_dec(v_snd_2333_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2421_;
goto v_resetjp_2354_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2351_; 
lean_inc(v_fst_2332_);
v___x_2339_ = l_Lean_Expr_beta(v_e_2316_, v_fst_2332_);
v___x_2340_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2314_, v___x_2339_, v___y_2338_);
lean_dec(v___y_2338_);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2340_, 0);
lean_dec(v_unused_2352_);
v___x_2342_ = v___x_2340_;
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v___x_2340_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
size_t v_sz_2344_; size_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_sz_2344_ = lean_array_size(v_fst_2332_);
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2344_, v___x_2345_, v_fst_2332_);
v___x_2347_ = lean_array_to_list(v___x_2346_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2347_);
v___x_2349_ = v___x_2342_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
v_resetjp_2354_:
{
lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = lean_array_get_size(v_fst_2332_);
v___x_2402_ = lean_nat_dec_eq(v___x_2401_, v_n_2317_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_del_object(v___x_2355_);
lean_del_object(v___x_2335_);
lean_dec(v_fst_2332_);
lean_dec(v_a_2326_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v___x_2403_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2404_ = l_Nat_reprFast(v_n_2317_);
v___x_2405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
v___x_2406_ = l_Lean_MessageData_ofFormat(v___x_2405_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2403_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_indentExpr(v_snd_2353_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2411_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
v___y_2358_ = v___y_2319_;
v___y_2359_ = v___y_2320_;
v___y_2360_ = v___y_2321_;
v___y_2361_ = v___y_2322_;
goto v___jp_2357_;
}
v___jp_2357_:
{
lean_object* v___x_2362_; 
lean_inc(v_a_2326_);
lean_inc(v_snd_2353_);
v___x_2362_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2318_, v_snd_2353_, v_a_2326_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; uint8_t v___x_2364_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = lean_unbox(v_a_2363_);
lean_dec(v_a_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec(v_fst_2332_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v___x_2365_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2366_ = l_Lean_indentExpr(v_a_2326_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 7);
lean_ctor_set(v___x_2355_, 1, v___x_2366_);
lean_ctor_set(v___x_2355_, 0, v___x_2365_);
v___x_2368_ = v___x_2355_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 7);
lean_ctor_set(v___x_2335_, 1, v___x_2369_);
lean_ctor_set(v___x_2335_, 0, v___x_2368_);
v___x_2371_ = v___x_2335_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v___x_2372_ = l_Lean_indentExpr(v_snd_2353_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Nat_reprFast(v_n_2317_);
v___x_2377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
v___x_2378_ = l_Lean_MessageData_ofFormat(v___x_2377_);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2375_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2381_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
else
{
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v___y_2358_);
lean_del_object(v___x_2355_);
lean_dec(v_snd_2353_);
lean_del_object(v___x_2335_);
lean_dec(v_a_2326_);
lean_dec(v_n_2317_);
v___y_2338_ = v___y_2359_;
goto v___jp_2337_;
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_del_object(v___x_2355_);
lean_dec(v_snd_2353_);
lean_del_object(v___x_2335_);
lean_dec(v_fst_2332_);
lean_dec(v_a_2326_);
lean_dec(v_n_2317_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v_a_2393_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2362_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2362_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_a_2326_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_n_2317_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v_a_2424_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2330_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2330_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_a_2326_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_n_2317_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v_a_2432_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2327_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2327_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_n_2317_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v_a_2440_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2325_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2325_);
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
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_n_2317_);
lean_dec_ref(v_e_2316_);
lean_dec(v_mvarId_2314_);
v_a_2448_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2324_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2324_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2456_, lean_object* v___x_2457_, lean_object* v_e_2458_, lean_object* v_n_2459_, lean_object* v_useApproxDefEq_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2466_; lean_object* v_res_2467_; 
v_useApproxDefEq_boxed_2466_ = lean_unbox(v_useApproxDefEq_2460_);
v_res_2467_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2456_, v___x_2457_, v_e_2458_, v_n_2459_, v_useApproxDefEq_boxed_2466_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2468_, lean_object* v_e_2469_, lean_object* v_n_2470_, uint8_t v_useApproxDefEq_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2478_ = lean_box(v_useApproxDefEq_2471_);
lean_inc(v_mvarId_2468_);
v___f_2479_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2479_, 0, v_mvarId_2468_);
lean_closure_set(v___f_2479_, 1, v___x_2477_);
lean_closure_set(v___f_2479_, 2, v_e_2469_);
lean_closure_set(v___f_2479_, 3, v_n_2470_);
lean_closure_set(v___f_2479_, 4, v___x_2478_);
v___x_2480_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2468_, v___f_2479_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2481_, lean_object* v_e_2482_, lean_object* v_n_2483_, lean_object* v_useApproxDefEq_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2490_; lean_object* v_res_2491_; 
v_useApproxDefEq_boxed_2490_ = lean_unbox(v_useApproxDefEq_2484_);
v_res_2491_ = l_Lean_MVarId_applyN(v_mvarId_2481_, v_e_2482_, v_n_2483_, v_useApproxDefEq_boxed_2490_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2492_, lean_object* v_msg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2500_, v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = lean_box(0);
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2520_ = l_Lean_mkConst(v___x_2519_, v___x_2518_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2521_, lean_object* v_type_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
lean_inc(v_a_2527_);
lean_inc_ref(v_a_2526_);
lean_inc(v_a_2525_);
lean_inc_ref(v_a_2524_);
v___x_2529_ = lean_whnf(v_type_2522_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2532_ = lean_unsigned_to_nat(2u);
v___x_2533_ = l_Lean_Expr_isAppOfArity(v_a_2530_, v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2534_ = lean_st_ref_get(v_a_2523_);
v___x_2535_ = lean_array_get_size(v___x_2534_);
lean_dec(v___x_2534_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v___x_2535_, v___x_2536_);
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2539_ = lean_name_append_index_after(v___x_2538_, v___x_2537_);
v___x_2540_ = l_Lean_Name_append(v_tag_2521_, v___x_2539_);
v___x_2541_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2530_, v___x_2540_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2553_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2553_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2553_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2546_ = lean_st_ref_take(v_a_2523_);
v___x_2547_ = l_Lean_Expr_mvarId_x21(v_a_2542_);
v___x_2548_ = lean_array_push(v___x_2546_, v___x_2547_);
v___x_2549_ = lean_st_ref_set(v_a_2523_, v___x_2548_);
if (v_isShared_2545_ == 0)
{
v___x_2551_ = v___x_2544_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2542_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
return v___x_2541_;
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = l_Lean_Expr_appFn_x21(v_a_2530_);
v___x_2555_ = l_Lean_Expr_appArg_x21(v___x_2554_);
lean_dec_ref(v___x_2554_);
lean_inc_ref(v___x_2555_);
lean_inc(v_tag_2521_);
v___x_2556_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2521_, v___x_2555_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = l_Lean_Expr_appArg_x21(v_a_2530_);
lean_dec(v_a_2530_);
lean_inc_ref(v___x_2558_);
v___x_2559_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2521_, v___x_2558_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2565_ = l_Lean_mkApp4(v___x_2564_, v___x_2555_, v___x_2558_, v_a_2557_, v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_dec_ref(v___x_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v___x_2555_);
return v___x_2559_;
}
}
else
{
lean_dec_ref(v___x_2555_);
lean_dec(v_a_2530_);
lean_dec(v_tag_2521_);
return v___x_2556_;
}
}
}
else
{
lean_dec(v_tag_2521_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2570_, lean_object* v_type_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2570_, v_type_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2579_, lean_object* v___x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
lean_inc(v_mvarId_2579_);
v___x_2586_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2579_, v___x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
lean_dec_ref(v___x_2586_);
lean_inc(v_mvarId_2579_);
v___x_2587_ = l_Lean_MVarId_getType_x27(v_mvarId_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2633_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2633_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2633_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2593_ = lean_unsigned_to_nat(2u);
v___x_2594_ = l_Lean_Expr_isAppOfArity(v_a_2588_, v___x_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
lean_dec(v_a_2588_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_mvarId_2579_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2596_);
v___x_2598_ = v___x_2590_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
else
{
lean_object* v___x_2600_; 
lean_del_object(v___x_2590_);
lean_inc(v_mvarId_2579_);
v___x_2600_ = l_Lean_MVarId_getTag(v_mvarId_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2603_ = lean_st_mk_ref(v___x_2602_);
v___x_2604_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2601_, v_a_2588_, v___x_2603_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = lean_st_ref_get(v___x_2603_);
lean_dec(v___x_2603_);
v___x_2607_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2579_, v_a_2605_, v___y_2582_);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v___x_2607_, 0);
lean_dec(v_unused_2616_);
v___x_2609_ = v___x_2607_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v___x_2607_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_array_to_list(v___x_2606_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2613_ = v___x_2609_;
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
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___x_2603_);
lean_dec(v_mvarId_2579_);
v_a_2617_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2604_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2604_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2588_);
lean_dec(v_mvarId_2579_);
v_a_2625_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2600_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2600_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_mvarId_2579_);
v_a_2634_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2587_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2587_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_mvarId_2579_);
v_a_2642_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2586_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2586_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2650_, lean_object* v___x_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2650_, v___x_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2661_);
v___f_2668_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2668_, 0, v_mvarId_2661_);
lean_closure_set(v___f_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2661_, v___f_2668_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_MVarId_splitAndCore(v_mvarId_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_MVarId_splitAndCore(v_mvarId_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_MVarId_splitAnd(v_mvarId_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2696_ = l_Lean_mkConst(v___x_2695_, v___x_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2701_, lean_object* v___x_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
lean_inc(v_mvarId_2701_);
v___x_2708_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2701_, v___x_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v___x_2709_; 
lean_dec_ref(v___x_2708_);
lean_inc(v_mvarId_2701_);
v___x_2709_ = l_Lean_MVarId_getType(v_mvarId_2701_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2710_, v___y_2704_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc_n(v_a_2712_, 2);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_Meta_getLevel(v_a_2712_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
lean_inc(v_mvarId_2701_);
v___x_2715_ = l_Lean_MVarId_getTag(v_mvarId_2701_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2719_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2718_, v_a_2716_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc_n(v_a_2720_, 2);
lean_dec_ref(v___x_2719_);
v___x_2721_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_a_2714_);
lean_ctor_set(v___x_2722_, 1, v___x_2717_);
v___x_2723_ = l_Lean_mkConst(v___x_2721_, v___x_2722_);
v___x_2724_ = l_Lean_mkAppB(v___x_2723_, v_a_2712_, v_a_2720_);
v___x_2725_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2701_, v___x_2724_, v___y_2704_);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v___x_2725_, 0);
lean_dec(v_unused_2734_);
v___x_2727_ = v___x_2725_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v___x_2725_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = l_Lean_Expr_mvarId_x21(v_a_2720_);
lean_dec(v_a_2720_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2729_);
v___x_2731_ = v___x_2727_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2714_);
lean_dec(v_a_2712_);
lean_dec(v_mvarId_2701_);
v_a_2735_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2719_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2719_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2714_);
lean_dec(v_a_2712_);
lean_dec(v_mvarId_2701_);
v_a_2743_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2715_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2715_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2712_);
lean_dec(v_mvarId_2701_);
v_a_2751_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2713_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2713_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_mvarId_2701_);
v_a_2759_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2709_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2709_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_mvarId_2701_);
v_a_2767_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2708_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2708_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2775_, lean_object* v___x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2775_, v___x_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; 
v___x_2792_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2786_);
v___f_2793_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2793_, 0, v_mvarId_2786_);
lean_closure_set(v___f_2793_, 1, v___x_2792_);
v___x_2794_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2786_, v___f_2793_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_MVarId_exfalso(v_mvarId_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
return v_res_2801_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2806_ = l_Lean_MessageData_ofFormat(v___x_2805_);
return v___x_2806_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2813_, lean_object* v_name_2814_, lean_object* v_idx_2815_, lean_object* v_expected_x3f_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___x_2829_; 
lean_inc(v_name_2814_);
lean_inc(v_goal_2813_);
v___x_2829_ = l_Lean_MVarId_checkNotAssigned(v_goal_2813_, v_name_2814_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v___x_2830_; 
lean_dec_ref(v___x_2829_);
lean_inc(v_goal_2813_);
v___x_2830_ = l_Lean_MVarId_getType_x27(v_goal_2813_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = l_Lean_Expr_getAppFn(v_a_2831_);
lean_dec(v_a_2831_);
if (lean_obj_tag(v___x_2832_) == 4)
{
lean_object* v_declName_2833_; lean_object* v_us_2834_; lean_object* v___x_2835_; lean_object* v_env_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; 
v_declName_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_declName_2833_);
v_us_2834_ = lean_ctor_get(v___x_2832_, 1);
lean_inc(v_us_2834_);
lean_dec_ref(v___x_2832_);
v___x_2835_ = lean_st_ref_get(v___y_2820_);
v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2836_);
lean_dec(v___x_2835_);
v___x_2837_ = 0;
v___x_2838_ = l_Lean_Environment_find_x3f(v_env_2836_, v_declName_2833_, v___x_2837_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec(v_us_2834_);
lean_dec(v_expected_x3f_2816_);
lean_dec(v_idx_2815_);
v___y_2823_ = v___y_2817_;
v___y_2824_ = v___y_2818_;
v___y_2825_ = v___y_2819_;
v___y_2826_ = v___y_2820_;
goto v___jp_2822_;
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2909_; 
v_val_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2909_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2909_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
if (lean_obj_tag(v_val_2839_) == 5)
{
lean_object* v_val_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2908_; 
v_val_2843_ = lean_ctor_get(v_val_2839_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_val_2839_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2845_ = v_val_2839_;
v_isShared_2846_ = v_isSharedCheck_2908_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_val_2843_);
lean_dec(v_val_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2908_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; 
if (lean_obj_tag(v_expected_x3f_2816_) == 1)
{
lean_object* v_val_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2907_; 
v_val_2878_ = lean_ctor_get(v_expected_x3f_2816_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_expected_x3f_2816_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2880_ = v_expected_x3f_2816_;
v_isShared_2881_ = v_isSharedCheck_2907_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_val_2878_);
lean_dec(v_expected_x3f_2816_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2907_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_ctors_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v_ctors_2882_ = lean_ctor_get(v_val_2843_, 4);
v___x_2883_ = l_List_lengthTR___redArg(v_ctors_2882_);
v___x_2884_ = lean_nat_dec_eq(v___x_2883_, v_val_2878_);
lean_dec(v___x_2883_);
if (v___x_2884_ == 0)
{
uint8_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2885_ = 1;
lean_inc(v_name_2814_);
v___x_2886_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2814_, v___x_2885_);
v___x_2887_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
v___x_2889_ = l_Nat_reprFast(v_val_2878_);
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofFormat(v___x_2893_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2894_);
v___x_2896_ = v___x_2880_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; 
lean_inc(v_goal_2813_);
lean_inc(v_name_2814_);
v___x_2897_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2814_, v_goal_2813_, v___x_2896_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref(v___x_2897_);
v___y_2848_ = v___y_2817_;
v___y_2849_ = v___y_2818_;
v___y_2850_ = v___y_2819_;
v___y_2851_ = v___y_2820_;
goto v___jp_2847_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_del_object(v___x_2845_);
lean_dec_ref(v_val_2843_);
lean_del_object(v___x_2841_);
lean_dec(v_us_2834_);
lean_dec(v_idx_2815_);
lean_dec(v_name_2814_);
lean_dec(v_goal_2813_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
lean_del_object(v___x_2880_);
lean_dec(v_val_2878_);
v___y_2848_ = v___y_2817_;
v___y_2849_ = v___y_2818_;
v___y_2850_ = v___y_2819_;
v___y_2851_ = v___y_2820_;
goto v___jp_2847_;
}
}
}
else
{
lean_dec(v_expected_x3f_2816_);
v___y_2848_ = v___y_2817_;
v___y_2849_ = v___y_2818_;
v___y_2850_ = v___y_2819_;
v___y_2851_ = v___y_2820_;
goto v___jp_2847_;
}
v___jp_2847_:
{
lean_object* v_ctors_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_ctors_2852_ = lean_ctor_get(v_val_2843_, 4);
lean_inc(v_ctors_2852_);
lean_dec_ref(v_val_2843_);
v___x_2853_ = l_List_lengthTR___redArg(v_ctors_2852_);
v___x_2854_ = lean_nat_dec_lt(v_idx_2815_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_dec(v_ctors_2852_);
lean_dec(v_us_2834_);
v___x_2855_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2856_ = l_Nat_reprFast(v_idx_2815_);
v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2859_ = lean_string_append(v___x_2857_, v___x_2858_);
v___x_2860_ = l_Nat_reprFast(v___x_2853_);
v___x_2861_ = lean_string_append(v___x_2859_, v___x_2860_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2863_ = lean_string_append(v___x_2861_, v___x_2862_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 3);
lean_ctor_set(v___x_2845_, 0, v___x_2863_);
v___x_2865_ = v___x_2845_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2866_ = l_Lean_MessageData_ofFormat(v___x_2865_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2866_);
v___x_2868_ = v___x_2841_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2814_, v_goal_2813_, v___x_2868_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2869_;
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v___x_2853_);
lean_del_object(v___x_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_name_2814_);
v___x_2872_ = l_List_get___redArg(v_ctors_2852_, v_idx_2815_);
lean_dec(v_ctors_2852_);
v___x_2873_ = l_Lean_mkConst(v___x_2872_, v_us_2834_);
v___x_2874_ = 0;
v___x_2875_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2875_, 0, v___x_2874_);
lean_ctor_set_uint8(v___x_2875_, 1, v___x_2854_);
lean_ctor_set_uint8(v___x_2875_, 2, v___x_2837_);
lean_ctor_set_uint8(v___x_2875_, 3, v___x_2854_);
v___x_2876_ = lean_box(0);
v___x_2877_ = l_Lean_MVarId_apply(v_goal_2813_, v___x_2873_, v___x_2875_, v___x_2876_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2877_;
}
}
}
}
else
{
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec(v_us_2834_);
lean_dec(v_expected_x3f_2816_);
lean_dec(v_idx_2815_);
v___y_2823_ = v___y_2817_;
v___y_2824_ = v___y_2818_;
v___y_2825_ = v___y_2819_;
v___y_2826_ = v___y_2820_;
goto v___jp_2822_;
}
}
}
}
else
{
lean_dec_ref(v___x_2832_);
lean_dec(v_expected_x3f_2816_);
lean_dec(v_idx_2815_);
v___y_2823_ = v___y_2817_;
v___y_2824_ = v___y_2818_;
v___y_2825_ = v___y_2819_;
v___y_2826_ = v___y_2820_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_expected_x3f_2816_);
lean_dec(v_idx_2815_);
lean_dec(v_name_2814_);
lean_dec(v_goal_2813_);
v_a_2910_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2830_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2830_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_expected_x3f_2816_);
lean_dec(v_idx_2815_);
lean_dec(v_name_2814_);
lean_dec(v_goal_2813_);
v_a_2918_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2829_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2829_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
v___jp_2822_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2828_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2814_, v_goal_2813_, v___x_2827_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2926_, lean_object* v_name_2927_, lean_object* v_idx_2928_, lean_object* v_expected_x3f_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2926_, v_name_2927_, v_idx_2928_, v_expected_x3f_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2936_, lean_object* v_idx_2937_, lean_object* v_expected_x3f_2938_, lean_object* v_goal_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___f_2945_; lean_object* v___x_2946_; 
lean_inc(v_goal_2939_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2945_, 0, v_goal_2939_);
lean_closure_set(v___f_2945_, 1, v_name_2936_);
lean_closure_set(v___f_2945_, 2, v_idx_2937_);
lean_closure_set(v___f_2945_, 3, v_expected_x3f_2938_);
v___x_2946_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2939_, v___f_2945_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2947_, lean_object* v_idx_2948_, lean_object* v_expected_x3f_2949_, lean_object* v_goal_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_MVarId_nthConstructor(v_name_2947_, v_idx_2948_, v_expected_x3f_2949_, v_goal_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Meta_saveState___redArg(v___y_2959_, v___y_2961_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
v___x_2965_ = lean_apply_5(v_x_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2964_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_a_2966_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2970_);
v___x_2972_ = v___x_2968_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3004_; 
v_a_2975_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2977_ = v___x_2965_;
v_isShared_2978_ = v_isSharedCheck_3004_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2965_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3004_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
uint8_t v___y_2980_; uint8_t v___x_3002_; 
v___x_3002_ = l_Lean_Exception_isInterrupt(v_a_2975_);
if (v___x_3002_ == 0)
{
uint8_t v___x_3003_; 
lean_inc(v_a_2975_);
v___x_3003_ = l_Lean_Exception_isRuntime(v_a_2975_);
v___y_2980_ = v___x_3003_;
goto v___jp_2979_;
}
else
{
v___y_2980_ = v___x_3002_;
goto v___jp_2979_;
}
v___jp_2979_:
{
if (v___y_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_del_object(v___x_2977_);
lean_dec(v_a_2975_);
v___x_2981_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2964_, v___y_2959_, v___y_2961_);
lean_dec(v_a_2964_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2990_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_box(0);
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
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2991_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2981_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2981_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
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
else
{
lean_object* v___x_3000_; 
lean_dec(v_a_2964_);
if (v_isShared_2978_ == 0)
{
v___x_3000_ = v___x_2977_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2975_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_x_2957_);
v_a_3005_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2963_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2963_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3028_, lean_object* v_x_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3028_, v_x_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3035_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3038_ = l_Lean_stringToMessageData(v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3039_, lean_object* v___x_3040_, lean_object* v___x_3041_, lean_object* v___x_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_MVarId_apply(v_mvarId_3039_, v___x_3040_, v___x_3041_, v___x_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3065_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3065_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3065_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; 
if (lean_obj_tag(v_a_3049_) == 1)
{
lean_object* v_tail_3060_; 
v_tail_3060_ = lean_ctor_get(v_a_3049_, 1);
if (lean_obj_tag(v_tail_3060_) == 0)
{
lean_object* v_head_3061_; lean_object* v___x_3063_; 
v_head_3061_ = lean_ctor_get(v_a_3049_, 0);
lean_inc(v_head_3061_);
lean_dec_ref(v_a_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_head_3061_);
v___x_3063_ = v___x_3051_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_head_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_dec_ref(v_a_3049_);
lean_del_object(v___x_3051_);
v___y_3054_ = v___y_3043_;
v___y_3055_ = v___y_3044_;
v___y_3056_ = v___y_3045_;
v___y_3057_ = v___y_3046_;
goto v___jp_3053_;
}
}
else
{
lean_del_object(v___x_3051_);
lean_dec(v_a_3049_);
v___y_3054_ = v___y_3043_;
v___y_3055_ = v___y_3044_;
v___y_3056_ = v___y_3045_;
v___y_3057_ = v___y_3046_;
goto v___jp_3053_;
}
v___jp_3053_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3059_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3058_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
return v___x_3059_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3048_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3048_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3074_, lean_object* v___x_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3074_, v___x_3075_, v___x_3076_, v___x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
return v_res_3083_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = lean_box(0);
v___x_3088_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3089_ = l_Lean_mkConst(v___x_3088_, v___x_3087_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; 
v___x_3100_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3101_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3102_ = lean_box(0);
lean_inc(v_mvarId_3094_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3103_, 0, v_mvarId_3094_);
lean_closure_set(v___f_3103_, 1, v___x_3100_);
lean_closure_set(v___f_3103_, 2, v___x_3101_);
lean_closure_set(v___f_3103_, 3, v___x_3102_);
v___x_3104_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3103_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3116_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
if (lean_obj_tag(v_a_3105_) == 0)
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v_mvarId_3094_);
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_mvarId_3094_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
else
{
lean_object* v_val_3112_; lean_object* v___x_3114_; 
lean_dec(v_mvarId_3094_);
v_val_3112_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_val_3112_);
lean_dec_ref(v_a_3105_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v_val_3112_);
v___x_3114_ = v___x_3107_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_val_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_mvarId_3094_);
v_a_3117_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3104_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3104_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_MVarId_iffOfEq(v_mvarId_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
return v_res_3131_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3140_ = l_Lean_mkConst(v___x_3139_, v___x_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3141_, lean_object* v_mvarId_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___x_3155_; uint8_t v_foApprox_3156_; uint8_t v_ctxApprox_3157_; uint8_t v_quasiPatternApprox_3158_; uint8_t v_constApprox_3159_; uint8_t v_isDefEqStuckEx_3160_; uint8_t v_unificationHints_3161_; uint8_t v_proofIrrelevance_3162_; uint8_t v_assignSyntheticOpaque_3163_; uint8_t v_offsetCnstrs_3164_; uint8_t v_etaStruct_3165_; uint8_t v_univApprox_3166_; uint8_t v_iota_3167_; uint8_t v_beta_3168_; uint8_t v_proj_3169_; uint8_t v_zeta_3170_; uint8_t v_zetaDelta_3171_; uint8_t v_zetaUnused_3172_; uint8_t v_zetaHave_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3261_; 
v___x_3155_ = l_Lean_Meta_Context_config(v___y_3143_);
v_foApprox_3156_ = lean_ctor_get_uint8(v___x_3155_, 0);
v_ctxApprox_3157_ = lean_ctor_get_uint8(v___x_3155_, 1);
v_quasiPatternApprox_3158_ = lean_ctor_get_uint8(v___x_3155_, 2);
v_constApprox_3159_ = lean_ctor_get_uint8(v___x_3155_, 3);
v_isDefEqStuckEx_3160_ = lean_ctor_get_uint8(v___x_3155_, 4);
v_unificationHints_3161_ = lean_ctor_get_uint8(v___x_3155_, 5);
v_proofIrrelevance_3162_ = lean_ctor_get_uint8(v___x_3155_, 6);
v_assignSyntheticOpaque_3163_ = lean_ctor_get_uint8(v___x_3155_, 7);
v_offsetCnstrs_3164_ = lean_ctor_get_uint8(v___x_3155_, 8);
v_etaStruct_3165_ = lean_ctor_get_uint8(v___x_3155_, 10);
v_univApprox_3166_ = lean_ctor_get_uint8(v___x_3155_, 11);
v_iota_3167_ = lean_ctor_get_uint8(v___x_3155_, 12);
v_beta_3168_ = lean_ctor_get_uint8(v___x_3155_, 13);
v_proj_3169_ = lean_ctor_get_uint8(v___x_3155_, 14);
v_zeta_3170_ = lean_ctor_get_uint8(v___x_3155_, 15);
v_zetaDelta_3171_ = lean_ctor_get_uint8(v___x_3155_, 16);
v_zetaUnused_3172_ = lean_ctor_get_uint8(v___x_3155_, 17);
v_zetaHave_3173_ = lean_ctor_get_uint8(v___x_3155_, 18);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3175_ = v___x_3155_;
v_isShared_3176_ = v_isSharedCheck_3261_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3155_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3261_;
goto v_resetjp_3174_;
}
v___jp_3148_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3154_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3153_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3154_;
}
v_resetjp_3174_:
{
uint8_t v_trackZetaDelta_3177_; lean_object* v_zetaDeltaSet_3178_; lean_object* v_lctx_3179_; lean_object* v_localInstances_3180_; lean_object* v_defEqCtx_x3f_3181_; lean_object* v_synthPendingDepth_3182_; lean_object* v_canUnfold_x3f_3183_; uint8_t v_univApprox_3184_; uint8_t v_inTypeClassResolution_3185_; uint8_t v_cacheInferType_3186_; lean_object* v_config_3188_; 
v_trackZetaDelta_3177_ = lean_ctor_get_uint8(v___y_3143_, sizeof(void*)*7);
v_zetaDeltaSet_3178_ = lean_ctor_get(v___y_3143_, 1);
v_lctx_3179_ = lean_ctor_get(v___y_3143_, 2);
v_localInstances_3180_ = lean_ctor_get(v___y_3143_, 3);
v_defEqCtx_x3f_3181_ = lean_ctor_get(v___y_3143_, 4);
v_synthPendingDepth_3182_ = lean_ctor_get(v___y_3143_, 5);
v_canUnfold_x3f_3183_ = lean_ctor_get(v___y_3143_, 6);
v_univApprox_3184_ = lean_ctor_get_uint8(v___y_3143_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3185_ = lean_ctor_get_uint8(v___y_3143_, sizeof(void*)*7 + 2);
v_cacheInferType_3186_ = lean_ctor_get_uint8(v___y_3143_, sizeof(void*)*7 + 3);
if (v_isShared_3176_ == 0)
{
v_config_3188_ = v___x_3175_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 0, v_foApprox_3156_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 1, v_ctxApprox_3157_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 2, v_quasiPatternApprox_3158_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 3, v_constApprox_3159_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 4, v_isDefEqStuckEx_3160_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 5, v_unificationHints_3161_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 6, v_proofIrrelevance_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 7, v_assignSyntheticOpaque_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 8, v_offsetCnstrs_3164_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 10, v_etaStruct_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 11, v_univApprox_3166_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 12, v_iota_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 13, v_beta_3168_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 14, v_proj_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 15, v_zeta_3170_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 16, v_zetaDelta_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 17, v_zetaUnused_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3260_, 18, v_zetaHave_3173_);
v_config_3188_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
uint64_t v___x_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v___x_3192_; uint64_t v___x_3193_; uint64_t v_key_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_ctor_set_uint8(v_config_3188_, 9, v___x_3141_);
v___x_3189_ = l_Lean_Meta_Context_configKey(v___y_3143_);
v___x_3190_ = 2ULL;
v___x_3191_ = lean_uint64_shift_right(v___x_3189_, v___x_3190_);
v___x_3192_ = lean_uint64_shift_left(v___x_3191_, v___x_3190_);
v___x_3193_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3141_);
v_key_3194_ = lean_uint64_lor(v___x_3192_, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3195_, 0, v_config_3188_);
lean_ctor_set_uint64(v___x_3195_, sizeof(void*)*1, v_key_3194_);
lean_inc(v_canUnfold_x3f_3183_);
lean_inc(v_synthPendingDepth_3182_);
lean_inc(v_defEqCtx_x3f_3181_);
lean_inc_ref(v_localInstances_3180_);
lean_inc_ref(v_lctx_3179_);
lean_inc(v_zetaDeltaSet_3178_);
v___x_3196_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v_zetaDeltaSet_3178_);
lean_ctor_set(v___x_3196_, 2, v_lctx_3179_);
lean_ctor_set(v___x_3196_, 3, v_localInstances_3180_);
lean_ctor_set(v___x_3196_, 4, v_defEqCtx_x3f_3181_);
lean_ctor_set(v___x_3196_, 5, v_synthPendingDepth_3182_);
lean_ctor_set(v___x_3196_, 6, v_canUnfold_x3f_3183_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7, v_trackZetaDelta_3177_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 1, v_univApprox_3184_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3185_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 3, v_cacheInferType_3186_);
lean_inc(v_mvarId_3142_);
v___x_3197_ = l_Lean_MVarId_getType_x27(v_mvarId_3142_, v___x_3196_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v___x_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3200_ = lean_unsigned_to_nat(3u);
v___x_3201_ = l_Lean_Expr_isAppOfArity(v_a_3198_, v___x_3199_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_dec(v_a_3198_);
lean_dec(v_mvarId_3142_);
v___x_3227_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3228_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3227_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = l_Lean_Expr_appFn_x21(v_a_3198_);
lean_dec(v_a_3198_);
v___x_3230_ = l_Lean_Expr_appArg_x21(v___x_3229_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = l_Lean_Meta_isProp(v___x_3230_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; uint8_t v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = lean_unbox(v_a_3232_);
lean_dec(v_a_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_mvarId_3142_);
v___x_3234_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3235_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3234_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
goto v___jp_3202_;
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_mvarId_3142_);
v_a_3244_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3231_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3231_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
v___jp_3202_:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3203_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3204_ = 0;
v___x_3205_ = 0;
v___x_3206_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3206_, 0, v___x_3204_);
lean_ctor_set_uint8(v___x_3206_, 1, v___x_3201_);
lean_ctor_set_uint8(v___x_3206_, 2, v___x_3205_);
lean_ctor_set_uint8(v___x_3206_, 3, v___x_3201_);
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_MVarId_apply(v_mvarId_3142_, v___x_3203_, v___x_3206_, v___x_3207_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3218_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
if (lean_obj_tag(v_a_3209_) == 1)
{
lean_object* v_tail_3213_; 
v_tail_3213_ = lean_ctor_get(v_a_3209_, 1);
if (lean_obj_tag(v_tail_3213_) == 0)
{
lean_object* v_head_3214_; lean_object* v___x_3216_; 
v_head_3214_ = lean_ctor_get(v_a_3209_, 0);
lean_inc(v_head_3214_);
lean_dec_ref(v_a_3209_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v_head_3214_);
v___x_3216_ = v___x_3211_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_head_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
else
{
lean_dec_ref(v_a_3209_);
lean_del_object(v___x_3211_);
v___y_3149_ = v___y_3143_;
v___y_3150_ = v___y_3144_;
v___y_3151_ = v___y_3145_;
v___y_3152_ = v___y_3146_;
goto v___jp_3148_;
}
}
else
{
lean_del_object(v___x_3211_);
lean_dec(v_a_3209_);
v___y_3149_ = v___y_3143_;
v___y_3150_ = v___y_3144_;
v___y_3151_ = v___y_3145_;
v___y_3152_ = v___y_3146_;
goto v___jp_3148_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
v_a_3219_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3208_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3208_);
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
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_mvarId_3142_);
v_a_3252_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3197_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3197_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3262_, lean_object* v_mvarId_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
uint8_t v___x_2435__boxed_3269_; lean_object* v_res_3270_; 
v___x_2435__boxed_3269_ = lean_unbox(v___x_3262_);
v_res_3270_ = l_Lean_MVarId_propext___lam__0(v___x_2435__boxed_3269_, v_mvarId_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v___x_3277_ = 2;
v___x_3278_ = lean_box(v___x_3277_);
lean_inc(v_mvarId_3271_);
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3279_, 0, v___x_3278_);
lean_closure_set(v___f_3279_, 1, v_mvarId_3271_);
v___x_3280_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3279_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3292_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
if (lean_obj_tag(v_a_3281_) == 0)
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_mvarId_3271_);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_mvarId_3271_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
else
{
lean_object* v_val_3288_; lean_object* v___x_3290_; 
lean_dec(v_mvarId_3271_);
v_val_3288_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_val_3288_);
lean_dec_ref(v_a_3281_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_val_3288_);
v___x_3290_ = v___x_3283_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_val_3288_);
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
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v_mvarId_3271_);
v_a_3293_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3280_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3280_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_MVarId_propext(v_mvarId_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
return v_res_3307_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3308_; uint64_t v___x_3309_; 
v___x_3308_ = 2;
v___x_3309_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3316_, lean_object* v___x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
lean_inc(v_mvarId_3316_);
v___x_3323_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3316_, v___x_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; uint8_t v_foApprox_3325_; uint8_t v_ctxApprox_3326_; uint8_t v_quasiPatternApprox_3327_; uint8_t v_constApprox_3328_; uint8_t v_isDefEqStuckEx_3329_; uint8_t v_unificationHints_3330_; uint8_t v_proofIrrelevance_3331_; uint8_t v_assignSyntheticOpaque_3332_; uint8_t v_offsetCnstrs_3333_; uint8_t v_etaStruct_3334_; uint8_t v_univApprox_3335_; uint8_t v_iota_3336_; uint8_t v_beta_3337_; uint8_t v_proj_3338_; uint8_t v_zeta_3339_; uint8_t v_zetaDelta_3340_; uint8_t v_zetaUnused_3341_; uint8_t v_zetaHave_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3412_; 
lean_dec_ref(v___x_3323_);
v___x_3324_ = l_Lean_Meta_Context_config(v___y_3318_);
v_foApprox_3325_ = lean_ctor_get_uint8(v___x_3324_, 0);
v_ctxApprox_3326_ = lean_ctor_get_uint8(v___x_3324_, 1);
v_quasiPatternApprox_3327_ = lean_ctor_get_uint8(v___x_3324_, 2);
v_constApprox_3328_ = lean_ctor_get_uint8(v___x_3324_, 3);
v_isDefEqStuckEx_3329_ = lean_ctor_get_uint8(v___x_3324_, 4);
v_unificationHints_3330_ = lean_ctor_get_uint8(v___x_3324_, 5);
v_proofIrrelevance_3331_ = lean_ctor_get_uint8(v___x_3324_, 6);
v_assignSyntheticOpaque_3332_ = lean_ctor_get_uint8(v___x_3324_, 7);
v_offsetCnstrs_3333_ = lean_ctor_get_uint8(v___x_3324_, 8);
v_etaStruct_3334_ = lean_ctor_get_uint8(v___x_3324_, 10);
v_univApprox_3335_ = lean_ctor_get_uint8(v___x_3324_, 11);
v_iota_3336_ = lean_ctor_get_uint8(v___x_3324_, 12);
v_beta_3337_ = lean_ctor_get_uint8(v___x_3324_, 13);
v_proj_3338_ = lean_ctor_get_uint8(v___x_3324_, 14);
v_zeta_3339_ = lean_ctor_get_uint8(v___x_3324_, 15);
v_zetaDelta_3340_ = lean_ctor_get_uint8(v___x_3324_, 16);
v_zetaUnused_3341_ = lean_ctor_get_uint8(v___x_3324_, 17);
v_zetaHave_3342_ = lean_ctor_get_uint8(v___x_3324_, 18);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3344_ = v___x_3324_;
v_isShared_3345_ = v_isSharedCheck_3412_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v___x_3324_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3412_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
uint8_t v_trackZetaDelta_3346_; lean_object* v_zetaDeltaSet_3347_; lean_object* v_lctx_3348_; lean_object* v_localInstances_3349_; lean_object* v_defEqCtx_x3f_3350_; lean_object* v_synthPendingDepth_3351_; lean_object* v_canUnfold_x3f_3352_; uint8_t v_univApprox_3353_; uint8_t v_inTypeClassResolution_3354_; uint8_t v_cacheInferType_3355_; uint8_t v___x_3356_; lean_object* v_config_3358_; 
v_trackZetaDelta_3346_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*7);
v_zetaDeltaSet_3347_ = lean_ctor_get(v___y_3318_, 1);
v_lctx_3348_ = lean_ctor_get(v___y_3318_, 2);
v_localInstances_3349_ = lean_ctor_get(v___y_3318_, 3);
v_defEqCtx_x3f_3350_ = lean_ctor_get(v___y_3318_, 4);
v_synthPendingDepth_3351_ = lean_ctor_get(v___y_3318_, 5);
v_canUnfold_x3f_3352_ = lean_ctor_get(v___y_3318_, 6);
v_univApprox_3353_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3354_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*7 + 2);
v_cacheInferType_3355_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*7 + 3);
v___x_3356_ = 2;
if (v_isShared_3345_ == 0)
{
v_config_3358_ = v___x_3344_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 0, v_foApprox_3325_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 1, v_ctxApprox_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 2, v_quasiPatternApprox_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 3, v_constApprox_3328_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 4, v_isDefEqStuckEx_3329_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 5, v_unificationHints_3330_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 6, v_proofIrrelevance_3331_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 7, v_assignSyntheticOpaque_3332_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 8, v_offsetCnstrs_3333_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 10, v_etaStruct_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 11, v_univApprox_3335_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 12, v_iota_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 13, v_beta_3337_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 14, v_proj_3338_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 15, v_zeta_3339_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 16, v_zetaDelta_3340_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 17, v_zetaUnused_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, 18, v_zetaHave_3342_);
v_config_3358_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
uint64_t v___x_3359_; uint64_t v___x_3360_; uint64_t v___x_3361_; uint64_t v___x_3362_; uint64_t v___x_3363_; uint64_t v_key_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_ctor_set_uint8(v_config_3358_, 9, v___x_3356_);
v___x_3359_ = l_Lean_Meta_Context_configKey(v___y_3318_);
v___x_3360_ = 2ULL;
v___x_3361_ = lean_uint64_shift_right(v___x_3359_, v___x_3360_);
v___x_3362_ = lean_uint64_shift_left(v___x_3361_, v___x_3360_);
v___x_3363_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3364_ = lean_uint64_lor(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3365_, 0, v_config_3358_);
lean_ctor_set_uint64(v___x_3365_, sizeof(void*)*1, v_key_3364_);
lean_inc(v_canUnfold_x3f_3352_);
lean_inc(v_synthPendingDepth_3351_);
lean_inc(v_defEqCtx_x3f_3350_);
lean_inc_ref(v_localInstances_3349_);
lean_inc_ref(v_lctx_3348_);
lean_inc(v_zetaDeltaSet_3347_);
v___x_3366_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_zetaDeltaSet_3347_);
lean_ctor_set(v___x_3366_, 2, v_lctx_3348_);
lean_ctor_set(v___x_3366_, 3, v_localInstances_3349_);
lean_ctor_set(v___x_3366_, 4, v_defEqCtx_x3f_3350_);
lean_ctor_set(v___x_3366_, 5, v_synthPendingDepth_3351_);
lean_ctor_set(v___x_3366_, 6, v_canUnfold_x3f_3352_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7, v_trackZetaDelta_3346_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 1, v_univApprox_3353_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3354_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*7 + 3, v_cacheInferType_3355_);
lean_inc(v_mvarId_3316_);
v___x_3367_ = l_Lean_MVarId_getType_x27(v_mvarId_3316_, v___x_3366_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec_ref(v___x_3366_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3370_ = lean_unsigned_to_nat(4u);
v___x_3371_ = l_Lean_Expr_isAppOfArity(v_a_3368_, v___x_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec(v_a_3368_);
lean_dec(v_mvarId_3316_);
v___x_3372_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3373_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3372_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v___x_3373_;
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3374_ = l_Lean_Expr_appFn_x21(v_a_3368_);
v___x_3375_ = l_Lean_Expr_appFn_x21(v___x_3374_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = l_Lean_Expr_appArg_x21(v___x_3375_);
lean_dec_ref(v___x_3375_);
v___x_3377_ = l_Lean_Expr_appArg_x21(v_a_3368_);
lean_dec(v_a_3368_);
v___x_3378_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3379_ = lean_unsigned_to_nat(2u);
v___x_3380_ = lean_mk_empty_array_with_capacity(v___x_3379_);
v___x_3381_ = lean_array_push(v___x_3380_, v___x_3376_);
v___x_3382_ = lean_array_push(v___x_3381_, v___x_3377_);
v___x_3383_ = l_Lean_Meta_mkAppM(v___x_3378_, v___x_3382_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3393_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref(v___x_3383_);
v___x_3385_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3316_, v_a_3384_, v___y_3319_);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3385_, 0);
lean_dec(v_unused_3394_);
v___x_3387_ = v___x_3385_;
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v___x_3385_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_box(v___x_3371_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3389_);
v___x_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v_mvarId_3316_);
v_a_3395_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3383_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3383_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_mvarId_3316_);
v_a_3403_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3367_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3367_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_mvarId_3316_);
v_a_3413_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3323_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3323_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3421_, lean_object* v___x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3421_, v___x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3449_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_a_3436_) == 0)
{
uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = 0;
v___x_3441_ = lean_box(v___x_3440_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
else
{
lean_object* v_val_3445_; lean_object* v___x_3447_; 
v_val_3445_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_val_3445_);
lean_dec_ref(v_a_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_val_3445_);
v___x_3447_ = v___x_3438_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_val_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3435_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3435_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v___x_3474_; lean_object* v___f_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; 
v___x_3474_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3468_);
v___f_3475_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3475_, 0, v_mvarId_3468_);
lean_closure_set(v___f_3475_, 1, v___x_3474_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3476_, 0, v___f_3475_);
v___x_3477_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3468_, v___f_3476_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3489_, lean_object* v___x_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
lean_inc(v_mvarId_3489_);
v___x_3496_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3489_, v___x_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v___x_3497_; uint8_t v_foApprox_3498_; uint8_t v_ctxApprox_3499_; uint8_t v_quasiPatternApprox_3500_; uint8_t v_constApprox_3501_; uint8_t v_isDefEqStuckEx_3502_; uint8_t v_unificationHints_3503_; uint8_t v_proofIrrelevance_3504_; uint8_t v_assignSyntheticOpaque_3505_; uint8_t v_offsetCnstrs_3506_; uint8_t v_etaStruct_3507_; uint8_t v_univApprox_3508_; uint8_t v_iota_3509_; uint8_t v_beta_3510_; uint8_t v_proj_3511_; uint8_t v_zeta_3512_; uint8_t v_zetaDelta_3513_; uint8_t v_zetaUnused_3514_; uint8_t v_zetaHave_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___x_3496_);
v___x_3497_ = l_Lean_Meta_Context_config(v___y_3491_);
v_foApprox_3498_ = lean_ctor_get_uint8(v___x_3497_, 0);
v_ctxApprox_3499_ = lean_ctor_get_uint8(v___x_3497_, 1);
v_quasiPatternApprox_3500_ = lean_ctor_get_uint8(v___x_3497_, 2);
v_constApprox_3501_ = lean_ctor_get_uint8(v___x_3497_, 3);
v_isDefEqStuckEx_3502_ = lean_ctor_get_uint8(v___x_3497_, 4);
v_unificationHints_3503_ = lean_ctor_get_uint8(v___x_3497_, 5);
v_proofIrrelevance_3504_ = lean_ctor_get_uint8(v___x_3497_, 6);
v_assignSyntheticOpaque_3505_ = lean_ctor_get_uint8(v___x_3497_, 7);
v_offsetCnstrs_3506_ = lean_ctor_get_uint8(v___x_3497_, 8);
v_etaStruct_3507_ = lean_ctor_get_uint8(v___x_3497_, 10);
v_univApprox_3508_ = lean_ctor_get_uint8(v___x_3497_, 11);
v_iota_3509_ = lean_ctor_get_uint8(v___x_3497_, 12);
v_beta_3510_ = lean_ctor_get_uint8(v___x_3497_, 13);
v_proj_3511_ = lean_ctor_get_uint8(v___x_3497_, 14);
v_zeta_3512_ = lean_ctor_get_uint8(v___x_3497_, 15);
v_zetaDelta_3513_ = lean_ctor_get_uint8(v___x_3497_, 16);
v_zetaUnused_3514_ = lean_ctor_get_uint8(v___x_3497_, 17);
v_zetaHave_3515_ = lean_ctor_get_uint8(v___x_3497_, 18);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3517_ = v___x_3497_;
v_isShared_3518_ = v_isSharedCheck_3584_;
goto v_resetjp_3516_;
}
else
{
lean_dec(v___x_3497_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3584_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
uint8_t v_trackZetaDelta_3519_; lean_object* v_zetaDeltaSet_3520_; lean_object* v_lctx_3521_; lean_object* v_localInstances_3522_; lean_object* v_defEqCtx_x3f_3523_; lean_object* v_synthPendingDepth_3524_; lean_object* v_canUnfold_x3f_3525_; uint8_t v_univApprox_3526_; uint8_t v_inTypeClassResolution_3527_; uint8_t v_cacheInferType_3528_; uint8_t v___x_3529_; lean_object* v_config_3531_; 
v_trackZetaDelta_3519_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*7);
v_zetaDeltaSet_3520_ = lean_ctor_get(v___y_3491_, 1);
v_lctx_3521_ = lean_ctor_get(v___y_3491_, 2);
v_localInstances_3522_ = lean_ctor_get(v___y_3491_, 3);
v_defEqCtx_x3f_3523_ = lean_ctor_get(v___y_3491_, 4);
v_synthPendingDepth_3524_ = lean_ctor_get(v___y_3491_, 5);
v_canUnfold_x3f_3525_ = lean_ctor_get(v___y_3491_, 6);
v_univApprox_3526_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3527_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*7 + 2);
v_cacheInferType_3528_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*7 + 3);
v___x_3529_ = 2;
if (v_isShared_3518_ == 0)
{
v_config_3531_ = v___x_3517_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 0, v_foApprox_3498_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 1, v_ctxApprox_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 2, v_quasiPatternApprox_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 3, v_constApprox_3501_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 4, v_isDefEqStuckEx_3502_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 5, v_unificationHints_3503_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 6, v_proofIrrelevance_3504_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 7, v_assignSyntheticOpaque_3505_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 8, v_offsetCnstrs_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 10, v_etaStruct_3507_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 11, v_univApprox_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 12, v_iota_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 13, v_beta_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 14, v_proj_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 15, v_zeta_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 16, v_zetaDelta_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 17, v_zetaUnused_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, 18, v_zetaHave_3515_);
v_config_3531_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
uint64_t v___x_3532_; uint64_t v___x_3533_; uint64_t v___x_3534_; uint64_t v___x_3535_; uint64_t v___x_3536_; uint64_t v_key_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_ctor_set_uint8(v_config_3531_, 9, v___x_3529_);
v___x_3532_ = l_Lean_Meta_Context_configKey(v___y_3491_);
v___x_3533_ = 2ULL;
v___x_3534_ = lean_uint64_shift_right(v___x_3532_, v___x_3533_);
v___x_3535_ = lean_uint64_shift_left(v___x_3534_, v___x_3533_);
v___x_3536_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3537_ = lean_uint64_lor(v___x_3535_, v___x_3536_);
v___x_3538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3538_, 0, v_config_3531_);
lean_ctor_set_uint64(v___x_3538_, sizeof(void*)*1, v_key_3537_);
lean_inc(v_canUnfold_x3f_3525_);
lean_inc(v_synthPendingDepth_3524_);
lean_inc(v_defEqCtx_x3f_3523_);
lean_inc_ref(v_localInstances_3522_);
lean_inc_ref(v_lctx_3521_);
lean_inc(v_zetaDeltaSet_3520_);
v___x_3539_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v_zetaDeltaSet_3520_);
lean_ctor_set(v___x_3539_, 2, v_lctx_3521_);
lean_ctor_set(v___x_3539_, 3, v_localInstances_3522_);
lean_ctor_set(v___x_3539_, 4, v_defEqCtx_x3f_3523_);
lean_ctor_set(v___x_3539_, 5, v_synthPendingDepth_3524_);
lean_ctor_set(v___x_3539_, 6, v_canUnfold_x3f_3525_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*7, v_trackZetaDelta_3519_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*7 + 1, v_univApprox_3526_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3527_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*7 + 3, v_cacheInferType_3528_);
lean_inc(v_mvarId_3489_);
v___x_3540_ = l_Lean_MVarId_getType_x27(v_mvarId_3489_, v___x_3539_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___x_3539_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref(v___x_3540_);
v___x_3542_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3543_ = lean_unsigned_to_nat(3u);
v___x_3544_ = l_Lean_Expr_isAppOfArity(v_a_3541_, v___x_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v_a_3541_);
lean_dec(v_mvarId_3489_);
v___x_3545_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3546_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3545_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3547_ = l_Lean_Expr_appFn_x21(v_a_3541_);
v___x_3548_ = l_Lean_Expr_appArg_x21(v___x_3547_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = l_Lean_Expr_appArg_x21(v_a_3541_);
lean_dec(v_a_3541_);
v___x_3550_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3551_ = lean_unsigned_to_nat(2u);
v___x_3552_ = lean_mk_empty_array_with_capacity(v___x_3551_);
v___x_3553_ = lean_array_push(v___x_3552_, v___x_3548_);
v___x_3554_ = lean_array_push(v___x_3553_, v___x_3549_);
v___x_3555_ = l_Lean_Meta_mkAppM(v___x_3550_, v___x_3554_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3565_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3489_, v_a_3556_, v___y_3492_);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3557_, 0);
lean_dec(v_unused_3566_);
v___x_3559_ = v___x_3557_;
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
else
{
lean_dec(v___x_3557_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3561_ = lean_box(v___x_3544_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_mvarId_3489_);
v_a_3567_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3555_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3555_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_mvarId_3489_);
v_a_3575_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3540_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3540_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_mvarId_3489_);
v_a_3585_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3496_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3496_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3593_, lean_object* v___x_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3593_, v___x_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; 
v___x_3610_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3604_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3611_, 0, v_mvarId_3604_);
lean_closure_set(v___f_3611_, 1, v___x_3610_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3612_, 0, v___f_3611_);
v___x_3613_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3604_, v___f_3612_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
return v_res_3620_;
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
