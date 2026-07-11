// Lean compiler output
// Module: Lean.Meta.FunInfo
// Imports: public import Lean.Meta.InferType import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqInfoCacheKey_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_find_expr(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_object* l_Lean_Meta_instBEqInfoCacheKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value;
LEAN_EXPORT uint64_t l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0;
LEAN_EXPORT uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunInfo"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(112, 52, 23, 53, 37, 12, 118, 217)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 147, 169, 8, 188, 234, 221, 232)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(140, 0, 92, 209, 70, 2, 10, 135)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(176, 237, 136, 34, 252, 176, 16, 86)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "FunInfoEnvCacheKey"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value),LEAN_SCALAR_PTR_LITERAL(77, 18, 248, 164, 207, 212, 124, 226)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instTypeNameFunInfoEnvCacheKey = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value;
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqInfoCacheKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hasMVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Meta.FunInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0;
static lean_once_cell_t l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "trying to realize `"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "` value but `enableRealizationsForConst` must be called for '"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' first"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Environment.realizeConst: `realizedImportedConsts` is empty"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value;
static const lean_ctor_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value)}};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Meta.Basic"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.realizeValue"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = lean_nat_dec_eq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
if (lean_obj_tag(v_x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 1;
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
}
else
{
if (lean_obj_tag(v_x_14_) == 0)
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
else
{
lean_object* v_head_18_; lean_object* v_tail_19_; lean_object* v_head_20_; lean_object* v_tail_21_; uint8_t v___x_22_; 
v_head_18_ = lean_ctor_get(v_x_13_, 0);
v_tail_19_ = lean_ctor_get(v_x_13_, 1);
v_head_20_ = lean_ctor_get(v_x_14_, 0);
v_tail_21_ = lean_ctor_get(v_x_14_, 1);
v___x_22_ = lean_level_eq(v_head_18_, v_head_20_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
v_x_13_ = v_tail_19_;
v_x_14_ = v_tail_21_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_x_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_c_30_; lean_object* v_ls_31_; lean_object* v_maxArgs_x3f_32_; lean_object* v_c_33_; lean_object* v_ls_34_; lean_object* v_maxArgs_x3f_35_; uint8_t v___x_36_; 
v_c_30_ = lean_ctor_get(v_x_28_, 0);
v_ls_31_ = lean_ctor_get(v_x_28_, 1);
v_maxArgs_x3f_32_ = lean_ctor_get(v_x_28_, 2);
v_c_33_ = lean_ctor_get(v_x_29_, 0);
v_ls_34_ = lean_ctor_get(v_x_29_, 1);
v_maxArgs_x3f_35_ = lean_ctor_get(v_x_29_, 2);
v___x_36_ = lean_name_eq(v_c_30_, v_c_33_);
if (v___x_36_ == 0)
{
return v___x_36_;
}
else
{
uint8_t v___x_37_; 
v___x_37_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_ls_31_, v_ls_34_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_maxArgs_x3f_32_, v_maxArgs_x3f_35_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_39_, v_x_40_);
lean_dec_ref(v_x_40_);
lean_dec_ref(v_x_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(uint64_t v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
return v_x_45_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; uint64_t v___x_49_; uint64_t v___x_50_; 
v_head_47_ = lean_ctor_get(v_x_46_, 0);
v_tail_48_ = lean_ctor_get(v_x_46_, 1);
v___x_49_ = l_Lean_Level_hash(v_head_47_);
v___x_50_ = lean_uint64_mix_hash(v_x_45_, v___x_49_);
v_x_45_ = v___x_50_;
v_x_46_ = v_tail_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0___boxed(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint64_t v_x_109__boxed_54_; uint64_t v_res_55_; lean_object* v_r_56_; 
v_x_109__boxed_54_ = lean_unbox_uint64(v_x_52_);
lean_dec_ref(v_x_52_);
v_res_55_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v_x_109__boxed_54_, v_x_53_);
lean_dec(v_x_53_);
v_r_56_ = lean_box_uint64(v_res_55_);
return v_r_56_;
}
}
static uint64_t _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0(void){
_start:
{
lean_object* v___x_57_; uint64_t v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(1723u);
v___x_58_ = lean_uint64_of_nat(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(lean_object* v_x_59_){
_start:
{
lean_object* v_c_60_; lean_object* v_ls_61_; lean_object* v_maxArgs_x3f_62_; uint64_t v___x_63_; uint64_t v___y_65_; 
v_c_60_ = lean_ctor_get(v_x_59_, 0);
v_ls_61_ = lean_ctor_get(v_x_59_, 1);
v_maxArgs_x3f_62_ = lean_ctor_get(v_x_59_, 2);
v___x_63_ = 0ULL;
if (lean_obj_tag(v_c_60_) == 0)
{
uint64_t v___x_77_; 
v___x_77_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_65_ = v___x_77_;
goto v___jp_64_;
}
else
{
uint64_t v_hash_78_; 
v_hash_78_ = lean_ctor_get_uint64(v_c_60_, sizeof(void*)*2);
v___y_65_ = v_hash_78_;
goto v___jp_64_;
}
v___jp_64_:
{
uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; 
v___x_66_ = lean_uint64_mix_hash(v___x_63_, v___y_65_);
v___x_67_ = 7ULL;
v___x_68_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v___x_67_, v_ls_61_);
v___x_69_ = lean_uint64_mix_hash(v___x_66_, v___x_68_);
if (lean_obj_tag(v_maxArgs_x3f_62_) == 0)
{
uint64_t v___x_70_; uint64_t v___x_71_; 
v___x_70_ = 11ULL;
v___x_71_ = lean_uint64_mix_hash(v___x_69_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_val_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; 
v_val_72_ = lean_ctor_get(v_maxArgs_x3f_62_, 0);
v___x_73_ = lean_uint64_of_nat(v_val_72_);
v___x_74_ = 13ULL;
v___x_75_ = lean_uint64_mix_hash(v___x_73_, v___x_74_);
v___x_76_ = lean_uint64_mix_hash(v___x_69_, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(lean_object* v_x_79_){
_start:
{
uint64_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_79_);
lean_dec_ref(v_x_79_);
v_r_81_ = lean_box_uint64(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* v_fn_118_, lean_object* v_maxArgs_x3f_119_, lean_object* v_k_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; 
lean_inc(v_maxArgs_x3f_119_);
lean_inc_ref(v_fn_118_);
v___x_126_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_118_, v_maxArgs_x3f_119_, v_a_121_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_194_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_194_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_194_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_194_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v_cache_132_; lean_object* v_funInfo_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_finfo_137_; lean_object* v___y_138_; lean_object* v___x_170_; 
v___x_131_ = lean_st_ref_get(v_a_122_);
v_cache_132_ = lean_ctor_get(v___x_131_, 1);
lean_inc_ref(v_cache_132_);
lean_dec(v___x_131_);
v_funInfo_133_ = lean_ctor_get(v_cache_132_, 1);
lean_inc_ref(v_funInfo_133_);
lean_dec_ref(v_cache_132_);
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0));
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1));
lean_inc(v_a_127_);
v___x_170_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_134_, v___x_135_, v_funInfo_133_, v_a_127_);
lean_dec_ref(v_funInfo_133_);
if (lean_obj_tag(v___x_170_) == 0)
{
if (lean_obj_tag(v_fn_118_) == 4)
{
lean_object* v_declName_171_; lean_object* v_us_172_; lean_object* v___f_173_; uint8_t v___x_174_; 
v_declName_171_ = lean_ctor_get(v_fn_118_, 0);
lean_inc(v_declName_171_);
v_us_172_ = lean_ctor_get(v_fn_118_, 1);
lean_inc_n(v_us_172_, 2);
lean_dec_ref_known(v_fn_118_, 2);
v___f_173_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
v___x_174_ = l_List_any___redArg(v_us_172_, v___f_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0));
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0));
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_178_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_inc(v_declName_171_);
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v_declName_171_);
lean_ctor_set(v___x_179_, 1, v_us_172_);
lean_ctor_set(v___x_179_, 2, v_maxArgs_x3f_119_);
v___x_180_ = l_Lean_Meta_realizeValue___redArg(v___x_175_, v___x_176_, v___x_177_, v___x_178_, v_declName_171_, v___x_179_, v_k_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v_finfo_137_ = v_a_181_;
v___y_138_ = v_a_122_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_129_);
lean_dec(v_a_127_);
return v___x_180_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_us_172_);
lean_dec(v_declName_171_);
lean_dec(v_maxArgs_x3f_119_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
v___x_182_ = lean_apply_5(v_k_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, lean_box(0));
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v_finfo_137_ = v_a_183_;
v___y_138_ = v_a_122_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_129_);
lean_dec(v_a_127_);
return v___x_182_;
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v_maxArgs_x3f_119_);
lean_dec_ref(v_fn_118_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
v___x_184_ = lean_apply_5(v_k_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, lean_box(0));
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v_finfo_137_ = v_a_185_;
v___y_138_ = v_a_122_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_129_);
lean_dec(v_a_127_);
return v___x_184_;
}
}
}
else
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_del_object(v___x_129_);
lean_dec(v_a_127_);
lean_dec_ref(v_k_120_);
lean_dec(v_maxArgs_x3f_119_);
lean_dec_ref(v_fn_118_);
v_val_186_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_170_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_val_186_);
lean_dec(v___x_170_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 0);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_val_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
v___jp_136_:
{
lean_object* v___x_139_; lean_object* v_cache_140_; lean_object* v_mctx_141_; lean_object* v_zetaDeltaFVarIds_142_; lean_object* v_postponed_143_; lean_object* v_diag_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_169_; 
v___x_139_ = lean_st_ref_take(v___y_138_);
v_cache_140_ = lean_ctor_get(v___x_139_, 1);
v_mctx_141_ = lean_ctor_get(v___x_139_, 0);
v_zetaDeltaFVarIds_142_ = lean_ctor_get(v___x_139_, 2);
v_postponed_143_ = lean_ctor_get(v___x_139_, 3);
v_diag_144_ = lean_ctor_get(v___x_139_, 4);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_169_ == 0)
{
v___x_146_ = v___x_139_;
v_isShared_147_ = v_isSharedCheck_169_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_diag_144_);
lean_inc(v_postponed_143_);
lean_inc(v_zetaDeltaFVarIds_142_);
lean_inc(v_cache_140_);
lean_inc(v_mctx_141_);
lean_dec(v___x_139_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_169_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_inferType_148_; lean_object* v_funInfo_149_; lean_object* v_synthInstance_150_; lean_object* v_whnf_151_; lean_object* v_defEqTrans_152_; lean_object* v_defEqPerm_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_168_; 
v_inferType_148_ = lean_ctor_get(v_cache_140_, 0);
v_funInfo_149_ = lean_ctor_get(v_cache_140_, 1);
v_synthInstance_150_ = lean_ctor_get(v_cache_140_, 2);
v_whnf_151_ = lean_ctor_get(v_cache_140_, 3);
v_defEqTrans_152_ = lean_ctor_get(v_cache_140_, 4);
v_defEqPerm_153_ = lean_ctor_get(v_cache_140_, 5);
v_isSharedCheck_168_ = !lean_is_exclusive(v_cache_140_);
if (v_isSharedCheck_168_ == 0)
{
v___x_155_ = v_cache_140_;
v_isShared_156_ = v_isSharedCheck_168_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_defEqPerm_153_);
lean_inc(v_defEqTrans_152_);
lean_inc(v_whnf_151_);
lean_inc(v_synthInstance_150_);
lean_inc(v_funInfo_149_);
lean_inc(v_inferType_148_);
lean_dec(v_cache_140_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_168_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_inc_ref(v_finfo_137_);
v___x_157_ = l_Lean_PersistentHashMap_insert___redArg(v___x_134_, v___x_135_, v_funInfo_149_, v_a_127_, v_finfo_137_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_inferType_148_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_synthInstance_150_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_whnf_151_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_defEqTrans_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_defEqPerm_153_);
v___x_159_ = v_reuseFailAlloc_167_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_161_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_159_);
v___x_161_ = v___x_146_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_mctx_141_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v_zetaDeltaFVarIds_142_);
lean_ctor_set(v_reuseFailAlloc_166_, 3, v_postponed_143_);
lean_ctor_set(v_reuseFailAlloc_166_, 4, v_diag_144_);
v___x_161_ = v_reuseFailAlloc_166_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_st_ref_set(v___y_138_, v___x_161_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_finfo_137_);
v___x_164_ = v___x_129_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_finfo_137_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
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
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec_ref(v_k_120_);
lean_dec(v_maxArgs_x3f_119_);
lean_dec_ref(v_fn_118_);
v_a_195_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_126_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_126_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(lean_object* v_fn_203_, lean_object* v_maxArgs_x3f_204_, lean_object* v_k_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(v_fn_203_, v_maxArgs_x3f_204_, v_k_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object* v_e_212_, lean_object* v_deps_213_, lean_object* v_k_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Expr_hasFVar(v_e_212_);
if (v___x_215_ == 0)
{
lean_dec(v_k_214_);
return v_deps_213_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_apply_1(v_k_214_, v_deps_213_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object* v_e_217_, lean_object* v_deps_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(v_e_217_, v_deps_218_, v_k_219_);
lean_dec_ref(v_e_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* v_00_u03b1_221_, lean_object* v_e_222_, lean_object* v_deps_223_, lean_object* v_k_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_Expr_hasFVar(v_e_222_);
if (v___x_225_ == 0)
{
lean_dec(v_k_224_);
return v_deps_223_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = lean_apply_1(v_k_224_, v_deps_223_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object* v_00_u03b1_227_, lean_object* v_e_228_, lean_object* v_deps_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(v_00_u03b1_227_, v_e_228_, v_deps_229_, v_k_230_);
lean_dec_ref(v_e_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(lean_object* v_xs_232_, lean_object* v_v_233_, lean_object* v_i_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_xs_232_);
v___x_236_ = lean_nat_dec_lt(v_i_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_i_234_);
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_fget_borrowed(v_xs_232_, v_i_234_);
v___x_239_ = lean_expr_eqv(v___x_238_, v_v_233_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_i_234_, v___x_240_);
lean_dec(v_i_234_);
v_i_234_ = v___x_241_;
goto _start;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_i_234_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_244_, lean_object* v_v_245_, lean_object* v_i_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_244_, v_v_245_, v_i_246_);
lean_dec_ref(v_v_245_);
lean_dec_ref(v_xs_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object* v_xs_248_, lean_object* v_v_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_248_, v_v_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object* v_xs_252_, lean_object* v_v_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_252_, v_v_253_);
lean_dec_ref(v_v_253_);
lean_dec_ref(v_xs_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* v_xs_255_, lean_object* v_v_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_255_, v_v_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(0);
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_val_259_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_val_259_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_val_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* v_xs_267_, lean_object* v_v_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_xs_267_, v_v_268_);
lean_dec_ref(v_v_268_);
lean_dec_ref(v_xs_267_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(lean_object* v_a_270_, lean_object* v_as_271_, size_t v_i_272_, size_t v_stop_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_eq(v_i_272_, v_stop_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_array_uget_borrowed(v_as_271_, v_i_272_);
v___x_276_ = lean_nat_dec_eq(v_a_270_, v___x_275_);
if (v___x_276_ == 0)
{
size_t v___x_277_; size_t v___x_278_; 
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_272_, v___x_277_);
v_i_272_ = v___x_278_;
goto _start;
}
else
{
return v___x_276_;
}
}
else
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(lean_object* v_a_281_, lean_object* v_as_282_, lean_object* v_i_283_, lean_object* v_stop_284_){
_start:
{
size_t v_i_boxed_285_; size_t v_stop_boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_i_boxed_285_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_stop_boxed_286_ = lean_unbox_usize(v_stop_284_);
lean_dec(v_stop_284_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_281_, v_as_282_, v_i_boxed_285_, v_stop_boxed_286_);
lean_dec_ref(v_as_282_);
lean_dec(v_a_281_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object* v_as_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_array_get_size(v_as_289_);
v___x_293_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
return v___x_293_;
}
else
{
if (v___x_293_ == 0)
{
return v___x_293_;
}
else
{
size_t v___x_294_; size_t v___x_295_; uint8_t v___x_296_; 
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_292_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_290_, v_as_289_, v___x_294_, v___x_295_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object* v_as_297_, lean_object* v_a_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_as_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* v_fvars_301_, lean_object* v_e_302_, lean_object* v_deps_303_){
_start:
{
lean_object* v_d_305_; lean_object* v_b_306_; 
switch(lean_obj_tag(v_e_302_))
{
case 5:
{
lean_object* v_fn_310_; lean_object* v_arg_311_; uint8_t v___x_312_; 
v_fn_310_ = lean_ctor_get(v_e_302_, 0);
v_arg_311_ = lean_ctor_get(v_e_302_, 1);
v___x_312_ = l_Lean_Expr_hasFVar(v_e_302_);
if (v___x_312_ == 0)
{
return v_deps_303_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_301_, v_fn_310_, v_deps_303_);
v_e_302_ = v_arg_311_;
v_deps_303_ = v___x_313_;
goto _start;
}
}
case 7:
{
lean_object* v_binderType_315_; lean_object* v_body_316_; 
v_binderType_315_ = lean_ctor_get(v_e_302_, 1);
v_body_316_ = lean_ctor_get(v_e_302_, 2);
v_d_305_ = v_binderType_315_;
v_b_306_ = v_body_316_;
goto v___jp_304_;
}
case 6:
{
lean_object* v_binderType_317_; lean_object* v_body_318_; 
v_binderType_317_ = lean_ctor_get(v_e_302_, 1);
v_body_318_ = lean_ctor_get(v_e_302_, 2);
v_d_305_ = v_binderType_317_;
v_b_306_ = v_body_318_;
goto v___jp_304_;
}
case 8:
{
lean_object* v_type_319_; lean_object* v_value_320_; lean_object* v_body_321_; uint8_t v___x_322_; 
v_type_319_ = lean_ctor_get(v_e_302_, 1);
v_value_320_ = lean_ctor_get(v_e_302_, 2);
v_body_321_ = lean_ctor_get(v_e_302_, 3);
v___x_322_ = l_Lean_Expr_hasFVar(v_e_302_);
if (v___x_322_ == 0)
{
return v_deps_303_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_301_, v_type_319_, v_deps_303_);
v___x_324_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_301_, v_value_320_, v___x_323_);
v_e_302_ = v_body_321_;
v_deps_303_ = v___x_324_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_326_; 
v_struct_326_ = lean_ctor_get(v_e_302_, 2);
v_e_302_ = v_struct_326_;
goto _start;
}
case 10:
{
lean_object* v_expr_328_; 
v_expr_328_ = lean_ctor_get(v_e_302_, 1);
v_e_302_ = v_expr_328_;
goto _start;
}
case 1:
{
lean_object* v___x_330_; 
v___x_330_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_301_, v_e_302_);
if (lean_obj_tag(v___x_330_) == 0)
{
return v_deps_303_;
}
else
{
lean_object* v_val_331_; uint8_t v___x_332_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_deps_303_, v_val_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_array_push(v_deps_303_, v_val_331_);
return v___x_333_;
}
else
{
lean_dec(v_val_331_);
return v_deps_303_;
}
}
}
default: 
{
return v_deps_303_;
}
}
v___jp_304_:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_Expr_hasFVar(v_e_302_);
if (v___x_307_ == 0)
{
return v_deps_303_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_301_, v_d_305_, v_deps_303_);
v_e_302_ = v_b_306_;
v_deps_303_ = v___x_308_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* v_fvars_334_, lean_object* v_e_335_, lean_object* v_deps_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_334_, v_e_335_, v_deps_336_);
lean_dec_ref(v_e_335_);
lean_dec_ref(v_fvars_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object* v_hi_338_, lean_object* v_pivot_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_k_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_nat_dec_lt(v_k_342_, v_hi_338_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v_k_342_);
v___x_344_ = lean_array_fswap(v_as_340_, v_i_341_, v_hi_338_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_i_341_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_array_fget_borrowed(v_as_340_, v_k_342_);
v___x_347_ = lean_nat_dec_lt(v___x_346_, v_pivot_339_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_k_342_, v___x_348_);
lean_dec(v_k_342_);
v_k_342_ = v___x_349_;
goto _start;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = lean_array_fswap(v_as_340_, v_i_341_, v_k_342_);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_i_341_, v___x_352_);
lean_dec(v_i_341_);
v___x_354_ = lean_nat_add(v_k_342_, v___x_352_);
lean_dec(v_k_342_);
v_as_340_ = v___x_351_;
v_i_341_ = v___x_353_;
v_k_342_ = v___x_354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_356_, lean_object* v_pivot_357_, lean_object* v_as_358_, lean_object* v_i_359_, lean_object* v_k_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_356_, v_pivot_357_, v_as_358_, v_i_359_, v_k_360_);
lean_dec(v_pivot_357_);
lean_dec(v_hi_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_n_362_, lean_object* v_as_363_, lean_object* v_lo_364_, lean_object* v_hi_365_){
_start:
{
lean_object* v___y_367_; uint8_t v___x_377_; 
v___x_377_ = lean_nat_dec_lt(v_lo_364_, v_hi_365_);
if (v___x_377_ == 0)
{
lean_dec(v_lo_364_);
return v_as_363_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_mid_380_; lean_object* v___y_382_; lean_object* v___y_388_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_378_ = lean_nat_add(v_lo_364_, v_hi_365_);
v___x_379_ = lean_unsigned_to_nat(1u);
v_mid_380_ = lean_nat_shiftr(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
v___x_393_ = lean_array_fget_borrowed(v_as_363_, v_mid_380_);
v___x_394_ = lean_array_fget_borrowed(v_as_363_, v_lo_364_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
v___y_388_ = v_as_363_;
goto v___jp_387_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_array_fswap(v_as_363_, v_lo_364_, v_mid_380_);
v___y_388_ = v___x_396_;
goto v___jp_387_;
}
v___jp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_383_ = lean_array_fget_borrowed(v___y_382_, v_mid_380_);
v___x_384_ = lean_array_fget_borrowed(v___y_382_, v_hi_365_);
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_mid_380_);
v___y_367_ = v___y_382_;
goto v___jp_366_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_array_fswap(v___y_382_, v_mid_380_, v_hi_365_);
lean_dec(v_mid_380_);
v___y_367_ = v___x_386_;
goto v___jp_366_;
}
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_array_fget_borrowed(v___y_388_, v_hi_365_);
v___x_390_ = lean_array_fget_borrowed(v___y_388_, v_lo_364_);
v___x_391_ = lean_nat_dec_lt(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
v___y_382_ = v___y_388_;
goto v___jp_381_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_array_fswap(v___y_388_, v_lo_364_, v_hi_365_);
v___y_382_ = v___x_392_;
goto v___jp_381_;
}
}
}
v___jp_366_:
{
lean_object* v_pivot_368_; lean_object* v___x_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; uint8_t v___x_372_; 
v_pivot_368_ = lean_array_fget(v___y_367_, v_hi_365_);
lean_inc_n(v_lo_364_, 2);
v___x_369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_365_, v_pivot_368_, v___y_367_, v_lo_364_, v_lo_364_);
lean_dec(v_pivot_368_);
v_fst_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_snd_371_);
lean_dec_ref(v___x_369_);
v___x_372_ = lean_nat_dec_le(v_hi_365_, v_fst_370_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_362_, v_snd_371_, v_lo_364_, v_fst_370_);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_nat_add(v_fst_370_, v___x_374_);
lean_dec(v_fst_370_);
v_as_363_ = v___x_373_;
v_lo_364_ = v___x_375_;
goto _start;
}
else
{
lean_dec(v_fst_370_);
lean_dec(v_lo_364_);
return v_snd_371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_n_397_, lean_object* v_as_398_, lean_object* v_lo_399_, lean_object* v_hi_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_397_, v_as_398_, v_lo_399_, v_hi_400_);
lean_dec(v_hi_400_);
lean_dec(v_n_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_404_, lean_object* v_e_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_deps_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0));
v_deps_408_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_404_, v_e_405_, v___x_407_);
v___x_409_ = lean_array_get_size(v_deps_408_);
v___x_410_ = lean_nat_dec_eq(v___x_409_, v___x_406_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___y_414_; uint8_t v___x_418_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_sub(v___x_409_, v___x_411_);
v___x_418_ = lean_nat_dec_le(v___x_406_, v___x_412_);
if (v___x_418_ == 0)
{
lean_inc(v___x_412_);
v___y_414_ = v___x_412_;
goto v___jp_413_;
}
else
{
v___y_414_ = v___x_406_;
goto v___jp_413_;
}
v___jp_413_:
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_le(v___y_414_, v___x_412_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_dec(v___x_412_);
lean_inc(v___y_414_);
v___x_416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_409_, v_deps_408_, v___y_414_, v___y_414_);
lean_dec(v___y_414_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_409_, v_deps_408_, v___y_414_, v___x_412_);
lean_dec(v___x_412_);
return v___x_417_;
}
}
}
else
{
return v_deps_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_419_, lean_object* v_e_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_419_, v_e_420_);
lean_dec_ref(v_e_420_);
lean_dec_ref(v_fvars_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_422_, lean_object* v_as_423_, lean_object* v_lo_424_, lean_object* v_hi_425_, lean_object* v_w_426_, lean_object* v_hlo_427_, lean_object* v_hhi_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_422_, v_as_423_, v_lo_424_, v_hi_425_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_430_, lean_object* v_as_431_, lean_object* v_lo_432_, lean_object* v_hi_433_, lean_object* v_w_434_, lean_object* v_hlo_435_, lean_object* v_hhi_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_430_, v_as_431_, v_lo_432_, v_hi_433_, v_w_434_, v_hlo_435_, v_hhi_436_);
lean_dec(v_hi_433_);
lean_dec(v_n_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object* v_n_438_, lean_object* v_lo_439_, lean_object* v_hi_440_, lean_object* v_hhi_441_, lean_object* v_pivot_442_, lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_k_445_, lean_object* v_ilo_446_, lean_object* v_ik_447_, lean_object* v_w_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_440_, v_pivot_442_, v_as_443_, v_i_444_, v_k_445_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object* v_n_450_, lean_object* v_lo_451_, lean_object* v_hi_452_, lean_object* v_hhi_453_, lean_object* v_pivot_454_, lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_k_457_, lean_object* v_ilo_458_, lean_object* v_ik_459_, lean_object* v_w_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_450_, v_lo_451_, v_hi_452_, v_hhi_453_, v_pivot_454_, v_as_455_, v_i_456_, v_k_457_, v_ilo_458_, v_ik_459_, v_w_460_);
lean_dec(v_pivot_454_);
lean_dec(v_hi_452_);
lean_dec(v_lo_451_);
lean_dec(v_n_450_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_462_, size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_466_ == 0)
{
return v_bs_465_;
}
else
{
lean_object* v_v_467_; uint8_t v_binderInfo_468_; uint8_t v_hasFwdDeps_469_; lean_object* v_backDeps_470_; uint8_t v_isProp_471_; uint8_t v_isDecInst_472_; uint8_t v_isInstance_473_; uint8_t v_higherOrderOutParam_474_; uint8_t v_dependsOnHigherOrderOutParam_475_; lean_object* v___x_476_; lean_object* v_bs_x27_477_; lean_object* v___y_479_; 
v_v_467_ = lean_array_uget(v_bs_465_, v_i_464_);
v_binderInfo_468_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1);
v_hasFwdDeps_469_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 1);
v_backDeps_470_ = lean_ctor_get(v_v_467_, 0);
v_isProp_471_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 2);
v_isDecInst_472_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 3);
v_isInstance_473_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_474_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_475_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1 + 6);
v___x_476_ = lean_unsigned_to_nat(0u);
v_bs_x27_477_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_476_);
if (v_hasFwdDeps_469_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_usize_to_nat(v_i_464_);
v___x_485_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_462_, v___x_484_);
lean_dec(v___x_484_);
if (v___x_485_ == 0)
{
v___y_479_ = v_v_467_;
goto v___jp_478_;
}
else
{
lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_inc_ref(v_backDeps_470_);
v_isSharedCheck_492_ = !lean_is_exclusive(v_v_467_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_v_467_, 0);
lean_dec(v_unused_493_);
v___x_487_ = v_v_467_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_dec(v_v_467_);
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
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_backDeps_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1, v_binderInfo_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 2, v_isProp_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 3, v_isDecInst_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 4, v_isInstance_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 5, v_higherOrderOutParam_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_475_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1 + 1, v___x_485_);
v___y_479_ = v___x_490_;
goto v___jp_478_;
}
}
}
}
else
{
v___y_479_ = v_v_467_;
goto v___jp_478_;
}
v___jp_478_:
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_add(v_i_464_, v___x_480_);
v___x_482_ = lean_array_uset(v_bs_x27_477_, v_i_464_, v___y_479_);
v_i_464_ = v___x_481_;
v_bs_465_ = v___x_482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_bs_497_){
_start:
{
size_t v_sz_boxed_498_; size_t v_i_boxed_499_; lean_object* v_res_500_; 
v_sz_boxed_498_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_494_, v_sz_boxed_498_, v_i_boxed_499_, v_bs_497_);
lean_dec_ref(v_backDeps_494_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_501_, lean_object* v_backDeps_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_array_get_size(v_backDeps_502_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_sz_506_ = lean_array_size(v_pinfo_501_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_502_, v_sz_506_, v___x_507_, v_pinfo_501_);
return v___x_508_;
}
else
{
return v_pinfo_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_509_, lean_object* v_backDeps_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_509_, v_backDeps_510_);
lean_dec_ref(v_backDeps_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_512_, lean_object* v_as_513_, size_t v_sz_514_, size_t v_i_515_, lean_object* v_bs_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_512_, v_sz_514_, v_i_515_, v_bs_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_518_, lean_object* v_as_519_, lean_object* v_sz_520_, lean_object* v_i_521_, lean_object* v_bs_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v_i_boxed_524_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_518_, v_as_519_, v_sz_boxed_523_, v_i_boxed_524_, v_bs_522_);
lean_dec_ref(v_as_519_);
lean_dec_ref(v_backDeps_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_526_, lean_object* v_b_527_, lean_object* v_c_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
v___x_534_ = lean_apply_7(v_k_526_, v_b_527_, v_c_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, lean_box(0));
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_535_, lean_object* v_b_536_, lean_object* v_c_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_535_, v_b_536_, v_c_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_544_, lean_object* v_k_545_, uint8_t v_cleanupAnnotations_546_, uint8_t v_whnfType_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___f_553_; lean_object* v___x_554_; 
v___f_553_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_553_, 0, v_k_545_);
v___x_554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_544_, v___f_553_, v_cleanupAnnotations_546_, v_whnfType_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
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
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_571_, lean_object* v_k_572_, lean_object* v_cleanupAnnotations_573_, lean_object* v_whnfType_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_580_; uint8_t v_whnfType_boxed_581_; lean_object* v_res_582_; 
v_cleanupAnnotations_boxed_580_ = lean_unbox(v_cleanupAnnotations_573_);
v_whnfType_boxed_581_ = lean_unbox(v_whnfType_574_);
v_res_582_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_571_, v_k_572_, v_cleanupAnnotations_boxed_580_, v_whnfType_boxed_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_583_, lean_object* v_type_584_, lean_object* v_k_585_, uint8_t v_cleanupAnnotations_586_, uint8_t v_whnfType_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_584_, v_k_585_, v_cleanupAnnotations_586_, v_whnfType_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_594_, lean_object* v_type_595_, lean_object* v_k_596_, lean_object* v_cleanupAnnotations_597_, lean_object* v_whnfType_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_604_; uint8_t v_whnfType_boxed_605_; lean_object* v_res_606_; 
v_cleanupAnnotations_boxed_604_ = lean_unbox(v_cleanupAnnotations_597_);
v_whnfType_boxed_605_ = lean_unbox(v_whnfType_598_);
v_res_606_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_594_, v_type_595_, v_k_596_, v_cleanupAnnotations_boxed_604_, v_whnfType_boxed_605_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_9899__overap_615_; lean_object* v___x_616_; 
v___f_614_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9899__overap_615_ = lean_panic_fn_borrowed(v___f_614_, v_msg_608_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___x_616_ = lean_apply_5(v___x_9899__overap_615_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, lean_box(0));
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_624_, lean_object* v_maxFVars_x3f_625_, lean_object* v_k_626_, uint8_t v_cleanupAnnotations_627_, uint8_t v_whnfType_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; 
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_634_, 0, v_k_626_);
v___x_635_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_624_, v_maxFVars_x3f_625_, v___f_634_, v_cleanupAnnotations_627_, v_whnfType_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_635_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_652_, lean_object* v_maxFVars_x3f_653_, lean_object* v_k_654_, lean_object* v_cleanupAnnotations_655_, lean_object* v_whnfType_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_662_; uint8_t v_whnfType_boxed_663_; lean_object* v_res_664_; 
v_cleanupAnnotations_boxed_662_ = lean_unbox(v_cleanupAnnotations_655_);
v_whnfType_boxed_663_ = lean_unbox(v_whnfType_656_);
v_res_664_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_652_, v_maxFVars_x3f_653_, v_k_654_, v_cleanupAnnotations_boxed_662_, v_whnfType_boxed_663_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_665_, lean_object* v_type_666_, lean_object* v_maxFVars_x3f_667_, lean_object* v_k_668_, uint8_t v_cleanupAnnotations_669_, uint8_t v_whnfType_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_666_, v_maxFVars_x3f_667_, v_k_668_, v_cleanupAnnotations_669_, v_whnfType_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_677_, lean_object* v_type_678_, lean_object* v_maxFVars_x3f_679_, lean_object* v_k_680_, lean_object* v_cleanupAnnotations_681_, lean_object* v_whnfType_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_688_; uint8_t v_whnfType_boxed_689_; lean_object* v_res_690_; 
v_cleanupAnnotations_boxed_688_ = lean_unbox(v_cleanupAnnotations_681_);
v_whnfType_boxed_689_ = lean_unbox(v_whnfType_682_);
v_res_690_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_677_, v_type_678_, v_maxFVars_x3f_679_, v_k_680_, v_cleanupAnnotations_boxed_688_, v_whnfType_boxed_689_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_691_, lean_object* v_val_692_, lean_object* v___x_693_, lean_object* v_fvars_694_, uint8_t v___y_695_, lean_object* v_a_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_a_704_; uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_lt(v_a_696_, v_upperBound_691_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v_a_696_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_b_697_);
return v___x_709_;
}
else
{
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_774_; 
v_fst_710_ = lean_ctor_get(v_b_697_, 0);
v_snd_711_ = lean_ctor_get(v_b_697_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_b_697_);
if (v_isSharedCheck_774_ == 0)
{
v___x_713_ = v_b_697_;
v_isShared_714_ = v_isSharedCheck_774_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_b_697_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_774_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
uint8_t v___x_715_; 
v___x_715_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_692_, v_a_696_);
if (v___x_715_ == 0)
{
lean_object* v___x_717_; 
if (v_isShared_714_ == 0)
{
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_710_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_a_704_ = v___x_717_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_array_fget_borrowed(v___x_693_, v_a_696_);
v___x_720_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_694_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___x_719_);
v___x_722_ = lean_infer_type(v___x_719_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_724_ = lean_whnf(v_a_723_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___y_727_; uint8_t v___x_733_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_733_ = l_Lean_Expr_isForall(v_a_725_);
lean_dec(v_a_725_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_fst_710_);
lean_ctor_set(v___x_734_, 1, v_snd_711_);
v_a_704_ = v___x_734_;
goto v___jp_703_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_array_get_size(v_fst_710_);
v___x_736_ = lean_nat_dec_lt(v_val_721_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_val_721_);
v___y_727_ = v_fst_710_;
goto v___jp_726_;
}
else
{
lean_object* v_v_737_; uint8_t v_binderInfo_738_; uint8_t v_hasFwdDeps_739_; lean_object* v_backDeps_740_; uint8_t v_isProp_741_; uint8_t v_isDecInst_742_; uint8_t v_isInstance_743_; uint8_t v_dependsOnHigherOrderOutParam_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_v_737_ = lean_array_fget(v_fst_710_, v_val_721_);
v_binderInfo_738_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1);
v_hasFwdDeps_739_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1 + 1);
v_backDeps_740_ = lean_ctor_get(v_v_737_, 0);
v_isProp_741_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1 + 2);
v_isDecInst_742_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1 + 3);
v_isInstance_743_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_744_ = lean_ctor_get_uint8(v_v_737_, sizeof(void*)*1 + 6);
v_isSharedCheck_754_ = !lean_is_exclusive(v_v_737_);
if (v_isSharedCheck_754_ == 0)
{
v___x_746_ = v_v_737_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_backDeps_740_);
lean_dec(v_v_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v_xs_x27_749_; lean_object* v___x_751_; 
v___x_748_ = lean_box(0);
v_xs_x27_749_ = lean_array_fset(v_fst_710_, v_val_721_, v___x_748_);
if (v_isShared_747_ == 0)
{
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_backDeps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1, v_binderInfo_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 1, v_hasFwdDeps_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 2, v_isProp_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 3, v_isDecInst_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 4, v_isInstance_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_744_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1 + 5, v___y_695_);
v___x_752_ = lean_array_fset(v_xs_x27_749_, v_val_721_, v___x_751_);
lean_dec(v_val_721_);
v___y_727_ = v___x_752_;
goto v___jp_726_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_728_ = l_Lean_Expr_fvarId_x21(v___x_719_);
v___x_729_ = l_Lean_FVarIdSet_insert(v_snd_711_, v___x_728_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_729_);
lean_ctor_set(v___x_713_, 0, v___y_727_);
v___x_731_ = v___x_713_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___y_727_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_704_ = v___x_731_;
goto v___jp_703_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_dec(v_a_696_);
v_a_755_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_724_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_724_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_dec(v_a_696_);
v_a_763_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_722_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_722_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_772_; 
lean_dec(v___x_720_);
if (v_isShared_714_ == 0)
{
v___x_772_ = v___x_713_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_fst_710_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_711_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_a_704_ = v___x_772_;
goto v___jp_703_;
}
}
}
}
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_a_696_, v___x_705_);
lean_dec(v_a_696_);
v_a_696_ = v___x_706_;
v_b_697_ = v_a_704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_775_, lean_object* v_val_776_, lean_object* v___x_777_, lean_object* v_fvars_778_, lean_object* v___y_779_, lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___y_12360__boxed_787_; lean_object* v_res_788_; 
v___y_12360__boxed_787_ = lean_unbox(v___y_779_);
v_res_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_775_, v_val_776_, v___x_777_, v_fvars_778_, v___y_12360__boxed_787_, v_a_780_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_fvars_778_);
lean_dec_ref(v___x_777_);
lean_dec_ref(v_val_776_);
lean_dec(v_upperBound_775_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_792_, lean_object* v_type_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_800_ = l_Lean_Expr_isAppOf(v_type_793_, v___x_799_);
v___x_801_ = lean_box(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_803_, lean_object* v_type_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_803_, v_type_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_type_804_);
lean_dec_ref(v_x_803_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_k_811_, lean_object* v_t_812_){
_start:
{
if (lean_obj_tag(v_t_812_) == 0)
{
lean_object* v_k_813_; lean_object* v_l_814_; lean_object* v_r_815_; uint8_t v___x_816_; 
v_k_813_ = lean_ctor_get(v_t_812_, 1);
v_l_814_ = lean_ctor_get(v_t_812_, 3);
v_r_815_ = lean_ctor_get(v_t_812_, 4);
v___x_816_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_811_, v_k_813_);
switch(v___x_816_)
{
case 0:
{
v_t_812_ = v_l_814_;
goto _start;
}
case 1:
{
uint8_t v___x_818_; 
v___x_818_ = 1;
return v___x_818_;
}
default: 
{
v_t_812_ = v_r_815_;
goto _start;
}
}
}
else
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_k_821_, lean_object* v_t_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_821_, v_t_822_);
lean_dec(v_t_822_);
lean_dec(v_k_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object* v_snd_825_, lean_object* v_e_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_Expr_isFVar(v_e_826_);
if (v___x_827_ == 0)
{
return v___x_827_;
}
else
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_Lean_Expr_fvarId_x21(v_e_826_);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_828_, v_snd_825_);
lean_dec(v___x_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object* v_snd_830_, lean_object* v_e_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_830_, v_e_831_);
lean_dec_ref(v_e_831_);
lean_dec(v_snd_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v_dummy_836_; 
v___x_835_ = lean_box(0);
v_dummy_836_ = l_Lean_Expr_sort___override(v___x_835_);
return v_dummy_836_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_841_ = lean_unsigned_to_nat(47u);
v___x_842_ = lean_unsigned_to_nat(121u);
v___x_843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_844_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_845_ = l_mkPanicMessageWithDecl(v___x_844_, v___x_843_, v___x_842_, v___x_841_, v___x_840_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_846_, lean_object* v_fvars_847_, lean_object* v_a_848_, lean_object* v_b_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_a_856_; uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_lt(v_a_848_, v_upperBound_846_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec(v_a_848_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_b_849_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_array_fget_borrowed(v_fvars_847_, v_a_848_);
v___x_863_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_862_, v___y_850_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_978_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v_fst_865_ = lean_ctor_get(v_b_849_, 0);
v_snd_866_ = lean_ctor_get(v_b_849_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_b_849_);
if (v_isSharedCheck_978_ == 0)
{
v___x_868_ = v_b_849_;
v_isShared_869_ = v_isSharedCheck_978_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
lean_dec(v_b_849_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_978_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___y_875_; uint8_t v___y_876_; uint8_t v___y_877_; uint8_t v___y_957_; uint8_t v___y_973_; 
v___f_870_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
lean_inc(v_snd_866_);
v___f_871_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_871_, 0, v_snd_866_);
v___x_872_ = l_Lean_LocalDecl_type(v_a_864_);
v___x_873_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_847_, v___x_872_);
if (lean_obj_tag(v_snd_866_) == 0)
{
uint8_t v___x_977_; 
v___x_977_ = 0;
v___y_973_ = v___x_977_;
goto v___jp_972_;
}
else
{
v___y_973_ = v___x_860_;
goto v___jp_972_;
}
v___jp_874_:
{
lean_object* v___x_878_; 
lean_inc_ref(v___x_872_);
v___x_878_ = l_Lean_Meta_isProp(v___x_872_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; lean_object* v___x_881_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = 0;
lean_inc_ref(v___x_872_);
v___x_881_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_872_, v___f_870_, v___x_880_, v___x_880_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_865_, v___x_873_);
v___x_884_ = l_Lean_LocalDecl_binderInfo(v_a_864_);
lean_dec(v_a_864_);
v___x_885_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_885_, 0, v___x_873_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_884_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 1, v___x_880_);
v___x_886_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 2, v___x_886_);
v___x_887_ = lean_unbox(v_a_882_);
lean_dec(v_a_882_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 3, v___x_887_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 4, v___y_877_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 5, v___x_880_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1 + 6, v___y_876_);
v___x_888_ = lean_array_push(v___x_883_, v___x_885_);
if (v___y_877_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_872_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_890_ = v___x_868_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_866_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
v_a_856_ = v___x_890_;
goto v___jp_855_;
}
}
else
{
if (lean_obj_tag(v___y_875_) == 1)
{
lean_object* v_val_892_; lean_object* v___x_893_; lean_object* v_env_894_; lean_object* v___x_895_; 
v_val_892_ = lean_ctor_get(v___y_875_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v___y_875_, 1);
v___x_893_ = lean_st_ref_get(v___y_853_);
v_env_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_env_894_);
lean_dec(v___x_893_);
v___x_895_ = l_Lean_getOutParamPositions_x3f(v_env_894_, v_val_892_);
lean_dec(v_val_892_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_array_get_size(v_val_896_);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_nat_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v_dummy_900_; lean_object* v_nargs_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v_dummy_900_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_901_ = l_Lean_Expr_getAppNumArgs(v___x_872_);
lean_inc(v_nargs_901_);
v___x_902_ = lean_mk_array(v_nargs_901_, v_dummy_900_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_sub(v_nargs_901_, v___x_903_);
lean_dec(v_nargs_901_);
v___x_905_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_872_, v___x_902_, v___x_904_);
v___x_906_ = lean_array_get_size(v___x_905_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_908_ = v___x_868_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_866_);
v___x_908_ = v_reuseFailAlloc_920_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; 
v___x_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_906_, v_val_896_, v___x_905_, v_fvars_847_, v___y_877_, v___x_898_, v___x_908_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec_ref(v___x_905_);
lean_dec(v_val_896_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v_fst_911_ = lean_ctor_get(v_a_910_, 0);
v_snd_912_ = lean_ctor_get(v_a_910_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v_a_910_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v_a_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
v_a_856_ = v___x_917_;
goto v___jp_855_;
}
}
}
else
{
lean_dec(v_a_848_);
return v___x_909_;
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec(v_val_896_);
lean_dec_ref(v___x_872_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_922_ = v___x_868_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_snd_866_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
v_a_856_ = v___x_922_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec(v___x_895_);
lean_dec_ref(v___x_872_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_925_ = v___x_868_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_snd_866_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v_a_856_ = v___x_925_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_872_);
v___x_927_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
v___x_928_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_927_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; 
lean_dec_ref_known(v___x_928_, 1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_930_ = v___x_868_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_snd_866_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
v_a_856_ = v___x_930_;
goto v___jp_855_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___x_888_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_a_848_);
v_a_932_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_928_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_879_);
lean_dec(v___y_875_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_940_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_881_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_881_);
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
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_948_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_878_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_878_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_956_:
{
lean_object* v___x_958_; 
lean_inc_ref(v___x_872_);
v___x_958_ = l_Lean_Meta_isClass_x3f(v___x_872_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
if (lean_obj_tag(v_a_959_) == 0)
{
uint8_t v___x_960_; 
v___x_960_ = 0;
v___y_875_ = v_a_959_;
v___y_876_ = v___y_957_;
v___y_877_ = v___x_960_;
goto v___jp_874_;
}
else
{
uint8_t v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_961_ = l_Lean_LocalDecl_binderInfo(v_a_864_);
v___x_962_ = l_Lean_BinderInfo_isExplicit(v___x_961_);
v___x_963_ = lean_bool_not(v___x_962_);
v___y_875_ = v_a_959_;
v___y_876_ = v___y_957_;
v___y_877_ = v___x_963_;
goto v___jp_874_;
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v___x_873_);
lean_dec_ref(v___x_872_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_964_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_958_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_958_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
v___jp_972_:
{
uint8_t v___x_974_; 
v___x_974_ = lean_bool_not(v___y_973_);
if (v___x_974_ == 0)
{
lean_dec_ref(v___f_871_);
v___y_957_ = v___x_974_;
goto v___jp_956_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_find_expr(v___f_871_, v___x_872_);
lean_dec_ref(v___f_871_);
if (lean_obj_tag(v___x_975_) == 0)
{
uint8_t v___x_976_; 
v___x_976_ = 0;
v___y_957_ = v___x_976_;
goto v___jp_956_;
}
else
{
lean_dec_ref_known(v___x_975_, 1);
v___y_957_ = v___x_974_;
goto v___jp_956_;
}
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v_b_849_);
lean_dec(v_a_848_);
v_a_979_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_863_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_863_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_a_848_, v___x_857_);
lean_dec(v_a_848_);
v_a_848_ = v___x_858_;
v_b_849_ = v_a_856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_987_, lean_object* v_fvars_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_987_, v_fvars_988_, v_a_989_, v_b_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_fvars_988_);
lean_dec(v_upperBound_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_999_, lean_object* v_fvars_1000_, lean_object* v_type_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1007_ = lean_array_get_size(v_fvars_1000_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_999_);
v___x_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1007_, v_fvars_1000_, v___x_1008_, v___x_1010_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1030_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_fst_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1028_; 
v_fst_1016_ = lean_ctor_get(v_a_1012_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_a_1012_, 1);
lean_dec(v_unused_1029_);
v___x_1018_ = v_a_1012_;
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_fst_1016_);
lean_dec(v_a_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1020_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_1000_, v_type_1001_);
v___x_1021_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_1016_, v___x_1020_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1020_);
lean_ctor_set(v___x_1018_, 0, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1020_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1023_);
v___x_1025_ = v___x_1014_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1011_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1011_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_1039_, lean_object* v_fvars_1040_, lean_object* v_type_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1039_, v_fvars_1040_, v_type_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_type_1041_);
lean_dec_ref(v_fvars_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1048_, lean_object* v_maxArgs_x3f_1049_, lean_object* v___f_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1056_ = lean_infer_type(v_fn_1048_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; uint8_t v_transparency_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; uint8_t v___y_1063_; uint8_t v___x_1121_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = l_Lean_Meta_Context_config(v___y_1051_);
v_transparency_1059_ = lean_ctor_get_uint8(v___x_1058_, 9);
v___x_1060_ = 1;
v___x_1061_ = 0;
v___x_1121_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1059_, v___x_1060_);
if (v___x_1121_ == 0)
{
v___y_1063_ = v_transparency_1059_;
goto v___jp_1062_;
}
else
{
v___y_1063_ = v___x_1060_;
goto v___jp_1062_;
}
v___jp_1062_:
{
uint8_t v_foApprox_1064_; uint8_t v_ctxApprox_1065_; uint8_t v_quasiPatternApprox_1066_; uint8_t v_constApprox_1067_; uint8_t v_isDefEqStuckEx_1068_; uint8_t v_unificationHints_1069_; uint8_t v_proofIrrelevance_1070_; uint8_t v_assignSyntheticOpaque_1071_; uint8_t v_offsetCnstrs_1072_; uint8_t v_etaStruct_1073_; uint8_t v_univApprox_1074_; uint8_t v_iota_1075_; uint8_t v_beta_1076_; uint8_t v_proj_1077_; uint8_t v_zeta_1078_; uint8_t v_zetaDelta_1079_; uint8_t v_zetaUnused_1080_; uint8_t v_zetaHave_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1120_; 
v_foApprox_1064_ = lean_ctor_get_uint8(v___x_1058_, 0);
v_ctxApprox_1065_ = lean_ctor_get_uint8(v___x_1058_, 1);
v_quasiPatternApprox_1066_ = lean_ctor_get_uint8(v___x_1058_, 2);
v_constApprox_1067_ = lean_ctor_get_uint8(v___x_1058_, 3);
v_isDefEqStuckEx_1068_ = lean_ctor_get_uint8(v___x_1058_, 4);
v_unificationHints_1069_ = lean_ctor_get_uint8(v___x_1058_, 5);
v_proofIrrelevance_1070_ = lean_ctor_get_uint8(v___x_1058_, 6);
v_assignSyntheticOpaque_1071_ = lean_ctor_get_uint8(v___x_1058_, 7);
v_offsetCnstrs_1072_ = lean_ctor_get_uint8(v___x_1058_, 8);
v_etaStruct_1073_ = lean_ctor_get_uint8(v___x_1058_, 10);
v_univApprox_1074_ = lean_ctor_get_uint8(v___x_1058_, 11);
v_iota_1075_ = lean_ctor_get_uint8(v___x_1058_, 12);
v_beta_1076_ = lean_ctor_get_uint8(v___x_1058_, 13);
v_proj_1077_ = lean_ctor_get_uint8(v___x_1058_, 14);
v_zeta_1078_ = lean_ctor_get_uint8(v___x_1058_, 15);
v_zetaDelta_1079_ = lean_ctor_get_uint8(v___x_1058_, 16);
v_zetaUnused_1080_ = lean_ctor_get_uint8(v___x_1058_, 17);
v_zetaHave_1081_ = lean_ctor_get_uint8(v___x_1058_, 18);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1083_ = v___x_1058_;
v_isShared_1084_ = v_isSharedCheck_1120_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v___x_1058_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1120_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
uint8_t v_trackZetaDelta_1085_; lean_object* v_zetaDeltaSet_1086_; lean_object* v_lctx_1087_; lean_object* v_localInstances_1088_; lean_object* v_defEqCtx_x3f_1089_; lean_object* v_synthPendingDepth_1090_; lean_object* v_canUnfold_x3f_1091_; uint8_t v_univApprox_1092_; uint8_t v_inTypeClassResolution_1093_; uint8_t v_cacheInferType_1094_; lean_object* v_config_1096_; 
v_trackZetaDelta_1085_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*7);
v_zetaDeltaSet_1086_ = lean_ctor_get(v___y_1051_, 1);
lean_inc(v_zetaDeltaSet_1086_);
v_lctx_1087_ = lean_ctor_get(v___y_1051_, 2);
lean_inc_ref(v_lctx_1087_);
v_localInstances_1088_ = lean_ctor_get(v___y_1051_, 3);
lean_inc_ref(v_localInstances_1088_);
v_defEqCtx_x3f_1089_ = lean_ctor_get(v___y_1051_, 4);
lean_inc(v_defEqCtx_x3f_1089_);
v_synthPendingDepth_1090_ = lean_ctor_get(v___y_1051_, 5);
lean_inc(v_synthPendingDepth_1090_);
v_canUnfold_x3f_1091_ = lean_ctor_get(v___y_1051_, 6);
lean_inc(v_canUnfold_x3f_1091_);
v_univApprox_1092_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1093_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*7 + 2);
v_cacheInferType_1094_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*7 + 3);
if (v_isShared_1084_ == 0)
{
v_config_1096_ = v___x_1083_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 0, v_foApprox_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 1, v_ctxApprox_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 2, v_quasiPatternApprox_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 3, v_constApprox_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 4, v_isDefEqStuckEx_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 5, v_unificationHints_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 6, v_proofIrrelevance_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 7, v_assignSyntheticOpaque_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 8, v_offsetCnstrs_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 10, v_etaStruct_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 11, v_univApprox_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 12, v_iota_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 13, v_beta_1076_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 14, v_proj_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 15, v_zeta_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 16, v_zetaDelta_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 17, v_zetaUnused_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, 18, v_zetaHave_1081_);
v_config_1096_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
uint64_t v___x_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1111_; 
lean_ctor_set_uint8(v_config_1096_, 9, v___y_1063_);
v___x_1097_ = l_Lean_Meta_Context_configKey(v___y_1051_);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_1051_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1112_ = lean_ctor_get(v___y_1051_, 6);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v___y_1051_, 5);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v___y_1051_, 4);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v___y_1051_, 3);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v___y_1051_, 2);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v___y_1051_, 1);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v___y_1051_, 0);
lean_dec(v_unused_1118_);
v___x_1099_ = v___y_1051_;
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v___y_1051_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v_key_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1101_ = 3ULL;
v___x_1102_ = lean_uint64_shift_right(v___x_1097_, v___x_1101_);
v___x_1103_ = lean_uint64_shift_left(v___x_1102_, v___x_1101_);
v___x_1104_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1063_);
v_key_1105_ = lean_uint64_lor(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1106_, 0, v_config_1096_);
lean_ctor_set_uint64(v___x_1106_, sizeof(void*)*1, v_key_1105_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1106_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_zetaDeltaSet_1086_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_lctx_1087_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_localInstances_1088_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_defEqCtx_x3f_1089_);
lean_ctor_set(v_reuseFailAlloc_1110_, 5, v_synthPendingDepth_1090_);
lean_ctor_set(v_reuseFailAlloc_1110_, 6, v_canUnfold_x3f_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*7, v_trackZetaDelta_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*7 + 1, v_univApprox_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*7 + 3, v_cacheInferType_1094_);
v___x_1108_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1057_, v_maxArgs_x3f_1049_, v___f_1050_, v___x_1061_, v___x_1061_, v___x_1108_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___x_1108_);
return v___x_1109_;
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v___f_1050_);
lean_dec(v_maxArgs_x3f_1049_);
v_a_1122_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1056_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1056_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1130_, lean_object* v_maxArgs_x3f_1131_, lean_object* v___f_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1130_, v_maxArgs_x3f_1131_, v___f_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_i_1141_, lean_object* v_k_1142_){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_array_get_size(v_keys_1139_);
v___x_1144_ = lean_nat_dec_lt(v_i_1141_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec(v_i_1141_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
else
{
lean_object* v_k_x27_1146_; uint8_t v___x_1147_; 
v_k_x27_1146_ = lean_array_fget_borrowed(v_keys_1139_, v_i_1141_);
v___x_1147_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1142_, v_k_x27_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_i_1141_, v___x_1148_);
lean_dec(v_i_1141_);
v_i_1141_ = v___x_1149_;
goto _start;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_array_fget_borrowed(v_vals_1140_, v_i_1141_);
lean_dec(v_i_1141_);
lean_inc(v___x_1151_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1153_, lean_object* v_vals_1154_, lean_object* v_i_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1153_, v_vals_1154_, v_i_1155_, v_k_1156_);
lean_dec_ref(v_k_1156_);
lean_dec_ref(v_vals_1154_);
lean_dec_ref(v_keys_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1158_, size_t v_x_1159_, lean_object* v_x_1160_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_object* v_es_1161_; lean_object* v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v_j_1165_; lean_object* v___x_1166_; 
v_es_1161_ = lean_ctor_get(v_x_1158_, 0);
v___x_1162_ = lean_box(2);
v___x_1163_ = ((size_t)31ULL);
v___x_1164_ = lean_usize_land(v_x_1159_, v___x_1163_);
v_j_1165_ = lean_usize_to_nat(v___x_1164_);
v___x_1166_ = lean_array_get_borrowed(v___x_1162_, v_es_1161_, v_j_1165_);
lean_dec(v_j_1165_);
switch(lean_obj_tag(v___x_1166_))
{
case 0:
{
lean_object* v_key_1167_; lean_object* v_val_1168_; uint8_t v___x_1169_; 
v_key_1167_ = lean_ctor_get(v___x_1166_, 0);
v_val_1168_ = lean_ctor_get(v___x_1166_, 1);
v___x_1169_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1160_, v_key_1167_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_inc(v_val_1168_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_val_1168_);
return v___x_1171_;
}
}
case 1:
{
lean_object* v_node_1172_; size_t v___x_1173_; size_t v___x_1174_; 
v_node_1172_ = lean_ctor_get(v___x_1166_, 0);
v___x_1173_ = ((size_t)5ULL);
v___x_1174_ = lean_usize_shift_right(v_x_1159_, v___x_1173_);
v_x_1158_ = v_node_1172_;
v_x_1159_ = v___x_1174_;
goto _start;
}
default: 
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
}
}
else
{
lean_object* v_ks_1177_; lean_object* v_vs_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_ks_1177_ = lean_ctor_get(v_x_1158_, 0);
v_vs_1178_ = lean_ctor_get(v_x_1158_, 1);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1177_, v_vs_1178_, v___x_1179_, v_x_1160_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
size_t v_x_13084__boxed_1184_; lean_object* v_res_1185_; 
v_x_13084__boxed_1184_ = lean_unbox_usize(v_x_1182_);
lean_dec(v_x_1182_);
v_res_1185_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1181_, v_x_13084__boxed_1184_, v_x_1183_);
lean_dec_ref(v_x_1183_);
lean_dec_ref(v_x_1181_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
uint64_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1187_);
v___x_1189_ = lean_uint64_to_usize(v___x_1188_);
v___x_1190_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1186_, v___x_1189_, v_x_1187_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1191_, v_x_1192_);
lean_dec_ref(v_x_1192_);
lean_dec_ref(v_x_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_ks_1198_; lean_object* v_vs_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1223_; 
v_ks_1198_ = lean_ctor_get(v_x_1194_, 0);
v_vs_1199_ = lean_ctor_get(v_x_1194_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1194_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1201_ = v_x_1194_;
v_isShared_1202_ = v_isSharedCheck_1223_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_vs_1199_);
lean_inc(v_ks_1198_);
lean_dec(v_x_1194_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1223_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_array_get_size(v_ks_1198_);
v___x_1204_ = lean_nat_dec_lt(v_x_1195_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec(v_x_1195_);
v___x_1205_ = lean_array_push(v_ks_1198_, v_x_1196_);
v___x_1206_ = lean_array_push(v_vs_1199_, v_x_1197_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1206_);
lean_ctor_set(v___x_1201_, 0, v___x_1205_);
v___x_1208_ = v___x_1201_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
lean_object* v_k_x27_1210_; uint8_t v___x_1211_; 
v_k_x27_1210_ = lean_array_fget_borrowed(v_ks_1198_, v_x_1195_);
v___x_1211_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1196_, v_k_x27_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1213_; 
if (v_isShared_1202_ == 0)
{
v___x_1213_ = v___x_1201_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_ks_1198_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_vs_1199_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_x_1195_, v___x_1214_);
lean_dec(v_x_1195_);
v_x_1194_ = v___x_1213_;
v_x_1195_ = v___x_1215_;
goto _start;
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1218_ = lean_array_fset(v_ks_1198_, v_x_1195_, v_x_1196_);
v___x_1219_ = lean_array_fset(v_vs_1199_, v_x_1195_, v_x_1197_);
lean_dec(v_x_1195_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1219_);
lean_ctor_set(v___x_1201_, 0, v___x_1218_);
v___x_1221_ = v___x_1201_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1224_, lean_object* v_k_1225_, lean_object* v_v_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_1224_, v___x_1227_, v_k_1225_, v_v_1226_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1230_, size_t v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_es_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v_j_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_es_1235_ = lean_ctor_get(v_x_1230_, 0);
v___x_1236_ = ((size_t)31ULL);
v___x_1237_ = lean_usize_land(v_x_1231_, v___x_1236_);
v_j_1238_ = lean_usize_to_nat(v___x_1237_);
v___x_1239_ = lean_array_get_size(v_es_1235_);
v___x_1240_ = lean_nat_dec_lt(v_j_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec(v_j_1238_);
lean_dec(v_x_1234_);
lean_dec_ref(v_x_1233_);
return v_x_1230_;
}
else
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1279_; 
lean_inc_ref(v_es_1235_);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_x_1230_, 0);
lean_dec(v_unused_1280_);
v___x_1242_ = v_x_1230_;
v_isShared_1243_ = v_isSharedCheck_1279_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1279_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_v_1244_; lean_object* v___x_1245_; lean_object* v_xs_x27_1246_; lean_object* v___y_1248_; 
v_v_1244_ = lean_array_fget(v_es_1235_, v_j_1238_);
v___x_1245_ = lean_box(0);
v_xs_x27_1246_ = lean_array_fset(v_es_1235_, v_j_1238_, v___x_1245_);
switch(lean_obj_tag(v_v_1244_))
{
case 0:
{
lean_object* v_key_1253_; lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1264_; 
v_key_1253_ = lean_ctor_get(v_v_1244_, 0);
v_val_1254_ = lean_ctor_get(v_v_1244_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_v_1244_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1256_ = v_v_1244_;
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_inc(v_key_1253_);
lean_dec(v_v_1244_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; 
v___x_1258_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1233_, v_key_1253_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_del_object(v___x_1256_);
v___x_1259_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1253_, v_val_1254_, v_x_1233_, v_x_1234_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___y_1248_ = v___x_1260_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1262_; 
lean_dec(v_val_1254_);
lean_dec(v_key_1253_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_x_1234_);
lean_ctor_set(v___x_1256_, 0, v_x_1233_);
v___x_1262_ = v___x_1256_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_x_1233_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_x_1234_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v___y_1248_ = v___x_1262_;
goto v___jp_1247_;
}
}
}
}
case 1:
{
lean_object* v_node_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1277_; 
v_node_1265_ = lean_ctor_get(v_v_1244_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_v_1244_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1267_ = v_v_1244_;
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_node_1265_);
lean_dec(v_v_1244_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1269_ = ((size_t)5ULL);
v___x_1270_ = lean_usize_shift_right(v_x_1231_, v___x_1269_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_x_1232_, v___x_1271_);
v___x_1273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1265_, v___x_1270_, v___x_1272_, v_x_1233_, v_x_1234_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1273_);
v___x_1275_ = v___x_1267_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v___y_1248_ = v___x_1275_;
goto v___jp_1247_;
}
}
}
default: 
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_x_1233_);
lean_ctor_set(v___x_1278_, 1, v_x_1234_);
v___y_1248_ = v___x_1278_;
goto v___jp_1247_;
}
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_array_fset(v_xs_x27_1246_, v_j_1238_, v___y_1248_);
lean_dec(v_j_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1249_);
v___x_1251_ = v___x_1242_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
else
{
lean_object* v_ks_1281_; lean_object* v_vs_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1302_; 
v_ks_1281_ = lean_ctor_get(v_x_1230_, 0);
v_vs_1282_ = lean_ctor_get(v_x_1230_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1284_ = v_x_1230_;
v_isShared_1285_ = v_isSharedCheck_1302_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_vs_1282_);
lean_inc(v_ks_1281_);
lean_dec(v_x_1230_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1302_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_ks_1281_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_vs_1282_);
v___x_1287_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v_newNode_1288_; uint8_t v___y_1290_; size_t v___x_1296_; uint8_t v___x_1297_; 
v_newNode_1288_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1287_, v_x_1233_, v_x_1234_);
v___x_1296_ = ((size_t)7ULL);
v___x_1297_ = lean_usize_dec_le(v___x_1296_, v_x_1232_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1298_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1288_);
v___x_1299_ = lean_unsigned_to_nat(4u);
v___x_1300_ = lean_nat_dec_lt(v___x_1298_, v___x_1299_);
lean_dec(v___x_1298_);
v___y_1290_ = v___x_1300_;
goto v___jp_1289_;
}
else
{
v___y_1290_ = v___x_1297_;
goto v___jp_1289_;
}
v___jp_1289_:
{
if (v___y_1290_ == 0)
{
lean_object* v_ks_1291_; lean_object* v_vs_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_ks_1291_ = lean_ctor_get(v_newNode_1288_, 0);
lean_inc_ref(v_ks_1291_);
v_vs_1292_ = lean_ctor_get(v_newNode_1288_, 1);
lean_inc_ref(v_vs_1292_);
lean_dec_ref(v_newNode_1288_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1232_, v_ks_1291_, v_vs_1292_, v___x_1293_, v___x_1294_);
lean_dec_ref(v_vs_1292_);
lean_dec_ref(v_ks_1291_);
return v___x_1295_;
}
else
{
return v_newNode_1288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1303_, lean_object* v_keys_1304_, lean_object* v_vals_1305_, lean_object* v_i_1306_, lean_object* v_entries_1307_){
_start:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_array_get_size(v_keys_1304_);
v___x_1309_ = lean_nat_dec_lt(v_i_1306_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec(v_i_1306_);
return v_entries_1307_;
}
else
{
lean_object* v_k_1310_; lean_object* v_v_1311_; uint64_t v___x_1312_; size_t v_h_1313_; size_t v___x_1314_; lean_object* v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v_h_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_k_1310_ = lean_array_fget_borrowed(v_keys_1304_, v_i_1306_);
v_v_1311_ = lean_array_fget_borrowed(v_vals_1305_, v_i_1306_);
v___x_1312_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1310_);
v_h_1313_ = lean_uint64_to_usize(v___x_1312_);
v___x_1314_ = ((size_t)5ULL);
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_sub(v_depth_1303_, v___x_1316_);
v___x_1318_ = lean_usize_mul(v___x_1314_, v___x_1317_);
v_h_1319_ = lean_usize_shift_right(v_h_1313_, v___x_1318_);
v___x_1320_ = lean_nat_add(v_i_1306_, v___x_1315_);
lean_dec(v_i_1306_);
lean_inc(v_v_1311_);
lean_inc(v_k_1310_);
v___x_1321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1307_, v_h_1319_, v_depth_1303_, v_k_1310_, v_v_1311_);
v_i_1306_ = v___x_1320_;
v_entries_1307_ = v___x_1321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1323_, lean_object* v_keys_1324_, lean_object* v_vals_1325_, lean_object* v_i_1326_, lean_object* v_entries_1327_){
_start:
{
size_t v_depth_boxed_1328_; lean_object* v_res_1329_; 
v_depth_boxed_1328_ = lean_unbox_usize(v_depth_1323_);
lean_dec(v_depth_1323_);
v_res_1329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1328_, v_keys_1324_, v_vals_1325_, v_i_1326_, v_entries_1327_);
lean_dec_ref(v_vals_1325_);
lean_dec_ref(v_keys_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
size_t v_x_13219__boxed_1335_; size_t v_x_13220__boxed_1336_; lean_object* v_res_1337_; 
v_x_13219__boxed_1335_ = lean_unbox_usize(v_x_1331_);
lean_dec(v_x_1331_);
v_x_13220__boxed_1336_ = lean_unbox_usize(v_x_1332_);
lean_dec(v_x_1332_);
v_res_1337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1330_, v_x_13219__boxed_1335_, v_x_13220__boxed_1336_, v_x_1333_, v_x_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint64_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1341_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1339_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1338_, v___x_1342_, v___x_1343_, v_x_1339_, v_x_1340_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1348_, lean_object* v_env_1349_, lean_object* v_forConst_1350_, lean_object* v_ctx_1351_, lean_object* v_importRealizationCtx_x3f_1352_, lean_object* v_realize_1353_, lean_object* v_opts_1354_, lean_object* v_key_1355_, lean_object* v_inst_1356_, lean_object* v_____r_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_fst_1362_; lean_object* v_snd_1363_; lean_object* v___y_1395_; lean_object* v___x_1400_; 
v___x_1359_ = lean_io_promise_new();
v___x_1360_ = lean_st_ref_take(v_realizeMapRef_1348_);
v___x_1400_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1360_, v_inst_1356_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1395_ = v___x_1401_;
goto v___jp_1394_;
}
else
{
lean_object* v_val_1402_; 
v_val_1402_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v___x_1400_, 1);
v___y_1395_ = v_val_1402_;
goto v___jp_1394_;
}
v___jp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_st_ref_set(v_realizeMapRef_1348_, v_snd_1363_);
if (lean_obj_tag(v_fst_1362_) == 1)
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v___x_1359_);
lean_dec_ref(v_opts_1354_);
lean_dec_ref(v_realize_1353_);
lean_dec(v_importRealizationCtx_x3f_1352_);
lean_dec_ref(v_ctx_1351_);
lean_dec(v_forConst_1350_);
lean_dec(v_env_1349_);
v_val_1365_ = lean_ctor_get(v_fst_1362_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_fst_1362_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1367_ = v_fst_1362_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v_fst_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_task_get_own(v_val_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v_base_1374_; lean_object* v_serverBaseExts_1375_; lean_object* v_checked_1376_; lean_object* v_asyncConstsMap_1377_; lean_object* v_asyncCtx_x3f_1378_; lean_object* v_localRealizationCtxMap_1379_; lean_object* v_allRealizations_1380_; uint8_t v_isExporting_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_fst_1362_);
v_base_1374_ = lean_ctor_get(v_env_1349_, 0);
v_serverBaseExts_1375_ = lean_ctor_get(v_env_1349_, 1);
v_checked_1376_ = lean_ctor_get(v_env_1349_, 2);
v_asyncConstsMap_1377_ = lean_ctor_get(v_env_1349_, 3);
v_asyncCtx_x3f_1378_ = lean_ctor_get(v_env_1349_, 4);
v_localRealizationCtxMap_1379_ = lean_ctor_get(v_env_1349_, 6);
v_allRealizations_1380_ = lean_ctor_get(v_env_1349_, 7);
v_isExporting_1381_ = lean_ctor_get_uint8(v_env_1349_, sizeof(void*)*8);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_env_1349_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_env_1349_, 5);
lean_dec(v_unused_1393_);
v___x_1383_ = v_env_1349_;
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_allRealizations_1380_);
lean_inc(v_localRealizationCtxMap_1379_);
lean_inc(v_asyncCtx_x3f_1378_);
lean_inc(v_asyncConstsMap_1377_);
lean_inc(v_checked_1376_);
lean_inc(v_serverBaseExts_1375_);
lean_inc(v_base_1374_);
lean_dec(v_env_1349_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1350_, v_ctx_1351_, v_localRealizationCtxMap_1379_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 6, v___x_1385_);
lean_ctor_set(v___x_1383_, 5, v_importRealizationCtx_x3f_1352_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_base_1374_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_serverBaseExts_1375_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_checked_1376_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_asyncConstsMap_1377_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_asyncCtx_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1391_, 5, v_importRealizationCtx_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1391_, 6, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1391_, 7, v_allRealizations_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1391_, sizeof(void*)*8, v_isExporting_1381_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_apply_3(v_realize_1353_, v___x_1387_, v_opts_1354_, lean_box(0));
lean_inc(v___x_1388_);
v___x_1389_ = lean_io_promise_resolve(v___x_1388_, v___x_1359_);
lean_dec(v___x_1359_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
return v___x_1390_;
}
}
}
}
v___jp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1395_, v_key_1355_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = l_IO_Promise_result_x21___redArg(v___x_1359_);
v___x_1398_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1395_, v_key_1355_, v___x_1397_);
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1356_, v___x_1398_, v___x_1360_);
v_fst_1362_ = v___x_1396_;
v_snd_1363_ = v___x_1399_;
goto v___jp_1361_;
}
else
{
lean_dec_ref(v___y_1395_);
lean_dec(v_inst_1356_);
lean_dec_ref(v_key_1355_);
v_fst_1362_ = v___x_1396_;
v_snd_1363_ = v___x_1360_;
goto v___jp_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1403_, lean_object* v_env_1404_, lean_object* v_forConst_1405_, lean_object* v_ctx_1406_, lean_object* v_importRealizationCtx_x3f_1407_, lean_object* v_realize_1408_, lean_object* v_opts_1409_, lean_object* v_key_1410_, lean_object* v_inst_1411_, lean_object* v_____r_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1403_, v_env_1404_, v_forConst_1405_, v_ctx_1406_, v_importRealizationCtx_x3f_1407_, v_realize_1408_, v_opts_1409_, v_key_1410_, v_inst_1411_, v_____r_1412_);
lean_dec(v_realizeMapRef_1403_);
return v_res_1414_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1416_) == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
else
{
lean_object* v_key_1418_; lean_object* v_tail_1419_; uint8_t v___x_1420_; 
v_key_1418_ = lean_ctor_get(v_x_1416_, 0);
v_tail_1419_ = lean_ctor_get(v_x_1416_, 2);
v___x_1420_ = lean_name_eq(v_key_1418_, v_a_1415_);
if (v___x_1420_ == 0)
{
v_x_1416_ = v_tail_1419_;
goto _start;
}
else
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1422_, lean_object* v_x_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1422_, v_x_1423_);
lean_dec(v_x_1423_);
lean_dec(v_a_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_buckets_1428_; lean_object* v___x_1429_; uint64_t v___y_1431_; 
v_buckets_1428_ = lean_ctor_get(v_m_1426_, 1);
v___x_1429_ = lean_array_get_size(v_buckets_1428_);
if (lean_obj_tag(v_a_1427_) == 0)
{
uint64_t v___x_1445_; 
v___x_1445_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_1431_ = v___x_1445_;
goto v___jp_1430_;
}
else
{
uint64_t v_hash_1446_; 
v_hash_1446_ = lean_ctor_get_uint64(v_a_1427_, sizeof(void*)*2);
v___y_1431_ = v_hash_1446_;
goto v___jp_1430_;
}
v___jp_1430_:
{
uint64_t v___x_1432_; uint64_t v___x_1433_; uint64_t v_fold_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1432_ = 32ULL;
v___x_1433_ = lean_uint64_shift_right(v___y_1431_, v___x_1432_);
v_fold_1434_ = lean_uint64_xor(v___y_1431_, v___x_1433_);
v___x_1435_ = 16ULL;
v___x_1436_ = lean_uint64_shift_right(v_fold_1434_, v___x_1435_);
v___x_1437_ = lean_uint64_xor(v_fold_1434_, v___x_1436_);
v___x_1438_ = lean_uint64_to_usize(v___x_1437_);
v___x_1439_ = lean_usize_of_nat(v___x_1429_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_sub(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_usize_land(v___x_1438_, v___x_1441_);
v___x_1443_ = lean_array_uget_borrowed(v_buckets_1428_, v___x_1442_);
v___x_1444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1427_, v___x_1443_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1447_, lean_object* v_a_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_m_1447_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1457_, lean_object* v_env_1458_, lean_object* v_forConst_1459_, lean_object* v_key_1460_, lean_object* v_realize_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v_a_1465_; lean_object* v___y_1469_; lean_object* v_base_1471_; lean_object* v_importRealizationCtx_x3f_1472_; lean_object* v_localRealizationCtxMap_1473_; uint8_t v_isExporting_1474_; lean_object* v_ctx_1476_; lean_object* v___y_1491_; 
v___x_1463_ = lean_io_get_num_heartbeats();
v_base_1471_ = lean_ctor_get(v_env_1458_, 0);
lean_inc_ref(v_base_1471_);
v_importRealizationCtx_x3f_1472_ = lean_ctor_get(v_env_1458_, 5);
lean_inc(v_importRealizationCtx_x3f_1472_);
v_localRealizationCtxMap_1473_ = lean_ctor_get(v_env_1458_, 6);
lean_inc(v_localRealizationCtxMap_1473_);
v_isExporting_1474_ = lean_ctor_get_uint8(v_env_1458_, sizeof(void*)*8);
lean_dec_ref(v_env_1458_);
if (v_isExporting_1474_ == 0)
{
lean_object* v_private_1511_; 
v_private_1511_ = lean_ctor_get(v_base_1471_, 0);
lean_inc(v_private_1511_);
lean_dec_ref(v_base_1471_);
v___y_1491_ = v_private_1511_;
goto v___jp_1490_;
}
else
{
lean_object* v_public_1512_; 
v_public_1512_ = lean_ctor_get(v_base_1471_, 1);
lean_inc(v_public_1512_);
lean_dec_ref(v_base_1471_);
v___y_1491_ = v_public_1512_;
goto v___jp_1490_;
}
v___jp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_io_set_heartbeats(v___x_1463_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1465_);
return v___x_1467_;
}
v___jp_1468_:
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___y_1469_);
v_a_1465_ = v_a_1470_;
goto v___jp_1464_;
}
v___jp_1475_:
{
lean_object* v_env_1477_; lean_object* v_opts_1478_; lean_object* v_realizeMapRef_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_env_1477_ = lean_ctor_get(v_ctx_1476_, 0);
lean_inc(v_env_1477_);
v_opts_1478_ = lean_ctor_get(v_ctx_1476_, 1);
lean_inc_ref(v_opts_1478_);
v_realizeMapRef_1479_ = lean_ctor_get(v_ctx_1476_, 2);
lean_inc(v_realizeMapRef_1479_);
v___x_1480_ = lean_st_ref_get(v_realizeMapRef_1479_);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1480_, v_inst_1457_);
lean_dec(v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 1)
{
lean_object* v_val_1482_; lean_object* v___x_1483_; 
v_val_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1482_, v_key_1460_);
lean_dec(v_val_1482_);
if (lean_obj_tag(v___x_1483_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; 
lean_dec(v_realizeMapRef_1479_);
lean_dec_ref(v_opts_1478_);
lean_dec(v_env_1477_);
lean_dec_ref(v_ctx_1476_);
lean_dec(v_importRealizationCtx_x3f_1472_);
lean_dec_ref(v_realize_1461_);
lean_dec_ref(v_key_1460_);
lean_dec(v_forConst_1459_);
lean_dec(v_inst_1457_);
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = lean_task_get_own(v_val_1484_);
v_a_1465_ = v___x_1485_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1479_, v_env_1477_, v_forConst_1459_, v_ctx_1476_, v_importRealizationCtx_x3f_1472_, v_realize_1461_, v_opts_1478_, v_key_1460_, v_inst_1457_, v___x_1486_);
lean_dec(v_realizeMapRef_1479_);
v___y_1469_ = v___x_1487_;
goto v___jp_1468_;
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec(v___x_1481_);
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1479_, v_env_1477_, v_forConst_1459_, v_ctx_1476_, v_importRealizationCtx_x3f_1472_, v_realize_1461_, v_opts_1478_, v_key_1460_, v_inst_1457_, v___x_1488_);
lean_dec(v_realizeMapRef_1479_);
v___y_1469_ = v___x_1489_;
goto v___jp_1468_;
}
}
v___jp_1490_:
{
lean_object* v_const2ModIdx_1492_; uint8_t v___x_1493_; 
v_const2ModIdx_1492_ = lean_ctor_get(v___y_1491_, 2);
lean_inc_ref(v_const2ModIdx_1492_);
lean_dec_ref(v___y_1491_);
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1492_, v_forConst_1459_);
lean_dec_ref(v_const2ModIdx_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1473_, v_forConst_1459_);
lean_dec(v_localRealizationCtxMap_1473_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v_importRealizationCtx_x3f_1472_);
lean_dec(v___x_1463_);
lean_dec_ref(v_realize_1461_);
lean_dec_ref(v_key_1460_);
v___x_1495_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1496_ = 1;
v___x_1497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1457_, v___x_1496_);
v___x_1498_ = lean_string_append(v___x_1495_, v___x_1497_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
v___x_1501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1459_, v___x_1496_);
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
else
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1494_, 1);
v_ctx_1476_ = v_val_1507_;
goto v___jp_1475_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1473_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1472_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v___x_1463_);
lean_dec_ref(v_realize_1461_);
lean_dec_ref(v_key_1460_);
lean_dec(v_forConst_1459_);
lean_dec(v_inst_1457_);
v___x_1508_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v_val_1510_; 
v_val_1510_ = lean_ctor_get(v_importRealizationCtx_x3f_1472_, 0);
lean_inc(v_val_1510_);
v_ctx_1476_ = v_val_1510_;
goto v___jp_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1513_, lean_object* v_env_1514_, lean_object* v_forConst_1515_, lean_object* v_key_1516_, lean_object* v_realize_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1513_, v_env_1514_, v_forConst_1515_, v_key_1516_, v_realize_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___f_1526_; lean_object* v___x_11359__overap_1527_; lean_object* v___x_1528_; 
v___f_1526_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_11359__overap_1527_ = lean_panic_fn_borrowed(v___f_1526_, v_msg_1520_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
v___x_1528_ = lean_apply_5(v___x_11359__overap_1527_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, lean_box(0));
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1536_, lean_object* v_inst_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
v___x_1543_ = lean_apply_5(v_realize_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_inst_1537_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_inst_1537_);
v_a_1553_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1543_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1543_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1561_, lean_object* v_inst_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1561_, v_inst_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
return v_res_1568_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = l_Lean_Options_empty;
v___x_1570_ = l_Lean_Core_getMaxHeartbeats(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_unsigned_to_nat(16u);
v___x_1573_ = lean_mk_array(v___x_1572_, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1579_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1580_ = lean_unsigned_to_nat(36u);
v___x_1581_ = lean_unsigned_to_nat(2631u);
v___x_1582_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1583_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1584_ = l_mkPanicMessageWithDecl(v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1586_ = lean_unsigned_to_nat(48u);
v___x_1587_ = lean_unsigned_to_nat(2622u);
v___x_1588_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1589_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1590_ = l_mkPanicMessageWithDecl(v___x_1589_, v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_forConst_1593_, lean_object* v_key_1594_, lean_object* v_realize_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_env_1602_; uint8_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1601_ = lean_st_ref_get(v_a_1599_);
v_env_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_env_1602_);
lean_dec(v___x_1601_);
v___x_1603_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1602_, v_forConst_1593_);
v___x_1604_ = lean_bool_not(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v_fileName_1606_; lean_object* v_fileMap_1607_; lean_object* v_ref_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1605_ = lean_io_get_num_heartbeats();
v_fileName_1606_ = lean_ctor_get(v_a_1598_, 0);
v_fileMap_1607_ = lean_ctor_get(v_a_1598_, 1);
v_ref_1608_ = lean_ctor_get(v_a_1598_, 5);
lean_inc(v_inst_1592_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1609_, 0, v_realize_1595_);
lean_closure_set(v___f_1609_, 1, v_inst_1592_);
v___x_1610_ = l_Lean_Options_empty;
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = lean_unsigned_to_nat(1000u);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1617_ = l_Lean_firstFrontendMacroScope;
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1607_);
lean_inc_ref(v_fileName_1606_);
v___x_1620_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1620_, 0, v_fileName_1606_);
lean_ctor_set(v___x_1620_, 1, v_fileMap_1607_);
lean_ctor_set(v___x_1620_, 2, v___x_1610_);
lean_ctor_set(v___x_1620_, 3, v___x_1611_);
lean_ctor_set(v___x_1620_, 4, v___x_1612_);
lean_ctor_set(v___x_1620_, 5, v___x_1613_);
lean_ctor_set(v___x_1620_, 6, v___x_1614_);
lean_ctor_set(v___x_1620_, 7, v___x_1615_);
lean_ctor_set(v___x_1620_, 8, v___x_1605_);
lean_ctor_set(v___x_1620_, 9, v___x_1616_);
lean_ctor_set(v___x_1620_, 10, v___x_1614_);
lean_ctor_set(v___x_1620_, 11, v___x_1617_);
lean_ctor_set(v___x_1620_, 12, v___x_1618_);
lean_ctor_set(v___x_1620_, 13, v___x_1619_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*14, v___x_1604_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*14 + 1, v___x_1604_);
v___x_1621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1621_, 0, v___f_1609_);
lean_closure_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1591_, v_env_1602_, v_forConst_1593_, v_key_1594_, v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1675_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1675_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1675_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1628_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1623_, v___x_1627_);
lean_dec(v_a_1623_);
if (lean_obj_tag(v___x_1628_) == 1)
{
lean_object* v_val_1629_; lean_object* v_res_x3f_1630_; lean_object* v_snap_x3f_1631_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v_snap_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; 
v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v_res_x3f_1630_ = lean_ctor_get(v_val_1629_, 0);
lean_inc_ref(v_res_x3f_1630_);
v_snap_x3f_1631_ = lean_ctor_get(v_val_1629_, 1);
lean_inc(v_snap_x3f_1631_);
lean_dec(v_val_1629_);
if (lean_obj_tag(v_snap_x3f_1631_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1666_; 
v_val_1665_ = lean_ctor_get(v_snap_x3f_1631_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_snap_x3f_1631_, 1);
v___x_1666_ = l_Lean_Syntax_getRange_x3f(v_ref_1608_, v___x_1604_);
if (lean_obj_tag(v___x_1666_) == 1)
{
lean_object* v_val_1667_; lean_object* v_start_1668_; lean_object* v_stop_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_start_1668_ = lean_ctor_get(v_val_1667_, 0);
lean_inc(v_start_1668_);
v_stop_1669_ = lean_ctor_get(v_val_1667_, 1);
lean_inc(v_stop_1669_);
lean_dec(v_val_1667_);
lean_inc_ref_n(v_fileMap_1607_, 2);
v___x_1670_ = l_Lean_FileMap_toPosition(v_fileMap_1607_, v_start_1668_);
lean_dec(v_start_1668_);
v___x_1671_ = l_Lean_FileMap_toPosition(v_fileMap_1607_, v_stop_1669_);
lean_dec(v_stop_1669_);
v___x_1672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1665_, v___x_1670_, v___x_1671_);
v_snap_1650_ = v___x_1672_;
v___y_1651_ = v_a_1596_;
v___y_1652_ = v_a_1597_;
v___y_1653_ = v_a_1598_;
v___y_1654_ = v_a_1599_;
goto v___jp_1649_;
}
else
{
lean_dec(v___x_1666_);
v_snap_1650_ = v_val_1665_;
v___y_1651_ = v_a_1596_;
v___y_1652_ = v_a_1597_;
v___y_1653_ = v_a_1598_;
v___y_1654_ = v_a_1599_;
goto v___jp_1649_;
}
}
else
{
lean_dec(v_snap_x3f_1631_);
v___y_1633_ = v_a_1596_;
v___y_1634_ = v_a_1597_;
v___y_1635_ = v_a_1598_;
v___y_1636_ = v_a_1599_;
goto v___jp_1632_;
}
v___jp_1632_:
{
if (lean_obj_tag(v_res_x3f_1630_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; 
lean_dec(v_inst_1592_);
v_a_1637_ = lean_ctor_get(v_res_x3f_1630_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v_res_x3f_1630_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 1);
lean_ctor_set(v___x_1625_, 0, v_a_1637_);
v___x_1639_ = v___x_1625_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v_res_x3f_1630_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v_res_x3f_1630_, 1);
v___x_1642_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1641_, v_inst_1592_);
lean_dec(v_inst_1592_);
lean_dec(v_a_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1625_);
v___x_1643_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1644_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1643_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1644_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; 
v_val_1645_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v___x_1642_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_val_1645_);
v___x_1647_ = v___x_1625_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_val_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
v___jp_1649_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1618_, v_snap_1650_);
v___x_1656_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1655_, v___y_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
v___y_1633_ = v___y_1651_;
v___y_1634_ = v___y_1652_;
v___y_1635_ = v___y_1653_;
v___y_1636_ = v___y_1654_;
goto v___jp_1632_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_res_x3f_1630_);
lean_del_object(v___x_1625_);
lean_dec(v_inst_1592_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec(v___x_1628_);
lean_del_object(v___x_1625_);
lean_dec(v_inst_1592_);
v___x_1673_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1674_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1673_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_inst_1592_);
v_a_1676_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1678_ = v___x_1622_;
v_isShared_1679_ = v_isSharedCheck_1687_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1622_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1687_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1680_ = lean_io_error_to_string(v_a_1676_);
v___x_1681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
v___x_1682_ = l_Lean_MessageData_ofFormat(v___x_1681_);
lean_inc(v_ref_1608_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_ref_1608_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1683_);
v___x_1685_ = v___x_1678_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v___x_1688_; 
lean_dec_ref(v_env_1602_);
lean_dec_ref(v_key_1594_);
lean_dec(v_forConst_1593_);
lean_dec(v_inst_1592_);
lean_dec(v_inst_1591_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
lean_inc(v_a_1597_);
lean_inc_ref(v_a_1596_);
v___x_1688_ = lean_apply_5(v_realize_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, lean_box(0));
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_forConst_1691_, lean_object* v_key_1692_, lean_object* v_realize_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1689_, v_inst_1690_, v_forConst_1691_, v_key_1692_, v_realize_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_i_1702_, lean_object* v_k_1703_){
_start:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_array_get_size(v_keys_1700_);
v___x_1705_ = lean_nat_dec_lt(v_i_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_i_1702_);
v___x_1706_ = lean_box(0);
return v___x_1706_;
}
else
{
lean_object* v_k_x27_1707_; uint8_t v___x_1708_; 
v_k_x27_1707_ = lean_array_fget_borrowed(v_keys_1700_, v_i_1702_);
v___x_1708_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1703_, v_k_x27_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_i_1702_, v___x_1709_);
lean_dec(v_i_1702_);
v_i_1702_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_array_fget_borrowed(v_vals_1701_, v_i_1702_);
lean_dec(v_i_1702_);
lean_inc(v___x_1712_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_i_1716_, lean_object* v_k_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1714_, v_vals_1715_, v_i_1716_, v_k_1717_);
lean_dec_ref(v_k_1717_);
lean_dec_ref(v_vals_1715_);
lean_dec_ref(v_keys_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1719_, size_t v_x_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_object* v_es_1722_; lean_object* v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v_j_1726_; lean_object* v___x_1727_; 
v_es_1722_ = lean_ctor_get(v_x_1719_, 0);
v___x_1723_ = lean_box(2);
v___x_1724_ = ((size_t)31ULL);
v___x_1725_ = lean_usize_land(v_x_1720_, v___x_1724_);
v_j_1726_ = lean_usize_to_nat(v___x_1725_);
v___x_1727_ = lean_array_get_borrowed(v___x_1723_, v_es_1722_, v_j_1726_);
lean_dec(v_j_1726_);
switch(lean_obj_tag(v___x_1727_))
{
case 0:
{
lean_object* v_key_1728_; lean_object* v_val_1729_; uint8_t v___x_1730_; 
v_key_1728_ = lean_ctor_get(v___x_1727_, 0);
v_val_1729_ = lean_ctor_get(v___x_1727_, 1);
v___x_1730_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1721_, v_key_1728_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_box(0);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
lean_inc(v_val_1729_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_val_1729_);
return v___x_1732_;
}
}
case 1:
{
lean_object* v_node_1733_; size_t v___x_1734_; size_t v___x_1735_; 
v_node_1733_ = lean_ctor_get(v___x_1727_, 0);
v___x_1734_ = ((size_t)5ULL);
v___x_1735_ = lean_usize_shift_right(v_x_1720_, v___x_1734_);
v_x_1719_ = v_node_1733_;
v_x_1720_ = v___x_1735_;
goto _start;
}
default: 
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_box(0);
return v___x_1737_;
}
}
}
else
{
lean_object* v_ks_1738_; lean_object* v_vs_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_ks_1738_ = lean_ctor_get(v_x_1719_, 0);
v_vs_1739_ = lean_ctor_get(v_x_1719_, 1);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1738_, v_vs_1739_, v___x_1740_, v_x_1721_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
size_t v_x_13965__boxed_1745_; lean_object* v_res_1746_; 
v_x_13965__boxed_1745_ = lean_unbox_usize(v_x_1743_);
lean_dec(v_x_1743_);
v_res_1746_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1742_, v_x_13965__boxed_1745_, v_x_1744_);
lean_dec_ref(v_x_1744_);
lean_dec_ref(v_x_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
uint64_t v_configKey_1749_; lean_object* v_expr_1750_; lean_object* v_nargs_x3f_1751_; uint64_t v___x_1752_; uint64_t v___y_1754_; 
v_configKey_1749_ = lean_ctor_get_uint64(v_x_1748_, sizeof(void*)*2);
v_expr_1750_ = lean_ctor_get(v_x_1748_, 0);
v_nargs_x3f_1751_ = lean_ctor_get(v_x_1748_, 1);
v___x_1752_ = l_Lean_Expr_hash(v_expr_1750_);
if (lean_obj_tag(v_nargs_x3f_1751_) == 0)
{
uint64_t v___x_1759_; 
v___x_1759_ = 11ULL;
v___y_1754_ = v___x_1759_;
goto v___jp_1753_;
}
else
{
lean_object* v_val_1760_; uint64_t v___x_1761_; uint64_t v___x_1762_; uint64_t v___x_1763_; 
v_val_1760_ = lean_ctor_get(v_nargs_x3f_1751_, 0);
v___x_1761_ = lean_uint64_of_nat(v_val_1760_);
v___x_1762_ = 13ULL;
v___x_1763_ = lean_uint64_mix_hash(v___x_1761_, v___x_1762_);
v___y_1754_ = v___x_1763_;
goto v___jp_1753_;
}
v___jp_1753_:
{
uint64_t v___x_1755_; uint64_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = lean_uint64_mix_hash(v___x_1752_, v___y_1754_);
v___x_1756_ = lean_uint64_mix_hash(v_configKey_1749_, v___x_1755_);
v___x_1757_ = lean_uint64_to_usize(v___x_1756_);
v___x_1758_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1747_, v___x_1757_, v_x_1748_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1764_, v_x_1765_);
lean_dec_ref(v_x_1765_);
lean_dec_ref(v_x_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v_ks_1771_; lean_object* v_vs_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1796_; 
v_ks_1771_ = lean_ctor_get(v_x_1767_, 0);
v_vs_1772_ = lean_ctor_get(v_x_1767_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1767_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1774_ = v_x_1767_;
v_isShared_1775_ = v_isSharedCheck_1796_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_vs_1772_);
lean_inc(v_ks_1771_);
lean_dec(v_x_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1796_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_array_get_size(v_ks_1771_);
v___x_1777_ = lean_nat_dec_lt(v_x_1768_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec(v_x_1768_);
v___x_1778_ = lean_array_push(v_ks_1771_, v_x_1769_);
v___x_1779_ = lean_array_push(v_vs_1772_, v_x_1770_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v___x_1779_);
lean_ctor_set(v___x_1774_, 0, v___x_1778_);
v___x_1781_ = v___x_1774_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v_k_x27_1783_; uint8_t v___x_1784_; 
v_k_x27_1783_ = lean_array_fget_borrowed(v_ks_1771_, v_x_1768_);
v___x_1784_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1769_, v_k_x27_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1786_; 
if (v_isShared_1775_ == 0)
{
v___x_1786_ = v___x_1774_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_ks_1771_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_vs_1772_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_x_1768_, v___x_1787_);
lean_dec(v_x_1768_);
v_x_1767_ = v___x_1786_;
v_x_1768_ = v___x_1788_;
goto _start;
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1791_ = lean_array_fset(v_ks_1771_, v_x_1768_, v_x_1769_);
v___x_1792_ = lean_array_fset(v_vs_1772_, v_x_1768_, v_x_1770_);
lean_dec(v_x_1768_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v___x_1792_);
lean_ctor_set(v___x_1774_, 0, v___x_1791_);
v___x_1794_ = v___x_1774_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1797_, lean_object* v_k_1798_, lean_object* v_v_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1797_, v___x_1800_, v_k_1798_, v_v_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1803_, size_t v_x_1804_, size_t v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 0)
{
lean_object* v_es_1808_; size_t v___x_1809_; size_t v___x_1810_; lean_object* v_j_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_es_1808_ = lean_ctor_get(v_x_1803_, 0);
v___x_1809_ = ((size_t)31ULL);
v___x_1810_ = lean_usize_land(v_x_1804_, v___x_1809_);
v_j_1811_ = lean_usize_to_nat(v___x_1810_);
v___x_1812_ = lean_array_get_size(v_es_1808_);
v___x_1813_ = lean_nat_dec_lt(v_j_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_dec(v_j_1811_);
lean_dec(v_x_1807_);
lean_dec_ref(v_x_1806_);
return v_x_1803_;
}
else
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1852_; 
lean_inc_ref(v_es_1808_);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_x_1803_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v_x_1803_, 0);
lean_dec(v_unused_1853_);
v___x_1815_ = v_x_1803_;
v_isShared_1816_ = v_isSharedCheck_1852_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v_x_1803_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1852_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_v_1817_; lean_object* v___x_1818_; lean_object* v_xs_x27_1819_; lean_object* v___y_1821_; 
v_v_1817_ = lean_array_fget(v_es_1808_, v_j_1811_);
v___x_1818_ = lean_box(0);
v_xs_x27_1819_ = lean_array_fset(v_es_1808_, v_j_1811_, v___x_1818_);
switch(lean_obj_tag(v_v_1817_))
{
case 0:
{
lean_object* v_key_1826_; lean_object* v_val_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1837_; 
v_key_1826_ = lean_ctor_get(v_v_1817_, 0);
v_val_1827_ = lean_ctor_get(v_v_1817_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_v_1817_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1829_ = v_v_1817_;
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_val_1827_);
lean_inc(v_key_1826_);
lean_dec(v_v_1817_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1806_, v_key_1826_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_del_object(v___x_1829_);
v___x_1832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1826_, v_val_1827_, v_x_1806_, v_x_1807_);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
v___y_1821_ = v___x_1833_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1835_; 
lean_dec(v_val_1827_);
lean_dec(v_key_1826_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v_x_1807_);
lean_ctor_set(v___x_1829_, 0, v_x_1806_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_x_1806_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_x_1807_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v___y_1821_ = v___x_1835_;
goto v___jp_1820_;
}
}
}
}
case 1:
{
lean_object* v_node_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1850_; 
v_node_1838_ = lean_ctor_get(v_v_1817_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_v_1817_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1840_ = v_v_1817_;
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_node_1838_);
lean_dec(v_v_1817_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1850_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
size_t v___x_1842_; size_t v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1842_ = ((size_t)5ULL);
v___x_1843_ = lean_usize_shift_right(v_x_1804_, v___x_1842_);
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_x_1805_, v___x_1844_);
v___x_1846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1838_, v___x_1843_, v___x_1845_, v_x_1806_, v_x_1807_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1846_);
v___x_1848_ = v___x_1840_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v___y_1821_ = v___x_1848_;
goto v___jp_1820_;
}
}
}
default: 
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_x_1806_);
lean_ctor_set(v___x_1851_, 1, v_x_1807_);
v___y_1821_ = v___x_1851_;
goto v___jp_1820_;
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_array_fset(v_xs_x27_1819_, v_j_1811_, v___y_1821_);
lean_dec(v_j_1811_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1822_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
else
{
lean_object* v_ks_1854_; lean_object* v_vs_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1875_; 
v_ks_1854_ = lean_ctor_get(v_x_1803_, 0);
v_vs_1855_ = lean_ctor_get(v_x_1803_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_x_1803_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1857_ = v_x_1803_;
v_isShared_1858_ = v_isSharedCheck_1875_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_vs_1855_);
lean_inc(v_ks_1854_);
lean_dec(v_x_1803_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1875_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_ks_1854_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_vs_1855_);
v___x_1860_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v_newNode_1861_; uint8_t v___y_1863_; size_t v___x_1869_; uint8_t v___x_1870_; 
v_newNode_1861_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1860_, v_x_1806_, v_x_1807_);
v___x_1869_ = ((size_t)7ULL);
v___x_1870_ = lean_usize_dec_le(v___x_1869_, v_x_1805_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1871_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1861_);
v___x_1872_ = lean_unsigned_to_nat(4u);
v___x_1873_ = lean_nat_dec_lt(v___x_1871_, v___x_1872_);
lean_dec(v___x_1871_);
v___y_1863_ = v___x_1873_;
goto v___jp_1862_;
}
else
{
v___y_1863_ = v___x_1870_;
goto v___jp_1862_;
}
v___jp_1862_:
{
if (v___y_1863_ == 0)
{
lean_object* v_ks_1864_; lean_object* v_vs_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_ks_1864_ = lean_ctor_get(v_newNode_1861_, 0);
lean_inc_ref(v_ks_1864_);
v_vs_1865_ = lean_ctor_get(v_newNode_1861_, 1);
lean_inc_ref(v_vs_1865_);
lean_dec_ref(v_newNode_1861_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1805_, v_ks_1864_, v_vs_1865_, v___x_1866_, v___x_1867_);
lean_dec_ref(v_vs_1865_);
lean_dec_ref(v_ks_1864_);
return v___x_1868_;
}
else
{
return v_newNode_1861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1876_, lean_object* v_keys_1877_, lean_object* v_vals_1878_, lean_object* v_i_1879_, lean_object* v_entries_1880_){
_start:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_array_get_size(v_keys_1877_);
v___x_1882_ = lean_nat_dec_lt(v_i_1879_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_dec(v_i_1879_);
return v_entries_1880_;
}
else
{
lean_object* v_k_1883_; uint64_t v_configKey_1884_; lean_object* v_expr_1885_; lean_object* v_nargs_x3f_1886_; lean_object* v_v_1887_; uint64_t v___x_1888_; uint64_t v___y_1890_; 
v_k_1883_ = lean_array_fget_borrowed(v_keys_1877_, v_i_1879_);
v_configKey_1884_ = lean_ctor_get_uint64(v_k_1883_, sizeof(void*)*2);
v_expr_1885_ = lean_ctor_get(v_k_1883_, 0);
v_nargs_x3f_1886_ = lean_ctor_get(v_k_1883_, 1);
v_v_1887_ = lean_array_fget_borrowed(v_vals_1878_, v_i_1879_);
v___x_1888_ = l_Lean_Expr_hash(v_expr_1885_);
if (lean_obj_tag(v_nargs_x3f_1886_) == 0)
{
uint64_t v___x_1903_; 
v___x_1903_ = 11ULL;
v___y_1890_ = v___x_1903_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1904_; uint64_t v___x_1905_; uint64_t v___x_1906_; uint64_t v___x_1907_; 
v_val_1904_ = lean_ctor_get(v_nargs_x3f_1886_, 0);
v___x_1905_ = lean_uint64_of_nat(v_val_1904_);
v___x_1906_ = 13ULL;
v___x_1907_ = lean_uint64_mix_hash(v___x_1905_, v___x_1906_);
v___y_1890_ = v___x_1907_;
goto v___jp_1889_;
}
v___jp_1889_:
{
uint64_t v___x_1891_; uint64_t v___x_1892_; size_t v_h_1893_; size_t v___x_1894_; lean_object* v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v_h_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1891_ = lean_uint64_mix_hash(v___x_1888_, v___y_1890_);
v___x_1892_ = lean_uint64_mix_hash(v_configKey_1884_, v___x_1891_);
v_h_1893_ = lean_uint64_to_usize(v___x_1892_);
v___x_1894_ = ((size_t)5ULL);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = ((size_t)1ULL);
v___x_1897_ = lean_usize_sub(v_depth_1876_, v___x_1896_);
v___x_1898_ = lean_usize_mul(v___x_1894_, v___x_1897_);
v_h_1899_ = lean_usize_shift_right(v_h_1893_, v___x_1898_);
v___x_1900_ = lean_nat_add(v_i_1879_, v___x_1895_);
lean_dec(v_i_1879_);
lean_inc(v_v_1887_);
lean_inc(v_k_1883_);
v___x_1901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1880_, v_h_1899_, v_depth_1876_, v_k_1883_, v_v_1887_);
v_i_1879_ = v___x_1900_;
v_entries_1880_ = v___x_1901_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1908_, lean_object* v_keys_1909_, lean_object* v_vals_1910_, lean_object* v_i_1911_, lean_object* v_entries_1912_){
_start:
{
size_t v_depth_boxed_1913_; lean_object* v_res_1914_; 
v_depth_boxed_1913_ = lean_unbox_usize(v_depth_1908_);
lean_dec(v_depth_1908_);
v_res_1914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1913_, v_keys_1909_, v_vals_1910_, v_i_1911_, v_entries_1912_);
lean_dec_ref(v_vals_1910_);
lean_dec_ref(v_keys_1909_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
size_t v_x_14136__boxed_1920_; size_t v_x_14137__boxed_1921_; lean_object* v_res_1922_; 
v_x_14136__boxed_1920_ = lean_unbox_usize(v_x_1916_);
lean_dec(v_x_1916_);
v_x_14137__boxed_1921_ = lean_unbox_usize(v_x_1917_);
lean_dec(v_x_1917_);
v_res_1922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1915_, v_x_14136__boxed_1920_, v_x_14137__boxed_1921_, v_x_1918_, v_x_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
uint64_t v_configKey_1926_; lean_object* v_expr_1927_; lean_object* v_nargs_x3f_1928_; uint64_t v___x_1929_; uint64_t v___y_1931_; 
v_configKey_1926_ = lean_ctor_get_uint64(v_x_1924_, sizeof(void*)*2);
v_expr_1927_ = lean_ctor_get(v_x_1924_, 0);
v_nargs_x3f_1928_ = lean_ctor_get(v_x_1924_, 1);
v___x_1929_ = l_Lean_Expr_hash(v_expr_1927_);
if (lean_obj_tag(v_nargs_x3f_1928_) == 0)
{
uint64_t v___x_1937_; 
v___x_1937_ = 11ULL;
v___y_1931_ = v___x_1937_;
goto v___jp_1930_;
}
else
{
lean_object* v_val_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; 
v_val_1938_ = lean_ctor_get(v_nargs_x3f_1928_, 0);
v___x_1939_ = lean_uint64_of_nat(v_val_1938_);
v___x_1940_ = 13ULL;
v___x_1941_ = lean_uint64_mix_hash(v___x_1939_, v___x_1940_);
v___y_1931_ = v___x_1941_;
goto v___jp_1930_;
}
v___jp_1930_:
{
uint64_t v___x_1932_; uint64_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1932_ = lean_uint64_mix_hash(v___x_1929_, v___y_1931_);
v___x_1933_ = lean_uint64_mix_hash(v_configKey_1926_, v___x_1932_);
v___x_1934_ = lean_uint64_to_usize(v___x_1933_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1923_, v___x_1934_, v___x_1935_, v_x_1924_, v_x_1925_);
return v___x_1936_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1942_){
_start:
{
if (lean_obj_tag(v_x_1942_) == 0)
{
uint8_t v___x_1943_; 
v___x_1943_ = 0;
return v___x_1943_;
}
else
{
lean_object* v_head_1944_; lean_object* v_tail_1945_; uint8_t v___x_1946_; 
v_head_1944_ = lean_ctor_get(v_x_1942_, 0);
v_tail_1945_ = lean_ctor_get(v_x_1942_, 1);
v___x_1946_ = l_Lean_Level_hasMVar(v_head_1944_);
if (v___x_1946_ == 0)
{
v_x_1942_ = v_tail_1945_;
goto _start;
}
else
{
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1948_){
_start:
{
uint8_t v_res_1949_; lean_object* v_r_1950_; 
v_res_1949_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1948_);
lean_dec(v_x_1948_);
v_r_1950_ = lean_box(v_res_1949_);
return v_r_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1953_, lean_object* v_maxArgs_x3f_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; 
lean_inc(v_maxArgs_x3f_1954_);
lean_inc_ref(v_fn_1953_);
v___x_1960_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1953_, v_maxArgs_x3f_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2025_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_2025_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2025_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_finfo_1966_; lean_object* v___y_1967_; lean_object* v___x_1999_; lean_object* v_cache_2000_; lean_object* v_funInfo_2001_; lean_object* v___x_2002_; 
v___x_1999_ = lean_st_ref_get(v_a_1956_);
v_cache_2000_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_cache_2000_);
lean_dec(v___x_1999_);
v_funInfo_2001_ = lean_ctor_get(v_cache_2000_, 1);
lean_inc_ref(v_funInfo_2001_);
lean_dec_ref(v_cache_2000_);
v___x_2002_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_2001_, v_a_1961_);
lean_dec_ref(v_funInfo_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___f_2003_; lean_object* v___f_2004_; 
v___f_2003_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1954_);
lean_inc_ref(v_fn_1953_);
v___f_2004_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2004_, 0, v_fn_1953_);
lean_closure_set(v___f_2004_, 1, v_maxArgs_x3f_1954_);
lean_closure_set(v___f_2004_, 2, v___f_2003_);
if (lean_obj_tag(v_fn_1953_) == 4)
{
lean_object* v_declName_2005_; lean_object* v_us_2006_; uint8_t v___x_2007_; 
v_declName_2005_ = lean_ctor_get(v_fn_1953_, 0);
v_us_2006_ = lean_ctor_get(v_fn_1953_, 1);
v___x_2007_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_inc(v_us_2006_);
lean_inc_n(v_declName_2005_, 2);
lean_dec_ref_known(v_fn_1953_, 2);
v___x_2008_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_2009_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_2010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2010_, 0, v_declName_2005_);
lean_ctor_set(v___x_2010_, 1, v_us_2006_);
lean_ctor_set(v___x_2010_, 2, v_maxArgs_x3f_1954_);
v___x_2011_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_2008_, v___x_2009_, v_declName_2005_, v___x_2010_, v___f_2004_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v_finfo_1966_ = v_a_2012_;
v___y_1967_ = v_a_1956_;
goto v___jp_1965_;
}
else
{
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
return v___x_2011_;
}
}
else
{
lean_object* v___x_2013_; 
lean_dec_ref(v___f_2004_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1957_);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
v___x_2013_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1953_, v_maxArgs_x3f_1954_, v___f_2003_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v_finfo_1966_ = v_a_2014_;
v___y_1967_ = v_a_1956_;
goto v___jp_1965_;
}
else
{
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
return v___x_2013_;
}
}
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref(v___f_2004_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1957_);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
v___x_2015_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1953_, v_maxArgs_x3f_1954_, v___f_2003_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v_finfo_1966_ = v_a_2016_;
v___y_1967_ = v_a_1956_;
goto v___jp_1965_;
}
else
{
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
return v___x_2015_;
}
}
}
else
{
lean_object* v_val_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
lean_dec(v_maxArgs_x3f_1954_);
lean_dec_ref(v_fn_1953_);
v_val_2017_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2002_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_val_2017_);
lean_dec(v___x_2002_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 0);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_val_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
v___jp_1965_:
{
lean_object* v___x_1968_; lean_object* v_cache_1969_; lean_object* v_mctx_1970_; lean_object* v_zetaDeltaFVarIds_1971_; lean_object* v_postponed_1972_; lean_object* v_diag_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1998_; 
v___x_1968_ = lean_st_ref_take(v___y_1967_);
v_cache_1969_ = lean_ctor_get(v___x_1968_, 1);
v_mctx_1970_ = lean_ctor_get(v___x_1968_, 0);
v_zetaDeltaFVarIds_1971_ = lean_ctor_get(v___x_1968_, 2);
v_postponed_1972_ = lean_ctor_get(v___x_1968_, 3);
v_diag_1973_ = lean_ctor_get(v___x_1968_, 4);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1975_ = v___x_1968_;
v_isShared_1976_ = v_isSharedCheck_1998_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_diag_1973_);
lean_inc(v_postponed_1972_);
lean_inc(v_zetaDeltaFVarIds_1971_);
lean_inc(v_cache_1969_);
lean_inc(v_mctx_1970_);
lean_dec(v___x_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1998_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_inferType_1977_; lean_object* v_funInfo_1978_; lean_object* v_synthInstance_1979_; lean_object* v_whnf_1980_; lean_object* v_defEqTrans_1981_; lean_object* v_defEqPerm_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1997_; 
v_inferType_1977_ = lean_ctor_get(v_cache_1969_, 0);
v_funInfo_1978_ = lean_ctor_get(v_cache_1969_, 1);
v_synthInstance_1979_ = lean_ctor_get(v_cache_1969_, 2);
v_whnf_1980_ = lean_ctor_get(v_cache_1969_, 3);
v_defEqTrans_1981_ = lean_ctor_get(v_cache_1969_, 4);
v_defEqPerm_1982_ = lean_ctor_get(v_cache_1969_, 5);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_cache_1969_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1984_ = v_cache_1969_;
v_isShared_1985_ = v_isSharedCheck_1997_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_defEqPerm_1982_);
lean_inc(v_defEqTrans_1981_);
lean_inc(v_whnf_1980_);
lean_inc(v_synthInstance_1979_);
lean_inc(v_funInfo_1978_);
lean_inc(v_inferType_1977_);
lean_dec(v_cache_1969_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1997_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_inc_ref(v_finfo_1966_);
v___x_1986_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1978_, v_a_1961_, v_finfo_1966_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_inferType_1977_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_synthInstance_1979_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_whnf_1980_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_defEqTrans_1981_);
lean_ctor_set(v_reuseFailAlloc_1996_, 5, v_defEqPerm_1982_);
v___x_1988_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_1988_);
v___x_1990_ = v___x_1975_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_mctx_1970_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_zetaDeltaFVarIds_1971_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_postponed_1972_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_diag_1973_);
v___x_1990_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_st_ref_set(v___y_1967_, v___x_1990_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_finfo_1966_);
v___x_1993_ = v___x_1963_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_finfo_1966_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
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
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_maxArgs_x3f_1954_);
lean_dec_ref(v_fn_1953_);
v_a_2026_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1960_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1960_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_2034_, lean_object* v_maxArgs_x3f_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2034_, v_maxArgs_x3f_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
return v_res_2041_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_2042_, lean_object* v_k_2043_, lean_object* v_t_2044_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_2043_, v_t_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2046_, lean_object* v_k_2047_, lean_object* v_t_2048_){
_start:
{
uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_res_2049_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2046_, v_k_2047_, v_t_2048_);
lean_dec(v_t_2048_);
lean_dec(v_k_2047_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2051_, lean_object* v_val_2052_, lean_object* v___x_2053_, lean_object* v_fvars_2054_, uint8_t v___y_2055_, lean_object* v_inst_2056_, lean_object* v_R_2057_, lean_object* v_a_2058_, lean_object* v_b_2059_, lean_object* v_c_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2051_, v_val_2052_, v___x_2053_, v_fvars_2054_, v___y_2055_, v_a_2058_, v_b_2059_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2067_, lean_object* v_val_2068_, lean_object* v___x_2069_, lean_object* v_fvars_2070_, lean_object* v___y_2071_, lean_object* v_inst_2072_, lean_object* v_R_2073_, lean_object* v_a_2074_, lean_object* v_b_2075_, lean_object* v_c_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v___y_14491__boxed_2082_; lean_object* v_res_2083_; 
v___y_14491__boxed_2082_ = lean_unbox(v___y_2071_);
v_res_2083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2067_, v_val_2068_, v___x_2069_, v_fvars_2070_, v___y_14491__boxed_2082_, v_inst_2072_, v_R_2073_, v_a_2074_, v_b_2075_, v_c_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_fvars_2070_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v_val_2068_);
lean_dec(v_upperBound_2067_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2084_, lean_object* v_fvars_2085_, lean_object* v_inst_2086_, lean_object* v_R_2087_, lean_object* v_a_2088_, lean_object* v_b_2089_, lean_object* v_c_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2084_, v_fvars_2085_, v_a_2088_, v_b_2089_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2097_, lean_object* v_fvars_2098_, lean_object* v_inst_2099_, lean_object* v_R_2100_, lean_object* v_a_2101_, lean_object* v_b_2102_, lean_object* v_c_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2097_, v_fvars_2098_, v_inst_2099_, v_R_2100_, v_a_2101_, v_b_2102_, v_c_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_fvars_2098_);
lean_dec(v_upperBound_2097_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2111_, v_x_2112_, v_x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2116_, v_x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2119_, lean_object* v_x_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2119_, v_x_2120_, v_x_2121_);
lean_dec_ref(v_x_2121_);
lean_dec_ref(v_x_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2123_, lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2131_, v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_forConst_2142_, lean_object* v_key_2143_, lean_object* v_realize_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2140_, v_inst_2141_, v_forConst_2142_, v_key_2143_, v_realize_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_forConst_2154_, lean_object* v_key_2155_, lean_object* v_realize_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2151_, v_inst_2152_, v_inst_2153_, v_forConst_2154_, v_key_2155_, v_realize_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2163_, lean_object* v_x_2164_, size_t v_x_2165_, size_t v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2164_, v_x_2165_, v_x_2166_, v_x_2167_, v_x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
size_t v_x_14588__boxed_2176_; size_t v_x_14589__boxed_2177_; lean_object* v_res_2178_; 
v_x_14588__boxed_2176_ = lean_unbox_usize(v_x_2172_);
lean_dec(v_x_2172_);
v_x_14589__boxed_2177_ = lean_unbox_usize(v_x_2173_);
lean_dec(v_x_2173_);
v_res_2178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2170_, v_x_2171_, v_x_14588__boxed_2176_, v_x_14589__boxed_2177_, v_x_2174_, v_x_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2179_, lean_object* v_x_2180_, size_t v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2180_, v_x_2181_, v_x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
size_t v_x_14605__boxed_2188_; lean_object* v_res_2189_; 
v_x_14605__boxed_2188_ = lean_unbox_usize(v_x_2186_);
lean_dec(v_x_2186_);
v_res_2189_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2184_, v_x_2185_, v_x_14605__boxed_2188_, v_x_2187_);
lean_dec_ref(v_x_2187_);
lean_dec_ref(v_x_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2190_, lean_object* v_n_2191_, lean_object* v_k_2192_, lean_object* v_v_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2191_, v_k_2192_, v_v_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2195_, size_t v_depth_2196_, lean_object* v_keys_2197_, lean_object* v_vals_2198_, lean_object* v_heq_2199_, lean_object* v_i_2200_, lean_object* v_entries_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2196_, v_keys_2197_, v_vals_2198_, v_i_2200_, v_entries_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2203_, lean_object* v_depth_2204_, lean_object* v_keys_2205_, lean_object* v_vals_2206_, lean_object* v_heq_2207_, lean_object* v_i_2208_, lean_object* v_entries_2209_){
_start:
{
size_t v_depth_boxed_2210_; lean_object* v_res_2211_; 
v_depth_boxed_2210_ = lean_unbox_usize(v_depth_2204_);
lean_dec(v_depth_2204_);
v_res_2211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2203_, v_depth_boxed_2210_, v_keys_2205_, v_vals_2206_, v_heq_2207_, v_i_2208_, v_entries_2209_);
lean_dec_ref(v_vals_2206_);
lean_dec_ref(v_keys_2205_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2212_, lean_object* v_keys_2213_, lean_object* v_vals_2214_, lean_object* v_heq_2215_, lean_object* v_i_2216_, lean_object* v_k_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2213_, v_vals_2214_, v_i_2216_, v_k_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_keys_2220_, lean_object* v_vals_2221_, lean_object* v_heq_2222_, lean_object* v_i_2223_, lean_object* v_k_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2219_, v_keys_2220_, v_vals_2221_, v_heq_2222_, v_i_2223_, v_k_2224_);
lean_dec_ref(v_k_2224_);
lean_dec_ref(v_vals_2221_);
lean_dec_ref(v_keys_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2227_, v_x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2230_, v_x_2231_, v_x_2232_);
lean_dec_ref(v_x_2232_);
lean_dec_ref(v_x_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2235_, v_x_2236_, v_x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2239_, lean_object* v_m_2240_, lean_object* v_a_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2240_, v_a_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2243_, lean_object* v_m_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_res_2246_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2243_, v_m_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_m_2244_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2249_, v_x_2250_, v_x_2251_, v_x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2254_, lean_object* v_x_2255_, size_t v_x_2256_, lean_object* v_x_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2255_, v_x_2256_, v_x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_){
_start:
{
size_t v_x_14650__boxed_2263_; lean_object* v_res_2264_; 
v_x_14650__boxed_2263_ = lean_unbox_usize(v_x_2261_);
lean_dec(v_x_2261_);
v_res_2264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2259_, v_x_2260_, v_x_14650__boxed_2263_, v_x_2262_);
lean_dec_ref(v_x_2262_);
lean_dec_ref(v_x_2260_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2265_, lean_object* v_x_2266_, size_t v_x_2267_, size_t v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2266_, v_x_2267_, v_x_2268_, v_x_2269_, v_x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
size_t v_x_14661__boxed_2278_; size_t v_x_14662__boxed_2279_; lean_object* v_res_2280_; 
v_x_14661__boxed_2278_ = lean_unbox_usize(v_x_2274_);
lean_dec(v_x_2274_);
v_x_14662__boxed_2279_ = lean_unbox_usize(v_x_2275_);
lean_dec(v_x_2275_);
v_res_2280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2272_, v_x_2273_, v_x_14661__boxed_2278_, v_x_14662__boxed_2279_, v_x_2276_, v_x_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2281_, lean_object* v_a_2282_, lean_object* v_x_2283_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2282_, v_x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_a_2286_, lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2285_, v_a_2286_, v_x_2287_);
lean_dec(v_x_2287_);
lean_dec(v_a_2286_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2290_, lean_object* v_keys_2291_, lean_object* v_vals_2292_, lean_object* v_heq_2293_, lean_object* v_i_2294_, lean_object* v_k_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2291_, v_vals_2292_, v_i_2294_, v_k_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2297_, lean_object* v_keys_2298_, lean_object* v_vals_2299_, lean_object* v_heq_2300_, lean_object* v_i_2301_, lean_object* v_k_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2297_, v_keys_2298_, v_vals_2299_, v_heq_2300_, v_i_2301_, v_k_2302_);
lean_dec_ref(v_k_2302_);
lean_dec_ref(v_vals_2299_);
lean_dec_ref(v_keys_2298_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2304_, lean_object* v_n_2305_, lean_object* v_k_2306_, lean_object* v_v_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2305_, v_k_2306_, v_v_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2309_, size_t v_depth_2310_, lean_object* v_keys_2311_, lean_object* v_vals_2312_, lean_object* v_heq_2313_, lean_object* v_i_2314_, lean_object* v_entries_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2310_, v_keys_2311_, v_vals_2312_, v_i_2314_, v_entries_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_depth_2318_, lean_object* v_keys_2319_, lean_object* v_vals_2320_, lean_object* v_heq_2321_, lean_object* v_i_2322_, lean_object* v_entries_2323_){
_start:
{
size_t v_depth_boxed_2324_; lean_object* v_res_2325_; 
v_depth_boxed_2324_ = lean_unbox_usize(v_depth_2318_);
lean_dec(v_depth_2318_);
v_res_2325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2317_, v_depth_boxed_2324_, v_keys_2319_, v_vals_2320_, v_heq_2321_, v_i_2322_, v_entries_2323_);
lean_dec_ref(v_vals_2320_);
lean_dec_ref(v_keys_2319_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2327_, v_x_2328_, v_x_2329_, v_x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2332_, lean_object* v_maxArgs_x3f_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2332_, v_maxArgs_x3f_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2340_, lean_object* v_maxArgs_x3f_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Meta_getFunInfo(v_fn_2340_, v_maxArgs_x3f_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2348_, lean_object* v_nargs_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_nargs_2349_);
v___x_2356_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2348_, v___x_2355_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2357_, lean_object* v_nargs_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2357_, v_nargs_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2365_){
_start:
{
lean_object* v_paramInfo_2366_; lean_object* v___x_2367_; 
v_paramInfo_2366_ = lean_ctor_get(v_info_2365_, 0);
v___x_2367_ = lean_array_get_size(v_paramInfo_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Meta_FunInfo_getArity(v_info_2368_);
lean_dec_ref(v_info_2368_);
return v_res_2369_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_FunInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_FunInfo(builtin);
}
#ifdef __cplusplus
}
#endif
