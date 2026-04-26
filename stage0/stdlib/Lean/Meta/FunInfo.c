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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqInfoCacheKey_beq(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
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
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Meta.FunInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1;
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
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_fn_118_);
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
lean_dec_ref(v___x_180_);
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
lean_dec_ref(v___x_182_);
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
lean_dec_ref(v___x_184_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0(lean_object* v_as_232_, size_t v_sz_233_, size_t v_i_234_, lean_object* v_b_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_236_ == 0)
{
return v_b_235_;
}
else
{
lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_264_; 
v_snd_237_ = lean_ctor_get(v_b_235_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_b_235_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_b_235_, 0);
lean_dec(v_unused_265_);
v___x_239_ = v_b_235_;
v_isShared_240_ = v_isSharedCheck_264_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_dec(v_b_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_264_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_a_241_; 
v_a_241_ = lean_array_uget_borrowed(v_as_232_, v_i_234_);
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v_deBruijnIndex_242_; uint8_t v___x_243_; 
v_deBruijnIndex_242_ = lean_ctor_get(v_a_241_, 0);
v___x_243_ = l_Nat_testBit(v_snd_237_, v_deBruijnIndex_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_244_ = lean_box(0);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_shiftl(v___x_245_, v_deBruijnIndex_242_);
v___x_247_ = lean_nat_lor(v_snd_237_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v_snd_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_247_);
lean_ctor_set(v___x_239_, 0, v___x_244_);
v___x_249_ = v___x_239_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
size_t v___x_250_; size_t v___x_251_; 
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_234_, v___x_250_);
v_i_234_ = v___x_251_;
v_b_235_ = v___x_249_;
goto _start;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_box(v___x_243_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_255_);
v___x_257_ = v___x_239_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_snd_237_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_box(v___x_236_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_260_);
v___x_262_ = v___x_239_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_snd_237_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0___boxed(lean_object* v_as_266_, lean_object* v_sz_267_, lean_object* v_i_268_, lean_object* v_b_269_){
_start:
{
size_t v_sz_boxed_270_; size_t v_i_boxed_271_; lean_object* v_res_272_; 
v_sz_boxed_270_ = lean_unbox_usize(v_sz_267_);
lean_dec(v_sz_267_);
v_i_boxed_271_ = lean_unbox_usize(v_i_268_);
lean_dec(v_i_268_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0(v_as_266_, v_sz_boxed_270_, v_i_boxed_271_, v_b_269_);
lean_dec_ref(v_as_266_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp(lean_object* v_args_276_){
_start:
{
lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v_fst_281_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___closed__0));
v_sz_278_ = lean_array_size(v_args_276_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp_spec__0(v_args_276_, v_sz_278_, v___x_279_, v___x_277_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_fst_281_);
lean_dec_ref(v___x_280_);
if (lean_obj_tag(v_fst_281_) == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
else
{
lean_object* v_val_283_; uint8_t v___x_284_; 
v_val_283_ = lean_ctor_get(v_fst_281_, 0);
lean_inc(v_val_283_);
lean_dec_ref(v_fst_281_);
v___x_284_ = lean_unbox(v_val_283_);
lean_dec(v_val_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp___boxed(lean_object* v_args_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp(v_args_285_);
lean_dec_ref(v_args_285_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3(lean_object* v_a_288_, lean_object* v_as_289_, size_t v_i_290_, size_t v_stop_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_eq(v_i_290_, v_stop_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_uget_borrowed(v_as_289_, v_i_290_);
v___x_294_ = lean_nat_dec_eq(v_a_288_, v___x_293_);
if (v___x_294_ == 0)
{
size_t v___x_295_; size_t v___x_296_; 
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_290_, v___x_295_);
v_i_290_ = v___x_296_;
goto _start;
}
else
{
return v___x_294_;
}
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3___boxed(lean_object* v_a_299_, lean_object* v_as_300_, lean_object* v_i_301_, lean_object* v_stop_302_){
_start:
{
size_t v_i_boxed_303_; size_t v_stop_boxed_304_; uint8_t v_res_305_; lean_object* v_r_306_; 
v_i_boxed_303_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_stop_boxed_304_ = lean_unbox_usize(v_stop_302_);
lean_dec(v_stop_302_);
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3(v_a_299_, v_as_300_, v_i_boxed_303_, v_stop_boxed_304_);
lean_dec_ref(v_as_300_);
lean_dec(v_a_299_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(lean_object* v_as_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get_size(v_as_307_);
v___x_311_ = lean_nat_dec_lt(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
return v___x_311_;
}
else
{
if (v___x_311_ == 0)
{
return v___x_311_;
}
else
{
size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_310_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2_spec__3(v_a_308_, v_as_307_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2___boxed(lean_object* v_as_315_, lean_object* v_a_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(v_as_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_as_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2(lean_object* v_xs_319_, lean_object* v_v_320_, lean_object* v_i_321_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_get_size(v_xs_319_);
v___x_323_ = lean_nat_dec_lt(v_i_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_i_321_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_array_fget_borrowed(v_xs_319_, v_i_321_);
v___x_326_ = lean_expr_eqv(v___x_325_, v_v_320_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_i_321_, v___x_327_);
lean_dec(v_i_321_);
v_i_321_ = v___x_328_;
goto _start;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_i_321_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_331_, lean_object* v_v_332_, lean_object* v_i_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2(v_xs_331_, v_v_332_, v_i_333_);
lean_dec_ref(v_v_332_);
lean_dec_ref(v_xs_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1(lean_object* v_xs_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1_spec__2(v_xs_335_, v_v_336_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1___boxed(lean_object* v_xs_339_, lean_object* v_v_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1(v_xs_339_, v_v_340_);
lean_dec_ref(v_v_340_);
lean_dec_ref(v_xs_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object* v_xs_342_, lean_object* v_v_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__1(v_xs_342_, v_v_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
else
{
lean_object* v_val_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_val_346_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_val_346_);
lean_dec(v___x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_val_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object* v_xs_354_, lean_object* v_v_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_xs_354_, v_v_355_);
lean_dec_ref(v_v_355_);
lean_dec_ref(v_xs_354_);
return v_res_356_;
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v_dummy_358_; 
v___x_357_ = lean_box(0);
v_dummy_358_ = l_Lean_Expr_sort___override(v___x_357_);
return v_dummy_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object* v_fvars_359_, lean_object* v_deps_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___y_365_; 
if (lean_obj_tag(v_x_361_) == 5)
{
lean_object* v_fn_377_; lean_object* v_arg_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_fn_377_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_fn_377_);
v_arg_378_ = lean_ctor_get(v_x_361_, 1);
lean_inc_ref(v_arg_378_);
lean_dec_ref(v_x_361_);
v___x_379_ = lean_array_set(v_x_362_, v_x_363_, v_arg_378_);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_sub(v_x_363_, v___x_380_);
lean_dec(v_x_363_);
v_x_361_ = v_fn_377_;
v_x_362_ = v___x_379_;
v_x_363_ = v___x_381_;
goto _start;
}
else
{
lean_dec(v_x_363_);
if (lean_obj_tag(v_x_361_) == 1)
{
uint8_t v___x_383_; 
v___x_383_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_isHigherOrderApp(v_x_362_);
if (v___x_383_ == 0)
{
v___y_365_ = v_deps_360_;
goto v___jp_364_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_fvars_359_, v_x_361_);
if (lean_obj_tag(v___x_384_) == 0)
{
v___y_365_ = v_deps_360_;
goto v___jp_364_;
}
else
{
lean_object* v_val_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; uint8_t v___x_388_; 
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref(v___x_384_);
v_fst_386_ = lean_ctor_get(v_deps_360_, 0);
v_snd_387_ = lean_ctor_get(v_deps_360_, 1);
v___x_388_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(v_snd_387_, v_val_385_);
if (v___x_388_ == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
lean_inc(v_snd_387_);
lean_inc(v_fst_386_);
v_isSharedCheck_396_ = !lean_is_exclusive(v_deps_360_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; 
v_unused_397_ = lean_ctor_get(v_deps_360_, 1);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_deps_360_, 0);
lean_dec(v_unused_398_);
v___x_390_ = v_deps_360_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_deps_360_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_array_push(v_snd_387_, v_val_385_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_fst_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v___y_365_ = v___x_394_;
goto v___jp_364_;
}
}
}
else
{
lean_dec(v_val_385_);
v___y_365_ = v_deps_360_;
goto v___jp_364_;
}
}
}
}
else
{
v___y_365_ = v_deps_360_;
goto v___jp_364_;
}
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_366_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_359_, v_x_361_, v___y_365_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_array_get_size(v_x_362_);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v_x_362_);
return v___x_366_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = lean_nat_dec_le(v___x_368_, v___x_368_);
if (v___x_370_ == 0)
{
if (v___x_369_ == 0)
{
lean_dec_ref(v_x_362_);
return v___x_366_;
}
else
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((size_t)0ULL);
v___x_372_ = lean_usize_of_nat(v___x_368_);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_359_, v_x_362_, v___x_371_, v___x_372_, v___x_366_);
lean_dec_ref(v_x_362_);
return v___x_373_;
}
}
else
{
size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((size_t)0ULL);
v___x_375_ = lean_usize_of_nat(v___x_368_);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_359_, v_x_362_, v___x_374_, v___x_375_, v___x_366_);
lean_dec_ref(v_x_362_);
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* v_fvars_399_, lean_object* v_e_400_, lean_object* v_deps_401_){
_start:
{
lean_object* v_d_403_; lean_object* v_b_404_; 
switch(lean_obj_tag(v_e_400_))
{
case 5:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_408_ == 0)
{
lean_dec_ref(v_e_400_);
return v_deps_401_;
}
else
{
lean_object* v_dummy_409_; lean_object* v_nargs_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_dummy_409_ = lean_obj_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0);
v_nargs_410_ = l_Lean_Expr_getAppNumArgs(v_e_400_);
lean_inc(v_nargs_410_);
v___x_411_ = lean_mk_array(v_nargs_410_, v_dummy_409_);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_sub(v_nargs_410_, v___x_412_);
lean_dec(v_nargs_410_);
v___x_414_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(v_fvars_399_, v_deps_401_, v_e_400_, v___x_411_, v___x_413_);
return v___x_414_;
}
}
case 7:
{
lean_object* v_binderType_415_; lean_object* v_body_416_; 
v_binderType_415_ = lean_ctor_get(v_e_400_, 1);
v_body_416_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_body_416_);
lean_inc_ref(v_binderType_415_);
v_d_403_ = v_binderType_415_;
v_b_404_ = v_body_416_;
goto v___jp_402_;
}
case 6:
{
lean_object* v_binderType_417_; lean_object* v_body_418_; 
v_binderType_417_ = lean_ctor_get(v_e_400_, 1);
v_body_418_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_body_418_);
lean_inc_ref(v_binderType_417_);
v_d_403_ = v_binderType_417_;
v_b_404_ = v_body_418_;
goto v___jp_402_;
}
case 8:
{
lean_object* v_type_419_; lean_object* v_value_420_; lean_object* v_body_421_; uint8_t v___x_422_; 
v_type_419_ = lean_ctor_get(v_e_400_, 1);
lean_inc_ref(v_type_419_);
v_value_420_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_value_420_);
v_body_421_ = lean_ctor_get(v_e_400_, 3);
lean_inc_ref(v_body_421_);
v___x_422_ = l_Lean_Expr_hasFVar(v_e_400_);
lean_dec_ref(v_e_400_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_body_421_);
lean_dec_ref(v_value_420_);
lean_dec_ref(v_type_419_);
return v_deps_401_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_399_, v_type_419_, v_deps_401_);
v___x_424_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_399_, v_value_420_, v___x_423_);
v_e_400_ = v_body_421_;
v_deps_401_ = v___x_424_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_426_; 
v_struct_426_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_struct_426_);
lean_dec_ref(v_e_400_);
v_e_400_ = v_struct_426_;
goto _start;
}
case 10:
{
lean_object* v_expr_428_; 
v_expr_428_ = lean_ctor_get(v_e_400_, 1);
lean_inc_ref(v_expr_428_);
lean_dec_ref(v_e_400_);
v_e_400_ = v_expr_428_;
goto _start;
}
case 1:
{
lean_object* v___x_430_; 
v___x_430_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_fvars_399_, v_e_400_);
lean_dec_ref(v_e_400_);
if (lean_obj_tag(v___x_430_) == 0)
{
return v_deps_401_;
}
else
{
lean_object* v_val_431_; lean_object* v_fst_432_; lean_object* v_snd_433_; uint8_t v___x_434_; 
v_val_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_431_);
lean_dec_ref(v___x_430_);
v_fst_432_ = lean_ctor_get(v_deps_401_, 0);
v_snd_433_ = lean_ctor_get(v_deps_401_, 1);
v___x_434_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(v_fst_432_, v_val_431_);
if (v___x_434_ == 0)
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_snd_433_);
lean_inc(v_fst_432_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_deps_401_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_deps_401_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_deps_401_, 0);
lean_dec(v_unused_444_);
v___x_436_ = v_deps_401_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_deps_401_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = lean_array_push(v_fst_432_, v_val_431_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_433_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_dec(v_val_431_);
return v_deps_401_;
}
}
}
default: 
{
lean_dec_ref(v_e_400_);
return v_deps_401_;
}
}
v___jp_402_:
{
uint8_t v___x_405_; 
v___x_405_ = l_Lean_Expr_hasFVar(v_e_400_);
lean_dec_ref(v_e_400_);
if (v___x_405_ == 0)
{
lean_dec_ref(v_b_404_);
lean_dec_ref(v_d_403_);
return v_deps_401_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_399_, v_d_403_, v_deps_401_);
v_e_400_ = v_b_404_;
v_deps_401_ = v___x_406_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* v_fvars_445_, lean_object* v_as_446_, size_t v_i_447_, size_t v_stop_448_, lean_object* v_b_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_447_, v_stop_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; size_t v___x_453_; size_t v___x_454_; 
v___x_451_ = lean_array_uget_borrowed(v_as_446_, v_i_447_);
lean_inc(v___x_451_);
v___x_452_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_445_, v___x_451_, v_b_449_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_447_, v___x_453_);
v_i_447_ = v___x_454_;
v_b_449_ = v___x_452_;
goto _start;
}
else
{
return v_b_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* v_fvars_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_456_, v_as_457_, v_i_boxed_461_, v_stop_boxed_462_, v_b_460_);
lean_dec_ref(v_as_457_);
lean_dec_ref(v_fvars_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* v_fvars_464_, lean_object* v_e_465_, lean_object* v_deps_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_464_, v_e_465_, v_deps_466_);
lean_dec_ref(v_fvars_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3___boxed(lean_object* v_fvars_468_, lean_object* v_deps_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(v_fvars_468_, v_deps_469_, v_x_470_, v_x_471_, v_x_472_);
lean_dec_ref(v_fvars_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object* v_hi_474_, lean_object* v_pivot_475_, lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_lt(v_k_478_, v_hi_474_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_k_478_);
v___x_480_ = lean_array_fswap(v_as_476_, v_i_477_, v_hi_474_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_i_477_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_array_fget_borrowed(v_as_476_, v_k_478_);
v___x_483_ = lean_nat_dec_lt(v___x_482_, v_pivot_475_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_k_478_, v___x_484_);
lean_dec(v_k_478_);
v_k_478_ = v___x_485_;
goto _start;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_array_fswap(v_as_476_, v_i_477_, v_k_478_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_i_477_, v___x_488_);
lean_dec(v_i_477_);
v___x_490_ = lean_nat_add(v_k_478_, v___x_488_);
lean_dec(v_k_478_);
v_as_476_ = v___x_487_;
v_i_477_ = v___x_489_;
v_k_478_ = v___x_490_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_492_, lean_object* v_pivot_493_, lean_object* v_as_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_492_, v_pivot_493_, v_as_494_, v_i_495_, v_k_496_);
lean_dec(v_pivot_493_);
lean_dec(v_hi_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_n_498_, lean_object* v_as_499_, lean_object* v_lo_500_, lean_object* v_hi_501_){
_start:
{
lean_object* v___y_503_; uint8_t v___x_513_; 
v___x_513_ = lean_nat_dec_lt(v_lo_500_, v_hi_501_);
if (v___x_513_ == 0)
{
lean_dec(v_lo_500_);
return v_as_499_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_mid_516_; lean_object* v___y_518_; lean_object* v___y_524_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_514_ = lean_nat_add(v_lo_500_, v_hi_501_);
v___x_515_ = lean_unsigned_to_nat(1u);
v_mid_516_ = lean_nat_shiftr(v___x_514_, v___x_515_);
lean_dec(v___x_514_);
v___x_529_ = lean_array_fget_borrowed(v_as_499_, v_mid_516_);
v___x_530_ = lean_array_fget_borrowed(v_as_499_, v_lo_500_);
v___x_531_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
v___y_524_ = v_as_499_;
goto v___jp_523_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_array_fswap(v_as_499_, v_lo_500_, v_mid_516_);
v___y_524_ = v___x_532_;
goto v___jp_523_;
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_array_fget_borrowed(v___y_518_, v_mid_516_);
v___x_520_ = lean_array_fget_borrowed(v___y_518_, v_hi_501_);
v___x_521_ = lean_nat_dec_lt(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v_mid_516_);
v___y_503_ = v___y_518_;
goto v___jp_502_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_array_fswap(v___y_518_, v_mid_516_, v_hi_501_);
lean_dec(v_mid_516_);
v___y_503_ = v___x_522_;
goto v___jp_502_;
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_array_fget_borrowed(v___y_524_, v_hi_501_);
v___x_526_ = lean_array_fget_borrowed(v___y_524_, v_lo_500_);
v___x_527_ = lean_nat_dec_lt(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
v___y_518_ = v___y_524_;
goto v___jp_517_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_array_fswap(v___y_524_, v_lo_500_, v_hi_501_);
v___y_518_ = v___x_528_;
goto v___jp_517_;
}
}
}
v___jp_502_:
{
lean_object* v_pivot_504_; lean_object* v___x_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; uint8_t v___x_508_; 
v_pivot_504_ = lean_array_fget(v___y_503_, v_hi_501_);
lean_inc_n(v_lo_500_, 2);
v___x_505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_501_, v_pivot_504_, v___y_503_, v_lo_500_, v_lo_500_);
lean_dec(v_pivot_504_);
v_fst_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_snd_507_);
lean_dec_ref(v___x_505_);
v___x_508_ = lean_nat_dec_le(v_hi_501_, v_fst_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_498_, v_snd_507_, v_lo_500_, v_fst_506_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v_fst_506_, v___x_510_);
lean_dec(v_fst_506_);
v_as_499_ = v___x_509_;
v_lo_500_ = v___x_511_;
goto _start;
}
else
{
lean_dec(v_fst_506_);
lean_dec(v_lo_500_);
return v_snd_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_n_533_, lean_object* v_as_534_, lean_object* v_lo_535_, lean_object* v_hi_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_533_, v_as_534_, v_lo_535_, v_hi_536_);
lean_dec(v_hi_536_);
lean_dec(v_n_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_542_, lean_object* v_e_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_deps_546_; lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_586_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1));
v_deps_546_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_542_, v_e_543_, v___x_545_);
v_fst_547_ = lean_ctor_get(v_deps_546_, 0);
v_snd_548_ = lean_ctor_get(v_deps_546_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_deps_546_);
if (v_isSharedCheck_586_ == 0)
{
v___x_550_ = v_deps_546_;
v_isShared_551_ = v_isSharedCheck_586_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snd_548_);
lean_inc(v_fst_547_);
lean_dec(v_deps_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_586_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_567_; lean_object* v___y_569_; lean_object* v___x_575_; lean_object* v___y_577_; lean_object* v___y_578_; uint8_t v___x_580_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_array_get_size(v_fst_547_);
v___x_580_ = lean_nat_dec_eq(v___x_575_, v___x_544_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___y_583_; uint8_t v___x_585_; 
v___x_581_ = lean_nat_sub(v___x_575_, v___x_567_);
v___x_585_ = lean_nat_dec_le(v___x_544_, v___x_581_);
if (v___x_585_ == 0)
{
lean_inc(v___x_581_);
v___y_583_ = v___x_581_;
goto v___jp_582_;
}
else
{
v___y_583_ = v___x_544_;
goto v___jp_582_;
}
v___jp_582_:
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_le(v___y_583_, v___x_581_);
if (v___x_584_ == 0)
{
lean_dec(v___x_581_);
lean_inc(v___y_583_);
v___y_577_ = v___y_583_;
v___y_578_ = v___y_583_;
goto v___jp_576_;
}
else
{
v___y_577_ = v___y_583_;
v___y_578_ = v___x_581_;
goto v___jp_576_;
}
}
}
else
{
v___y_569_ = v_fst_547_;
goto v___jp_568_;
}
v___jp_552_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___y_555_, v_snd_548_, v___y_554_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_557_);
lean_ctor_set(v___x_550_, 0, v___y_553_);
v___x_559_ = v___x_550_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___y_553_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
v___jp_561_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_le(v___y_565_, v___y_563_);
if (v___x_566_ == 0)
{
lean_dec(v___y_563_);
lean_inc(v___y_565_);
v___y_553_ = v___y_562_;
v___y_554_ = v___y_565_;
v___y_555_ = v___y_564_;
v___y_556_ = v___y_565_;
goto v___jp_552_;
}
else
{
v___y_553_ = v___y_562_;
v___y_554_ = v___y_565_;
v___y_555_ = v___y_564_;
v___y_556_ = v___y_563_;
goto v___jp_552_;
}
}
v___jp_568_:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_array_get_size(v_snd_548_);
v___x_571_ = lean_nat_dec_eq(v___x_570_, v___x_544_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_nat_sub(v___x_570_, v___x_567_);
v___x_573_ = lean_nat_dec_le(v___x_544_, v___x_572_);
if (v___x_573_ == 0)
{
lean_inc(v___x_572_);
v___y_562_ = v___y_569_;
v___y_563_ = v___x_572_;
v___y_564_ = v___x_570_;
v___y_565_ = v___x_572_;
goto v___jp_561_;
}
else
{
v___y_562_ = v___y_569_;
v___y_563_ = v___x_572_;
v___y_564_ = v___x_570_;
v___y_565_ = v___x_544_;
goto v___jp_561_;
}
}
else
{
lean_object* v___x_574_; 
lean_del_object(v___x_550_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_569_);
lean_ctor_set(v___x_574_, 1, v_snd_548_);
return v___x_574_;
}
}
v___jp_576_:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_575_, v_fst_547_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
v___y_569_ = v___x_579_;
goto v___jp_568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_587_, lean_object* v_e_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_587_, v_e_588_);
lean_dec_ref(v_fvars_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_590_, lean_object* v_as_591_, lean_object* v_lo_592_, lean_object* v_hi_593_, lean_object* v_w_594_, lean_object* v_hlo_595_, lean_object* v_hhi_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_590_, v_as_591_, v_lo_592_, v_hi_593_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_598_, lean_object* v_as_599_, lean_object* v_lo_600_, lean_object* v_hi_601_, lean_object* v_w_602_, lean_object* v_hlo_603_, lean_object* v_hhi_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_598_, v_as_599_, v_lo_600_, v_hi_601_, v_w_602_, v_hlo_603_, v_hhi_604_);
lean_dec(v_hi_601_);
lean_dec(v_n_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object* v_n_606_, lean_object* v_lo_607_, lean_object* v_hi_608_, lean_object* v_hhi_609_, lean_object* v_pivot_610_, lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_k_613_, lean_object* v_ilo_614_, lean_object* v_ik_615_, lean_object* v_w_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_608_, v_pivot_610_, v_as_611_, v_i_612_, v_k_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object* v_n_618_, lean_object* v_lo_619_, lean_object* v_hi_620_, lean_object* v_hhi_621_, lean_object* v_pivot_622_, lean_object* v_as_623_, lean_object* v_i_624_, lean_object* v_k_625_, lean_object* v_ilo_626_, lean_object* v_ik_627_, lean_object* v_w_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_618_, v_lo_619_, v_hi_620_, v_hhi_621_, v_pivot_622_, v_as_623_, v_i_624_, v_k_625_, v_ilo_626_, v_ik_627_, v_w_628_);
lean_dec(v_pivot_622_);
lean_dec(v_hi_620_);
lean_dec(v_lo_619_);
lean_dec(v_n_618_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_630_, lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_j_633_, lean_object* v_bs_634_){
_start:
{
lean_object* v_zero_635_; uint8_t v_isZero_636_; 
v_zero_635_ = lean_unsigned_to_nat(0u);
v_isZero_636_ = lean_nat_dec_eq(v_i_632_, v_zero_635_);
if (v_isZero_636_ == 1)
{
lean_dec(v_j_633_);
lean_dec(v_i_632_);
return v_bs_634_;
}
else
{
lean_object* v___x_637_; uint8_t v_binderInfo_638_; uint8_t v_hasFwdDeps_639_; lean_object* v_backDeps_640_; uint8_t v_isProp_641_; uint8_t v_isDecInst_642_; uint8_t v_isInstance_643_; uint8_t v_higherOrderImplicit_644_; uint8_t v_dependsOnHigherOrderImplicit_645_; lean_object* v_one_646_; lean_object* v_n_647_; lean_object* v___y_649_; 
v___x_637_ = lean_array_fget(v_as_631_, v_j_633_);
v_binderInfo_638_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1);
v_hasFwdDeps_639_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 1);
v_backDeps_640_ = lean_ctor_get(v___x_637_, 0);
v_isProp_641_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 2);
v_isDecInst_642_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 3);
v_isInstance_643_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 4);
v_higherOrderImplicit_644_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderImplicit_645_ = lean_ctor_get_uint8(v___x_637_, sizeof(void*)*1 + 6);
v_one_646_ = lean_unsigned_to_nat(1u);
v_n_647_ = lean_nat_sub(v_i_632_, v_one_646_);
lean_dec(v_i_632_);
if (v_hasFwdDeps_639_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(v_backDeps_630_, v_j_633_);
if (v___x_653_ == 0)
{
v___y_649_ = v___x_637_;
goto v___jp_648_;
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_inc_ref(v_backDeps_640_);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_661_);
v___x_655_ = v___x_637_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_dec(v___x_637_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_backDeps_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1, v_binderInfo_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1 + 2, v_isProp_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1 + 3, v_isDecInst_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1 + 4, v_isInstance_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1 + 5, v_higherOrderImplicit_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderImplicit_645_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1 + 1, v___x_653_);
v___y_649_ = v___x_658_;
goto v___jp_648_;
}
}
}
}
else
{
v___y_649_ = v___x_637_;
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_nat_add(v_j_633_, v_one_646_);
lean_dec(v_j_633_);
v___x_651_ = lean_array_push(v_bs_634_, v___y_649_);
v_i_632_ = v_n_647_;
v_j_633_ = v___x_650_;
v_bs_634_ = v___x_651_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_j_665_, lean_object* v_bs_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_662_, v_as_663_, v_i_664_, v_j_665_, v_bs_666_);
lean_dec_ref(v_as_663_);
lean_dec_ref(v_backDeps_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_668_, lean_object* v_backDeps_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_array_get_size(v_backDeps_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_eq(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_array_get_size(v_pinfo_668_);
v___x_674_ = lean_mk_empty_array_with_capacity(v___x_673_);
v___x_675_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_669_, v_pinfo_668_, v___x_673_, v___x_671_, v___x_674_);
return v___x_675_;
}
else
{
lean_inc_ref(v_pinfo_668_);
return v_pinfo_668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_676_, lean_object* v_backDeps_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_676_, v_backDeps_677_);
lean_dec_ref(v_backDeps_677_);
lean_dec_ref(v_pinfo_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_679_, lean_object* v_as_680_, lean_object* v_i_681_, lean_object* v_j_682_, lean_object* v_inv_683_, lean_object* v_bs_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_679_, v_as_680_, v_i_681_, v_j_682_, v_bs_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_686_, lean_object* v_as_687_, lean_object* v_i_688_, lean_object* v_j_689_, lean_object* v_inv_690_, lean_object* v_bs_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_686_, v_as_687_, v_i_688_, v_j_689_, v_inv_690_, v_bs_691_);
lean_dec_ref(v_as_687_);
lean_dec_ref(v_backDeps_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_693_, lean_object* v_b_694_, lean_object* v_c_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
v___x_701_ = lean_apply_7(v_k_693_, v_b_694_, v_c_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_702_, lean_object* v_b_703_, lean_object* v_c_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_702_, v_b_703_, v_c_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_711_, lean_object* v_k_712_, uint8_t v_cleanupAnnotations_713_, uint8_t v_whnfType_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___f_720_; lean_object* v___x_721_; 
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_720_, 0, v_k_712_);
v___x_721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_711_, v___f_720_, v_cleanupAnnotations_713_, v_whnfType_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v_cleanupAnnotations_740_, lean_object* v_whnfType_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_747_; uint8_t v_whnfType_boxed_748_; lean_object* v_res_749_; 
v_cleanupAnnotations_boxed_747_ = lean_unbox(v_cleanupAnnotations_740_);
v_whnfType_boxed_748_ = lean_unbox(v_whnfType_741_);
v_res_749_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_738_, v_k_739_, v_cleanupAnnotations_boxed_747_, v_whnfType_boxed_748_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_750_, lean_object* v_type_751_, lean_object* v_k_752_, uint8_t v_cleanupAnnotations_753_, uint8_t v_whnfType_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_751_, v_k_752_, v_cleanupAnnotations_753_, v_whnfType_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_761_, lean_object* v_type_762_, lean_object* v_k_763_, lean_object* v_cleanupAnnotations_764_, lean_object* v_whnfType_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_771_; uint8_t v_whnfType_boxed_772_; lean_object* v_res_773_; 
v_cleanupAnnotations_boxed_771_ = lean_unbox(v_cleanupAnnotations_764_);
v_whnfType_boxed_772_ = lean_unbox(v_whnfType_765_);
v_res_773_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_761_, v_type_762_, v_k_763_, v_cleanupAnnotations_boxed_771_, v_whnfType_boxed_772_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___f_781_; lean_object* v___x_11962__overap_782_; lean_object* v___x_783_; 
v___f_781_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_11962__overap_782_ = lean_panic_fn_borrowed(v___f_781_, v_msg_775_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
v___x_783_ = lean_apply_5(v___x_11962__overap_782_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_791_, lean_object* v_maxFVars_x3f_792_, lean_object* v_k_793_, uint8_t v_cleanupAnnotations_794_, uint8_t v_whnfType_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; 
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_801_, 0, v_k_793_);
v___x_802_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_791_, v_maxFVars_x3f_792_, v___f_801_, v_cleanupAnnotations_794_, v_whnfType_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_802_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_802_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_819_, lean_object* v_maxFVars_x3f_820_, lean_object* v_k_821_, lean_object* v_cleanupAnnotations_822_, lean_object* v_whnfType_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_829_; uint8_t v_whnfType_boxed_830_; lean_object* v_res_831_; 
v_cleanupAnnotations_boxed_829_ = lean_unbox(v_cleanupAnnotations_822_);
v_whnfType_boxed_830_ = lean_unbox(v_whnfType_823_);
v_res_831_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_819_, v_maxFVars_x3f_820_, v_k_821_, v_cleanupAnnotations_boxed_829_, v_whnfType_boxed_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_832_, lean_object* v_type_833_, lean_object* v_maxFVars_x3f_834_, lean_object* v_k_835_, uint8_t v_cleanupAnnotations_836_, uint8_t v_whnfType_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_833_, v_maxFVars_x3f_834_, v_k_835_, v_cleanupAnnotations_836_, v_whnfType_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_844_, lean_object* v_type_845_, lean_object* v_maxFVars_x3f_846_, lean_object* v_k_847_, lean_object* v_cleanupAnnotations_848_, lean_object* v_whnfType_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_855_; uint8_t v_whnfType_boxed_856_; lean_object* v_res_857_; 
v_cleanupAnnotations_boxed_855_ = lean_unbox(v_cleanupAnnotations_848_);
v_whnfType_boxed_856_ = lean_unbox(v_whnfType_849_);
v_res_857_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_844_, v_type_845_, v_maxFVars_x3f_846_, v_k_847_, v_cleanupAnnotations_boxed_855_, v_whnfType_boxed_856_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_858_, lean_object* v_val_859_, lean_object* v___x_860_, lean_object* v_fvars_861_, uint8_t v___y_862_, lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_a_872_; uint8_t v___x_876_; 
v___x_876_ = lean_nat_dec_lt(v_a_864_, v_upperBound_858_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_a_864_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v_b_865_);
return v___x_877_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__2(v_val_859_, v_a_864_);
if (v___x_878_ == 0)
{
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_array_fget_borrowed(v___x_860_, v_a_864_);
v___x_880_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_fvars_861_, v___x_879_);
if (lean_obj_tag(v___x_880_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_882_; 
v_val_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_881_);
lean_dec_ref(v___x_880_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___x_879_);
v___x_882_ = lean_infer_type(v___x_879_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
v___x_884_ = lean_whnf(v_a_883_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___y_887_; uint8_t v___x_908_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_908_ = l_Lean_Expr_isForall(v_a_885_);
lean_dec(v_a_885_);
if (v___x_908_ == 0)
{
lean_dec(v_val_881_);
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_910_ = lean_array_get_borrowed(v___x_909_, v_b_865_, v_val_881_);
v___x_911_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_910_);
if (v___x_911_ == 0)
{
v___y_887_ = v___x_911_;
goto v___jp_886_;
}
else
{
uint8_t v_isProp_912_; 
v_isProp_912_ = lean_ctor_get_uint8(v___x_910_, sizeof(void*)*1 + 2);
if (v_isProp_912_ == 0)
{
v___y_887_ = v___x_911_;
goto v___jp_886_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_nat_dec_eq(v___x_863_, v___x_913_);
v___y_887_ = v___x_914_;
goto v___jp_886_;
}
}
}
v___jp_886_:
{
if (v___y_887_ == 0)
{
lean_dec(v_val_881_);
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
else
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_array_get_size(v_b_865_);
v___x_889_ = lean_nat_dec_lt(v_val_881_, v___x_888_);
if (v___x_889_ == 0)
{
lean_dec(v_val_881_);
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
else
{
lean_object* v_v_890_; uint8_t v_binderInfo_891_; uint8_t v_hasFwdDeps_892_; lean_object* v_backDeps_893_; uint8_t v_isProp_894_; uint8_t v_isDecInst_895_; uint8_t v_isInstance_896_; uint8_t v_dependsOnHigherOrderImplicit_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
v_v_890_ = lean_array_fget(v_b_865_, v_val_881_);
v_binderInfo_891_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1);
v_hasFwdDeps_892_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1 + 1);
v_backDeps_893_ = lean_ctor_get(v_v_890_, 0);
v_isProp_894_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1 + 2);
v_isDecInst_895_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1 + 3);
v_isInstance_896_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderImplicit_897_ = lean_ctor_get_uint8(v_v_890_, sizeof(void*)*1 + 6);
v_isSharedCheck_907_ = !lean_is_exclusive(v_v_890_);
if (v_isSharedCheck_907_ == 0)
{
v___x_899_ = v_v_890_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_backDeps_893_);
lean_dec(v_v_890_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v_xs_x27_902_; lean_object* v___x_904_; 
v___x_901_ = lean_box(0);
v_xs_x27_902_ = lean_array_fset(v_b_865_, v_val_881_, v___x_901_);
if (v_isShared_900_ == 0)
{
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_backDeps_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1, v_binderInfo_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1 + 1, v_hasFwdDeps_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1 + 2, v_isProp_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1 + 3, v_isDecInst_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1 + 4, v_isInstance_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderImplicit_897_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1 + 5, v___y_862_);
v___x_905_ = lean_array_fset(v_xs_x27_902_, v_val_881_, v___x_904_);
lean_dec(v_val_881_);
v_a_872_ = v___x_905_;
goto v___jp_871_;
}
}
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_val_881_);
lean_dec_ref(v_b_865_);
lean_dec(v_a_864_);
v_a_915_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_884_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_884_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_val_881_);
lean_dec_ref(v_b_865_);
lean_dec(v_a_864_);
v_a_923_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_882_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_882_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_dec(v___x_880_);
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
}
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_a_864_, v___x_873_);
lean_dec(v_a_864_);
v_a_864_ = v___x_874_;
v_b_865_ = v_a_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_931_, lean_object* v_val_932_, lean_object* v___x_933_, lean_object* v_fvars_934_, lean_object* v___y_935_, lean_object* v___x_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___y_14414__boxed_944_; lean_object* v_res_945_; 
v___y_14414__boxed_944_ = lean_unbox(v___y_935_);
v_res_945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_931_, v_val_932_, v___x_933_, v_fvars_934_, v___y_14414__boxed_944_, v___x_936_, v_a_937_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___x_936_);
lean_dec_ref(v_fvars_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v_val_932_);
lean_dec(v_upperBound_931_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_949_, lean_object* v_type_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_957_ = l_Lean_Expr_isAppOf(v_type_950_, v___x_956_);
v___x_958_ = lean_box(v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_960_, lean_object* v_type_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_960_, v_type_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_type_961_);
lean_dec_ref(v_x_960_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_as_968_, size_t v_sz_969_, size_t v_i_970_, lean_object* v_b_971_){
_start:
{
lean_object* v_a_974_; uint8_t v___y_979_; lean_object* v___y_980_; uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_970_, v_sz_969_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_971_);
return v___x_984_;
}
else
{
lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1021_; 
v_fst_985_ = lean_ctor_get(v_b_971_, 0);
v_snd_986_ = lean_ctor_get(v_b_971_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_b_971_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_988_ = v_b_971_;
v_isShared_989_ = v_isSharedCheck_1021_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_b_971_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1021_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_994_; lean_object* v_a_995_; uint8_t v___y_997_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_994_ = l_Lean_Meta_instInhabitedParamInfo_default;
v_a_995_ = lean_array_uget_borrowed(v_as_968_, v_i_970_);
v___x_1018_ = lean_array_get_borrowed(v___x_994_, v_fst_985_, v_a_995_);
v___x_1019_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_1018_);
if (v___x_1019_ == 0)
{
v___y_997_ = v___x_1019_;
goto v___jp_996_;
}
else
{
uint8_t v_isProp_1020_; 
v_isProp_1020_ = lean_ctor_get_uint8(v___x_1018_, sizeof(void*)*1 + 2);
if (v_isProp_1020_ == 0)
{
v___y_997_ = v___x_1019_;
goto v___jp_996_;
}
else
{
goto v___jp_990_;
}
}
v___jp_990_:
{
lean_object* v___x_992_; 
if (v_isShared_989_ == 0)
{
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_snd_986_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_a_974_ = v___x_992_;
goto v___jp_973_;
}
}
v___jp_996_:
{
if (v___y_997_ == 0)
{
goto v___jp_990_;
}
else
{
lean_object* v___x_998_; uint8_t v___x_999_; 
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
v___x_998_ = lean_array_get_size(v_fst_985_);
v___x_999_ = lean_nat_dec_lt(v_a_995_, v___x_998_);
if (v___x_999_ == 0)
{
v___y_979_ = v___y_997_;
v___y_980_ = v_fst_985_;
goto v___jp_978_;
}
else
{
lean_object* v_v_1000_; uint8_t v_binderInfo_1001_; uint8_t v_hasFwdDeps_1002_; lean_object* v_backDeps_1003_; uint8_t v_isProp_1004_; uint8_t v_isDecInst_1005_; uint8_t v_isInstance_1006_; uint8_t v_dependsOnHigherOrderImplicit_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1017_; 
v_v_1000_ = lean_array_fget(v_fst_985_, v_a_995_);
v_binderInfo_1001_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1);
v_hasFwdDeps_1002_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1 + 1);
v_backDeps_1003_ = lean_ctor_get(v_v_1000_, 0);
v_isProp_1004_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1 + 2);
v_isDecInst_1005_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1 + 3);
v_isInstance_1006_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderImplicit_1007_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*1 + 6);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_v_1000_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1009_ = v_v_1000_;
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_backDeps_1003_);
lean_dec(v_v_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_xs_x27_1012_; lean_object* v___x_1014_; 
v___x_1011_ = lean_box(0);
v_xs_x27_1012_ = lean_array_fset(v_fst_985_, v_a_995_, v___x_1011_);
if (v_isShared_1010_ == 0)
{
v___x_1014_ = v___x_1009_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_backDeps_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1, v_binderInfo_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1 + 1, v_hasFwdDeps_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1 + 2, v_isProp_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1 + 3, v_isDecInst_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1 + 4, v_isInstance_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderImplicit_1007_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1 + 5, v___y_997_);
v___x_1015_ = lean_array_fset(v_xs_x27_1012_, v_a_995_, v___x_1014_);
v___y_979_ = v___y_997_;
v___y_980_ = v___x_1015_;
goto v___jp_978_;
}
}
}
}
}
}
}
v___jp_973_:
{
size_t v___x_975_; size_t v___x_976_; 
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_970_, v___x_975_);
v_i_970_ = v___x_976_;
v_b_971_ = v_a_974_;
goto _start;
}
v___jp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(v___y_979_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___y_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v_a_974_ = v___x_982_;
goto v___jp_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_as_1022_, lean_object* v_sz_1023_, lean_object* v_i_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_){
_start:
{
size_t v_sz_boxed_1027_; size_t v_i_boxed_1028_; lean_object* v_res_1029_; 
v_sz_boxed_1027_ = lean_unbox_usize(v_sz_1023_);
lean_dec(v_sz_1023_);
v_i_boxed_1028_ = lean_unbox_usize(v_i_1024_);
lean_dec(v_i_1024_);
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_as_1022_, v_sz_boxed_1027_, v_i_boxed_1028_, v_b_1025_);
lean_dec_ref(v_as_1022_);
return v_res_1029_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1034_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_1035_ = lean_unsigned_to_nat(47u);
v___x_1036_ = lean_unsigned_to_nat(144u);
v___x_1037_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_1038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1));
v___x_1039_ = l_mkPanicMessageWithDecl(v___x_1038_, v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_1040_, lean_object* v_fvars_1041_, lean_object* v_a_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_a_1050_; uint8_t v___x_1054_; 
v___x_1054_ = lean_nat_dec_lt(v_a_1042_, v_upperBound_1040_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_a_1042_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1043_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_array_fget_borrowed(v_fvars_1041_, v_a_1042_);
v___x_1057_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_1056_, v___y_1044_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1156_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_LocalDecl_type(v_a_1058_);
lean_inc_ref(v___x_1059_);
v___x_1060_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_1041_, v___x_1059_);
v_fst_1061_ = lean_ctor_get(v___x_1060_, 0);
v_snd_1062_ = lean_ctor_get(v___x_1060_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1064_ = v___x_1060_;
v_isShared_1065_ = v_isSharedCheck_1156_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snd_1062_);
lean_inc(v_fst_1061_);
lean_dec(v___x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1156_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; 
lean_inc_ref(v___x_1059_);
v___x_1066_ = l_Lean_Meta_isClass_x3f(v___x_1059_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___f_1068_; uint8_t v___y_1070_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1066_);
v___f_1068_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
if (lean_obj_tag(v_a_1067_) == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
v___y_1070_ = v___x_1144_;
goto v___jp_1069_;
}
else
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = l_Lean_LocalDecl_binderInfo(v_a_1058_);
v___x_1146_ = l_Lean_BinderInfo_isExplicit(v___x_1145_);
if (v___x_1146_ == 0)
{
v___y_1070_ = v___x_1054_;
goto v___jp_1069_;
}
else
{
uint8_t v___x_1147_; 
v___x_1147_ = 0;
v___y_1070_ = v___x_1147_;
goto v___jp_1069_;
}
}
v___jp_1069_:
{
lean_object* v___x_1071_; 
lean_inc_ref(v___x_1059_);
v___x_1071_ = l_Lean_Meta_isProp(v___x_1059_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_b_1043_, v_fst_1061_);
lean_dec_ref(v_b_1043_);
v___x_1074_ = 0;
v___x_1075_ = lean_box(v___x_1074_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___x_1075_);
lean_ctor_set(v___x_1064_, 0, v___x_1073_);
v___x_1077_ = v___x_1064_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v_sz_1078_ = lean_array_size(v_snd_1062_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_snd_1062_, v_sz_1078_, v___x_1079_, v___x_1077_);
lean_dec(v_snd_1062_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
lean_inc_ref(v___x_1059_);
v___x_1082_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_1059_, v___f_1068_, v___x_1074_, v___x_1074_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v_fst_1084_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_fst_1084_);
v_snd_1085_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1085_);
lean_dec(v_a_1081_);
v___x_1086_ = l_Lean_LocalDecl_binderInfo(v_a_1058_);
lean_dec(v_a_1058_);
v___x_1087_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_1087_, 0, v_fst_1061_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v___x_1086_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 1, v___x_1074_);
v___x_1088_ = lean_unbox(v_a_1072_);
lean_dec(v_a_1072_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 2, v___x_1088_);
v___x_1089_ = lean_unbox(v_a_1083_);
lean_dec(v_a_1083_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 3, v___x_1089_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 4, v___y_1070_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 5, v___x_1074_);
v___x_1090_ = lean_unbox(v_snd_1085_);
lean_dec(v_snd_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1 + 6, v___x_1090_);
v___x_1091_ = lean_array_push(v_fst_1084_, v___x_1087_);
if (v___y_1070_ == 0)
{
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1059_);
v_a_1050_ = v___x_1091_;
goto v___jp_1049_;
}
else
{
if (lean_obj_tag(v_a_1067_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1093_; lean_object* v_env_1094_; lean_object* v___x_1095_; 
v_val_1092_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_val_1092_);
lean_dec_ref(v_a_1067_);
v___x_1093_ = lean_st_ref_get(v___y_1047_);
v_env_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_env_1094_);
lean_dec(v___x_1093_);
v___x_1095_ = l_Lean_getOutParamPositions_x3f(v_env_1094_, v_val_1092_);
lean_dec(v_val_1092_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_val_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = lean_array_get_size(v_val_1096_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_dec_eq(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v_dummy_1100_; lean_object* v_nargs_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_dummy_1100_ = lean_obj_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___closed__0);
v_nargs_1101_ = l_Lean_Expr_getAppNumArgs(v___x_1059_);
lean_inc(v_nargs_1101_);
v___x_1102_ = lean_mk_array(v_nargs_1101_, v_dummy_1100_);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_sub(v_nargs_1101_, v___x_1103_);
lean_dec(v_nargs_1101_);
v___x_1105_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1059_, v___x_1102_, v___x_1104_);
v___x_1106_ = lean_array_get_size(v___x_1105_);
v___x_1107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_1106_, v_val_1096_, v___x_1105_, v_fvars_1041_, v___y_1070_, v___x_1097_, v___x_1098_, v___x_1091_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec_ref(v___x_1105_);
lean_dec(v_val_1096_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v_a_1050_ = v_a_1108_;
goto v___jp_1049_;
}
else
{
lean_dec(v_a_1042_);
return v___x_1107_;
}
}
else
{
lean_dec(v_val_1096_);
lean_dec_ref(v___x_1059_);
v_a_1050_ = v___x_1091_;
goto v___jp_1049_;
}
}
else
{
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1059_);
v_a_1050_ = v___x_1091_;
goto v___jp_1049_;
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1059_);
v___x_1109_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4);
v___x_1110_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_1109_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref(v___x_1110_);
v_a_1050_ = v___x_1091_;
goto v___jp_1049_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v___x_1091_);
lean_dec(v_a_1042_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
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
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1081_);
lean_dec(v_a_1072_);
lean_dec(v_a_1067_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1059_);
lean_dec(v_a_1058_);
lean_dec(v_a_1042_);
v_a_1119_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1082_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1082_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1072_);
lean_dec(v_a_1067_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1059_);
lean_dec(v_a_1058_);
lean_dec(v_a_1042_);
v_a_1127_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1080_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1080_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1067_);
lean_del_object(v___x_1064_);
lean_dec(v_snd_1062_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_b_1043_);
lean_dec(v_a_1042_);
v_a_1136_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1071_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1071_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1064_);
lean_dec(v_snd_1062_);
lean_dec(v_fst_1061_);
lean_dec_ref(v___x_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_b_1043_);
lean_dec(v_a_1042_);
v_a_1148_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1066_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1066_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_b_1043_);
lean_dec(v_a_1042_);
v_a_1157_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1057_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1057_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
v___jp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_nat_add(v_a_1042_, v___x_1051_);
lean_dec(v_a_1042_);
v_a_1042_ = v___x_1052_;
v_b_1043_ = v_a_1050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_1165_, lean_object* v_fvars_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_1165_, v_fvars_1166_, v_a_1167_, v_b_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_fvars_1166_);
lean_dec(v_upperBound_1165_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v_fvars_1177_, lean_object* v_type_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = lean_array_get_size(v_fvars_1177_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1184_, v_fvars_1177_, v___x_1185_, v___x_1186_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
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
lean_object* v___x_1192_; lean_object* v_fst_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1204_; 
v___x_1192_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_1177_, v_type_1178_);
v_fst_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v___x_1192_, 1);
lean_dec(v_unused_1205_);
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_fst_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_a_1188_, v_fst_1193_);
lean_dec(v_a_1188_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_fst_1193_);
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_fst_1193_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1199_);
v___x_1201_ = v___x_1190_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
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
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v_type_1178_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v_fvars_1215_, lean_object* v_type_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v_fvars_1215_, v_type_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_fvars_1215_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1223_, lean_object* v_maxArgs_x3f_1224_, lean_object* v___f_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
v___x_1231_ = lean_infer_type(v_fn_1223_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1233_; uint8_t v_transparency_1234_; uint8_t v___x_1235_; uint8_t v___x_1236_; uint8_t v___y_1238_; uint8_t v___x_1296_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Lean_Meta_Context_config(v___y_1226_);
v_transparency_1234_ = lean_ctor_get_uint8(v___x_1233_, 9);
v___x_1235_ = 1;
v___x_1236_ = 0;
v___x_1296_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1234_, v___x_1235_);
if (v___x_1296_ == 0)
{
v___y_1238_ = v_transparency_1234_;
goto v___jp_1237_;
}
else
{
v___y_1238_ = v___x_1235_;
goto v___jp_1237_;
}
v___jp_1237_:
{
uint8_t v_foApprox_1239_; uint8_t v_ctxApprox_1240_; uint8_t v_quasiPatternApprox_1241_; uint8_t v_constApprox_1242_; uint8_t v_isDefEqStuckEx_1243_; uint8_t v_unificationHints_1244_; uint8_t v_proofIrrelevance_1245_; uint8_t v_assignSyntheticOpaque_1246_; uint8_t v_offsetCnstrs_1247_; uint8_t v_etaStruct_1248_; uint8_t v_univApprox_1249_; uint8_t v_iota_1250_; uint8_t v_beta_1251_; uint8_t v_proj_1252_; uint8_t v_zeta_1253_; uint8_t v_zetaDelta_1254_; uint8_t v_zetaUnused_1255_; uint8_t v_zetaHave_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1295_; 
v_foApprox_1239_ = lean_ctor_get_uint8(v___x_1233_, 0);
v_ctxApprox_1240_ = lean_ctor_get_uint8(v___x_1233_, 1);
v_quasiPatternApprox_1241_ = lean_ctor_get_uint8(v___x_1233_, 2);
v_constApprox_1242_ = lean_ctor_get_uint8(v___x_1233_, 3);
v_isDefEqStuckEx_1243_ = lean_ctor_get_uint8(v___x_1233_, 4);
v_unificationHints_1244_ = lean_ctor_get_uint8(v___x_1233_, 5);
v_proofIrrelevance_1245_ = lean_ctor_get_uint8(v___x_1233_, 6);
v_assignSyntheticOpaque_1246_ = lean_ctor_get_uint8(v___x_1233_, 7);
v_offsetCnstrs_1247_ = lean_ctor_get_uint8(v___x_1233_, 8);
v_etaStruct_1248_ = lean_ctor_get_uint8(v___x_1233_, 10);
v_univApprox_1249_ = lean_ctor_get_uint8(v___x_1233_, 11);
v_iota_1250_ = lean_ctor_get_uint8(v___x_1233_, 12);
v_beta_1251_ = lean_ctor_get_uint8(v___x_1233_, 13);
v_proj_1252_ = lean_ctor_get_uint8(v___x_1233_, 14);
v_zeta_1253_ = lean_ctor_get_uint8(v___x_1233_, 15);
v_zetaDelta_1254_ = lean_ctor_get_uint8(v___x_1233_, 16);
v_zetaUnused_1255_ = lean_ctor_get_uint8(v___x_1233_, 17);
v_zetaHave_1256_ = lean_ctor_get_uint8(v___x_1233_, 18);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1258_ = v___x_1233_;
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1233_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
uint8_t v_trackZetaDelta_1260_; lean_object* v_zetaDeltaSet_1261_; lean_object* v_lctx_1262_; lean_object* v_localInstances_1263_; lean_object* v_defEqCtx_x3f_1264_; lean_object* v_synthPendingDepth_1265_; lean_object* v_canUnfold_x3f_1266_; uint8_t v_univApprox_1267_; uint8_t v_inTypeClassResolution_1268_; uint8_t v_cacheInferType_1269_; lean_object* v_config_1271_; 
v_trackZetaDelta_1260_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*7);
v_zetaDeltaSet_1261_ = lean_ctor_get(v___y_1226_, 1);
lean_inc(v_zetaDeltaSet_1261_);
v_lctx_1262_ = lean_ctor_get(v___y_1226_, 2);
lean_inc_ref(v_lctx_1262_);
v_localInstances_1263_ = lean_ctor_get(v___y_1226_, 3);
lean_inc_ref(v_localInstances_1263_);
v_defEqCtx_x3f_1264_ = lean_ctor_get(v___y_1226_, 4);
lean_inc(v_defEqCtx_x3f_1264_);
v_synthPendingDepth_1265_ = lean_ctor_get(v___y_1226_, 5);
lean_inc(v_synthPendingDepth_1265_);
v_canUnfold_x3f_1266_ = lean_ctor_get(v___y_1226_, 6);
lean_inc(v_canUnfold_x3f_1266_);
v_univApprox_1267_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1268_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*7 + 2);
v_cacheInferType_1269_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*7 + 3);
if (v_isShared_1259_ == 0)
{
v_config_1271_ = v___x_1258_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 0, v_foApprox_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 1, v_ctxApprox_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 2, v_quasiPatternApprox_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 3, v_constApprox_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 4, v_isDefEqStuckEx_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 5, v_unificationHints_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 6, v_proofIrrelevance_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 7, v_assignSyntheticOpaque_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 8, v_offsetCnstrs_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 10, v_etaStruct_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 11, v_univApprox_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 12, v_iota_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 13, v_beta_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 14, v_proj_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 15, v_zeta_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 16, v_zetaDelta_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 17, v_zetaUnused_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, 18, v_zetaHave_1256_);
v_config_1271_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
uint64_t v___x_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1286_; 
lean_ctor_set_uint8(v_config_1271_, 9, v___y_1238_);
v___x_1272_ = l_Lean_Meta_Context_configKey(v___y_1226_);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___y_1226_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; lean_object* v_unused_1288_; lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; 
v_unused_1287_ = lean_ctor_get(v___y_1226_, 6);
lean_dec(v_unused_1287_);
v_unused_1288_ = lean_ctor_get(v___y_1226_, 5);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v___y_1226_, 4);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v___y_1226_, 3);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v___y_1226_, 2);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v___y_1226_, 1);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v___y_1226_, 0);
lean_dec(v_unused_1293_);
v___x_1274_ = v___y_1226_;
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___y_1226_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; uint64_t v___x_1279_; uint64_t v_key_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1276_ = 2ULL;
v___x_1277_ = lean_uint64_shift_right(v___x_1272_, v___x_1276_);
v___x_1278_ = lean_uint64_shift_left(v___x_1277_, v___x_1276_);
v___x_1279_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1238_);
v_key_1280_ = lean_uint64_lor(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1281_, 0, v_config_1271_);
lean_ctor_set_uint64(v___x_1281_, sizeof(void*)*1, v_key_1280_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1281_);
v___x_1283_ = v___x_1274_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_zetaDeltaSet_1261_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_lctx_1262_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_localInstances_1263_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_defEqCtx_x3f_1264_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v_synthPendingDepth_1265_);
lean_ctor_set(v_reuseFailAlloc_1285_, 6, v_canUnfold_x3f_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*7, v_trackZetaDelta_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*7 + 1, v_univApprox_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*7 + 3, v_cacheInferType_1269_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1232_, v_maxArgs_x3f_1224_, v___f_1225_, v___x_1236_, v___x_1236_, v___x_1283_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___x_1283_);
return v___x_1284_;
}
}
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___f_1225_);
lean_dec(v_maxArgs_x3f_1224_);
v_a_1297_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1231_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1231_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1305_, lean_object* v_maxArgs_x3f_1306_, lean_object* v___f_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1305_, v_maxArgs_x3f_1306_, v___f_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1314_, lean_object* v_vals_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_array_get_size(v_keys_1314_);
v___x_1319_ = lean_nat_dec_lt(v_i_1316_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_i_1316_);
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v_k_x27_1321_; uint8_t v___x_1322_; 
v_k_x27_1321_ = lean_array_fget_borrowed(v_keys_1314_, v_i_1316_);
v___x_1322_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1317_, v_k_x27_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_add(v_i_1316_, v___x_1323_);
lean_dec(v_i_1316_);
v_i_1316_ = v___x_1324_;
goto _start;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_array_fget_borrowed(v_vals_1315_, v_i_1316_);
lean_dec(v_i_1316_);
lean_inc(v___x_1326_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1328_, lean_object* v_vals_1329_, lean_object* v_i_1330_, lean_object* v_k_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1328_, v_vals_1329_, v_i_1330_, v_k_1331_);
lean_dec_ref(v_k_1331_);
lean_dec_ref(v_vals_1329_);
lean_dec_ref(v_keys_1328_);
return v_res_1332_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0(void){
_start:
{
size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; 
v___x_1333_ = ((size_t)5ULL);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_shift_left(v___x_1334_, v___x_1333_);
return v___x_1335_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; 
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0);
v___x_1338_ = lean_usize_sub(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1339_, size_t v_x_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 0)
{
lean_object* v_es_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v_j_1347_; lean_object* v___x_1348_; 
v_es_1342_ = lean_ctor_get(v_x_1339_, 0);
v___x_1343_ = lean_box(2);
v___x_1344_ = ((size_t)5ULL);
v___x_1345_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1346_ = lean_usize_land(v_x_1340_, v___x_1345_);
v_j_1347_ = lean_usize_to_nat(v___x_1346_);
v___x_1348_ = lean_array_get_borrowed(v___x_1343_, v_es_1342_, v_j_1347_);
lean_dec(v_j_1347_);
switch(lean_obj_tag(v___x_1348_))
{
case 0:
{
lean_object* v_key_1349_; lean_object* v_val_1350_; uint8_t v___x_1351_; 
v_key_1349_ = lean_ctor_get(v___x_1348_, 0);
v_val_1350_ = lean_ctor_get(v___x_1348_, 1);
v___x_1351_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1341_, v_key_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
lean_inc(v_val_1350_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_val_1350_);
return v___x_1353_;
}
}
case 1:
{
lean_object* v_node_1354_; size_t v___x_1355_; 
v_node_1354_ = lean_ctor_get(v___x_1348_, 0);
v___x_1355_ = lean_usize_shift_right(v_x_1340_, v___x_1344_);
v_x_1339_ = v_node_1354_;
v_x_1340_ = v___x_1355_;
goto _start;
}
default: 
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
}
}
else
{
lean_object* v_ks_1358_; lean_object* v_vs_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_ks_1358_ = lean_ctor_get(v_x_1339_, 0);
v_vs_1359_ = lean_ctor_get(v_x_1339_, 1);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1358_, v_vs_1359_, v___x_1360_, v_x_1341_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
size_t v_x_15142__boxed_1365_; lean_object* v_res_1366_; 
v_x_15142__boxed_1365_ = lean_unbox_usize(v_x_1363_);
lean_dec(v_x_1363_);
v_res_1366_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1362_, v_x_15142__boxed_1365_, v_x_1364_);
lean_dec_ref(v_x_1364_);
lean_dec_ref(v_x_1362_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
uint64_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1368_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1367_, v___x_1370_, v_x_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1372_, v_x_1373_);
lean_dec_ref(v_x_1373_);
lean_dec_ref(v_x_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_ks_1379_; lean_object* v_vs_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1404_; 
v_ks_1379_ = lean_ctor_get(v_x_1375_, 0);
v_vs_1380_ = lean_ctor_get(v_x_1375_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1375_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1382_ = v_x_1375_;
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_vs_1380_);
lean_inc(v_ks_1379_);
lean_dec(v_x_1375_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_array_get_size(v_ks_1379_);
v___x_1385_ = lean_nat_dec_lt(v_x_1376_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_x_1376_);
v___x_1386_ = lean_array_push(v_ks_1379_, v_x_1377_);
v___x_1387_ = lean_array_push(v_vs_1380_, v_x_1378_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1387_);
lean_ctor_set(v___x_1382_, 0, v___x_1386_);
v___x_1389_ = v___x_1382_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v_k_x27_1391_; uint8_t v___x_1392_; 
v_k_x27_1391_ = lean_array_fget_borrowed(v_ks_1379_, v_x_1376_);
v___x_1392_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1377_, v_k_x27_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1394_; 
if (v_isShared_1383_ == 0)
{
v___x_1394_ = v___x_1382_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_ks_1379_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_vs_1380_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_x_1376_, v___x_1395_);
lean_dec(v_x_1376_);
v_x_1375_ = v___x_1394_;
v_x_1376_ = v___x_1396_;
goto _start;
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1399_ = lean_array_fset(v_ks_1379_, v_x_1376_, v_x_1377_);
v___x_1400_ = lean_array_fset(v_vs_1380_, v_x_1376_, v_x_1378_);
lean_dec(v_x_1376_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1400_);
lean_ctor_set(v___x_1382_, 0, v___x_1399_);
v___x_1402_ = v___x_1382_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1405_, lean_object* v_k_1406_, lean_object* v_v_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_1405_, v___x_1408_, v_k_1406_, v_v_1407_);
return v___x_1409_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1411_, size_t v_x_1412_, size_t v_x_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_es_1416_; size_t v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; lean_object* v_j_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_es_1416_ = lean_ctor_get(v_x_1411_, 0);
v___x_1417_ = ((size_t)5ULL);
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1420_ = lean_usize_land(v_x_1412_, v___x_1419_);
v_j_1421_ = lean_usize_to_nat(v___x_1420_);
v___x_1422_ = lean_array_get_size(v_es_1416_);
v___x_1423_ = lean_nat_dec_lt(v_j_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v_j_1421_);
lean_dec(v_x_1415_);
lean_dec_ref(v_x_1414_);
return v_x_1411_;
}
else
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1460_; 
lean_inc_ref(v_es_1416_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_x_1411_, 0);
lean_dec(v_unused_1461_);
v___x_1425_ = v_x_1411_;
v_isShared_1426_ = v_isSharedCheck_1460_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_x_1411_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1460_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_v_1427_; lean_object* v___x_1428_; lean_object* v_xs_x27_1429_; lean_object* v___y_1431_; 
v_v_1427_ = lean_array_fget(v_es_1416_, v_j_1421_);
v___x_1428_ = lean_box(0);
v_xs_x27_1429_ = lean_array_fset(v_es_1416_, v_j_1421_, v___x_1428_);
switch(lean_obj_tag(v_v_1427_))
{
case 0:
{
lean_object* v_key_1436_; lean_object* v_val_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1447_; 
v_key_1436_ = lean_ctor_get(v_v_1427_, 0);
v_val_1437_ = lean_ctor_get(v_v_1427_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_v_1427_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1439_ = v_v_1427_;
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_val_1437_);
lean_inc(v_key_1436_);
lean_dec(v_v_1427_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; 
v___x_1441_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1414_, v_key_1436_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1439_);
v___x_1442_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1436_, v_val_1437_, v_x_1414_, v_x_1415_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___y_1431_ = v___x_1443_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1445_; 
lean_dec(v_val_1437_);
lean_dec(v_key_1436_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_x_1415_);
lean_ctor_set(v___x_1439_, 0, v_x_1414_);
v___x_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_x_1414_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_x_1415_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v___y_1431_ = v___x_1445_;
goto v___jp_1430_;
}
}
}
}
case 1:
{
lean_object* v_node_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v_node_1448_ = lean_ctor_get(v_v_1427_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_v_1427_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1450_ = v_v_1427_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_node_1448_);
lean_dec(v_v_1427_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1452_ = lean_usize_shift_right(v_x_1412_, v___x_1417_);
v___x_1453_ = lean_usize_add(v_x_1413_, v___x_1418_);
v___x_1454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1448_, v___x_1452_, v___x_1453_, v_x_1414_, v_x_1415_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1454_);
v___x_1456_ = v___x_1450_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
v___y_1431_ = v___x_1456_;
goto v___jp_1430_;
}
}
}
default: 
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_x_1414_);
lean_ctor_set(v___x_1459_, 1, v_x_1415_);
v___y_1431_ = v___x_1459_;
goto v___jp_1430_;
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_array_fset(v_xs_x27_1429_, v_j_1421_, v___y_1431_);
lean_dec(v_j_1421_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1432_);
v___x_1434_ = v___x_1425_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v_ks_1462_; lean_object* v_vs_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1483_; 
v_ks_1462_ = lean_ctor_get(v_x_1411_, 0);
v_vs_1463_ = lean_ctor_get(v_x_1411_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1465_ = v_x_1411_;
v_isShared_1466_ = v_isSharedCheck_1483_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_vs_1463_);
lean_inc(v_ks_1462_);
lean_dec(v_x_1411_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1483_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_ks_1462_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_vs_1463_);
v___x_1468_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v_newNode_1469_; uint8_t v___y_1471_; size_t v___x_1477_; uint8_t v___x_1478_; 
v_newNode_1469_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1468_, v_x_1414_, v_x_1415_);
v___x_1477_ = ((size_t)7ULL);
v___x_1478_ = lean_usize_dec_le(v___x_1477_, v_x_1413_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1469_);
v___x_1480_ = lean_unsigned_to_nat(4u);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
v___y_1471_ = v___x_1481_;
goto v___jp_1470_;
}
else
{
v___y_1471_ = v___x_1478_;
goto v___jp_1470_;
}
v___jp_1470_:
{
if (v___y_1471_ == 0)
{
lean_object* v_ks_1472_; lean_object* v_vs_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_ks_1472_ = lean_ctor_get(v_newNode_1469_, 0);
lean_inc_ref(v_ks_1472_);
v_vs_1473_ = lean_ctor_get(v_newNode_1469_, 1);
lean_inc_ref(v_vs_1473_);
lean_dec_ref(v_newNode_1469_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1413_, v_ks_1472_, v_vs_1473_, v___x_1474_, v___x_1475_);
lean_dec_ref(v_vs_1473_);
lean_dec_ref(v_ks_1472_);
return v___x_1476_;
}
else
{
return v_newNode_1469_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_i_1487_, lean_object* v_entries_1488_){
_start:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_array_get_size(v_keys_1485_);
v___x_1490_ = lean_nat_dec_lt(v_i_1487_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec(v_i_1487_);
return v_entries_1488_;
}
else
{
lean_object* v_k_1491_; lean_object* v_v_1492_; uint64_t v___x_1493_; size_t v_h_1494_; size_t v___x_1495_; lean_object* v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; size_t v___x_1499_; size_t v_h_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_k_1491_ = lean_array_fget_borrowed(v_keys_1485_, v_i_1487_);
v_v_1492_ = lean_array_fget_borrowed(v_vals_1486_, v_i_1487_);
v___x_1493_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1491_);
v_h_1494_ = lean_uint64_to_usize(v___x_1493_);
v___x_1495_ = ((size_t)5ULL);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_sub(v_depth_1484_, v___x_1497_);
v___x_1499_ = lean_usize_mul(v___x_1495_, v___x_1498_);
v_h_1500_ = lean_usize_shift_right(v_h_1494_, v___x_1499_);
v___x_1501_ = lean_nat_add(v_i_1487_, v___x_1496_);
lean_dec(v_i_1487_);
lean_inc(v_v_1492_);
lean_inc(v_k_1491_);
v___x_1502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1488_, v_h_1500_, v_depth_1484_, v_k_1491_, v_v_1492_);
v_i_1487_ = v___x_1501_;
v_entries_1488_ = v___x_1502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1504_, lean_object* v_keys_1505_, lean_object* v_vals_1506_, lean_object* v_i_1507_, lean_object* v_entries_1508_){
_start:
{
size_t v_depth_boxed_1509_; lean_object* v_res_1510_; 
v_depth_boxed_1509_ = lean_unbox_usize(v_depth_1504_);
lean_dec(v_depth_1504_);
v_res_1510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1509_, v_keys_1505_, v_vals_1506_, v_i_1507_, v_entries_1508_);
lean_dec_ref(v_vals_1506_);
lean_dec_ref(v_keys_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
size_t v_x_15289__boxed_1516_; size_t v_x_15290__boxed_1517_; lean_object* v_res_1518_; 
v_x_15289__boxed_1516_ = lean_unbox_usize(v_x_1512_);
lean_dec(v_x_1512_);
v_x_15290__boxed_1517_ = lean_unbox_usize(v_x_1513_);
lean_dec(v_x_1513_);
v_res_1518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1511_, v_x_15289__boxed_1516_, v_x_15290__boxed_1517_, v_x_1514_, v_x_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
uint64_t v___x_1522_; size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1520_);
v___x_1523_ = lean_uint64_to_usize(v___x_1522_);
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1519_, v___x_1523_, v___x_1524_, v_x_1520_, v_x_1521_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1529_, lean_object* v_env_1530_, lean_object* v_forConst_1531_, lean_object* v_ctx_1532_, lean_object* v_importRealizationCtx_x3f_1533_, lean_object* v_realize_1534_, lean_object* v_opts_1535_, lean_object* v_key_1536_, lean_object* v_inst_1537_, lean_object* v_____r_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_fst_1543_; lean_object* v_snd_1544_; lean_object* v___y_1576_; lean_object* v___x_1581_; 
v___x_1540_ = lean_io_promise_new();
v___x_1541_ = lean_st_ref_take(v_realizeMapRef_1529_);
v___x_1581_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1541_, v_inst_1537_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1576_ = v___x_1582_;
goto v___jp_1575_;
}
else
{
lean_object* v_val_1583_; 
v_val_1583_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_val_1583_);
lean_dec_ref(v___x_1581_);
v___y_1576_ = v_val_1583_;
goto v___jp_1575_;
}
v___jp_1542_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_st_ref_set(v_realizeMapRef_1529_, v_snd_1544_);
if (lean_obj_tag(v_fst_1543_) == 1)
{
lean_object* v_val_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v___x_1540_);
lean_dec_ref(v_opts_1535_);
lean_dec_ref(v_realize_1534_);
lean_dec(v_importRealizationCtx_x3f_1533_);
lean_dec_ref(v_ctx_1532_);
lean_dec(v_forConst_1531_);
lean_dec(v_env_1530_);
v_val_1546_ = lean_ctor_get(v_fst_1543_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_fst_1543_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1548_ = v_fst_1543_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_val_1546_);
lean_dec(v_fst_1543_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_task_get_own(v_val_1546_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_base_1555_; lean_object* v_serverBaseExts_1556_; lean_object* v_checked_1557_; lean_object* v_asyncConstsMap_1558_; lean_object* v_asyncCtx_x3f_1559_; lean_object* v_localRealizationCtxMap_1560_; lean_object* v_allRealizations_1561_; uint8_t v_isExporting_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_fst_1543_);
v_base_1555_ = lean_ctor_get(v_env_1530_, 0);
v_serverBaseExts_1556_ = lean_ctor_get(v_env_1530_, 1);
v_checked_1557_ = lean_ctor_get(v_env_1530_, 2);
v_asyncConstsMap_1558_ = lean_ctor_get(v_env_1530_, 3);
v_asyncCtx_x3f_1559_ = lean_ctor_get(v_env_1530_, 4);
v_localRealizationCtxMap_1560_ = lean_ctor_get(v_env_1530_, 6);
v_allRealizations_1561_ = lean_ctor_get(v_env_1530_, 7);
v_isExporting_1562_ = lean_ctor_get_uint8(v_env_1530_, sizeof(void*)*8);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_env_1530_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_env_1530_, 5);
lean_dec(v_unused_1574_);
v___x_1564_ = v_env_1530_;
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_allRealizations_1561_);
lean_inc(v_localRealizationCtxMap_1560_);
lean_inc(v_asyncCtx_x3f_1559_);
lean_inc(v_asyncConstsMap_1558_);
lean_inc(v_checked_1557_);
lean_inc(v_serverBaseExts_1556_);
lean_inc(v_base_1555_);
lean_dec(v_env_1530_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1531_, v_ctx_1532_, v_localRealizationCtxMap_1560_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 6, v___x_1566_);
lean_ctor_set(v___x_1564_, 5, v_importRealizationCtx_x3f_1533_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_base_1555_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_serverBaseExts_1556_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_checked_1557_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_asyncConstsMap_1558_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_asyncCtx_x3f_1559_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v_importRealizationCtx_x3f_1533_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v_allRealizations_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1572_, sizeof(void*)*8, v_isExporting_1562_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_apply_3(v_realize_1534_, v___x_1568_, v_opts_1535_, lean_box(0));
lean_inc(v___x_1569_);
v___x_1570_ = lean_io_promise_resolve(v___x_1569_, v___x_1540_);
lean_dec(v___x_1540_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
return v___x_1571_;
}
}
}
}
v___jp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1576_, v_key_1536_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = l_IO_Promise_result_x21___redArg(v___x_1540_);
v___x_1579_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1576_, v_key_1536_, v___x_1578_);
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1537_, v___x_1579_, v___x_1541_);
v_fst_1543_ = v___x_1577_;
v_snd_1544_ = v___x_1580_;
goto v___jp_1542_;
}
else
{
lean_dec_ref(v___y_1576_);
lean_dec(v_inst_1537_);
lean_dec_ref(v_key_1536_);
v_fst_1543_ = v___x_1577_;
v_snd_1544_ = v___x_1541_;
goto v___jp_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1584_, lean_object* v_env_1585_, lean_object* v_forConst_1586_, lean_object* v_ctx_1587_, lean_object* v_importRealizationCtx_x3f_1588_, lean_object* v_realize_1589_, lean_object* v_opts_1590_, lean_object* v_key_1591_, lean_object* v_inst_1592_, lean_object* v_____r_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1584_, v_env_1585_, v_forConst_1586_, v_ctx_1587_, v_importRealizationCtx_x3f_1588_, v_realize_1589_, v_opts_1590_, v_key_1591_, v_inst_1592_, v_____r_1593_);
lean_dec(v_realizeMapRef_1584_);
return v_res_1595_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = 0;
return v___x_1598_;
}
else
{
lean_object* v_key_1599_; lean_object* v_tail_1600_; uint8_t v___x_1601_; 
v_key_1599_ = lean_ctor_get(v_x_1597_, 0);
v_tail_1600_ = lean_ctor_get(v_x_1597_, 2);
v___x_1601_ = lean_name_eq(v_key_1599_, v_a_1596_);
if (v___x_1601_ == 0)
{
v_x_1597_ = v_tail_1600_;
goto _start;
}
else
{
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1603_, lean_object* v_x_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1603_, v_x_1604_);
lean_dec(v_x_1604_);
lean_dec(v_a_1603_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_buckets_1609_; lean_object* v___x_1610_; uint64_t v___y_1612_; 
v_buckets_1609_ = lean_ctor_get(v_m_1607_, 1);
v___x_1610_ = lean_array_get_size(v_buckets_1609_);
if (lean_obj_tag(v_a_1608_) == 0)
{
uint64_t v___x_1626_; 
v___x_1626_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_1612_ = v___x_1626_;
goto v___jp_1611_;
}
else
{
uint64_t v_hash_1627_; 
v_hash_1627_ = lean_ctor_get_uint64(v_a_1608_, sizeof(void*)*2);
v___y_1612_ = v_hash_1627_;
goto v___jp_1611_;
}
v___jp_1611_:
{
uint64_t v___x_1613_; uint64_t v___x_1614_; uint64_t v_fold_1615_; uint64_t v___x_1616_; uint64_t v___x_1617_; uint64_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1613_ = 32ULL;
v___x_1614_ = lean_uint64_shift_right(v___y_1612_, v___x_1613_);
v_fold_1615_ = lean_uint64_xor(v___y_1612_, v___x_1614_);
v___x_1616_ = 16ULL;
v___x_1617_ = lean_uint64_shift_right(v_fold_1615_, v___x_1616_);
v___x_1618_ = lean_uint64_xor(v_fold_1615_, v___x_1617_);
v___x_1619_ = lean_uint64_to_usize(v___x_1618_);
v___x_1620_ = lean_usize_of_nat(v___x_1610_);
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_sub(v___x_1620_, v___x_1621_);
v___x_1623_ = lean_usize_land(v___x_1619_, v___x_1622_);
v___x_1624_ = lean_array_uget_borrowed(v_buckets_1609_, v___x_1623_);
v___x_1625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1608_, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1628_, lean_object* v_a_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_m_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1638_, lean_object* v_env_1639_, lean_object* v_forConst_1640_, lean_object* v_key_1641_, lean_object* v_realize_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v_a_1646_; lean_object* v___y_1650_; lean_object* v_base_1652_; lean_object* v_importRealizationCtx_x3f_1653_; lean_object* v_localRealizationCtxMap_1654_; uint8_t v_isExporting_1655_; lean_object* v_ctx_1657_; lean_object* v___y_1672_; 
v___x_1644_ = lean_io_get_num_heartbeats();
v_base_1652_ = lean_ctor_get(v_env_1639_, 0);
lean_inc_ref(v_base_1652_);
v_importRealizationCtx_x3f_1653_ = lean_ctor_get(v_env_1639_, 5);
lean_inc(v_importRealizationCtx_x3f_1653_);
v_localRealizationCtxMap_1654_ = lean_ctor_get(v_env_1639_, 6);
lean_inc(v_localRealizationCtxMap_1654_);
v_isExporting_1655_ = lean_ctor_get_uint8(v_env_1639_, sizeof(void*)*8);
lean_dec_ref(v_env_1639_);
if (v_isExporting_1655_ == 0)
{
lean_object* v_private_1692_; 
v_private_1692_ = lean_ctor_get(v_base_1652_, 0);
lean_inc(v_private_1692_);
lean_dec_ref(v_base_1652_);
v___y_1672_ = v_private_1692_;
goto v___jp_1671_;
}
else
{
lean_object* v_public_1693_; 
v_public_1693_ = lean_ctor_get(v_base_1652_, 1);
lean_inc(v_public_1693_);
lean_dec_ref(v_base_1652_);
v___y_1672_ = v_public_1693_;
goto v___jp_1671_;
}
v___jp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_io_set_heartbeats(v___x_1644_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_a_1646_);
return v___x_1648_;
}
v___jp_1649_:
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___y_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___y_1650_);
v_a_1646_ = v_a_1651_;
goto v___jp_1645_;
}
v___jp_1656_:
{
lean_object* v_env_1658_; lean_object* v_opts_1659_; lean_object* v_realizeMapRef_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_env_1658_ = lean_ctor_get(v_ctx_1657_, 0);
lean_inc(v_env_1658_);
v_opts_1659_ = lean_ctor_get(v_ctx_1657_, 1);
lean_inc_ref(v_opts_1659_);
v_realizeMapRef_1660_ = lean_ctor_get(v_ctx_1657_, 2);
lean_inc(v_realizeMapRef_1660_);
v___x_1661_ = lean_st_ref_get(v_realizeMapRef_1660_);
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1661_, v_inst_1638_);
lean_dec(v___x_1661_);
if (lean_obj_tag(v___x_1662_) == 1)
{
lean_object* v_val_1663_; lean_object* v___x_1664_; 
v_val_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1663_);
lean_dec_ref(v___x_1662_);
v___x_1664_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1663_, v_key_1641_);
lean_dec(v_val_1663_);
if (lean_obj_tag(v___x_1664_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1666_; 
lean_dec(v_realizeMapRef_1660_);
lean_dec_ref(v_opts_1659_);
lean_dec(v_env_1658_);
lean_dec_ref(v_ctx_1657_);
lean_dec(v_importRealizationCtx_x3f_1653_);
lean_dec_ref(v_realize_1642_);
lean_dec_ref(v_key_1641_);
lean_dec(v_forConst_1640_);
lean_dec(v_inst_1638_);
v_val_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_val_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = lean_task_get_own(v_val_1665_);
v_a_1646_ = v___x_1666_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v___x_1668_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1660_, v_env_1658_, v_forConst_1640_, v_ctx_1657_, v_importRealizationCtx_x3f_1653_, v_realize_1642_, v_opts_1659_, v_key_1641_, v_inst_1638_, v___x_1667_);
lean_dec(v_realizeMapRef_1660_);
v___y_1650_ = v___x_1668_;
goto v___jp_1649_;
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v___x_1662_);
v___x_1669_ = lean_box(0);
v___x_1670_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1660_, v_env_1658_, v_forConst_1640_, v_ctx_1657_, v_importRealizationCtx_x3f_1653_, v_realize_1642_, v_opts_1659_, v_key_1641_, v_inst_1638_, v___x_1669_);
lean_dec(v_realizeMapRef_1660_);
v___y_1650_ = v___x_1670_;
goto v___jp_1649_;
}
}
v___jp_1671_:
{
lean_object* v_const2ModIdx_1673_; uint8_t v___x_1674_; 
v_const2ModIdx_1673_ = lean_ctor_get(v___y_1672_, 2);
lean_inc_ref(v_const2ModIdx_1673_);
lean_dec_ref(v___y_1672_);
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1673_, v_forConst_1640_);
lean_dec_ref(v_const2ModIdx_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1654_, v_forConst_1640_);
lean_dec(v_localRealizationCtxMap_1654_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_importRealizationCtx_x3f_1653_);
lean_dec(v___x_1644_);
lean_dec_ref(v_realize_1642_);
lean_dec_ref(v_key_1641_);
v___x_1676_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1677_ = 1;
v___x_1678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1638_, v___x_1677_);
v___x_1679_ = lean_string_append(v___x_1676_, v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1681_ = lean_string_append(v___x_1679_, v___x_1680_);
v___x_1682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1640_, v___x_1677_);
v___x_1683_ = lean_string_append(v___x_1681_, v___x_1682_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1685_ = lean_string_append(v___x_1683_, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
else
{
lean_object* v_val_1688_; 
v_val_1688_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1688_);
lean_dec_ref(v___x_1675_);
v_ctx_1657_ = v_val_1688_;
goto v___jp_1656_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1654_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1653_) == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1644_);
lean_dec_ref(v_realize_1642_);
lean_dec_ref(v_key_1641_);
lean_dec(v_forConst_1640_);
lean_dec(v_inst_1638_);
v___x_1689_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; 
v_val_1691_ = lean_ctor_get(v_importRealizationCtx_x3f_1653_, 0);
lean_inc(v_val_1691_);
v_ctx_1657_ = v_val_1691_;
goto v___jp_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1694_, lean_object* v_env_1695_, lean_object* v_forConst_1696_, lean_object* v_key_1697_, lean_object* v_realize_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1694_, v_env_1695_, v_forConst_1696_, v_key_1697_, v_realize_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___f_1707_; lean_object* v___x_13406__overap_1708_; lean_object* v___x_1709_; 
v___f_1707_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_13406__overap_1708_ = lean_panic_fn_borrowed(v___f_1707_, v_msg_1701_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1709_ = lean_apply_5(v___x_13406__overap_1708_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1717_, lean_object* v_inst_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
v___x_1724_ = lean_apply_5(v_realize_1717_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, lean_box(0));
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_inst_1718_);
lean_ctor_set(v___x_1729_, 1, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_inst_1718_);
v_a_1734_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1724_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1724_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1742_, lean_object* v_inst_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1742_, v_inst_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
return v_res_1749_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l_Lean_Options_empty;
v___x_1751_ = l_Lean_Core_getMaxHeartbeats(v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_unsigned_to_nat(16u);
v___x_1754_ = lean_mk_array(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_1761_ = lean_unsigned_to_nat(36u);
v___x_1762_ = lean_unsigned_to_nat(2592u);
v___x_1763_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1764_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1765_ = l_mkPanicMessageWithDecl(v___x_1764_, v___x_1763_, v___x_1762_, v___x_1761_, v___x_1760_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_1767_ = lean_unsigned_to_nat(48u);
v___x_1768_ = lean_unsigned_to_nat(2583u);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1770_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1771_ = l_mkPanicMessageWithDecl(v___x_1770_, v___x_1769_, v___x_1768_, v___x_1767_, v___x_1766_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_forConst_1774_, lean_object* v_key_1775_, lean_object* v_realize_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v_env_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_st_ref_get(v_a_1780_);
v_env_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc_ref(v_env_1783_);
lean_dec(v___x_1782_);
v___x_1784_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1783_, v_forConst_1774_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
lean_dec_ref(v_env_1783_);
lean_dec_ref(v_key_1775_);
lean_dec(v_forConst_1774_);
lean_dec(v_inst_1773_);
lean_dec(v_inst_1772_);
lean_inc(v_a_1780_);
lean_inc_ref(v_a_1779_);
lean_inc(v_a_1778_);
lean_inc_ref(v_a_1777_);
v___x_1785_ = lean_apply_5(v_realize_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, lean_box(0));
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v_fileName_1787_; lean_object* v_fileMap_1788_; lean_object* v_ref_1789_; lean_object* v___f_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1786_ = lean_io_get_num_heartbeats();
v_fileName_1787_ = lean_ctor_get(v_a_1779_, 0);
v_fileMap_1788_ = lean_ctor_get(v_a_1779_, 1);
v_ref_1789_ = lean_ctor_get(v_a_1779_, 5);
lean_inc(v_inst_1773_);
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1790_, 0, v_realize_1776_);
lean_closure_set(v___f_1790_, 1, v_inst_1773_);
v___x_1791_ = 0;
v___x_1792_ = l_Lean_Options_empty;
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_unsigned_to_nat(1000u);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1799_ = l_Lean_firstFrontendMacroScope;
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1788_);
lean_inc_ref(v_fileName_1787_);
v___x_1802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1802_, 0, v_fileName_1787_);
lean_ctor_set(v___x_1802_, 1, v_fileMap_1788_);
lean_ctor_set(v___x_1802_, 2, v___x_1792_);
lean_ctor_set(v___x_1802_, 3, v___x_1793_);
lean_ctor_set(v___x_1802_, 4, v___x_1794_);
lean_ctor_set(v___x_1802_, 5, v___x_1795_);
lean_ctor_set(v___x_1802_, 6, v___x_1796_);
lean_ctor_set(v___x_1802_, 7, v___x_1797_);
lean_ctor_set(v___x_1802_, 8, v___x_1786_);
lean_ctor_set(v___x_1802_, 9, v___x_1798_);
lean_ctor_set(v___x_1802_, 10, v___x_1796_);
lean_ctor_set(v___x_1802_, 11, v___x_1799_);
lean_ctor_set(v___x_1802_, 12, v___x_1800_);
lean_ctor_set(v___x_1802_, 13, v___x_1801_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14, v___x_1791_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14 + 1, v___x_1791_);
v___x_1803_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1803_, 0, v___f_1790_);
lean_closure_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1772_, v_env_1783_, v_forConst_1774_, v_key_1775_, v___x_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1857_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1857_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1857_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1810_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1805_, v___x_1809_);
lean_dec(v_a_1805_);
if (lean_obj_tag(v___x_1810_) == 1)
{
lean_object* v_val_1811_; lean_object* v_res_x3f_1812_; lean_object* v_snap_x3f_1813_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v_snap_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; 
v_val_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_val_1811_);
lean_dec_ref(v___x_1810_);
v_res_x3f_1812_ = lean_ctor_get(v_val_1811_, 0);
lean_inc_ref(v_res_x3f_1812_);
v_snap_x3f_1813_ = lean_ctor_get(v_val_1811_, 1);
lean_inc(v_snap_x3f_1813_);
lean_dec(v_val_1811_);
if (lean_obj_tag(v_snap_x3f_1813_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1848_; 
v_val_1847_ = lean_ctor_get(v_snap_x3f_1813_, 0);
lean_inc(v_val_1847_);
lean_dec_ref(v_snap_x3f_1813_);
v___x_1848_ = l_Lean_Syntax_getRange_x3f(v_ref_1789_, v___x_1791_);
if (lean_obj_tag(v___x_1848_) == 1)
{
lean_object* v_val_1849_; lean_object* v_start_1850_; lean_object* v_stop_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_val_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1849_);
lean_dec_ref(v___x_1848_);
v_start_1850_ = lean_ctor_get(v_val_1849_, 0);
lean_inc(v_start_1850_);
v_stop_1851_ = lean_ctor_get(v_val_1849_, 1);
lean_inc(v_stop_1851_);
lean_dec(v_val_1849_);
lean_inc_ref_n(v_fileMap_1788_, 2);
v___x_1852_ = l_Lean_FileMap_toPosition(v_fileMap_1788_, v_start_1850_);
lean_dec(v_start_1850_);
v___x_1853_ = l_Lean_FileMap_toPosition(v_fileMap_1788_, v_stop_1851_);
lean_dec(v_stop_1851_);
v___x_1854_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1847_, v___x_1852_, v___x_1853_);
v_snap_1832_ = v___x_1854_;
v___y_1833_ = v_a_1777_;
v___y_1834_ = v_a_1778_;
v___y_1835_ = v_a_1779_;
v___y_1836_ = v_a_1780_;
goto v___jp_1831_;
}
else
{
lean_dec(v___x_1848_);
v_snap_1832_ = v_val_1847_;
v___y_1833_ = v_a_1777_;
v___y_1834_ = v_a_1778_;
v___y_1835_ = v_a_1779_;
v___y_1836_ = v_a_1780_;
goto v___jp_1831_;
}
}
else
{
lean_dec(v_snap_x3f_1813_);
v___y_1815_ = v_a_1777_;
v___y_1816_ = v_a_1778_;
v___y_1817_ = v_a_1779_;
v___y_1818_ = v_a_1780_;
goto v___jp_1814_;
}
v___jp_1814_:
{
if (lean_obj_tag(v_res_x3f_1812_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; 
lean_dec(v_inst_1773_);
v_a_1819_ = lean_ctor_get(v_res_x3f_1812_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v_res_x3f_1812_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
lean_ctor_set(v___x_1807_, 0, v_a_1819_);
v___x_1821_ = v___x_1807_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v_res_x3f_1812_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v_res_x3f_1812_);
v___x_1824_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1823_, v_inst_1773_);
lean_dec(v_inst_1773_);
lean_dec(v_a_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_del_object(v___x_1807_);
v___x_1825_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1826_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1825_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1826_;
}
else
{
lean_object* v_val_1827_; lean_object* v___x_1829_; 
v_val_1827_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1827_);
lean_dec_ref(v___x_1824_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_val_1827_);
v___x_1829_ = v___x_1807_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_val_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
v___jp_1831_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1800_, v_snap_1832_);
v___x_1838_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1837_, v___y_1836_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref(v___x_1838_);
v___y_1815_ = v___y_1833_;
v___y_1816_ = v___y_1834_;
v___y_1817_ = v___y_1835_;
v___y_1818_ = v___y_1836_;
goto v___jp_1814_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_res_x3f_1812_);
lean_del_object(v___x_1807_);
lean_dec(v_inst_1773_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v___x_1810_);
lean_del_object(v___x_1807_);
lean_dec(v_inst_1773_);
v___x_1855_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1856_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1855_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_inst_1773_);
v_a_1858_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1860_ = v___x_1804_;
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1804_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1862_ = lean_io_error_to_string(v_a_1858_);
v___x_1863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
lean_inc(v_ref_1789_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_ref_1789_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1865_);
v___x_1867_ = v___x_1860_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_forConst_1872_, lean_object* v_key_1873_, lean_object* v_realize_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1870_, v_inst_1871_, v_forConst_1872_, v_key_1873_, v_realize_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_i_1883_, lean_object* v_k_1884_){
_start:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_get_size(v_keys_1881_);
v___x_1886_ = lean_nat_dec_lt(v_i_1883_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec(v_i_1883_);
v___x_1887_ = lean_box(0);
return v___x_1887_;
}
else
{
lean_object* v_k_x27_1888_; uint8_t v___x_1889_; 
v_k_x27_1888_ = lean_array_fget_borrowed(v_keys_1881_, v_i_1883_);
v___x_1889_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1884_, v_k_x27_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_add(v_i_1883_, v___x_1890_);
lean_dec(v_i_1883_);
v_i_1883_ = v___x_1891_;
goto _start;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_array_fget_borrowed(v_vals_1882_, v_i_1883_);
lean_dec(v_i_1883_);
lean_inc(v___x_1893_);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1895_, v_vals_1896_, v_i_1897_, v_k_1898_);
lean_dec_ref(v_k_1898_);
lean_dec_ref(v_vals_1896_);
lean_dec_ref(v_keys_1895_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1900_, size_t v_x_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
lean_object* v_es_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; lean_object* v_j_1908_; lean_object* v___x_1909_; 
v_es_1903_ = lean_ctor_get(v_x_1900_, 0);
v___x_1904_ = lean_box(2);
v___x_1905_ = ((size_t)5ULL);
v___x_1906_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1907_ = lean_usize_land(v_x_1901_, v___x_1906_);
v_j_1908_ = lean_usize_to_nat(v___x_1907_);
v___x_1909_ = lean_array_get_borrowed(v___x_1904_, v_es_1903_, v_j_1908_);
lean_dec(v_j_1908_);
switch(lean_obj_tag(v___x_1909_))
{
case 0:
{
lean_object* v_key_1910_; lean_object* v_val_1911_; uint8_t v___x_1912_; 
v_key_1910_ = lean_ctor_get(v___x_1909_, 0);
v_val_1911_ = lean_ctor_get(v___x_1909_, 1);
v___x_1912_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1902_, v_key_1910_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_box(0);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
lean_inc(v_val_1911_);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_val_1911_);
return v___x_1914_;
}
}
case 1:
{
lean_object* v_node_1915_; size_t v___x_1916_; 
v_node_1915_ = lean_ctor_get(v___x_1909_, 0);
v___x_1916_ = lean_usize_shift_right(v_x_1901_, v___x_1905_);
v_x_1900_ = v_node_1915_;
v_x_1901_ = v___x_1916_;
goto _start;
}
default: 
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_box(0);
return v___x_1918_;
}
}
}
else
{
lean_object* v_ks_1919_; lean_object* v_vs_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_ks_1919_ = lean_ctor_get(v_x_1900_, 0);
v_vs_1920_ = lean_ctor_get(v_x_1900_, 1);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1919_, v_vs_1920_, v___x_1921_, v_x_1902_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
size_t v_x_16041__boxed_1926_; lean_object* v_res_1927_; 
v_x_16041__boxed_1926_ = lean_unbox_usize(v_x_1924_);
lean_dec(v_x_1924_);
v_res_1927_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1923_, v_x_16041__boxed_1926_, v_x_1925_);
lean_dec_ref(v_x_1925_);
lean_dec_ref(v_x_1923_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
uint64_t v_configKey_1930_; lean_object* v_expr_1931_; lean_object* v_nargs_x3f_1932_; uint64_t v___x_1933_; uint64_t v___y_1935_; 
v_configKey_1930_ = lean_ctor_get_uint64(v_x_1929_, sizeof(void*)*2);
v_expr_1931_ = lean_ctor_get(v_x_1929_, 0);
v_nargs_x3f_1932_ = lean_ctor_get(v_x_1929_, 1);
v___x_1933_ = l_Lean_Expr_hash(v_expr_1931_);
if (lean_obj_tag(v_nargs_x3f_1932_) == 0)
{
uint64_t v___x_1940_; 
v___x_1940_ = 11ULL;
v___y_1935_ = v___x_1940_;
goto v___jp_1934_;
}
else
{
lean_object* v_val_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; 
v_val_1941_ = lean_ctor_get(v_nargs_x3f_1932_, 0);
v___x_1942_ = lean_uint64_of_nat(v_val_1941_);
v___x_1943_ = 13ULL;
v___x_1944_ = lean_uint64_mix_hash(v___x_1942_, v___x_1943_);
v___y_1935_ = v___x_1944_;
goto v___jp_1934_;
}
v___jp_1934_:
{
uint64_t v___x_1936_; uint64_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = lean_uint64_mix_hash(v___x_1933_, v___y_1935_);
v___x_1937_ = lean_uint64_mix_hash(v_configKey_1930_, v___x_1936_);
v___x_1938_ = lean_uint64_to_usize(v___x_1937_);
v___x_1939_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1928_, v___x_1938_, v_x_1929_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1945_, v_x_1946_);
lean_dec_ref(v_x_1946_);
lean_dec_ref(v_x_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v_ks_1952_; lean_object* v_vs_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1977_; 
v_ks_1952_ = lean_ctor_get(v_x_1948_, 0);
v_vs_1953_ = lean_ctor_get(v_x_1948_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1948_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1955_ = v_x_1948_;
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_vs_1953_);
lean_inc(v_ks_1952_);
lean_dec(v_x_1948_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = lean_array_get_size(v_ks_1952_);
v___x_1958_ = lean_nat_dec_lt(v_x_1949_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_x_1949_);
v___x_1959_ = lean_array_push(v_ks_1952_, v_x_1950_);
v___x_1960_ = lean_array_push(v_vs_1953_, v_x_1951_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v___x_1960_);
lean_ctor_set(v___x_1955_, 0, v___x_1959_);
v___x_1962_ = v___x_1955_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v_k_x27_1964_; uint8_t v___x_1965_; 
v_k_x27_1964_ = lean_array_fget_borrowed(v_ks_1952_, v_x_1949_);
v___x_1965_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1950_, v_k_x27_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; 
if (v_isShared_1956_ == 0)
{
v___x_1967_ = v___x_1955_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_ks_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_vs_1953_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_add(v_x_1949_, v___x_1968_);
lean_dec(v_x_1949_);
v_x_1948_ = v___x_1967_;
v_x_1949_ = v___x_1969_;
goto _start;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = lean_array_fset(v_ks_1952_, v_x_1949_, v_x_1950_);
v___x_1973_ = lean_array_fset(v_vs_1953_, v_x_1949_, v_x_1951_);
lean_dec(v_x_1949_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v___x_1973_);
lean_ctor_set(v___x_1955_, 0, v___x_1972_);
v___x_1975_ = v___x_1955_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1978_, lean_object* v_k_1979_, lean_object* v_v_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1978_, v___x_1981_, v_k_1979_, v_v_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1984_, size_t v_x_1985_, size_t v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v_es_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v_j_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_es_1989_ = lean_ctor_get(v_x_1984_, 0);
v___x_1990_ = ((size_t)5ULL);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1993_ = lean_usize_land(v_x_1985_, v___x_1992_);
v_j_1994_ = lean_usize_to_nat(v___x_1993_);
v___x_1995_ = lean_array_get_size(v_es_1989_);
v___x_1996_ = lean_nat_dec_lt(v_j_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec(v_j_1994_);
lean_dec(v_x_1988_);
lean_dec_ref(v_x_1987_);
return v_x_1984_;
}
else
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2033_; 
lean_inc_ref(v_es_1989_);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_x_1984_, 0);
lean_dec(v_unused_2034_);
v___x_1998_ = v_x_1984_;
v_isShared_1999_ = v_isSharedCheck_2033_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_x_1984_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2033_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_v_2000_; lean_object* v___x_2001_; lean_object* v_xs_x27_2002_; lean_object* v___y_2004_; 
v_v_2000_ = lean_array_fget(v_es_1989_, v_j_1994_);
v___x_2001_ = lean_box(0);
v_xs_x27_2002_ = lean_array_fset(v_es_1989_, v_j_1994_, v___x_2001_);
switch(lean_obj_tag(v_v_2000_))
{
case 0:
{
lean_object* v_key_2009_; lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_key_2009_ = lean_ctor_get(v_v_2000_, 0);
v_val_2010_ = lean_ctor_get(v_v_2000_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_v_2000_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v_v_2000_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_inc(v_key_2009_);
lean_dec(v_v_2000_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1987_, v_key_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_2012_);
v___x_2015_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2009_, v_val_2010_, v_x_1987_, v_x_1988_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___y_2004_ = v___x_2016_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2018_; 
lean_dec(v_val_2010_);
lean_dec(v_key_2009_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_x_1988_);
lean_ctor_set(v___x_2012_, 0, v_x_1987_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_x_1987_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_x_1988_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v___y_2004_ = v___x_2018_;
goto v___jp_2003_;
}
}
}
}
case 1:
{
lean_object* v_node_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2031_; 
v_node_2021_ = lean_ctor_get(v_v_2000_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_v_2000_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2023_ = v_v_2000_;
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_node_2021_);
lean_dec(v_v_2000_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2031_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2025_ = lean_usize_shift_right(v_x_1985_, v___x_1990_);
v___x_2026_ = lean_usize_add(v_x_1986_, v___x_1991_);
v___x_2027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_2021_, v___x_2025_, v___x_2026_, v_x_1987_, v_x_1988_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2027_);
v___x_2029_ = v___x_2023_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
v___y_2004_ = v___x_2029_;
goto v___jp_2003_;
}
}
}
default: 
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_x_1987_);
lean_ctor_set(v___x_2032_, 1, v_x_1988_);
v___y_2004_ = v___x_2032_;
goto v___jp_2003_;
}
}
v___jp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_array_fset(v_xs_x27_2002_, v_j_1994_, v___y_2004_);
lean_dec(v_j_1994_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2005_);
v___x_2007_ = v___x_1998_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v_ks_2035_; lean_object* v_vs_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2056_; 
v_ks_2035_ = lean_ctor_get(v_x_1984_, 0);
v_vs_2036_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2038_ = v_x_1984_;
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_vs_2036_);
lean_inc(v_ks_2035_);
lean_dec(v_x_1984_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_ks_2035_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_vs_2036_);
v___x_2041_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v_newNode_2042_; uint8_t v___y_2044_; size_t v___x_2050_; uint8_t v___x_2051_; 
v_newNode_2042_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_2041_, v_x_1987_, v_x_1988_);
v___x_2050_ = ((size_t)7ULL);
v___x_2051_ = lean_usize_dec_le(v___x_2050_, v_x_1986_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2042_);
v___x_2053_ = lean_unsigned_to_nat(4u);
v___x_2054_ = lean_nat_dec_lt(v___x_2052_, v___x_2053_);
lean_dec(v___x_2052_);
v___y_2044_ = v___x_2054_;
goto v___jp_2043_;
}
else
{
v___y_2044_ = v___x_2051_;
goto v___jp_2043_;
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
lean_object* v_ks_2045_; lean_object* v_vs_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_ks_2045_ = lean_ctor_get(v_newNode_2042_, 0);
lean_inc_ref(v_ks_2045_);
v_vs_2046_ = lean_ctor_get(v_newNode_2042_, 1);
lean_inc_ref(v_vs_2046_);
lean_dec_ref(v_newNode_2042_);
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_2049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1986_, v_ks_2045_, v_vs_2046_, v___x_2047_, v___x_2048_);
lean_dec_ref(v_vs_2046_);
lean_dec_ref(v_ks_2045_);
return v___x_2049_;
}
else
{
return v_newNode_2042_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_2057_, lean_object* v_keys_2058_, lean_object* v_vals_2059_, lean_object* v_i_2060_, lean_object* v_entries_2061_){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_array_get_size(v_keys_2058_);
v___x_2063_ = lean_nat_dec_lt(v_i_2060_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec(v_i_2060_);
return v_entries_2061_;
}
else
{
lean_object* v_k_2064_; uint64_t v_configKey_2065_; lean_object* v_expr_2066_; lean_object* v_nargs_x3f_2067_; lean_object* v_v_2068_; uint64_t v___x_2069_; uint64_t v___y_2071_; 
v_k_2064_ = lean_array_fget_borrowed(v_keys_2058_, v_i_2060_);
v_configKey_2065_ = lean_ctor_get_uint64(v_k_2064_, sizeof(void*)*2);
v_expr_2066_ = lean_ctor_get(v_k_2064_, 0);
v_nargs_x3f_2067_ = lean_ctor_get(v_k_2064_, 1);
v_v_2068_ = lean_array_fget_borrowed(v_vals_2059_, v_i_2060_);
v___x_2069_ = l_Lean_Expr_hash(v_expr_2066_);
if (lean_obj_tag(v_nargs_x3f_2067_) == 0)
{
uint64_t v___x_2084_; 
v___x_2084_ = 11ULL;
v___y_2071_ = v___x_2084_;
goto v___jp_2070_;
}
else
{
lean_object* v_val_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; 
v_val_2085_ = lean_ctor_get(v_nargs_x3f_2067_, 0);
v___x_2086_ = lean_uint64_of_nat(v_val_2085_);
v___x_2087_ = 13ULL;
v___x_2088_ = lean_uint64_mix_hash(v___x_2086_, v___x_2087_);
v___y_2071_ = v___x_2088_;
goto v___jp_2070_;
}
v___jp_2070_:
{
uint64_t v___x_2072_; uint64_t v___x_2073_; size_t v_h_2074_; size_t v___x_2075_; lean_object* v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; size_t v_h_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2072_ = lean_uint64_mix_hash(v___x_2069_, v___y_2071_);
v___x_2073_ = lean_uint64_mix_hash(v_configKey_2065_, v___x_2072_);
v_h_2074_ = lean_uint64_to_usize(v___x_2073_);
v___x_2075_ = ((size_t)5ULL);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_sub(v_depth_2057_, v___x_2077_);
v___x_2079_ = lean_usize_mul(v___x_2075_, v___x_2078_);
v_h_2080_ = lean_usize_shift_right(v_h_2074_, v___x_2079_);
v___x_2081_ = lean_nat_add(v_i_2060_, v___x_2076_);
lean_dec(v_i_2060_);
lean_inc(v_v_2068_);
lean_inc(v_k_2064_);
v___x_2082_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_2061_, v_h_2080_, v_depth_2057_, v_k_2064_, v_v_2068_);
v_i_2060_ = v___x_2081_;
v_entries_2061_ = v___x_2082_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2089_, lean_object* v_keys_2090_, lean_object* v_vals_2091_, lean_object* v_i_2092_, lean_object* v_entries_2093_){
_start:
{
size_t v_depth_boxed_2094_; lean_object* v_res_2095_; 
v_depth_boxed_2094_ = lean_unbox_usize(v_depth_2089_);
lean_dec(v_depth_2089_);
v_res_2095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_2094_, v_keys_2090_, v_vals_2091_, v_i_2092_, v_entries_2093_);
lean_dec_ref(v_vals_2091_);
lean_dec_ref(v_keys_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
size_t v_x_16220__boxed_2101_; size_t v_x_16221__boxed_2102_; lean_object* v_res_2103_; 
v_x_16220__boxed_2101_ = lean_unbox_usize(v_x_2097_);
lean_dec(v_x_2097_);
v_x_16221__boxed_2102_ = lean_unbox_usize(v_x_2098_);
lean_dec(v_x_2098_);
v_res_2103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2096_, v_x_16220__boxed_2101_, v_x_16221__boxed_2102_, v_x_2099_, v_x_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
uint64_t v_configKey_2107_; lean_object* v_expr_2108_; lean_object* v_nargs_x3f_2109_; uint64_t v___x_2110_; uint64_t v___y_2112_; 
v_configKey_2107_ = lean_ctor_get_uint64(v_x_2105_, sizeof(void*)*2);
v_expr_2108_ = lean_ctor_get(v_x_2105_, 0);
v_nargs_x3f_2109_ = lean_ctor_get(v_x_2105_, 1);
v___x_2110_ = l_Lean_Expr_hash(v_expr_2108_);
if (lean_obj_tag(v_nargs_x3f_2109_) == 0)
{
uint64_t v___x_2118_; 
v___x_2118_ = 11ULL;
v___y_2112_ = v___x_2118_;
goto v___jp_2111_;
}
else
{
lean_object* v_val_2119_; uint64_t v___x_2120_; uint64_t v___x_2121_; uint64_t v___x_2122_; 
v_val_2119_ = lean_ctor_get(v_nargs_x3f_2109_, 0);
v___x_2120_ = lean_uint64_of_nat(v_val_2119_);
v___x_2121_ = 13ULL;
v___x_2122_ = lean_uint64_mix_hash(v___x_2120_, v___x_2121_);
v___y_2112_ = v___x_2122_;
goto v___jp_2111_;
}
v___jp_2111_:
{
uint64_t v___x_2113_; uint64_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2113_ = lean_uint64_mix_hash(v___x_2110_, v___y_2112_);
v___x_2114_ = lean_uint64_mix_hash(v_configKey_2107_, v___x_2113_);
v___x_2115_ = lean_uint64_to_usize(v___x_2114_);
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2104_, v___x_2115_, v___x_2116_, v_x_2105_, v_x_2106_);
return v___x_2117_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 0)
{
uint8_t v___x_2124_; 
v___x_2124_ = 0;
return v___x_2124_;
}
else
{
lean_object* v_head_2125_; lean_object* v_tail_2126_; uint8_t v___x_2127_; 
v_head_2125_ = lean_ctor_get(v_x_2123_, 0);
v_tail_2126_ = lean_ctor_get(v_x_2123_, 1);
v___x_2127_ = l_Lean_Level_hasMVar(v_head_2125_);
if (v___x_2127_ == 0)
{
v_x_2123_ = v_tail_2126_;
goto _start;
}
else
{
return v___x_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_2129_){
_start:
{
uint8_t v_res_2130_; lean_object* v_r_2131_; 
v_res_2130_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_2129_);
lean_dec(v_x_2129_);
v_r_2131_ = lean_box(v_res_2130_);
return v_r_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_2133_, lean_object* v_maxArgs_x3f_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; 
lean_inc(v_maxArgs_x3f_2134_);
lean_inc_ref(v_fn_2133_);
v___x_2140_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_2133_, v_maxArgs_x3f_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2205_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2205_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2205_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_finfo_2146_; lean_object* v___y_2147_; lean_object* v___x_2179_; lean_object* v_cache_2180_; lean_object* v_funInfo_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_st_ref_get(v_a_2136_);
v_cache_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc_ref(v_cache_2180_);
lean_dec(v___x_2179_);
v_funInfo_2181_ = lean_ctor_get(v_cache_2180_, 1);
lean_inc_ref(v_funInfo_2181_);
lean_dec_ref(v_cache_2180_);
v___x_2182_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_2181_, v_a_2141_);
lean_dec_ref(v_funInfo_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v___f_2183_; lean_object* v___f_2184_; 
v___f_2183_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_2134_);
lean_inc_ref(v_fn_2133_);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2184_, 0, v_fn_2133_);
lean_closure_set(v___f_2184_, 1, v_maxArgs_x3f_2134_);
lean_closure_set(v___f_2184_, 2, v___f_2183_);
if (lean_obj_tag(v_fn_2133_) == 4)
{
lean_object* v_declName_2185_; lean_object* v_us_2186_; uint8_t v___x_2187_; 
v_declName_2185_ = lean_ctor_get(v_fn_2133_, 0);
v_us_2186_ = lean_ctor_get(v_fn_2133_, 1);
v___x_2187_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_inc(v_us_2186_);
lean_inc_n(v_declName_2185_, 2);
lean_dec_ref(v_fn_2133_);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_2189_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_2190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2190_, 0, v_declName_2185_);
lean_ctor_set(v___x_2190_, 1, v_us_2186_);
lean_ctor_set(v___x_2190_, 2, v_maxArgs_x3f_2134_);
v___x_2191_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_2188_, v___x_2189_, v_declName_2185_, v___x_2190_, v___f_2184_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v___x_2191_);
v_finfo_2146_ = v_a_2192_;
v___y_2147_ = v_a_2136_;
goto v___jp_2145_;
}
else
{
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
return v___x_2191_;
}
}
else
{
lean_object* v___x_2193_; 
lean_dec_ref(v___f_2184_);
lean_inc(v_a_2138_);
lean_inc_ref(v_a_2137_);
lean_inc(v_a_2136_);
lean_inc_ref(v_a_2135_);
v___x_2193_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_2133_, v_maxArgs_x3f_2134_, v___f_2183_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v_finfo_2146_ = v_a_2194_;
v___y_2147_ = v_a_2136_;
goto v___jp_2145_;
}
else
{
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
return v___x_2193_;
}
}
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v___f_2184_);
lean_inc(v_a_2138_);
lean_inc_ref(v_a_2137_);
lean_inc(v_a_2136_);
lean_inc_ref(v_a_2135_);
v___x_2195_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_2133_, v_maxArgs_x3f_2134_, v___f_2183_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v_finfo_2146_ = v_a_2196_;
v___y_2147_ = v_a_2136_;
goto v___jp_2145_;
}
else
{
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
return v___x_2195_;
}
}
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
lean_dec(v_maxArgs_x3f_2134_);
lean_dec_ref(v_fn_2133_);
v_val_2197_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2182_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v___x_2182_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_val_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
v___jp_2145_:
{
lean_object* v___x_2148_; lean_object* v_cache_2149_; lean_object* v_mctx_2150_; lean_object* v_zetaDeltaFVarIds_2151_; lean_object* v_postponed_2152_; lean_object* v_diag_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2178_; 
v___x_2148_ = lean_st_ref_take(v___y_2147_);
v_cache_2149_ = lean_ctor_get(v___x_2148_, 1);
v_mctx_2150_ = lean_ctor_get(v___x_2148_, 0);
v_zetaDeltaFVarIds_2151_ = lean_ctor_get(v___x_2148_, 2);
v_postponed_2152_ = lean_ctor_get(v___x_2148_, 3);
v_diag_2153_ = lean_ctor_get(v___x_2148_, 4);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2155_ = v___x_2148_;
v_isShared_2156_ = v_isSharedCheck_2178_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_diag_2153_);
lean_inc(v_postponed_2152_);
lean_inc(v_zetaDeltaFVarIds_2151_);
lean_inc(v_cache_2149_);
lean_inc(v_mctx_2150_);
lean_dec(v___x_2148_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2178_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_inferType_2157_; lean_object* v_funInfo_2158_; lean_object* v_synthInstance_2159_; lean_object* v_whnf_2160_; lean_object* v_defEqTrans_2161_; lean_object* v_defEqPerm_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2177_; 
v_inferType_2157_ = lean_ctor_get(v_cache_2149_, 0);
v_funInfo_2158_ = lean_ctor_get(v_cache_2149_, 1);
v_synthInstance_2159_ = lean_ctor_get(v_cache_2149_, 2);
v_whnf_2160_ = lean_ctor_get(v_cache_2149_, 3);
v_defEqTrans_2161_ = lean_ctor_get(v_cache_2149_, 4);
v_defEqPerm_2162_ = lean_ctor_get(v_cache_2149_, 5);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_cache_2149_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2164_ = v_cache_2149_;
v_isShared_2165_ = v_isSharedCheck_2177_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_defEqPerm_2162_);
lean_inc(v_defEqTrans_2161_);
lean_inc(v_whnf_2160_);
lean_inc(v_synthInstance_2159_);
lean_inc(v_funInfo_2158_);
lean_inc(v_inferType_2157_);
lean_dec(v_cache_2149_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2177_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_inc_ref(v_finfo_2146_);
v___x_2166_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_2158_, v_a_2141_, v_finfo_2146_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_inferType_2157_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_synthInstance_2159_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_whnf_2160_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_defEqTrans_2161_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_defEqPerm_2162_);
v___x_2168_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2168_);
v___x_2170_ = v___x_2155_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_mctx_2150_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_zetaDeltaFVarIds_2151_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_postponed_2152_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_diag_2153_);
v___x_2170_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_st_ref_set(v___y_2147_, v___x_2170_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_finfo_2146_);
v___x_2173_ = v___x_2143_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_finfo_2146_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
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
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_maxArgs_x3f_2134_);
lean_dec_ref(v_fn_2133_);
v_a_2206_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2140_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2140_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_2214_, lean_object* v_maxArgs_x3f_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2214_, v_maxArgs_x3f_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_b_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_as_2222_, v_sz_2223_, v_i_2224_, v_b_2225_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_as_2232_, lean_object* v_sz_2233_, lean_object* v_i_2234_, lean_object* v_b_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
size_t v_sz_boxed_2241_; size_t v_i_boxed_2242_; lean_object* v_res_2243_; 
v_sz_boxed_2241_ = lean_unbox_usize(v_sz_2233_);
lean_dec(v_sz_2233_);
v_i_boxed_2242_ = lean_unbox_usize(v_i_2234_);
lean_dec(v_i_2234_);
v_res_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_as_2232_, v_sz_boxed_2241_, v_i_boxed_2242_, v_b_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_as_2232_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2244_, lean_object* v_val_2245_, lean_object* v___x_2246_, lean_object* v_fvars_2247_, uint8_t v___y_2248_, lean_object* v___x_2249_, lean_object* v_inst_2250_, lean_object* v_R_2251_, lean_object* v_a_2252_, lean_object* v_b_2253_, lean_object* v_c_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2244_, v_val_2245_, v___x_2246_, v_fvars_2247_, v___y_2248_, v___x_2249_, v_a_2252_, v_b_2253_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2261_, lean_object* v_val_2262_, lean_object* v___x_2263_, lean_object* v_fvars_2264_, lean_object* v___y_2265_, lean_object* v___x_2266_, lean_object* v_inst_2267_, lean_object* v_R_2268_, lean_object* v_a_2269_, lean_object* v_b_2270_, lean_object* v_c_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v___y_16587__boxed_2277_; lean_object* v_res_2278_; 
v___y_16587__boxed_2277_ = lean_unbox(v___y_2265_);
v_res_2278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2261_, v_val_2262_, v___x_2263_, v_fvars_2264_, v___y_16587__boxed_2277_, v___x_2266_, v_inst_2267_, v_R_2268_, v_a_2269_, v_b_2270_, v_c_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___x_2266_);
lean_dec_ref(v_fvars_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v_val_2262_);
lean_dec(v_upperBound_2261_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2279_, lean_object* v_fvars_2280_, lean_object* v_inst_2281_, lean_object* v_R_2282_, lean_object* v_a_2283_, lean_object* v_b_2284_, lean_object* v_c_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2279_, v_fvars_2280_, v_a_2283_, v_b_2284_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2292_, lean_object* v_fvars_2293_, lean_object* v_inst_2294_, lean_object* v_R_2295_, lean_object* v_a_2296_, lean_object* v_b_2297_, lean_object* v_c_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2292_, v_fvars_2293_, v_inst_2294_, v_R_2295_, v_a_2296_, v_b_2297_, v_c_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v_fvars_2293_);
lean_dec(v_upperBound_2292_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2306_, v_x_2307_, v_x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2311_, v_x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2314_, v_x_2315_, v_x_2316_);
lean_dec_ref(v_x_2316_);
lean_dec_ref(v_x_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2318_, lean_object* v_msg_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2326_, lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2326_, v_msg_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_forConst_2337_, lean_object* v_key_2338_, lean_object* v_realize_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2335_, v_inst_2336_, v_forConst_2337_, v_key_2338_, v_realize_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_forConst_2349_, lean_object* v_key_2350_, lean_object* v_realize_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2346_, v_inst_2347_, v_inst_2348_, v_forConst_2349_, v_key_2350_, v_realize_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2358_, lean_object* v_x_2359_, size_t v_x_2360_, size_t v_x_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2359_, v_x_2360_, v_x_2361_, v_x_2362_, v_x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
size_t v_x_16687__boxed_2371_; size_t v_x_16688__boxed_2372_; lean_object* v_res_2373_; 
v_x_16687__boxed_2371_ = lean_unbox_usize(v_x_2367_);
lean_dec(v_x_2367_);
v_x_16688__boxed_2372_ = lean_unbox_usize(v_x_2368_);
lean_dec(v_x_2368_);
v_res_2373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2365_, v_x_2366_, v_x_16687__boxed_2371_, v_x_16688__boxed_2372_, v_x_2369_, v_x_2370_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2374_, lean_object* v_x_2375_, size_t v_x_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2375_, v_x_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_16704__boxed_2383_; lean_object* v_res_2384_; 
v_x_16704__boxed_2383_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2384_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2379_, v_x_2380_, v_x_16704__boxed_2383_, v_x_2382_);
lean_dec_ref(v_x_2382_);
lean_dec_ref(v_x_2380_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2385_, lean_object* v_n_2386_, lean_object* v_k_2387_, lean_object* v_v_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2386_, v_k_2387_, v_v_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2390_, size_t v_depth_2391_, lean_object* v_keys_2392_, lean_object* v_vals_2393_, lean_object* v_heq_2394_, lean_object* v_i_2395_, lean_object* v_entries_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2391_, v_keys_2392_, v_vals_2393_, v_i_2395_, v_entries_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_depth_2399_, lean_object* v_keys_2400_, lean_object* v_vals_2401_, lean_object* v_heq_2402_, lean_object* v_i_2403_, lean_object* v_entries_2404_){
_start:
{
size_t v_depth_boxed_2405_; lean_object* v_res_2406_; 
v_depth_boxed_2405_ = lean_unbox_usize(v_depth_2399_);
lean_dec(v_depth_2399_);
v_res_2406_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2398_, v_depth_boxed_2405_, v_keys_2400_, v_vals_2401_, v_heq_2402_, v_i_2403_, v_entries_2404_);
lean_dec_ref(v_vals_2401_);
lean_dec_ref(v_keys_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2407_, lean_object* v_keys_2408_, lean_object* v_vals_2409_, lean_object* v_heq_2410_, lean_object* v_i_2411_, lean_object* v_k_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2408_, v_vals_2409_, v_i_2411_, v_k_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2414_, lean_object* v_keys_2415_, lean_object* v_vals_2416_, lean_object* v_heq_2417_, lean_object* v_i_2418_, lean_object* v_k_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2414_, v_keys_2415_, v_vals_2416_, v_heq_2417_, v_i_2418_, v_k_2419_);
lean_dec_ref(v_k_2419_);
lean_dec_ref(v_vals_2416_);
lean_dec_ref(v_keys_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2422_, v_x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2425_, v_x_2426_, v_x_2427_);
lean_dec_ref(v_x_2427_);
lean_dec_ref(v_x_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2430_, v_x_2431_, v_x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2434_, lean_object* v_m_2435_, lean_object* v_a_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2435_, v_a_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2438_, lean_object* v_m_2439_, lean_object* v_a_2440_){
_start:
{
uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_res_2441_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2438_, v_m_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_m_2439_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2444_, v_x_2445_, v_x_2446_, v_x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2449_, lean_object* v_x_2450_, size_t v_x_2451_, lean_object* v_x_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2450_, v_x_2451_, v_x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_){
_start:
{
size_t v_x_16749__boxed_2458_; lean_object* v_res_2459_; 
v_x_16749__boxed_2458_ = lean_unbox_usize(v_x_2456_);
lean_dec(v_x_2456_);
v_res_2459_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2454_, v_x_2455_, v_x_16749__boxed_2458_, v_x_2457_);
lean_dec_ref(v_x_2457_);
lean_dec_ref(v_x_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2460_, lean_object* v_x_2461_, size_t v_x_2462_, size_t v_x_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2461_, v_x_2462_, v_x_2463_, v_x_2464_, v_x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
size_t v_x_16760__boxed_2473_; size_t v_x_16761__boxed_2474_; lean_object* v_res_2475_; 
v_x_16760__boxed_2473_ = lean_unbox_usize(v_x_2469_);
lean_dec(v_x_2469_);
v_x_16761__boxed_2474_ = lean_unbox_usize(v_x_2470_);
lean_dec(v_x_2470_);
v_res_2475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2467_, v_x_2468_, v_x_16760__boxed_2473_, v_x_16761__boxed_2474_, v_x_2471_, v_x_2472_);
return v_res_2475_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2476_, lean_object* v_a_2477_, lean_object* v_x_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2477_, v_x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2480_, lean_object* v_a_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2480_, v_a_2481_, v_x_2482_);
lean_dec(v_x_2482_);
lean_dec(v_a_2481_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2485_, lean_object* v_keys_2486_, lean_object* v_vals_2487_, lean_object* v_heq_2488_, lean_object* v_i_2489_, lean_object* v_k_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2486_, v_vals_2487_, v_i_2489_, v_k_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2492_, lean_object* v_keys_2493_, lean_object* v_vals_2494_, lean_object* v_heq_2495_, lean_object* v_i_2496_, lean_object* v_k_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2492_, v_keys_2493_, v_vals_2494_, v_heq_2495_, v_i_2496_, v_k_2497_);
lean_dec_ref(v_k_2497_);
lean_dec_ref(v_vals_2494_);
lean_dec_ref(v_keys_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2499_, lean_object* v_n_2500_, lean_object* v_k_2501_, lean_object* v_v_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2500_, v_k_2501_, v_v_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2504_, size_t v_depth_2505_, lean_object* v_keys_2506_, lean_object* v_vals_2507_, lean_object* v_heq_2508_, lean_object* v_i_2509_, lean_object* v_entries_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2505_, v_keys_2506_, v_vals_2507_, v_i_2509_, v_entries_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2512_, lean_object* v_depth_2513_, lean_object* v_keys_2514_, lean_object* v_vals_2515_, lean_object* v_heq_2516_, lean_object* v_i_2517_, lean_object* v_entries_2518_){
_start:
{
size_t v_depth_boxed_2519_; lean_object* v_res_2520_; 
v_depth_boxed_2519_ = lean_unbox_usize(v_depth_2513_);
lean_dec(v_depth_2513_);
v_res_2520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2512_, v_depth_boxed_2519_, v_keys_2514_, v_vals_2515_, v_heq_2516_, v_i_2517_, v_entries_2518_);
lean_dec_ref(v_vals_2515_);
lean_dec_ref(v_keys_2514_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2522_, v_x_2523_, v_x_2524_, v_x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2527_, lean_object* v_maxArgs_x3f_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2527_, v_maxArgs_x3f_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2535_, lean_object* v_maxArgs_x3f_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_getFunInfo(v_fn_2535_, v_maxArgs_x3f_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2543_, lean_object* v_nargs_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_nargs_2544_);
v___x_2551_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2543_, v___x_2550_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2552_, lean_object* v_nargs_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2552_, v_nargs_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2560_){
_start:
{
lean_object* v_paramInfo_2561_; lean_object* v___x_2562_; 
v_paramInfo_2561_ = lean_ctor_get(v_info_2560_, 0);
v___x_2562_ = lean_array_get_size(v_paramInfo_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Meta_FunInfo_getArity(v_info_2563_);
lean_dec_ref(v_info_2563_);
return v_res_2564_;
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
