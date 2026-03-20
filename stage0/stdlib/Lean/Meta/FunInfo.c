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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_Level_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Meta_instBEqInfoCacheKey_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_instHashableInfoCacheKey___private__1(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_instBEqInfoCacheKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0;
static lean_once_cell_t l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "trying to realize `"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__0 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__0_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "` value but `enableRealizationsForConst` must be called for '"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__1 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__1_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' first"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__2 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__2_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Environment.realizeConst: `realizedImportedConsts` is empty"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__3 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__3_value;
static const lean_ctor_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__3_value)}};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__4 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Meta.Basic"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.realizeValue"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
if (lean_obj_tag(v___x_170_) == 0)
{
if (lean_obj_tag(v_fn_118_) == 4)
{
lean_object* v_declName_171_; lean_object* v_us_172_; lean_object* v___f_173_; uint8_t v___x_174_; 
v_declName_171_ = lean_ctor_get(v_fn_118_, 0);
lean_inc(v_declName_171_);
v_us_172_ = lean_ctor_get(v_fn_118_, 1);
lean_inc(v_us_172_);
lean_dec_ref(v_fn_118_);
v___f_173_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
lean_inc(v_us_172_);
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
lean_inc(v_a_122_);
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
lean_dec(v_a_122_);
return v___x_180_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_us_172_);
lean_dec(v_declName_171_);
lean_dec(v_maxArgs_x3f_119_);
lean_inc(v_a_122_);
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
lean_dec(v_a_122_);
return v___x_182_;
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v_maxArgs_x3f_119_);
lean_dec_ref(v_fn_118_);
lean_inc(v_a_122_);
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
lean_dec(v_a_122_);
return v___x_184_;
}
}
}
else
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_del_object(v___x_129_);
lean_dec(v_a_127_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
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
lean_dec(v___y_138_);
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
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
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
lean_dec_ref(v___x_330_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_as_339_, lean_object* v_lo_340_, lean_object* v_hi_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_nat_dec_lt(v_lo_340_, v_hi_341_);
if (v___x_342_ == 0)
{
lean_dec(v_lo_340_);
return v_as_339_;
}
else
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; uint8_t v___x_347_; 
v___f_343_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___closed__0));
lean_inc(v_lo_340_);
v___x_344_ = l_Array_qpartition___redArg(v_as_339_, v___f_343_, v_lo_340_, v_hi_341_);
v_fst_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_snd_346_);
lean_dec_ref(v___x_344_);
v___x_347_ = lean_nat_dec_le(v_hi_341_, v_fst_345_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_snd_346_, v_lo_340_, v_fst_345_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_fst_345_, v___x_349_);
lean_dec(v_fst_345_);
v_as_339_ = v___x_348_;
v_lo_340_ = v___x_350_;
goto _start;
}
else
{
lean_dec(v_fst_345_);
lean_dec(v_lo_340_);
return v_snd_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_as_352_, lean_object* v_lo_353_, lean_object* v_hi_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_as_352_, v_lo_353_, v_hi_354_);
lean_dec(v_hi_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_358_, lean_object* v_e_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_deps_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0));
v_deps_362_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_358_, v_e_359_, v___x_361_);
v___x_363_ = lean_array_get_size(v_deps_362_);
v___x_364_ = lean_nat_dec_eq(v___x_363_, v___x_360_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___y_368_; uint8_t v___x_372_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_sub(v___x_363_, v___x_365_);
v___x_372_ = lean_nat_dec_le(v___x_360_, v___x_366_);
if (v___x_372_ == 0)
{
lean_inc(v___x_366_);
v___y_368_ = v___x_366_;
goto v___jp_367_;
}
else
{
v___y_368_ = v___x_360_;
goto v___jp_367_;
}
v___jp_367_:
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_le(v___y_368_, v___x_366_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v___x_366_);
lean_inc(v___y_368_);
v___x_370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_deps_362_, v___y_368_, v___y_368_);
lean_dec(v___y_368_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_deps_362_, v___y_368_, v___x_366_);
lean_dec(v___x_366_);
return v___x_371_;
}
}
}
else
{
return v_deps_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_373_, lean_object* v_e_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_373_, v_e_374_);
lean_dec_ref(v_e_374_);
lean_dec_ref(v_fvars_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_376_, lean_object* v_as_377_, lean_object* v_lo_378_, lean_object* v_hi_379_, lean_object* v_w_380_, lean_object* v_hlo_381_, lean_object* v_hhi_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_as_377_, v_lo_378_, v_hi_379_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_384_, lean_object* v_as_385_, lean_object* v_lo_386_, lean_object* v_hi_387_, lean_object* v_w_388_, lean_object* v_hlo_389_, lean_object* v_hhi_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_384_, v_as_385_, v_lo_386_, v_hi_387_, v_w_388_, v_hlo_389_, v_hhi_390_);
lean_dec(v_hi_387_);
lean_dec(v_n_384_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_392_, lean_object* v_as_393_, lean_object* v_i_394_, lean_object* v_j_395_, lean_object* v_bs_396_){
_start:
{
lean_object* v_zero_397_; uint8_t v_isZero_398_; 
v_zero_397_ = lean_unsigned_to_nat(0u);
v_isZero_398_ = lean_nat_dec_eq(v_i_394_, v_zero_397_);
if (v_isZero_398_ == 1)
{
lean_dec(v_j_395_);
lean_dec(v_i_394_);
return v_bs_396_;
}
else
{
lean_object* v___x_399_; uint8_t v_binderInfo_400_; uint8_t v_hasFwdDeps_401_; lean_object* v_backDeps_402_; uint8_t v_isProp_403_; uint8_t v_isDecInst_404_; uint8_t v_isInstance_405_; uint8_t v_higherOrderOutParam_406_; uint8_t v_dependsOnHigherOrderOutParam_407_; lean_object* v_one_408_; lean_object* v_n_409_; lean_object* v___y_411_; 
v___x_399_ = lean_array_fget(v_as_393_, v_j_395_);
v_binderInfo_400_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1);
v_hasFwdDeps_401_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 1);
v_backDeps_402_ = lean_ctor_get(v___x_399_, 0);
v_isProp_403_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 2);
v_isDecInst_404_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 3);
v_isInstance_405_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_406_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_407_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*1 + 6);
v_one_408_ = lean_unsigned_to_nat(1u);
v_n_409_ = lean_nat_sub(v_i_394_, v_one_408_);
lean_dec(v_i_394_);
if (v_hasFwdDeps_401_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_392_, v_j_395_);
if (v___x_415_ == 0)
{
v___y_411_ = v___x_399_;
goto v___jp_410_;
}
else
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_inc_ref(v_backDeps_402_);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_423_);
v___x_417_ = v___x_399_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_dec(v___x_399_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_backDeps_402_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1, v_binderInfo_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1 + 2, v_isProp_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1 + 3, v_isDecInst_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1 + 4, v_isInstance_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1 + 5, v_higherOrderOutParam_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_421_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_407_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1 + 1, v___x_415_);
v___y_411_ = v___x_420_;
goto v___jp_410_;
}
}
}
}
else
{
v___y_411_ = v___x_399_;
goto v___jp_410_;
}
v___jp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_nat_add(v_j_395_, v_one_408_);
lean_dec(v_j_395_);
v___x_413_ = lean_array_push(v_bs_396_, v___y_411_);
v_i_394_ = v_n_409_;
v_j_395_ = v___x_412_;
v_bs_396_ = v___x_413_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_424_, lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_j_427_, lean_object* v_bs_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_424_, v_as_425_, v_i_426_, v_j_427_, v_bs_428_);
lean_dec_ref(v_as_425_);
lean_dec_ref(v_backDeps_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_430_, lean_object* v_backDeps_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_array_get_size(v_backDeps_431_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_dec_eq(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_array_get_size(v_pinfo_430_);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_431_, v_pinfo_430_, v___x_435_, v___x_433_, v___x_436_);
return v___x_437_;
}
else
{
lean_inc_ref(v_pinfo_430_);
return v_pinfo_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_438_, lean_object* v_backDeps_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_438_, v_backDeps_439_);
lean_dec_ref(v_backDeps_439_);
lean_dec_ref(v_pinfo_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_441_, lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_j_444_, lean_object* v_inv_445_, lean_object* v_bs_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_441_, v_as_442_, v_i_443_, v_j_444_, v_bs_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_448_, lean_object* v_as_449_, lean_object* v_i_450_, lean_object* v_j_451_, lean_object* v_inv_452_, lean_object* v_bs_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_448_, v_as_449_, v_i_450_, v_j_451_, v_inv_452_, v_bs_453_);
lean_dec_ref(v_as_449_);
lean_dec_ref(v_backDeps_448_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_455_, lean_object* v_b_456_, lean_object* v_c_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_apply_7(v_k_455_, v_b_456_, v_c_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, lean_box(0));
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_464_, lean_object* v_b_465_, lean_object* v_c_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_464_, v_b_465_, v_c_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_473_, lean_object* v_k_474_, uint8_t v_cleanupAnnotations_475_, uint8_t v_whnfType_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___f_482_; lean_object* v___x_483_; 
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_482_, 0, v_k_474_);
v___x_483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_473_, v___f_482_, v_cleanupAnnotations_475_, v_whnfType_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_483_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_483_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_500_, lean_object* v_k_501_, lean_object* v_cleanupAnnotations_502_, lean_object* v_whnfType_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_509_; uint8_t v_whnfType_boxed_510_; lean_object* v_res_511_; 
v_cleanupAnnotations_boxed_509_ = lean_unbox(v_cleanupAnnotations_502_);
v_whnfType_boxed_510_ = lean_unbox(v_whnfType_503_);
v_res_511_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_500_, v_k_501_, v_cleanupAnnotations_boxed_509_, v_whnfType_boxed_510_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_512_, lean_object* v_type_513_, lean_object* v_k_514_, uint8_t v_cleanupAnnotations_515_, uint8_t v_whnfType_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_513_, v_k_514_, v_cleanupAnnotations_515_, v_whnfType_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_523_, lean_object* v_type_524_, lean_object* v_k_525_, lean_object* v_cleanupAnnotations_526_, lean_object* v_whnfType_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_533_; uint8_t v_whnfType_boxed_534_; lean_object* v_res_535_; 
v_cleanupAnnotations_boxed_533_ = lean_unbox(v_cleanupAnnotations_526_);
v_whnfType_boxed_534_ = lean_unbox(v_whnfType_527_);
v_res_535_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_523_, v_type_524_, v_k_525_, v_cleanupAnnotations_boxed_533_, v_whnfType_boxed_534_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___f_543_; lean_object* v___x_10364__overap_544_; lean_object* v___x_545_; 
v___f_543_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_10364__overap_544_ = lean_panic_fn(v___f_543_, v_msg_537_);
v___x_545_ = lean_apply_5(v___x_10364__overap_544_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_553_, lean_object* v_maxFVars_x3f_554_, lean_object* v_k_555_, uint8_t v_cleanupAnnotations_556_, uint8_t v_whnfType_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___f_563_; lean_object* v___x_564_; 
v___f_563_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_563_, 0, v_k_555_);
v___x_564_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_553_, v_maxFVars_x3f_554_, v___f_563_, v_cleanupAnnotations_556_, v_whnfType_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_581_, lean_object* v_maxFVars_x3f_582_, lean_object* v_k_583_, lean_object* v_cleanupAnnotations_584_, lean_object* v_whnfType_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_591_; uint8_t v_whnfType_boxed_592_; lean_object* v_res_593_; 
v_cleanupAnnotations_boxed_591_ = lean_unbox(v_cleanupAnnotations_584_);
v_whnfType_boxed_592_ = lean_unbox(v_whnfType_585_);
v_res_593_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_581_, v_maxFVars_x3f_582_, v_k_583_, v_cleanupAnnotations_boxed_591_, v_whnfType_boxed_592_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_594_, lean_object* v_type_595_, lean_object* v_maxFVars_x3f_596_, lean_object* v_k_597_, uint8_t v_cleanupAnnotations_598_, uint8_t v_whnfType_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_595_, v_maxFVars_x3f_596_, v_k_597_, v_cleanupAnnotations_598_, v_whnfType_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_606_, lean_object* v_type_607_, lean_object* v_maxFVars_x3f_608_, lean_object* v_k_609_, lean_object* v_cleanupAnnotations_610_, lean_object* v_whnfType_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_617_; uint8_t v_whnfType_boxed_618_; lean_object* v_res_619_; 
v_cleanupAnnotations_boxed_617_ = lean_unbox(v_cleanupAnnotations_610_);
v_whnfType_boxed_618_ = lean_unbox(v_whnfType_611_);
v_res_619_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_606_, v_type_607_, v_maxFVars_x3f_608_, v_k_609_, v_cleanupAnnotations_boxed_617_, v_whnfType_boxed_618_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_620_, lean_object* v_val_621_, lean_object* v___x_622_, lean_object* v_fvars_623_, uint8_t v___y_624_, lean_object* v_a_625_, lean_object* v_b_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_a_633_; uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_lt(v_a_625_, v_upperBound_620_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_a_625_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_626_);
return v___x_638_;
}
else
{
lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_703_; 
v_fst_639_ = lean_ctor_get(v_b_626_, 0);
v_snd_640_ = lean_ctor_get(v_b_626_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_626_);
if (v_isSharedCheck_703_ == 0)
{
v___x_642_ = v_b_626_;
v_isShared_643_ = v_isSharedCheck_703_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_inc(v_fst_639_);
lean_dec(v_b_626_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_703_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_621_, v_a_625_);
if (v___x_644_ == 0)
{
lean_object* v___x_646_; 
if (v_isShared_643_ == 0)
{
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_640_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v_a_633_ = v___x_646_;
goto v___jp_632_;
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_array_fget_borrowed(v___x_622_, v_a_625_);
v___x_649_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_623_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___x_651_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v___x_649_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___x_648_);
v___x_651_ = lean_infer_type(v___x_648_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
v___x_653_ = lean_whnf(v_a_652_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___y_656_; uint8_t v___x_662_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v___x_662_ = l_Lean_Expr_isForall(v_a_654_);
lean_dec(v_a_654_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_val_650_);
lean_del_object(v___x_642_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_fst_639_);
lean_ctor_set(v___x_663_, 1, v_snd_640_);
v_a_633_ = v___x_663_;
goto v___jp_632_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_array_get_size(v_fst_639_);
v___x_665_ = lean_nat_dec_lt(v_val_650_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_val_650_);
v___y_656_ = v_fst_639_;
goto v___jp_655_;
}
else
{
lean_object* v_v_666_; uint8_t v_binderInfo_667_; uint8_t v_hasFwdDeps_668_; lean_object* v_backDeps_669_; uint8_t v_isProp_670_; uint8_t v_isDecInst_671_; uint8_t v_isInstance_672_; uint8_t v_dependsOnHigherOrderOutParam_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_683_; 
v_v_666_ = lean_array_fget(v_fst_639_, v_val_650_);
v_binderInfo_667_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1);
v_hasFwdDeps_668_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1 + 1);
v_backDeps_669_ = lean_ctor_get(v_v_666_, 0);
v_isProp_670_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1 + 2);
v_isDecInst_671_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1 + 3);
v_isInstance_672_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_673_ = lean_ctor_get_uint8(v_v_666_, sizeof(void*)*1 + 6);
v_isSharedCheck_683_ = !lean_is_exclusive(v_v_666_);
if (v_isSharedCheck_683_ == 0)
{
v___x_675_ = v_v_666_;
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_backDeps_669_);
lean_dec(v_v_666_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v_xs_x27_678_; lean_object* v___x_680_; 
v___x_677_ = lean_box(0);
v_xs_x27_678_ = lean_array_fset(v_fst_639_, v_val_650_, v___x_677_);
if (v_isShared_676_ == 0)
{
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_backDeps_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1, v_binderInfo_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1 + 1, v_hasFwdDeps_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1 + 2, v_isProp_670_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1 + 3, v_isDecInst_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1 + 4, v_isInstance_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_673_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1 + 5, v___y_624_);
v___x_681_ = lean_array_fset(v_xs_x27_678_, v_val_650_, v___x_680_);
lean_dec(v_val_650_);
v___y_656_ = v___x_681_;
goto v___jp_655_;
}
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_657_ = l_Lean_Expr_fvarId_x21(v___x_648_);
v___x_658_ = l_Lean_FVarIdSet_insert(v_snd_640_, v___x_657_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_658_);
lean_ctor_set(v___x_642_, 0, v___y_656_);
v___x_660_ = v___x_642_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___y_656_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_633_ = v___x_660_;
goto v___jp_632_;
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_val_650_);
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
lean_dec(v_fst_639_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_a_625_);
v_a_684_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_653_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_653_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_val_650_);
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
lean_dec(v_fst_639_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_a_625_);
v_a_692_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_651_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_651_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_701_; 
lean_dec(v___x_649_);
if (v_isShared_643_ == 0)
{
v___x_701_ = v___x_642_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_640_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_a_633_ = v___x_701_;
goto v___jp_632_;
}
}
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_a_625_, v___x_634_);
lean_dec(v_a_625_);
v_a_625_ = v___x_635_;
v_b_626_ = v_a_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_704_, lean_object* v_val_705_, lean_object* v___x_706_, lean_object* v_fvars_707_, lean_object* v___y_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___y_12800__boxed_716_; lean_object* v_res_717_; 
v___y_12800__boxed_716_ = lean_unbox(v___y_708_);
v_res_717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_704_, v_val_705_, v___x_706_, v_fvars_707_, v___y_12800__boxed_716_, v_a_709_, v_b_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec_ref(v_fvars_707_);
lean_dec_ref(v___x_706_);
lean_dec_ref(v_val_705_);
lean_dec(v_upperBound_704_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_721_, lean_object* v_type_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_729_ = l_Lean_Expr_isAppOf(v_type_722_, v___x_728_);
v___x_730_ = lean_box(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_732_, lean_object* v_type_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_732_, v_type_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v_type_733_);
lean_dec_ref(v_x_732_);
return v_res_739_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_k_740_, lean_object* v_t_741_){
_start:
{
if (lean_obj_tag(v_t_741_) == 0)
{
lean_object* v_k_742_; lean_object* v_l_743_; lean_object* v_r_744_; uint8_t v___x_745_; 
v_k_742_ = lean_ctor_get(v_t_741_, 1);
v_l_743_ = lean_ctor_get(v_t_741_, 3);
v_r_744_ = lean_ctor_get(v_t_741_, 4);
v___x_745_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_740_, v_k_742_);
switch(v___x_745_)
{
case 0:
{
v_t_741_ = v_l_743_;
goto _start;
}
case 1:
{
uint8_t v___x_747_; 
v___x_747_ = 1;
return v___x_747_;
}
default: 
{
v_t_741_ = v_r_744_;
goto _start;
}
}
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_k_750_, lean_object* v_t_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_750_, v_t_751_);
lean_dec(v_t_751_);
lean_dec(v_k_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object* v_snd_754_, lean_object* v_e_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = l_Lean_Expr_isFVar(v_e_755_);
if (v___x_756_ == 0)
{
return v___x_756_;
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = l_Lean_Expr_fvarId_x21(v_e_755_);
v___x_758_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_757_, v_snd_754_);
lean_dec(v___x_757_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object* v_snd_759_, lean_object* v_e_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_759_, v_e_760_);
lean_dec_ref(v_e_760_);
lean_dec(v_snd_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_764_; lean_object* v_dummy_765_; 
v___x_764_ = lean_box(0);
v_dummy_765_ = l_Lean_Expr_sort___override(v___x_764_);
return v_dummy_765_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_770_ = lean_unsigned_to_nat(47u);
v___x_771_ = lean_unsigned_to_nat(121u);
v___x_772_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_774_ = l_mkPanicMessageWithDecl(v___x_773_, v___x_772_, v___x_771_, v___x_770_, v___x_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_775_, lean_object* v_fvars_776_, lean_object* v_a_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_a_785_; uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_lt(v_a_777_, v_upperBound_775_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_b_778_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_array_fget_borrowed(v_fvars_776_, v_a_777_);
lean_inc_ref(v___y_779_);
v___x_792_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_791_, v___y_779_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_904_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_792_);
v_fst_794_ = lean_ctor_get(v_b_778_, 0);
v_snd_795_ = lean_ctor_get(v_b_778_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_b_778_);
if (v_isSharedCheck_904_ == 0)
{
v___x_797_ = v_b_778_;
v_isShared_798_ = v_isSharedCheck_904_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_inc(v_fst_794_);
lean_dec(v_b_778_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_904_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___y_803_; lean_object* v___y_804_; uint8_t v___y_805_; uint8_t v___y_885_; 
v___f_799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
v___x_800_ = l_Lean_LocalDecl_type(v_a_793_);
v___x_801_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_776_, v___x_800_);
if (lean_obj_tag(v_snd_795_) == 0)
{
lean_object* v___f_900_; lean_object* v___x_901_; 
lean_inc_ref(v_snd_795_);
v___f_900_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_900_, 0, v_snd_795_);
v___x_901_ = lean_find_expr(v___f_900_, v___x_800_);
lean_dec_ref(v___f_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
uint8_t v___x_902_; 
v___x_902_ = 0;
v___y_885_ = v___x_902_;
goto v___jp_884_;
}
else
{
lean_dec_ref(v___x_901_);
v___y_885_ = v___x_789_;
goto v___jp_884_;
}
}
else
{
uint8_t v___x_903_; 
v___x_903_ = 0;
v___y_885_ = v___x_903_;
goto v___jp_884_;
}
v___jp_802_:
{
lean_object* v___x_806_; 
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc_ref(v___x_800_);
v___x_806_ = l_Lean_Meta_isProp(v___x_800_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; lean_object* v___x_809_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v___x_808_ = 0;
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc_ref(v___x_800_);
v___x_809_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_800_, v___f_799_, v___x_808_, v___x_808_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___x_809_);
v___x_811_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_794_, v___x_801_);
lean_dec(v_fst_794_);
v___x_812_ = l_Lean_LocalDecl_binderInfo(v_a_793_);
lean_dec(v_a_793_);
v___x_813_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_813_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1, v___x_812_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 1, v___x_808_);
v___x_814_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 2, v___x_814_);
v___x_815_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 3, v___x_815_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 4, v___y_805_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 5, v___x_808_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1 + 6, v___y_803_);
v___x_816_ = lean_array_push(v___x_811_, v___x_813_);
if (v___y_805_ == 0)
{
lean_object* v___x_818_; 
lean_dec(v___y_804_);
lean_dec_ref(v___x_800_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_818_ = v___x_797_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_snd_795_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_785_ = v___x_818_;
goto v___jp_784_;
}
}
else
{
if (lean_obj_tag(v___y_804_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_821_; lean_object* v_env_822_; lean_object* v___x_823_; 
v_val_820_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v___y_804_);
v___x_821_ = lean_st_ref_get(v___y_782_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = l_Lean_getOutParamPositions_x3f(v_env_822_, v_val_820_);
lean_dec(v_val_820_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_824_);
lean_dec_ref(v___x_823_);
v___x_825_ = lean_array_get_size(v_val_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v_dummy_828_; lean_object* v_nargs_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v_dummy_828_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_829_ = l_Lean_Expr_getAppNumArgs(v___x_800_);
lean_inc(v_nargs_829_);
v___x_830_ = lean_mk_array(v_nargs_829_, v_dummy_828_);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_sub(v_nargs_829_, v___x_831_);
lean_dec(v_nargs_829_);
v___x_833_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_800_, v___x_830_, v___x_832_);
v___x_834_ = lean_array_get_size(v___x_833_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_836_ = v___x_797_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_795_);
v___x_836_ = v_reuseFailAlloc_848_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_834_, v_val_824_, v___x_833_, v_fvars_776_, v___y_805_, v___x_826_, v___x_836_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___x_833_);
lean_dec(v_val_824_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v_fst_839_ = lean_ctor_get(v_a_838_, 0);
v_snd_840_ = lean_ctor_get(v_a_838_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v_a_838_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
lean_dec(v_a_838_);
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
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_fst_839_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_snd_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v_a_785_ = v___x_845_;
goto v___jp_784_;
}
}
}
else
{
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
return v___x_837_;
}
}
}
else
{
lean_object* v___x_850_; 
lean_dec(v_val_824_);
lean_dec_ref(v___x_800_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_850_ = v___x_797_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_snd_795_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v_a_785_ = v___x_850_;
goto v___jp_784_;
}
}
}
else
{
lean_object* v___x_853_; 
lean_dec(v___x_823_);
lean_dec_ref(v___x_800_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_853_ = v___x_797_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_snd_795_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v_a_785_ = v___x_853_;
goto v___jp_784_;
}
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___y_804_);
lean_dec_ref(v___x_800_);
v___x_855_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_856_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_855_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_858_; 
lean_dec_ref(v___x_856_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_816_);
v___x_858_ = v___x_797_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_795_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
v_a_785_ = v___x_858_;
goto v___jp_784_;
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___x_816_);
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
v_a_860_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_856_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_807_);
lean_dec(v___y_804_);
lean_dec_ref(v___x_801_);
lean_dec_ref(v___x_800_);
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_a_793_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
v_a_868_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_809_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_809_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v___y_804_);
lean_dec_ref(v___x_801_);
lean_dec_ref(v___x_800_);
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_a_793_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
v_a_876_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_806_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_806_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_886_; 
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc_ref(v___x_800_);
v___x_886_ = l_Lean_Meta_isClass_x3f(v___x_800_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_886_);
if (lean_obj_tag(v_a_887_) == 0)
{
uint8_t v___x_888_; 
v___x_888_ = 0;
v___y_803_ = v___y_885_;
v___y_804_ = v_a_887_;
v___y_805_ = v___x_888_;
goto v___jp_802_;
}
else
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = l_Lean_LocalDecl_binderInfo(v_a_793_);
v___x_890_ = l_Lean_BinderInfo_isExplicit(v___x_889_);
if (v___x_890_ == 0)
{
v___y_803_ = v___y_885_;
v___y_804_ = v_a_887_;
v___y_805_ = v___x_789_;
goto v___jp_802_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = 0;
v___y_803_ = v___y_885_;
v___y_804_ = v_a_887_;
v___y_805_ = v___x_891_;
goto v___jp_802_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___x_801_);
lean_dec_ref(v___x_800_);
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_a_793_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_777_);
v_a_892_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_886_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_886_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec_ref(v_b_778_);
lean_dec(v_a_777_);
v_a_905_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_792_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_792_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_a_777_, v___x_786_);
lean_dec(v_a_777_);
v_a_777_ = v___x_787_;
v_b_778_ = v_a_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_913_, lean_object* v_fvars_914_, lean_object* v_a_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_913_, v_fvars_914_, v_a_915_, v_b_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec_ref(v_fvars_914_);
lean_dec(v_upperBound_913_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_925_, lean_object* v_fvars_926_, lean_object* v_type_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_933_ = lean_array_get_size(v_fvars_926_);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_925_);
v___x_937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_933_, v_fvars_926_, v___x_934_, v___x_936_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_956_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_956_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_fst_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_954_; 
v_fst_942_ = lean_ctor_get(v_a_938_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_a_938_, 1);
lean_dec(v_unused_955_);
v___x_944_ = v_a_938_;
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_fst_942_);
lean_dec(v_a_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_926_, v_type_927_);
v___x_947_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_942_, v___x_946_);
lean_dec(v_fst_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_946_);
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_946_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_951_ = v___x_940_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_937_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_937_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_965_, lean_object* v_fvars_966_, lean_object* v_type_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_965_, v_fvars_966_, v_type_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec_ref(v_type_967_);
lean_dec_ref(v_fvars_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_974_, lean_object* v_maxArgs_x3f_975_, lean_object* v___f_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
v___x_982_ = lean_infer_type(v_fn_974_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; uint8_t v_transparency_985_; uint8_t v___x_986_; uint8_t v___x_987_; uint8_t v___y_989_; uint8_t v___x_1047_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = l_Lean_Meta_Context_config(v___y_977_);
v_transparency_985_ = lean_ctor_get_uint8(v___x_984_, 9);
v___x_986_ = 1;
v___x_987_ = 0;
v___x_1047_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_985_, v___x_986_);
if (v___x_1047_ == 0)
{
v___y_989_ = v_transparency_985_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___x_986_;
goto v___jp_988_;
}
v___jp_988_:
{
uint8_t v_foApprox_990_; uint8_t v_ctxApprox_991_; uint8_t v_quasiPatternApprox_992_; uint8_t v_constApprox_993_; uint8_t v_isDefEqStuckEx_994_; uint8_t v_unificationHints_995_; uint8_t v_proofIrrelevance_996_; uint8_t v_assignSyntheticOpaque_997_; uint8_t v_offsetCnstrs_998_; uint8_t v_etaStruct_999_; uint8_t v_univApprox_1000_; uint8_t v_iota_1001_; uint8_t v_beta_1002_; uint8_t v_proj_1003_; uint8_t v_zeta_1004_; uint8_t v_zetaDelta_1005_; uint8_t v_zetaUnused_1006_; uint8_t v_zetaHave_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1046_; 
v_foApprox_990_ = lean_ctor_get_uint8(v___x_984_, 0);
v_ctxApprox_991_ = lean_ctor_get_uint8(v___x_984_, 1);
v_quasiPatternApprox_992_ = lean_ctor_get_uint8(v___x_984_, 2);
v_constApprox_993_ = lean_ctor_get_uint8(v___x_984_, 3);
v_isDefEqStuckEx_994_ = lean_ctor_get_uint8(v___x_984_, 4);
v_unificationHints_995_ = lean_ctor_get_uint8(v___x_984_, 5);
v_proofIrrelevance_996_ = lean_ctor_get_uint8(v___x_984_, 6);
v_assignSyntheticOpaque_997_ = lean_ctor_get_uint8(v___x_984_, 7);
v_offsetCnstrs_998_ = lean_ctor_get_uint8(v___x_984_, 8);
v_etaStruct_999_ = lean_ctor_get_uint8(v___x_984_, 10);
v_univApprox_1000_ = lean_ctor_get_uint8(v___x_984_, 11);
v_iota_1001_ = lean_ctor_get_uint8(v___x_984_, 12);
v_beta_1002_ = lean_ctor_get_uint8(v___x_984_, 13);
v_proj_1003_ = lean_ctor_get_uint8(v___x_984_, 14);
v_zeta_1004_ = lean_ctor_get_uint8(v___x_984_, 15);
v_zetaDelta_1005_ = lean_ctor_get_uint8(v___x_984_, 16);
v_zetaUnused_1006_ = lean_ctor_get_uint8(v___x_984_, 17);
v_zetaHave_1007_ = lean_ctor_get_uint8(v___x_984_, 18);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1009_ = v___x_984_;
v_isShared_1010_ = v_isSharedCheck_1046_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_984_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1046_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v_trackZetaDelta_1011_; lean_object* v_zetaDeltaSet_1012_; lean_object* v_lctx_1013_; lean_object* v_localInstances_1014_; lean_object* v_defEqCtx_x3f_1015_; lean_object* v_synthPendingDepth_1016_; lean_object* v_canUnfold_x3f_1017_; uint8_t v_univApprox_1018_; uint8_t v_inTypeClassResolution_1019_; uint8_t v_cacheInferType_1020_; lean_object* v_config_1022_; 
v_trackZetaDelta_1011_ = lean_ctor_get_uint8(v___y_977_, sizeof(void*)*7);
v_zetaDeltaSet_1012_ = lean_ctor_get(v___y_977_, 1);
lean_inc(v_zetaDeltaSet_1012_);
v_lctx_1013_ = lean_ctor_get(v___y_977_, 2);
lean_inc_ref(v_lctx_1013_);
v_localInstances_1014_ = lean_ctor_get(v___y_977_, 3);
lean_inc_ref(v_localInstances_1014_);
v_defEqCtx_x3f_1015_ = lean_ctor_get(v___y_977_, 4);
lean_inc(v_defEqCtx_x3f_1015_);
v_synthPendingDepth_1016_ = lean_ctor_get(v___y_977_, 5);
lean_inc(v_synthPendingDepth_1016_);
v_canUnfold_x3f_1017_ = lean_ctor_get(v___y_977_, 6);
lean_inc(v_canUnfold_x3f_1017_);
v_univApprox_1018_ = lean_ctor_get_uint8(v___y_977_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1019_ = lean_ctor_get_uint8(v___y_977_, sizeof(void*)*7 + 2);
v_cacheInferType_1020_ = lean_ctor_get_uint8(v___y_977_, sizeof(void*)*7 + 3);
if (v_isShared_1010_ == 0)
{
v_config_1022_ = v___x_1009_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 0, v_foApprox_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 1, v_ctxApprox_991_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 2, v_quasiPatternApprox_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 3, v_constApprox_993_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 4, v_isDefEqStuckEx_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 5, v_unificationHints_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 6, v_proofIrrelevance_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 7, v_assignSyntheticOpaque_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 8, v_offsetCnstrs_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 10, v_etaStruct_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 11, v_univApprox_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 12, v_iota_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 13, v_beta_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 14, v_proj_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 15, v_zeta_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 16, v_zetaDelta_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 17, v_zetaUnused_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, 18, v_zetaHave_1007_);
v_config_1022_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
uint64_t v___x_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
lean_ctor_set_uint8(v_config_1022_, 9, v___y_989_);
v___x_1023_ = l_Lean_Meta_Context_configKey(v___y_977_);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___y_977_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; lean_object* v_unused_1039_; lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; lean_object* v_unused_1044_; 
v_unused_1038_ = lean_ctor_get(v___y_977_, 6);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v___y_977_, 5);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v___y_977_, 4);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v___y_977_, 3);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v___y_977_, 2);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v___y_977_, 1);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v___y_977_, 0);
lean_dec(v_unused_1044_);
v___x_1025_ = v___y_977_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v___y_977_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v_key_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1027_ = 2ULL;
v___x_1028_ = lean_uint64_shift_right(v___x_1023_, v___x_1027_);
v___x_1029_ = lean_uint64_shift_left(v___x_1028_, v___x_1027_);
v___x_1030_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_989_);
v_key_1031_ = lean_uint64_lor(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1032_, 0, v_config_1022_);
lean_ctor_set_uint64(v___x_1032_, sizeof(void*)*1, v_key_1031_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1032_);
v___x_1034_ = v___x_1025_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_zetaDeltaSet_1012_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_lctx_1013_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_localInstances_1014_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v_defEqCtx_x3f_1015_);
lean_ctor_set(v_reuseFailAlloc_1036_, 5, v_synthPendingDepth_1016_);
lean_ctor_set(v_reuseFailAlloc_1036_, 6, v_canUnfold_x3f_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*7, v_trackZetaDelta_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*7 + 1, v_univApprox_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*7 + 3, v_cacheInferType_1020_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_983_, v_maxArgs_x3f_975_, v___f_976_, v___x_987_, v___x_987_, v___x_1034_, v___y_978_, v___y_979_, v___y_980_);
return v___x_1035_;
}
}
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v___f_976_);
lean_dec(v_maxArgs_x3f_975_);
v_a_1048_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_982_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_982_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1056_, lean_object* v_maxArgs_x3f_1057_, lean_object* v___f_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1056_, v_maxArgs_x3f_1057_, v___f_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_i_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_array_get_size(v_keys_1065_);
v___x_1070_ = lean_nat_dec_lt(v_i_1067_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_i_1067_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
else
{
lean_object* v_k_x27_1072_; uint8_t v___x_1073_; 
v_k_x27_1072_ = lean_array_fget_borrowed(v_keys_1065_, v_i_1067_);
v___x_1073_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1068_, v_k_x27_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_nat_add(v_i_1067_, v___x_1074_);
lean_dec(v_i_1067_);
v_i_1067_ = v___x_1075_;
goto _start;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_array_fget_borrowed(v_vals_1066_, v_i_1067_);
lean_dec(v_i_1067_);
lean_inc(v___x_1077_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1079_, lean_object* v_vals_1080_, lean_object* v_i_1081_, lean_object* v_k_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1079_, v_vals_1080_, v_i_1081_, v_k_1082_);
lean_dec_ref(v_k_1082_);
lean_dec_ref(v_vals_1080_);
lean_dec_ref(v_keys_1079_);
return v_res_1083_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; 
v___x_1084_ = ((size_t)5ULL);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_shift_left(v___x_1085_, v___x_1084_);
return v___x_1086_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; 
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__0);
v___x_1089_ = lean_usize_sub(v___x_1088_, v___x_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1090_, size_t v_x_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_object* v_es_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1114_; 
v_es_1093_ = lean_ctor_get(v_x_1090_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1095_ = v_x_1090_;
v_isShared_1096_ = v_isSharedCheck_1114_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_es_1093_);
lean_dec(v_x_1090_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1114_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v_j_1101_; lean_object* v___x_1102_; 
v___x_1097_ = lean_box(2);
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1);
v___x_1100_ = lean_usize_land(v_x_1091_, v___x_1099_);
v_j_1101_ = lean_usize_to_nat(v___x_1100_);
v___x_1102_ = lean_array_get(v___x_1097_, v_es_1093_, v_j_1101_);
lean_dec(v_j_1101_);
lean_dec_ref(v_es_1093_);
switch(lean_obj_tag(v___x_1102_))
{
case 0:
{
lean_object* v_key_1103_; lean_object* v_val_1104_; uint8_t v___x_1105_; 
v_key_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_key_1103_);
v_val_1104_ = lean_ctor_get(v___x_1102_, 1);
lean_inc(v_val_1104_);
lean_dec_ref(v___x_1102_);
v___x_1105_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1092_, v_key_1103_);
lean_dec(v_key_1103_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_val_1104_);
lean_del_object(v___x_1095_);
v___x_1106_ = lean_box(0);
return v___x_1106_;
}
else
{
lean_object* v___x_1108_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
lean_ctor_set(v___x_1095_, 0, v_val_1104_);
v___x_1108_ = v___x_1095_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1104_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
case 1:
{
lean_object* v_node_1110_; size_t v___x_1111_; 
lean_del_object(v___x_1095_);
v_node_1110_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_node_1110_);
lean_dec_ref(v___x_1102_);
v___x_1111_ = lean_usize_shift_right(v_x_1091_, v___x_1098_);
v_x_1090_ = v_node_1110_;
v_x_1091_ = v___x_1111_;
goto _start;
}
default: 
{
lean_object* v___x_1113_; 
lean_del_object(v___x_1095_);
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_ks_1115_; lean_object* v_vs_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_ks_1115_ = lean_ctor_get(v_x_1090_, 0);
lean_inc_ref(v_ks_1115_);
v_vs_1116_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_vs_1116_);
lean_dec_ref(v_x_1090_);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1115_, v_vs_1116_, v___x_1117_, v_x_1092_);
lean_dec_ref(v_vs_1116_);
lean_dec_ref(v_ks_1115_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
size_t v_x_13530__boxed_1122_; lean_object* v_res_1123_; 
v_x_13530__boxed_1122_ = lean_unbox_usize(v_x_1120_);
lean_dec(v_x_1120_);
v_res_1123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1119_, v_x_13530__boxed_1122_, v_x_1121_);
lean_dec_ref(v_x_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
uint64_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_Meta_instHashableInfoCacheKey___private__1(v_x_1125_);
v___x_1127_ = lean_uint64_to_usize(v___x_1126_);
v___x_1128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1124_, v___x_1127_, v_x_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1129_, v_x_1130_);
lean_dec_ref(v_x_1130_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11___redArg(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v_ks_1136_; lean_object* v_vs_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_ks_1136_ = lean_ctor_get(v_x_1132_, 0);
v_vs_1137_ = lean_ctor_get(v_x_1132_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v_x_1132_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_vs_1137_);
lean_inc(v_ks_1136_);
lean_dec(v_x_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_get_size(v_ks_1136_);
v___x_1142_ = lean_nat_dec_lt(v_x_1133_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_dec(v_x_1133_);
v___x_1143_ = lean_array_push(v_ks_1136_, v_x_1134_);
v___x_1144_ = lean_array_push(v_vs_1137_, v_x_1135_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1144_);
lean_ctor_set(v___x_1139_, 0, v___x_1143_);
v___x_1146_ = v___x_1139_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
lean_object* v_k_x27_1148_; uint8_t v___x_1149_; 
v_k_x27_1148_ = lean_array_fget_borrowed(v_ks_1136_, v_x_1133_);
v___x_1149_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1134_, v_k_x27_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1151_; 
if (v_isShared_1140_ == 0)
{
v___x_1151_ = v___x_1139_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_ks_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_vs_1137_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_x_1133_, v___x_1152_);
lean_dec(v_x_1133_);
v_x_1132_ = v___x_1151_;
v_x_1133_ = v___x_1153_;
goto _start;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_array_fset(v_ks_1136_, v_x_1133_, v_x_1134_);
v___x_1157_ = lean_array_fset(v_vs_1137_, v_x_1133_, v_x_1135_);
lean_dec(v_x_1133_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1157_);
lean_ctor_set(v___x_1139_, 0, v___x_1156_);
v___x_1159_ = v___x_1139_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1162_, lean_object* v_k_1163_, lean_object* v_v_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11___redArg(v_n_1162_, v___x_1165_, v_k_1163_, v_v_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1168_, size_t v_x_1169_, size_t v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_es_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v_j_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_es_1173_ = lean_ctor_get(v_x_1168_, 0);
v___x_1174_ = ((size_t)5ULL);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1);
v___x_1177_ = lean_usize_land(v_x_1169_, v___x_1176_);
v_j_1178_ = lean_usize_to_nat(v___x_1177_);
v___x_1179_ = lean_array_get_size(v_es_1173_);
v___x_1180_ = lean_nat_dec_lt(v_j_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_dec(v_j_1178_);
lean_dec(v_x_1172_);
lean_dec_ref(v_x_1171_);
return v_x_1168_;
}
else
{
lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1217_; 
lean_inc_ref(v_es_1173_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_x_1168_, 0);
lean_dec(v_unused_1218_);
v___x_1182_ = v_x_1168_;
v_isShared_1183_ = v_isSharedCheck_1217_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v_x_1168_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1217_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_v_1184_; lean_object* v___x_1185_; lean_object* v_xs_x27_1186_; lean_object* v___y_1188_; 
v_v_1184_ = lean_array_fget(v_es_1173_, v_j_1178_);
v___x_1185_ = lean_box(0);
v_xs_x27_1186_ = lean_array_fset(v_es_1173_, v_j_1178_, v___x_1185_);
switch(lean_obj_tag(v_v_1184_))
{
case 0:
{
lean_object* v_key_1193_; lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1204_; 
v_key_1193_ = lean_ctor_get(v_v_1184_, 0);
v_val_1194_ = lean_ctor_get(v_v_1184_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_v_1184_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1196_ = v_v_1184_;
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_inc(v_key_1193_);
lean_dec(v_v_1184_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1171_, v_key_1193_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1196_);
v___x_1199_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1193_, v_val_1194_, v_x_1171_, v_x_1172_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
v___y_1188_ = v___x_1200_;
goto v___jp_1187_;
}
else
{
lean_object* v___x_1202_; 
lean_dec(v_val_1194_);
lean_dec(v_key_1193_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v_x_1172_);
lean_ctor_set(v___x_1196_, 0, v_x_1171_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_x_1171_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_x_1172_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
v___y_1188_ = v___x_1202_;
goto v___jp_1187_;
}
}
}
}
case 1:
{
lean_object* v_node_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1215_; 
v_node_1205_ = lean_ctor_get(v_v_1184_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_v_1184_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1207_ = v_v_1184_;
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_node_1205_);
lean_dec(v_v_1184_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1209_ = lean_usize_shift_right(v_x_1169_, v___x_1174_);
v___x_1210_ = lean_usize_add(v_x_1170_, v___x_1175_);
v___x_1211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1205_, v___x_1209_, v___x_1210_, v_x_1171_, v_x_1172_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1211_);
v___x_1213_ = v___x_1207_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
v___y_1188_ = v___x_1213_;
goto v___jp_1187_;
}
}
}
default: 
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_x_1171_);
lean_ctor_set(v___x_1216_, 1, v_x_1172_);
v___y_1188_ = v___x_1216_;
goto v___jp_1187_;
}
}
v___jp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_array_fset(v_xs_x27_1186_, v_j_1178_, v___y_1188_);
lean_dec(v_j_1178_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1189_);
v___x_1191_ = v___x_1182_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_ks_1219_; lean_object* v_vs_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1240_; 
v_ks_1219_ = lean_ctor_get(v_x_1168_, 0);
v_vs_1220_ = lean_ctor_get(v_x_1168_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1222_ = v_x_1168_;
v_isShared_1223_ = v_isSharedCheck_1240_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_vs_1220_);
lean_inc(v_ks_1219_);
lean_dec(v_x_1168_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1240_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_ks_1219_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_vs_1220_);
v___x_1225_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v_newNode_1226_; uint8_t v___y_1228_; size_t v___x_1234_; uint8_t v___x_1235_; 
v_newNode_1226_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1225_, v_x_1171_, v_x_1172_);
v___x_1234_ = ((size_t)7ULL);
v___x_1235_ = lean_usize_dec_le(v___x_1234_, v_x_1170_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1226_);
v___x_1237_ = lean_unsigned_to_nat(4u);
v___x_1238_ = lean_nat_dec_lt(v___x_1236_, v___x_1237_);
lean_dec(v___x_1236_);
v___y_1228_ = v___x_1238_;
goto v___jp_1227_;
}
else
{
v___y_1228_ = v___x_1235_;
goto v___jp_1227_;
}
v___jp_1227_:
{
if (v___y_1228_ == 0)
{
lean_object* v_ks_1229_; lean_object* v_vs_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_ks_1229_ = lean_ctor_get(v_newNode_1226_, 0);
lean_inc_ref(v_ks_1229_);
v_vs_1230_ = lean_ctor_get(v_newNode_1226_, 1);
lean_inc_ref(v_vs_1230_);
lean_dec_ref(v_newNode_1226_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1170_, v_ks_1229_, v_vs_1230_, v___x_1231_, v___x_1232_);
lean_dec_ref(v_vs_1230_);
lean_dec_ref(v_ks_1229_);
return v___x_1233_;
}
else
{
return v_newNode_1226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1241_, lean_object* v_keys_1242_, lean_object* v_vals_1243_, lean_object* v_i_1244_, lean_object* v_entries_1245_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_array_get_size(v_keys_1242_);
v___x_1247_ = lean_nat_dec_lt(v_i_1244_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v_i_1244_);
return v_entries_1245_;
}
else
{
lean_object* v_k_1248_; lean_object* v_v_1249_; uint64_t v___x_1250_; size_t v_h_1251_; size_t v___x_1252_; lean_object* v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v_h_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_k_1248_ = lean_array_fget_borrowed(v_keys_1242_, v_i_1244_);
v_v_1249_ = lean_array_fget_borrowed(v_vals_1243_, v_i_1244_);
v___x_1250_ = l_Lean_Meta_instHashableInfoCacheKey___private__1(v_k_1248_);
v_h_1251_ = lean_uint64_to_usize(v___x_1250_);
v___x_1252_ = ((size_t)5ULL);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_sub(v_depth_1241_, v___x_1254_);
v___x_1256_ = lean_usize_mul(v___x_1252_, v___x_1255_);
v_h_1257_ = lean_usize_shift_right(v_h_1251_, v___x_1256_);
v___x_1258_ = lean_nat_add(v_i_1244_, v___x_1253_);
lean_dec(v_i_1244_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
v___x_1259_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1245_, v_h_1257_, v_depth_1241_, v_k_1248_, v_v_1249_);
v_i_1244_ = v___x_1258_;
v_entries_1245_ = v___x_1259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1261_, lean_object* v_keys_1262_, lean_object* v_vals_1263_, lean_object* v_i_1264_, lean_object* v_entries_1265_){
_start:
{
size_t v_depth_boxed_1266_; lean_object* v_res_1267_; 
v_depth_boxed_1266_ = lean_unbox_usize(v_depth_1261_);
lean_dec(v_depth_1261_);
v_res_1267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1266_, v_keys_1262_, v_vals_1263_, v_i_1264_, v_entries_1265_);
lean_dec_ref(v_vals_1263_);
lean_dec_ref(v_keys_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
size_t v_x_13689__boxed_1273_; size_t v_x_13690__boxed_1274_; lean_object* v_res_1275_; 
v_x_13689__boxed_1273_ = lean_unbox_usize(v_x_1269_);
lean_dec(v_x_1269_);
v_x_13690__boxed_1274_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_res_1275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1268_, v_x_13689__boxed_1273_, v_x_13690__boxed_1274_, v_x_1271_, v_x_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint64_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_Meta_instHashableInfoCacheKey___private__1(v_x_1277_);
v___x_1280_ = lean_uint64_to_usize(v___x_1279_);
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1276_, v___x_1280_, v___x_1281_, v_x_1277_, v_x_1278_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___f_1289_; lean_object* v___x_11812__overap_1290_; lean_object* v___x_1291_; 
v___f_1289_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_11812__overap_1290_ = lean_panic_fn(v___f_1289_, v_msg_1283_);
v___x_1291_ = lean_apply_5(v___x_11812__overap_1290_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(v_msg_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg(lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_keys_1299_);
v___x_1304_ = lean_nat_dec_lt(v_i_1301_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_i_1301_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
else
{
lean_object* v_k_x27_1306_; uint8_t v___x_1307_; 
v_k_x27_1306_ = lean_array_fget_borrowed(v_keys_1299_, v_i_1301_);
v___x_1307_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1302_, v_k_x27_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_nat_add(v_i_1301_, v___x_1308_);
lean_dec(v_i_1301_);
v_i_1301_ = v___x_1309_;
goto _start;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_array_fget_borrowed(v_vals_1300_, v_i_1301_);
lean_dec(v_i_1301_);
lean_inc(v___x_1311_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg___boxed(lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_i_1315_, lean_object* v_k_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg(v_keys_1313_, v_vals_1314_, v_i_1315_, v_k_1316_);
lean_dec_ref(v_k_1316_);
lean_dec_ref(v_vals_1314_);
lean_dec_ref(v_keys_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg(lean_object* v_x_1318_, size_t v_x_1319_, lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_es_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1342_; 
v_es_1321_ = lean_ctor_get(v_x_1318_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1323_ = v_x_1318_;
v_isShared_1324_ = v_isSharedCheck_1342_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_es_1321_);
lean_dec(v_x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1342_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v_j_1329_; lean_object* v___x_1330_; 
v___x_1325_ = lean_box(2);
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1);
v___x_1328_ = lean_usize_land(v_x_1319_, v___x_1327_);
v_j_1329_ = lean_usize_to_nat(v___x_1328_);
v___x_1330_ = lean_array_get(v___x_1325_, v_es_1321_, v_j_1329_);
lean_dec(v_j_1329_);
lean_dec_ref(v_es_1321_);
switch(lean_obj_tag(v___x_1330_))
{
case 0:
{
lean_object* v_key_1331_; lean_object* v_val_1332_; uint8_t v___x_1333_; 
v_key_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_key_1331_);
v_val_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_val_1332_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1320_, v_key_1331_);
lean_dec(v_key_1331_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_dec(v_val_1332_);
lean_del_object(v___x_1323_);
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
else
{
lean_object* v___x_1336_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 1);
lean_ctor_set(v___x_1323_, 0, v_val_1332_);
v___x_1336_ = v___x_1323_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1332_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
case 1:
{
lean_object* v_node_1338_; size_t v___x_1339_; 
lean_del_object(v___x_1323_);
v_node_1338_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_node_1338_);
lean_dec_ref(v___x_1330_);
v___x_1339_ = lean_usize_shift_right(v_x_1319_, v___x_1326_);
v_x_1318_ = v_node_1338_;
v_x_1319_ = v___x_1339_;
goto _start;
}
default: 
{
lean_object* v___x_1341_; 
lean_del_object(v___x_1323_);
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_ks_1343_; lean_object* v_vs_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_ks_1343_ = lean_ctor_get(v_x_1318_, 0);
lean_inc_ref(v_ks_1343_);
v_vs_1344_ = lean_ctor_get(v_x_1318_, 1);
lean_inc_ref(v_vs_1344_);
lean_dec_ref(v_x_1318_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg(v_ks_1343_, v_vs_1344_, v___x_1345_, v_x_1320_);
lean_dec_ref(v_vs_1344_);
lean_dec_ref(v_ks_1343_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg___boxed(lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
size_t v_x_13903__boxed_1350_; lean_object* v_res_1351_; 
v_x_13903__boxed_1350_ = lean_unbox_usize(v_x_1348_);
lean_dec(v_x_1348_);
v_res_1351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg(v_x_1347_, v_x_13903__boxed_1350_, v_x_1349_);
lean_dec_ref(v_x_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
uint64_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1353_);
v___x_1355_ = lean_uint64_to_usize(v___x_1354_);
v___x_1356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg(v_x_1352_, v___x_1355_, v_x_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(v_x_1357_, v_x_1358_);
lean_dec_ref(v_x_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg(lean_object* v_a_1360_, lean_object* v_x_1361_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 0)
{
uint8_t v___x_1362_; 
v___x_1362_ = 0;
return v___x_1362_;
}
else
{
lean_object* v_key_1363_; lean_object* v_tail_1364_; uint8_t v___x_1365_; 
v_key_1363_ = lean_ctor_get(v_x_1361_, 0);
v_tail_1364_ = lean_ctor_get(v_x_1361_, 2);
v___x_1365_ = lean_name_eq(v_key_1363_, v_a_1360_);
if (v___x_1365_ == 0)
{
v_x_1361_ = v_tail_1364_;
goto _start;
}
else
{
return v___x_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg___boxed(lean_object* v_a_1367_, lean_object* v_x_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg(v_a_1367_, v_x_1368_);
lean_dec(v_x_1368_);
lean_dec(v_a_1367_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg(lean_object* v_m_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_buckets_1373_; lean_object* v___x_1374_; uint64_t v___y_1376_; 
v_buckets_1373_ = lean_ctor_get(v_m_1371_, 1);
v___x_1374_ = lean_array_get_size(v_buckets_1373_);
if (lean_obj_tag(v_a_1372_) == 0)
{
uint64_t v___x_1390_; 
v___x_1390_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_1376_ = v___x_1390_;
goto v___jp_1375_;
}
else
{
uint64_t v_hash_1391_; 
v_hash_1391_ = lean_ctor_get_uint64(v_a_1372_, sizeof(void*)*2);
v___y_1376_ = v_hash_1391_;
goto v___jp_1375_;
}
v___jp_1375_:
{
uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v_fold_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1377_ = 32ULL;
v___x_1378_ = lean_uint64_shift_right(v___y_1376_, v___x_1377_);
v_fold_1379_ = lean_uint64_xor(v___y_1376_, v___x_1378_);
v___x_1380_ = 16ULL;
v___x_1381_ = lean_uint64_shift_right(v_fold_1379_, v___x_1380_);
v___x_1382_ = lean_uint64_xor(v_fold_1379_, v___x_1381_);
v___x_1383_ = lean_uint64_to_usize(v___x_1382_);
v___x_1384_ = lean_usize_of_nat(v___x_1374_);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_sub(v___x_1384_, v___x_1385_);
v___x_1387_ = lean_usize_land(v___x_1383_, v___x_1386_);
v___x_1388_ = lean_array_uget_borrowed(v_buckets_1373_, v___x_1387_);
v___x_1389_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg(v_a_1372_, v___x_1388_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg___boxed(lean_object* v_m_1392_, lean_object* v_a_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg(v_m_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_m_1392_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23___redArg(lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_ks_1400_; lean_object* v_vs_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_ks_1400_ = lean_ctor_get(v_x_1396_, 0);
v_vs_1401_ = lean_ctor_get(v_x_1396_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v_x_1396_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_vs_1401_);
lean_inc(v_ks_1400_);
lean_dec(v_x_1396_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_array_get_size(v_ks_1400_);
v___x_1406_ = lean_nat_dec_lt(v_x_1397_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec(v_x_1397_);
v___x_1407_ = lean_array_push(v_ks_1400_, v_x_1398_);
v___x_1408_ = lean_array_push(v_vs_1401_, v_x_1399_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1408_);
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1410_ = v___x_1403_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
lean_object* v_k_x27_1412_; uint8_t v___x_1413_; 
v_k_x27_1412_ = lean_array_fget_borrowed(v_ks_1400_, v_x_1397_);
v___x_1413_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1398_, v_k_x27_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1415_; 
if (v_isShared_1404_ == 0)
{
v___x_1415_ = v___x_1403_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_ks_1400_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_vs_1401_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_x_1397_, v___x_1416_);
lean_dec(v_x_1397_);
v_x_1396_ = v___x_1415_;
v_x_1397_ = v___x_1417_;
goto _start;
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = lean_array_fset(v_ks_1400_, v_x_1397_, v_x_1398_);
v___x_1421_ = lean_array_fset(v_vs_1401_, v_x_1397_, v_x_1399_);
lean_dec(v_x_1397_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1421_);
lean_ctor_set(v___x_1403_, 0, v___x_1420_);
v___x_1423_ = v___x_1403_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21___redArg(lean_object* v_n_1426_, lean_object* v_k_1427_, lean_object* v_v_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23___redArg(v_n_1426_, v___x_1429_, v_k_1427_, v_v_1428_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(lean_object* v_x_1432_, size_t v_x_1433_, size_t v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
lean_object* v_es_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; lean_object* v_j_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_es_1437_ = lean_ctor_get(v_x_1432_, 0);
v___x_1438_ = ((size_t)5ULL);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___closed__1);
v___x_1441_ = lean_usize_land(v_x_1433_, v___x_1440_);
v_j_1442_ = lean_usize_to_nat(v___x_1441_);
v___x_1443_ = lean_array_get_size(v_es_1437_);
v___x_1444_ = lean_nat_dec_lt(v_j_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_dec(v_j_1442_);
lean_dec(v_x_1436_);
lean_dec_ref(v_x_1435_);
return v_x_1432_;
}
else
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1481_; 
lean_inc_ref(v_es_1437_);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1432_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_x_1432_, 0);
lean_dec(v_unused_1482_);
v___x_1446_ = v_x_1432_;
v_isShared_1447_ = v_isSharedCheck_1481_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_x_1432_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1481_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_v_1448_; lean_object* v___x_1449_; lean_object* v_xs_x27_1450_; lean_object* v___y_1452_; 
v_v_1448_ = lean_array_fget(v_es_1437_, v_j_1442_);
v___x_1449_ = lean_box(0);
v_xs_x27_1450_ = lean_array_fset(v_es_1437_, v_j_1442_, v___x_1449_);
switch(lean_obj_tag(v_v_1448_))
{
case 0:
{
lean_object* v_key_1457_; lean_object* v_val_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_key_1457_ = lean_ctor_get(v_v_1448_, 0);
v_val_1458_ = lean_ctor_get(v_v_1448_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_v_1448_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v_v_1448_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_val_1458_);
lean_inc(v_key_1457_);
lean_dec(v_v_1448_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
uint8_t v___x_1462_; 
v___x_1462_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1435_, v_key_1457_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_del_object(v___x_1460_);
v___x_1463_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1457_, v_val_1458_, v_x_1435_, v_x_1436_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
v___y_1452_ = v___x_1464_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_val_1458_);
lean_dec(v_key_1457_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_x_1436_);
lean_ctor_set(v___x_1460_, 0, v_x_1435_);
v___x_1466_ = v___x_1460_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_x_1435_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_x_1436_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
v___y_1452_ = v___x_1466_;
goto v___jp_1451_;
}
}
}
}
case 1:
{
lean_object* v_node_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1479_; 
v_node_1469_ = lean_ctor_get(v_v_1448_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_v_1448_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1471_ = v_v_1448_;
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_node_1469_);
lean_dec(v_v_1448_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
size_t v___x_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1473_ = lean_usize_shift_right(v_x_1433_, v___x_1438_);
v___x_1474_ = lean_usize_add(v_x_1434_, v___x_1439_);
v___x_1475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(v_node_1469_, v___x_1473_, v___x_1474_, v_x_1435_, v_x_1436_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1475_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v___y_1452_ = v___x_1477_;
goto v___jp_1451_;
}
}
}
default: 
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_x_1435_);
lean_ctor_set(v___x_1480_, 1, v_x_1436_);
v___y_1452_ = v___x_1480_;
goto v___jp_1451_;
}
}
v___jp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_array_fset(v_xs_x27_1450_, v_j_1442_, v___y_1452_);
lean_dec(v_j_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1453_);
v___x_1455_ = v___x_1446_;
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
lean_object* v_ks_1483_; lean_object* v_vs_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1504_; 
v_ks_1483_ = lean_ctor_get(v_x_1432_, 0);
v_vs_1484_ = lean_ctor_get(v_x_1432_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1432_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1486_ = v_x_1432_;
v_isShared_1487_ = v_isSharedCheck_1504_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_vs_1484_);
lean_inc(v_ks_1483_);
lean_dec(v_x_1432_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1504_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_ks_1483_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_vs_1484_);
v___x_1489_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v_newNode_1490_; uint8_t v___y_1492_; size_t v___x_1498_; uint8_t v___x_1499_; 
v_newNode_1490_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21___redArg(v___x_1489_, v_x_1435_, v_x_1436_);
v___x_1498_ = ((size_t)7ULL);
v___x_1499_ = lean_usize_dec_le(v___x_1498_, v_x_1434_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1500_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1490_);
v___x_1501_ = lean_unsigned_to_nat(4u);
v___x_1502_ = lean_nat_dec_lt(v___x_1500_, v___x_1501_);
lean_dec(v___x_1500_);
v___y_1492_ = v___x_1502_;
goto v___jp_1491_;
}
else
{
v___y_1492_ = v___x_1499_;
goto v___jp_1491_;
}
v___jp_1491_:
{
if (v___y_1492_ == 0)
{
lean_object* v_ks_1493_; lean_object* v_vs_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_ks_1493_ = lean_ctor_get(v_newNode_1490_, 0);
lean_inc_ref(v_ks_1493_);
v_vs_1494_ = lean_ctor_get(v_newNode_1490_, 1);
lean_inc_ref(v_vs_1494_);
lean_dec_ref(v_newNode_1490_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___closed__0);
v___x_1497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg(v_x_1434_, v_ks_1493_, v_vs_1494_, v___x_1495_, v___x_1496_);
lean_dec_ref(v_vs_1494_);
lean_dec_ref(v_ks_1493_);
return v___x_1497_;
}
else
{
return v_newNode_1490_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg(size_t v_depth_1505_, lean_object* v_keys_1506_, lean_object* v_vals_1507_, lean_object* v_i_1508_, lean_object* v_entries_1509_){
_start:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_array_get_size(v_keys_1506_);
v___x_1511_ = lean_nat_dec_lt(v_i_1508_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v_i_1508_);
return v_entries_1509_;
}
else
{
lean_object* v_k_1512_; lean_object* v_v_1513_; uint64_t v___x_1514_; size_t v_h_1515_; size_t v___x_1516_; lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; size_t v_h_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_k_1512_ = lean_array_fget_borrowed(v_keys_1506_, v_i_1508_);
v_v_1513_ = lean_array_fget_borrowed(v_vals_1507_, v_i_1508_);
v___x_1514_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1512_);
v_h_1515_ = lean_uint64_to_usize(v___x_1514_);
v___x_1516_ = ((size_t)5ULL);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_sub(v_depth_1505_, v___x_1518_);
v___x_1520_ = lean_usize_mul(v___x_1516_, v___x_1519_);
v_h_1521_ = lean_usize_shift_right(v_h_1515_, v___x_1520_);
v___x_1522_ = lean_nat_add(v_i_1508_, v___x_1517_);
lean_dec(v_i_1508_);
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
v___x_1523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(v_entries_1509_, v_h_1521_, v_depth_1505_, v_k_1512_, v_v_1513_);
v_i_1508_ = v___x_1522_;
v_entries_1509_ = v___x_1523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg___boxed(lean_object* v_depth_1525_, lean_object* v_keys_1526_, lean_object* v_vals_1527_, lean_object* v_i_1528_, lean_object* v_entries_1529_){
_start:
{
size_t v_depth_boxed_1530_; lean_object* v_res_1531_; 
v_depth_boxed_1530_ = lean_unbox_usize(v_depth_1525_);
lean_dec(v_depth_1525_);
v_res_1531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg(v_depth_boxed_1530_, v_keys_1526_, v_vals_1527_, v_i_1528_, v_entries_1529_);
lean_dec_ref(v_vals_1527_);
lean_dec_ref(v_keys_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg___boxed(lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
size_t v_x_14110__boxed_1537_; size_t v_x_14111__boxed_1538_; lean_object* v_res_1539_; 
v_x_14110__boxed_1537_ = lean_unbox_usize(v_x_1533_);
lean_dec(v_x_1533_);
v_x_14111__boxed_1538_ = lean_unbox_usize(v_x_1534_);
lean_dec(v_x_1534_);
v_res_1539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(v_x_1532_, v_x_14110__boxed_1537_, v_x_14111__boxed_1538_, v_x_1535_, v_x_1536_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15___redArg(lean_object* v_x_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
uint64_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1541_);
v___x_1544_ = lean_uint64_to_usize(v___x_1543_);
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(v_x_1540_, v___x_1544_, v___x_1545_, v_x_1541_, v_x_1542_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0(lean_object* v_realizeMapRef_1550_, lean_object* v_env_1551_, lean_object* v_forConst_1552_, lean_object* v_ctx_1553_, lean_object* v_importRealizationCtx_x3f_1554_, lean_object* v_realize_1555_, lean_object* v_opts_1556_, lean_object* v_key_1557_, lean_object* v_inst_1558_, lean_object* v_____r_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v___y_1597_; lean_object* v___x_1602_; 
v___x_1561_ = lean_io_promise_new();
v___x_1562_ = lean_st_ref_take(v_realizeMapRef_1550_);
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1562_, v_inst_1558_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___closed__1);
v___y_1597_ = v___x_1603_;
goto v___jp_1596_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v___x_1602_);
v___y_1597_ = v_val_1604_;
goto v___jp_1596_;
}
v___jp_1563_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_st_ref_set(v_realizeMapRef_1550_, v_snd_1565_);
if (lean_obj_tag(v_fst_1564_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v___x_1561_);
lean_dec_ref(v_opts_1556_);
lean_dec_ref(v_realize_1555_);
lean_dec(v_importRealizationCtx_x3f_1554_);
lean_dec_ref(v_ctx_1553_);
lean_dec(v_forConst_1552_);
lean_dec(v_env_1551_);
v_val_1567_ = lean_ctor_get(v_fst_1564_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_fst_1564_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1569_ = v_fst_1564_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v_fst_1564_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_task_get_own(v_val_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_base_1576_; lean_object* v_serverBaseExts_1577_; lean_object* v_checked_1578_; lean_object* v_asyncConstsMap_1579_; lean_object* v_asyncCtx_x3f_1580_; lean_object* v_localRealizationCtxMap_1581_; lean_object* v_allRealizations_1582_; uint8_t v_isExporting_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_fst_1564_);
v_base_1576_ = lean_ctor_get(v_env_1551_, 0);
v_serverBaseExts_1577_ = lean_ctor_get(v_env_1551_, 1);
v_checked_1578_ = lean_ctor_get(v_env_1551_, 2);
v_asyncConstsMap_1579_ = lean_ctor_get(v_env_1551_, 3);
v_asyncCtx_x3f_1580_ = lean_ctor_get(v_env_1551_, 4);
v_localRealizationCtxMap_1581_ = lean_ctor_get(v_env_1551_, 6);
v_allRealizations_1582_ = lean_ctor_get(v_env_1551_, 7);
v_isExporting_1583_ = lean_ctor_get_uint8(v_env_1551_, sizeof(void*)*8);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_env_1551_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_env_1551_, 5);
lean_dec(v_unused_1595_);
v___x_1585_ = v_env_1551_;
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_allRealizations_1582_);
lean_inc(v_localRealizationCtxMap_1581_);
lean_inc(v_asyncCtx_x3f_1580_);
lean_inc(v_asyncConstsMap_1579_);
lean_inc(v_checked_1578_);
lean_inc(v_serverBaseExts_1577_);
lean_inc(v_base_1576_);
lean_dec(v_env_1551_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1552_, v_ctx_1553_, v_localRealizationCtxMap_1581_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 6, v___x_1587_);
lean_ctor_set(v___x_1585_, 5, v_importRealizationCtx_x3f_1554_);
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_base_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_serverBaseExts_1577_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_checked_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_asyncConstsMap_1579_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_asyncCtx_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_importRealizationCtx_x3f_1554_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_allRealizations_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*8, v_isExporting_1583_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_apply_3(v_realize_1555_, v___x_1589_, v_opts_1556_, lean_box(0));
lean_inc(v___x_1590_);
v___x_1591_ = lean_io_promise_resolve(v___x_1590_, v___x_1561_);
lean_dec(v___x_1561_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
return v___x_1592_;
}
}
}
}
v___jp_1596_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v___y_1597_);
v___x_1598_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(v___y_1597_, v_key_1557_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = l_IO_Promise_result_x21___redArg(v___x_1561_);
v___x_1600_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15___redArg(v___y_1597_, v_key_1557_, v___x_1599_);
v___x_1601_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1558_, v___x_1600_, v___x_1562_);
v_fst_1564_ = v___x_1598_;
v_snd_1565_ = v___x_1601_;
goto v___jp_1563_;
}
else
{
lean_dec_ref(v___y_1597_);
lean_dec(v_inst_1558_);
lean_dec_ref(v_key_1557_);
v_fst_1564_ = v___x_1598_;
v_snd_1565_ = v___x_1562_;
goto v___jp_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0___boxed(lean_object* v_realizeMapRef_1605_, lean_object* v_env_1606_, lean_object* v_forConst_1607_, lean_object* v_ctx_1608_, lean_object* v_importRealizationCtx_x3f_1609_, lean_object* v_realize_1610_, lean_object* v_opts_1611_, lean_object* v_key_1612_, lean_object* v_inst_1613_, lean_object* v_____r_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0(v_realizeMapRef_1605_, v_env_1606_, v_forConst_1607_, v_ctx_1608_, v_importRealizationCtx_x3f_1609_, v_realize_1610_, v_opts_1611_, v_key_1612_, v_inst_1613_, v_____r_1614_);
lean_dec(v_realizeMapRef_1605_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10(lean_object* v_inst_1623_, lean_object* v_env_1624_, lean_object* v_forConst_1625_, lean_object* v_key_1626_, lean_object* v_realize_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v_a_1631_; lean_object* v___y_1635_; lean_object* v_base_1637_; lean_object* v_importRealizationCtx_x3f_1638_; lean_object* v_localRealizationCtxMap_1639_; uint8_t v_isExporting_1640_; lean_object* v_ctx_1642_; lean_object* v___y_1657_; 
v___x_1629_ = lean_io_get_num_heartbeats();
v_base_1637_ = lean_ctor_get(v_env_1624_, 0);
lean_inc_ref(v_base_1637_);
v_importRealizationCtx_x3f_1638_ = lean_ctor_get(v_env_1624_, 5);
lean_inc(v_importRealizationCtx_x3f_1638_);
v_localRealizationCtxMap_1639_ = lean_ctor_get(v_env_1624_, 6);
lean_inc(v_localRealizationCtxMap_1639_);
v_isExporting_1640_ = lean_ctor_get_uint8(v_env_1624_, sizeof(void*)*8);
lean_dec_ref(v_env_1624_);
if (v_isExporting_1640_ == 0)
{
lean_object* v_private_1677_; 
v_private_1677_ = lean_ctor_get(v_base_1637_, 0);
lean_inc(v_private_1677_);
lean_dec_ref(v_base_1637_);
v___y_1657_ = v_private_1677_;
goto v___jp_1656_;
}
else
{
lean_object* v_public_1678_; 
v_public_1678_ = lean_ctor_get(v_base_1637_, 1);
lean_inc(v_public_1678_);
lean_dec_ref(v_base_1637_);
v___y_1657_ = v_public_1678_;
goto v___jp_1656_;
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_io_set_heartbeats(v___x_1629_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1631_);
return v___x_1633_;
}
v___jp_1634_:
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___y_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___y_1635_);
v_a_1631_ = v_a_1636_;
goto v___jp_1630_;
}
v___jp_1641_:
{
lean_object* v_env_1643_; lean_object* v_opts_1644_; lean_object* v_realizeMapRef_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_env_1643_ = lean_ctor_get(v_ctx_1642_, 0);
lean_inc(v_env_1643_);
v_opts_1644_ = lean_ctor_get(v_ctx_1642_, 1);
lean_inc_ref(v_opts_1644_);
v_realizeMapRef_1645_ = lean_ctor_get(v_ctx_1642_, 2);
lean_inc(v_realizeMapRef_1645_);
v___x_1646_ = lean_st_ref_get(v_realizeMapRef_1645_);
v___x_1647_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1646_, v_inst_1623_);
lean_dec(v___x_1646_);
if (lean_obj_tag(v___x_1647_) == 1)
{
lean_object* v_val_1648_; lean_object* v___x_1649_; 
v_val_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1648_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(v_val_1648_, v_key_1626_);
if (lean_obj_tag(v___x_1649_) == 1)
{
lean_object* v_val_1650_; lean_object* v___x_1651_; 
lean_dec(v_realizeMapRef_1645_);
lean_dec_ref(v_opts_1644_);
lean_dec(v_env_1643_);
lean_dec_ref(v_ctx_1642_);
lean_dec(v_importRealizationCtx_x3f_1638_);
lean_dec_ref(v_realize_1627_);
lean_dec_ref(v_key_1626_);
lean_dec(v_forConst_1625_);
lean_dec(v_inst_1623_);
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_task_get_own(v_val_1650_);
v_a_1631_ = v___x_1651_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v___x_1653_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0(v_realizeMapRef_1645_, v_env_1643_, v_forConst_1625_, v_ctx_1642_, v_importRealizationCtx_x3f_1638_, v_realize_1627_, v_opts_1644_, v_key_1626_, v_inst_1623_, v___x_1652_);
lean_dec(v_realizeMapRef_1645_);
v___y_1635_ = v___x_1653_;
goto v___jp_1634_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v___x_1647_);
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___lam__0(v_realizeMapRef_1645_, v_env_1643_, v_forConst_1625_, v_ctx_1642_, v_importRealizationCtx_x3f_1638_, v_realize_1627_, v_opts_1644_, v_key_1626_, v_inst_1623_, v___x_1654_);
lean_dec(v_realizeMapRef_1645_);
v___y_1635_ = v___x_1655_;
goto v___jp_1634_;
}
}
v___jp_1656_:
{
lean_object* v_const2ModIdx_1658_; uint8_t v___x_1659_; 
v_const2ModIdx_1658_ = lean_ctor_get(v___y_1657_, 2);
lean_inc_ref(v_const2ModIdx_1658_);
lean_dec_ref(v___y_1657_);
v___x_1659_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg(v_const2ModIdx_1658_, v_forConst_1625_);
lean_dec_ref(v_const2ModIdx_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1639_, v_forConst_1625_);
lean_dec(v_localRealizationCtxMap_1639_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_importRealizationCtx_x3f_1638_);
lean_dec(v___x_1629_);
lean_dec_ref(v_realize_1627_);
lean_dec_ref(v_key_1626_);
v___x_1661_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__0));
v___x_1662_ = 1;
v___x_1663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1623_, v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1661_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__1));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1625_, v___x_1662_);
v___x_1668_ = lean_string_append(v___x_1666_, v___x_1667_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__2));
v___x_1670_ = lean_string_append(v___x_1668_, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
else
{
lean_object* v_val_1673_; 
v_val_1673_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1673_);
lean_dec_ref(v___x_1660_);
v_ctx_1642_ = v_val_1673_;
goto v___jp_1641_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1639_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1638_) == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v___x_1629_);
lean_dec_ref(v_realize_1627_);
lean_dec_ref(v_key_1626_);
lean_dec(v_forConst_1625_);
lean_dec(v_inst_1623_);
v___x_1674_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___closed__4));
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; 
v_val_1676_ = lean_ctor_get(v_importRealizationCtx_x3f_1638_, 0);
lean_inc(v_val_1676_);
v_ctx_1642_ = v_val_1676_;
goto v___jp_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10___boxed(lean_object* v_inst_1679_, lean_object* v_env_1680_, lean_object* v_forConst_1681_, lean_object* v_key_1682_, lean_object* v_realize_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10(v_inst_1679_, v_env_1680_, v_forConst_1681_, v_key_1682_, v_realize_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0(lean_object* v_realize_1686_, lean_object* v_inst_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_apply_5(v_realize_1686_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, lean_box(0));
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_inst_1687_);
lean_ctor_set(v___x_1698_, 1, v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_inst_1687_);
v_a_1703_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1693_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1693_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0___boxed(lean_object* v_realize_1711_, lean_object* v_inst_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0(v_realize_1711_, v_inst_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v_res_1718_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = l_Lean_Options_empty;
v___x_1720_ = l_Lean_Core_getMaxHeartbeats(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_unsigned_to_nat(16u);
v___x_1723_ = lean_mk_array(v___x_1722_, v___x_1721_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__1);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1730_ = lean_unsigned_to_nat(36u);
v___x_1731_ = lean_unsigned_to_nat(2606u);
v___x_1732_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__4));
v___x_1733_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__3));
v___x_1734_ = l_mkPanicMessageWithDecl(v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_, v___x_1729_);
return v___x_1734_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1736_ = lean_unsigned_to_nat(48u);
v___x_1737_ = lean_unsigned_to_nat(2597u);
v___x_1738_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__4));
v___x_1739_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__3));
v___x_1740_ = l_mkPanicMessageWithDecl(v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_, v___x_1735_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_forConst_1743_, lean_object* v_key_1744_, lean_object* v_realize_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v_env_1752_; uint8_t v___x_1753_; 
v___x_1751_ = lean_st_ref_get(v_a_1749_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1752_, v_forConst_1743_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref(v_env_1752_);
lean_dec_ref(v_key_1744_);
lean_dec(v_forConst_1743_);
lean_dec(v_inst_1742_);
lean_dec(v_inst_1741_);
v___x_1754_ = lean_apply_5(v_realize_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, lean_box(0));
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v_fileName_1756_; lean_object* v_fileMap_1757_; lean_object* v_ref_1758_; lean_object* v___f_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1755_ = lean_io_get_num_heartbeats();
v_fileName_1756_ = lean_ctor_get(v_a_1748_, 0);
v_fileMap_1757_ = lean_ctor_get(v_a_1748_, 1);
v_ref_1758_ = lean_ctor_get(v_a_1748_, 5);
lean_inc(v_inst_1742_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1759_, 0, v_realize_1745_);
lean_closure_set(v___f_1759_, 1, v_inst_1742_);
v___x_1760_ = 0;
v___x_1761_ = l_Lean_Options_empty;
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_unsigned_to_nat(1000u);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__0);
v___x_1768_ = l_Lean_firstFrontendMacroScope;
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__2);
lean_inc_ref(v_fileMap_1757_);
lean_inc_ref(v_fileName_1756_);
v___x_1771_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1771_, 0, v_fileName_1756_);
lean_ctor_set(v___x_1771_, 1, v_fileMap_1757_);
lean_ctor_set(v___x_1771_, 2, v___x_1761_);
lean_ctor_set(v___x_1771_, 3, v___x_1762_);
lean_ctor_set(v___x_1771_, 4, v___x_1763_);
lean_ctor_set(v___x_1771_, 5, v___x_1764_);
lean_ctor_set(v___x_1771_, 6, v___x_1765_);
lean_ctor_set(v___x_1771_, 7, v___x_1766_);
lean_ctor_set(v___x_1771_, 8, v___x_1755_);
lean_ctor_set(v___x_1771_, 9, v___x_1767_);
lean_ctor_set(v___x_1771_, 10, v___x_1765_);
lean_ctor_set(v___x_1771_, 11, v___x_1768_);
lean_ctor_set(v___x_1771_, 12, v___x_1769_);
lean_ctor_set(v___x_1771_, 13, v___x_1770_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*14, v___x_1760_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*14 + 1, v___x_1760_);
v___x_1772_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1772_, 0, v___f_1759_);
lean_closure_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10(v_inst_1741_, v_env_1752_, v_forConst_1743_, v_key_1744_, v___x_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1826_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1826_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1826_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1779_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1774_, v___x_1778_);
lean_dec(v_a_1774_);
if (lean_obj_tag(v___x_1779_) == 1)
{
lean_object* v_val_1780_; lean_object* v_res_x3f_1781_; lean_object* v_snap_x3f_1782_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v_snap_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref(v___x_1779_);
v_res_x3f_1781_ = lean_ctor_get(v_val_1780_, 0);
lean_inc_ref(v_res_x3f_1781_);
v_snap_x3f_1782_ = lean_ctor_get(v_val_1780_, 1);
lean_inc(v_snap_x3f_1782_);
lean_dec(v_val_1780_);
if (lean_obj_tag(v_snap_x3f_1782_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; 
v_val_1816_ = lean_ctor_get(v_snap_x3f_1782_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v_snap_x3f_1782_);
v___x_1817_ = l_Lean_Syntax_getRange_x3f(v_ref_1758_, v___x_1760_);
if (lean_obj_tag(v___x_1817_) == 1)
{
lean_object* v_val_1818_; lean_object* v_start_1819_; lean_object* v_stop_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_val_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_val_1818_);
lean_dec_ref(v___x_1817_);
v_start_1819_ = lean_ctor_get(v_val_1818_, 0);
lean_inc(v_start_1819_);
v_stop_1820_ = lean_ctor_get(v_val_1818_, 1);
lean_inc(v_stop_1820_);
lean_dec(v_val_1818_);
lean_inc_ref(v_fileMap_1757_);
v___x_1821_ = l_Lean_FileMap_toPosition(v_fileMap_1757_, v_start_1819_);
lean_dec(v_start_1819_);
lean_inc_ref(v_fileMap_1757_);
v___x_1822_ = l_Lean_FileMap_toPosition(v_fileMap_1757_, v_stop_1820_);
lean_dec(v_stop_1820_);
v___x_1823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1816_, v___x_1821_, v___x_1822_);
v_snap_1801_ = v___x_1823_;
v___y_1802_ = v_a_1746_;
v___y_1803_ = v_a_1747_;
v___y_1804_ = v_a_1748_;
v___y_1805_ = v_a_1749_;
goto v___jp_1800_;
}
else
{
lean_dec(v___x_1817_);
v_snap_1801_ = v_val_1816_;
v___y_1802_ = v_a_1746_;
v___y_1803_ = v_a_1747_;
v___y_1804_ = v_a_1748_;
v___y_1805_ = v_a_1749_;
goto v___jp_1800_;
}
}
else
{
lean_dec(v_snap_x3f_1782_);
v___y_1784_ = v_a_1746_;
v___y_1785_ = v_a_1747_;
v___y_1786_ = v_a_1748_;
v___y_1787_ = v_a_1749_;
goto v___jp_1783_;
}
v___jp_1783_:
{
if (lean_obj_tag(v_res_x3f_1781_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; 
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v_inst_1742_);
v_a_1788_ = lean_ctor_get(v_res_x3f_1781_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v_res_x3f_1781_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 1);
lean_ctor_set(v___x_1776_, 0, v_a_1788_);
v___x_1790_ = v___x_1776_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v_res_x3f_1781_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v_res_x3f_1781_);
v___x_1793_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1792_, v_inst_1742_);
lean_dec(v_inst_1742_);
lean_dec(v_a_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1776_);
v___x_1794_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__5);
v___x_1795_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(v___x_1794_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1795_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1798_; 
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
v_val_1796_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_val_1796_);
lean_dec_ref(v___x_1793_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_val_1796_);
v___x_1798_ = v___x_1776_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_val_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v___jp_1800_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1769_, v_snap_1801_);
v___x_1807_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1806_, v___y_1805_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec_ref(v___x_1807_);
v___y_1784_ = v___y_1802_;
v___y_1785_ = v___y_1803_;
v___y_1786_ = v___y_1804_;
v___y_1787_ = v___y_1805_;
goto v___jp_1783_;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_res_x3f_1781_);
lean_del_object(v___x_1776_);
lean_dec(v_inst_1742_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1779_);
lean_del_object(v___x_1776_);
lean_dec(v_inst_1742_);
v___x_1824_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___closed__6);
v___x_1825_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(v___x_1824_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
lean_inc(v_ref_1758_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_inst_1742_);
v_a_1827_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v___x_1773_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1773_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1831_ = lean_io_error_to_string(v_a_1827_);
v___x_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = l_Lean_MessageData_ofFormat(v___x_1832_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_ref_1758_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1834_);
v___x_1836_ = v___x_1829_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg___boxed(lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_forConst_1841_, lean_object* v_key_1842_, lean_object* v_realize_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(v_inst_1839_, v_inst_1840_, v_forConst_1841_, v_key_1842_, v_realize_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1852_, lean_object* v_maxArgs_x3f_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
lean_inc(v_maxArgs_x3f_1853_);
lean_inc_ref(v_fn_1852_);
v___x_1859_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1852_, v_maxArgs_x3f_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1925_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1925_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1925_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_finfo_1865_; lean_object* v___y_1866_; lean_object* v___x_1898_; lean_object* v_cache_1899_; lean_object* v_funInfo_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_st_ref_get(v_a_1855_);
v_cache_1899_ = lean_ctor_get(v___x_1898_, 1);
lean_inc_ref(v_cache_1899_);
lean_dec(v___x_1898_);
v_funInfo_1900_ = lean_ctor_get(v_cache_1899_, 1);
lean_inc_ref(v_funInfo_1900_);
lean_dec_ref(v_cache_1899_);
v___x_1901_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1900_, v_a_1860_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___f_1902_; lean_object* v___f_1903_; 
v___f_1902_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1853_);
lean_inc_ref(v_fn_1852_);
v___f_1903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1903_, 0, v_fn_1852_);
lean_closure_set(v___f_1903_, 1, v_maxArgs_x3f_1853_);
lean_closure_set(v___f_1903_, 2, v___f_1902_);
if (lean_obj_tag(v_fn_1852_) == 4)
{
lean_object* v_declName_1904_; lean_object* v_us_1905_; lean_object* v___f_1906_; uint8_t v___x_1907_; 
v_declName_1904_ = lean_ctor_get(v_fn_1852_, 0);
v_us_1905_ = lean_ctor_get(v_fn_1852_, 1);
v___f_1906_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
lean_inc(v_us_1905_);
v___x_1907_ = l_List_any___redArg(v_us_1905_, v___f_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_inc(v_us_1905_);
lean_inc(v_declName_1904_);
lean_dec_ref(v_fn_1852_);
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_1909_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_inc(v_declName_1904_);
v___x_1910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1910_, 0, v_declName_1904_);
lean_ctor_set(v___x_1910_, 1, v_us_1905_);
lean_ctor_set(v___x_1910_, 2, v_maxArgs_x3f_1853_);
lean_inc(v_a_1855_);
v___x_1911_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(v___x_1908_, v___x_1909_, v_declName_1904_, v___x_1910_, v___f_1903_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v_finfo_1865_ = v_a_1912_;
v___y_1866_ = v_a_1855_;
goto v___jp_1864_;
}
else
{
lean_del_object(v___x_1862_);
lean_dec(v_a_1860_);
lean_dec(v_a_1855_);
return v___x_1911_;
}
}
else
{
lean_object* v___x_1913_; 
lean_dec_ref(v___f_1903_);
lean_inc(v_a_1855_);
v___x_1913_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1852_, v_maxArgs_x3f_1853_, v___f_1902_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v_finfo_1865_ = v_a_1914_;
v___y_1866_ = v_a_1855_;
goto v___jp_1864_;
}
else
{
lean_del_object(v___x_1862_);
lean_dec(v_a_1860_);
lean_dec(v_a_1855_);
return v___x_1913_;
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref(v___f_1903_);
lean_inc(v_a_1855_);
v___x_1915_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1852_, v_maxArgs_x3f_1853_, v___f_1902_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v_finfo_1865_ = v_a_1916_;
v___y_1866_ = v_a_1855_;
goto v___jp_1864_;
}
else
{
lean_del_object(v___x_1862_);
lean_dec(v_a_1860_);
lean_dec(v_a_1855_);
return v___x_1915_;
}
}
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1862_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_maxArgs_x3f_1853_);
lean_dec_ref(v_fn_1852_);
v_val_1917_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1901_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_val_1917_);
lean_dec(v___x_1901_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 0);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_val_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
v___jp_1864_:
{
lean_object* v___x_1867_; lean_object* v_cache_1868_; lean_object* v_mctx_1869_; lean_object* v_zetaDeltaFVarIds_1870_; lean_object* v_postponed_1871_; lean_object* v_diag_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1897_; 
v___x_1867_ = lean_st_ref_take(v___y_1866_);
v_cache_1868_ = lean_ctor_get(v___x_1867_, 1);
v_mctx_1869_ = lean_ctor_get(v___x_1867_, 0);
v_zetaDeltaFVarIds_1870_ = lean_ctor_get(v___x_1867_, 2);
v_postponed_1871_ = lean_ctor_get(v___x_1867_, 3);
v_diag_1872_ = lean_ctor_get(v___x_1867_, 4);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1874_ = v___x_1867_;
v_isShared_1875_ = v_isSharedCheck_1897_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_diag_1872_);
lean_inc(v_postponed_1871_);
lean_inc(v_zetaDeltaFVarIds_1870_);
lean_inc(v_cache_1868_);
lean_inc(v_mctx_1869_);
lean_dec(v___x_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1897_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_inferType_1876_; lean_object* v_funInfo_1877_; lean_object* v_synthInstance_1878_; lean_object* v_whnf_1879_; lean_object* v_defEqTrans_1880_; lean_object* v_defEqPerm_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1896_; 
v_inferType_1876_ = lean_ctor_get(v_cache_1868_, 0);
v_funInfo_1877_ = lean_ctor_get(v_cache_1868_, 1);
v_synthInstance_1878_ = lean_ctor_get(v_cache_1868_, 2);
v_whnf_1879_ = lean_ctor_get(v_cache_1868_, 3);
v_defEqTrans_1880_ = lean_ctor_get(v_cache_1868_, 4);
v_defEqPerm_1881_ = lean_ctor_get(v_cache_1868_, 5);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_cache_1868_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1883_ = v_cache_1868_;
v_isShared_1884_ = v_isSharedCheck_1896_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_defEqPerm_1881_);
lean_inc(v_defEqTrans_1880_);
lean_inc(v_whnf_1879_);
lean_inc(v_synthInstance_1878_);
lean_inc(v_funInfo_1877_);
lean_inc(v_inferType_1876_);
lean_dec(v_cache_1868_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1896_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_inc_ref(v_finfo_1865_);
v___x_1885_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1877_, v_a_1860_, v_finfo_1865_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_inferType_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_synthInstance_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_whnf_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_defEqTrans_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_defEqPerm_1881_);
v___x_1887_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1887_);
v___x_1889_ = v___x_1874_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_mctx_1869_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_zetaDeltaFVarIds_1870_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_postponed_1871_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_diag_1872_);
v___x_1889_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_st_ref_set(v___y_1866_, v___x_1889_);
lean_dec(v___y_1866_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_finfo_1865_);
v___x_1892_ = v___x_1862_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_finfo_1865_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
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
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_maxArgs_x3f_1853_);
lean_dec_ref(v_fn_1852_);
v_a_1926_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1859_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1859_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_1934_, lean_object* v_maxArgs_x3f_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_1934_, v_maxArgs_x3f_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_1942_, lean_object* v_k_1943_, lean_object* v_t_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_1943_, v_t_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_1946_, lean_object* v_k_1947_, lean_object* v_t_1948_){
_start:
{
uint8_t v_res_1949_; lean_object* v_r_1950_; 
v_res_1949_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_1946_, v_k_1947_, v_t_1948_);
lean_dec(v_t_1948_);
lean_dec(v_k_1947_);
v_r_1950_ = lean_box(v_res_1949_);
return v_r_1950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_1951_, lean_object* v_val_1952_, lean_object* v___x_1953_, lean_object* v_fvars_1954_, uint8_t v___y_1955_, lean_object* v_inst_1956_, lean_object* v_R_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_, lean_object* v_c_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_1951_, v_val_1952_, v___x_1953_, v_fvars_1954_, v___y_1955_, v_a_1958_, v_b_1959_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_1967_, lean_object* v_val_1968_, lean_object* v___x_1969_, lean_object* v_fvars_1970_, lean_object* v___y_1971_, lean_object* v_inst_1972_, lean_object* v_R_1973_, lean_object* v_a_1974_, lean_object* v_b_1975_, lean_object* v_c_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___y_14929__boxed_1982_; lean_object* v_res_1983_; 
v___y_14929__boxed_1982_ = lean_unbox(v___y_1971_);
v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_1967_, v_val_1968_, v___x_1969_, v_fvars_1970_, v___y_14929__boxed_1982_, v_inst_1972_, v_R_1973_, v_a_1974_, v_b_1975_, v_c_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec_ref(v_fvars_1970_);
lean_dec_ref(v___x_1969_);
lean_dec_ref(v_val_1968_);
lean_dec(v_upperBound_1967_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_1984_, lean_object* v_fvars_1985_, lean_object* v_inst_1986_, lean_object* v_R_1987_, lean_object* v_a_1988_, lean_object* v_b_1989_, lean_object* v_c_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_1984_, v_fvars_1985_, v_a_1988_, v_b_1989_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_1997_, lean_object* v_fvars_1998_, lean_object* v_inst_1999_, lean_object* v_R_2000_, lean_object* v_a_2001_, lean_object* v_b_2002_, lean_object* v_c_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_1997_, v_fvars_1998_, v_inst_1999_, v_R_2000_, v_a_2001_, v_b_2002_, v_c_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec_ref(v_fvars_1998_);
lean_dec(v_upperBound_1997_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2011_, v_x_2012_, v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2016_, v_x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2019_, v_x_2020_, v_x_2021_);
lean_dec_ref(v_x_2021_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11(lean_object* v_00_u03b2_2023_, lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___redArg(v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__11(v_00_u03b2_2031_, v_msg_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_00_u03b2_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_forConst_2042_, lean_object* v_key_2043_, lean_object* v_realize_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(v_inst_2040_, v_inst_2041_, v_forConst_2042_, v_key_2043_, v_realize_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_forConst_2054_, lean_object* v_key_2055_, lean_object* v_realize_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_00_u03b2_2051_, v_inst_2052_, v_inst_2053_, v_forConst_2054_, v_key_2055_, v_realize_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2063_, lean_object* v_x_2064_, size_t v_x_2065_, size_t v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2064_, v_x_2065_, v_x_2066_, v_x_2067_, v_x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
size_t v_x_15038__boxed_2076_; size_t v_x_15039__boxed_2077_; lean_object* v_res_2078_; 
v_x_15038__boxed_2076_ = lean_unbox_usize(v_x_2072_);
lean_dec(v_x_2072_);
v_x_15039__boxed_2077_ = lean_unbox_usize(v_x_2073_);
lean_dec(v_x_2073_);
v_res_2078_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2070_, v_x_2071_, v_x_15038__boxed_2076_, v_x_15039__boxed_2077_, v_x_2074_, v_x_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2079_, lean_object* v_x_2080_, size_t v_x_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2080_, v_x_2081_, v_x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_){
_start:
{
size_t v_x_15055__boxed_2088_; lean_object* v_res_2089_; 
v_x_15055__boxed_2088_ = lean_unbox_usize(v_x_2086_);
lean_dec(v_x_2086_);
v_res_2089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2084_, v_x_2085_, v_x_15055__boxed_2088_, v_x_2087_);
lean_dec_ref(v_x_2087_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2090_, lean_object* v_n_2091_, lean_object* v_k_2092_, lean_object* v_v_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2091_, v_k_2092_, v_v_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2095_, size_t v_depth_2096_, lean_object* v_keys_2097_, lean_object* v_vals_2098_, lean_object* v_heq_2099_, lean_object* v_i_2100_, lean_object* v_entries_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2096_, v_keys_2097_, v_vals_2098_, v_i_2100_, v_entries_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2103_, lean_object* v_depth_2104_, lean_object* v_keys_2105_, lean_object* v_vals_2106_, lean_object* v_heq_2107_, lean_object* v_i_2108_, lean_object* v_entries_2109_){
_start:
{
size_t v_depth_boxed_2110_; lean_object* v_res_2111_; 
v_depth_boxed_2110_ = lean_unbox_usize(v_depth_2104_);
lean_dec(v_depth_2104_);
v_res_2111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2103_, v_depth_boxed_2110_, v_keys_2105_, v_vals_2106_, v_heq_2107_, v_i_2108_, v_entries_2109_);
lean_dec_ref(v_vals_2106_);
lean_dec_ref(v_keys_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2112_, lean_object* v_keys_2113_, lean_object* v_vals_2114_, lean_object* v_heq_2115_, lean_object* v_i_2116_, lean_object* v_k_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2113_, v_vals_2114_, v_i_2116_, v_k_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2119_, lean_object* v_keys_2120_, lean_object* v_vals_2121_, lean_object* v_heq_2122_, lean_object* v_i_2123_, lean_object* v_k_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2119_, v_keys_2120_, v_vals_2121_, v_heq_2122_, v_i_2123_, v_k_2124_);
lean_dec_ref(v_k_2124_);
lean_dec_ref(v_vals_2121_);
lean_dec_ref(v_keys_2120_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14(lean_object* v_00_u03b2_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___redArg(v_x_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14(v_00_u03b2_2130_, v_x_2131_, v_x_2132_);
lean_dec_ref(v_x_2132_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15(lean_object* v_00_u03b2_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15___redArg(v_x_2135_, v_x_2136_, v_x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16(lean_object* v_00_u03b2_2139_, lean_object* v_m_2140_, lean_object* v_a_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___redArg(v_m_2140_, v_a_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2143_, lean_object* v_m_2144_, lean_object* v_a_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16(v_00_u03b2_2143_, v_m_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_m_2144_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11(lean_object* v_00_u03b2_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__11___redArg(v_x_2149_, v_x_2150_, v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, size_t v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___redArg(v_x_2155_, v_x_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
size_t v_x_15100__boxed_2163_; lean_object* v_res_2164_; 
v_x_15100__boxed_2163_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_res_2164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17(v_00_u03b2_2159_, v_x_2160_, v_x_15100__boxed_2163_, v_x_2162_);
lean_dec_ref(v_x_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, size_t v_x_2167_, size_t v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___redArg(v_x_2166_, v_x_2167_, v_x_2168_, v_x_2169_, v_x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19___boxed(lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
size_t v_x_15111__boxed_2178_; size_t v_x_15112__boxed_2179_; lean_object* v_res_2180_; 
v_x_15111__boxed_2178_ = lean_unbox_usize(v_x_2174_);
lean_dec(v_x_2174_);
v_x_15112__boxed_2179_ = lean_unbox_usize(v_x_2175_);
lean_dec(v_x_2175_);
v_res_2180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19(v_00_u03b2_2172_, v_x_2173_, v_x_15111__boxed_2178_, v_x_15112__boxed_2179_, v_x_2176_, v_x_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21(lean_object* v_00_u03b2_2181_, lean_object* v_a_2182_, lean_object* v_x_2183_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___redArg(v_a_2182_, v_x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21___boxed(lean_object* v_00_u03b2_2185_, lean_object* v_a_2186_, lean_object* v_x_2187_){
_start:
{
uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_res_2188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__16_spec__21(v_00_u03b2_2185_, v_a_2186_, v_x_2187_);
lean_dec(v_x_2187_);
lean_dec(v_a_2186_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18(lean_object* v_00_u03b2_2190_, lean_object* v_keys_2191_, lean_object* v_vals_2192_, lean_object* v_heq_2193_, lean_object* v_i_2194_, lean_object* v_k_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___redArg(v_keys_2191_, v_vals_2192_, v_i_2194_, v_k_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_keys_2198_, lean_object* v_vals_2199_, lean_object* v_heq_2200_, lean_object* v_i_2201_, lean_object* v_k_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__14_spec__17_spec__18(v_00_u03b2_2197_, v_keys_2198_, v_vals_2199_, v_heq_2200_, v_i_2201_, v_k_2202_);
lean_dec_ref(v_k_2202_);
lean_dec_ref(v_vals_2199_);
lean_dec_ref(v_keys_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21(lean_object* v_00_u03b2_2204_, lean_object* v_n_2205_, lean_object* v_k_2206_, lean_object* v_v_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21___redArg(v_n_2205_, v_k_2206_, v_v_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22(lean_object* v_00_u03b2_2209_, size_t v_depth_2210_, lean_object* v_keys_2211_, lean_object* v_vals_2212_, lean_object* v_heq_2213_, lean_object* v_i_2214_, lean_object* v_entries_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___redArg(v_depth_2210_, v_keys_2211_, v_vals_2212_, v_i_2214_, v_entries_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22___boxed(lean_object* v_00_u03b2_2217_, lean_object* v_depth_2218_, lean_object* v_keys_2219_, lean_object* v_vals_2220_, lean_object* v_heq_2221_, lean_object* v_i_2222_, lean_object* v_entries_2223_){
_start:
{
size_t v_depth_boxed_2224_; lean_object* v_res_2225_; 
v_depth_boxed_2224_ = lean_unbox_usize(v_depth_2218_);
lean_dec(v_depth_2218_);
v_res_2225_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__22(v_00_u03b2_2217_, v_depth_boxed_2224_, v_keys_2219_, v_vals_2220_, v_heq_2221_, v_i_2222_, v_entries_2223_);
lean_dec_ref(v_vals_2220_);
lean_dec_ref(v_keys_2219_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23(lean_object* v_00_u03b2_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8_spec__10_spec__15_spec__19_spec__21_spec__23___redArg(v_x_2227_, v_x_2228_, v_x_2229_, v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2232_, lean_object* v_maxArgs_x3f_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2232_, v_maxArgs_x3f_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2240_, lean_object* v_maxArgs_x3f_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Meta_getFunInfo(v_fn_2240_, v_maxArgs_x3f_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2248_, lean_object* v_nargs_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_nargs_2249_);
v___x_2256_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2248_, v___x_2255_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2257_, lean_object* v_nargs_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2257_, v_nargs_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2265_){
_start:
{
lean_object* v_paramInfo_2266_; lean_object* v___x_2267_; 
v_paramInfo_2266_ = lean_ctor_get(v_info_2265_, 0);
v___x_2267_ = lean_array_get_size(v_paramInfo_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_FunInfo_getArity(v_info_2268_);
lean_dec_ref(v_info_2268_);
return v_res_2269_;
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
