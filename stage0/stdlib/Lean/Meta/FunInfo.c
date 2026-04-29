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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_j_465_, lean_object* v_bs_466_){
_start:
{
lean_object* v_zero_467_; uint8_t v_isZero_468_; 
v_zero_467_ = lean_unsigned_to_nat(0u);
v_isZero_468_ = lean_nat_dec_eq(v_i_464_, v_zero_467_);
if (v_isZero_468_ == 1)
{
lean_dec(v_j_465_);
lean_dec(v_i_464_);
return v_bs_466_;
}
else
{
lean_object* v___x_469_; uint8_t v_binderInfo_470_; uint8_t v_hasFwdDeps_471_; lean_object* v_backDeps_472_; uint8_t v_isProp_473_; uint8_t v_isDecInst_474_; uint8_t v_isInstance_475_; uint8_t v_higherOrderOutParam_476_; uint8_t v_dependsOnHigherOrderOutParam_477_; lean_object* v_one_478_; lean_object* v_n_479_; lean_object* v___y_481_; 
v___x_469_ = lean_array_fget(v_as_463_, v_j_465_);
v_binderInfo_470_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1);
v_hasFwdDeps_471_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 1);
v_backDeps_472_ = lean_ctor_get(v___x_469_, 0);
v_isProp_473_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 2);
v_isDecInst_474_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 3);
v_isInstance_475_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_476_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_477_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*1 + 6);
v_one_478_ = lean_unsigned_to_nat(1u);
v_n_479_ = lean_nat_sub(v_i_464_, v_one_478_);
lean_dec(v_i_464_);
if (v_hasFwdDeps_471_ == 0)
{
uint8_t v___x_485_; 
v___x_485_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_462_, v_j_465_);
if (v___x_485_ == 0)
{
v___y_481_ = v___x_469_;
goto v___jp_480_;
}
else
{
lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_inc_ref(v_backDeps_472_);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_493_);
v___x_487_ = v___x_469_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_dec(v___x_469_);
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
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_backDeps_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1, v_binderInfo_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 2, v_isProp_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 3, v_isDecInst_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 4, v_isInstance_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 5, v_higherOrderOutParam_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_477_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1 + 1, v___x_485_);
v___y_481_ = v___x_490_;
goto v___jp_480_;
}
}
}
}
else
{
v___y_481_ = v___x_469_;
goto v___jp_480_;
}
v___jp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_nat_add(v_j_465_, v_one_478_);
lean_dec(v_j_465_);
v___x_483_ = lean_array_push(v_bs_466_, v___y_481_);
v_i_464_ = v_n_479_;
v_j_465_ = v___x_482_;
v_bs_466_ = v___x_483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_494_, lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_j_497_, lean_object* v_bs_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_494_, v_as_495_, v_i_496_, v_j_497_, v_bs_498_);
lean_dec_ref(v_as_495_);
lean_dec_ref(v_backDeps_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_500_, lean_object* v_backDeps_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_array_get_size(v_backDeps_501_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_nat_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_array_get_size(v_pinfo_500_);
v___x_506_ = lean_mk_empty_array_with_capacity(v___x_505_);
v___x_507_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_501_, v_pinfo_500_, v___x_505_, v___x_503_, v___x_506_);
return v___x_507_;
}
else
{
lean_inc_ref(v_pinfo_500_);
return v_pinfo_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_508_, lean_object* v_backDeps_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_508_, v_backDeps_509_);
lean_dec_ref(v_backDeps_509_);
lean_dec_ref(v_pinfo_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_511_, lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_j_514_, lean_object* v_inv_515_, lean_object* v_bs_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_511_, v_as_512_, v_i_513_, v_j_514_, v_bs_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_j_521_, lean_object* v_inv_522_, lean_object* v_bs_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_518_, v_as_519_, v_i_520_, v_j_521_, v_inv_522_, v_bs_523_);
lean_dec_ref(v_as_519_);
lean_dec_ref(v_backDeps_518_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_525_, lean_object* v_b_526_, lean_object* v_c_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
v___x_533_ = lean_apply_7(v_k_525_, v_b_526_, v_c_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, lean_box(0));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_534_, lean_object* v_b_535_, lean_object* v_c_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_534_, v_b_535_, v_c_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_543_, lean_object* v_k_544_, uint8_t v_cleanupAnnotations_545_, uint8_t v_whnfType_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___f_552_; lean_object* v___x_553_; 
v___f_552_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_552_, 0, v_k_544_);
v___x_553_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_543_, v___f_552_, v_cleanupAnnotations_545_, v_whnfType_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_a_562_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_553_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_570_, lean_object* v_k_571_, lean_object* v_cleanupAnnotations_572_, lean_object* v_whnfType_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_579_; uint8_t v_whnfType_boxed_580_; lean_object* v_res_581_; 
v_cleanupAnnotations_boxed_579_ = lean_unbox(v_cleanupAnnotations_572_);
v_whnfType_boxed_580_ = lean_unbox(v_whnfType_573_);
v_res_581_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_570_, v_k_571_, v_cleanupAnnotations_boxed_579_, v_whnfType_boxed_580_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_582_, lean_object* v_type_583_, lean_object* v_k_584_, uint8_t v_cleanupAnnotations_585_, uint8_t v_whnfType_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_583_, v_k_584_, v_cleanupAnnotations_585_, v_whnfType_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_593_, lean_object* v_type_594_, lean_object* v_k_595_, lean_object* v_cleanupAnnotations_596_, lean_object* v_whnfType_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_603_; uint8_t v_whnfType_boxed_604_; lean_object* v_res_605_; 
v_cleanupAnnotations_boxed_603_ = lean_unbox(v_cleanupAnnotations_596_);
v_whnfType_boxed_604_ = lean_unbox(v_whnfType_597_);
v_res_605_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_593_, v_type_594_, v_k_595_, v_cleanupAnnotations_boxed_603_, v_whnfType_boxed_604_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___f_613_; lean_object* v___x_9957__overap_614_; lean_object* v___x_615_; 
v___f_613_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9957__overap_614_ = lean_panic_fn_borrowed(v___f_613_, v_msg_607_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
v___x_615_ = lean_apply_5(v___x_9957__overap_614_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, lean_box(0));
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_623_, lean_object* v_maxFVars_x3f_624_, lean_object* v_k_625_, uint8_t v_cleanupAnnotations_626_, uint8_t v_whnfType_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_633_, 0, v_k_625_);
v___x_634_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_623_, v_maxFVars_x3f_624_, v___f_633_, v_cleanupAnnotations_626_, v_whnfType_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_634_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_651_, lean_object* v_maxFVars_x3f_652_, lean_object* v_k_653_, lean_object* v_cleanupAnnotations_654_, lean_object* v_whnfType_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_661_; uint8_t v_whnfType_boxed_662_; lean_object* v_res_663_; 
v_cleanupAnnotations_boxed_661_ = lean_unbox(v_cleanupAnnotations_654_);
v_whnfType_boxed_662_ = lean_unbox(v_whnfType_655_);
v_res_663_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_651_, v_maxFVars_x3f_652_, v_k_653_, v_cleanupAnnotations_boxed_661_, v_whnfType_boxed_662_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_664_, lean_object* v_type_665_, lean_object* v_maxFVars_x3f_666_, lean_object* v_k_667_, uint8_t v_cleanupAnnotations_668_, uint8_t v_whnfType_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_665_, v_maxFVars_x3f_666_, v_k_667_, v_cleanupAnnotations_668_, v_whnfType_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_676_, lean_object* v_type_677_, lean_object* v_maxFVars_x3f_678_, lean_object* v_k_679_, lean_object* v_cleanupAnnotations_680_, lean_object* v_whnfType_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_687_; uint8_t v_whnfType_boxed_688_; lean_object* v_res_689_; 
v_cleanupAnnotations_boxed_687_ = lean_unbox(v_cleanupAnnotations_680_);
v_whnfType_boxed_688_ = lean_unbox(v_whnfType_681_);
v_res_689_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_676_, v_type_677_, v_maxFVars_x3f_678_, v_k_679_, v_cleanupAnnotations_boxed_687_, v_whnfType_boxed_688_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_690_, lean_object* v_val_691_, lean_object* v___x_692_, lean_object* v_fvars_693_, uint8_t v___y_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_a_703_; uint8_t v___x_707_; 
v___x_707_ = lean_nat_dec_lt(v_a_695_, v_upperBound_690_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
lean_dec(v_a_695_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_b_696_);
return v___x_708_;
}
else
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_773_; 
v_fst_709_ = lean_ctor_get(v_b_696_, 0);
v_snd_710_ = lean_ctor_get(v_b_696_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_b_696_);
if (v_isSharedCheck_773_ == 0)
{
v___x_712_ = v_b_696_;
v_isShared_713_ = v_isSharedCheck_773_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_b_696_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_773_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; 
v___x_714_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_691_, v_a_695_);
if (v___x_714_ == 0)
{
lean_object* v___x_716_; 
if (v_isShared_713_ == 0)
{
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_snd_710_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
v_a_703_ = v___x_716_;
goto v___jp_702_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_array_fget_borrowed(v___x_692_, v_a_695_);
v___x_719_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_693_, v___x_718_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v___x_719_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___x_718_);
v___x_721_ = lean_infer_type(v___x_718_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
v___x_723_ = lean_whnf(v_a_722_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___y_726_; uint8_t v___x_732_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_732_ = l_Lean_Expr_isForall(v_a_724_);
lean_dec(v_a_724_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v_val_720_);
lean_del_object(v___x_712_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_fst_709_);
lean_ctor_set(v___x_733_, 1, v_snd_710_);
v_a_703_ = v___x_733_;
goto v___jp_702_;
}
else
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_array_get_size(v_fst_709_);
v___x_735_ = lean_nat_dec_lt(v_val_720_, v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v_val_720_);
v___y_726_ = v_fst_709_;
goto v___jp_725_;
}
else
{
lean_object* v_v_736_; uint8_t v_binderInfo_737_; uint8_t v_hasFwdDeps_738_; lean_object* v_backDeps_739_; uint8_t v_isProp_740_; uint8_t v_isDecInst_741_; uint8_t v_isInstance_742_; uint8_t v_dependsOnHigherOrderOutParam_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_v_736_ = lean_array_fget(v_fst_709_, v_val_720_);
v_binderInfo_737_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1);
v_hasFwdDeps_738_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 1);
v_backDeps_739_ = lean_ctor_get(v_v_736_, 0);
v_isProp_740_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 2);
v_isDecInst_741_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 3);
v_isInstance_742_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_743_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 6);
v_isSharedCheck_753_ = !lean_is_exclusive(v_v_736_);
if (v_isSharedCheck_753_ == 0)
{
v___x_745_ = v_v_736_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_backDeps_739_);
lean_dec(v_v_736_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v_xs_x27_748_; lean_object* v___x_750_; 
v___x_747_ = lean_box(0);
v_xs_x27_748_ = lean_array_fset(v_fst_709_, v_val_720_, v___x_747_);
if (v_isShared_746_ == 0)
{
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_backDeps_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1, v_binderInfo_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1 + 1, v_hasFwdDeps_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1 + 2, v_isProp_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1 + 3, v_isDecInst_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1 + 4, v_isInstance_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_743_);
v___x_750_ = v_reuseFailAlloc_752_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*1 + 5, v___y_694_);
v___x_751_ = lean_array_fset(v_xs_x27_748_, v_val_720_, v___x_750_);
lean_dec(v_val_720_);
v___y_726_ = v___x_751_;
goto v___jp_725_;
}
}
}
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = l_Lean_Expr_fvarId_x21(v___x_718_);
v___x_728_ = l_Lean_FVarIdSet_insert(v_snd_710_, v___x_727_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_728_);
lean_ctor_set(v___x_712_, 0, v___y_726_);
v___x_730_ = v___x_712_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___y_726_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_703_ = v___x_730_;
goto v___jp_702_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_val_720_);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec(v_a_695_);
v_a_754_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_723_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_723_);
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
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_val_720_);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec(v_a_695_);
v_a_762_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_721_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_721_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_771_; 
lean_dec(v___x_719_);
if (v_isShared_713_ == 0)
{
v___x_771_ = v___x_712_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_snd_710_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v_a_703_ = v___x_771_;
goto v___jp_702_;
}
}
}
}
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_a_695_, v___x_704_);
lean_dec(v_a_695_);
v_a_695_ = v___x_705_;
v_b_696_ = v_a_703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_774_, lean_object* v_val_775_, lean_object* v___x_776_, lean_object* v_fvars_777_, lean_object* v___y_778_, lean_object* v_a_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___y_12426__boxed_786_; lean_object* v_res_787_; 
v___y_12426__boxed_786_ = lean_unbox(v___y_778_);
v_res_787_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_774_, v_val_775_, v___x_776_, v_fvars_777_, v___y_12426__boxed_786_, v_a_779_, v_b_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_fvars_777_);
lean_dec_ref(v___x_776_);
lean_dec_ref(v_val_775_);
lean_dec(v_upperBound_774_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_791_, lean_object* v_type_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_799_ = l_Lean_Expr_isAppOf(v_type_792_, v___x_798_);
v___x_800_ = lean_box(v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_802_, lean_object* v_type_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_802_, v_type_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_type_803_);
lean_dec_ref(v_x_802_);
return v_res_809_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_k_810_, lean_object* v_t_811_){
_start:
{
if (lean_obj_tag(v_t_811_) == 0)
{
lean_object* v_k_812_; lean_object* v_l_813_; lean_object* v_r_814_; uint8_t v___x_815_; 
v_k_812_ = lean_ctor_get(v_t_811_, 1);
v_l_813_ = lean_ctor_get(v_t_811_, 3);
v_r_814_ = lean_ctor_get(v_t_811_, 4);
v___x_815_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_810_, v_k_812_);
switch(v___x_815_)
{
case 0:
{
v_t_811_ = v_l_813_;
goto _start;
}
case 1:
{
uint8_t v___x_817_; 
v___x_817_ = 1;
return v___x_817_;
}
default: 
{
v_t_811_ = v_r_814_;
goto _start;
}
}
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_k_820_, lean_object* v_t_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_820_, v_t_821_);
lean_dec(v_t_821_);
lean_dec(v_k_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object* v_snd_824_, lean_object* v_e_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = l_Lean_Expr_isFVar(v_e_825_);
if (v___x_826_ == 0)
{
return v___x_826_;
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = l_Lean_Expr_fvarId_x21(v_e_825_);
v___x_828_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_827_, v_snd_824_);
lean_dec(v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object* v_snd_829_, lean_object* v_e_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_829_, v_e_830_);
lean_dec_ref(v_e_830_);
lean_dec(v_snd_829_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v_dummy_835_; 
v___x_834_ = lean_box(0);
v_dummy_835_ = l_Lean_Expr_sort___override(v___x_834_);
return v_dummy_835_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_839_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_840_ = lean_unsigned_to_nat(47u);
v___x_841_ = lean_unsigned_to_nat(121u);
v___x_842_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_844_ = l_mkPanicMessageWithDecl(v___x_843_, v___x_842_, v___x_841_, v___x_840_, v___x_839_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_845_, lean_object* v_fvars_846_, lean_object* v_a_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_a_855_; uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_lt(v_a_847_, v_upperBound_845_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_dec(v_a_847_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_b_848_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_array_fget_borrowed(v_fvars_846_, v_a_847_);
v___x_862_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_861_, v___y_849_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_974_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v_fst_864_ = lean_ctor_get(v_b_848_, 0);
v_snd_865_ = lean_ctor_get(v_b_848_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_b_848_);
if (v_isSharedCheck_974_ == 0)
{
v___x_867_ = v_b_848_;
v_isShared_868_ = v_isSharedCheck_974_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_b_848_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_974_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___y_873_; uint8_t v___y_874_; uint8_t v___y_875_; uint8_t v___y_955_; 
v___f_869_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
v___x_870_ = l_Lean_LocalDecl_type(v_a_863_);
v___x_871_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_846_, v___x_870_);
if (lean_obj_tag(v_snd_865_) == 0)
{
lean_object* v___f_970_; lean_object* v___x_971_; 
lean_inc_ref(v_snd_865_);
v___f_970_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_970_, 0, v_snd_865_);
v___x_971_ = lean_find_expr(v___f_970_, v___x_870_);
lean_dec_ref(v___f_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
uint8_t v___x_972_; 
v___x_972_ = 0;
v___y_955_ = v___x_972_;
goto v___jp_954_;
}
else
{
lean_dec_ref(v___x_971_);
v___y_955_ = v___x_859_;
goto v___jp_954_;
}
}
else
{
uint8_t v___x_973_; 
v___x_973_ = 0;
v___y_955_ = v___x_973_;
goto v___jp_954_;
}
v___jp_872_:
{
lean_object* v___x_876_; 
lean_inc_ref(v___x_870_);
v___x_876_ = l_Lean_Meta_isProp(v___x_870_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; uint8_t v___x_878_; lean_object* v___x_879_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = 0;
lean_inc_ref(v___x_870_);
v___x_879_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_870_, v___f_869_, v___x_878_, v___x_878_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_864_, v___x_871_);
lean_dec(v_fst_864_);
v___x_882_ = l_Lean_LocalDecl_binderInfo(v_a_863_);
lean_dec(v_a_863_);
v___x_883_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_883_, 0, v___x_871_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_882_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 1, v___x_878_);
v___x_884_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 2, v___x_884_);
v___x_885_ = lean_unbox(v_a_880_);
lean_dec(v_a_880_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 3, v___x_885_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 4, v___y_875_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 5, v___x_878_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1 + 6, v___y_874_);
v___x_886_ = lean_array_push(v___x_881_, v___x_883_);
if (v___y_875_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v___y_873_);
lean_dec_ref(v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_886_);
v___x_888_ = v___x_867_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_865_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_a_855_ = v___x_888_;
goto v___jp_854_;
}
}
else
{
if (lean_obj_tag(v___y_873_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_891_; lean_object* v_env_892_; lean_object* v___x_893_; 
v_val_890_ = lean_ctor_get(v___y_873_, 0);
lean_inc(v_val_890_);
lean_dec_ref(v___y_873_);
v___x_891_ = lean_st_ref_get(v___y_852_);
v_env_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_891_);
v___x_893_ = l_Lean_getOutParamPositions_x3f(v_env_892_, v_val_890_);
lean_dec(v_val_890_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v_val_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_val_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_array_get_size(v_val_894_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_nat_dec_eq(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v_dummy_898_; lean_object* v_nargs_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v_dummy_898_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_899_ = l_Lean_Expr_getAppNumArgs(v___x_870_);
lean_inc(v_nargs_899_);
v___x_900_ = lean_mk_array(v_nargs_899_, v_dummy_898_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_sub(v_nargs_899_, v___x_901_);
lean_dec(v_nargs_899_);
v___x_903_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_870_, v___x_900_, v___x_902_);
v___x_904_ = lean_array_get_size(v___x_903_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_886_);
v___x_906_ = v___x_867_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_865_);
v___x_906_ = v_reuseFailAlloc_918_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; 
v___x_907_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_904_, v_val_894_, v___x_903_, v_fvars_846_, v___y_875_, v___x_896_, v___x_906_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec_ref(v___x_903_);
lean_dec(v_val_894_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v_fst_909_ = lean_ctor_get(v_a_908_, 0);
v_snd_910_ = lean_ctor_get(v_a_908_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v_a_908_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_inc(v_fst_909_);
lean_dec(v_a_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_909_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v_a_855_ = v___x_915_;
goto v___jp_854_;
}
}
}
else
{
lean_dec(v_a_847_);
return v___x_907_;
}
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_val_894_);
lean_dec_ref(v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_886_);
v___x_920_ = v___x_867_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_snd_865_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v_a_855_ = v___x_920_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v___x_893_);
lean_dec_ref(v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_886_);
v___x_923_ = v___x_867_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_865_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v_a_855_ = v___x_923_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v___y_873_);
lean_dec_ref(v___x_870_);
v___x_925_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
v___x_926_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_925_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v___x_926_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_886_);
v___x_928_ = v___x_867_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_snd_865_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
v_a_855_ = v___x_928_;
goto v___jp_854_;
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v___x_886_);
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_a_847_);
v_a_930_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_926_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_877_);
lean_dec(v___y_873_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec(v_a_863_);
lean_dec(v_a_847_);
v_a_938_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_879_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_879_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___y_873_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec(v_a_863_);
lean_dec(v_a_847_);
v_a_946_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_876_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_876_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
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
v___jp_954_:
{
lean_object* v___x_956_; 
lean_inc_ref(v___x_870_);
v___x_956_ = l_Lean_Meta_isClass_x3f(v___x_870_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
if (lean_obj_tag(v_a_957_) == 0)
{
uint8_t v___x_958_; 
v___x_958_ = 0;
v___y_873_ = v_a_957_;
v___y_874_ = v___y_955_;
v___y_875_ = v___x_958_;
goto v___jp_872_;
}
else
{
uint8_t v___x_959_; uint8_t v___x_960_; 
v___x_959_ = l_Lean_LocalDecl_binderInfo(v_a_863_);
v___x_960_ = l_Lean_BinderInfo_isExplicit(v___x_959_);
if (v___x_960_ == 0)
{
v___y_873_ = v_a_957_;
v___y_874_ = v___y_955_;
v___y_875_ = v___x_859_;
goto v___jp_872_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = 0;
v___y_873_ = v_a_957_;
v___y_874_ = v___y_955_;
v___y_875_ = v___x_961_;
goto v___jp_872_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec(v_a_863_);
lean_dec(v_a_847_);
v_a_962_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_956_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_956_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v_b_848_);
lean_dec(v_a_847_);
v_a_975_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_862_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_862_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
v___jp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_a_847_, v___x_856_);
lean_dec(v_a_847_);
v_a_847_ = v___x_857_;
v_b_848_ = v_a_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_983_, lean_object* v_fvars_984_, lean_object* v_a_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_983_, v_fvars_984_, v_a_985_, v_b_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v_fvars_984_);
lean_dec(v_upperBound_983_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_995_, lean_object* v_fvars_996_, lean_object* v_type_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1003_ = lean_array_get_size(v_fvars_996_);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_995_);
v___x_1007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1003_, v_fvars_996_, v___x_1004_, v___x_1006_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1026_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1026_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1026_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_fst_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1024_; 
v_fst_1012_ = lean_ctor_get(v_a_1008_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_1008_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_a_1008_, 1);
lean_dec(v_unused_1025_);
v___x_1014_ = v_a_1008_;
v_isShared_1015_ = v_isSharedCheck_1024_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_fst_1012_);
lean_dec(v_a_1008_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1024_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_996_, v_type_997_);
v___x_1017_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_1012_, v___x_1016_);
lean_dec(v_fst_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1016_);
lean_ctor_set(v___x_1014_, 0, v___x_1017_);
v___x_1019_ = v___x_1014_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1016_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1019_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1007_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1007_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_1035_, lean_object* v_fvars_1036_, lean_object* v_type_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1035_, v_fvars_1036_, v_type_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v_type_1037_);
lean_dec_ref(v_fvars_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1044_, lean_object* v_maxArgs_x3f_1045_, lean_object* v___f_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
v___x_1052_ = lean_infer_type(v_fn_1044_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; uint8_t v_transparency_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___y_1059_; uint8_t v___x_1117_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_Meta_Context_config(v___y_1047_);
v_transparency_1055_ = lean_ctor_get_uint8(v___x_1054_, 9);
v___x_1056_ = 1;
v___x_1057_ = 0;
v___x_1117_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1055_, v___x_1056_);
if (v___x_1117_ == 0)
{
v___y_1059_ = v_transparency_1055_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v___x_1056_;
goto v___jp_1058_;
}
v___jp_1058_:
{
uint8_t v_foApprox_1060_; uint8_t v_ctxApprox_1061_; uint8_t v_quasiPatternApprox_1062_; uint8_t v_constApprox_1063_; uint8_t v_isDefEqStuckEx_1064_; uint8_t v_unificationHints_1065_; uint8_t v_proofIrrelevance_1066_; uint8_t v_assignSyntheticOpaque_1067_; uint8_t v_offsetCnstrs_1068_; uint8_t v_etaStruct_1069_; uint8_t v_univApprox_1070_; uint8_t v_iota_1071_; uint8_t v_beta_1072_; uint8_t v_proj_1073_; uint8_t v_zeta_1074_; uint8_t v_zetaDelta_1075_; uint8_t v_zetaUnused_1076_; uint8_t v_zetaHave_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1116_; 
v_foApprox_1060_ = lean_ctor_get_uint8(v___x_1054_, 0);
v_ctxApprox_1061_ = lean_ctor_get_uint8(v___x_1054_, 1);
v_quasiPatternApprox_1062_ = lean_ctor_get_uint8(v___x_1054_, 2);
v_constApprox_1063_ = lean_ctor_get_uint8(v___x_1054_, 3);
v_isDefEqStuckEx_1064_ = lean_ctor_get_uint8(v___x_1054_, 4);
v_unificationHints_1065_ = lean_ctor_get_uint8(v___x_1054_, 5);
v_proofIrrelevance_1066_ = lean_ctor_get_uint8(v___x_1054_, 6);
v_assignSyntheticOpaque_1067_ = lean_ctor_get_uint8(v___x_1054_, 7);
v_offsetCnstrs_1068_ = lean_ctor_get_uint8(v___x_1054_, 8);
v_etaStruct_1069_ = lean_ctor_get_uint8(v___x_1054_, 10);
v_univApprox_1070_ = lean_ctor_get_uint8(v___x_1054_, 11);
v_iota_1071_ = lean_ctor_get_uint8(v___x_1054_, 12);
v_beta_1072_ = lean_ctor_get_uint8(v___x_1054_, 13);
v_proj_1073_ = lean_ctor_get_uint8(v___x_1054_, 14);
v_zeta_1074_ = lean_ctor_get_uint8(v___x_1054_, 15);
v_zetaDelta_1075_ = lean_ctor_get_uint8(v___x_1054_, 16);
v_zetaUnused_1076_ = lean_ctor_get_uint8(v___x_1054_, 17);
v_zetaHave_1077_ = lean_ctor_get_uint8(v___x_1054_, 18);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1079_ = v___x_1054_;
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v___x_1054_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
uint8_t v_trackZetaDelta_1081_; lean_object* v_zetaDeltaSet_1082_; lean_object* v_lctx_1083_; lean_object* v_localInstances_1084_; lean_object* v_defEqCtx_x3f_1085_; lean_object* v_synthPendingDepth_1086_; lean_object* v_canUnfold_x3f_1087_; uint8_t v_univApprox_1088_; uint8_t v_inTypeClassResolution_1089_; uint8_t v_cacheInferType_1090_; lean_object* v_config_1092_; 
v_trackZetaDelta_1081_ = lean_ctor_get_uint8(v___y_1047_, sizeof(void*)*7);
v_zetaDeltaSet_1082_ = lean_ctor_get(v___y_1047_, 1);
lean_inc(v_zetaDeltaSet_1082_);
v_lctx_1083_ = lean_ctor_get(v___y_1047_, 2);
lean_inc_ref(v_lctx_1083_);
v_localInstances_1084_ = lean_ctor_get(v___y_1047_, 3);
lean_inc_ref(v_localInstances_1084_);
v_defEqCtx_x3f_1085_ = lean_ctor_get(v___y_1047_, 4);
lean_inc(v_defEqCtx_x3f_1085_);
v_synthPendingDepth_1086_ = lean_ctor_get(v___y_1047_, 5);
lean_inc(v_synthPendingDepth_1086_);
v_canUnfold_x3f_1087_ = lean_ctor_get(v___y_1047_, 6);
lean_inc(v_canUnfold_x3f_1087_);
v_univApprox_1088_ = lean_ctor_get_uint8(v___y_1047_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1089_ = lean_ctor_get_uint8(v___y_1047_, sizeof(void*)*7 + 2);
v_cacheInferType_1090_ = lean_ctor_get_uint8(v___y_1047_, sizeof(void*)*7 + 3);
if (v_isShared_1080_ == 0)
{
v_config_1092_ = v___x_1079_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 0, v_foApprox_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 1, v_ctxApprox_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 2, v_quasiPatternApprox_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 3, v_constApprox_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 4, v_isDefEqStuckEx_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 5, v_unificationHints_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 6, v_proofIrrelevance_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 7, v_assignSyntheticOpaque_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 8, v_offsetCnstrs_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 10, v_etaStruct_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 11, v_univApprox_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 12, v_iota_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 13, v_beta_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 14, v_proj_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 15, v_zeta_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 16, v_zetaDelta_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 17, v_zetaUnused_1076_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, 18, v_zetaHave_1077_);
v_config_1092_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
uint64_t v___x_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1107_; 
lean_ctor_set_uint8(v_config_1092_, 9, v___y_1059_);
v___x_1093_ = l_Lean_Meta_Context_configKey(v___y_1047_);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1047_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1108_ = lean_ctor_get(v___y_1047_, 6);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v___y_1047_, 5);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v___y_1047_, 4);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v___y_1047_, 3);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v___y_1047_, 2);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v___y_1047_, 1);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v___y_1047_, 0);
lean_dec(v_unused_1114_);
v___x_1095_ = v___y_1047_;
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___y_1047_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v_key_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1097_ = 2ULL;
v___x_1098_ = lean_uint64_shift_right(v___x_1093_, v___x_1097_);
v___x_1099_ = lean_uint64_shift_left(v___x_1098_, v___x_1097_);
v___x_1100_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1059_);
v_key_1101_ = lean_uint64_lor(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1102_, 0, v_config_1092_);
lean_ctor_set_uint64(v___x_1102_, sizeof(void*)*1, v_key_1101_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_zetaDeltaSet_1082_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_lctx_1083_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_localInstances_1084_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_defEqCtx_x3f_1085_);
lean_ctor_set(v_reuseFailAlloc_1106_, 5, v_synthPendingDepth_1086_);
lean_ctor_set(v_reuseFailAlloc_1106_, 6, v_canUnfold_x3f_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*7, v_trackZetaDelta_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*7 + 1, v_univApprox_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*7 + 3, v_cacheInferType_1090_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1053_, v_maxArgs_x3f_1045_, v___f_1046_, v___x_1057_, v___x_1057_, v___x_1104_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___x_1104_);
return v___x_1105_;
}
}
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v___f_1046_);
lean_dec(v_maxArgs_x3f_1045_);
v_a_1118_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1052_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1052_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1126_, lean_object* v_maxArgs_x3f_1127_, lean_object* v___f_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1126_, v_maxArgs_x3f_1127_, v___f_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1135_, lean_object* v_vals_1136_, lean_object* v_i_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_array_get_size(v_keys_1135_);
v___x_1140_ = lean_nat_dec_lt(v_i_1137_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_i_1137_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
else
{
lean_object* v_k_x27_1142_; uint8_t v___x_1143_; 
v_k_x27_1142_ = lean_array_fget_borrowed(v_keys_1135_, v_i_1137_);
v___x_1143_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1138_, v_k_x27_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_i_1137_, v___x_1144_);
lean_dec(v_i_1137_);
v_i_1137_ = v___x_1145_;
goto _start;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_array_fget_borrowed(v_vals_1136_, v_i_1137_);
lean_dec(v_i_1137_);
lean_inc(v___x_1147_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1149_, v_vals_1150_, v_i_1151_, v_k_1152_);
lean_dec_ref(v_k_1152_);
lean_dec_ref(v_vals_1150_);
lean_dec_ref(v_keys_1149_);
return v_res_1153_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0(void){
_start:
{
size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; 
v___x_1154_ = ((size_t)5ULL);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_shift_left(v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; 
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0);
v___x_1159_ = lean_usize_sub(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1160_, size_t v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 0)
{
lean_object* v_es_1163_; lean_object* v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; lean_object* v_j_1168_; lean_object* v___x_1169_; 
v_es_1163_ = lean_ctor_get(v_x_1160_, 0);
v___x_1164_ = lean_box(2);
v___x_1165_ = ((size_t)5ULL);
v___x_1166_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1167_ = lean_usize_land(v_x_1161_, v___x_1166_);
v_j_1168_ = lean_usize_to_nat(v___x_1167_);
v___x_1169_ = lean_array_get_borrowed(v___x_1164_, v_es_1163_, v_j_1168_);
lean_dec(v_j_1168_);
switch(lean_obj_tag(v___x_1169_))
{
case 0:
{
lean_object* v_key_1170_; lean_object* v_val_1171_; uint8_t v___x_1172_; 
v_key_1170_ = lean_ctor_get(v___x_1169_, 0);
v_val_1171_ = lean_ctor_get(v___x_1169_, 1);
v___x_1172_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1162_, v_key_1170_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_inc(v_val_1171_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_val_1171_);
return v___x_1174_;
}
}
case 1:
{
lean_object* v_node_1175_; size_t v___x_1176_; 
v_node_1175_ = lean_ctor_get(v___x_1169_, 0);
v___x_1176_ = lean_usize_shift_right(v_x_1161_, v___x_1165_);
v_x_1160_ = v_node_1175_;
v_x_1161_ = v___x_1176_;
goto _start;
}
default: 
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
}
}
else
{
lean_object* v_ks_1179_; lean_object* v_vs_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_ks_1179_ = lean_ctor_get(v_x_1160_, 0);
v_vs_1180_ = lean_ctor_get(v_x_1160_, 1);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1179_, v_vs_1180_, v___x_1181_, v_x_1162_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
size_t v_x_13156__boxed_1186_; lean_object* v_res_1187_; 
v_x_13156__boxed_1186_ = lean_unbox_usize(v_x_1184_);
lean_dec(v_x_1184_);
v_res_1187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1183_, v_x_13156__boxed_1186_, v_x_1185_);
lean_dec_ref(v_x_1185_);
lean_dec_ref(v_x_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
uint64_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1189_);
v___x_1191_ = lean_uint64_to_usize(v___x_1190_);
v___x_1192_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1188_, v___x_1191_, v_x_1189_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1193_, v_x_1194_);
lean_dec_ref(v_x_1194_);
lean_dec_ref(v_x_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
lean_object* v_ks_1200_; lean_object* v_vs_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1225_; 
v_ks_1200_ = lean_ctor_get(v_x_1196_, 0);
v_vs_1201_ = lean_ctor_get(v_x_1196_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1203_ = v_x_1196_;
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_vs_1201_);
lean_inc(v_ks_1200_);
lean_dec(v_x_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_array_get_size(v_ks_1200_);
v___x_1206_ = lean_nat_dec_lt(v_x_1197_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec(v_x_1197_);
v___x_1207_ = lean_array_push(v_ks_1200_, v_x_1198_);
v___x_1208_ = lean_array_push(v_vs_1201_, v_x_1199_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1208_);
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v_k_x27_1212_; uint8_t v___x_1213_; 
v_k_x27_1212_ = lean_array_fget_borrowed(v_ks_1200_, v_x_1197_);
v___x_1213_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1198_, v_k_x27_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1215_; 
if (v_isShared_1204_ == 0)
{
v___x_1215_ = v___x_1203_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_ks_1200_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_vs_1201_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_x_1197_, v___x_1216_);
lean_dec(v_x_1197_);
v_x_1196_ = v___x_1215_;
v_x_1197_ = v___x_1217_;
goto _start;
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = lean_array_fset(v_ks_1200_, v_x_1197_, v_x_1198_);
v___x_1221_ = lean_array_fset(v_vs_1201_, v_x_1197_, v_x_1199_);
lean_dec(v_x_1197_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1221_);
lean_ctor_set(v___x_1203_, 0, v___x_1220_);
v___x_1223_ = v___x_1203_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1226_, lean_object* v_k_1227_, lean_object* v_v_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_1226_, v___x_1229_, v_k_1227_, v_v_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1232_, size_t v_x_1233_, size_t v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_es_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; lean_object* v_j_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_es_1237_ = lean_ctor_get(v_x_1232_, 0);
v___x_1238_ = ((size_t)5ULL);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1241_ = lean_usize_land(v_x_1233_, v___x_1240_);
v_j_1242_ = lean_usize_to_nat(v___x_1241_);
v___x_1243_ = lean_array_get_size(v_es_1237_);
v___x_1244_ = lean_nat_dec_lt(v_j_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v_j_1242_);
lean_dec(v_x_1236_);
lean_dec_ref(v_x_1235_);
return v_x_1232_;
}
else
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1281_; 
lean_inc_ref(v_es_1237_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1232_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_x_1232_, 0);
lean_dec(v_unused_1282_);
v___x_1246_ = v_x_1232_;
v_isShared_1247_ = v_isSharedCheck_1281_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v_x_1232_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1281_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_v_1248_; lean_object* v___x_1249_; lean_object* v_xs_x27_1250_; lean_object* v___y_1252_; 
v_v_1248_ = lean_array_fget(v_es_1237_, v_j_1242_);
v___x_1249_ = lean_box(0);
v_xs_x27_1250_ = lean_array_fset(v_es_1237_, v_j_1242_, v___x_1249_);
switch(lean_obj_tag(v_v_1248_))
{
case 0:
{
lean_object* v_key_1257_; lean_object* v_val_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1268_; 
v_key_1257_ = lean_ctor_get(v_v_1248_, 0);
v_val_1258_ = lean_ctor_get(v_v_1248_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_v_1248_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1260_ = v_v_1248_;
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_val_1258_);
lean_inc(v_key_1257_);
lean_dec(v_v_1248_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
uint8_t v___x_1262_; 
v___x_1262_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1235_, v_key_1257_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_del_object(v___x_1260_);
v___x_1263_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1257_, v_val_1258_, v_x_1235_, v_x_1236_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
v___y_1252_ = v___x_1264_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_val_1258_);
lean_dec(v_key_1257_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_x_1236_);
lean_ctor_set(v___x_1260_, 0, v_x_1235_);
v___x_1266_ = v___x_1260_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_x_1235_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_x_1236_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1252_ = v___x_1266_;
goto v___jp_1251_;
}
}
}
}
case 1:
{
lean_object* v_node_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1279_; 
v_node_1269_ = lean_ctor_get(v_v_1248_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_v_1248_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1271_ = v_v_1248_;
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_node_1269_);
lean_dec(v_v_1248_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1273_ = lean_usize_shift_right(v_x_1233_, v___x_1238_);
v___x_1274_ = lean_usize_add(v_x_1234_, v___x_1239_);
v___x_1275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1269_, v___x_1273_, v___x_1274_, v_x_1235_, v_x_1236_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1275_);
v___x_1277_ = v___x_1271_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v___y_1252_ = v___x_1277_;
goto v___jp_1251_;
}
}
}
default: 
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_x_1235_);
lean_ctor_set(v___x_1280_, 1, v_x_1236_);
v___y_1252_ = v___x_1280_;
goto v___jp_1251_;
}
}
v___jp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_array_fset(v_xs_x27_1250_, v_j_1242_, v___y_1252_);
lean_dec(v_j_1242_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1253_);
v___x_1255_ = v___x_1246_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
else
{
lean_object* v_ks_1283_; lean_object* v_vs_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1304_; 
v_ks_1283_ = lean_ctor_get(v_x_1232_, 0);
v_vs_1284_ = lean_ctor_get(v_x_1232_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_x_1232_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1286_ = v_x_1232_;
v_isShared_1287_ = v_isSharedCheck_1304_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_vs_1284_);
lean_inc(v_ks_1283_);
lean_dec(v_x_1232_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1304_;
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
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_ks_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_vs_1284_);
v___x_1289_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v_newNode_1290_; uint8_t v___y_1292_; size_t v___x_1298_; uint8_t v___x_1299_; 
v_newNode_1290_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1289_, v_x_1235_, v_x_1236_);
v___x_1298_ = ((size_t)7ULL);
v___x_1299_ = lean_usize_dec_le(v___x_1298_, v_x_1234_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1290_);
v___x_1301_ = lean_unsigned_to_nat(4u);
v___x_1302_ = lean_nat_dec_lt(v___x_1300_, v___x_1301_);
lean_dec(v___x_1300_);
v___y_1292_ = v___x_1302_;
goto v___jp_1291_;
}
else
{
v___y_1292_ = v___x_1299_;
goto v___jp_1291_;
}
v___jp_1291_:
{
if (v___y_1292_ == 0)
{
lean_object* v_ks_1293_; lean_object* v_vs_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_ks_1293_ = lean_ctor_get(v_newNode_1290_, 0);
lean_inc_ref(v_ks_1293_);
v_vs_1294_ = lean_ctor_get(v_newNode_1290_, 1);
lean_inc_ref(v_vs_1294_);
lean_dec_ref(v_newNode_1290_);
v___x_1295_ = lean_unsigned_to_nat(0u);
v___x_1296_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1234_, v_ks_1293_, v_vs_1294_, v___x_1295_, v___x_1296_);
lean_dec_ref(v_vs_1294_);
lean_dec_ref(v_ks_1293_);
return v___x_1297_;
}
else
{
return v_newNode_1290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1305_, lean_object* v_keys_1306_, lean_object* v_vals_1307_, lean_object* v_i_1308_, lean_object* v_entries_1309_){
_start:
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_array_get_size(v_keys_1306_);
v___x_1311_ = lean_nat_dec_lt(v_i_1308_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec(v_i_1308_);
return v_entries_1309_;
}
else
{
lean_object* v_k_1312_; lean_object* v_v_1313_; uint64_t v___x_1314_; size_t v_h_1315_; size_t v___x_1316_; lean_object* v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v_h_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_k_1312_ = lean_array_fget_borrowed(v_keys_1306_, v_i_1308_);
v_v_1313_ = lean_array_fget_borrowed(v_vals_1307_, v_i_1308_);
v___x_1314_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1312_);
v_h_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = ((size_t)5ULL);
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = lean_usize_sub(v_depth_1305_, v___x_1318_);
v___x_1320_ = lean_usize_mul(v___x_1316_, v___x_1319_);
v_h_1321_ = lean_usize_shift_right(v_h_1315_, v___x_1320_);
v___x_1322_ = lean_nat_add(v_i_1308_, v___x_1317_);
lean_dec(v_i_1308_);
lean_inc(v_v_1313_);
lean_inc(v_k_1312_);
v___x_1323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1309_, v_h_1321_, v_depth_1305_, v_k_1312_, v_v_1313_);
v_i_1308_ = v___x_1322_;
v_entries_1309_ = v___x_1323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1325_, lean_object* v_keys_1326_, lean_object* v_vals_1327_, lean_object* v_i_1328_, lean_object* v_entries_1329_){
_start:
{
size_t v_depth_boxed_1330_; lean_object* v_res_1331_; 
v_depth_boxed_1330_ = lean_unbox_usize(v_depth_1325_);
lean_dec(v_depth_1325_);
v_res_1331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1330_, v_keys_1326_, v_vals_1327_, v_i_1328_, v_entries_1329_);
lean_dec_ref(v_vals_1327_);
lean_dec_ref(v_keys_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_13303__boxed_1337_; size_t v_x_13304__boxed_1338_; lean_object* v_res_1339_; 
v_x_13303__boxed_1337_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_x_13304__boxed_1338_ = lean_unbox_usize(v_x_1334_);
lean_dec(v_x_1334_);
v_res_1339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1332_, v_x_13303__boxed_1337_, v_x_13304__boxed_1338_, v_x_1335_, v_x_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
uint64_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1343_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1341_);
v___x_1344_ = lean_uint64_to_usize(v___x_1343_);
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1340_, v___x_1344_, v___x_1345_, v_x_1341_, v_x_1342_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1350_, lean_object* v_env_1351_, lean_object* v_forConst_1352_, lean_object* v_ctx_1353_, lean_object* v_importRealizationCtx_x3f_1354_, lean_object* v_realize_1355_, lean_object* v_opts_1356_, lean_object* v_key_1357_, lean_object* v_inst_1358_, lean_object* v_____r_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_fst_1364_; lean_object* v_snd_1365_; lean_object* v___y_1397_; lean_object* v___x_1402_; 
v___x_1361_ = lean_io_promise_new();
v___x_1362_ = lean_st_ref_take(v_realizeMapRef_1350_);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1362_, v_inst_1358_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1397_ = v___x_1403_;
goto v___jp_1396_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1404_);
lean_dec_ref(v___x_1402_);
v___y_1397_ = v_val_1404_;
goto v___jp_1396_;
}
v___jp_1363_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_st_ref_set(v_realizeMapRef_1350_, v_snd_1365_);
if (lean_obj_tag(v_fst_1364_) == 1)
{
lean_object* v_val_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v___x_1361_);
lean_dec_ref(v_opts_1356_);
lean_dec_ref(v_realize_1355_);
lean_dec(v_importRealizationCtx_x3f_1354_);
lean_dec_ref(v_ctx_1353_);
lean_dec(v_forConst_1352_);
lean_dec(v_env_1351_);
v_val_1367_ = lean_ctor_get(v_fst_1364_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_fst_1364_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v_fst_1364_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_val_1367_);
lean_dec(v_fst_1364_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_task_get_own(v_val_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_base_1376_; lean_object* v_serverBaseExts_1377_; lean_object* v_checked_1378_; lean_object* v_asyncConstsMap_1379_; lean_object* v_asyncCtx_x3f_1380_; lean_object* v_localRealizationCtxMap_1381_; lean_object* v_allRealizations_1382_; uint8_t v_isExporting_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_fst_1364_);
v_base_1376_ = lean_ctor_get(v_env_1351_, 0);
v_serverBaseExts_1377_ = lean_ctor_get(v_env_1351_, 1);
v_checked_1378_ = lean_ctor_get(v_env_1351_, 2);
v_asyncConstsMap_1379_ = lean_ctor_get(v_env_1351_, 3);
v_asyncCtx_x3f_1380_ = lean_ctor_get(v_env_1351_, 4);
v_localRealizationCtxMap_1381_ = lean_ctor_get(v_env_1351_, 6);
v_allRealizations_1382_ = lean_ctor_get(v_env_1351_, 7);
v_isExporting_1383_ = lean_ctor_get_uint8(v_env_1351_, sizeof(void*)*8);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_env_1351_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v_env_1351_, 5);
lean_dec(v_unused_1395_);
v___x_1385_ = v_env_1351_;
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_allRealizations_1382_);
lean_inc(v_localRealizationCtxMap_1381_);
lean_inc(v_asyncCtx_x3f_1380_);
lean_inc(v_asyncConstsMap_1379_);
lean_inc(v_checked_1378_);
lean_inc(v_serverBaseExts_1377_);
lean_inc(v_base_1376_);
lean_dec(v_env_1351_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1352_, v_ctx_1353_, v_localRealizationCtxMap_1381_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 6, v___x_1387_);
lean_ctor_set(v___x_1385_, 5, v_importRealizationCtx_x3f_1354_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_base_1376_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_serverBaseExts_1377_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_checked_1378_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_asyncConstsMap_1379_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_asyncCtx_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1393_, 5, v_importRealizationCtx_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1393_, 6, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1393_, 7, v_allRealizations_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1393_, sizeof(void*)*8, v_isExporting_1383_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_apply_3(v_realize_1355_, v___x_1389_, v_opts_1356_, lean_box(0));
lean_inc(v___x_1390_);
v___x_1391_ = lean_io_promise_resolve(v___x_1390_, v___x_1361_);
lean_dec(v___x_1361_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
return v___x_1392_;
}
}
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1397_, v_key_1357_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = l_IO_Promise_result_x21___redArg(v___x_1361_);
v___x_1400_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1397_, v_key_1357_, v___x_1399_);
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1358_, v___x_1400_, v___x_1362_);
v_fst_1364_ = v___x_1398_;
v_snd_1365_ = v___x_1401_;
goto v___jp_1363_;
}
else
{
lean_dec_ref(v___y_1397_);
lean_dec(v_inst_1358_);
lean_dec_ref(v_key_1357_);
v_fst_1364_ = v___x_1398_;
v_snd_1365_ = v___x_1362_;
goto v___jp_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1405_, lean_object* v_env_1406_, lean_object* v_forConst_1407_, lean_object* v_ctx_1408_, lean_object* v_importRealizationCtx_x3f_1409_, lean_object* v_realize_1410_, lean_object* v_opts_1411_, lean_object* v_key_1412_, lean_object* v_inst_1413_, lean_object* v_____r_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1405_, v_env_1406_, v_forConst_1407_, v_ctx_1408_, v_importRealizationCtx_x3f_1409_, v_realize_1410_, v_opts_1411_, v_key_1412_, v_inst_1413_, v_____r_1414_);
lean_dec(v_realizeMapRef_1405_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1417_, lean_object* v_x_1418_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
else
{
lean_object* v_key_1420_; lean_object* v_tail_1421_; uint8_t v___x_1422_; 
v_key_1420_ = lean_ctor_get(v_x_1418_, 0);
v_tail_1421_ = lean_ctor_get(v_x_1418_, 2);
v___x_1422_ = lean_name_eq(v_key_1420_, v_a_1417_);
if (v___x_1422_ == 0)
{
v_x_1418_ = v_tail_1421_;
goto _start;
}
else
{
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1424_, lean_object* v_x_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1424_, v_x_1425_);
lean_dec(v_x_1425_);
lean_dec(v_a_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_buckets_1430_; lean_object* v___x_1431_; uint64_t v___y_1433_; 
v_buckets_1430_ = lean_ctor_get(v_m_1428_, 1);
v___x_1431_ = lean_array_get_size(v_buckets_1430_);
if (lean_obj_tag(v_a_1429_) == 0)
{
uint64_t v___x_1447_; 
v___x_1447_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_1433_ = v___x_1447_;
goto v___jp_1432_;
}
else
{
uint64_t v_hash_1448_; 
v_hash_1448_ = lean_ctor_get_uint64(v_a_1429_, sizeof(void*)*2);
v___y_1433_ = v_hash_1448_;
goto v___jp_1432_;
}
v___jp_1432_:
{
uint64_t v___x_1434_; uint64_t v___x_1435_; uint64_t v_fold_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1434_ = 32ULL;
v___x_1435_ = lean_uint64_shift_right(v___y_1433_, v___x_1434_);
v_fold_1436_ = lean_uint64_xor(v___y_1433_, v___x_1435_);
v___x_1437_ = 16ULL;
v___x_1438_ = lean_uint64_shift_right(v_fold_1436_, v___x_1437_);
v___x_1439_ = lean_uint64_xor(v_fold_1436_, v___x_1438_);
v___x_1440_ = lean_uint64_to_usize(v___x_1439_);
v___x_1441_ = lean_usize_of_nat(v___x_1431_);
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_sub(v___x_1441_, v___x_1442_);
v___x_1444_ = lean_usize_land(v___x_1440_, v___x_1443_);
v___x_1445_ = lean_array_uget_borrowed(v_buckets_1430_, v___x_1444_);
v___x_1446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1429_, v___x_1445_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_m_1449_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1459_, lean_object* v_env_1460_, lean_object* v_forConst_1461_, lean_object* v_key_1462_, lean_object* v_realize_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v_a_1467_; lean_object* v___y_1471_; lean_object* v_base_1473_; lean_object* v_importRealizationCtx_x3f_1474_; lean_object* v_localRealizationCtxMap_1475_; uint8_t v_isExporting_1476_; lean_object* v_ctx_1478_; lean_object* v___y_1493_; 
v___x_1465_ = lean_io_get_num_heartbeats();
v_base_1473_ = lean_ctor_get(v_env_1460_, 0);
lean_inc_ref(v_base_1473_);
v_importRealizationCtx_x3f_1474_ = lean_ctor_get(v_env_1460_, 5);
lean_inc(v_importRealizationCtx_x3f_1474_);
v_localRealizationCtxMap_1475_ = lean_ctor_get(v_env_1460_, 6);
lean_inc(v_localRealizationCtxMap_1475_);
v_isExporting_1476_ = lean_ctor_get_uint8(v_env_1460_, sizeof(void*)*8);
lean_dec_ref(v_env_1460_);
if (v_isExporting_1476_ == 0)
{
lean_object* v_private_1513_; 
v_private_1513_ = lean_ctor_get(v_base_1473_, 0);
lean_inc(v_private_1513_);
lean_dec_ref(v_base_1473_);
v___y_1493_ = v_private_1513_;
goto v___jp_1492_;
}
else
{
lean_object* v_public_1514_; 
v_public_1514_ = lean_ctor_get(v_base_1473_, 1);
lean_inc(v_public_1514_);
lean_dec_ref(v_base_1473_);
v___y_1493_ = v_public_1514_;
goto v___jp_1492_;
}
v___jp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_io_set_heartbeats(v___x_1465_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1467_);
return v___x_1469_;
}
v___jp_1470_:
{
lean_object* v_a_1472_; 
v_a_1472_ = lean_ctor_get(v___y_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___y_1471_);
v_a_1467_ = v_a_1472_;
goto v___jp_1466_;
}
v___jp_1477_:
{
lean_object* v_env_1479_; lean_object* v_opts_1480_; lean_object* v_realizeMapRef_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_env_1479_ = lean_ctor_get(v_ctx_1478_, 0);
lean_inc(v_env_1479_);
v_opts_1480_ = lean_ctor_get(v_ctx_1478_, 1);
lean_inc_ref(v_opts_1480_);
v_realizeMapRef_1481_ = lean_ctor_get(v_ctx_1478_, 2);
lean_inc(v_realizeMapRef_1481_);
v___x_1482_ = lean_st_ref_get(v_realizeMapRef_1481_);
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1482_, v_inst_1459_);
lean_dec(v___x_1482_);
if (lean_obj_tag(v___x_1483_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; 
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1484_, v_key_1462_);
lean_dec(v_val_1484_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
lean_dec(v_realizeMapRef_1481_);
lean_dec_ref(v_opts_1480_);
lean_dec(v_env_1479_);
lean_dec_ref(v_ctx_1478_);
lean_dec(v_importRealizationCtx_x3f_1474_);
lean_dec_ref(v_realize_1463_);
lean_dec_ref(v_key_1462_);
lean_dec(v_forConst_1461_);
lean_dec(v_inst_1459_);
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref(v___x_1485_);
v___x_1487_ = lean_task_get_own(v_val_1486_);
v_a_1467_ = v___x_1487_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1481_, v_env_1479_, v_forConst_1461_, v_ctx_1478_, v_importRealizationCtx_x3f_1474_, v_realize_1463_, v_opts_1480_, v_key_1462_, v_inst_1459_, v___x_1488_);
lean_dec(v_realizeMapRef_1481_);
v___y_1471_ = v___x_1489_;
goto v___jp_1470_;
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v___x_1483_);
v___x_1490_ = lean_box(0);
v___x_1491_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1481_, v_env_1479_, v_forConst_1461_, v_ctx_1478_, v_importRealizationCtx_x3f_1474_, v_realize_1463_, v_opts_1480_, v_key_1462_, v_inst_1459_, v___x_1490_);
lean_dec(v_realizeMapRef_1481_);
v___y_1471_ = v___x_1491_;
goto v___jp_1470_;
}
}
v___jp_1492_:
{
lean_object* v_const2ModIdx_1494_; uint8_t v___x_1495_; 
v_const2ModIdx_1494_ = lean_ctor_get(v___y_1493_, 2);
lean_inc_ref(v_const2ModIdx_1494_);
lean_dec_ref(v___y_1493_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1494_, v_forConst_1461_);
lean_dec_ref(v_const2ModIdx_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1475_, v_forConst_1461_);
lean_dec(v_localRealizationCtxMap_1475_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v_importRealizationCtx_x3f_1474_);
lean_dec(v___x_1465_);
lean_dec_ref(v_realize_1463_);
lean_dec_ref(v_key_1462_);
v___x_1497_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1498_ = 1;
v___x_1499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1459_, v___x_1498_);
v___x_1500_ = lean_string_append(v___x_1497_, v___x_1499_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1461_, v___x_1498_);
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1506_ = lean_string_append(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
else
{
lean_object* v_val_1509_; 
v_val_1509_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v___x_1496_);
v_ctx_1478_ = v_val_1509_;
goto v___jp_1477_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1475_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1474_) == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v___x_1465_);
lean_dec_ref(v_realize_1463_);
lean_dec_ref(v_key_1462_);
lean_dec(v_forConst_1461_);
lean_dec(v_inst_1459_);
v___x_1510_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v_val_1512_; 
v_val_1512_ = lean_ctor_get(v_importRealizationCtx_x3f_1474_, 0);
lean_inc(v_val_1512_);
v_ctx_1478_ = v_val_1512_;
goto v___jp_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1515_, lean_object* v_env_1516_, lean_object* v_forConst_1517_, lean_object* v_key_1518_, lean_object* v_realize_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1515_, v_env_1516_, v_forConst_1517_, v_key_1518_, v_realize_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___f_1528_; lean_object* v___x_11419__overap_1529_; lean_object* v___x_1530_; 
v___f_1528_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_11419__overap_1529_ = lean_panic_fn_borrowed(v___f_1528_, v_msg_1522_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
v___x_1530_ = lean_apply_5(v___x_11419__overap_1529_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, lean_box(0));
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1538_, lean_object* v_inst_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
v___x_1545_ = lean_apply_5(v_realize_1538_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_inst_1539_);
lean_ctor_set(v___x_1550_, 1, v_a_1546_);
if (v_isShared_1549_ == 0)
{
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
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_inst_1539_);
v_a_1555_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1545_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1545_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1563_, lean_object* v_inst_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1563_, v_inst_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
return v_res_1570_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = l_Lean_Options_empty;
v___x_1572_ = l_Lean_Core_getMaxHeartbeats(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_unsigned_to_nat(16u);
v___x_1575_ = lean_mk_array(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1576_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1581_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1582_ = lean_unsigned_to_nat(36u);
v___x_1583_ = lean_unsigned_to_nat(2618u);
v___x_1584_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1585_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1586_ = l_mkPanicMessageWithDecl(v___x_1585_, v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1588_ = lean_unsigned_to_nat(48u);
v___x_1589_ = lean_unsigned_to_nat(2609u);
v___x_1590_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1591_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1592_ = l_mkPanicMessageWithDecl(v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_, v___x_1587_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_forConst_1595_, lean_object* v_key_1596_, lean_object* v_realize_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v_env_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_st_ref_get(v_a_1601_);
v_env_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_ref(v_env_1604_);
lean_dec(v___x_1603_);
v___x_1605_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1604_, v_forConst_1595_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_env_1604_);
lean_dec_ref(v_key_1596_);
lean_dec(v_forConst_1595_);
lean_dec(v_inst_1594_);
lean_dec(v_inst_1593_);
lean_inc(v_a_1601_);
lean_inc_ref(v_a_1600_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
v___x_1606_ = lean_apply_5(v_realize_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, lean_box(0));
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v_fileName_1608_; lean_object* v_fileMap_1609_; lean_object* v_ref_1610_; lean_object* v___f_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1607_ = lean_io_get_num_heartbeats();
v_fileName_1608_ = lean_ctor_get(v_a_1600_, 0);
v_fileMap_1609_ = lean_ctor_get(v_a_1600_, 1);
v_ref_1610_ = lean_ctor_get(v_a_1600_, 5);
lean_inc(v_inst_1594_);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1611_, 0, v_realize_1597_);
lean_closure_set(v___f_1611_, 1, v_inst_1594_);
v___x_1612_ = 0;
v___x_1613_ = l_Lean_Options_empty;
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_unsigned_to_nat(1000u);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1620_ = l_Lean_firstFrontendMacroScope;
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1609_);
lean_inc_ref(v_fileName_1608_);
v___x_1623_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1623_, 0, v_fileName_1608_);
lean_ctor_set(v___x_1623_, 1, v_fileMap_1609_);
lean_ctor_set(v___x_1623_, 2, v___x_1613_);
lean_ctor_set(v___x_1623_, 3, v___x_1614_);
lean_ctor_set(v___x_1623_, 4, v___x_1615_);
lean_ctor_set(v___x_1623_, 5, v___x_1616_);
lean_ctor_set(v___x_1623_, 6, v___x_1617_);
lean_ctor_set(v___x_1623_, 7, v___x_1618_);
lean_ctor_set(v___x_1623_, 8, v___x_1607_);
lean_ctor_set(v___x_1623_, 9, v___x_1619_);
lean_ctor_set(v___x_1623_, 10, v___x_1617_);
lean_ctor_set(v___x_1623_, 11, v___x_1620_);
lean_ctor_set(v___x_1623_, 12, v___x_1621_);
lean_ctor_set(v___x_1623_, 13, v___x_1622_);
lean_ctor_set_uint8(v___x_1623_, sizeof(void*)*14, v___x_1612_);
lean_ctor_set_uint8(v___x_1623_, sizeof(void*)*14 + 1, v___x_1612_);
v___x_1624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1624_, 0, v___f_1611_);
lean_closure_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1593_, v_env_1604_, v_forConst_1595_, v_key_1596_, v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1678_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1678_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1678_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1631_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1626_, v___x_1630_);
lean_dec(v_a_1626_);
if (lean_obj_tag(v___x_1631_) == 1)
{
lean_object* v_val_1632_; lean_object* v_res_x3f_1633_; lean_object* v_snap_x3f_1634_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v_snap_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref(v___x_1631_);
v_res_x3f_1633_ = lean_ctor_get(v_val_1632_, 0);
lean_inc_ref(v_res_x3f_1633_);
v_snap_x3f_1634_ = lean_ctor_get(v_val_1632_, 1);
lean_inc(v_snap_x3f_1634_);
lean_dec(v_val_1632_);
if (lean_obj_tag(v_snap_x3f_1634_) == 1)
{
lean_object* v_val_1668_; lean_object* v___x_1669_; 
v_val_1668_ = lean_ctor_get(v_snap_x3f_1634_, 0);
lean_inc(v_val_1668_);
lean_dec_ref(v_snap_x3f_1634_);
v___x_1669_ = l_Lean_Syntax_getRange_x3f(v_ref_1610_, v___x_1612_);
if (lean_obj_tag(v___x_1669_) == 1)
{
lean_object* v_val_1670_; lean_object* v_start_1671_; lean_object* v_stop_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_val_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_val_1670_);
lean_dec_ref(v___x_1669_);
v_start_1671_ = lean_ctor_get(v_val_1670_, 0);
lean_inc(v_start_1671_);
v_stop_1672_ = lean_ctor_get(v_val_1670_, 1);
lean_inc(v_stop_1672_);
lean_dec(v_val_1670_);
lean_inc_ref_n(v_fileMap_1609_, 2);
v___x_1673_ = l_Lean_FileMap_toPosition(v_fileMap_1609_, v_start_1671_);
lean_dec(v_start_1671_);
v___x_1674_ = l_Lean_FileMap_toPosition(v_fileMap_1609_, v_stop_1672_);
lean_dec(v_stop_1672_);
v___x_1675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1668_, v___x_1673_, v___x_1674_);
v_snap_1653_ = v___x_1675_;
v___y_1654_ = v_a_1598_;
v___y_1655_ = v_a_1599_;
v___y_1656_ = v_a_1600_;
v___y_1657_ = v_a_1601_;
goto v___jp_1652_;
}
else
{
lean_dec(v___x_1669_);
v_snap_1653_ = v_val_1668_;
v___y_1654_ = v_a_1598_;
v___y_1655_ = v_a_1599_;
v___y_1656_ = v_a_1600_;
v___y_1657_ = v_a_1601_;
goto v___jp_1652_;
}
}
else
{
lean_dec(v_snap_x3f_1634_);
v___y_1636_ = v_a_1598_;
v___y_1637_ = v_a_1599_;
v___y_1638_ = v_a_1600_;
v___y_1639_ = v_a_1601_;
goto v___jp_1635_;
}
v___jp_1635_:
{
if (lean_obj_tag(v_res_x3f_1633_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; 
lean_dec(v_inst_1594_);
v_a_1640_ = lean_ctor_get(v_res_x3f_1633_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v_res_x3f_1633_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 1);
lean_ctor_set(v___x_1628_, 0, v_a_1640_);
v___x_1642_ = v___x_1628_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v_res_x3f_1633_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v_res_x3f_1633_);
v___x_1645_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1644_, v_inst_1594_);
lean_dec(v_inst_1594_);
lean_dec(v_a_1644_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_del_object(v___x_1628_);
v___x_1646_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1647_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1646_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1647_;
}
else
{
lean_object* v_val_1648_; lean_object* v___x_1650_; 
v_val_1648_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_val_1648_);
lean_dec_ref(v___x_1645_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v_val_1648_);
v___x_1650_ = v___x_1628_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_val_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
v___jp_1652_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1621_, v_snap_1653_);
v___x_1659_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1658_, v___y_1657_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec_ref(v___x_1659_);
v___y_1636_ = v___y_1654_;
v___y_1637_ = v___y_1655_;
v___y_1638_ = v___y_1656_;
v___y_1639_ = v___y_1657_;
goto v___jp_1635_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_res_x3f_1633_);
lean_del_object(v___x_1628_);
lean_dec(v_inst_1594_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1631_);
lean_del_object(v___x_1628_);
lean_dec(v_inst_1594_);
v___x_1676_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1677_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1676_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_inst_1594_);
v_a_1679_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1681_ = v___x_1625_;
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1625_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1683_ = lean_io_error_to_string(v_a_1679_);
v___x_1684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = l_Lean_MessageData_ofFormat(v___x_1684_);
lean_inc(v_ref_1610_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_ref_1610_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1686_);
v___x_1688_ = v___x_1681_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_forConst_1693_, lean_object* v_key_1694_, lean_object* v_realize_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1691_, v_inst_1692_, v_forConst_1693_, v_key_1694_, v_realize_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1702_, lean_object* v_vals_1703_, lean_object* v_i_1704_, lean_object* v_k_1705_){
_start:
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = lean_array_get_size(v_keys_1702_);
v___x_1707_ = lean_nat_dec_lt(v_i_1704_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
lean_dec(v_i_1704_);
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
else
{
lean_object* v_k_x27_1709_; uint8_t v___x_1710_; 
v_k_x27_1709_ = lean_array_fget_borrowed(v_keys_1702_, v_i_1704_);
v___x_1710_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1705_, v_k_x27_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_nat_add(v_i_1704_, v___x_1711_);
lean_dec(v_i_1704_);
v_i_1704_ = v___x_1712_;
goto _start;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_array_fget_borrowed(v_vals_1703_, v_i_1704_);
lean_dec(v_i_1704_);
lean_inc(v___x_1714_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1716_, lean_object* v_vals_1717_, lean_object* v_i_1718_, lean_object* v_k_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1716_, v_vals_1717_, v_i_1718_, v_k_1719_);
lean_dec_ref(v_k_1719_);
lean_dec_ref(v_vals_1717_);
lean_dec_ref(v_keys_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1721_, size_t v_x_1722_, lean_object* v_x_1723_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_object* v_es_1724_; lean_object* v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v_j_1729_; lean_object* v___x_1730_; 
v_es_1724_ = lean_ctor_get(v_x_1721_, 0);
v___x_1725_ = lean_box(2);
v___x_1726_ = ((size_t)5ULL);
v___x_1727_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1728_ = lean_usize_land(v_x_1722_, v___x_1727_);
v_j_1729_ = lean_usize_to_nat(v___x_1728_);
v___x_1730_ = lean_array_get_borrowed(v___x_1725_, v_es_1724_, v_j_1729_);
lean_dec(v_j_1729_);
switch(lean_obj_tag(v___x_1730_))
{
case 0:
{
lean_object* v_key_1731_; lean_object* v_val_1732_; uint8_t v___x_1733_; 
v_key_1731_ = lean_ctor_get(v___x_1730_, 0);
v_val_1732_ = lean_ctor_get(v___x_1730_, 1);
v___x_1733_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1723_, v_key_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_box(0);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
lean_inc(v_val_1732_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_val_1732_);
return v___x_1735_;
}
}
case 1:
{
lean_object* v_node_1736_; size_t v___x_1737_; 
v_node_1736_ = lean_ctor_get(v___x_1730_, 0);
v___x_1737_ = lean_usize_shift_right(v_x_1722_, v___x_1726_);
v_x_1721_ = v_node_1736_;
v_x_1722_ = v___x_1737_;
goto _start;
}
default: 
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_box(0);
return v___x_1739_;
}
}
}
else
{
lean_object* v_ks_1740_; lean_object* v_vs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_ks_1740_ = lean_ctor_get(v_x_1721_, 0);
v_vs_1741_ = lean_ctor_get(v_x_1721_, 1);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1740_, v_vs_1741_, v___x_1742_, v_x_1723_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
size_t v_x_14055__boxed_1747_; lean_object* v_res_1748_; 
v_x_14055__boxed_1747_ = lean_unbox_usize(v_x_1745_);
lean_dec(v_x_1745_);
v_res_1748_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1744_, v_x_14055__boxed_1747_, v_x_1746_);
lean_dec_ref(v_x_1746_);
lean_dec_ref(v_x_1744_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
uint64_t v_configKey_1751_; lean_object* v_expr_1752_; lean_object* v_nargs_x3f_1753_; uint64_t v___x_1754_; uint64_t v___y_1756_; 
v_configKey_1751_ = lean_ctor_get_uint64(v_x_1750_, sizeof(void*)*2);
v_expr_1752_ = lean_ctor_get(v_x_1750_, 0);
v_nargs_x3f_1753_ = lean_ctor_get(v_x_1750_, 1);
v___x_1754_ = l_Lean_Expr_hash(v_expr_1752_);
if (lean_obj_tag(v_nargs_x3f_1753_) == 0)
{
uint64_t v___x_1761_; 
v___x_1761_ = 11ULL;
v___y_1756_ = v___x_1761_;
goto v___jp_1755_;
}
else
{
lean_object* v_val_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; 
v_val_1762_ = lean_ctor_get(v_nargs_x3f_1753_, 0);
v___x_1763_ = lean_uint64_of_nat(v_val_1762_);
v___x_1764_ = 13ULL;
v___x_1765_ = lean_uint64_mix_hash(v___x_1763_, v___x_1764_);
v___y_1756_ = v___x_1765_;
goto v___jp_1755_;
}
v___jp_1755_:
{
uint64_t v___x_1757_; uint64_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = lean_uint64_mix_hash(v___x_1754_, v___y_1756_);
v___x_1758_ = lean_uint64_mix_hash(v_configKey_1751_, v___x_1757_);
v___x_1759_ = lean_uint64_to_usize(v___x_1758_);
v___x_1760_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1749_, v___x_1759_, v_x_1750_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1766_, v_x_1767_);
lean_dec_ref(v_x_1767_);
lean_dec_ref(v_x_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_ks_1773_; lean_object* v_vs_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1798_; 
v_ks_1773_ = lean_ctor_get(v_x_1769_, 0);
v_vs_1774_ = lean_ctor_get(v_x_1769_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_x_1769_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1776_ = v_x_1769_;
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_vs_1774_);
lean_inc(v_ks_1773_);
lean_dec(v_x_1769_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_array_get_size(v_ks_1773_);
v___x_1779_ = lean_nat_dec_lt(v_x_1770_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec(v_x_1770_);
v___x_1780_ = lean_array_push(v_ks_1773_, v_x_1771_);
v___x_1781_ = lean_array_push(v_vs_1774_, v_x_1772_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v___x_1781_);
lean_ctor_set(v___x_1776_, 0, v___x_1780_);
v___x_1783_ = v___x_1776_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
else
{
lean_object* v_k_x27_1785_; uint8_t v___x_1786_; 
v_k_x27_1785_ = lean_array_fget_borrowed(v_ks_1773_, v_x_1770_);
v___x_1786_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1771_, v_k_x27_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1788_; 
if (v_isShared_1777_ == 0)
{
v___x_1788_ = v___x_1776_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_ks_1773_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_vs_1774_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_add(v_x_1770_, v___x_1789_);
lean_dec(v_x_1770_);
v_x_1769_ = v___x_1788_;
v_x_1770_ = v___x_1790_;
goto _start;
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1793_ = lean_array_fset(v_ks_1773_, v_x_1770_, v_x_1771_);
v___x_1794_ = lean_array_fset(v_vs_1774_, v_x_1770_, v_x_1772_);
lean_dec(v_x_1770_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v___x_1794_);
lean_ctor_set(v___x_1776_, 0, v___x_1793_);
v___x_1796_ = v___x_1776_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1799_, lean_object* v_k_1800_, lean_object* v_v_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1799_, v___x_1802_, v_k_1800_, v_v_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1805_, size_t v_x_1806_, size_t v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v_es_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; lean_object* v_j_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_es_1810_ = lean_ctor_get(v_x_1805_, 0);
v___x_1811_ = ((size_t)5ULL);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
v___x_1814_ = lean_usize_land(v_x_1806_, v___x_1813_);
v_j_1815_ = lean_usize_to_nat(v___x_1814_);
v___x_1816_ = lean_array_get_size(v_es_1810_);
v___x_1817_ = lean_nat_dec_lt(v_j_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_j_1815_);
lean_dec(v_x_1809_);
lean_dec_ref(v_x_1808_);
return v_x_1805_;
}
else
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1854_; 
lean_inc_ref(v_es_1810_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1805_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_x_1805_, 0);
lean_dec(v_unused_1855_);
v___x_1819_ = v_x_1805_;
v_isShared_1820_ = v_isSharedCheck_1854_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_x_1805_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1854_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_v_1821_; lean_object* v___x_1822_; lean_object* v_xs_x27_1823_; lean_object* v___y_1825_; 
v_v_1821_ = lean_array_fget(v_es_1810_, v_j_1815_);
v___x_1822_ = lean_box(0);
v_xs_x27_1823_ = lean_array_fset(v_es_1810_, v_j_1815_, v___x_1822_);
switch(lean_obj_tag(v_v_1821_))
{
case 0:
{
lean_object* v_key_1830_; lean_object* v_val_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1841_; 
v_key_1830_ = lean_ctor_get(v_v_1821_, 0);
v_val_1831_ = lean_ctor_get(v_v_1821_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_v_1821_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1833_ = v_v_1821_;
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_val_1831_);
lean_inc(v_key_1830_);
lean_dec(v_v_1821_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1808_, v_key_1830_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_del_object(v___x_1833_);
v___x_1836_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1830_, v_val_1831_, v_x_1808_, v_x_1809_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
v___y_1825_ = v___x_1837_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_val_1831_);
lean_dec(v_key_1830_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v_x_1809_);
lean_ctor_set(v___x_1833_, 0, v_x_1808_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_x_1808_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_x_1809_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1825_ = v___x_1839_;
goto v___jp_1824_;
}
}
}
}
case 1:
{
lean_object* v_node_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
v_node_1842_ = lean_ctor_get(v_v_1821_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_v_1821_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1844_ = v_v_1821_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_node_1842_);
lean_dec(v_v_1821_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1846_ = lean_usize_shift_right(v_x_1806_, v___x_1811_);
v___x_1847_ = lean_usize_add(v_x_1807_, v___x_1812_);
v___x_1848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1842_, v___x_1846_, v___x_1847_, v_x_1808_, v_x_1809_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1848_);
v___x_1850_ = v___x_1844_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
v___y_1825_ = v___x_1850_;
goto v___jp_1824_;
}
}
}
default: 
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_x_1808_);
lean_ctor_set(v___x_1853_, 1, v_x_1809_);
v___y_1825_ = v___x_1853_;
goto v___jp_1824_;
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_array_fset(v_xs_x27_1823_, v_j_1815_, v___y_1825_);
lean_dec(v_j_1815_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
else
{
lean_object* v_ks_1856_; lean_object* v_vs_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1877_; 
v_ks_1856_ = lean_ctor_get(v_x_1805_, 0);
v_vs_1857_ = lean_ctor_get(v_x_1805_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1805_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1859_ = v_x_1805_;
v_isShared_1860_ = v_isSharedCheck_1877_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_vs_1857_);
lean_inc(v_ks_1856_);
lean_dec(v_x_1805_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1877_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_ks_1856_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_vs_1857_);
v___x_1862_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v_newNode_1863_; uint8_t v___y_1865_; size_t v___x_1871_; uint8_t v___x_1872_; 
v_newNode_1863_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1862_, v_x_1808_, v_x_1809_);
v___x_1871_ = ((size_t)7ULL);
v___x_1872_ = lean_usize_dec_le(v___x_1871_, v_x_1807_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1873_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1863_);
v___x_1874_ = lean_unsigned_to_nat(4u);
v___x_1875_ = lean_nat_dec_lt(v___x_1873_, v___x_1874_);
lean_dec(v___x_1873_);
v___y_1865_ = v___x_1875_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1872_;
goto v___jp_1864_;
}
v___jp_1864_:
{
if (v___y_1865_ == 0)
{
lean_object* v_ks_1866_; lean_object* v_vs_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_ks_1866_ = lean_ctor_get(v_newNode_1863_, 0);
lean_inc_ref(v_ks_1866_);
v_vs_1867_ = lean_ctor_get(v_newNode_1863_, 1);
lean_inc_ref(v_vs_1867_);
lean_dec_ref(v_newNode_1863_);
v___x_1868_ = lean_unsigned_to_nat(0u);
v___x_1869_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1807_, v_ks_1866_, v_vs_1867_, v___x_1868_, v___x_1869_);
lean_dec_ref(v_vs_1867_);
lean_dec_ref(v_ks_1866_);
return v___x_1870_;
}
else
{
return v_newNode_1863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1878_, lean_object* v_keys_1879_, lean_object* v_vals_1880_, lean_object* v_i_1881_, lean_object* v_entries_1882_){
_start:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = lean_array_get_size(v_keys_1879_);
v___x_1884_ = lean_nat_dec_lt(v_i_1881_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_dec(v_i_1881_);
return v_entries_1882_;
}
else
{
lean_object* v_k_1885_; uint64_t v_configKey_1886_; lean_object* v_expr_1887_; lean_object* v_nargs_x3f_1888_; lean_object* v_v_1889_; uint64_t v___x_1890_; uint64_t v___y_1892_; 
v_k_1885_ = lean_array_fget_borrowed(v_keys_1879_, v_i_1881_);
v_configKey_1886_ = lean_ctor_get_uint64(v_k_1885_, sizeof(void*)*2);
v_expr_1887_ = lean_ctor_get(v_k_1885_, 0);
v_nargs_x3f_1888_ = lean_ctor_get(v_k_1885_, 1);
v_v_1889_ = lean_array_fget_borrowed(v_vals_1880_, v_i_1881_);
v___x_1890_ = l_Lean_Expr_hash(v_expr_1887_);
if (lean_obj_tag(v_nargs_x3f_1888_) == 0)
{
uint64_t v___x_1905_; 
v___x_1905_ = 11ULL;
v___y_1892_ = v___x_1905_;
goto v___jp_1891_;
}
else
{
lean_object* v_val_1906_; uint64_t v___x_1907_; uint64_t v___x_1908_; uint64_t v___x_1909_; 
v_val_1906_ = lean_ctor_get(v_nargs_x3f_1888_, 0);
v___x_1907_ = lean_uint64_of_nat(v_val_1906_);
v___x_1908_ = 13ULL;
v___x_1909_ = lean_uint64_mix_hash(v___x_1907_, v___x_1908_);
v___y_1892_ = v___x_1909_;
goto v___jp_1891_;
}
v___jp_1891_:
{
uint64_t v___x_1893_; uint64_t v___x_1894_; size_t v_h_1895_; size_t v___x_1896_; lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v_h_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1893_ = lean_uint64_mix_hash(v___x_1890_, v___y_1892_);
v___x_1894_ = lean_uint64_mix_hash(v_configKey_1886_, v___x_1893_);
v_h_1895_ = lean_uint64_to_usize(v___x_1894_);
v___x_1896_ = ((size_t)5ULL);
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_sub(v_depth_1878_, v___x_1898_);
v___x_1900_ = lean_usize_mul(v___x_1896_, v___x_1899_);
v_h_1901_ = lean_usize_shift_right(v_h_1895_, v___x_1900_);
v___x_1902_ = lean_nat_add(v_i_1881_, v___x_1897_);
lean_dec(v_i_1881_);
lean_inc(v_v_1889_);
lean_inc(v_k_1885_);
v___x_1903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1882_, v_h_1901_, v_depth_1878_, v_k_1885_, v_v_1889_);
v_i_1881_ = v___x_1902_;
v_entries_1882_ = v___x_1903_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1910_, lean_object* v_keys_1911_, lean_object* v_vals_1912_, lean_object* v_i_1913_, lean_object* v_entries_1914_){
_start:
{
size_t v_depth_boxed_1915_; lean_object* v_res_1916_; 
v_depth_boxed_1915_ = lean_unbox_usize(v_depth_1910_);
lean_dec(v_depth_1910_);
v_res_1916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1915_, v_keys_1911_, v_vals_1912_, v_i_1913_, v_entries_1914_);
lean_dec_ref(v_vals_1912_);
lean_dec_ref(v_keys_1911_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
size_t v_x_14234__boxed_1922_; size_t v_x_14235__boxed_1923_; lean_object* v_res_1924_; 
v_x_14234__boxed_1922_ = lean_unbox_usize(v_x_1918_);
lean_dec(v_x_1918_);
v_x_14235__boxed_1923_ = lean_unbox_usize(v_x_1919_);
lean_dec(v_x_1919_);
v_res_1924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1917_, v_x_14234__boxed_1922_, v_x_14235__boxed_1923_, v_x_1920_, v_x_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
uint64_t v_configKey_1928_; lean_object* v_expr_1929_; lean_object* v_nargs_x3f_1930_; uint64_t v___x_1931_; uint64_t v___y_1933_; 
v_configKey_1928_ = lean_ctor_get_uint64(v_x_1926_, sizeof(void*)*2);
v_expr_1929_ = lean_ctor_get(v_x_1926_, 0);
v_nargs_x3f_1930_ = lean_ctor_get(v_x_1926_, 1);
v___x_1931_ = l_Lean_Expr_hash(v_expr_1929_);
if (lean_obj_tag(v_nargs_x3f_1930_) == 0)
{
uint64_t v___x_1939_; 
v___x_1939_ = 11ULL;
v___y_1933_ = v___x_1939_;
goto v___jp_1932_;
}
else
{
lean_object* v_val_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; 
v_val_1940_ = lean_ctor_get(v_nargs_x3f_1930_, 0);
v___x_1941_ = lean_uint64_of_nat(v_val_1940_);
v___x_1942_ = 13ULL;
v___x_1943_ = lean_uint64_mix_hash(v___x_1941_, v___x_1942_);
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
v___jp_1932_:
{
uint64_t v___x_1934_; uint64_t v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1934_ = lean_uint64_mix_hash(v___x_1931_, v___y_1933_);
v___x_1935_ = lean_uint64_mix_hash(v_configKey_1928_, v___x_1934_);
v___x_1936_ = lean_uint64_to_usize(v___x_1935_);
v___x_1937_ = ((size_t)1ULL);
v___x_1938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1925_, v___x_1936_, v___x_1937_, v_x_1926_, v_x_1927_);
return v___x_1938_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1944_){
_start:
{
if (lean_obj_tag(v_x_1944_) == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = 0;
return v___x_1945_;
}
else
{
lean_object* v_head_1946_; lean_object* v_tail_1947_; uint8_t v___x_1948_; 
v_head_1946_ = lean_ctor_get(v_x_1944_, 0);
v_tail_1947_ = lean_ctor_get(v_x_1944_, 1);
v___x_1948_ = l_Lean_Level_hasMVar(v_head_1946_);
if (v___x_1948_ == 0)
{
v_x_1944_ = v_tail_1947_;
goto _start;
}
else
{
return v___x_1948_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1950_);
lean_dec(v_x_1950_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1955_, lean_object* v_maxArgs_x3f_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
lean_inc(v_maxArgs_x3f_1956_);
lean_inc_ref(v_fn_1955_);
v___x_1962_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1955_, v_maxArgs_x3f_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2027_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_2027_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2027_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_finfo_1968_; lean_object* v___y_1969_; lean_object* v___x_2001_; lean_object* v_cache_2002_; lean_object* v_funInfo_2003_; lean_object* v___x_2004_; 
v___x_2001_ = lean_st_ref_get(v_a_1958_);
v_cache_2002_ = lean_ctor_get(v___x_2001_, 1);
lean_inc_ref(v_cache_2002_);
lean_dec(v___x_2001_);
v_funInfo_2003_ = lean_ctor_get(v_cache_2002_, 1);
lean_inc_ref(v_funInfo_2003_);
lean_dec_ref(v_cache_2002_);
v___x_2004_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_2003_, v_a_1963_);
lean_dec_ref(v_funInfo_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___f_2005_; lean_object* v___f_2006_; 
v___f_2005_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1956_);
lean_inc_ref(v_fn_1955_);
v___f_2006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2006_, 0, v_fn_1955_);
lean_closure_set(v___f_2006_, 1, v_maxArgs_x3f_1956_);
lean_closure_set(v___f_2006_, 2, v___f_2005_);
if (lean_obj_tag(v_fn_1955_) == 4)
{
lean_object* v_declName_2007_; lean_object* v_us_2008_; uint8_t v___x_2009_; 
v_declName_2007_ = lean_ctor_get(v_fn_1955_, 0);
v_us_2008_ = lean_ctor_get(v_fn_1955_, 1);
v___x_2009_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_inc(v_us_2008_);
lean_inc_n(v_declName_2007_, 2);
lean_dec_ref(v_fn_1955_);
v___x_2010_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_2011_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_2012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2012_, 0, v_declName_2007_);
lean_ctor_set(v___x_2012_, 1, v_us_2008_);
lean_ctor_set(v___x_2012_, 2, v_maxArgs_x3f_1956_);
v___x_2013_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_2010_, v___x_2011_, v_declName_2007_, v___x_2012_, v___f_2006_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v_finfo_1968_ = v_a_2014_;
v___y_1969_ = v_a_1958_;
goto v___jp_1967_;
}
else
{
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref(v___f_2006_);
lean_inc(v_a_1960_);
lean_inc_ref(v_a_1959_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1957_);
v___x_2015_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1955_, v_maxArgs_x3f_1956_, v___f_2005_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v_finfo_1968_ = v_a_2016_;
v___y_1969_ = v_a_1958_;
goto v___jp_1967_;
}
else
{
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2017_; 
lean_dec_ref(v___f_2006_);
lean_inc(v_a_1960_);
lean_inc_ref(v_a_1959_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1957_);
v___x_2017_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1955_, v_maxArgs_x3f_1956_, v___f_2005_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2017_);
v_finfo_1968_ = v_a_2018_;
v___y_1969_ = v_a_1958_;
goto v___jp_1967_;
}
else
{
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
return v___x_2017_;
}
}
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
lean_dec(v_maxArgs_x3f_1956_);
lean_dec_ref(v_fn_1955_);
v_val_2019_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2004_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v___x_2004_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set_tag(v___x_2021_, 0);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_val_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
v___jp_1967_:
{
lean_object* v___x_1970_; lean_object* v_cache_1971_; lean_object* v_mctx_1972_; lean_object* v_zetaDeltaFVarIds_1973_; lean_object* v_postponed_1974_; lean_object* v_diag_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2000_; 
v___x_1970_ = lean_st_ref_take(v___y_1969_);
v_cache_1971_ = lean_ctor_get(v___x_1970_, 1);
v_mctx_1972_ = lean_ctor_get(v___x_1970_, 0);
v_zetaDeltaFVarIds_1973_ = lean_ctor_get(v___x_1970_, 2);
v_postponed_1974_ = lean_ctor_get(v___x_1970_, 3);
v_diag_1975_ = lean_ctor_get(v___x_1970_, 4);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1977_ = v___x_1970_;
v_isShared_1978_ = v_isSharedCheck_2000_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_diag_1975_);
lean_inc(v_postponed_1974_);
lean_inc(v_zetaDeltaFVarIds_1973_);
lean_inc(v_cache_1971_);
lean_inc(v_mctx_1972_);
lean_dec(v___x_1970_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2000_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_inferType_1979_; lean_object* v_funInfo_1980_; lean_object* v_synthInstance_1981_; lean_object* v_whnf_1982_; lean_object* v_defEqTrans_1983_; lean_object* v_defEqPerm_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1999_; 
v_inferType_1979_ = lean_ctor_get(v_cache_1971_, 0);
v_funInfo_1980_ = lean_ctor_get(v_cache_1971_, 1);
v_synthInstance_1981_ = lean_ctor_get(v_cache_1971_, 2);
v_whnf_1982_ = lean_ctor_get(v_cache_1971_, 3);
v_defEqTrans_1983_ = lean_ctor_get(v_cache_1971_, 4);
v_defEqPerm_1984_ = lean_ctor_get(v_cache_1971_, 5);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_cache_1971_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1986_ = v_cache_1971_;
v_isShared_1987_ = v_isSharedCheck_1999_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_defEqPerm_1984_);
lean_inc(v_defEqTrans_1983_);
lean_inc(v_whnf_1982_);
lean_inc(v_synthInstance_1981_);
lean_inc(v_funInfo_1980_);
lean_inc(v_inferType_1979_);
lean_dec(v_cache_1971_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1999_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_inc_ref(v_finfo_1968_);
v___x_1988_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1980_, v_a_1963_, v_finfo_1968_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_inferType_1979_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_synthInstance_1981_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_whnf_1982_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v_defEqTrans_1983_);
lean_ctor_set(v_reuseFailAlloc_1998_, 5, v_defEqPerm_1984_);
v___x_1990_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_1990_);
v___x_1992_ = v___x_1977_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_mctx_1972_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_zetaDeltaFVarIds_1973_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_postponed_1974_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v_diag_1975_);
v___x_1992_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_st_ref_set(v___y_1969_, v___x_1992_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_finfo_1968_);
v___x_1995_ = v___x_1965_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_finfo_1968_);
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
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_maxArgs_x3f_1956_);
lean_dec_ref(v_fn_1955_);
v_a_2028_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1962_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1962_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_2036_, lean_object* v_maxArgs_x3f_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2036_, v_maxArgs_x3f_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_2044_, lean_object* v_k_2045_, lean_object* v_t_2046_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_2045_, v_t_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2048_, lean_object* v_k_2049_, lean_object* v_t_2050_){
_start:
{
uint8_t v_res_2051_; lean_object* v_r_2052_; 
v_res_2051_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2048_, v_k_2049_, v_t_2050_);
lean_dec(v_t_2050_);
lean_dec(v_k_2049_);
v_r_2052_ = lean_box(v_res_2051_);
return v_r_2052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2053_, lean_object* v_val_2054_, lean_object* v___x_2055_, lean_object* v_fvars_2056_, uint8_t v___y_2057_, lean_object* v_inst_2058_, lean_object* v_R_2059_, lean_object* v_a_2060_, lean_object* v_b_2061_, lean_object* v_c_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2053_, v_val_2054_, v___x_2055_, v_fvars_2056_, v___y_2057_, v_a_2060_, v_b_2061_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2069_, lean_object* v_val_2070_, lean_object* v___x_2071_, lean_object* v_fvars_2072_, lean_object* v___y_2073_, lean_object* v_inst_2074_, lean_object* v_R_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_, lean_object* v_c_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v___y_14589__boxed_2084_; lean_object* v_res_2085_; 
v___y_14589__boxed_2084_ = lean_unbox(v___y_2073_);
v_res_2085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2069_, v_val_2070_, v___x_2071_, v_fvars_2072_, v___y_14589__boxed_2084_, v_inst_2074_, v_R_2075_, v_a_2076_, v_b_2077_, v_c_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_fvars_2072_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v_val_2070_);
lean_dec(v_upperBound_2069_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2086_, lean_object* v_fvars_2087_, lean_object* v_inst_2088_, lean_object* v_R_2089_, lean_object* v_a_2090_, lean_object* v_b_2091_, lean_object* v_c_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2086_, v_fvars_2087_, v_a_2090_, v_b_2091_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2099_, lean_object* v_fvars_2100_, lean_object* v_inst_2101_, lean_object* v_R_2102_, lean_object* v_a_2103_, lean_object* v_b_2104_, lean_object* v_c_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2099_, v_fvars_2100_, v_inst_2101_, v_R_2102_, v_a_2103_, v_b_2104_, v_c_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v_fvars_2100_);
lean_dec(v_upperBound_2099_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2113_, v_x_2114_, v_x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2117_, lean_object* v_x_2118_, lean_object* v_x_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2118_, v_x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2121_, v_x_2122_, v_x_2123_);
lean_dec_ref(v_x_2123_);
lean_dec_ref(v_x_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2125_, lean_object* v_msg_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2133_, v_msg_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_forConst_2144_, lean_object* v_key_2145_, lean_object* v_realize_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2142_, v_inst_2143_, v_forConst_2144_, v_key_2145_, v_realize_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_forConst_2156_, lean_object* v_key_2157_, lean_object* v_realize_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2153_, v_inst_2154_, v_inst_2155_, v_forConst_2156_, v_key_2157_, v_realize_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, size_t v_x_2167_, size_t v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2166_, v_x_2167_, v_x_2168_, v_x_2169_, v_x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
size_t v_x_14686__boxed_2178_; size_t v_x_14687__boxed_2179_; lean_object* v_res_2180_; 
v_x_14686__boxed_2178_ = lean_unbox_usize(v_x_2174_);
lean_dec(v_x_2174_);
v_x_14687__boxed_2179_ = lean_unbox_usize(v_x_2175_);
lean_dec(v_x_2175_);
v_res_2180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2172_, v_x_2173_, v_x_14686__boxed_2178_, v_x_14687__boxed_2179_, v_x_2176_, v_x_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2181_, lean_object* v_x_2182_, size_t v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2182_, v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
size_t v_x_14703__boxed_2190_; lean_object* v_res_2191_; 
v_x_14703__boxed_2190_ = lean_unbox_usize(v_x_2188_);
lean_dec(v_x_2188_);
v_res_2191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2186_, v_x_2187_, v_x_14703__boxed_2190_, v_x_2189_);
lean_dec_ref(v_x_2189_);
lean_dec_ref(v_x_2187_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2192_, lean_object* v_n_2193_, lean_object* v_k_2194_, lean_object* v_v_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2193_, v_k_2194_, v_v_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2197_, size_t v_depth_2198_, lean_object* v_keys_2199_, lean_object* v_vals_2200_, lean_object* v_heq_2201_, lean_object* v_i_2202_, lean_object* v_entries_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2198_, v_keys_2199_, v_vals_2200_, v_i_2202_, v_entries_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_depth_2206_, lean_object* v_keys_2207_, lean_object* v_vals_2208_, lean_object* v_heq_2209_, lean_object* v_i_2210_, lean_object* v_entries_2211_){
_start:
{
size_t v_depth_boxed_2212_; lean_object* v_res_2213_; 
v_depth_boxed_2212_ = lean_unbox_usize(v_depth_2206_);
lean_dec(v_depth_2206_);
v_res_2213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2205_, v_depth_boxed_2212_, v_keys_2207_, v_vals_2208_, v_heq_2209_, v_i_2210_, v_entries_2211_);
lean_dec_ref(v_vals_2208_);
lean_dec_ref(v_keys_2207_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2214_, lean_object* v_keys_2215_, lean_object* v_vals_2216_, lean_object* v_heq_2217_, lean_object* v_i_2218_, lean_object* v_k_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2215_, v_vals_2216_, v_i_2218_, v_k_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_keys_2222_, lean_object* v_vals_2223_, lean_object* v_heq_2224_, lean_object* v_i_2225_, lean_object* v_k_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2221_, v_keys_2222_, v_vals_2223_, v_heq_2224_, v_i_2225_, v_k_2226_);
lean_dec_ref(v_k_2226_);
lean_dec_ref(v_vals_2223_);
lean_dec_ref(v_keys_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2229_, v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2232_, v_x_2233_, v_x_2234_);
lean_dec_ref(v_x_2234_);
lean_dec_ref(v_x_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2237_, v_x_2238_, v_x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2241_, lean_object* v_m_2242_, lean_object* v_a_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2242_, v_a_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_m_2246_, lean_object* v_a_2247_){
_start:
{
uint8_t v_res_2248_; lean_object* v_r_2249_; 
v_res_2248_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2245_, v_m_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_m_2246_);
v_r_2249_ = lean_box(v_res_2248_);
return v_r_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2251_, v_x_2252_, v_x_2253_, v_x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2256_, lean_object* v_x_2257_, size_t v_x_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2257_, v_x_2258_, v_x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2261_, lean_object* v_x_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_){
_start:
{
size_t v_x_14748__boxed_2265_; lean_object* v_res_2266_; 
v_x_14748__boxed_2265_ = lean_unbox_usize(v_x_2263_);
lean_dec(v_x_2263_);
v_res_2266_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2261_, v_x_2262_, v_x_14748__boxed_2265_, v_x_2264_);
lean_dec_ref(v_x_2264_);
lean_dec_ref(v_x_2262_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2267_, lean_object* v_x_2268_, size_t v_x_2269_, size_t v_x_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2268_, v_x_2269_, v_x_2270_, v_x_2271_, v_x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
size_t v_x_14759__boxed_2280_; size_t v_x_14760__boxed_2281_; lean_object* v_res_2282_; 
v_x_14759__boxed_2280_ = lean_unbox_usize(v_x_2276_);
lean_dec(v_x_2276_);
v_x_14760__boxed_2281_ = lean_unbox_usize(v_x_2277_);
lean_dec(v_x_2277_);
v_res_2282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2274_, v_x_2275_, v_x_14759__boxed_2280_, v_x_14760__boxed_2281_, v_x_2278_, v_x_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2283_, lean_object* v_a_2284_, lean_object* v_x_2285_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2284_, v_x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2287_, lean_object* v_a_2288_, lean_object* v_x_2289_){
_start:
{
uint8_t v_res_2290_; lean_object* v_r_2291_; 
v_res_2290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2287_, v_a_2288_, v_x_2289_);
lean_dec(v_x_2289_);
lean_dec(v_a_2288_);
v_r_2291_ = lean_box(v_res_2290_);
return v_r_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2292_, lean_object* v_keys_2293_, lean_object* v_vals_2294_, lean_object* v_heq_2295_, lean_object* v_i_2296_, lean_object* v_k_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2293_, v_vals_2294_, v_i_2296_, v_k_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2299_, lean_object* v_keys_2300_, lean_object* v_vals_2301_, lean_object* v_heq_2302_, lean_object* v_i_2303_, lean_object* v_k_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2299_, v_keys_2300_, v_vals_2301_, v_heq_2302_, v_i_2303_, v_k_2304_);
lean_dec_ref(v_k_2304_);
lean_dec_ref(v_vals_2301_);
lean_dec_ref(v_keys_2300_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2306_, lean_object* v_n_2307_, lean_object* v_k_2308_, lean_object* v_v_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2307_, v_k_2308_, v_v_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2311_, size_t v_depth_2312_, lean_object* v_keys_2313_, lean_object* v_vals_2314_, lean_object* v_heq_2315_, lean_object* v_i_2316_, lean_object* v_entries_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2312_, v_keys_2313_, v_vals_2314_, v_i_2316_, v_entries_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2319_, lean_object* v_depth_2320_, lean_object* v_keys_2321_, lean_object* v_vals_2322_, lean_object* v_heq_2323_, lean_object* v_i_2324_, lean_object* v_entries_2325_){
_start:
{
size_t v_depth_boxed_2326_; lean_object* v_res_2327_; 
v_depth_boxed_2326_ = lean_unbox_usize(v_depth_2320_);
lean_dec(v_depth_2320_);
v_res_2327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2319_, v_depth_boxed_2326_, v_keys_2321_, v_vals_2322_, v_heq_2323_, v_i_2324_, v_entries_2325_);
lean_dec_ref(v_vals_2322_);
lean_dec_ref(v_keys_2321_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2329_, v_x_2330_, v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2334_, lean_object* v_maxArgs_x3f_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2334_, v_maxArgs_x3f_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2342_, lean_object* v_maxArgs_x3f_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_getFunInfo(v_fn_2342_, v_maxArgs_x3f_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2350_, lean_object* v_nargs_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_nargs_2351_);
v___x_2358_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2350_, v___x_2357_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2359_, lean_object* v_nargs_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2359_, v_nargs_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2367_){
_start:
{
lean_object* v_paramInfo_2368_; lean_object* v___x_2369_; 
v_paramInfo_2368_ = lean_ctor_get(v_info_2367_, 0);
v___x_2369_ = lean_array_get_size(v_paramInfo_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Meta_FunInfo_getArity(v_info_2370_);
lean_dec_ref(v_info_2370_);
return v_res_2371_;
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
