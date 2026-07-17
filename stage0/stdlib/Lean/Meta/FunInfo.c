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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* v___f_614_; lean_object* v___x_9819__overap_615_; lean_object* v___x_616_; 
v___f_614_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9819__overap_615_ = lean_panic_fn_borrowed(v___f_614_, v_msg_608_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___x_616_ = lean_apply_5(v___x_9819__overap_615_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, lean_box(0));
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
uint8_t v___y_12270__boxed_787_; lean_object* v_res_788_; 
v___y_12270__boxed_787_ = lean_unbox(v___y_779_);
v_res_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_775_, v_val_776_, v___x_777_, v_fvars_778_, v___y_12270__boxed_787_, v_a_780_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
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
lean_object* v_a_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_975_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v_fst_865_ = lean_ctor_get(v_b_849_, 0);
v_snd_866_ = lean_ctor_get(v_b_849_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_b_849_);
if (v_isSharedCheck_975_ == 0)
{
v___x_868_ = v_b_849_;
v_isShared_869_ = v_isSharedCheck_975_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
lean_dec(v_b_849_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_975_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___y_874_; lean_object* v___y_875_; uint8_t v___y_876_; uint8_t v___y_956_; 
v___f_870_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
v___x_871_ = l_Lean_LocalDecl_type(v_a_864_);
v___x_872_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_847_, v___x_871_);
if (lean_obj_tag(v_snd_866_) == 0)
{
lean_object* v___f_971_; lean_object* v___x_972_; 
lean_inc_ref(v_snd_866_);
v___f_971_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_971_, 0, v_snd_866_);
v___x_972_ = lean_find_expr(v___f_971_, v___x_871_);
lean_dec_ref(v___f_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
uint8_t v___x_973_; 
v___x_973_ = 0;
v___y_956_ = v___x_973_;
goto v___jp_955_;
}
else
{
lean_dec_ref_known(v___x_972_, 1);
v___y_956_ = v___x_860_;
goto v___jp_955_;
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = 0;
v___y_956_ = v___x_974_;
goto v___jp_955_;
}
v___jp_873_:
{
lean_object* v___x_877_; 
lean_inc_ref(v___x_871_);
v___x_877_ = l_Lean_Meta_isProp(v___x_871_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; uint8_t v___x_879_; lean_object* v___x_880_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = 0;
lean_inc_ref(v___x_871_);
v___x_880_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_871_, v___f_870_, v___x_879_, v___x_879_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_865_, v___x_872_);
v___x_883_ = l_Lean_LocalDecl_binderInfo(v_a_864_);
lean_dec(v_a_864_);
v___x_884_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_884_, 0, v___x_872_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_883_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 1, v___x_879_);
v___x_885_ = lean_unbox(v_a_878_);
lean_dec(v_a_878_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 2, v___x_885_);
v___x_886_ = lean_unbox(v_a_881_);
lean_dec(v_a_881_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 3, v___x_886_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 4, v___y_876_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 5, v___x_879_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 6, v___y_874_);
v___x_887_ = lean_array_push(v___x_882_, v___x_884_);
if (v___y_876_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_889_ = v___x_868_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_866_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_856_ = v___x_889_;
goto v___jp_855_;
}
}
else
{
if (lean_obj_tag(v___y_875_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; 
v_val_891_ = lean_ctor_get(v___y_875_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___y_875_, 1);
v___x_892_ = lean_st_ref_get(v___y_853_);
v_env_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_892_);
v___x_894_ = l_Lean_getOutParamPositions_x3f(v_env_893_, v_val_891_);
lean_dec(v_val_891_);
if (lean_obj_tag(v___x_894_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_val_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = lean_array_get_size(v_val_895_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v_dummy_899_; lean_object* v_nargs_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v_dummy_899_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_900_ = l_Lean_Expr_getAppNumArgs(v___x_871_);
lean_inc(v_nargs_900_);
v___x_901_ = lean_mk_array(v_nargs_900_, v_dummy_899_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_sub(v_nargs_900_, v___x_902_);
lean_dec(v_nargs_900_);
v___x_904_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_871_, v___x_901_, v___x_903_);
v___x_905_ = lean_array_get_size(v___x_904_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_907_ = v___x_868_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_snd_866_);
v___x_907_ = v_reuseFailAlloc_919_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_905_, v_val_895_, v___x_904_, v_fvars_847_, v___y_876_, v___x_897_, v___x_907_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec_ref(v___x_904_);
lean_dec(v_val_895_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v_fst_910_ = lean_ctor_get(v_a_909_, 0);
v_snd_911_ = lean_ctor_get(v_a_909_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v_a_909_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_a_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_snd_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v_a_856_ = v___x_916_;
goto v___jp_855_;
}
}
}
else
{
lean_dec(v_a_848_);
return v___x_908_;
}
}
}
else
{
lean_object* v___x_921_; 
lean_dec(v_val_895_);
lean_dec_ref(v___x_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_921_ = v___x_868_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_snd_866_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_a_856_ = v___x_921_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_894_);
lean_dec_ref(v___x_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_924_ = v___x_868_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_snd_866_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v_a_856_ = v___x_924_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_871_);
v___x_926_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
v___x_927_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_926_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_929_; 
lean_dec_ref_known(v___x_927_, 1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_929_ = v___x_868_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_snd_866_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_a_856_ = v___x_929_;
goto v___jp_855_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v___x_887_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_a_848_);
v_a_931_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_927_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_a_878_);
lean_dec(v___y_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_871_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_939_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_880_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_880_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v___y_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_871_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_947_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_877_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_877_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
v___jp_955_:
{
lean_object* v___x_957_; 
lean_inc_ref(v___x_871_);
v___x_957_ = l_Lean_Meta_isClass_x3f(v___x_871_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
if (lean_obj_tag(v_a_958_) == 0)
{
uint8_t v___x_959_; 
v___x_959_ = 0;
v___y_874_ = v___y_956_;
v___y_875_ = v_a_958_;
v___y_876_ = v___x_959_;
goto v___jp_873_;
}
else
{
uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = l_Lean_LocalDecl_binderInfo(v_a_864_);
v___x_961_ = l_Lean_BinderInfo_isExplicit(v___x_960_);
if (v___x_961_ == 0)
{
v___y_874_ = v___y_956_;
v___y_875_ = v_a_958_;
v___y_876_ = v___x_860_;
goto v___jp_873_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = 0;
v___y_874_ = v___y_956_;
v___y_875_ = v_a_958_;
v___y_876_ = v___x_962_;
goto v___jp_873_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_871_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
lean_dec(v_fst_865_);
lean_dec(v_a_864_);
lean_dec(v_a_848_);
v_a_963_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_957_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_957_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_b_849_);
lean_dec(v_a_848_);
v_a_976_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_863_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_863_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_984_, lean_object* v_fvars_985_, lean_object* v_a_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_984_, v_fvars_985_, v_a_986_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_fvars_985_);
lean_dec(v_upperBound_984_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_996_, lean_object* v_fvars_997_, lean_object* v_type_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1004_ = lean_array_get_size(v_fvars_997_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_996_);
v___x_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1004_, v_fvars_997_, v___x_1005_, v___x_1007_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1027_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1027_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1027_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_fst_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1025_; 
v_fst_1013_ = lean_ctor_get(v_a_1009_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_a_1009_, 1);
lean_dec(v_unused_1026_);
v___x_1015_ = v_a_1009_;
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_fst_1013_);
lean_dec(v_a_1009_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1017_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_997_, v_type_998_);
v___x_1018_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_1013_, v___x_1017_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___x_1017_);
lean_ctor_set(v___x_1015_, 0, v___x_1018_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1017_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1020_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1008_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1008_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_1036_, lean_object* v_fvars_1037_, lean_object* v_type_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1036_, v_fvars_1037_, v_type_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_type_1038_);
lean_dec_ref(v_fvars_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1045_, lean_object* v_maxArgs_x3f_1046_, lean_object* v___f_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1053_ = lean_infer_type(v_fn_1045_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; uint8_t v_transparency_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___y_1060_; uint8_t v___x_1081_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = l_Lean_Meta_Context_config(v___y_1048_);
v_transparency_1056_ = lean_ctor_get_uint8(v___x_1055_, 9);
lean_dec_ref(v___x_1055_);
v___x_1057_ = 1;
v___x_1058_ = 0;
v___x_1081_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1056_, v___x_1057_);
if (v___x_1081_ == 0)
{
v___y_1060_ = v_transparency_1056_;
goto v___jp_1059_;
}
else
{
v___y_1060_ = v___x_1057_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v_keyedConfig_1061_; uint8_t v_trackZetaDelta_1062_; lean_object* v_zetaDeltaSet_1063_; lean_object* v_lctx_1064_; lean_object* v_localInstances_1065_; lean_object* v_defEqCtx_x3f_1066_; lean_object* v_synthPendingDepth_1067_; lean_object* v_customCanUnfoldPredicate_x3f_1068_; uint8_t v_univApprox_1069_; uint8_t v_inTypeClassResolution_1070_; uint8_t v_cacheInferType_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1080_; 
v_keyedConfig_1061_ = lean_ctor_get(v___y_1048_, 0);
v_trackZetaDelta_1062_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7);
v_zetaDeltaSet_1063_ = lean_ctor_get(v___y_1048_, 1);
v_lctx_1064_ = lean_ctor_get(v___y_1048_, 2);
v_localInstances_1065_ = lean_ctor_get(v___y_1048_, 3);
v_defEqCtx_x3f_1066_ = lean_ctor_get(v___y_1048_, 4);
v_synthPendingDepth_1067_ = lean_ctor_get(v___y_1048_, 5);
v_customCanUnfoldPredicate_x3f_1068_ = lean_ctor_get(v___y_1048_, 6);
v_univApprox_1069_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1070_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 2);
v_cacheInferType_1071_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 3);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1073_ = v___y_1048_;
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1068_);
lean_inc(v_synthPendingDepth_1067_);
lean_inc(v_defEqCtx_x3f_1066_);
lean_inc(v_localInstances_1065_);
lean_inc(v_lctx_1064_);
lean_inc(v_zetaDeltaSet_1063_);
lean_inc(v_keyedConfig_1061_);
lean_dec(v___y_1048_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_1060_, v_keyedConfig_1061_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_zetaDeltaSet_1063_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_lctx_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_localInstances_1065_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_defEqCtx_x3f_1066_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_synthPendingDepth_1067_);
lean_ctor_set(v_reuseFailAlloc_1079_, 6, v_customCanUnfoldPredicate_x3f_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*7, v_trackZetaDelta_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*7 + 1, v_univApprox_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*7 + 3, v_cacheInferType_1071_);
v___x_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1054_, v_maxArgs_x3f_1046_, v___f_1047_, v___x_1058_, v___x_1058_, v___x_1077_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___x_1077_);
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v___f_1047_);
lean_dec(v_maxArgs_x3f_1046_);
v_a_1082_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1053_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1053_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1090_, lean_object* v_maxArgs_x3f_1091_, lean_object* v___f_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1090_, v_maxArgs_x3f_1091_, v___f_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1099_, lean_object* v_vals_1100_, lean_object* v_i_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_array_get_size(v_keys_1099_);
v___x_1104_ = lean_nat_dec_lt(v_i_1101_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec(v_i_1101_);
v___x_1105_ = lean_box(0);
return v___x_1105_;
}
else
{
lean_object* v_k_x27_1106_; uint8_t v___x_1107_; 
v_k_x27_1106_ = lean_array_fget_borrowed(v_keys_1099_, v_i_1101_);
v___x_1107_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1102_, v_k_x27_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_add(v_i_1101_, v___x_1108_);
lean_dec(v_i_1101_);
v_i_1101_ = v___x_1109_;
goto _start;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_array_fget_borrowed(v_vals_1100_, v_i_1101_);
lean_dec(v_i_1101_);
lean_inc(v___x_1111_);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_i_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1113_, v_vals_1114_, v_i_1115_, v_k_1116_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_vals_1114_);
lean_dec_ref(v_keys_1113_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1118_, size_t v_x_1119_, lean_object* v_x_1120_){
_start:
{
if (lean_obj_tag(v_x_1118_) == 0)
{
lean_object* v_es_1121_; lean_object* v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v_j_1125_; lean_object* v___x_1126_; 
v_es_1121_ = lean_ctor_get(v_x_1118_, 0);
v___x_1122_ = lean_box(2);
v___x_1123_ = ((size_t)31ULL);
v___x_1124_ = lean_usize_land(v_x_1119_, v___x_1123_);
v_j_1125_ = lean_usize_to_nat(v___x_1124_);
v___x_1126_ = lean_array_get_borrowed(v___x_1122_, v_es_1121_, v_j_1125_);
lean_dec(v_j_1125_);
switch(lean_obj_tag(v___x_1126_))
{
case 0:
{
lean_object* v_key_1127_; lean_object* v_val_1128_; uint8_t v___x_1129_; 
v_key_1127_ = lean_ctor_get(v___x_1126_, 0);
v_val_1128_ = lean_ctor_get(v___x_1126_, 1);
v___x_1129_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1120_, v_key_1127_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; 
lean_inc(v_val_1128_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_val_1128_);
return v___x_1131_;
}
}
case 1:
{
lean_object* v_node_1132_; size_t v___x_1133_; size_t v___x_1134_; 
v_node_1132_ = lean_ctor_get(v___x_1126_, 0);
v___x_1133_ = ((size_t)5ULL);
v___x_1134_ = lean_usize_shift_right(v_x_1119_, v___x_1133_);
v_x_1118_ = v_node_1132_;
v_x_1119_ = v___x_1134_;
goto _start;
}
default: 
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_box(0);
return v___x_1136_;
}
}
}
else
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_ks_1137_ = lean_ctor_get(v_x_1118_, 0);
v_vs_1138_ = lean_ctor_get(v_x_1118_, 1);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1137_, v_vs_1138_, v___x_1139_, v_x_1120_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
size_t v_x_12952__boxed_1144_; lean_object* v_res_1145_; 
v_x_12952__boxed_1144_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1145_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1141_, v_x_12952__boxed_1144_, v_x_1143_);
lean_dec_ref(v_x_1143_);
lean_dec_ref(v_x_1141_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
uint64_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1147_);
v___x_1149_ = lean_uint64_to_usize(v___x_1148_);
v___x_1150_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1146_, v___x_1149_, v_x_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1151_, v_x_1152_);
lean_dec_ref(v_x_1152_);
lean_dec_ref(v_x_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_ks_1158_; lean_object* v_vs_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1183_; 
v_ks_1158_ = lean_ctor_get(v_x_1154_, 0);
v_vs_1159_ = lean_ctor_get(v_x_1154_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1154_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1161_ = v_x_1154_;
v_isShared_1162_ = v_isSharedCheck_1183_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_vs_1159_);
lean_inc(v_ks_1158_);
lean_dec(v_x_1154_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1183_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_array_get_size(v_ks_1158_);
v___x_1164_ = lean_nat_dec_lt(v_x_1155_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec(v_x_1155_);
v___x_1165_ = lean_array_push(v_ks_1158_, v_x_1156_);
v___x_1166_ = lean_array_push(v_vs_1159_, v_x_1157_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1166_);
lean_ctor_set(v___x_1161_, 0, v___x_1165_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
else
{
lean_object* v_k_x27_1170_; uint8_t v___x_1171_; 
v_k_x27_1170_ = lean_array_fget_borrowed(v_ks_1158_, v_x_1155_);
v___x_1171_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1156_, v_k_x27_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1173_; 
if (v_isShared_1162_ == 0)
{
v___x_1173_ = v___x_1161_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_ks_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_vs_1159_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_add(v_x_1155_, v___x_1174_);
lean_dec(v_x_1155_);
v_x_1154_ = v___x_1173_;
v_x_1155_ = v___x_1175_;
goto _start;
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_array_fset(v_ks_1158_, v_x_1155_, v_x_1156_);
v___x_1179_ = lean_array_fset(v_vs_1159_, v_x_1155_, v_x_1157_);
lean_dec(v_x_1155_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1179_);
lean_ctor_set(v___x_1161_, 0, v___x_1178_);
v___x_1181_ = v___x_1161_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1184_, lean_object* v_k_1185_, lean_object* v_v_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_1184_, v___x_1187_, v_k_1185_, v_v_1186_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1190_, size_t v_x_1191_, size_t v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 0)
{
lean_object* v_es_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v_j_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_es_1195_ = lean_ctor_get(v_x_1190_, 0);
v___x_1196_ = ((size_t)31ULL);
v___x_1197_ = lean_usize_land(v_x_1191_, v___x_1196_);
v_j_1198_ = lean_usize_to_nat(v___x_1197_);
v___x_1199_ = lean_array_get_size(v_es_1195_);
v___x_1200_ = lean_nat_dec_lt(v_j_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_j_1198_);
lean_dec(v_x_1194_);
lean_dec_ref(v_x_1193_);
return v_x_1190_;
}
else
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1239_; 
lean_inc_ref(v_es_1195_);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_x_1190_, 0);
lean_dec(v_unused_1240_);
v___x_1202_ = v_x_1190_;
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v_x_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_v_1204_; lean_object* v___x_1205_; lean_object* v_xs_x27_1206_; lean_object* v___y_1208_; 
v_v_1204_ = lean_array_fget(v_es_1195_, v_j_1198_);
v___x_1205_ = lean_box(0);
v_xs_x27_1206_ = lean_array_fset(v_es_1195_, v_j_1198_, v___x_1205_);
switch(lean_obj_tag(v_v_1204_))
{
case 0:
{
lean_object* v_key_1213_; lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1224_; 
v_key_1213_ = lean_ctor_get(v_v_1204_, 0);
v_val_1214_ = lean_ctor_get(v_v_1204_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_v_1204_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1216_ = v_v_1204_;
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_inc(v_key_1213_);
lean_dec(v_v_1204_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
uint8_t v___x_1218_; 
v___x_1218_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1193_, v_key_1213_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1216_);
v___x_1219_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1213_, v_val_1214_, v_x_1193_, v_x_1194_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
v___y_1208_ = v___x_1220_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1222_; 
lean_dec(v_val_1214_);
lean_dec(v_key_1213_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_x_1194_);
lean_ctor_set(v___x_1216_, 0, v_x_1193_);
v___x_1222_ = v___x_1216_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_x_1193_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_x_1194_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
v___y_1208_ = v___x_1222_;
goto v___jp_1207_;
}
}
}
}
case 1:
{
lean_object* v_node_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1237_; 
v_node_1225_ = lean_ctor_get(v_v_1204_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_v_1204_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1227_ = v_v_1204_;
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_node_1225_);
lean_dec(v_v_1204_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1229_ = ((size_t)5ULL);
v___x_1230_ = lean_usize_shift_right(v_x_1191_, v___x_1229_);
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_x_1192_, v___x_1231_);
v___x_1233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1225_, v___x_1230_, v___x_1232_, v_x_1193_, v_x_1194_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1233_);
v___x_1235_ = v___x_1227_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
v___y_1208_ = v___x_1235_;
goto v___jp_1207_;
}
}
}
default: 
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_x_1193_);
lean_ctor_set(v___x_1238_, 1, v_x_1194_);
v___y_1208_ = v___x_1238_;
goto v___jp_1207_;
}
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_array_fset(v_xs_x27_1206_, v_j_1198_, v___y_1208_);
lean_dec(v_j_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1209_);
v___x_1211_ = v___x_1202_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
else
{
lean_object* v_ks_1241_; lean_object* v_vs_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1262_; 
v_ks_1241_ = lean_ctor_get(v_x_1190_, 0);
v_vs_1242_ = lean_ctor_get(v_x_1190_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1244_ = v_x_1190_;
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_vs_1242_);
lean_inc(v_ks_1241_);
lean_dec(v_x_1190_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_ks_1241_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_vs_1242_);
v___x_1247_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v_newNode_1248_; uint8_t v___y_1250_; size_t v___x_1256_; uint8_t v___x_1257_; 
v_newNode_1248_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1247_, v_x_1193_, v_x_1194_);
v___x_1256_ = ((size_t)7ULL);
v___x_1257_ = lean_usize_dec_le(v___x_1256_, v_x_1192_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1248_);
v___x_1259_ = lean_unsigned_to_nat(4u);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
lean_dec(v___x_1258_);
v___y_1250_ = v___x_1260_;
goto v___jp_1249_;
}
else
{
v___y_1250_ = v___x_1257_;
goto v___jp_1249_;
}
v___jp_1249_:
{
if (v___y_1250_ == 0)
{
lean_object* v_ks_1251_; lean_object* v_vs_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_ks_1251_ = lean_ctor_get(v_newNode_1248_, 0);
lean_inc_ref(v_ks_1251_);
v_vs_1252_ = lean_ctor_get(v_newNode_1248_, 1);
lean_inc_ref(v_vs_1252_);
lean_dec_ref(v_newNode_1248_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1192_, v_ks_1251_, v_vs_1252_, v___x_1253_, v___x_1254_);
lean_dec_ref(v_vs_1252_);
lean_dec_ref(v_ks_1251_);
return v___x_1255_;
}
else
{
return v_newNode_1248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1263_, lean_object* v_keys_1264_, lean_object* v_vals_1265_, lean_object* v_i_1266_, lean_object* v_entries_1267_){
_start:
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_array_get_size(v_keys_1264_);
v___x_1269_ = lean_nat_dec_lt(v_i_1266_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec(v_i_1266_);
return v_entries_1267_;
}
else
{
lean_object* v_k_1270_; lean_object* v_v_1271_; uint64_t v___x_1272_; size_t v_h_1273_; size_t v___x_1274_; lean_object* v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v_h_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_k_1270_ = lean_array_fget_borrowed(v_keys_1264_, v_i_1266_);
v_v_1271_ = lean_array_fget_borrowed(v_vals_1265_, v_i_1266_);
v___x_1272_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1270_);
v_h_1273_ = lean_uint64_to_usize(v___x_1272_);
v___x_1274_ = ((size_t)5ULL);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_sub(v_depth_1263_, v___x_1276_);
v___x_1278_ = lean_usize_mul(v___x_1274_, v___x_1277_);
v_h_1279_ = lean_usize_shift_right(v_h_1273_, v___x_1278_);
v___x_1280_ = lean_nat_add(v_i_1266_, v___x_1275_);
lean_dec(v_i_1266_);
lean_inc(v_v_1271_);
lean_inc(v_k_1270_);
v___x_1281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1267_, v_h_1279_, v_depth_1263_, v_k_1270_, v_v_1271_);
v_i_1266_ = v___x_1280_;
v_entries_1267_ = v___x_1281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1283_, lean_object* v_keys_1284_, lean_object* v_vals_1285_, lean_object* v_i_1286_, lean_object* v_entries_1287_){
_start:
{
size_t v_depth_boxed_1288_; lean_object* v_res_1289_; 
v_depth_boxed_1288_ = lean_unbox_usize(v_depth_1283_);
lean_dec(v_depth_1283_);
v_res_1289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1288_, v_keys_1284_, v_vals_1285_, v_i_1286_, v_entries_1287_);
lean_dec_ref(v_vals_1285_);
lean_dec_ref(v_keys_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_13087__boxed_1295_; size_t v_x_13088__boxed_1296_; lean_object* v_res_1297_; 
v_x_13087__boxed_1295_ = lean_unbox_usize(v_x_1291_);
lean_dec(v_x_1291_);
v_x_13088__boxed_1296_ = lean_unbox_usize(v_x_1292_);
lean_dec(v_x_1292_);
v_res_1297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1290_, v_x_13087__boxed_1295_, v_x_13088__boxed_1296_, v_x_1293_, v_x_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
uint64_t v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1299_);
v___x_1302_ = lean_uint64_to_usize(v___x_1301_);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1298_, v___x_1302_, v___x_1303_, v_x_1299_, v_x_1300_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1308_, lean_object* v_env_1309_, lean_object* v_forConst_1310_, lean_object* v_ctx_1311_, lean_object* v_importRealizationCtx_x3f_1312_, lean_object* v_realize_1313_, lean_object* v_opts_1314_, lean_object* v_key_1315_, lean_object* v_inst_1316_, lean_object* v_____r_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v___y_1355_; lean_object* v___x_1360_; 
v___x_1319_ = lean_io_promise_new();
v___x_1320_ = lean_st_ref_take(v_realizeMapRef_1308_);
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1320_, v_inst_1316_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1355_ = v___x_1361_;
goto v___jp_1354_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1360_, 1);
v___y_1355_ = v_val_1362_;
goto v___jp_1354_;
}
v___jp_1321_:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_st_ref_set(v_realizeMapRef_1308_, v_snd_1323_);
if (lean_obj_tag(v_fst_1322_) == 1)
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1319_);
lean_dec_ref(v_opts_1314_);
lean_dec_ref(v_realize_1313_);
lean_dec(v_importRealizationCtx_x3f_1312_);
lean_dec_ref(v_ctx_1311_);
lean_dec(v_forConst_1310_);
lean_dec(v_env_1309_);
v_val_1325_ = lean_ctor_get(v_fst_1322_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_fst_1322_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1327_ = v_fst_1322_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v_fst_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_task_get_own(v_val_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_base_1334_; lean_object* v_serverBaseExts_1335_; lean_object* v_checked_1336_; lean_object* v_asyncConstsMap_1337_; lean_object* v_asyncCtx_x3f_1338_; lean_object* v_localRealizationCtxMap_1339_; lean_object* v_allRealizations_1340_; uint8_t v_isExporting_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_fst_1322_);
v_base_1334_ = lean_ctor_get(v_env_1309_, 0);
v_serverBaseExts_1335_ = lean_ctor_get(v_env_1309_, 1);
v_checked_1336_ = lean_ctor_get(v_env_1309_, 2);
v_asyncConstsMap_1337_ = lean_ctor_get(v_env_1309_, 3);
v_asyncCtx_x3f_1338_ = lean_ctor_get(v_env_1309_, 4);
v_localRealizationCtxMap_1339_ = lean_ctor_get(v_env_1309_, 6);
v_allRealizations_1340_ = lean_ctor_get(v_env_1309_, 7);
v_isExporting_1341_ = lean_ctor_get_uint8(v_env_1309_, sizeof(void*)*8);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_env_1309_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_env_1309_, 5);
lean_dec(v_unused_1353_);
v___x_1343_ = v_env_1309_;
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_allRealizations_1340_);
lean_inc(v_localRealizationCtxMap_1339_);
lean_inc(v_asyncCtx_x3f_1338_);
lean_inc(v_asyncConstsMap_1337_);
lean_inc(v_checked_1336_);
lean_inc(v_serverBaseExts_1335_);
lean_inc(v_base_1334_);
lean_dec(v_env_1309_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1310_, v_ctx_1311_, v_localRealizationCtxMap_1339_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 6, v___x_1345_);
lean_ctor_set(v___x_1343_, 5, v_importRealizationCtx_x3f_1312_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_base_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_serverBaseExts_1335_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_checked_1336_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_asyncConstsMap_1337_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_asyncCtx_x3f_1338_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_importRealizationCtx_x3f_1312_);
lean_ctor_set(v_reuseFailAlloc_1351_, 6, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1351_, 7, v_allRealizations_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*8, v_isExporting_1341_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_apply_3(v_realize_1313_, v___x_1347_, v_opts_1314_, lean_box(0));
lean_inc(v___x_1348_);
v___x_1349_ = lean_io_promise_resolve(v___x_1348_, v___x_1319_);
lean_dec(v___x_1319_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
return v___x_1350_;
}
}
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1355_, v_key_1315_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = l_IO_Promise_result_x21___redArg(v___x_1319_);
v___x_1358_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1355_, v_key_1315_, v___x_1357_);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1316_, v___x_1358_, v___x_1320_);
v_fst_1322_ = v___x_1356_;
v_snd_1323_ = v___x_1359_;
goto v___jp_1321_;
}
else
{
lean_dec_ref(v___y_1355_);
lean_dec(v_inst_1316_);
lean_dec_ref(v_key_1315_);
v_fst_1322_ = v___x_1356_;
v_snd_1323_ = v___x_1320_;
goto v___jp_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1363_, lean_object* v_env_1364_, lean_object* v_forConst_1365_, lean_object* v_ctx_1366_, lean_object* v_importRealizationCtx_x3f_1367_, lean_object* v_realize_1368_, lean_object* v_opts_1369_, lean_object* v_key_1370_, lean_object* v_inst_1371_, lean_object* v_____r_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1363_, v_env_1364_, v_forConst_1365_, v_ctx_1366_, v_importRealizationCtx_x3f_1367_, v_realize_1368_, v_opts_1369_, v_key_1370_, v_inst_1371_, v_____r_1372_);
lean_dec(v_realizeMapRef_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = 0;
return v___x_1377_;
}
else
{
lean_object* v_key_1378_; lean_object* v_tail_1379_; uint8_t v___x_1380_; 
v_key_1378_ = lean_ctor_get(v_x_1376_, 0);
v_tail_1379_ = lean_ctor_get(v_x_1376_, 2);
v___x_1380_ = lean_name_eq(v_key_1378_, v_a_1375_);
if (v___x_1380_ == 0)
{
v_x_1376_ = v_tail_1379_;
goto _start;
}
else
{
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1382_, lean_object* v_x_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1382_, v_x_1383_);
lean_dec(v_x_1383_);
lean_dec(v_a_1382_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_buckets_1388_; lean_object* v___x_1389_; uint64_t v___y_1391_; 
v_buckets_1388_ = lean_ctor_get(v_m_1386_, 1);
v___x_1389_ = lean_array_get_size(v_buckets_1388_);
if (lean_obj_tag(v_a_1387_) == 0)
{
uint64_t v___x_1405_; 
v___x_1405_ = lean_uint64_once(&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0, &l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once, _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
v___y_1391_ = v___x_1405_;
goto v___jp_1390_;
}
else
{
uint64_t v_hash_1406_; 
v_hash_1406_ = lean_ctor_get_uint64(v_a_1387_, sizeof(void*)*2);
v___y_1391_ = v_hash_1406_;
goto v___jp_1390_;
}
v___jp_1390_:
{
uint64_t v___x_1392_; uint64_t v___x_1393_; uint64_t v_fold_1394_; uint64_t v___x_1395_; uint64_t v___x_1396_; uint64_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1392_ = 32ULL;
v___x_1393_ = lean_uint64_shift_right(v___y_1391_, v___x_1392_);
v_fold_1394_ = lean_uint64_xor(v___y_1391_, v___x_1393_);
v___x_1395_ = 16ULL;
v___x_1396_ = lean_uint64_shift_right(v_fold_1394_, v___x_1395_);
v___x_1397_ = lean_uint64_xor(v_fold_1394_, v___x_1396_);
v___x_1398_ = lean_uint64_to_usize(v___x_1397_);
v___x_1399_ = lean_usize_of_nat(v___x_1389_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_sub(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_usize_land(v___x_1398_, v___x_1401_);
v___x_1403_ = lean_array_uget_borrowed(v_buckets_1388_, v___x_1402_);
v___x_1404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1387_, v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_m_1407_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1417_, lean_object* v_env_1418_, lean_object* v_forConst_1419_, lean_object* v_key_1420_, lean_object* v_realize_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v_a_1425_; lean_object* v___y_1429_; lean_object* v_base_1431_; lean_object* v_importRealizationCtx_x3f_1432_; lean_object* v_localRealizationCtxMap_1433_; uint8_t v_isExporting_1434_; lean_object* v_ctx_1436_; lean_object* v___y_1451_; 
v___x_1423_ = lean_io_get_num_heartbeats();
v_base_1431_ = lean_ctor_get(v_env_1418_, 0);
lean_inc_ref(v_base_1431_);
v_importRealizationCtx_x3f_1432_ = lean_ctor_get(v_env_1418_, 5);
lean_inc(v_importRealizationCtx_x3f_1432_);
v_localRealizationCtxMap_1433_ = lean_ctor_get(v_env_1418_, 6);
lean_inc(v_localRealizationCtxMap_1433_);
v_isExporting_1434_ = lean_ctor_get_uint8(v_env_1418_, sizeof(void*)*8);
lean_dec_ref(v_env_1418_);
if (v_isExporting_1434_ == 0)
{
lean_object* v_private_1471_; 
v_private_1471_ = lean_ctor_get(v_base_1431_, 0);
lean_inc(v_private_1471_);
lean_dec_ref(v_base_1431_);
v___y_1451_ = v_private_1471_;
goto v___jp_1450_;
}
else
{
lean_object* v_public_1472_; 
v_public_1472_ = lean_ctor_get(v_base_1431_, 1);
lean_inc(v_public_1472_);
lean_dec_ref(v_base_1431_);
v___y_1451_ = v_public_1472_;
goto v___jp_1450_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_io_set_heartbeats(v___x_1423_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_a_1425_);
return v___x_1427_;
}
v___jp_1428_:
{
lean_object* v_a_1430_; 
v_a_1430_ = lean_ctor_get(v___y_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___y_1429_);
v_a_1425_ = v_a_1430_;
goto v___jp_1424_;
}
v___jp_1435_:
{
lean_object* v_env_1437_; lean_object* v_opts_1438_; lean_object* v_realizeMapRef_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_env_1437_ = lean_ctor_get(v_ctx_1436_, 0);
lean_inc(v_env_1437_);
v_opts_1438_ = lean_ctor_get(v_ctx_1436_, 1);
lean_inc_ref(v_opts_1438_);
v_realizeMapRef_1439_ = lean_ctor_get(v_ctx_1436_, 2);
lean_inc(v_realizeMapRef_1439_);
v___x_1440_ = lean_st_ref_get(v_realizeMapRef_1439_);
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1440_, v_inst_1417_);
lean_dec(v___x_1440_);
if (lean_obj_tag(v___x_1441_) == 1)
{
lean_object* v_val_1442_; lean_object* v___x_1443_; 
v_val_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1442_, v_key_1420_);
lean_dec(v_val_1442_);
if (lean_obj_tag(v___x_1443_) == 1)
{
lean_object* v_val_1444_; lean_object* v___x_1445_; 
lean_dec(v_realizeMapRef_1439_);
lean_dec_ref(v_opts_1438_);
lean_dec(v_env_1437_);
lean_dec_ref(v_ctx_1436_);
lean_dec(v_importRealizationCtx_x3f_1432_);
lean_dec_ref(v_realize_1421_);
lean_dec_ref(v_key_1420_);
lean_dec(v_forConst_1419_);
lean_dec(v_inst_1417_);
v_val_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1445_ = lean_task_get_own(v_val_1444_);
v_a_1425_ = v___x_1445_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1439_, v_env_1437_, v_forConst_1419_, v_ctx_1436_, v_importRealizationCtx_x3f_1432_, v_realize_1421_, v_opts_1438_, v_key_1420_, v_inst_1417_, v___x_1446_);
lean_dec(v_realizeMapRef_1439_);
v___y_1429_ = v___x_1447_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec(v___x_1441_);
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1439_, v_env_1437_, v_forConst_1419_, v_ctx_1436_, v_importRealizationCtx_x3f_1432_, v_realize_1421_, v_opts_1438_, v_key_1420_, v_inst_1417_, v___x_1448_);
lean_dec(v_realizeMapRef_1439_);
v___y_1429_ = v___x_1449_;
goto v___jp_1428_;
}
}
v___jp_1450_:
{
lean_object* v_const2ModIdx_1452_; uint8_t v___x_1453_; 
v_const2ModIdx_1452_ = lean_ctor_get(v___y_1451_, 2);
lean_inc_ref(v_const2ModIdx_1452_);
lean_dec_ref(v___y_1451_);
v___x_1453_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1452_, v_forConst_1419_);
lean_dec_ref(v_const2ModIdx_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1433_, v_forConst_1419_);
lean_dec(v_localRealizationCtxMap_1433_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_importRealizationCtx_x3f_1432_);
lean_dec(v___x_1423_);
lean_dec_ref(v_realize_1421_);
lean_dec_ref(v_key_1420_);
v___x_1455_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1456_ = 1;
v___x_1457_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1417_, v___x_1456_);
v___x_1458_ = lean_string_append(v___x_1455_, v___x_1457_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
v___x_1461_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1419_, v___x_1456_);
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1464_ = lean_string_append(v___x_1462_, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
else
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v___x_1454_, 1);
v_ctx_1436_ = v_val_1467_;
goto v___jp_1435_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1433_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1432_) == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1423_);
lean_dec_ref(v_realize_1421_);
lean_dec_ref(v_key_1420_);
lean_dec(v_forConst_1419_);
lean_dec(v_inst_1417_);
v___x_1468_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
else
{
lean_object* v_val_1470_; 
v_val_1470_ = lean_ctor_get(v_importRealizationCtx_x3f_1432_, 0);
lean_inc(v_val_1470_);
v_ctx_1436_ = v_val_1470_;
goto v___jp_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1473_, lean_object* v_env_1474_, lean_object* v_forConst_1475_, lean_object* v_key_1476_, lean_object* v_realize_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1473_, v_env_1474_, v_forConst_1475_, v_key_1476_, v_realize_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___f_1486_; lean_object* v___x_11275__overap_1487_; lean_object* v___x_1488_; 
v___f_1486_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_11275__overap_1487_ = lean_panic_fn_borrowed(v___f_1486_, v_msg_1480_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
v___x_1488_ = lean_apply_5(v___x_11275__overap_1487_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1496_, lean_object* v_inst_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
v___x_1503_ = lean_apply_5(v_realize_1496_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1512_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_inst_1497_);
lean_ctor_set(v___x_1508_, 1, v_a_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_inst_1497_);
v_a_1513_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1503_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1503_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1521_, lean_object* v_inst_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1521_, v_inst_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = l_Lean_Options_empty;
v___x_1530_ = l_Lean_Core_getMaxHeartbeats(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_unsigned_to_nat(16u);
v___x_1533_ = lean_mk_array(v___x_1532_, v___x_1531_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1540_ = lean_unsigned_to_nat(36u);
v___x_1541_ = lean_unsigned_to_nat(2664u);
v___x_1542_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1543_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1544_ = l_mkPanicMessageWithDecl(v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_, v___x_1539_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1546_ = lean_unsigned_to_nat(48u);
v___x_1547_ = lean_unsigned_to_nat(2655u);
v___x_1548_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1549_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1550_ = l_mkPanicMessageWithDecl(v___x_1549_, v___x_1548_, v___x_1547_, v___x_1546_, v___x_1545_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_forConst_1553_, lean_object* v_key_1554_, lean_object* v_realize_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_env_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_st_ref_get(v_a_1559_);
v_env_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc_ref(v_env_1562_);
lean_dec(v___x_1561_);
v___x_1563_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1562_, v_forConst_1553_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref(v_env_1562_);
lean_dec_ref(v_key_1554_);
lean_dec(v_forConst_1553_);
lean_dec(v_inst_1552_);
lean_dec(v_inst_1551_);
lean_inc(v_a_1559_);
lean_inc_ref(v_a_1558_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
v___x_1564_ = lean_apply_5(v_realize_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, lean_box(0));
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v_fileName_1566_; lean_object* v_fileMap_1567_; lean_object* v_ref_1568_; lean_object* v___f_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1565_ = lean_io_get_num_heartbeats();
v_fileName_1566_ = lean_ctor_get(v_a_1558_, 0);
v_fileMap_1567_ = lean_ctor_get(v_a_1558_, 1);
v_ref_1568_ = lean_ctor_get(v_a_1558_, 5);
lean_inc(v_inst_1552_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1569_, 0, v_realize_1555_);
lean_closure_set(v___f_1569_, 1, v_inst_1552_);
v___x_1570_ = 0;
v___x_1571_ = l_Lean_Options_empty;
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_unsigned_to_nat(1000u);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1578_ = l_Lean_firstFrontendMacroScope;
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1567_);
lean_inc_ref(v_fileName_1566_);
v___x_1581_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1581_, 0, v_fileName_1566_);
lean_ctor_set(v___x_1581_, 1, v_fileMap_1567_);
lean_ctor_set(v___x_1581_, 2, v___x_1571_);
lean_ctor_set(v___x_1581_, 3, v___x_1572_);
lean_ctor_set(v___x_1581_, 4, v___x_1573_);
lean_ctor_set(v___x_1581_, 5, v___x_1574_);
lean_ctor_set(v___x_1581_, 6, v___x_1575_);
lean_ctor_set(v___x_1581_, 7, v___x_1576_);
lean_ctor_set(v___x_1581_, 8, v___x_1565_);
lean_ctor_set(v___x_1581_, 9, v___x_1577_);
lean_ctor_set(v___x_1581_, 10, v___x_1575_);
lean_ctor_set(v___x_1581_, 11, v___x_1578_);
lean_ctor_set(v___x_1581_, 12, v___x_1579_);
lean_ctor_set(v___x_1581_, 13, v___x_1580_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*14, v___x_1570_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*14 + 1, v___x_1570_);
v___x_1582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1582_, 0, v___f_1569_);
lean_closure_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1551_, v_env_1562_, v_forConst_1553_, v_key_1554_, v___x_1582_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1636_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1636_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1636_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1589_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1584_, v___x_1588_);
lean_dec(v_a_1584_);
if (lean_obj_tag(v___x_1589_) == 1)
{
lean_object* v_val_1590_; lean_object* v_res_x3f_1591_; lean_object* v_snap_x3f_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v_snap_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; 
v_val_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v_res_x3f_1591_ = lean_ctor_get(v_val_1590_, 0);
lean_inc_ref(v_res_x3f_1591_);
v_snap_x3f_1592_ = lean_ctor_get(v_val_1590_, 1);
lean_inc(v_snap_x3f_1592_);
lean_dec(v_val_1590_);
if (lean_obj_tag(v_snap_x3f_1592_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1627_; 
v_val_1626_ = lean_ctor_get(v_snap_x3f_1592_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v_snap_x3f_1592_, 1);
v___x_1627_ = l_Lean_Syntax_getRange_x3f(v_ref_1568_, v___x_1570_);
if (lean_obj_tag(v___x_1627_) == 1)
{
lean_object* v_val_1628_; lean_object* v_start_1629_; lean_object* v_stop_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v_start_1629_ = lean_ctor_get(v_val_1628_, 0);
lean_inc(v_start_1629_);
v_stop_1630_ = lean_ctor_get(v_val_1628_, 1);
lean_inc(v_stop_1630_);
lean_dec(v_val_1628_);
lean_inc_ref_n(v_fileMap_1567_, 2);
v___x_1631_ = l_Lean_FileMap_toPosition(v_fileMap_1567_, v_start_1629_);
lean_dec(v_start_1629_);
v___x_1632_ = l_Lean_FileMap_toPosition(v_fileMap_1567_, v_stop_1630_);
lean_dec(v_stop_1630_);
v___x_1633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1626_, v___x_1631_, v___x_1632_);
v_snap_1611_ = v___x_1633_;
v___y_1612_ = v_a_1556_;
v___y_1613_ = v_a_1557_;
v___y_1614_ = v_a_1558_;
v___y_1615_ = v_a_1559_;
goto v___jp_1610_;
}
else
{
lean_dec(v___x_1627_);
v_snap_1611_ = v_val_1626_;
v___y_1612_ = v_a_1556_;
v___y_1613_ = v_a_1557_;
v___y_1614_ = v_a_1558_;
v___y_1615_ = v_a_1559_;
goto v___jp_1610_;
}
}
else
{
lean_dec(v_snap_x3f_1592_);
v___y_1594_ = v_a_1556_;
v___y_1595_ = v_a_1557_;
v___y_1596_ = v_a_1558_;
v___y_1597_ = v_a_1559_;
goto v___jp_1593_;
}
v___jp_1593_:
{
if (lean_obj_tag(v_res_x3f_1591_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; 
lean_dec(v_inst_1552_);
v_a_1598_ = lean_ctor_get(v_res_x3f_1591_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v_res_x3f_1591_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 1);
lean_ctor_set(v___x_1586_, 0, v_a_1598_);
v___x_1600_ = v___x_1586_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_a_1602_ = lean_ctor_get(v_res_x3f_1591_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v_res_x3f_1591_, 1);
v___x_1603_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1602_, v_inst_1552_);
lean_dec(v_inst_1552_);
lean_dec(v_a_1602_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_del_object(v___x_1586_);
v___x_1604_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1605_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1604_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1605_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1608_; 
v_val_1606_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1603_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_val_1606_);
v___x_1608_ = v___x_1586_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_val_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
v___jp_1610_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1579_, v_snap_1611_);
v___x_1617_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1616_, v___y_1615_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
v___y_1594_ = v___y_1612_;
v___y_1595_ = v___y_1613_;
v___y_1596_ = v___y_1614_;
v___y_1597_ = v___y_1615_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_res_x3f_1591_);
lean_del_object(v___x_1586_);
lean_dec(v_inst_1552_);
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v___x_1589_);
lean_del_object(v___x_1586_);
lean_dec(v_inst_1552_);
v___x_1634_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1635_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1634_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
return v___x_1635_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_inst_1552_);
v_a_1637_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1639_ = v___x_1583_;
v_isShared_1640_ = v_isSharedCheck_1648_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1583_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1648_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1641_ = lean_io_error_to_string(v_a_1637_);
v___x_1642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
v___x_1643_ = l_Lean_MessageData_ofFormat(v___x_1642_);
lean_inc(v_ref_1568_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_ref_1568_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1644_);
v___x_1646_ = v___x_1639_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_forConst_1651_, lean_object* v_key_1652_, lean_object* v_realize_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1649_, v_inst_1650_, v_forConst_1651_, v_key_1652_, v_realize_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_i_1662_, lean_object* v_k_1663_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_array_get_size(v_keys_1660_);
v___x_1665_ = lean_nat_dec_lt(v_i_1662_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec(v_i_1662_);
v___x_1666_ = lean_box(0);
return v___x_1666_;
}
else
{
lean_object* v_k_x27_1667_; uint8_t v___x_1668_; 
v_k_x27_1667_ = lean_array_fget_borrowed(v_keys_1660_, v_i_1662_);
v___x_1668_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1663_, v_k_x27_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_i_1662_, v___x_1669_);
lean_dec(v_i_1662_);
v_i_1662_ = v___x_1670_;
goto _start;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_array_fget_borrowed(v_vals_1661_, v_i_1662_);
lean_dec(v_i_1662_);
lean_inc(v___x_1672_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1674_, lean_object* v_vals_1675_, lean_object* v_i_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1674_, v_vals_1675_, v_i_1676_, v_k_1677_);
lean_dec_ref(v_k_1677_);
lean_dec_ref(v_vals_1675_);
lean_dec_ref(v_keys_1674_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1679_, size_t v_x_1680_, lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 0)
{
lean_object* v_es_1682_; lean_object* v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v_j_1686_; lean_object* v___x_1687_; 
v_es_1682_ = lean_ctor_get(v_x_1679_, 0);
v___x_1683_ = lean_box(2);
v___x_1684_ = ((size_t)31ULL);
v___x_1685_ = lean_usize_land(v_x_1680_, v___x_1684_);
v_j_1686_ = lean_usize_to_nat(v___x_1685_);
v___x_1687_ = lean_array_get_borrowed(v___x_1683_, v_es_1682_, v_j_1686_);
lean_dec(v_j_1686_);
switch(lean_obj_tag(v___x_1687_))
{
case 0:
{
lean_object* v_key_1688_; lean_object* v_val_1689_; uint8_t v___x_1690_; 
v_key_1688_ = lean_ctor_get(v___x_1687_, 0);
v_val_1689_ = lean_ctor_get(v___x_1687_, 1);
v___x_1690_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1681_, v_key_1688_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_box(0);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; 
lean_inc(v_val_1689_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_val_1689_);
return v___x_1692_;
}
}
case 1:
{
lean_object* v_node_1693_; size_t v___x_1694_; size_t v___x_1695_; 
v_node_1693_ = lean_ctor_get(v___x_1687_, 0);
v___x_1694_ = ((size_t)5ULL);
v___x_1695_ = lean_usize_shift_right(v_x_1680_, v___x_1694_);
v_x_1679_ = v_node_1693_;
v_x_1680_ = v___x_1695_;
goto _start;
}
default: 
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
}
}
else
{
lean_object* v_ks_1698_; lean_object* v_vs_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_ks_1698_ = lean_ctor_get(v_x_1679_, 0);
v_vs_1699_ = lean_ctor_get(v_x_1679_, 1);
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1698_, v_vs_1699_, v___x_1700_, v_x_1681_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
size_t v_x_13833__boxed_1705_; lean_object* v_res_1706_; 
v_x_13833__boxed_1705_ = lean_unbox_usize(v_x_1703_);
lean_dec(v_x_1703_);
v_res_1706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1702_, v_x_13833__boxed_1705_, v_x_1704_);
lean_dec_ref(v_x_1704_);
lean_dec_ref(v_x_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
uint64_t v_configKey_1709_; lean_object* v_expr_1710_; lean_object* v_nargs_x3f_1711_; uint64_t v___x_1712_; uint64_t v___y_1714_; 
v_configKey_1709_ = lean_ctor_get_uint64(v_x_1708_, sizeof(void*)*2);
v_expr_1710_ = lean_ctor_get(v_x_1708_, 0);
v_nargs_x3f_1711_ = lean_ctor_get(v_x_1708_, 1);
v___x_1712_ = l_Lean_Expr_hash(v_expr_1710_);
if (lean_obj_tag(v_nargs_x3f_1711_) == 0)
{
uint64_t v___x_1719_; 
v___x_1719_ = 11ULL;
v___y_1714_ = v___x_1719_;
goto v___jp_1713_;
}
else
{
lean_object* v_val_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; uint64_t v___x_1723_; 
v_val_1720_ = lean_ctor_get(v_nargs_x3f_1711_, 0);
v___x_1721_ = lean_uint64_of_nat(v_val_1720_);
v___x_1722_ = 13ULL;
v___x_1723_ = lean_uint64_mix_hash(v___x_1721_, v___x_1722_);
v___y_1714_ = v___x_1723_;
goto v___jp_1713_;
}
v___jp_1713_:
{
uint64_t v___x_1715_; uint64_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_uint64_mix_hash(v___x_1712_, v___y_1714_);
v___x_1716_ = lean_uint64_mix_hash(v_configKey_1709_, v___x_1715_);
v___x_1717_ = lean_uint64_to_usize(v___x_1716_);
v___x_1718_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1707_, v___x_1717_, v_x_1708_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1724_, v_x_1725_);
lean_dec_ref(v_x_1725_);
lean_dec_ref(v_x_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v_ks_1731_; lean_object* v_vs_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1756_; 
v_ks_1731_ = lean_ctor_get(v_x_1727_, 0);
v_vs_1732_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1734_ = v_x_1727_;
v_isShared_1735_ = v_isSharedCheck_1756_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_vs_1732_);
lean_inc(v_ks_1731_);
lean_dec(v_x_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1756_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_ks_1731_);
v___x_1737_ = lean_nat_dec_lt(v_x_1728_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_dec(v_x_1728_);
v___x_1738_ = lean_array_push(v_ks_1731_, v_x_1729_);
v___x_1739_ = lean_array_push(v_vs_1732_, v_x_1730_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1739_);
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1741_ = v___x_1734_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
else
{
lean_object* v_k_x27_1743_; uint8_t v___x_1744_; 
v_k_x27_1743_ = lean_array_fget_borrowed(v_ks_1731_, v_x_1728_);
v___x_1744_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1729_, v_k_x27_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1746_; 
if (v_isShared_1735_ == 0)
{
v___x_1746_ = v___x_1734_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_ks_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_vs_1732_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_add(v_x_1728_, v___x_1747_);
lean_dec(v_x_1728_);
v_x_1727_ = v___x_1746_;
v_x_1728_ = v___x_1748_;
goto _start;
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1751_ = lean_array_fset(v_ks_1731_, v_x_1728_, v_x_1729_);
v___x_1752_ = lean_array_fset(v_vs_1732_, v_x_1728_, v_x_1730_);
lean_dec(v_x_1728_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1752_);
lean_ctor_set(v___x_1734_, 0, v___x_1751_);
v___x_1754_ = v___x_1734_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1757_, lean_object* v_k_1758_, lean_object* v_v_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1757_, v___x_1760_, v_k_1758_, v_v_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1763_, size_t v_x_1764_, size_t v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
lean_object* v_es_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v_j_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_es_1768_ = lean_ctor_get(v_x_1763_, 0);
v___x_1769_ = ((size_t)31ULL);
v___x_1770_ = lean_usize_land(v_x_1764_, v___x_1769_);
v_j_1771_ = lean_usize_to_nat(v___x_1770_);
v___x_1772_ = lean_array_get_size(v_es_1768_);
v___x_1773_ = lean_nat_dec_lt(v_j_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec(v_j_1771_);
lean_dec(v_x_1767_);
lean_dec_ref(v_x_1766_);
return v_x_1763_;
}
else
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1812_; 
lean_inc_ref(v_es_1768_);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v_x_1763_, 0);
lean_dec(v_unused_1813_);
v___x_1775_ = v_x_1763_;
v_isShared_1776_ = v_isSharedCheck_1812_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1812_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_v_1777_; lean_object* v___x_1778_; lean_object* v_xs_x27_1779_; lean_object* v___y_1781_; 
v_v_1777_ = lean_array_fget(v_es_1768_, v_j_1771_);
v___x_1778_ = lean_box(0);
v_xs_x27_1779_ = lean_array_fset(v_es_1768_, v_j_1771_, v___x_1778_);
switch(lean_obj_tag(v_v_1777_))
{
case 0:
{
lean_object* v_key_1786_; lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1797_; 
v_key_1786_ = lean_ctor_get(v_v_1777_, 0);
v_val_1787_ = lean_ctor_get(v_v_1777_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_v_1777_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1789_ = v_v_1777_;
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_inc(v_key_1786_);
lean_dec(v_v_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1766_, v_key_1786_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1789_);
v___x_1792_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1786_, v_val_1787_, v_x_1766_, v_x_1767_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
v___y_1781_ = v___x_1793_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1795_; 
lean_dec(v_val_1787_);
lean_dec(v_key_1786_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_x_1767_);
lean_ctor_set(v___x_1789_, 0, v_x_1766_);
v___x_1795_ = v___x_1789_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_x_1766_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_x_1767_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
v___y_1781_ = v___x_1795_;
goto v___jp_1780_;
}
}
}
}
case 1:
{
lean_object* v_node_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1810_; 
v_node_1798_ = lean_ctor_get(v_v_1777_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_v_1777_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1800_ = v_v_1777_;
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_node_1798_);
lean_dec(v_v_1777_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1802_ = ((size_t)5ULL);
v___x_1803_ = lean_usize_shift_right(v_x_1764_, v___x_1802_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_x_1765_, v___x_1804_);
v___x_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1798_, v___x_1803_, v___x_1805_, v_x_1766_, v_x_1767_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1806_);
v___x_1808_ = v___x_1800_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v___y_1781_ = v___x_1808_;
goto v___jp_1780_;
}
}
}
default: 
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_x_1766_);
lean_ctor_set(v___x_1811_, 1, v_x_1767_);
v___y_1781_ = v___x_1811_;
goto v___jp_1780_;
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_array_fset(v_xs_x27_1779_, v_j_1771_, v___y_1781_);
lean_dec(v_j_1771_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1782_);
v___x_1784_ = v___x_1775_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v_ks_1814_; lean_object* v_vs_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1835_; 
v_ks_1814_ = lean_ctor_get(v_x_1763_, 0);
v_vs_1815_ = lean_ctor_get(v_x_1763_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1817_ = v_x_1763_;
v_isShared_1818_ = v_isSharedCheck_1835_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_vs_1815_);
lean_inc(v_ks_1814_);
lean_dec(v_x_1763_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1835_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_ks_1814_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_vs_1815_);
v___x_1820_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v_newNode_1821_; uint8_t v___y_1823_; size_t v___x_1829_; uint8_t v___x_1830_; 
v_newNode_1821_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1820_, v_x_1766_, v_x_1767_);
v___x_1829_ = ((size_t)7ULL);
v___x_1830_ = lean_usize_dec_le(v___x_1829_, v_x_1765_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1821_);
v___x_1832_ = lean_unsigned_to_nat(4u);
v___x_1833_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
lean_dec(v___x_1831_);
v___y_1823_ = v___x_1833_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___x_1830_;
goto v___jp_1822_;
}
v___jp_1822_:
{
if (v___y_1823_ == 0)
{
lean_object* v_ks_1824_; lean_object* v_vs_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_ks_1824_ = lean_ctor_get(v_newNode_1821_, 0);
lean_inc_ref(v_ks_1824_);
v_vs_1825_ = lean_ctor_get(v_newNode_1821_, 1);
lean_inc_ref(v_vs_1825_);
lean_dec_ref(v_newNode_1821_);
v___x_1826_ = lean_unsigned_to_nat(0u);
v___x_1827_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1765_, v_ks_1824_, v_vs_1825_, v___x_1826_, v___x_1827_);
lean_dec_ref(v_vs_1825_);
lean_dec_ref(v_ks_1824_);
return v___x_1828_;
}
else
{
return v_newNode_1821_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1836_, lean_object* v_keys_1837_, lean_object* v_vals_1838_, lean_object* v_i_1839_, lean_object* v_entries_1840_){
_start:
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_array_get_size(v_keys_1837_);
v___x_1842_ = lean_nat_dec_lt(v_i_1839_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec(v_i_1839_);
return v_entries_1840_;
}
else
{
lean_object* v_k_1843_; uint64_t v_configKey_1844_; lean_object* v_expr_1845_; lean_object* v_nargs_x3f_1846_; lean_object* v_v_1847_; uint64_t v___x_1848_; uint64_t v___y_1850_; 
v_k_1843_ = lean_array_fget_borrowed(v_keys_1837_, v_i_1839_);
v_configKey_1844_ = lean_ctor_get_uint64(v_k_1843_, sizeof(void*)*2);
v_expr_1845_ = lean_ctor_get(v_k_1843_, 0);
v_nargs_x3f_1846_ = lean_ctor_get(v_k_1843_, 1);
v_v_1847_ = lean_array_fget_borrowed(v_vals_1838_, v_i_1839_);
v___x_1848_ = l_Lean_Expr_hash(v_expr_1845_);
if (lean_obj_tag(v_nargs_x3f_1846_) == 0)
{
uint64_t v___x_1863_; 
v___x_1863_ = 11ULL;
v___y_1850_ = v___x_1863_;
goto v___jp_1849_;
}
else
{
lean_object* v_val_1864_; uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v___x_1867_; 
v_val_1864_ = lean_ctor_get(v_nargs_x3f_1846_, 0);
v___x_1865_ = lean_uint64_of_nat(v_val_1864_);
v___x_1866_ = 13ULL;
v___x_1867_ = lean_uint64_mix_hash(v___x_1865_, v___x_1866_);
v___y_1850_ = v___x_1867_;
goto v___jp_1849_;
}
v___jp_1849_:
{
uint64_t v___x_1851_; uint64_t v___x_1852_; size_t v_h_1853_; size_t v___x_1854_; lean_object* v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; size_t v_h_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1851_ = lean_uint64_mix_hash(v___x_1848_, v___y_1850_);
v___x_1852_ = lean_uint64_mix_hash(v_configKey_1844_, v___x_1851_);
v_h_1853_ = lean_uint64_to_usize(v___x_1852_);
v___x_1854_ = ((size_t)5ULL);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = ((size_t)1ULL);
v___x_1857_ = lean_usize_sub(v_depth_1836_, v___x_1856_);
v___x_1858_ = lean_usize_mul(v___x_1854_, v___x_1857_);
v_h_1859_ = lean_usize_shift_right(v_h_1853_, v___x_1858_);
v___x_1860_ = lean_nat_add(v_i_1839_, v___x_1855_);
lean_dec(v_i_1839_);
lean_inc(v_v_1847_);
lean_inc(v_k_1843_);
v___x_1861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1840_, v_h_1859_, v_depth_1836_, v_k_1843_, v_v_1847_);
v_i_1839_ = v___x_1860_;
v_entries_1840_ = v___x_1861_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1868_, lean_object* v_keys_1869_, lean_object* v_vals_1870_, lean_object* v_i_1871_, lean_object* v_entries_1872_){
_start:
{
size_t v_depth_boxed_1873_; lean_object* v_res_1874_; 
v_depth_boxed_1873_ = lean_unbox_usize(v_depth_1868_);
lean_dec(v_depth_1868_);
v_res_1874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1873_, v_keys_1869_, v_vals_1870_, v_i_1871_, v_entries_1872_);
lean_dec_ref(v_vals_1870_);
lean_dec_ref(v_keys_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
size_t v_x_14004__boxed_1880_; size_t v_x_14005__boxed_1881_; lean_object* v_res_1882_; 
v_x_14004__boxed_1880_ = lean_unbox_usize(v_x_1876_);
lean_dec(v_x_1876_);
v_x_14005__boxed_1881_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_res_1882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1875_, v_x_14004__boxed_1880_, v_x_14005__boxed_1881_, v_x_1878_, v_x_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
uint64_t v_configKey_1886_; lean_object* v_expr_1887_; lean_object* v_nargs_x3f_1888_; uint64_t v___x_1889_; uint64_t v___y_1891_; 
v_configKey_1886_ = lean_ctor_get_uint64(v_x_1884_, sizeof(void*)*2);
v_expr_1887_ = lean_ctor_get(v_x_1884_, 0);
v_nargs_x3f_1888_ = lean_ctor_get(v_x_1884_, 1);
v___x_1889_ = l_Lean_Expr_hash(v_expr_1887_);
if (lean_obj_tag(v_nargs_x3f_1888_) == 0)
{
uint64_t v___x_1897_; 
v___x_1897_ = 11ULL;
v___y_1891_ = v___x_1897_;
goto v___jp_1890_;
}
else
{
lean_object* v_val_1898_; uint64_t v___x_1899_; uint64_t v___x_1900_; uint64_t v___x_1901_; 
v_val_1898_ = lean_ctor_get(v_nargs_x3f_1888_, 0);
v___x_1899_ = lean_uint64_of_nat(v_val_1898_);
v___x_1900_ = 13ULL;
v___x_1901_ = lean_uint64_mix_hash(v___x_1899_, v___x_1900_);
v___y_1891_ = v___x_1901_;
goto v___jp_1890_;
}
v___jp_1890_:
{
uint64_t v___x_1892_; uint64_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1892_ = lean_uint64_mix_hash(v___x_1889_, v___y_1891_);
v___x_1893_ = lean_uint64_mix_hash(v_configKey_1886_, v___x_1892_);
v___x_1894_ = lean_uint64_to_usize(v___x_1893_);
v___x_1895_ = ((size_t)1ULL);
v___x_1896_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1883_, v___x_1894_, v___x_1895_, v_x_1884_, v_x_1885_);
return v___x_1896_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = 0;
return v___x_1903_;
}
else
{
lean_object* v_head_1904_; lean_object* v_tail_1905_; uint8_t v___x_1906_; 
v_head_1904_ = lean_ctor_get(v_x_1902_, 0);
v_tail_1905_ = lean_ctor_get(v_x_1902_, 1);
v___x_1906_ = l_Lean_Level_hasMVar(v_head_1904_);
if (v___x_1906_ == 0)
{
v_x_1902_ = v_tail_1905_;
goto _start;
}
else
{
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1908_){
_start:
{
uint8_t v_res_1909_; lean_object* v_r_1910_; 
v_res_1909_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1908_);
lean_dec(v_x_1908_);
v_r_1910_ = lean_box(v_res_1909_);
return v_r_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1913_, lean_object* v_maxArgs_x3f_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
lean_inc(v_maxArgs_x3f_1914_);
lean_inc_ref(v_fn_1913_);
v___x_1920_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1913_, v_maxArgs_x3f_1914_, v_a_1915_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1985_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1985_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1985_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_finfo_1926_; lean_object* v___y_1927_; lean_object* v___x_1959_; lean_object* v_cache_1960_; lean_object* v_funInfo_1961_; lean_object* v___x_1962_; 
v___x_1959_ = lean_st_ref_get(v_a_1916_);
v_cache_1960_ = lean_ctor_get(v___x_1959_, 1);
lean_inc_ref(v_cache_1960_);
lean_dec(v___x_1959_);
v_funInfo_1961_ = lean_ctor_get(v_cache_1960_, 1);
lean_inc_ref(v_funInfo_1961_);
lean_dec_ref(v_cache_1960_);
v___x_1962_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1961_, v_a_1921_);
lean_dec_ref(v_funInfo_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___f_1963_; lean_object* v___f_1964_; 
v___f_1963_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1914_);
lean_inc_ref(v_fn_1913_);
v___f_1964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1964_, 0, v_fn_1913_);
lean_closure_set(v___f_1964_, 1, v_maxArgs_x3f_1914_);
lean_closure_set(v___f_1964_, 2, v___f_1963_);
if (lean_obj_tag(v_fn_1913_) == 4)
{
lean_object* v_declName_1965_; lean_object* v_us_1966_; uint8_t v___x_1967_; 
v_declName_1965_ = lean_ctor_get(v_fn_1913_, 0);
v_us_1966_ = lean_ctor_get(v_fn_1913_, 1);
v___x_1967_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc(v_us_1966_);
lean_inc_n(v_declName_1965_, 2);
lean_dec_ref_known(v_fn_1913_, 2);
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_));
v___x_1969_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1970_, 0, v_declName_1965_);
lean_ctor_set(v___x_1970_, 1, v_us_1966_);
lean_ctor_set(v___x_1970_, 2, v_maxArgs_x3f_1914_);
v___x_1971_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_1968_, v___x_1969_, v_declName_1965_, v___x_1970_, v___f_1964_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v_finfo_1926_ = v_a_1972_;
v___y_1927_ = v_a_1916_;
goto v___jp_1925_;
}
else
{
lean_del_object(v___x_1923_);
lean_dec(v_a_1921_);
return v___x_1971_;
}
}
else
{
lean_object* v___x_1973_; 
lean_dec_ref(v___f_1964_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
v___x_1973_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1913_, v_maxArgs_x3f_1914_, v___f_1963_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v_finfo_1926_ = v_a_1974_;
v___y_1927_ = v_a_1916_;
goto v___jp_1925_;
}
else
{
lean_del_object(v___x_1923_);
lean_dec(v_a_1921_);
return v___x_1973_;
}
}
}
else
{
lean_object* v___x_1975_; 
lean_dec_ref(v___f_1964_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
v___x_1975_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1913_, v_maxArgs_x3f_1914_, v___f_1963_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v_finfo_1926_ = v_a_1976_;
v___y_1927_ = v_a_1916_;
goto v___jp_1925_;
}
else
{
lean_del_object(v___x_1923_);
lean_dec(v_a_1921_);
return v___x_1975_;
}
}
}
else
{
lean_object* v_val_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_del_object(v___x_1923_);
lean_dec(v_a_1921_);
lean_dec(v_maxArgs_x3f_1914_);
lean_dec_ref(v_fn_1913_);
v_val_1977_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1962_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_val_1977_);
lean_dec(v___x_1962_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 0);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_val_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
v___jp_1925_:
{
lean_object* v___x_1928_; lean_object* v_cache_1929_; lean_object* v_mctx_1930_; lean_object* v_zetaDeltaFVarIds_1931_; lean_object* v_postponed_1932_; lean_object* v_diag_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1958_; 
v___x_1928_ = lean_st_ref_take(v___y_1927_);
v_cache_1929_ = lean_ctor_get(v___x_1928_, 1);
v_mctx_1930_ = lean_ctor_get(v___x_1928_, 0);
v_zetaDeltaFVarIds_1931_ = lean_ctor_get(v___x_1928_, 2);
v_postponed_1932_ = lean_ctor_get(v___x_1928_, 3);
v_diag_1933_ = lean_ctor_get(v___x_1928_, 4);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1935_ = v___x_1928_;
v_isShared_1936_ = v_isSharedCheck_1958_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_diag_1933_);
lean_inc(v_postponed_1932_);
lean_inc(v_zetaDeltaFVarIds_1931_);
lean_inc(v_cache_1929_);
lean_inc(v_mctx_1930_);
lean_dec(v___x_1928_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1958_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_inferType_1937_; lean_object* v_funInfo_1938_; lean_object* v_synthInstance_1939_; lean_object* v_whnf_1940_; lean_object* v_defEqTrans_1941_; lean_object* v_defEqPerm_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1957_; 
v_inferType_1937_ = lean_ctor_get(v_cache_1929_, 0);
v_funInfo_1938_ = lean_ctor_get(v_cache_1929_, 1);
v_synthInstance_1939_ = lean_ctor_get(v_cache_1929_, 2);
v_whnf_1940_ = lean_ctor_get(v_cache_1929_, 3);
v_defEqTrans_1941_ = lean_ctor_get(v_cache_1929_, 4);
v_defEqPerm_1942_ = lean_ctor_get(v_cache_1929_, 5);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_cache_1929_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1944_ = v_cache_1929_;
v_isShared_1945_ = v_isSharedCheck_1957_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_defEqPerm_1942_);
lean_inc(v_defEqTrans_1941_);
lean_inc(v_whnf_1940_);
lean_inc(v_synthInstance_1939_);
lean_inc(v_funInfo_1938_);
lean_inc(v_inferType_1937_);
lean_dec(v_cache_1929_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1957_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_inc_ref(v_finfo_1926_);
v___x_1946_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1938_, v_a_1921_, v_finfo_1926_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_inferType_1937_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_synthInstance_1939_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_whnf_1940_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_defEqTrans_1941_);
lean_ctor_set(v_reuseFailAlloc_1956_, 5, v_defEqPerm_1942_);
v___x_1948_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v___x_1948_);
v___x_1950_ = v___x_1935_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_mctx_1930_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_zetaDeltaFVarIds_1931_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_postponed_1932_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_diag_1933_);
v___x_1950_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = lean_st_ref_set(v___y_1927_, v___x_1950_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v_finfo_1926_);
v___x_1953_ = v___x_1923_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_finfo_1926_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
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
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_maxArgs_x3f_1914_);
lean_dec_ref(v_fn_1913_);
v_a_1986_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1920_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1920_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_1994_, lean_object* v_maxArgs_x3f_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_1994_, v_maxArgs_x3f_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_2002_, lean_object* v_k_2003_, lean_object* v_t_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_2003_, v_t_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2006_, lean_object* v_k_2007_, lean_object* v_t_2008_){
_start:
{
uint8_t v_res_2009_; lean_object* v_r_2010_; 
v_res_2009_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2006_, v_k_2007_, v_t_2008_);
lean_dec(v_t_2008_);
lean_dec(v_k_2007_);
v_r_2010_ = lean_box(v_res_2009_);
return v_r_2010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2011_, lean_object* v_val_2012_, lean_object* v___x_2013_, lean_object* v_fvars_2014_, uint8_t v___y_2015_, lean_object* v_inst_2016_, lean_object* v_R_2017_, lean_object* v_a_2018_, lean_object* v_b_2019_, lean_object* v_c_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2011_, v_val_2012_, v___x_2013_, v_fvars_2014_, v___y_2015_, v_a_2018_, v_b_2019_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2027_, lean_object* v_val_2028_, lean_object* v___x_2029_, lean_object* v_fvars_2030_, lean_object* v___y_2031_, lean_object* v_inst_2032_, lean_object* v_R_2033_, lean_object* v_a_2034_, lean_object* v_b_2035_, lean_object* v_c_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v___y_14359__boxed_2042_; lean_object* v_res_2043_; 
v___y_14359__boxed_2042_ = lean_unbox(v___y_2031_);
v_res_2043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2027_, v_val_2028_, v___x_2029_, v_fvars_2030_, v___y_14359__boxed_2042_, v_inst_2032_, v_R_2033_, v_a_2034_, v_b_2035_, v_c_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_fvars_2030_);
lean_dec_ref(v___x_2029_);
lean_dec_ref(v_val_2028_);
lean_dec(v_upperBound_2027_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2044_, lean_object* v_fvars_2045_, lean_object* v_inst_2046_, lean_object* v_R_2047_, lean_object* v_a_2048_, lean_object* v_b_2049_, lean_object* v_c_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2044_, v_fvars_2045_, v_a_2048_, v_b_2049_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2057_, lean_object* v_fvars_2058_, lean_object* v_inst_2059_, lean_object* v_R_2060_, lean_object* v_a_2061_, lean_object* v_b_2062_, lean_object* v_c_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2057_, v_fvars_2058_, v_inst_2059_, v_R_2060_, v_a_2061_, v_b_2062_, v_c_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec_ref(v_fvars_2058_);
lean_dec(v_upperBound_2057_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2071_, v_x_2072_, v_x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2076_, v_x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2079_, v_x_2080_, v_x_2081_);
lean_dec_ref(v_x_2081_);
lean_dec_ref(v_x_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2083_, lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2091_, lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2091_, v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_forConst_2102_, lean_object* v_key_2103_, lean_object* v_realize_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2100_, v_inst_2101_, v_forConst_2102_, v_key_2103_, v_realize_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_forConst_2114_, lean_object* v_key_2115_, lean_object* v_realize_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2111_, v_inst_2112_, v_inst_2113_, v_forConst_2114_, v_key_2115_, v_realize_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2123_, lean_object* v_x_2124_, size_t v_x_2125_, size_t v_x_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2124_, v_x_2125_, v_x_2126_, v_x_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
size_t v_x_14456__boxed_2136_; size_t v_x_14457__boxed_2137_; lean_object* v_res_2138_; 
v_x_14456__boxed_2136_ = lean_unbox_usize(v_x_2132_);
lean_dec(v_x_2132_);
v_x_14457__boxed_2137_ = lean_unbox_usize(v_x_2133_);
lean_dec(v_x_2133_);
v_res_2138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2130_, v_x_2131_, v_x_14456__boxed_2136_, v_x_14457__boxed_2137_, v_x_2134_, v_x_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2139_, lean_object* v_x_2140_, size_t v_x_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2140_, v_x_2141_, v_x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
size_t v_x_14473__boxed_2148_; lean_object* v_res_2149_; 
v_x_14473__boxed_2148_ = lean_unbox_usize(v_x_2146_);
lean_dec(v_x_2146_);
v_res_2149_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2144_, v_x_2145_, v_x_14473__boxed_2148_, v_x_2147_);
lean_dec_ref(v_x_2147_);
lean_dec_ref(v_x_2145_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2150_, lean_object* v_n_2151_, lean_object* v_k_2152_, lean_object* v_v_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2151_, v_k_2152_, v_v_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2155_, size_t v_depth_2156_, lean_object* v_keys_2157_, lean_object* v_vals_2158_, lean_object* v_heq_2159_, lean_object* v_i_2160_, lean_object* v_entries_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2156_, v_keys_2157_, v_vals_2158_, v_i_2160_, v_entries_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2163_, lean_object* v_depth_2164_, lean_object* v_keys_2165_, lean_object* v_vals_2166_, lean_object* v_heq_2167_, lean_object* v_i_2168_, lean_object* v_entries_2169_){
_start:
{
size_t v_depth_boxed_2170_; lean_object* v_res_2171_; 
v_depth_boxed_2170_ = lean_unbox_usize(v_depth_2164_);
lean_dec(v_depth_2164_);
v_res_2171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2163_, v_depth_boxed_2170_, v_keys_2165_, v_vals_2166_, v_heq_2167_, v_i_2168_, v_entries_2169_);
lean_dec_ref(v_vals_2166_);
lean_dec_ref(v_keys_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2172_, lean_object* v_keys_2173_, lean_object* v_vals_2174_, lean_object* v_heq_2175_, lean_object* v_i_2176_, lean_object* v_k_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2173_, v_vals_2174_, v_i_2176_, v_k_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2179_, lean_object* v_keys_2180_, lean_object* v_vals_2181_, lean_object* v_heq_2182_, lean_object* v_i_2183_, lean_object* v_k_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2179_, v_keys_2180_, v_vals_2181_, v_heq_2182_, v_i_2183_, v_k_2184_);
lean_dec_ref(v_k_2184_);
lean_dec_ref(v_vals_2181_);
lean_dec_ref(v_keys_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2187_, v_x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2190_, v_x_2191_, v_x_2192_);
lean_dec_ref(v_x_2192_);
lean_dec_ref(v_x_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2195_, v_x_2196_, v_x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2199_, lean_object* v_m_2200_, lean_object* v_a_2201_){
_start:
{
uint8_t v___x_2202_; 
v___x_2202_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2200_, v_a_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2203_, lean_object* v_m_2204_, lean_object* v_a_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2203_, v_m_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_m_2204_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2209_, v_x_2210_, v_x_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2214_, lean_object* v_x_2215_, size_t v_x_2216_, lean_object* v_x_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2215_, v_x_2216_, v_x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
size_t v_x_14518__boxed_2223_; lean_object* v_res_2224_; 
v_x_14518__boxed_2223_ = lean_unbox_usize(v_x_2221_);
lean_dec(v_x_2221_);
v_res_2224_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2219_, v_x_2220_, v_x_14518__boxed_2223_, v_x_2222_);
lean_dec_ref(v_x_2222_);
lean_dec_ref(v_x_2220_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2225_, lean_object* v_x_2226_, size_t v_x_2227_, size_t v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2226_, v_x_2227_, v_x_2228_, v_x_2229_, v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
size_t v_x_14529__boxed_2238_; size_t v_x_14530__boxed_2239_; lean_object* v_res_2240_; 
v_x_14529__boxed_2238_ = lean_unbox_usize(v_x_2234_);
lean_dec(v_x_2234_);
v_x_14530__boxed_2239_ = lean_unbox_usize(v_x_2235_);
lean_dec(v_x_2235_);
v_res_2240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2232_, v_x_2233_, v_x_14529__boxed_2238_, v_x_14530__boxed_2239_, v_x_2236_, v_x_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2241_, lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2242_, v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_a_2246_, lean_object* v_x_2247_){
_start:
{
uint8_t v_res_2248_; lean_object* v_r_2249_; 
v_res_2248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2245_, v_a_2246_, v_x_2247_);
lean_dec(v_x_2247_);
lean_dec(v_a_2246_);
v_r_2249_ = lean_box(v_res_2248_);
return v_r_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2250_, lean_object* v_keys_2251_, lean_object* v_vals_2252_, lean_object* v_heq_2253_, lean_object* v_i_2254_, lean_object* v_k_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2251_, v_vals_2252_, v_i_2254_, v_k_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2257_, lean_object* v_keys_2258_, lean_object* v_vals_2259_, lean_object* v_heq_2260_, lean_object* v_i_2261_, lean_object* v_k_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2257_, v_keys_2258_, v_vals_2259_, v_heq_2260_, v_i_2261_, v_k_2262_);
lean_dec_ref(v_k_2262_);
lean_dec_ref(v_vals_2259_);
lean_dec_ref(v_keys_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2264_, lean_object* v_n_2265_, lean_object* v_k_2266_, lean_object* v_v_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2265_, v_k_2266_, v_v_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2269_, size_t v_depth_2270_, lean_object* v_keys_2271_, lean_object* v_vals_2272_, lean_object* v_heq_2273_, lean_object* v_i_2274_, lean_object* v_entries_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2270_, v_keys_2271_, v_vals_2272_, v_i_2274_, v_entries_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2277_, lean_object* v_depth_2278_, lean_object* v_keys_2279_, lean_object* v_vals_2280_, lean_object* v_heq_2281_, lean_object* v_i_2282_, lean_object* v_entries_2283_){
_start:
{
size_t v_depth_boxed_2284_; lean_object* v_res_2285_; 
v_depth_boxed_2284_ = lean_unbox_usize(v_depth_2278_);
lean_dec(v_depth_2278_);
v_res_2285_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2277_, v_depth_boxed_2284_, v_keys_2279_, v_vals_2280_, v_heq_2281_, v_i_2282_, v_entries_2283_);
lean_dec_ref(v_vals_2280_);
lean_dec_ref(v_keys_2279_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2287_, v_x_2288_, v_x_2289_, v_x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2292_, lean_object* v_maxArgs_x3f_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2292_, v_maxArgs_x3f_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2300_, lean_object* v_maxArgs_x3f_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Meta_getFunInfo(v_fn_2300_, v_maxArgs_x3f_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2308_, lean_object* v_nargs_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v_nargs_2309_);
v___x_2316_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2308_, v___x_2315_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2317_, lean_object* v_nargs_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2317_, v_nargs_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2325_){
_start:
{
lean_object* v_paramInfo_2326_; lean_object* v___x_2327_; 
v_paramInfo_2326_ = lean_ctor_get(v_info_2325_, 0);
v___x_2327_ = lean_array_get_size(v_paramInfo_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Meta_FunInfo_getArity(v_info_2328_);
lean_dec_ref(v_info_2328_);
return v_res_2329_;
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
