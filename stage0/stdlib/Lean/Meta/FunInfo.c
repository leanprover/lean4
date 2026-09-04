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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FunInfo"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(112, 52, 23, 53, 37, 12, 118, 217)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 147, 169, 8, 188, 234, 221, 232)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(140, 0, 92, 209, 70, 2, 10, 135)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(176, 237, 136, 34, 252, 176, 16, 86)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_string_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "FunInfoEnvCacheKey"};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
static const lean_ctor_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),((lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value),LEAN_SCALAR_PTR_LITERAL(77, 18, 248, 164, 207, 212, 124, 226)}};
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_ = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instTypeNameFunInfoEnvCacheKey = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65__value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint64_t v_x_108__boxed_54_; uint64_t v_res_55_; lean_object* v_r_56_; 
v_x_108__boxed_54_ = lean_unbox_uint64(v_x_52_);
lean_dec_ref(v_x_52_);
v_res_55_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v_x_108__boxed_54_, v_x_53_);
lean_dec(v_x_53_);
v_r_56_ = lean_box_uint64(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(lean_object* v_x_57_){
_start:
{
lean_object* v_c_58_; lean_object* v_ls_59_; lean_object* v_maxArgs_x3f_60_; uint64_t v___x_61_; uint64_t v___y_63_; 
v_c_58_ = lean_ctor_get(v_x_57_, 0);
v_ls_59_ = lean_ctor_get(v_x_57_, 1);
v_maxArgs_x3f_60_ = lean_ctor_get(v_x_57_, 2);
v___x_61_ = 0ULL;
if (lean_obj_tag(v_c_58_) == 0)
{
uint64_t v___x_75_; 
v___x_75_ = 1723ULL;
v___y_63_ = v___x_75_;
goto v___jp_62_;
}
else
{
uint64_t v_hash_76_; 
v_hash_76_ = lean_ctor_get_uint64(v_c_58_, sizeof(void*)*2);
v___y_63_ = v_hash_76_;
goto v___jp_62_;
}
v___jp_62_:
{
uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; 
v___x_64_ = lean_uint64_mix_hash(v___x_61_, v___y_63_);
v___x_65_ = 7ULL;
v___x_66_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v___x_65_, v_ls_59_);
v___x_67_ = lean_uint64_mix_hash(v___x_64_, v___x_66_);
if (lean_obj_tag(v_maxArgs_x3f_60_) == 0)
{
uint64_t v___x_68_; uint64_t v___x_69_; 
v___x_68_ = 11ULL;
v___x_69_ = lean_uint64_mix_hash(v___x_67_, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; 
v_val_70_ = lean_ctor_get(v_maxArgs_x3f_60_, 0);
v___x_71_ = lean_uint64_of_nat(v_val_70_);
v___x_72_ = 13ULL;
v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
v___x_74_ = lean_uint64_mix_hash(v___x_67_, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(lean_object* v_x_77_){
_start:
{
uint64_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_77_);
lean_dec_ref(v_x_77_);
v_r_79_ = lean_box_uint64(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* v_fn_116_, lean_object* v_maxArgs_x3f_117_, lean_object* v_k_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; 
lean_inc(v_maxArgs_x3f_117_);
lean_inc_ref(v_fn_116_);
v___x_124_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_116_, v_maxArgs_x3f_117_, v_a_119_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_192_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_192_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_192_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_192_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v_cache_130_; lean_object* v_funInfo_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_finfo_135_; lean_object* v___y_136_; lean_object* v___x_168_; 
v___x_129_ = lean_st_ref_get(v_a_120_);
v_cache_130_ = lean_ctor_get(v___x_129_, 1);
lean_inc_ref(v_cache_130_);
lean_dec(v___x_129_);
v_funInfo_131_ = lean_ctor_get(v_cache_130_, 1);
lean_inc_ref(v_funInfo_131_);
lean_dec_ref(v_cache_130_);
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0));
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1));
lean_inc(v_a_125_);
v___x_168_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_132_, v___x_133_, v_funInfo_131_, v_a_125_);
lean_dec_ref(v_funInfo_131_);
if (lean_obj_tag(v___x_168_) == 0)
{
if (lean_obj_tag(v_fn_116_) == 4)
{
lean_object* v_declName_169_; lean_object* v_us_170_; lean_object* v___f_171_; uint8_t v___x_172_; 
v_declName_169_ = lean_ctor_get(v_fn_116_, 0);
lean_inc(v_declName_169_);
v_us_170_ = lean_ctor_get(v_fn_116_, 1);
lean_inc_n(v_us_170_, 2);
lean_dec_ref_known(v_fn_116_, 2);
v___f_171_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
v___x_172_ = l_List_any___redArg(v_us_170_, v___f_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0));
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0));
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_176_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_inc(v_declName_169_);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_declName_169_);
lean_ctor_set(v___x_177_, 1, v_us_170_);
lean_ctor_set(v___x_177_, 2, v_maxArgs_x3f_117_);
v___x_178_ = l_Lean_Meta_realizeValue___redArg(v___x_173_, v___x_174_, v___x_175_, v___x_176_, v_declName_169_, v___x_177_, v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v_finfo_135_ = v_a_179_;
v___y_136_ = v_a_120_;
goto v___jp_134_;
}
else
{
lean_del_object(v___x_127_);
lean_dec(v_a_125_);
return v___x_178_;
}
}
else
{
lean_object* v___x_180_; 
lean_dec(v_us_170_);
lean_dec(v_declName_169_);
lean_dec(v_maxArgs_x3f_117_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_180_ = lean_apply_5(v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v_finfo_135_ = v_a_181_;
v___y_136_ = v_a_120_;
goto v___jp_134_;
}
else
{
lean_del_object(v___x_127_);
lean_dec(v_a_125_);
return v___x_180_;
}
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_182_ = lean_apply_5(v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v_finfo_135_ = v_a_183_;
v___y_136_ = v_a_120_;
goto v___jp_134_;
}
else
{
lean_del_object(v___x_127_);
lean_dec(v_a_125_);
return v___x_182_;
}
}
}
else
{
lean_object* v_val_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_del_object(v___x_127_);
lean_dec(v_a_125_);
lean_dec_ref(v_k_118_);
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
v_val_184_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_168_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_val_184_);
lean_dec(v___x_168_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_val_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
v___jp_134_:
{
lean_object* v___x_137_; lean_object* v_cache_138_; lean_object* v_mctx_139_; lean_object* v_zetaDeltaFVarIds_140_; lean_object* v_postponed_141_; lean_object* v_diag_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_167_; 
v___x_137_ = lean_st_ref_take(v___y_136_);
v_cache_138_ = lean_ctor_get(v___x_137_, 1);
v_mctx_139_ = lean_ctor_get(v___x_137_, 0);
v_zetaDeltaFVarIds_140_ = lean_ctor_get(v___x_137_, 2);
v_postponed_141_ = lean_ctor_get(v___x_137_, 3);
v_diag_142_ = lean_ctor_get(v___x_137_, 4);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_167_ == 0)
{
v___x_144_ = v___x_137_;
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_diag_142_);
lean_inc(v_postponed_141_);
lean_inc(v_zetaDeltaFVarIds_140_);
lean_inc(v_cache_138_);
lean_inc(v_mctx_139_);
lean_dec(v___x_137_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_inferType_146_; lean_object* v_funInfo_147_; lean_object* v_synthInstance_148_; lean_object* v_whnf_149_; lean_object* v_defEqTrans_150_; lean_object* v_defEqPerm_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_166_; 
v_inferType_146_ = lean_ctor_get(v_cache_138_, 0);
v_funInfo_147_ = lean_ctor_get(v_cache_138_, 1);
v_synthInstance_148_ = lean_ctor_get(v_cache_138_, 2);
v_whnf_149_ = lean_ctor_get(v_cache_138_, 3);
v_defEqTrans_150_ = lean_ctor_get(v_cache_138_, 4);
v_defEqPerm_151_ = lean_ctor_get(v_cache_138_, 5);
v_isSharedCheck_166_ = !lean_is_exclusive(v_cache_138_);
if (v_isSharedCheck_166_ == 0)
{
v___x_153_ = v_cache_138_;
v_isShared_154_ = v_isSharedCheck_166_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_defEqPerm_151_);
lean_inc(v_defEqTrans_150_);
lean_inc(v_whnf_149_);
lean_inc(v_synthInstance_148_);
lean_inc(v_funInfo_147_);
lean_inc(v_inferType_146_);
lean_dec(v_cache_138_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_166_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_inc_ref(v_finfo_135_);
v___x_155_ = l_Lean_PersistentHashMap_insert___redArg(v___x_132_, v___x_133_, v_funInfo_147_, v_a_125_, v_finfo_135_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_inferType_146_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_synthInstance_148_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_whnf_149_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_defEqTrans_150_);
lean_ctor_set(v_reuseFailAlloc_165_, 5, v_defEqPerm_151_);
v___x_157_ = v_reuseFailAlloc_165_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_157_);
v___x_159_ = v___x_144_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_mctx_139_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_zetaDeltaFVarIds_140_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_postponed_141_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v_diag_142_);
v___x_159_ = v_reuseFailAlloc_164_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_st_ref_put(v___y_136_, v___x_159_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v_finfo_135_);
v___x_162_ = v___x_127_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_finfo_135_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
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
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_k_118_);
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
v_a_193_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_124_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_124_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(lean_object* v_fn_201_, lean_object* v_maxArgs_x3f_202_, lean_object* v_k_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(v_fn_201_, v_maxArgs_x3f_202_, v_k_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object* v_e_210_, lean_object* v_deps_211_, lean_object* v_k_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_Lean_Expr_hasFVar(v_e_210_);
if (v___x_213_ == 0)
{
lean_dec(v_k_212_);
return v_deps_211_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_apply_1(v_k_212_, v_deps_211_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object* v_e_215_, lean_object* v_deps_216_, lean_object* v_k_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(v_e_215_, v_deps_216_, v_k_217_);
lean_dec_ref(v_e_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* v_00_u03b1_219_, lean_object* v_e_220_, lean_object* v_deps_221_, lean_object* v_k_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_Expr_hasFVar(v_e_220_);
if (v___x_223_ == 0)
{
lean_dec(v_k_222_);
return v_deps_221_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_apply_1(v_k_222_, v_deps_221_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object* v_00_u03b1_225_, lean_object* v_e_226_, lean_object* v_deps_227_, lean_object* v_k_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(v_00_u03b1_225_, v_e_226_, v_deps_227_, v_k_228_);
lean_dec_ref(v_e_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(lean_object* v_xs_230_, lean_object* v_v_231_, lean_object* v_i_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_array_get_size(v_xs_230_);
v___x_234_ = lean_nat_dec_lt(v_i_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v_i_232_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_array_fget_borrowed(v_xs_230_, v_i_232_);
v___x_237_ = lean_expr_eqv(v___x_236_, v_v_231_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_i_232_, v___x_238_);
lean_dec(v_i_232_);
v_i_232_ = v___x_239_;
goto _start;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_i_232_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_242_, lean_object* v_v_243_, lean_object* v_i_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_242_, v_v_243_, v_i_244_);
lean_dec_ref(v_v_243_);
lean_dec_ref(v_xs_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object* v_xs_246_, lean_object* v_v_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_246_, v_v_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object* v_xs_250_, lean_object* v_v_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_250_, v_v_251_);
lean_dec_ref(v_v_251_);
lean_dec_ref(v_xs_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* v_xs_253_, lean_object* v_v_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_253_, v_v_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_val_257_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_255_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_val_257_);
lean_dec(v___x_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_val_257_);
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
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* v_xs_265_, lean_object* v_v_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_xs_265_, v_v_266_);
lean_dec_ref(v_v_266_);
lean_dec_ref(v_xs_265_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(lean_object* v_a_268_, lean_object* v_as_269_, size_t v_i_270_, size_t v_stop_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_eq(v_i_270_, v_stop_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_array_uget_borrowed(v_as_269_, v_i_270_);
v___x_274_ = lean_nat_dec_eq(v_a_268_, v___x_273_);
if (v___x_274_ == 0)
{
size_t v___x_275_; size_t v___x_276_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_270_, v___x_275_);
v_i_270_ = v___x_276_;
goto _start;
}
else
{
return v___x_274_;
}
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(lean_object* v_a_279_, lean_object* v_as_280_, lean_object* v_i_281_, lean_object* v_stop_282_){
_start:
{
size_t v_i_boxed_283_; size_t v_stop_boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_i_boxed_283_ = lean_unbox_usize(v_i_281_);
lean_dec(v_i_281_);
v_stop_boxed_284_ = lean_unbox_usize(v_stop_282_);
lean_dec(v_stop_282_);
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_279_, v_as_280_, v_i_boxed_283_, v_stop_boxed_284_);
lean_dec_ref(v_as_280_);
lean_dec(v_a_279_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object* v_as_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_array_get_size(v_as_287_);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
return v___x_291_;
}
else
{
if (v___x_291_ == 0)
{
return v___x_291_;
}
else
{
size_t v___x_292_; size_t v___x_293_; uint8_t v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_290_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_288_, v_as_287_, v___x_292_, v___x_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object* v_as_295_, lean_object* v_a_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_as_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* v_fvars_299_, lean_object* v_e_300_, lean_object* v_deps_301_){
_start:
{
lean_object* v_d_303_; lean_object* v_b_304_; 
switch(lean_obj_tag(v_e_300_))
{
case 5:
{
lean_object* v_fn_308_; lean_object* v_arg_309_; uint8_t v___x_310_; 
v_fn_308_ = lean_ctor_get(v_e_300_, 0);
v_arg_309_ = lean_ctor_get(v_e_300_, 1);
v___x_310_ = l_Lean_Expr_hasFVar(v_e_300_);
if (v___x_310_ == 0)
{
return v_deps_301_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_299_, v_fn_308_, v_deps_301_);
v_e_300_ = v_arg_309_;
v_deps_301_ = v___x_311_;
goto _start;
}
}
case 7:
{
lean_object* v_binderType_313_; lean_object* v_body_314_; 
v_binderType_313_ = lean_ctor_get(v_e_300_, 1);
v_body_314_ = lean_ctor_get(v_e_300_, 2);
v_d_303_ = v_binderType_313_;
v_b_304_ = v_body_314_;
goto v___jp_302_;
}
case 6:
{
lean_object* v_binderType_315_; lean_object* v_body_316_; 
v_binderType_315_ = lean_ctor_get(v_e_300_, 1);
v_body_316_ = lean_ctor_get(v_e_300_, 2);
v_d_303_ = v_binderType_315_;
v_b_304_ = v_body_316_;
goto v___jp_302_;
}
case 8:
{
lean_object* v_type_317_; lean_object* v_value_318_; lean_object* v_body_319_; uint8_t v___x_320_; 
v_type_317_ = lean_ctor_get(v_e_300_, 1);
v_value_318_ = lean_ctor_get(v_e_300_, 2);
v_body_319_ = lean_ctor_get(v_e_300_, 3);
v___x_320_ = l_Lean_Expr_hasFVar(v_e_300_);
if (v___x_320_ == 0)
{
return v_deps_301_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_299_, v_type_317_, v_deps_301_);
v___x_322_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_299_, v_value_318_, v___x_321_);
v_e_300_ = v_body_319_;
v_deps_301_ = v___x_322_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_324_; 
v_struct_324_ = lean_ctor_get(v_e_300_, 2);
v_e_300_ = v_struct_324_;
goto _start;
}
case 10:
{
lean_object* v_expr_326_; 
v_expr_326_ = lean_ctor_get(v_e_300_, 1);
v_e_300_ = v_expr_326_;
goto _start;
}
case 1:
{
lean_object* v___x_328_; 
v___x_328_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_299_, v_e_300_);
if (lean_obj_tag(v___x_328_) == 0)
{
return v_deps_301_;
}
else
{
lean_object* v_val_329_; uint8_t v___x_330_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_deps_301_, v_val_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_array_push(v_deps_301_, v_val_329_);
return v___x_331_;
}
else
{
lean_dec(v_val_329_);
return v_deps_301_;
}
}
}
default: 
{
return v_deps_301_;
}
}
v___jp_302_:
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_Expr_hasFVar(v_e_300_);
if (v___x_305_ == 0)
{
return v_deps_301_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_299_, v_d_303_, v_deps_301_);
v_e_300_ = v_b_304_;
v_deps_301_ = v___x_306_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* v_fvars_332_, lean_object* v_e_333_, lean_object* v_deps_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_332_, v_e_333_, v_deps_334_);
lean_dec_ref(v_e_333_);
lean_dec_ref(v_fvars_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object* v_hi_336_, lean_object* v_pivot_337_, lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_k_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_nat_dec_lt(v_k_340_, v_hi_336_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_k_340_);
v___x_342_ = lean_array_fswap(v_as_338_, v_i_339_, v_hi_336_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_i_339_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_array_fget_borrowed(v_as_338_, v_k_340_);
v___x_345_ = lean_nat_dec_lt(v___x_344_, v_pivot_337_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_k_340_, v___x_346_);
lean_dec(v_k_340_);
v_k_340_ = v___x_347_;
goto _start;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = lean_array_fswap(v_as_338_, v_i_339_, v_k_340_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_i_339_, v___x_350_);
lean_dec(v_i_339_);
v___x_352_ = lean_nat_add(v_k_340_, v___x_350_);
lean_dec(v_k_340_);
v_as_338_ = v___x_349_;
v_i_339_ = v___x_351_;
v_k_340_ = v___x_352_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_354_, lean_object* v_pivot_355_, lean_object* v_as_356_, lean_object* v_i_357_, lean_object* v_k_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_354_, v_pivot_355_, v_as_356_, v_i_357_, v_k_358_);
lean_dec(v_pivot_355_);
lean_dec(v_hi_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_n_360_, lean_object* v_as_361_, lean_object* v_lo_362_, lean_object* v_hi_363_){
_start:
{
lean_object* v___y_365_; uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_lt(v_lo_362_, v_hi_363_);
if (v___x_375_ == 0)
{
lean_dec(v_lo_362_);
return v_as_361_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_mid_378_; lean_object* v___y_380_; lean_object* v___y_386_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_376_ = lean_nat_add(v_lo_362_, v_hi_363_);
v___x_377_ = lean_unsigned_to_nat(1u);
v_mid_378_ = lean_nat_shiftr(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
v___x_391_ = lean_array_fget_borrowed(v_as_361_, v_mid_378_);
v___x_392_ = lean_array_fget_borrowed(v_as_361_, v_lo_362_);
v___x_393_ = lean_nat_dec_lt(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
v___y_386_ = v_as_361_;
goto v___jp_385_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_array_fswap(v_as_361_, v_lo_362_, v_mid_378_);
v___y_386_ = v___x_394_;
goto v___jp_385_;
}
v___jp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_array_fget_borrowed(v___y_380_, v_mid_378_);
v___x_382_ = lean_array_fget_borrowed(v___y_380_, v_hi_363_);
v___x_383_ = lean_nat_dec_lt(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v_mid_378_);
v___y_365_ = v___y_380_;
goto v___jp_364_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_array_fswap(v___y_380_, v_mid_378_, v_hi_363_);
lean_dec(v_mid_378_);
v___y_365_ = v___x_384_;
goto v___jp_364_;
}
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_array_fget_borrowed(v___y_386_, v_hi_363_);
v___x_388_ = lean_array_fget_borrowed(v___y_386_, v_lo_362_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
v___y_380_ = v___y_386_;
goto v___jp_379_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = lean_array_fswap(v___y_386_, v_lo_362_, v_hi_363_);
v___y_380_ = v___x_390_;
goto v___jp_379_;
}
}
}
v___jp_364_:
{
lean_object* v_pivot_366_; lean_object* v___x_367_; lean_object* v_fst_368_; lean_object* v_snd_369_; uint8_t v___x_370_; 
v_pivot_366_ = lean_array_fget(v___y_365_, v_hi_363_);
lean_inc_n(v_lo_362_, 2);
v___x_367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_363_, v_pivot_366_, v___y_365_, v_lo_362_, v_lo_362_);
lean_dec(v_pivot_366_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_368_);
v_snd_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_snd_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_nat_dec_le(v_hi_363_, v_fst_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_360_, v_snd_369_, v_lo_362_, v_fst_368_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_fst_368_, v___x_372_);
lean_dec(v_fst_368_);
v_as_361_ = v___x_371_;
v_lo_362_ = v___x_373_;
goto _start;
}
else
{
lean_dec(v_fst_368_);
lean_dec(v_lo_362_);
return v_snd_369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_n_395_, lean_object* v_as_396_, lean_object* v_lo_397_, lean_object* v_hi_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_395_, v_as_396_, v_lo_397_, v_hi_398_);
lean_dec(v_hi_398_);
lean_dec(v_n_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_402_, lean_object* v_e_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_deps_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0));
v_deps_406_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_402_, v_e_403_, v___x_405_);
v___x_407_ = lean_array_get_size(v_deps_406_);
v___x_408_ = lean_nat_dec_eq(v___x_407_, v___x_404_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___y_412_; uint8_t v___x_416_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_sub(v___x_407_, v___x_409_);
v___x_416_ = lean_nat_dec_le(v___x_404_, v___x_410_);
if (v___x_416_ == 0)
{
lean_inc(v___x_410_);
v___y_412_ = v___x_410_;
goto v___jp_411_;
}
else
{
v___y_412_ = v___x_404_;
goto v___jp_411_;
}
v___jp_411_:
{
uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_le(v___y_412_, v___x_410_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v___x_410_);
lean_inc(v___y_412_);
v___x_414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_407_, v_deps_406_, v___y_412_, v___y_412_);
lean_dec(v___y_412_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_407_, v_deps_406_, v___y_412_, v___x_410_);
lean_dec(v___x_410_);
return v___x_415_;
}
}
}
else
{
return v_deps_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_417_, lean_object* v_e_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_417_, v_e_418_);
lean_dec_ref(v_e_418_);
lean_dec_ref(v_fvars_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_420_, lean_object* v_as_421_, lean_object* v_lo_422_, lean_object* v_hi_423_, lean_object* v_w_424_, lean_object* v_hlo_425_, lean_object* v_hhi_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_420_, v_as_421_, v_lo_422_, v_hi_423_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_428_, lean_object* v_as_429_, lean_object* v_lo_430_, lean_object* v_hi_431_, lean_object* v_w_432_, lean_object* v_hlo_433_, lean_object* v_hhi_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_428_, v_as_429_, v_lo_430_, v_hi_431_, v_w_432_, v_hlo_433_, v_hhi_434_);
lean_dec(v_hi_431_);
lean_dec(v_n_428_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object* v_n_436_, lean_object* v_lo_437_, lean_object* v_hi_438_, lean_object* v_hhi_439_, lean_object* v_pivot_440_, lean_object* v_as_441_, lean_object* v_i_442_, lean_object* v_k_443_, lean_object* v_ilo_444_, lean_object* v_ik_445_, lean_object* v_w_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_438_, v_pivot_440_, v_as_441_, v_i_442_, v_k_443_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object* v_n_448_, lean_object* v_lo_449_, lean_object* v_hi_450_, lean_object* v_hhi_451_, lean_object* v_pivot_452_, lean_object* v_as_453_, lean_object* v_i_454_, lean_object* v_k_455_, lean_object* v_ilo_456_, lean_object* v_ik_457_, lean_object* v_w_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_448_, v_lo_449_, v_hi_450_, v_hhi_451_, v_pivot_452_, v_as_453_, v_i_454_, v_k_455_, v_ilo_456_, v_ik_457_, v_w_458_);
lean_dec(v_pivot_452_);
lean_dec(v_hi_450_);
lean_dec(v_lo_449_);
lean_dec(v_n_448_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_bs_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_464_ == 0)
{
return v_bs_463_;
}
else
{
lean_object* v_v_465_; uint8_t v_binderInfo_466_; uint8_t v_hasFwdDeps_467_; lean_object* v_backDeps_468_; uint8_t v_isProp_469_; uint8_t v_isDecInst_470_; uint8_t v_isInstance_471_; uint8_t v_higherOrderOutParam_472_; uint8_t v_dependsOnHigherOrderOutParam_473_; lean_object* v___x_474_; lean_object* v_bs_x27_475_; lean_object* v___y_477_; 
v_v_465_ = lean_array_uget(v_bs_463_, v_i_462_);
v_binderInfo_466_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1);
v_hasFwdDeps_467_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 1);
v_backDeps_468_ = lean_ctor_get(v_v_465_, 0);
v_isProp_469_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 2);
v_isDecInst_470_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 3);
v_isInstance_471_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_472_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_473_ = lean_ctor_get_uint8(v_v_465_, sizeof(void*)*1 + 6);
v___x_474_ = lean_unsigned_to_nat(0u);
v_bs_x27_475_ = lean_array_uset(v_bs_463_, v_i_462_, v___x_474_);
if (v_hasFwdDeps_467_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_usize_to_nat(v_i_462_);
v___x_483_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_460_, v___x_482_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
v___y_477_ = v_v_465_;
goto v___jp_476_;
}
else
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_inc_ref(v_backDeps_468_);
v_isSharedCheck_490_ = !lean_is_exclusive(v_v_465_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_v_465_, 0);
lean_dec(v_unused_491_);
v___x_485_ = v_v_465_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_v_465_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_backDeps_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1, v_binderInfo_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1 + 2, v_isProp_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1 + 3, v_isDecInst_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1 + 4, v_isInstance_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1 + 5, v_higherOrderOutParam_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_489_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_473_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*1 + 1, v___x_483_);
v___y_477_ = v___x_488_;
goto v___jp_476_;
}
}
}
}
else
{
v___y_477_ = v_v_465_;
goto v___jp_476_;
}
v___jp_476_:
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_462_, v___x_478_);
v___x_480_ = lean_array_uset(v_bs_x27_475_, v_i_462_, v___y_477_);
v_i_462_ = v___x_479_;
v_bs_463_ = v___x_480_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_bs_495_){
_start:
{
size_t v_sz_boxed_496_; size_t v_i_boxed_497_; lean_object* v_res_498_; 
v_sz_boxed_496_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_497_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_492_, v_sz_boxed_496_, v_i_boxed_497_, v_bs_495_);
lean_dec_ref(v_backDeps_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* v_pinfo_499_, lean_object* v_backDeps_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_array_get_size(v_backDeps_500_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_nat_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
size_t v_sz_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_sz_504_ = lean_array_size(v_pinfo_499_);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_500_, v_sz_504_, v___x_505_, v_pinfo_499_);
return v___x_506_;
}
else
{
return v_pinfo_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* v_pinfo_507_, lean_object* v_backDeps_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_pinfo_507_, v_backDeps_508_);
lean_dec_ref(v_backDeps_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_510_, lean_object* v_as_511_, size_t v_sz_512_, size_t v_i_513_, lean_object* v_bs_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_510_, v_sz_512_, v_i_513_, v_bs_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_516_, lean_object* v_as_517_, lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_bs_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_516_, v_as_517_, v_sz_boxed_521_, v_i_boxed_522_, v_bs_520_);
lean_dec_ref(v_as_517_);
lean_dec_ref(v_backDeps_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(lean_object* v_k_524_, lean_object* v_b_525_, lean_object* v_c_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; 
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
v___x_532_ = lean_apply_7(v_k_524_, v_b_525_, v_c_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, lean_box(0));
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_533_, lean_object* v_b_534_, lean_object* v_c_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_533_, v_b_534_, v_c_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* v_type_542_, lean_object* v_k_543_, uint8_t v_cleanupAnnotations_544_, uint8_t v_whnfType_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___f_551_; lean_object* v___x_552_; 
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_551_, 0, v_k_543_);
v___x_552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_542_, v___f_551_, v_cleanupAnnotations_544_, v_whnfType_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_552_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_552_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* v_type_569_, lean_object* v_k_570_, lean_object* v_cleanupAnnotations_571_, lean_object* v_whnfType_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_578_; uint8_t v_whnfType_boxed_579_; lean_object* v_res_580_; 
v_cleanupAnnotations_boxed_578_ = lean_unbox(v_cleanupAnnotations_571_);
v_whnfType_boxed_579_ = lean_unbox(v_whnfType_572_);
v_res_580_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_569_, v_k_570_, v_cleanupAnnotations_boxed_578_, v_whnfType_boxed_579_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* v_00_u03b1_581_, lean_object* v_type_582_, lean_object* v_k_583_, uint8_t v_cleanupAnnotations_584_, uint8_t v_whnfType_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_582_, v_k_583_, v_cleanupAnnotations_584_, v_whnfType_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* v_00_u03b1_592_, lean_object* v_type_593_, lean_object* v_k_594_, lean_object* v_cleanupAnnotations_595_, lean_object* v_whnfType_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_602_; uint8_t v_whnfType_boxed_603_; lean_object* v_res_604_; 
v_cleanupAnnotations_boxed_602_ = lean_unbox(v_cleanupAnnotations_595_);
v_whnfType_boxed_603_ = lean_unbox(v_whnfType_596_);
v_res_604_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_592_, v_type_593_, v_k_594_, v_cleanupAnnotations_boxed_602_, v_whnfType_boxed_603_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___f_612_; lean_object* v___x_8494__overap_613_; lean_object* v___x_614_; 
v___f_612_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_8494__overap_613_ = lean_panic_fn_borrowed(v___f_612_, v_msg_606_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
v___x_614_ = lean_apply_5(v___x_8494__overap_613_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* v_type_622_, lean_object* v_maxFVars_x3f_623_, lean_object* v_k_624_, uint8_t v_cleanupAnnotations_625_, uint8_t v_whnfType_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___f_632_; lean_object* v___x_633_; 
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_632_, 0, v_k_624_);
v___x_633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_622_, v_maxFVars_x3f_623_, v___f_632_, v_cleanupAnnotations_625_, v_whnfType_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* v_type_650_, lean_object* v_maxFVars_x3f_651_, lean_object* v_k_652_, lean_object* v_cleanupAnnotations_653_, lean_object* v_whnfType_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_660_; uint8_t v_whnfType_boxed_661_; lean_object* v_res_662_; 
v_cleanupAnnotations_boxed_660_ = lean_unbox(v_cleanupAnnotations_653_);
v_whnfType_boxed_661_ = lean_unbox(v_whnfType_654_);
v_res_662_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_650_, v_maxFVars_x3f_651_, v_k_652_, v_cleanupAnnotations_boxed_660_, v_whnfType_boxed_661_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* v_00_u03b1_663_, lean_object* v_type_664_, lean_object* v_maxFVars_x3f_665_, lean_object* v_k_666_, uint8_t v_cleanupAnnotations_667_, uint8_t v_whnfType_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_664_, v_maxFVars_x3f_665_, v_k_666_, v_cleanupAnnotations_667_, v_whnfType_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* v_00_u03b1_675_, lean_object* v_type_676_, lean_object* v_maxFVars_x3f_677_, lean_object* v_k_678_, lean_object* v_cleanupAnnotations_679_, lean_object* v_whnfType_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_686_; uint8_t v_whnfType_boxed_687_; lean_object* v_res_688_; 
v_cleanupAnnotations_boxed_686_ = lean_unbox(v_cleanupAnnotations_679_);
v_whnfType_boxed_687_ = lean_unbox(v_whnfType_680_);
v_res_688_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_675_, v_type_676_, v_maxFVars_x3f_677_, v_k_678_, v_cleanupAnnotations_boxed_686_, v_whnfType_boxed_687_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_689_, lean_object* v_val_690_, lean_object* v___x_691_, lean_object* v_fvars_692_, lean_object* v_next_693_, lean_object* v_upperBound_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_a_703_; uint8_t v___x_707_; 
v___x_707_ = lean_nat_dec_lt(v_a_695_, v_upperBound_689_);
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
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_774_; 
v_fst_709_ = lean_ctor_get(v_b_696_, 0);
v_snd_710_ = lean_ctor_get(v_b_696_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_b_696_);
if (v_isSharedCheck_774_ == 0)
{
v___x_712_ = v_b_696_;
v_isShared_713_ = v_isSharedCheck_774_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_b_696_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_774_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; 
v___x_714_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_690_, v_a_695_);
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
v___x_718_ = lean_array_fget_borrowed(v___x_691_, v_a_695_);
v___x_719_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_692_, v___x_718_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v___x_719_, 1);
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
lean_dec_ref_known(v___x_721_, 1);
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
lean_dec_ref_known(v___x_723_, 1);
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
lean_object* v_v_736_; uint8_t v_binderInfo_737_; uint8_t v_hasFwdDeps_738_; lean_object* v_backDeps_739_; uint8_t v_isProp_740_; uint8_t v_isDecInst_741_; uint8_t v_isInstance_742_; uint8_t v_dependsOnHigherOrderOutParam_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_754_; 
v_v_736_ = lean_array_fget(v_fst_709_, v_val_720_);
v_binderInfo_737_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1);
v_hasFwdDeps_738_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 1);
v_backDeps_739_ = lean_ctor_get(v_v_736_, 0);
v_isProp_740_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 2);
v_isDecInst_741_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 3);
v_isInstance_742_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_743_ = lean_ctor_get_uint8(v_v_736_, sizeof(void*)*1 + 6);
v_isSharedCheck_754_ = !lean_is_exclusive(v_v_736_);
if (v_isSharedCheck_754_ == 0)
{
v___x_745_ = v_v_736_;
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_backDeps_739_);
lean_dec(v_v_736_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v_xs_x27_749_; lean_object* v___x_751_; 
v___x_747_ = lean_nat_dec_lt(v_next_693_, v_upperBound_694_);
v___x_748_ = lean_box(0);
v_xs_x27_749_ = lean_array_fset(v_fst_709_, v_val_720_, v___x_748_);
if (v_isShared_746_ == 0)
{
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_backDeps_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1, v_binderInfo_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 1, v_hasFwdDeps_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 2, v_isProp_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 3, v_isDecInst_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 4, v_isInstance_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_743_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1 + 5, v___x_747_);
v___x_752_ = lean_array_fset(v_xs_x27_749_, v_val_720_, v___x_751_);
lean_dec(v_val_720_);
v___y_726_ = v___x_752_;
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
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_val_720_);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec(v_a_695_);
v_a_755_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_723_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_723_);
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
lean_dec(v_val_720_);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec(v_a_695_);
v_a_763_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_721_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_721_);
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
lean_dec(v___x_719_);
if (v_isShared_713_ == 0)
{
v___x_772_ = v___x_712_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_710_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_a_703_ = v___x_772_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_775_, lean_object* v_val_776_, lean_object* v___x_777_, lean_object* v_fvars_778_, lean_object* v_next_779_, lean_object* v_upperBound_780_, lean_object* v_a_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_775_, v_val_776_, v___x_777_, v_fvars_778_, v_next_779_, v_upperBound_780_, v_a_781_, v_b_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_upperBound_780_);
lean_dec(v_next_779_);
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
lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___y_874_; uint8_t v___y_875_; uint8_t v___y_876_; uint8_t v___y_956_; 
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
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1 + 6, v___y_875_);
v___x_887_ = lean_array_push(v___x_882_, v___x_884_);
if (v___y_876_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v___y_874_);
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
if (lean_obj_tag(v___y_874_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; 
v_val_891_ = lean_ctor_get(v___y_874_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___y_874_, 1);
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
v___x_908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_905_, v_val_895_, v___x_904_, v_fvars_847_, v_a_848_, v_upperBound_846_, v___x_897_, v___x_907_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
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
lean_dec(v___y_874_);
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
lean_dec(v___y_874_);
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
lean_dec(v___y_874_);
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
v___y_874_ = v_a_958_;
v___y_875_ = v___y_956_;
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
v___y_874_ = v_a_958_;
v___y_875_ = v___y_956_;
v___y_876_ = v___x_860_;
goto v___jp_873_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = 0;
v___y_874_ = v_a_958_;
v___y_875_ = v___y_956_;
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
lean_object* v___y_1054_; lean_object* v___x_1071_; 
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1071_ = lean_infer_type(v_fn_1045_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v_transparency_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Lean_Meta_Context_config(v___y_1048_);
v_transparency_1074_ = lean_ctor_get_uint8(v___x_1073_, 9);
lean_dec_ref(v___x_1073_);
v___x_1075_ = 1;
v___x_1076_ = 0;
v___x_1077_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1074_, v___x_1075_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1072_, v_maxArgs_x3f_1046_, v___f_1047_, v___x_1076_, v___x_1076_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
v___y_1054_ = v___x_1078_;
goto v___jp_1053_;
}
else
{
lean_object* v_keyedConfig_1079_; uint8_t v_trackZetaDelta_1080_; lean_object* v_zetaDeltaSet_1081_; lean_object* v_lctx_1082_; lean_object* v_localInstances_1083_; lean_object* v_defEqCtx_x3f_1084_; lean_object* v_synthPendingDepth_1085_; lean_object* v_customCanUnfoldPredicate_x3f_1086_; uint8_t v_univApprox_1087_; uint8_t v_inTypeClassResolution_1088_; uint8_t v_cacheInferType_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1098_; 
v_keyedConfig_1079_ = lean_ctor_get(v___y_1048_, 0);
v_trackZetaDelta_1080_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7);
v_zetaDeltaSet_1081_ = lean_ctor_get(v___y_1048_, 1);
v_lctx_1082_ = lean_ctor_get(v___y_1048_, 2);
v_localInstances_1083_ = lean_ctor_get(v___y_1048_, 3);
v_defEqCtx_x3f_1084_ = lean_ctor_get(v___y_1048_, 4);
v_synthPendingDepth_1085_ = lean_ctor_get(v___y_1048_, 5);
v_customCanUnfoldPredicate_x3f_1086_ = lean_ctor_get(v___y_1048_, 6);
v_univApprox_1087_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1088_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 2);
v_cacheInferType_1089_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*7 + 3);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1091_ = v___y_1048_;
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1086_);
lean_inc(v_synthPendingDepth_1085_);
lean_inc(v_defEqCtx_x3f_1084_);
lean_inc(v_localInstances_1083_);
lean_inc(v_lctx_1082_);
lean_inc(v_zetaDeltaSet_1081_);
lean_inc(v_keyedConfig_1079_);
lean_dec(v___y_1048_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1075_, v_keyedConfig_1079_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_zetaDeltaSet_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_lctx_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_localInstances_1083_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_defEqCtx_x3f_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_synthPendingDepth_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 6, v_customCanUnfoldPredicate_x3f_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*7, v_trackZetaDelta_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*7 + 1, v_univApprox_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*7 + 3, v_cacheInferType_1089_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1072_, v_maxArgs_x3f_1046_, v___f_1047_, v___x_1076_, v___x_1076_, v___x_1095_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___x_1095_);
v___y_1054_ = v___x_1096_;
goto v___jp_1053_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v___f_1047_);
lean_dec(v_maxArgs_x3f_1046_);
v_a_1099_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1071_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1071_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
v___jp_1053_:
{
if (lean_obj_tag(v___y_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___y_1054_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___y_1054_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___y_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___y_1054_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___y_1054_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___y_1054_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___y_1054_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1107_, lean_object* v_maxArgs_x3f_1108_, lean_object* v___f_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1107_, v_maxArgs_x3f_1108_, v___f_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_i_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_array_get_size(v_keys_1116_);
v___x_1121_ = lean_nat_dec_lt(v_i_1118_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec(v_i_1118_);
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_k_x27_1123_; uint8_t v___x_1124_; 
v_k_x27_1123_ = lean_array_fget_borrowed(v_keys_1116_, v_i_1118_);
v___x_1124_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1119_, v_k_x27_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v_i_1118_, v___x_1125_);
lean_dec(v_i_1118_);
v_i_1118_ = v___x_1126_;
goto _start;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_array_fget_borrowed(v_vals_1117_, v_i_1118_);
lean_dec(v_i_1118_);
lean_inc(v___x_1128_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1130_, lean_object* v_vals_1131_, lean_object* v_i_1132_, lean_object* v_k_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1130_, v_vals_1131_, v_i_1132_, v_k_1133_);
lean_dec_ref(v_k_1133_);
lean_dec_ref(v_vals_1131_);
lean_dec_ref(v_keys_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1135_, size_t v_x_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_object* v_es_1138_; lean_object* v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; lean_object* v_j_1142_; lean_object* v___x_1143_; 
v_es_1138_ = lean_ctor_get(v_x_1135_, 0);
v___x_1139_ = lean_box(2);
v___x_1140_ = ((size_t)31ULL);
v___x_1141_ = lean_usize_land(v_x_1136_, v___x_1140_);
v_j_1142_ = lean_usize_to_nat(v___x_1141_);
v___x_1143_ = lean_array_get_borrowed(v___x_1139_, v_es_1138_, v_j_1142_);
lean_dec(v_j_1142_);
switch(lean_obj_tag(v___x_1143_))
{
case 0:
{
lean_object* v_key_1144_; lean_object* v_val_1145_; uint8_t v___x_1146_; 
v_key_1144_ = lean_ctor_get(v___x_1143_, 0);
v_val_1145_ = lean_ctor_get(v___x_1143_, 1);
v___x_1146_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1137_, v_key_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_box(0);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
lean_inc(v_val_1145_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_val_1145_);
return v___x_1148_;
}
}
case 1:
{
lean_object* v_node_1149_; size_t v___x_1150_; size_t v___x_1151_; 
v_node_1149_ = lean_ctor_get(v___x_1143_, 0);
v___x_1150_ = ((size_t)5ULL);
v___x_1151_ = lean_usize_shift_right(v_x_1136_, v___x_1150_);
v_x_1135_ = v_node_1149_;
v_x_1136_ = v___x_1151_;
goto _start;
}
default: 
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
}
else
{
lean_object* v_ks_1154_; lean_object* v_vs_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_ks_1154_ = lean_ctor_get(v_x_1135_, 0);
v_vs_1155_ = lean_ctor_get(v_x_1135_, 1);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1154_, v_vs_1155_, v___x_1156_, v_x_1137_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
size_t v_x_11691__boxed_1161_; lean_object* v_res_1162_; 
v_x_11691__boxed_1161_ = lean_unbox_usize(v_x_1159_);
lean_dec(v_x_1159_);
v_res_1162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1158_, v_x_11691__boxed_1161_, v_x_1160_);
lean_dec_ref(v_x_1160_);
lean_dec_ref(v_x_1158_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
uint64_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1164_);
v___x_1166_ = lean_uint64_to_usize(v___x_1165_);
v___x_1167_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1163_, v___x_1166_, v_x_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1168_, v_x_1169_);
lean_dec_ref(v_x_1169_);
lean_dec_ref(v_x_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_ks_1175_; lean_object* v_vs_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_ks_1175_ = lean_ctor_get(v_x_1171_, 0);
v_vs_1176_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v_x_1171_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_vs_1176_);
lean_inc(v_ks_1175_);
lean_dec(v_x_1171_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_ks_1175_);
v___x_1181_ = lean_nat_dec_lt(v_x_1172_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_x_1172_);
v___x_1182_ = lean_array_push(v_ks_1175_, v_x_1173_);
v___x_1183_ = lean_array_push(v_vs_1176_, v_x_1174_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1183_);
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v_k_x27_1187_; uint8_t v___x_1188_; 
v_k_x27_1187_ = lean_array_fget_borrowed(v_ks_1175_, v_x_1172_);
v___x_1188_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1173_, v_k_x27_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
if (v_isShared_1179_ == 0)
{
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ks_1175_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_vs_1176_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_x_1172_, v___x_1191_);
lean_dec(v_x_1172_);
v_x_1171_ = v___x_1190_;
v_x_1172_ = v___x_1192_;
goto _start;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_array_fset(v_ks_1175_, v_x_1172_, v_x_1173_);
v___x_1196_ = lean_array_fset(v_vs_1176_, v_x_1172_, v_x_1174_);
lean_dec(v_x_1172_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1196_);
lean_ctor_set(v___x_1178_, 0, v___x_1195_);
v___x_1198_ = v___x_1178_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1201_, lean_object* v_k_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_1201_, v___x_1204_, v_k_1202_, v_v_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1207_, size_t v_x_1208_, size_t v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_es_1212_ = lean_ctor_get(v_x_1207_, 0);
v___x_1213_ = ((size_t)31ULL);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_size(v_es_1212_);
v___x_1217_ = lean_nat_dec_lt(v_j_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_j_1215_);
lean_dec(v_x_1211_);
lean_dec_ref(v_x_1210_);
return v_x_1207_;
}
else
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1256_; 
lean_inc_ref(v_es_1212_);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_x_1207_, 0);
lean_dec(v_unused_1257_);
v___x_1219_ = v_x_1207_;
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_x_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_v_1221_; lean_object* v___x_1222_; lean_object* v_xs_x27_1223_; lean_object* v___y_1225_; 
v_v_1221_ = lean_array_fget(v_es_1212_, v_j_1215_);
v___x_1222_ = lean_box(0);
v_xs_x27_1223_ = lean_array_fset(v_es_1212_, v_j_1215_, v___x_1222_);
switch(lean_obj_tag(v_v_1221_))
{
case 0:
{
lean_object* v_key_1230_; lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
v_key_1230_ = lean_ctor_get(v_v_1221_, 0);
v_val_1231_ = lean_ctor_get(v_v_1221_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v_v_1221_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_inc(v_key_1230_);
lean_dec(v_v_1221_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1210_, v_key_1230_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_del_object(v___x_1233_);
v___x_1236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1230_, v_val_1231_, v_x_1210_, v_x_1211_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
v___y_1225_ = v___x_1237_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_val_1231_);
lean_dec(v_key_1230_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_x_1211_);
lean_ctor_set(v___x_1233_, 0, v_x_1210_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_x_1210_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_x_1211_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v___y_1225_ = v___x_1239_;
goto v___jp_1224_;
}
}
}
}
case 1:
{
lean_object* v_node_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
v_node_1242_ = lean_ctor_get(v_v_1221_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1244_ = v_v_1221_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_node_1242_);
lean_dec(v_v_1221_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_shift_right(v_x_1208_, v___x_1246_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_x_1209_, v___x_1248_);
v___x_1250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1242_, v___x_1247_, v___x_1249_, v_x_1210_, v_x_1211_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1250_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1225_ = v___x_1252_;
goto v___jp_1224_;
}
}
}
default: 
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_x_1210_);
lean_ctor_set(v___x_1255_, 1, v_x_1211_);
v___y_1225_ = v___x_1255_;
goto v___jp_1224_;
}
}
v___jp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_array_fset(v_xs_x27_1223_, v_j_1215_, v___y_1225_);
lean_dec(v_j_1215_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1226_);
v___x_1228_ = v___x_1219_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_ks_1258_; lean_object* v_vs_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1277_; 
v_ks_1258_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1259_ = lean_ctor_get(v_x_1207_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1261_ = v_x_1207_;
v_isShared_1262_ = v_isSharedCheck_1277_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_vs_1259_);
lean_inc(v_ks_1258_);
lean_dec(v_x_1207_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1277_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_ks_1258_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_vs_1259_);
v___x_1264_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v_newNode_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v_newNode_1265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1264_, v_x_1210_, v_x_1211_);
v___x_1266_ = ((size_t)7ULL);
v___x_1267_ = lean_usize_dec_le(v___x_1266_, v_x_1209_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1265_);
v___x_1269_ = lean_unsigned_to_nat(4u);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
if (v___x_1270_ == 0)
{
lean_object* v_ks_1271_; lean_object* v_vs_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_ks_1271_ = lean_ctor_get(v_newNode_1265_, 0);
lean_inc_ref(v_ks_1271_);
v_vs_1272_ = lean_ctor_get(v_newNode_1265_, 1);
lean_inc_ref(v_vs_1272_);
lean_dec_ref(v_newNode_1265_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1209_, v_ks_1271_, v_vs_1272_, v___x_1273_, v___x_1274_);
lean_dec_ref(v_vs_1272_);
lean_dec_ref(v_ks_1271_);
return v___x_1275_;
}
else
{
return v_newNode_1265_;
}
}
else
{
return v_newNode_1265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_i_1281_, lean_object* v_entries_1282_){
_start:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_array_get_size(v_keys_1279_);
v___x_1284_ = lean_nat_dec_lt(v_i_1281_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec(v_i_1281_);
return v_entries_1282_;
}
else
{
lean_object* v_k_1285_; lean_object* v_v_1286_; uint64_t v___x_1287_; size_t v_h_1288_; size_t v___x_1289_; lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v_h_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_k_1285_ = lean_array_fget_borrowed(v_keys_1279_, v_i_1281_);
v_v_1286_ = lean_array_fget_borrowed(v_vals_1280_, v_i_1281_);
v___x_1287_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1285_);
v_h_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = ((size_t)5ULL);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_sub(v_depth_1278_, v___x_1291_);
v___x_1293_ = lean_usize_mul(v___x_1289_, v___x_1292_);
v_h_1294_ = lean_usize_shift_right(v_h_1288_, v___x_1293_);
v___x_1295_ = lean_nat_add(v_i_1281_, v___x_1290_);
lean_dec(v_i_1281_);
lean_inc(v_v_1286_);
lean_inc(v_k_1285_);
v___x_1296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1282_, v_h_1294_, v_depth_1278_, v_k_1285_, v_v_1286_);
v_i_1281_ = v___x_1295_;
v_entries_1282_ = v___x_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1298_, lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_entries_1302_){
_start:
{
size_t v_depth_boxed_1303_; lean_object* v_res_1304_; 
v_depth_boxed_1303_ = lean_unbox_usize(v_depth_1298_);
lean_dec(v_depth_1298_);
v_res_1304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1303_, v_keys_1299_, v_vals_1300_, v_i_1301_, v_entries_1302_);
lean_dec_ref(v_vals_1300_);
lean_dec_ref(v_keys_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
size_t v_x_11826__boxed_1310_; size_t v_x_11827__boxed_1311_; lean_object* v_res_1312_; 
v_x_11826__boxed_1310_ = lean_unbox_usize(v_x_1306_);
lean_dec(v_x_1306_);
v_x_11827__boxed_1311_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_res_1312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1305_, v_x_11826__boxed_1310_, v_x_11827__boxed_1311_, v_x_1308_, v_x_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1314_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1313_, v___x_1317_, v___x_1318_, v_x_1314_, v_x_1315_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1320_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1323_, lean_object* v_env_1324_, lean_object* v_forConst_1325_, lean_object* v_ctx_1326_, lean_object* v_importRealizationCtx_x3f_1327_, lean_object* v_realize_1328_, lean_object* v_opts_1329_, lean_object* v_key_1330_, lean_object* v_inst_1331_, lean_object* v_____r_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___y_1370_; lean_object* v___x_1375_; 
v___x_1334_ = lean_io_promise_new();
v___x_1335_ = lean_st_ref_take(v_realizeMapRef_1323_);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1335_, v_inst_1331_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1370_ = v___x_1376_;
goto v___jp_1369_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1375_, 1);
v___y_1370_ = v_val_1377_;
goto v___jp_1369_;
}
v___jp_1336_:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_st_ref_put(v_realizeMapRef_1323_, v_snd_1338_);
if (lean_obj_tag(v_fst_1337_) == 1)
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v___x_1334_);
lean_dec_ref(v_opts_1329_);
lean_dec_ref(v_realize_1328_);
lean_dec(v_importRealizationCtx_x3f_1327_);
lean_dec_ref(v_ctx_1326_);
lean_dec(v_forConst_1325_);
lean_dec(v_env_1324_);
v_val_1340_ = lean_ctor_get(v_fst_1337_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_fst_1337_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1342_ = v_fst_1337_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v_fst_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_task_get_own(v_val_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_base_1349_; lean_object* v_serverBaseExts_1350_; lean_object* v_checked_1351_; lean_object* v_asyncConstsMap_1352_; lean_object* v_asyncCtx_x3f_1353_; lean_object* v_localRealizationCtxMap_1354_; lean_object* v_allRealizations_1355_; uint8_t v_isExporting_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_fst_1337_);
v_base_1349_ = lean_ctor_get(v_env_1324_, 0);
v_serverBaseExts_1350_ = lean_ctor_get(v_env_1324_, 1);
v_checked_1351_ = lean_ctor_get(v_env_1324_, 2);
v_asyncConstsMap_1352_ = lean_ctor_get(v_env_1324_, 3);
v_asyncCtx_x3f_1353_ = lean_ctor_get(v_env_1324_, 4);
v_localRealizationCtxMap_1354_ = lean_ctor_get(v_env_1324_, 6);
v_allRealizations_1355_ = lean_ctor_get(v_env_1324_, 7);
v_isExporting_1356_ = lean_ctor_get_uint8(v_env_1324_, sizeof(void*)*8);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_env_1324_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v_env_1324_, 5);
lean_dec(v_unused_1368_);
v___x_1358_ = v_env_1324_;
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_allRealizations_1355_);
lean_inc(v_localRealizationCtxMap_1354_);
lean_inc(v_asyncCtx_x3f_1353_);
lean_inc(v_asyncConstsMap_1352_);
lean_inc(v_checked_1351_);
lean_inc(v_serverBaseExts_1350_);
lean_inc(v_base_1349_);
lean_dec(v_env_1324_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1325_, v_ctx_1326_, v_localRealizationCtxMap_1354_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 6, v___x_1360_);
lean_ctor_set(v___x_1358_, 5, v_importRealizationCtx_x3f_1327_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_base_1349_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_serverBaseExts_1350_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_checked_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_asyncConstsMap_1352_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_asyncCtx_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1366_, 5, v_importRealizationCtx_x3f_1327_);
lean_ctor_set(v_reuseFailAlloc_1366_, 6, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 7, v_allRealizations_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*8, v_isExporting_1356_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_apply_3(v_realize_1328_, v___x_1362_, v_opts_1329_, lean_box(0));
lean_inc(v___x_1363_);
v___x_1364_ = lean_io_promise_resolve(v___x_1363_, v___x_1334_);
lean_dec(v___x_1334_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
return v___x_1365_;
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1370_, v_key_1330_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = l_IO_Promise_result_x21___redArg(v___x_1334_);
v___x_1373_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1370_, v_key_1330_, v___x_1372_);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1331_, v___x_1373_, v___x_1335_);
v_fst_1337_ = v___x_1371_;
v_snd_1338_ = v___x_1374_;
goto v___jp_1336_;
}
else
{
lean_dec_ref(v___y_1370_);
lean_dec(v_inst_1331_);
lean_dec_ref(v_key_1330_);
v_fst_1337_ = v___x_1371_;
v_snd_1338_ = v___x_1335_;
goto v___jp_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1378_, lean_object* v_env_1379_, lean_object* v_forConst_1380_, lean_object* v_ctx_1381_, lean_object* v_importRealizationCtx_x3f_1382_, lean_object* v_realize_1383_, lean_object* v_opts_1384_, lean_object* v_key_1385_, lean_object* v_inst_1386_, lean_object* v_____r_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1378_, v_env_1379_, v_forConst_1380_, v_ctx_1381_, v_importRealizationCtx_x3f_1382_, v_realize_1383_, v_opts_1384_, v_key_1385_, v_inst_1386_, v_____r_1387_);
lean_dec(v_realizeMapRef_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = 0;
return v___x_1392_;
}
else
{
lean_object* v_key_1393_; lean_object* v_tail_1394_; uint8_t v___x_1395_; 
v_key_1393_ = lean_ctor_get(v_x_1391_, 0);
v_tail_1394_ = lean_ctor_get(v_x_1391_, 2);
v___x_1395_ = lean_name_eq(v_key_1393_, v_a_1390_);
if (v___x_1395_ == 0)
{
v_x_1391_ = v_tail_1394_;
goto _start;
}
else
{
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1397_, lean_object* v_x_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1397_, v_x_1398_);
lean_dec(v_x_1398_);
lean_dec(v_a_1397_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_buckets_1403_; lean_object* v___x_1404_; uint64_t v___y_1406_; 
v_buckets_1403_ = lean_ctor_get(v_m_1401_, 1);
v___x_1404_ = lean_array_get_size(v_buckets_1403_);
if (lean_obj_tag(v_a_1402_) == 0)
{
uint64_t v___x_1420_; 
v___x_1420_ = 1723ULL;
v___y_1406_ = v___x_1420_;
goto v___jp_1405_;
}
else
{
uint64_t v_hash_1421_; 
v_hash_1421_ = lean_ctor_get_uint64(v_a_1402_, sizeof(void*)*2);
v___y_1406_ = v_hash_1421_;
goto v___jp_1405_;
}
v___jp_1405_:
{
uint64_t v___x_1407_; uint64_t v___x_1408_; uint64_t v_fold_1409_; uint64_t v___x_1410_; uint64_t v___x_1411_; uint64_t v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1407_ = 32ULL;
v___x_1408_ = lean_uint64_shift_right(v___y_1406_, v___x_1407_);
v_fold_1409_ = lean_uint64_xor(v___y_1406_, v___x_1408_);
v___x_1410_ = 16ULL;
v___x_1411_ = lean_uint64_shift_right(v_fold_1409_, v___x_1410_);
v___x_1412_ = lean_uint64_xor(v_fold_1409_, v___x_1411_);
v___x_1413_ = lean_uint64_to_usize(v___x_1412_);
v___x_1414_ = lean_usize_of_nat(v___x_1404_);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_sub(v___x_1414_, v___x_1415_);
v___x_1417_ = lean_usize_land(v___x_1413_, v___x_1416_);
v___x_1418_ = lean_array_uget_borrowed(v_buckets_1403_, v___x_1417_);
v___x_1419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1402_, v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1422_, lean_object* v_a_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_m_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1432_, lean_object* v_env_1433_, lean_object* v_forConst_1434_, lean_object* v_key_1435_, lean_object* v_realize_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v_a_1440_; lean_object* v___y_1444_; lean_object* v_base_1446_; lean_object* v_importRealizationCtx_x3f_1447_; lean_object* v_localRealizationCtxMap_1448_; uint8_t v_isExporting_1449_; lean_object* v_ctx_1451_; lean_object* v___y_1466_; 
v___x_1438_ = lean_io_get_num_heartbeats();
v_base_1446_ = lean_ctor_get(v_env_1433_, 0);
lean_inc_ref(v_base_1446_);
v_importRealizationCtx_x3f_1447_ = lean_ctor_get(v_env_1433_, 5);
lean_inc(v_importRealizationCtx_x3f_1447_);
v_localRealizationCtxMap_1448_ = lean_ctor_get(v_env_1433_, 6);
lean_inc(v_localRealizationCtxMap_1448_);
v_isExporting_1449_ = lean_ctor_get_uint8(v_env_1433_, sizeof(void*)*8);
lean_dec_ref(v_env_1433_);
if (v_isExporting_1449_ == 0)
{
lean_object* v_private_1486_; 
v_private_1486_ = lean_ctor_get(v_base_1446_, 0);
lean_inc(v_private_1486_);
lean_dec_ref(v_base_1446_);
v___y_1466_ = v_private_1486_;
goto v___jp_1465_;
}
else
{
lean_object* v_public_1487_; 
v_public_1487_ = lean_ctor_get(v_base_1446_, 1);
lean_inc(v_public_1487_);
lean_dec_ref(v_base_1446_);
v___y_1466_ = v_public_1487_;
goto v___jp_1465_;
}
v___jp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_io_set_heartbeats(v___x_1438_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1440_);
return v___x_1442_;
}
v___jp_1443_:
{
lean_object* v_a_1445_; 
v_a_1445_ = lean_ctor_get(v___y_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___y_1444_);
v_a_1440_ = v_a_1445_;
goto v___jp_1439_;
}
v___jp_1450_:
{
lean_object* v_env_1452_; lean_object* v_opts_1453_; lean_object* v_realizeMapRef_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_env_1452_ = lean_ctor_get(v_ctx_1451_, 0);
lean_inc(v_env_1452_);
v_opts_1453_ = lean_ctor_get(v_ctx_1451_, 1);
lean_inc_ref(v_opts_1453_);
v_realizeMapRef_1454_ = lean_ctor_get(v_ctx_1451_, 2);
lean_inc(v_realizeMapRef_1454_);
v___x_1455_ = lean_st_ref_get(v_realizeMapRef_1454_);
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1455_, v_inst_1432_);
lean_dec(v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 1)
{
lean_object* v_val_1457_; lean_object* v___x_1458_; 
v_val_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1457_, v_key_1435_);
lean_dec(v_val_1457_);
if (lean_obj_tag(v___x_1458_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1460_; 
lean_dec(v_realizeMapRef_1454_);
lean_dec_ref(v_opts_1453_);
lean_dec(v_env_1452_);
lean_dec_ref(v_ctx_1451_);
lean_dec(v_importRealizationCtx_x3f_1447_);
lean_dec_ref(v_realize_1436_);
lean_dec_ref(v_key_1435_);
lean_dec(v_forConst_1434_);
lean_dec(v_inst_1432_);
v_val_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = lean_task_get_own(v_val_1459_);
v_a_1440_ = v___x_1460_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v___x_1462_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1454_, v_env_1452_, v_forConst_1434_, v_ctx_1451_, v_importRealizationCtx_x3f_1447_, v_realize_1436_, v_opts_1453_, v_key_1435_, v_inst_1432_, v___x_1461_);
lean_dec(v_realizeMapRef_1454_);
v___y_1444_ = v___x_1462_;
goto v___jp_1443_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v___x_1456_);
v___x_1463_ = lean_box(0);
v___x_1464_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1454_, v_env_1452_, v_forConst_1434_, v_ctx_1451_, v_importRealizationCtx_x3f_1447_, v_realize_1436_, v_opts_1453_, v_key_1435_, v_inst_1432_, v___x_1463_);
lean_dec(v_realizeMapRef_1454_);
v___y_1444_ = v___x_1464_;
goto v___jp_1443_;
}
}
v___jp_1465_:
{
lean_object* v_const2ModIdx_1467_; uint8_t v___x_1468_; 
v_const2ModIdx_1467_ = lean_ctor_get(v___y_1466_, 2);
lean_inc_ref(v_const2ModIdx_1467_);
lean_dec_ref(v___y_1466_);
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1467_, v_forConst_1434_);
lean_dec_ref(v_const2ModIdx_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1448_, v_forConst_1434_);
lean_dec(v_localRealizationCtxMap_1448_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_importRealizationCtx_x3f_1447_);
lean_dec(v___x_1438_);
lean_dec_ref(v_realize_1436_);
lean_dec_ref(v_key_1435_);
v___x_1470_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1471_ = 1;
v___x_1472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1432_, v___x_1471_);
v___x_1473_ = lean_string_append(v___x_1470_, v___x_1472_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1475_ = lean_string_append(v___x_1473_, v___x_1474_);
v___x_1476_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1434_, v___x_1471_);
v___x_1477_ = lean_string_append(v___x_1475_, v___x_1476_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1479_ = lean_string_append(v___x_1477_, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
else
{
lean_object* v_val_1482_; 
v_val_1482_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v___x_1469_, 1);
v_ctx_1451_ = v_val_1482_;
goto v___jp_1450_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1448_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1447_) == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v___x_1438_);
lean_dec_ref(v_realize_1436_);
lean_dec_ref(v_key_1435_);
lean_dec(v_forConst_1434_);
lean_dec(v_inst_1432_);
v___x_1483_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
else
{
lean_object* v_val_1485_; 
v_val_1485_ = lean_ctor_get(v_importRealizationCtx_x3f_1447_, 0);
lean_inc(v_val_1485_);
v_ctx_1451_ = v_val_1485_;
goto v___jp_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1488_, lean_object* v_env_1489_, lean_object* v_forConst_1490_, lean_object* v_key_1491_, lean_object* v_realize_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1488_, v_env_1489_, v_forConst_1490_, v_key_1491_, v_realize_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___f_1501_; lean_object* v___x_9958__overap_1502_; lean_object* v___x_1503_; 
v___f_1501_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9958__overap_1502_ = lean_panic_fn_borrowed(v___f_1501_, v_msg_1495_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v___x_1503_ = lean_apply_5(v___x_9958__overap_1502_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, lean_box(0));
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1511_, lean_object* v_inst_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
v___x_1518_ = lean_apply_5(v_realize_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, lean_box(0));
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v_inst_1512_);
lean_ctor_set(v___x_1523_, 1, v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_inst_1512_);
v_a_1528_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1518_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1518_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1536_, lean_object* v_inst_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1536_, v_inst_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1543_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_unsigned_to_nat(16u);
v___x_1546_ = lean_mk_array(v___x_1545_, v___x_1544_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = l_Lean_Options_empty;
v___x_1551_ = l_Lean_Core_getMaxHeartbeats(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1555_ = lean_unsigned_to_nat(36u);
v___x_1556_ = lean_unsigned_to_nat(2665u);
v___x_1557_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1558_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1559_ = l_mkPanicMessageWithDecl(v___x_1558_, v___x_1557_, v___x_1556_, v___x_1555_, v___x_1554_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1561_ = lean_unsigned_to_nat(48u);
v___x_1562_ = lean_unsigned_to_nat(2656u);
v___x_1563_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1564_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1565_ = l_mkPanicMessageWithDecl(v___x_1564_, v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_forConst_1568_, lean_object* v_key_1569_, lean_object* v_realize_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v_env_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_st_ref_get(v_a_1574_);
v_env_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc_ref(v_env_1577_);
lean_dec(v___x_1576_);
v___x_1578_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1577_, v_forConst_1568_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_env_1577_);
lean_dec_ref(v_key_1569_);
lean_dec(v_forConst_1568_);
lean_dec(v_inst_1567_);
lean_dec(v_inst_1566_);
lean_inc(v_a_1574_);
lean_inc_ref(v_a_1573_);
lean_inc(v_a_1572_);
lean_inc_ref(v_a_1571_);
v___x_1579_ = lean_apply_5(v_realize_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, lean_box(0));
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v_toCold_1581_; lean_object* v_ref_1582_; lean_object* v_fileName_1583_; lean_object* v_fileMap_1584_; lean_object* v___f_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1580_ = lean_io_get_num_heartbeats();
v_toCold_1581_ = lean_ctor_get(v_a_1573_, 0);
v_ref_1582_ = lean_ctor_get(v_a_1573_, 4);
v_fileName_1583_ = lean_ctor_get(v_toCold_1581_, 0);
v_fileMap_1584_ = lean_ctor_get(v_toCold_1581_, 1);
lean_inc(v_inst_1567_);
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1585_, 0, v_realize_1570_);
lean_closure_set(v___f_1585_, 1, v_inst_1567_);
v___x_1586_ = 0;
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
lean_inc_ref(v_fileMap_1584_);
lean_inc_ref(v_fileName_1583_);
v___x_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1591_, 0, v_fileName_1583_);
lean_ctor_set(v___x_1591_, 1, v_fileMap_1584_);
lean_ctor_set(v___x_1591_, 2, v___x_1587_);
lean_ctor_set(v___x_1591_, 3, v___x_1588_);
lean_ctor_set(v___x_1591_, 4, v___x_1590_);
v___x_1592_ = l_Lean_Options_empty;
v___x_1593_ = lean_unsigned_to_nat(1000u);
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
v___x_1597_ = l_Lean_firstFrontendMacroScope;
v___x_1598_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1598_, 0, v___x_1591_);
lean_ctor_set(v___x_1598_, 1, v___x_1592_);
lean_ctor_set(v___x_1598_, 2, v___x_1589_);
lean_ctor_set(v___x_1598_, 3, v___x_1593_);
lean_ctor_set(v___x_1598_, 4, v___x_1594_);
lean_ctor_set(v___x_1598_, 5, v___x_1587_);
lean_ctor_set(v___x_1598_, 6, v___x_1595_);
lean_ctor_set(v___x_1598_, 7, v___x_1580_);
lean_ctor_set(v___x_1598_, 8, v___x_1596_);
lean_ctor_set(v___x_1598_, 9, v___x_1597_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*10, v___x_1586_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*10 + 1, v___x_1586_);
v___x_1599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1599_, 0, v___f_1585_);
lean_closure_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1566_, v_env_1577_, v_forConst_1568_, v_key_1569_, v___x_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1653_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1653_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1653_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1606_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1601_, v___x_1605_);
lean_dec(v_a_1601_);
if (lean_obj_tag(v___x_1606_) == 1)
{
lean_object* v_val_1607_; lean_object* v_res_x3f_1608_; lean_object* v_snap_x3f_1609_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v_snap_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; 
v_val_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v_res_x3f_1608_ = lean_ctor_get(v_val_1607_, 0);
lean_inc_ref(v_res_x3f_1608_);
v_snap_x3f_1609_ = lean_ctor_get(v_val_1607_, 1);
lean_inc(v_snap_x3f_1609_);
lean_dec(v_val_1607_);
if (lean_obj_tag(v_snap_x3f_1609_) == 1)
{
lean_object* v_val_1643_; lean_object* v___x_1644_; 
v_val_1643_ = lean_ctor_get(v_snap_x3f_1609_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_snap_x3f_1609_, 1);
v___x_1644_ = l_Lean_Syntax_getRange_x3f(v_ref_1582_, v___x_1586_);
if (lean_obj_tag(v___x_1644_) == 1)
{
lean_object* v_val_1645_; lean_object* v_start_1646_; lean_object* v_stop_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_val_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v_start_1646_ = lean_ctor_get(v_val_1645_, 0);
lean_inc(v_start_1646_);
v_stop_1647_ = lean_ctor_get(v_val_1645_, 1);
lean_inc(v_stop_1647_);
lean_dec(v_val_1645_);
lean_inc_ref_n(v_fileMap_1584_, 2);
v___x_1648_ = l_Lean_FileMap_toPosition(v_fileMap_1584_, v_start_1646_);
lean_dec(v_start_1646_);
v___x_1649_ = l_Lean_FileMap_toPosition(v_fileMap_1584_, v_stop_1647_);
lean_dec(v_stop_1647_);
v___x_1650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1643_, v___x_1648_, v___x_1649_);
v_snap_1628_ = v___x_1650_;
v___y_1629_ = v_a_1571_;
v___y_1630_ = v_a_1572_;
v___y_1631_ = v_a_1573_;
v___y_1632_ = v_a_1574_;
goto v___jp_1627_;
}
else
{
lean_dec(v___x_1644_);
v_snap_1628_ = v_val_1643_;
v___y_1629_ = v_a_1571_;
v___y_1630_ = v_a_1572_;
v___y_1631_ = v_a_1573_;
v___y_1632_ = v_a_1574_;
goto v___jp_1627_;
}
}
else
{
lean_dec(v_snap_x3f_1609_);
v___y_1611_ = v_a_1571_;
v___y_1612_ = v_a_1572_;
v___y_1613_ = v_a_1573_;
v___y_1614_ = v_a_1574_;
goto v___jp_1610_;
}
v___jp_1610_:
{
if (lean_obj_tag(v_res_x3f_1608_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; 
lean_dec(v_inst_1567_);
v_a_1615_ = lean_ctor_get(v_res_x3f_1608_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v_res_x3f_1608_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 1);
lean_ctor_set(v___x_1603_, 0, v_a_1615_);
v___x_1617_ = v___x_1603_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v_res_x3f_1608_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v_res_x3f_1608_, 1);
v___x_1620_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1619_, v_inst_1567_);
lean_dec(v_inst_1567_);
lean_dec(v_a_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_del_object(v___x_1603_);
v___x_1621_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1622_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1621_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1625_; 
v_val_1623_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v___x_1620_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_val_1623_);
v___x_1625_ = v___x_1603_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_val_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
v___jp_1627_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1588_, v_snap_1628_);
v___x_1634_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1633_, v___y_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
v___y_1611_ = v___y_1629_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1631_;
v___y_1614_ = v___y_1632_;
goto v___jp_1610_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_res_x3f_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_inst_1567_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v___x_1606_);
lean_del_object(v___x_1603_);
lean_dec(v_inst_1567_);
v___x_1651_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1652_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1651_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_inst_1567_);
v_a_1654_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1656_ = v___x_1600_;
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1600_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1658_ = lean_io_error_to_string(v_a_1654_);
v___x_1659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
v___x_1660_ = l_Lean_MessageData_ofFormat(v___x_1659_);
lean_inc(v_ref_1582_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_ref_1582_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1661_);
v___x_1663_ = v___x_1656_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_forConst_1668_, lean_object* v_key_1669_, lean_object* v_realize_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1666_, v_inst_1667_, v_forConst_1668_, v_key_1669_, v_realize_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1677_, lean_object* v_vals_1678_, lean_object* v_i_1679_, lean_object* v_k_1680_){
_start:
{
lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = lean_array_get_size(v_keys_1677_);
v___x_1682_ = lean_nat_dec_lt(v_i_1679_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec(v_i_1679_);
v___x_1683_ = lean_box(0);
return v___x_1683_;
}
else
{
lean_object* v_k_x27_1684_; uint8_t v___x_1685_; 
v_k_x27_1684_ = lean_array_fget_borrowed(v_keys_1677_, v_i_1679_);
v___x_1685_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1680_, v_k_x27_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v_i_1679_, v___x_1686_);
lean_dec(v_i_1679_);
v_i_1679_ = v___x_1687_;
goto _start;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_array_fget_borrowed(v_vals_1678_, v_i_1679_);
lean_dec(v_i_1679_);
lean_inc(v___x_1689_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1691_, lean_object* v_vals_1692_, lean_object* v_i_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1691_, v_vals_1692_, v_i_1693_, v_k_1694_);
lean_dec_ref(v_k_1694_);
lean_dec_ref(v_vals_1692_);
lean_dec_ref(v_keys_1691_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1696_, size_t v_x_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_es_1699_; lean_object* v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v_j_1703_; lean_object* v___x_1704_; 
v_es_1699_ = lean_ctor_get(v_x_1696_, 0);
v___x_1700_ = lean_box(2);
v___x_1701_ = ((size_t)31ULL);
v___x_1702_ = lean_usize_land(v_x_1697_, v___x_1701_);
v_j_1703_ = lean_usize_to_nat(v___x_1702_);
v___x_1704_ = lean_array_get_borrowed(v___x_1700_, v_es_1699_, v_j_1703_);
lean_dec(v_j_1703_);
switch(lean_obj_tag(v___x_1704_))
{
case 0:
{
lean_object* v_key_1705_; lean_object* v_val_1706_; uint8_t v___x_1707_; 
v_key_1705_ = lean_ctor_get(v___x_1704_, 0);
v_val_1706_ = lean_ctor_get(v___x_1704_, 1);
v___x_1707_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1698_, v_key_1705_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; 
lean_inc(v_val_1706_);
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_val_1706_);
return v___x_1709_;
}
}
case 1:
{
lean_object* v_node_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v_node_1710_ = lean_ctor_get(v___x_1704_, 0);
v___x_1711_ = ((size_t)5ULL);
v___x_1712_ = lean_usize_shift_right(v_x_1697_, v___x_1711_);
v_x_1696_ = v_node_1710_;
v_x_1697_ = v___x_1712_;
goto _start;
}
default: 
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_box(0);
return v___x_1714_;
}
}
}
else
{
lean_object* v_ks_1715_; lean_object* v_vs_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_ks_1715_ = lean_ctor_get(v_x_1696_, 0);
v_vs_1716_ = lean_ctor_get(v_x_1696_, 1);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1715_, v_vs_1716_, v___x_1717_, v_x_1698_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
size_t v_x_12567__boxed_1722_; lean_object* v_res_1723_; 
v_x_12567__boxed_1722_ = lean_unbox_usize(v_x_1720_);
lean_dec(v_x_1720_);
v_res_1723_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1719_, v_x_12567__boxed_1722_, v_x_1721_);
lean_dec_ref(v_x_1721_);
lean_dec_ref(v_x_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
uint64_t v_configKey_1726_; lean_object* v_expr_1727_; lean_object* v_nargs_x3f_1728_; uint64_t v___x_1729_; uint64_t v___y_1731_; 
v_configKey_1726_ = lean_ctor_get_uint64(v_x_1725_, sizeof(void*)*2);
v_expr_1727_ = lean_ctor_get(v_x_1725_, 0);
v_nargs_x3f_1728_ = lean_ctor_get(v_x_1725_, 1);
v___x_1729_ = l_Lean_Expr_hash(v_expr_1727_);
if (lean_obj_tag(v_nargs_x3f_1728_) == 0)
{
uint64_t v___x_1736_; 
v___x_1736_ = 11ULL;
v___y_1731_ = v___x_1736_;
goto v___jp_1730_;
}
else
{
lean_object* v_val_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; uint64_t v___x_1740_; 
v_val_1737_ = lean_ctor_get(v_nargs_x3f_1728_, 0);
v___x_1738_ = lean_uint64_of_nat(v_val_1737_);
v___x_1739_ = 13ULL;
v___x_1740_ = lean_uint64_mix_hash(v___x_1738_, v___x_1739_);
v___y_1731_ = v___x_1740_;
goto v___jp_1730_;
}
v___jp_1730_:
{
uint64_t v___x_1732_; uint64_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_uint64_mix_hash(v___x_1729_, v___y_1731_);
v___x_1733_ = lean_uint64_mix_hash(v_configKey_1726_, v___x_1732_);
v___x_1734_ = lean_uint64_to_usize(v___x_1733_);
v___x_1735_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1724_, v___x_1734_, v_x_1725_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1741_, v_x_1742_);
lean_dec_ref(v_x_1742_);
lean_dec_ref(v_x_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_ks_1748_; lean_object* v_vs_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1773_; 
v_ks_1748_ = lean_ctor_get(v_x_1744_, 0);
v_vs_1749_ = lean_ctor_get(v_x_1744_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1744_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1751_ = v_x_1744_;
v_isShared_1752_ = v_isSharedCheck_1773_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_vs_1749_);
lean_inc(v_ks_1748_);
lean_dec(v_x_1744_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1773_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_ks_1748_);
v___x_1754_ = lean_nat_dec_lt(v_x_1745_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v_x_1745_);
v___x_1755_ = lean_array_push(v_ks_1748_, v_x_1746_);
v___x_1756_ = lean_array_push(v_vs_1749_, v_x_1747_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1756_);
lean_ctor_set(v___x_1751_, 0, v___x_1755_);
v___x_1758_ = v___x_1751_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
else
{
lean_object* v_k_x27_1760_; uint8_t v___x_1761_; 
v_k_x27_1760_ = lean_array_fget_borrowed(v_ks_1748_, v_x_1745_);
v___x_1761_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1746_, v_k_x27_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1763_; 
if (v_isShared_1752_ == 0)
{
v___x_1763_ = v___x_1751_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_ks_1748_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_vs_1749_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_x_1745_, v___x_1764_);
lean_dec(v_x_1745_);
v_x_1744_ = v___x_1763_;
v_x_1745_ = v___x_1765_;
goto _start;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = lean_array_fset(v_ks_1748_, v_x_1745_, v_x_1746_);
v___x_1769_ = lean_array_fset(v_vs_1749_, v_x_1745_, v_x_1747_);
lean_dec(v_x_1745_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1769_);
lean_ctor_set(v___x_1751_, 0, v___x_1768_);
v___x_1771_ = v___x_1751_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1774_, lean_object* v_k_1775_, lean_object* v_v_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1774_, v___x_1777_, v_k_1775_, v_v_1776_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1780_, size_t v_x_1781_, size_t v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
if (lean_obj_tag(v_x_1780_) == 0)
{
lean_object* v_es_1785_; size_t v___x_1786_; size_t v___x_1787_; lean_object* v_j_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_es_1785_ = lean_ctor_get(v_x_1780_, 0);
v___x_1786_ = ((size_t)31ULL);
v___x_1787_ = lean_usize_land(v_x_1781_, v___x_1786_);
v_j_1788_ = lean_usize_to_nat(v___x_1787_);
v___x_1789_ = lean_array_get_size(v_es_1785_);
v___x_1790_ = lean_nat_dec_lt(v_j_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec(v_j_1788_);
lean_dec(v_x_1784_);
lean_dec_ref(v_x_1783_);
return v_x_1780_;
}
else
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1829_; 
lean_inc_ref(v_es_1785_);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_x_1780_, 0);
lean_dec(v_unused_1830_);
v___x_1792_ = v_x_1780_;
v_isShared_1793_ = v_isSharedCheck_1829_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_x_1780_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1829_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_v_1794_; lean_object* v___x_1795_; lean_object* v_xs_x27_1796_; lean_object* v___y_1798_; 
v_v_1794_ = lean_array_fget(v_es_1785_, v_j_1788_);
v___x_1795_ = lean_box(0);
v_xs_x27_1796_ = lean_array_fset(v_es_1785_, v_j_1788_, v___x_1795_);
switch(lean_obj_tag(v_v_1794_))
{
case 0:
{
lean_object* v_key_1803_; lean_object* v_val_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1814_; 
v_key_1803_ = lean_ctor_get(v_v_1794_, 0);
v_val_1804_ = lean_ctor_get(v_v_1794_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_v_1794_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1806_ = v_v_1794_;
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_val_1804_);
lean_inc(v_key_1803_);
lean_dec(v_v_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1783_, v_key_1803_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1806_);
v___x_1809_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1803_, v_val_1804_, v_x_1783_, v_x_1784_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
v___y_1798_ = v___x_1810_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_val_1804_);
lean_dec(v_key_1803_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v_x_1784_);
lean_ctor_set(v___x_1806_, 0, v_x_1783_);
v___x_1812_ = v___x_1806_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_x_1783_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_x_1784_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
v___y_1798_ = v___x_1812_;
goto v___jp_1797_;
}
}
}
}
case 1:
{
lean_object* v_node_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1827_; 
v_node_1815_ = lean_ctor_get(v_v_1794_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_v_1794_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1817_ = v_v_1794_;
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_node_1815_);
lean_dec(v_v_1794_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
size_t v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1819_ = ((size_t)5ULL);
v___x_1820_ = lean_usize_shift_right(v_x_1781_, v___x_1819_);
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_x_1782_, v___x_1821_);
v___x_1823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1815_, v___x_1820_, v___x_1822_, v_x_1783_, v_x_1784_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1823_);
v___x_1825_ = v___x_1817_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1798_ = v___x_1825_;
goto v___jp_1797_;
}
}
}
default: 
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_x_1783_);
lean_ctor_set(v___x_1828_, 1, v_x_1784_);
v___y_1798_ = v___x_1828_;
goto v___jp_1797_;
}
}
v___jp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = lean_array_fset(v_xs_x27_1796_, v_j_1788_, v___y_1798_);
lean_dec(v_j_1788_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1799_);
v___x_1801_ = v___x_1792_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
else
{
lean_object* v_ks_1831_; lean_object* v_vs_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1850_; 
v_ks_1831_ = lean_ctor_get(v_x_1780_, 0);
v_vs_1832_ = lean_ctor_get(v_x_1780_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1834_ = v_x_1780_;
v_isShared_1835_ = v_isSharedCheck_1850_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_vs_1832_);
lean_inc(v_ks_1831_);
lean_dec(v_x_1780_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1850_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_ks_1831_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_vs_1832_);
v___x_1837_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v_newNode_1838_; size_t v___x_1839_; uint8_t v___x_1840_; 
v_newNode_1838_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1837_, v_x_1783_, v_x_1784_);
v___x_1839_ = ((size_t)7ULL);
v___x_1840_ = lean_usize_dec_le(v___x_1839_, v_x_1782_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1841_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1838_);
v___x_1842_ = lean_unsigned_to_nat(4u);
v___x_1843_ = lean_nat_dec_lt(v___x_1841_, v___x_1842_);
lean_dec(v___x_1841_);
if (v___x_1843_ == 0)
{
lean_object* v_ks_1844_; lean_object* v_vs_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_ks_1844_ = lean_ctor_get(v_newNode_1838_, 0);
lean_inc_ref(v_ks_1844_);
v_vs_1845_ = lean_ctor_get(v_newNode_1838_, 1);
lean_inc_ref(v_vs_1845_);
lean_dec_ref(v_newNode_1838_);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1782_, v_ks_1844_, v_vs_1845_, v___x_1846_, v___x_1847_);
lean_dec_ref(v_vs_1845_);
lean_dec_ref(v_ks_1844_);
return v___x_1848_;
}
else
{
return v_newNode_1838_;
}
}
else
{
return v_newNode_1838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1851_, lean_object* v_keys_1852_, lean_object* v_vals_1853_, lean_object* v_i_1854_, lean_object* v_entries_1855_){
_start:
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = lean_array_get_size(v_keys_1852_);
v___x_1857_ = lean_nat_dec_lt(v_i_1854_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec(v_i_1854_);
return v_entries_1855_;
}
else
{
lean_object* v_k_1858_; uint64_t v_configKey_1859_; lean_object* v_expr_1860_; lean_object* v_nargs_x3f_1861_; lean_object* v_v_1862_; uint64_t v___x_1863_; uint64_t v___y_1865_; 
v_k_1858_ = lean_array_fget_borrowed(v_keys_1852_, v_i_1854_);
v_configKey_1859_ = lean_ctor_get_uint64(v_k_1858_, sizeof(void*)*2);
v_expr_1860_ = lean_ctor_get(v_k_1858_, 0);
v_nargs_x3f_1861_ = lean_ctor_get(v_k_1858_, 1);
v_v_1862_ = lean_array_fget_borrowed(v_vals_1853_, v_i_1854_);
v___x_1863_ = l_Lean_Expr_hash(v_expr_1860_);
if (lean_obj_tag(v_nargs_x3f_1861_) == 0)
{
uint64_t v___x_1878_; 
v___x_1878_ = 11ULL;
v___y_1865_ = v___x_1878_;
goto v___jp_1864_;
}
else
{
lean_object* v_val_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; 
v_val_1879_ = lean_ctor_get(v_nargs_x3f_1861_, 0);
v___x_1880_ = lean_uint64_of_nat(v_val_1879_);
v___x_1881_ = 13ULL;
v___x_1882_ = lean_uint64_mix_hash(v___x_1880_, v___x_1881_);
v___y_1865_ = v___x_1882_;
goto v___jp_1864_;
}
v___jp_1864_:
{
uint64_t v___x_1866_; uint64_t v___x_1867_; size_t v_h_1868_; size_t v___x_1869_; lean_object* v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v_h_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1866_ = lean_uint64_mix_hash(v___x_1863_, v___y_1865_);
v___x_1867_ = lean_uint64_mix_hash(v_configKey_1859_, v___x_1866_);
v_h_1868_ = lean_uint64_to_usize(v___x_1867_);
v___x_1869_ = ((size_t)5ULL);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = ((size_t)1ULL);
v___x_1872_ = lean_usize_sub(v_depth_1851_, v___x_1871_);
v___x_1873_ = lean_usize_mul(v___x_1869_, v___x_1872_);
v_h_1874_ = lean_usize_shift_right(v_h_1868_, v___x_1873_);
v___x_1875_ = lean_nat_add(v_i_1854_, v___x_1870_);
lean_dec(v_i_1854_);
lean_inc(v_v_1862_);
lean_inc(v_k_1858_);
v___x_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1855_, v_h_1874_, v_depth_1851_, v_k_1858_, v_v_1862_);
v_i_1854_ = v___x_1875_;
v_entries_1855_ = v___x_1876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1883_, lean_object* v_keys_1884_, lean_object* v_vals_1885_, lean_object* v_i_1886_, lean_object* v_entries_1887_){
_start:
{
size_t v_depth_boxed_1888_; lean_object* v_res_1889_; 
v_depth_boxed_1888_ = lean_unbox_usize(v_depth_1883_);
lean_dec(v_depth_1883_);
v_res_1889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1888_, v_keys_1884_, v_vals_1885_, v_i_1886_, v_entries_1887_);
lean_dec_ref(v_vals_1885_);
lean_dec_ref(v_keys_1884_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
size_t v_x_12738__boxed_1895_; size_t v_x_12739__boxed_1896_; lean_object* v_res_1897_; 
v_x_12738__boxed_1895_ = lean_unbox_usize(v_x_1891_);
lean_dec(v_x_1891_);
v_x_12739__boxed_1896_ = lean_unbox_usize(v_x_1892_);
lean_dec(v_x_1892_);
v_res_1897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1890_, v_x_12738__boxed_1895_, v_x_12739__boxed_1896_, v_x_1893_, v_x_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
uint64_t v_configKey_1901_; lean_object* v_expr_1902_; lean_object* v_nargs_x3f_1903_; uint64_t v___x_1904_; uint64_t v___y_1906_; 
v_configKey_1901_ = lean_ctor_get_uint64(v_x_1899_, sizeof(void*)*2);
v_expr_1902_ = lean_ctor_get(v_x_1899_, 0);
v_nargs_x3f_1903_ = lean_ctor_get(v_x_1899_, 1);
v___x_1904_ = l_Lean_Expr_hash(v_expr_1902_);
if (lean_obj_tag(v_nargs_x3f_1903_) == 0)
{
uint64_t v___x_1912_; 
v___x_1912_ = 11ULL;
v___y_1906_ = v___x_1912_;
goto v___jp_1905_;
}
else
{
lean_object* v_val_1913_; uint64_t v___x_1914_; uint64_t v___x_1915_; uint64_t v___x_1916_; 
v_val_1913_ = lean_ctor_get(v_nargs_x3f_1903_, 0);
v___x_1914_ = lean_uint64_of_nat(v_val_1913_);
v___x_1915_ = 13ULL;
v___x_1916_ = lean_uint64_mix_hash(v___x_1914_, v___x_1915_);
v___y_1906_ = v___x_1916_;
goto v___jp_1905_;
}
v___jp_1905_:
{
uint64_t v___x_1907_; uint64_t v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1907_ = lean_uint64_mix_hash(v___x_1904_, v___y_1906_);
v___x_1908_ = lean_uint64_mix_hash(v_configKey_1901_, v___x_1907_);
v___x_1909_ = lean_uint64_to_usize(v___x_1908_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1898_, v___x_1909_, v___x_1910_, v_x_1899_, v_x_1900_);
return v___x_1911_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1917_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
uint8_t v___x_1918_; 
v___x_1918_ = 0;
return v___x_1918_;
}
else
{
lean_object* v_head_1919_; lean_object* v_tail_1920_; uint8_t v___x_1921_; 
v_head_1919_ = lean_ctor_get(v_x_1917_, 0);
v_tail_1920_ = lean_ctor_get(v_x_1917_, 1);
v___x_1921_ = l_Lean_Level_hasMVar(v_head_1919_);
if (v___x_1921_ == 0)
{
v_x_1917_ = v_tail_1920_;
goto _start;
}
else
{
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1923_){
_start:
{
uint8_t v_res_1924_; lean_object* v_r_1925_; 
v_res_1924_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1923_);
lean_dec(v_x_1923_);
v_r_1925_ = lean_box(v_res_1924_);
return v_r_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1928_, lean_object* v_maxArgs_x3f_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; 
lean_inc(v_maxArgs_x3f_1929_);
lean_inc_ref(v_fn_1928_);
v___x_1935_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1928_, v_maxArgs_x3f_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_2000_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_2000_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_2000_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_finfo_1941_; lean_object* v___y_1942_; lean_object* v___x_1974_; lean_object* v_cache_1975_; lean_object* v_funInfo_1976_; lean_object* v___x_1977_; 
v___x_1974_ = lean_st_ref_get(v_a_1931_);
v_cache_1975_ = lean_ctor_get(v___x_1974_, 1);
lean_inc_ref(v_cache_1975_);
lean_dec(v___x_1974_);
v_funInfo_1976_ = lean_ctor_get(v_cache_1975_, 1);
lean_inc_ref(v_funInfo_1976_);
lean_dec_ref(v_cache_1975_);
v___x_1977_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1976_, v_a_1936_);
lean_dec_ref(v_funInfo_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___f_1978_; lean_object* v___f_1979_; 
v___f_1978_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1929_);
lean_inc_ref(v_fn_1928_);
v___f_1979_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1979_, 0, v_fn_1928_);
lean_closure_set(v___f_1979_, 1, v_maxArgs_x3f_1929_);
lean_closure_set(v___f_1979_, 2, v___f_1978_);
if (lean_obj_tag(v_fn_1928_) == 4)
{
lean_object* v_declName_1980_; lean_object* v_us_1981_; uint8_t v___x_1982_; 
v_declName_1980_ = lean_ctor_get(v_fn_1928_, 0);
v_us_1981_ = lean_ctor_get(v_fn_1928_, 1);
v___x_1982_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_inc(v_us_1981_);
lean_inc_n(v_declName_1980_, 2);
lean_dec_ref_known(v_fn_1928_, 2);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_1984_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_1985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1985_, 0, v_declName_1980_);
lean_ctor_set(v___x_1985_, 1, v_us_1981_);
lean_ctor_set(v___x_1985_, 2, v_maxArgs_x3f_1929_);
v___x_1986_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_1983_, v___x_1984_, v_declName_1980_, v___x_1985_, v___f_1979_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_finfo_1941_ = v_a_1987_;
v___y_1942_ = v_a_1931_;
goto v___jp_1940_;
}
else
{
lean_del_object(v___x_1938_);
lean_dec(v_a_1936_);
return v___x_1986_;
}
}
else
{
lean_object* v___x_1988_; 
lean_dec_ref(v___f_1979_);
lean_inc(v_a_1933_);
lean_inc_ref(v_a_1932_);
lean_inc(v_a_1931_);
lean_inc_ref(v_a_1930_);
v___x_1988_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1928_, v_maxArgs_x3f_1929_, v___f_1978_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v_finfo_1941_ = v_a_1989_;
v___y_1942_ = v_a_1931_;
goto v___jp_1940_;
}
else
{
lean_del_object(v___x_1938_);
lean_dec(v_a_1936_);
return v___x_1988_;
}
}
}
else
{
lean_object* v___x_1990_; 
lean_dec_ref(v___f_1979_);
lean_inc(v_a_1933_);
lean_inc_ref(v_a_1932_);
lean_inc(v_a_1931_);
lean_inc_ref(v_a_1930_);
v___x_1990_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1928_, v_maxArgs_x3f_1929_, v___f_1978_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_finfo_1941_ = v_a_1991_;
v___y_1942_ = v_a_1931_;
goto v___jp_1940_;
}
else
{
lean_del_object(v___x_1938_);
lean_dec(v_a_1936_);
return v___x_1990_;
}
}
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_del_object(v___x_1938_);
lean_dec(v_a_1936_);
lean_dec(v_maxArgs_x3f_1929_);
lean_dec_ref(v_fn_1928_);
v_val_1992_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1977_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v___x_1977_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 0);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_val_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
v___jp_1940_:
{
lean_object* v___x_1943_; lean_object* v_cache_1944_; lean_object* v_mctx_1945_; lean_object* v_zetaDeltaFVarIds_1946_; lean_object* v_postponed_1947_; lean_object* v_diag_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1973_; 
v___x_1943_ = lean_st_ref_take(v___y_1942_);
v_cache_1944_ = lean_ctor_get(v___x_1943_, 1);
v_mctx_1945_ = lean_ctor_get(v___x_1943_, 0);
v_zetaDeltaFVarIds_1946_ = lean_ctor_get(v___x_1943_, 2);
v_postponed_1947_ = lean_ctor_get(v___x_1943_, 3);
v_diag_1948_ = lean_ctor_get(v___x_1943_, 4);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1950_ = v___x_1943_;
v_isShared_1951_ = v_isSharedCheck_1973_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_diag_1948_);
lean_inc(v_postponed_1947_);
lean_inc(v_zetaDeltaFVarIds_1946_);
lean_inc(v_cache_1944_);
lean_inc(v_mctx_1945_);
lean_dec(v___x_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1973_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_inferType_1952_; lean_object* v_funInfo_1953_; lean_object* v_synthInstance_1954_; lean_object* v_whnf_1955_; lean_object* v_defEqTrans_1956_; lean_object* v_defEqPerm_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1972_; 
v_inferType_1952_ = lean_ctor_get(v_cache_1944_, 0);
v_funInfo_1953_ = lean_ctor_get(v_cache_1944_, 1);
v_synthInstance_1954_ = lean_ctor_get(v_cache_1944_, 2);
v_whnf_1955_ = lean_ctor_get(v_cache_1944_, 3);
v_defEqTrans_1956_ = lean_ctor_get(v_cache_1944_, 4);
v_defEqPerm_1957_ = lean_ctor_get(v_cache_1944_, 5);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_cache_1944_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1959_ = v_cache_1944_;
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_defEqPerm_1957_);
lean_inc(v_defEqTrans_1956_);
lean_inc(v_whnf_1955_);
lean_inc(v_synthInstance_1954_);
lean_inc(v_funInfo_1953_);
lean_inc(v_inferType_1952_);
lean_dec(v_cache_1944_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc_ref(v_finfo_1941_);
v___x_1961_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1953_, v_a_1936_, v_finfo_1941_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_inferType_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_synthInstance_1954_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_whnf_1955_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_defEqTrans_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_defEqPerm_1957_);
v___x_1963_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_1963_);
v___x_1965_ = v___x_1950_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_mctx_1945_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_zetaDeltaFVarIds_1946_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_postponed_1947_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_diag_1948_);
v___x_1965_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_st_ref_put(v___y_1942_, v___x_1965_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_finfo_1941_);
v___x_1968_ = v___x_1938_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_finfo_1941_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
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
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_maxArgs_x3f_1929_);
lean_dec_ref(v_fn_1928_);
v_a_2001_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1935_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1935_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_2009_, lean_object* v_maxArgs_x3f_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2009_, v_maxArgs_x3f_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_2017_, lean_object* v_k_2018_, lean_object* v_t_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_2018_, v_t_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2021_, lean_object* v_k_2022_, lean_object* v_t_2023_){
_start:
{
uint8_t v_res_2024_; lean_object* v_r_2025_; 
v_res_2024_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2021_, v_k_2022_, v_t_2023_);
lean_dec(v_t_2023_);
lean_dec(v_k_2022_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2026_, lean_object* v_val_2027_, lean_object* v___x_2028_, lean_object* v_fvars_2029_, lean_object* v_next_2030_, lean_object* v_upperBound_2031_, lean_object* v_inst_2032_, lean_object* v_R_2033_, lean_object* v_a_2034_, lean_object* v_b_2035_, lean_object* v_c_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2026_, v_val_2027_, v___x_2028_, v_fvars_2029_, v_next_2030_, v_upperBound_2031_, v_a_2034_, v_b_2035_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2043_, lean_object* v_val_2044_, lean_object* v___x_2045_, lean_object* v_fvars_2046_, lean_object* v_next_2047_, lean_object* v_upperBound_2048_, lean_object* v_inst_2049_, lean_object* v_R_2050_, lean_object* v_a_2051_, lean_object* v_b_2052_, lean_object* v_c_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2043_, v_val_2044_, v___x_2045_, v_fvars_2046_, v_next_2047_, v_upperBound_2048_, v_inst_2049_, v_R_2050_, v_a_2051_, v_b_2052_, v_c_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_upperBound_2048_);
lean_dec(v_next_2047_);
lean_dec_ref(v_fvars_2046_);
lean_dec_ref(v___x_2045_);
lean_dec_ref(v_val_2044_);
lean_dec(v_upperBound_2043_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2060_, lean_object* v_fvars_2061_, lean_object* v_inst_2062_, lean_object* v_R_2063_, lean_object* v_a_2064_, lean_object* v_b_2065_, lean_object* v_c_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2060_, v_fvars_2061_, v_a_2064_, v_b_2065_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2073_, lean_object* v_fvars_2074_, lean_object* v_inst_2075_, lean_object* v_R_2076_, lean_object* v_a_2077_, lean_object* v_b_2078_, lean_object* v_c_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2073_, v_fvars_2074_, v_inst_2075_, v_R_2076_, v_a_2077_, v_b_2078_, v_c_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v_fvars_2074_);
lean_dec(v_upperBound_2073_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2087_, v_x_2088_, v_x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2092_, v_x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2095_, v_x_2096_, v_x_2097_);
lean_dec_ref(v_x_2097_);
lean_dec_ref(v_x_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2107_, lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2107_, v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_forConst_2118_, lean_object* v_key_2119_, lean_object* v_realize_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2116_, v_inst_2117_, v_forConst_2118_, v_key_2119_, v_realize_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_forConst_2130_, lean_object* v_key_2131_, lean_object* v_realize_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2127_, v_inst_2128_, v_inst_2129_, v_forConst_2130_, v_key_2131_, v_realize_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2139_, lean_object* v_x_2140_, size_t v_x_2141_, size_t v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2140_, v_x_2141_, v_x_2142_, v_x_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
size_t v_x_13186__boxed_2152_; size_t v_x_13187__boxed_2153_; lean_object* v_res_2154_; 
v_x_13186__boxed_2152_ = lean_unbox_usize(v_x_2148_);
lean_dec(v_x_2148_);
v_x_13187__boxed_2153_ = lean_unbox_usize(v_x_2149_);
lean_dec(v_x_2149_);
v_res_2154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2146_, v_x_2147_, v_x_13186__boxed_2152_, v_x_13187__boxed_2153_, v_x_2150_, v_x_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2155_, lean_object* v_x_2156_, size_t v_x_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2156_, v_x_2157_, v_x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
size_t v_x_13203__boxed_2164_; lean_object* v_res_2165_; 
v_x_13203__boxed_2164_ = lean_unbox_usize(v_x_2162_);
lean_dec(v_x_2162_);
v_res_2165_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2160_, v_x_2161_, v_x_13203__boxed_2164_, v_x_2163_);
lean_dec_ref(v_x_2163_);
lean_dec_ref(v_x_2161_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2166_, lean_object* v_n_2167_, lean_object* v_k_2168_, lean_object* v_v_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2167_, v_k_2168_, v_v_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2171_, size_t v_depth_2172_, lean_object* v_keys_2173_, lean_object* v_vals_2174_, lean_object* v_heq_2175_, lean_object* v_i_2176_, lean_object* v_entries_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2172_, v_keys_2173_, v_vals_2174_, v_i_2176_, v_entries_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2179_, lean_object* v_depth_2180_, lean_object* v_keys_2181_, lean_object* v_vals_2182_, lean_object* v_heq_2183_, lean_object* v_i_2184_, lean_object* v_entries_2185_){
_start:
{
size_t v_depth_boxed_2186_; lean_object* v_res_2187_; 
v_depth_boxed_2186_ = lean_unbox_usize(v_depth_2180_);
lean_dec(v_depth_2180_);
v_res_2187_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2179_, v_depth_boxed_2186_, v_keys_2181_, v_vals_2182_, v_heq_2183_, v_i_2184_, v_entries_2185_);
lean_dec_ref(v_vals_2182_);
lean_dec_ref(v_keys_2181_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2188_, lean_object* v_keys_2189_, lean_object* v_vals_2190_, lean_object* v_heq_2191_, lean_object* v_i_2192_, lean_object* v_k_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2189_, v_vals_2190_, v_i_2192_, v_k_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2195_, lean_object* v_keys_2196_, lean_object* v_vals_2197_, lean_object* v_heq_2198_, lean_object* v_i_2199_, lean_object* v_k_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2195_, v_keys_2196_, v_vals_2197_, v_heq_2198_, v_i_2199_, v_k_2200_);
lean_dec_ref(v_k_2200_);
lean_dec_ref(v_vals_2197_);
lean_dec_ref(v_keys_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2203_, v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2206_, v_x_2207_, v_x_2208_);
lean_dec_ref(v_x_2208_);
lean_dec_ref(v_x_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2211_, v_x_2212_, v_x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2215_, lean_object* v_m_2216_, lean_object* v_a_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2216_, v_a_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_m_2220_, lean_object* v_a_2221_){
_start:
{
uint8_t v_res_2222_; lean_object* v_r_2223_; 
v_res_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2219_, v_m_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_m_2220_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2225_, v_x_2226_, v_x_2227_, v_x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2230_, lean_object* v_x_2231_, size_t v_x_2232_, lean_object* v_x_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2231_, v_x_2232_, v_x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
size_t v_x_13248__boxed_2239_; lean_object* v_res_2240_; 
v_x_13248__boxed_2239_ = lean_unbox_usize(v_x_2237_);
lean_dec(v_x_2237_);
v_res_2240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2235_, v_x_2236_, v_x_13248__boxed_2239_, v_x_2238_);
lean_dec_ref(v_x_2238_);
lean_dec_ref(v_x_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2241_, lean_object* v_x_2242_, size_t v_x_2243_, size_t v_x_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2242_, v_x_2243_, v_x_2244_, v_x_2245_, v_x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
size_t v_x_13259__boxed_2254_; size_t v_x_13260__boxed_2255_; lean_object* v_res_2256_; 
v_x_13259__boxed_2254_ = lean_unbox_usize(v_x_2250_);
lean_dec(v_x_2250_);
v_x_13260__boxed_2255_ = lean_unbox_usize(v_x_2251_);
lean_dec(v_x_2251_);
v_res_2256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2248_, v_x_2249_, v_x_13259__boxed_2254_, v_x_13260__boxed_2255_, v_x_2252_, v_x_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2257_, lean_object* v_a_2258_, lean_object* v_x_2259_){
_start:
{
uint8_t v___x_2260_; 
v___x_2260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2258_, v_x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2261_, lean_object* v_a_2262_, lean_object* v_x_2263_){
_start:
{
uint8_t v_res_2264_; lean_object* v_r_2265_; 
v_res_2264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2261_, v_a_2262_, v_x_2263_);
lean_dec(v_x_2263_);
lean_dec(v_a_2262_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2266_, lean_object* v_keys_2267_, lean_object* v_vals_2268_, lean_object* v_heq_2269_, lean_object* v_i_2270_, lean_object* v_k_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2267_, v_vals_2268_, v_i_2270_, v_k_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2273_, lean_object* v_keys_2274_, lean_object* v_vals_2275_, lean_object* v_heq_2276_, lean_object* v_i_2277_, lean_object* v_k_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2273_, v_keys_2274_, v_vals_2275_, v_heq_2276_, v_i_2277_, v_k_2278_);
lean_dec_ref(v_k_2278_);
lean_dec_ref(v_vals_2275_);
lean_dec_ref(v_keys_2274_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2280_, lean_object* v_n_2281_, lean_object* v_k_2282_, lean_object* v_v_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2281_, v_k_2282_, v_v_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2285_, size_t v_depth_2286_, lean_object* v_keys_2287_, lean_object* v_vals_2288_, lean_object* v_heq_2289_, lean_object* v_i_2290_, lean_object* v_entries_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2286_, v_keys_2287_, v_vals_2288_, v_i_2290_, v_entries_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2293_, lean_object* v_depth_2294_, lean_object* v_keys_2295_, lean_object* v_vals_2296_, lean_object* v_heq_2297_, lean_object* v_i_2298_, lean_object* v_entries_2299_){
_start:
{
size_t v_depth_boxed_2300_; lean_object* v_res_2301_; 
v_depth_boxed_2300_ = lean_unbox_usize(v_depth_2294_);
lean_dec(v_depth_2294_);
v_res_2301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2293_, v_depth_boxed_2300_, v_keys_2295_, v_vals_2296_, v_heq_2297_, v_i_2298_, v_entries_2299_);
lean_dec_ref(v_vals_2296_);
lean_dec_ref(v_keys_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2303_, v_x_2304_, v_x_2305_, v_x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2308_, lean_object* v_maxArgs_x3f_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2308_, v_maxArgs_x3f_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2316_, lean_object* v_maxArgs_x3f_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Meta_getFunInfo(v_fn_2316_, v_maxArgs_x3f_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2324_, lean_object* v_nargs_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_nargs_2325_);
v___x_2332_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2324_, v___x_2331_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2333_, lean_object* v_nargs_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2333_, v_nargs_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2341_){
_start:
{
lean_object* v_paramInfo_2342_; lean_object* v___x_2343_; 
v_paramInfo_2342_ = lean_ctor_get(v_info_2341_, 0);
v___x_2343_ = lean_array_get_size(v_paramInfo_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_FunInfo_getArity(v_info_2344_);
lean_dec_ref(v_info_2344_);
return v_res_2345_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
