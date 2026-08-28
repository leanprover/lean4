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
lean_object* v___f_612_; lean_object* v___x_8505__overap_613_; lean_object* v___x_614_; 
v___f_612_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_8505__overap_613_ = lean_panic_fn_borrowed(v___f_612_, v_msg_606_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
v___x_614_ = lean_apply_5(v___x_8505__overap_613_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
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
size_t v_x_11656__boxed_1144_; lean_object* v_res_1145_; 
v_x_11656__boxed_1144_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1145_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1141_, v_x_11656__boxed_1144_, v_x_1143_);
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
lean_object* v_ks_1241_; lean_object* v_vs_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1260_; 
v_ks_1241_ = lean_ctor_get(v_x_1190_, 0);
v_vs_1242_ = lean_ctor_get(v_x_1190_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1244_ = v_x_1190_;
v_isShared_1245_ = v_isSharedCheck_1260_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_vs_1242_);
lean_inc(v_ks_1241_);
lean_dec(v_x_1190_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1260_;
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
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_ks_1241_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_vs_1242_);
v___x_1247_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v_newNode_1248_; size_t v___x_1249_; uint8_t v___x_1250_; 
v_newNode_1248_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1247_, v_x_1193_, v_x_1194_);
v___x_1249_ = ((size_t)7ULL);
v___x_1250_ = lean_usize_dec_le(v___x_1249_, v_x_1192_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1248_);
v___x_1252_ = lean_unsigned_to_nat(4u);
v___x_1253_ = lean_nat_dec_lt(v___x_1251_, v___x_1252_);
lean_dec(v___x_1251_);
if (v___x_1253_ == 0)
{
lean_object* v_ks_1254_; lean_object* v_vs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_ks_1254_ = lean_ctor_get(v_newNode_1248_, 0);
lean_inc_ref(v_ks_1254_);
v_vs_1255_ = lean_ctor_get(v_newNode_1248_, 1);
lean_inc_ref(v_vs_1255_);
lean_dec_ref(v_newNode_1248_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1192_, v_ks_1254_, v_vs_1255_, v___x_1256_, v___x_1257_);
lean_dec_ref(v_vs_1255_);
lean_dec_ref(v_ks_1254_);
return v___x_1258_;
}
else
{
return v_newNode_1248_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1261_, lean_object* v_keys_1262_, lean_object* v_vals_1263_, lean_object* v_i_1264_, lean_object* v_entries_1265_){
_start:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_array_get_size(v_keys_1262_);
v___x_1267_ = lean_nat_dec_lt(v_i_1264_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec(v_i_1264_);
return v_entries_1265_;
}
else
{
lean_object* v_k_1268_; lean_object* v_v_1269_; uint64_t v___x_1270_; size_t v_h_1271_; size_t v___x_1272_; lean_object* v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v_h_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_k_1268_ = lean_array_fget_borrowed(v_keys_1262_, v_i_1264_);
v_v_1269_ = lean_array_fget_borrowed(v_vals_1263_, v_i_1264_);
v___x_1270_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1268_);
v_h_1271_ = lean_uint64_to_usize(v___x_1270_);
v___x_1272_ = ((size_t)5ULL);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_sub(v_depth_1261_, v___x_1274_);
v___x_1276_ = lean_usize_mul(v___x_1272_, v___x_1275_);
v_h_1277_ = lean_usize_shift_right(v_h_1271_, v___x_1276_);
v___x_1278_ = lean_nat_add(v_i_1264_, v___x_1273_);
lean_dec(v_i_1264_);
lean_inc(v_v_1269_);
lean_inc(v_k_1268_);
v___x_1279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1265_, v_h_1277_, v_depth_1261_, v_k_1268_, v_v_1269_);
v_i_1264_ = v___x_1278_;
v_entries_1265_ = v___x_1279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_i_1284_, lean_object* v_entries_1285_){
_start:
{
size_t v_depth_boxed_1286_; lean_object* v_res_1287_; 
v_depth_boxed_1286_ = lean_unbox_usize(v_depth_1281_);
lean_dec(v_depth_1281_);
v_res_1287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1286_, v_keys_1282_, v_vals_1283_, v_i_1284_, v_entries_1285_);
lean_dec_ref(v_vals_1283_);
lean_dec_ref(v_keys_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
size_t v_x_11791__boxed_1293_; size_t v_x_11792__boxed_1294_; lean_object* v_res_1295_; 
v_x_11791__boxed_1293_ = lean_unbox_usize(v_x_1289_);
lean_dec(v_x_1289_);
v_x_11792__boxed_1294_ = lean_unbox_usize(v_x_1290_);
lean_dec(v_x_1290_);
v_res_1295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1288_, v_x_11791__boxed_1293_, v_x_11792__boxed_1294_, v_x_1291_, v_x_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint64_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1297_);
v___x_1300_ = lean_uint64_to_usize(v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1296_, v___x_1300_, v___x_1301_, v_x_1297_, v_x_1298_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1306_, lean_object* v_env_1307_, lean_object* v_forConst_1308_, lean_object* v_ctx_1309_, lean_object* v_importRealizationCtx_x3f_1310_, lean_object* v_realize_1311_, lean_object* v_opts_1312_, lean_object* v_key_1313_, lean_object* v_inst_1314_, lean_object* v_____r_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_fst_1320_; lean_object* v_snd_1321_; lean_object* v___y_1353_; lean_object* v___x_1358_; 
v___x_1317_ = lean_io_promise_new();
v___x_1318_ = lean_st_ref_take(v_realizeMapRef_1306_);
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1318_, v_inst_1314_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1353_ = v___x_1359_;
goto v___jp_1352_;
}
else
{
lean_object* v_val_1360_; 
v_val_1360_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v___x_1358_, 1);
v___y_1353_ = v_val_1360_;
goto v___jp_1352_;
}
v___jp_1319_:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_st_ref_put(v_realizeMapRef_1306_, v_snd_1321_);
if (lean_obj_tag(v_fst_1320_) == 1)
{
lean_object* v_val_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v___x_1317_);
lean_dec_ref(v_opts_1312_);
lean_dec_ref(v_realize_1311_);
lean_dec(v_importRealizationCtx_x3f_1310_);
lean_dec_ref(v_ctx_1309_);
lean_dec(v_forConst_1308_);
lean_dec(v_env_1307_);
v_val_1323_ = lean_ctor_get(v_fst_1320_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_fst_1320_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v_fst_1320_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_val_1323_);
lean_dec(v_fst_1320_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = lean_task_get_own(v_val_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_object* v_base_1332_; lean_object* v_serverBaseExts_1333_; lean_object* v_checked_1334_; lean_object* v_asyncConstsMap_1335_; lean_object* v_asyncCtx_x3f_1336_; lean_object* v_localRealizationCtxMap_1337_; lean_object* v_allRealizations_1338_; uint8_t v_isExporting_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_fst_1320_);
v_base_1332_ = lean_ctor_get(v_env_1307_, 0);
v_serverBaseExts_1333_ = lean_ctor_get(v_env_1307_, 1);
v_checked_1334_ = lean_ctor_get(v_env_1307_, 2);
v_asyncConstsMap_1335_ = lean_ctor_get(v_env_1307_, 3);
v_asyncCtx_x3f_1336_ = lean_ctor_get(v_env_1307_, 4);
v_localRealizationCtxMap_1337_ = lean_ctor_get(v_env_1307_, 6);
v_allRealizations_1338_ = lean_ctor_get(v_env_1307_, 7);
v_isExporting_1339_ = lean_ctor_get_uint8(v_env_1307_, sizeof(void*)*8);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_env_1307_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_env_1307_, 5);
lean_dec(v_unused_1351_);
v___x_1341_ = v_env_1307_;
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_allRealizations_1338_);
lean_inc(v_localRealizationCtxMap_1337_);
lean_inc(v_asyncCtx_x3f_1336_);
lean_inc(v_asyncConstsMap_1335_);
lean_inc(v_checked_1334_);
lean_inc(v_serverBaseExts_1333_);
lean_inc(v_base_1332_);
lean_dec(v_env_1307_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1308_, v_ctx_1309_, v_localRealizationCtxMap_1337_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 6, v___x_1343_);
lean_ctor_set(v___x_1341_, 5, v_importRealizationCtx_x3f_1310_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_base_1332_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_serverBaseExts_1333_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_checked_1334_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_asyncConstsMap_1335_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_asyncCtx_x3f_1336_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_importRealizationCtx_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1349_, 6, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 7, v_allRealizations_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*8, v_isExporting_1339_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_apply_3(v_realize_1311_, v___x_1345_, v_opts_1312_, lean_box(0));
lean_inc(v___x_1346_);
v___x_1347_ = lean_io_promise_resolve(v___x_1346_, v___x_1317_);
lean_dec(v___x_1317_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
return v___x_1348_;
}
}
}
}
v___jp_1352_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1353_, v_key_1313_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = l_IO_Promise_result_x21___redArg(v___x_1317_);
v___x_1356_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1353_, v_key_1313_, v___x_1355_);
v___x_1357_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1314_, v___x_1356_, v___x_1318_);
v_fst_1320_ = v___x_1354_;
v_snd_1321_ = v___x_1357_;
goto v___jp_1319_;
}
else
{
lean_dec_ref(v___y_1353_);
lean_dec(v_inst_1314_);
lean_dec_ref(v_key_1313_);
v_fst_1320_ = v___x_1354_;
v_snd_1321_ = v___x_1318_;
goto v___jp_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1361_, lean_object* v_env_1362_, lean_object* v_forConst_1363_, lean_object* v_ctx_1364_, lean_object* v_importRealizationCtx_x3f_1365_, lean_object* v_realize_1366_, lean_object* v_opts_1367_, lean_object* v_key_1368_, lean_object* v_inst_1369_, lean_object* v_____r_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1361_, v_env_1362_, v_forConst_1363_, v_ctx_1364_, v_importRealizationCtx_x3f_1365_, v_realize_1366_, v_opts_1367_, v_key_1368_, v_inst_1369_, v_____r_1370_);
lean_dec(v_realizeMapRef_1361_);
return v_res_1372_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(lean_object* v_a_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = 0;
return v___x_1375_;
}
else
{
lean_object* v_key_1376_; lean_object* v_tail_1377_; uint8_t v___x_1378_; 
v_key_1376_ = lean_ctor_get(v_x_1374_, 0);
v_tail_1377_ = lean_ctor_get(v_x_1374_, 2);
v___x_1378_ = lean_name_eq(v_key_1376_, v_a_1373_);
if (v___x_1378_ == 0)
{
v_x_1374_ = v_tail_1377_;
goto _start;
}
else
{
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(lean_object* v_a_1380_, lean_object* v_x_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1380_, v_x_1381_);
lean_dec(v_x_1381_);
lean_dec(v_a_1380_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(lean_object* v_m_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_buckets_1386_; lean_object* v___x_1387_; uint64_t v___y_1389_; 
v_buckets_1386_ = lean_ctor_get(v_m_1384_, 1);
v___x_1387_ = lean_array_get_size(v_buckets_1386_);
if (lean_obj_tag(v_a_1385_) == 0)
{
uint64_t v___x_1403_; 
v___x_1403_ = 1723ULL;
v___y_1389_ = v___x_1403_;
goto v___jp_1388_;
}
else
{
uint64_t v_hash_1404_; 
v_hash_1404_ = lean_ctor_get_uint64(v_a_1385_, sizeof(void*)*2);
v___y_1389_ = v_hash_1404_;
goto v___jp_1388_;
}
v___jp_1388_:
{
uint64_t v___x_1390_; uint64_t v___x_1391_; uint64_t v_fold_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1390_ = 32ULL;
v___x_1391_ = lean_uint64_shift_right(v___y_1389_, v___x_1390_);
v_fold_1392_ = lean_uint64_xor(v___y_1389_, v___x_1391_);
v___x_1393_ = 16ULL;
v___x_1394_ = lean_uint64_shift_right(v_fold_1392_, v___x_1393_);
v___x_1395_ = lean_uint64_xor(v_fold_1392_, v___x_1394_);
v___x_1396_ = lean_uint64_to_usize(v___x_1395_);
v___x_1397_ = lean_usize_of_nat(v___x_1387_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_sub(v___x_1397_, v___x_1398_);
v___x_1400_ = lean_usize_land(v___x_1396_, v___x_1399_);
v___x_1401_ = lean_array_uget_borrowed(v_buckets_1386_, v___x_1400_);
v___x_1402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_1385_, v___x_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(lean_object* v_m_1405_, lean_object* v_a_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_m_1405_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1415_, lean_object* v_env_1416_, lean_object* v_forConst_1417_, lean_object* v_key_1418_, lean_object* v_realize_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v_a_1423_; lean_object* v___y_1427_; lean_object* v_base_1429_; lean_object* v_importRealizationCtx_x3f_1430_; lean_object* v_localRealizationCtxMap_1431_; uint8_t v_isExporting_1432_; lean_object* v_ctx_1434_; lean_object* v___y_1449_; 
v___x_1421_ = lean_io_get_num_heartbeats();
v_base_1429_ = lean_ctor_get(v_env_1416_, 0);
lean_inc_ref(v_base_1429_);
v_importRealizationCtx_x3f_1430_ = lean_ctor_get(v_env_1416_, 5);
lean_inc(v_importRealizationCtx_x3f_1430_);
v_localRealizationCtxMap_1431_ = lean_ctor_get(v_env_1416_, 6);
lean_inc(v_localRealizationCtxMap_1431_);
v_isExporting_1432_ = lean_ctor_get_uint8(v_env_1416_, sizeof(void*)*8);
lean_dec_ref(v_env_1416_);
if (v_isExporting_1432_ == 0)
{
lean_object* v_private_1469_; 
v_private_1469_ = lean_ctor_get(v_base_1429_, 0);
lean_inc(v_private_1469_);
lean_dec_ref(v_base_1429_);
v___y_1449_ = v_private_1469_;
goto v___jp_1448_;
}
else
{
lean_object* v_public_1470_; 
v_public_1470_ = lean_ctor_get(v_base_1429_, 1);
lean_inc(v_public_1470_);
lean_dec_ref(v_base_1429_);
v___y_1449_ = v_public_1470_;
goto v___jp_1448_;
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_io_set_heartbeats(v___x_1421_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1423_);
return v___x_1425_;
}
v___jp_1426_:
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v___y_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___y_1427_);
v_a_1423_ = v_a_1428_;
goto v___jp_1422_;
}
v___jp_1433_:
{
lean_object* v_env_1435_; lean_object* v_opts_1436_; lean_object* v_realizeMapRef_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_env_1435_ = lean_ctor_get(v_ctx_1434_, 0);
lean_inc(v_env_1435_);
v_opts_1436_ = lean_ctor_get(v_ctx_1434_, 1);
lean_inc_ref(v_opts_1436_);
v_realizeMapRef_1437_ = lean_ctor_get(v_ctx_1434_, 2);
lean_inc(v_realizeMapRef_1437_);
v___x_1438_ = lean_st_ref_get(v_realizeMapRef_1437_);
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1438_, v_inst_1415_);
lean_dec(v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 1)
{
lean_object* v_val_1440_; lean_object* v___x_1441_; 
v_val_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1440_, v_key_1418_);
lean_dec(v_val_1440_);
if (lean_obj_tag(v___x_1441_) == 1)
{
lean_object* v_val_1442_; lean_object* v___x_1443_; 
lean_dec(v_realizeMapRef_1437_);
lean_dec_ref(v_opts_1436_);
lean_dec(v_env_1435_);
lean_dec_ref(v_ctx_1434_);
lean_dec(v_importRealizationCtx_x3f_1430_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
lean_dec(v_forConst_1417_);
lean_dec(v_inst_1415_);
v_val_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = lean_task_get_own(v_val_1442_);
v_a_1423_ = v___x_1443_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1437_, v_env_1435_, v_forConst_1417_, v_ctx_1434_, v_importRealizationCtx_x3f_1430_, v_realize_1419_, v_opts_1436_, v_key_1418_, v_inst_1415_, v___x_1444_);
lean_dec(v_realizeMapRef_1437_);
v___y_1427_ = v___x_1445_;
goto v___jp_1426_;
}
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec(v___x_1439_);
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1437_, v_env_1435_, v_forConst_1417_, v_ctx_1434_, v_importRealizationCtx_x3f_1430_, v_realize_1419_, v_opts_1436_, v_key_1418_, v_inst_1415_, v___x_1446_);
lean_dec(v_realizeMapRef_1437_);
v___y_1427_ = v___x_1447_;
goto v___jp_1426_;
}
}
v___jp_1448_:
{
lean_object* v_const2ModIdx_1450_; uint8_t v___x_1451_; 
v_const2ModIdx_1450_ = lean_ctor_get(v___y_1449_, 2);
lean_inc_ref(v_const2ModIdx_1450_);
lean_dec_ref(v___y_1449_);
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_1450_, v_forConst_1417_);
lean_dec_ref(v_const2ModIdx_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1431_, v_forConst_1417_);
lean_dec(v_localRealizationCtxMap_1431_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v_importRealizationCtx_x3f_1430_);
lean_dec(v___x_1421_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
v___x_1453_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1454_ = 1;
v___x_1455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1415_, v___x_1454_);
v___x_1456_ = lean_string_append(v___x_1453_, v___x_1455_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1458_ = lean_string_append(v___x_1456_, v___x_1457_);
v___x_1459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1417_, v___x_1454_);
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
else
{
lean_object* v_val_1465_; 
v_val_1465_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v___x_1452_, 1);
v_ctx_1434_ = v_val_1465_;
goto v___jp_1433_;
}
}
else
{
lean_dec(v_localRealizationCtxMap_1431_);
if (lean_obj_tag(v_importRealizationCtx_x3f_1430_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v___x_1421_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
lean_dec(v_forConst_1417_);
lean_dec(v_inst_1415_);
v___x_1466_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v_val_1468_; 
v_val_1468_ = lean_ctor_get(v_importRealizationCtx_x3f_1430_, 0);
lean_inc(v_val_1468_);
v_ctx_1434_ = v_val_1468_;
goto v___jp_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1471_, lean_object* v_env_1472_, lean_object* v_forConst_1473_, lean_object* v_key_1474_, lean_object* v_realize_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1471_, v_env_1472_, v_forConst_1473_, v_key_1474_, v_realize_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___f_1484_; lean_object* v___x_9965__overap_1485_; lean_object* v___x_1486_; 
v___f_1484_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9965__overap_1485_ = lean_panic_fn_borrowed(v___f_1484_, v_msg_1478_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
v___x_1486_ = lean_apply_5(v___x_9965__overap_1485_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, lean_box(0));
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1494_, lean_object* v_inst_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
v___x_1501_ = lean_apply_5(v_realize_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, lean_box(0));
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1510_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_inst_1495_);
lean_ctor_set(v___x_1506_, 1, v_a_1502_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1506_);
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_inst_1495_);
v_a_1511_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1501_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1501_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1519_, lean_object* v_inst_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1519_, v_inst_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
return v_res_1526_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = l_Lean_Options_empty;
v___x_1528_ = l_Lean_Core_getMaxHeartbeats(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_unsigned_to_nat(16u);
v___x_1531_ = lean_mk_array(v___x_1530_, v___x_1529_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1532_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1538_ = lean_unsigned_to_nat(36u);
v___x_1539_ = lean_unsigned_to_nat(2664u);
v___x_1540_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1541_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1542_ = l_mkPanicMessageWithDecl(v___x_1541_, v___x_1540_, v___x_1539_, v___x_1538_, v___x_1537_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1544_ = lean_unsigned_to_nat(48u);
v___x_1545_ = lean_unsigned_to_nat(2655u);
v___x_1546_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1547_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3));
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1547_, v___x_1546_, v___x_1545_, v___x_1544_, v___x_1543_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_forConst_1551_, lean_object* v_key_1552_, lean_object* v_realize_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v_env_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_st_ref_get(v_a_1557_);
v_env_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc_ref(v_env_1560_);
lean_dec(v___x_1559_);
v___x_1561_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1560_, v_forConst_1551_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec_ref(v_env_1560_);
lean_dec_ref(v_key_1552_);
lean_dec(v_forConst_1551_);
lean_dec(v_inst_1550_);
lean_dec(v_inst_1549_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
v___x_1562_ = lean_apply_5(v_realize_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, lean_box(0));
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; lean_object* v_fileName_1564_; lean_object* v_fileMap_1565_; lean_object* v_ref_1566_; lean_object* v___f_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1563_ = lean_io_get_num_heartbeats();
v_fileName_1564_ = lean_ctor_get(v_a_1556_, 0);
v_fileMap_1565_ = lean_ctor_get(v_a_1556_, 1);
v_ref_1566_ = lean_ctor_get(v_a_1556_, 5);
lean_inc(v_inst_1550_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1567_, 0, v_realize_1553_);
lean_closure_set(v___f_1567_, 1, v_inst_1550_);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_Options_empty;
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_unsigned_to_nat(1000u);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1576_ = l_Lean_firstFrontendMacroScope;
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1565_);
lean_inc_ref(v_fileName_1564_);
v___x_1579_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1579_, 0, v_fileName_1564_);
lean_ctor_set(v___x_1579_, 1, v_fileMap_1565_);
lean_ctor_set(v___x_1579_, 2, v___x_1569_);
lean_ctor_set(v___x_1579_, 3, v___x_1570_);
lean_ctor_set(v___x_1579_, 4, v___x_1571_);
lean_ctor_set(v___x_1579_, 5, v___x_1572_);
lean_ctor_set(v___x_1579_, 6, v___x_1573_);
lean_ctor_set(v___x_1579_, 7, v___x_1574_);
lean_ctor_set(v___x_1579_, 8, v___x_1563_);
lean_ctor_set(v___x_1579_, 9, v___x_1575_);
lean_ctor_set(v___x_1579_, 10, v___x_1573_);
lean_ctor_set(v___x_1579_, 11, v___x_1576_);
lean_ctor_set(v___x_1579_, 12, v___x_1577_);
lean_ctor_set(v___x_1579_, 13, v___x_1578_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*14, v___x_1568_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*14 + 1, v___x_1568_);
v___x_1580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1580_, 0, v___f_1567_);
lean_closure_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1549_, v_env_1560_, v_forConst_1551_, v_key_1552_, v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1634_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1634_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1634_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1587_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1582_, v___x_1586_);
lean_dec(v_a_1582_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v_res_x3f_1589_; lean_object* v_snap_x3f_1590_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v_snap_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_res_x3f_1589_ = lean_ctor_get(v_val_1588_, 0);
lean_inc_ref(v_res_x3f_1589_);
v_snap_x3f_1590_ = lean_ctor_get(v_val_1588_, 1);
lean_inc(v_snap_x3f_1590_);
lean_dec(v_val_1588_);
if (lean_obj_tag(v_snap_x3f_1590_) == 1)
{
lean_object* v_val_1624_; lean_object* v___x_1625_; 
v_val_1624_ = lean_ctor_get(v_snap_x3f_1590_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_snap_x3f_1590_, 1);
v___x_1625_ = l_Lean_Syntax_getRange_x3f(v_ref_1566_, v___x_1568_);
if (lean_obj_tag(v___x_1625_) == 1)
{
lean_object* v_val_1626_; lean_object* v_start_1627_; lean_object* v_stop_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_start_1627_ = lean_ctor_get(v_val_1626_, 0);
lean_inc(v_start_1627_);
v_stop_1628_ = lean_ctor_get(v_val_1626_, 1);
lean_inc(v_stop_1628_);
lean_dec(v_val_1626_);
lean_inc_ref_n(v_fileMap_1565_, 2);
v___x_1629_ = l_Lean_FileMap_toPosition(v_fileMap_1565_, v_start_1627_);
lean_dec(v_start_1627_);
v___x_1630_ = l_Lean_FileMap_toPosition(v_fileMap_1565_, v_stop_1628_);
lean_dec(v_stop_1628_);
v___x_1631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1624_, v___x_1629_, v___x_1630_);
v_snap_1609_ = v___x_1631_;
v___y_1610_ = v_a_1554_;
v___y_1611_ = v_a_1555_;
v___y_1612_ = v_a_1556_;
v___y_1613_ = v_a_1557_;
goto v___jp_1608_;
}
else
{
lean_dec(v___x_1625_);
v_snap_1609_ = v_val_1624_;
v___y_1610_ = v_a_1554_;
v___y_1611_ = v_a_1555_;
v___y_1612_ = v_a_1556_;
v___y_1613_ = v_a_1557_;
goto v___jp_1608_;
}
}
else
{
lean_dec(v_snap_x3f_1590_);
v___y_1592_ = v_a_1554_;
v___y_1593_ = v_a_1555_;
v___y_1594_ = v_a_1556_;
v___y_1595_ = v_a_1557_;
goto v___jp_1591_;
}
v___jp_1591_:
{
if (lean_obj_tag(v_res_x3f_1589_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; 
lean_dec(v_inst_1550_);
v_a_1596_ = lean_ctor_get(v_res_x3f_1589_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_res_x3f_1589_, 1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
lean_ctor_set(v___x_1584_, 0, v_a_1596_);
v___x_1598_ = v___x_1584_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
v_a_1600_ = lean_ctor_get(v_res_x3f_1589_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v_res_x3f_1589_, 1);
v___x_1601_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1600_, v_inst_1550_);
lean_dec(v_inst_1550_);
lean_dec(v_a_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1584_);
v___x_1602_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
v___x_1603_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1602_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1603_;
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
v_val_1604_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v___x_1601_, 1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_val_1604_);
v___x_1606_ = v___x_1584_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
v___jp_1608_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1577_, v_snap_1609_);
v___x_1615_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1614_, v___y_1613_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref_known(v___x_1615_, 1);
v___y_1592_ = v___y_1610_;
v___y_1593_ = v___y_1611_;
v___y_1594_ = v___y_1612_;
v___y_1595_ = v___y_1613_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_res_x3f_1589_);
lean_del_object(v___x_1584_);
lean_dec(v_inst_1550_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v___x_1587_);
lean_del_object(v___x_1584_);
lean_dec(v_inst_1550_);
v___x_1632_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1633_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1632_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_inst_1550_);
v_a_1635_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1637_ = v___x_1581_;
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1581_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1639_ = lean_io_error_to_string(v_a_1635_);
v___x_1640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = l_Lean_MessageData_ofFormat(v___x_1640_);
lean_inc(v_ref_1566_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_ref_1566_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1642_);
v___x_1644_ = v___x_1637_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_forConst_1649_, lean_object* v_key_1650_, lean_object* v_realize_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1647_, v_inst_1648_, v_forConst_1649_, v_key_1650_, v_realize_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1658_, lean_object* v_vals_1659_, lean_object* v_i_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_array_get_size(v_keys_1658_);
v___x_1663_ = lean_nat_dec_lt(v_i_1660_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_dec(v_i_1660_);
v___x_1664_ = lean_box(0);
return v___x_1664_;
}
else
{
lean_object* v_k_x27_1665_; uint8_t v___x_1666_; 
v_k_x27_1665_ = lean_array_fget_borrowed(v_keys_1658_, v_i_1660_);
v___x_1666_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1661_, v_k_x27_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v_i_1660_, v___x_1667_);
lean_dec(v_i_1660_);
v_i_1660_ = v___x_1668_;
goto _start;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_array_fget_borrowed(v_vals_1659_, v_i_1660_);
lean_dec(v_i_1660_);
lean_inc(v___x_1670_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1672_, lean_object* v_vals_1673_, lean_object* v_i_1674_, lean_object* v_k_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1672_, v_vals_1673_, v_i_1674_, v_k_1675_);
lean_dec_ref(v_k_1675_);
lean_dec_ref(v_vals_1673_);
lean_dec_ref(v_keys_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1677_, size_t v_x_1678_, lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v_es_1680_; lean_object* v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; lean_object* v_j_1684_; lean_object* v___x_1685_; 
v_es_1680_ = lean_ctor_get(v_x_1677_, 0);
v___x_1681_ = lean_box(2);
v___x_1682_ = ((size_t)31ULL);
v___x_1683_ = lean_usize_land(v_x_1678_, v___x_1682_);
v_j_1684_ = lean_usize_to_nat(v___x_1683_);
v___x_1685_ = lean_array_get_borrowed(v___x_1681_, v_es_1680_, v_j_1684_);
lean_dec(v_j_1684_);
switch(lean_obj_tag(v___x_1685_))
{
case 0:
{
lean_object* v_key_1686_; lean_object* v_val_1687_; uint8_t v___x_1688_; 
v_key_1686_ = lean_ctor_get(v___x_1685_, 0);
v_val_1687_ = lean_ctor_get(v___x_1685_, 1);
v___x_1688_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1679_, v_key_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_box(0);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; 
lean_inc(v_val_1687_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_val_1687_);
return v___x_1690_;
}
}
case 1:
{
lean_object* v_node_1691_; size_t v___x_1692_; size_t v___x_1693_; 
v_node_1691_ = lean_ctor_get(v___x_1685_, 0);
v___x_1692_ = ((size_t)5ULL);
v___x_1693_ = lean_usize_shift_right(v_x_1678_, v___x_1692_);
v_x_1677_ = v_node_1691_;
v_x_1678_ = v___x_1693_;
goto _start;
}
default: 
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_box(0);
return v___x_1695_;
}
}
}
else
{
lean_object* v_ks_1696_; lean_object* v_vs_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_ks_1696_ = lean_ctor_get(v_x_1677_, 0);
v_vs_1697_ = lean_ctor_get(v_x_1677_, 1);
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1696_, v_vs_1697_, v___x_1698_, v_x_1679_);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
size_t v_x_12530__boxed_1703_; lean_object* v_res_1704_; 
v_x_12530__boxed_1703_ = lean_unbox_usize(v_x_1701_);
lean_dec(v_x_1701_);
v_res_1704_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1700_, v_x_12530__boxed_1703_, v_x_1702_);
lean_dec_ref(v_x_1702_);
lean_dec_ref(v_x_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
uint64_t v_configKey_1707_; lean_object* v_expr_1708_; lean_object* v_nargs_x3f_1709_; uint64_t v___x_1710_; uint64_t v___y_1712_; 
v_configKey_1707_ = lean_ctor_get_uint64(v_x_1706_, sizeof(void*)*2);
v_expr_1708_ = lean_ctor_get(v_x_1706_, 0);
v_nargs_x3f_1709_ = lean_ctor_get(v_x_1706_, 1);
v___x_1710_ = l_Lean_Expr_hash(v_expr_1708_);
if (lean_obj_tag(v_nargs_x3f_1709_) == 0)
{
uint64_t v___x_1717_; 
v___x_1717_ = 11ULL;
v___y_1712_ = v___x_1717_;
goto v___jp_1711_;
}
else
{
lean_object* v_val_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; 
v_val_1718_ = lean_ctor_get(v_nargs_x3f_1709_, 0);
v___x_1719_ = lean_uint64_of_nat(v_val_1718_);
v___x_1720_ = 13ULL;
v___x_1721_ = lean_uint64_mix_hash(v___x_1719_, v___x_1720_);
v___y_1712_ = v___x_1721_;
goto v___jp_1711_;
}
v___jp_1711_:
{
uint64_t v___x_1713_; uint64_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1713_ = lean_uint64_mix_hash(v___x_1710_, v___y_1712_);
v___x_1714_ = lean_uint64_mix_hash(v_configKey_1707_, v___x_1713_);
v___x_1715_ = lean_uint64_to_usize(v___x_1714_);
v___x_1716_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1705_, v___x_1715_, v_x_1706_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1722_, v_x_1723_);
lean_dec_ref(v_x_1723_);
lean_dec_ref(v_x_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v_ks_1729_; lean_object* v_vs_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1754_; 
v_ks_1729_ = lean_ctor_get(v_x_1725_, 0);
v_vs_1730_ = lean_ctor_get(v_x_1725_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_x_1725_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1732_ = v_x_1725_;
v_isShared_1733_ = v_isSharedCheck_1754_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_vs_1730_);
lean_inc(v_ks_1729_);
lean_dec(v_x_1725_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1754_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_array_get_size(v_ks_1729_);
v___x_1735_ = lean_nat_dec_lt(v_x_1726_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec(v_x_1726_);
v___x_1736_ = lean_array_push(v_ks_1729_, v_x_1727_);
v___x_1737_ = lean_array_push(v_vs_1730_, v_x_1728_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1737_);
lean_ctor_set(v___x_1732_, 0, v___x_1736_);
v___x_1739_ = v___x_1732_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
lean_object* v_k_x27_1741_; uint8_t v___x_1742_; 
v_k_x27_1741_ = lean_array_fget_borrowed(v_ks_1729_, v_x_1726_);
v___x_1742_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1727_, v_k_x27_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1744_; 
if (v_isShared_1733_ == 0)
{
v___x_1744_ = v___x_1732_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_ks_1729_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_vs_1730_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_add(v_x_1726_, v___x_1745_);
lean_dec(v_x_1726_);
v_x_1725_ = v___x_1744_;
v_x_1726_ = v___x_1746_;
goto _start;
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = lean_array_fset(v_ks_1729_, v_x_1726_, v_x_1727_);
v___x_1750_ = lean_array_fset(v_vs_1730_, v_x_1726_, v_x_1728_);
lean_dec(v_x_1726_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1750_);
lean_ctor_set(v___x_1732_, 0, v___x_1749_);
v___x_1752_ = v___x_1732_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1755_, lean_object* v_k_1756_, lean_object* v_v_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1755_, v___x_1758_, v_k_1756_, v_v_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1761_, size_t v_x_1762_, size_t v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1761_) == 0)
{
lean_object* v_es_1766_; size_t v___x_1767_; size_t v___x_1768_; lean_object* v_j_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_es_1766_ = lean_ctor_get(v_x_1761_, 0);
v___x_1767_ = ((size_t)31ULL);
v___x_1768_ = lean_usize_land(v_x_1762_, v___x_1767_);
v_j_1769_ = lean_usize_to_nat(v___x_1768_);
v___x_1770_ = lean_array_get_size(v_es_1766_);
v___x_1771_ = lean_nat_dec_lt(v_j_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec(v_j_1769_);
lean_dec(v_x_1765_);
lean_dec_ref(v_x_1764_);
return v_x_1761_;
}
else
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1810_; 
lean_inc_ref(v_es_1766_);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_x_1761_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v_x_1761_, 0);
lean_dec(v_unused_1811_);
v___x_1773_ = v_x_1761_;
v_isShared_1774_ = v_isSharedCheck_1810_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v_x_1761_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1810_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_v_1775_; lean_object* v___x_1776_; lean_object* v_xs_x27_1777_; lean_object* v___y_1779_; 
v_v_1775_ = lean_array_fget(v_es_1766_, v_j_1769_);
v___x_1776_ = lean_box(0);
v_xs_x27_1777_ = lean_array_fset(v_es_1766_, v_j_1769_, v___x_1776_);
switch(lean_obj_tag(v_v_1775_))
{
case 0:
{
lean_object* v_key_1784_; lean_object* v_val_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_key_1784_ = lean_ctor_get(v_v_1775_, 0);
v_val_1785_ = lean_ctor_get(v_v_1775_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_v_1775_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v_v_1775_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_val_1785_);
lean_inc(v_key_1784_);
lean_dec(v_v_1775_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
uint8_t v___x_1789_; 
v___x_1789_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1764_, v_key_1784_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_del_object(v___x_1787_);
v___x_1790_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1784_, v_val_1785_, v_x_1764_, v_x_1765_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
v___y_1779_ = v___x_1791_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1793_; 
lean_dec(v_val_1785_);
lean_dec(v_key_1784_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_x_1765_);
lean_ctor_set(v___x_1787_, 0, v_x_1764_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_x_1764_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_x_1765_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v___y_1779_ = v___x_1793_;
goto v___jp_1778_;
}
}
}
}
case 1:
{
lean_object* v_node_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1808_; 
v_node_1796_ = lean_ctor_get(v_v_1775_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_v_1775_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1798_ = v_v_1775_;
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_node_1796_);
lean_dec(v_v_1775_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
size_t v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1800_ = ((size_t)5ULL);
v___x_1801_ = lean_usize_shift_right(v_x_1762_, v___x_1800_);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_x_1763_, v___x_1802_);
v___x_1804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1796_, v___x_1801_, v___x_1803_, v_x_1764_, v_x_1765_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1804_);
v___x_1806_ = v___x_1798_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v___y_1779_ = v___x_1806_;
goto v___jp_1778_;
}
}
}
default: 
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_x_1764_);
lean_ctor_set(v___x_1809_, 1, v_x_1765_);
v___y_1779_ = v___x_1809_;
goto v___jp_1778_;
}
}
v___jp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_array_fset(v_xs_x27_1777_, v_j_1769_, v___y_1779_);
lean_dec(v_j_1769_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1780_);
v___x_1782_ = v___x_1773_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
else
{
lean_object* v_ks_1812_; lean_object* v_vs_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1831_; 
v_ks_1812_ = lean_ctor_get(v_x_1761_, 0);
v_vs_1813_ = lean_ctor_get(v_x_1761_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_x_1761_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1815_ = v_x_1761_;
v_isShared_1816_ = v_isSharedCheck_1831_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_vs_1813_);
lean_inc(v_ks_1812_);
lean_dec(v_x_1761_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1831_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_ks_1812_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_vs_1813_);
v___x_1818_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v_newNode_1819_; size_t v___x_1820_; uint8_t v___x_1821_; 
v_newNode_1819_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1818_, v_x_1764_, v_x_1765_);
v___x_1820_ = ((size_t)7ULL);
v___x_1821_ = lean_usize_dec_le(v___x_1820_, v_x_1763_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1822_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1819_);
v___x_1823_ = lean_unsigned_to_nat(4u);
v___x_1824_ = lean_nat_dec_lt(v___x_1822_, v___x_1823_);
lean_dec(v___x_1822_);
if (v___x_1824_ == 0)
{
lean_object* v_ks_1825_; lean_object* v_vs_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_ks_1825_ = lean_ctor_get(v_newNode_1819_, 0);
lean_inc_ref(v_ks_1825_);
v_vs_1826_ = lean_ctor_get(v_newNode_1819_, 1);
lean_inc_ref(v_vs_1826_);
lean_dec_ref(v_newNode_1819_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
v___x_1829_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1763_, v_ks_1825_, v_vs_1826_, v___x_1827_, v___x_1828_);
lean_dec_ref(v_vs_1826_);
lean_dec_ref(v_ks_1825_);
return v___x_1829_;
}
else
{
return v_newNode_1819_;
}
}
else
{
return v_newNode_1819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1832_, lean_object* v_keys_1833_, lean_object* v_vals_1834_, lean_object* v_i_1835_, lean_object* v_entries_1836_){
_start:
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_array_get_size(v_keys_1833_);
v___x_1838_ = lean_nat_dec_lt(v_i_1835_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec(v_i_1835_);
return v_entries_1836_;
}
else
{
lean_object* v_k_1839_; uint64_t v_configKey_1840_; lean_object* v_expr_1841_; lean_object* v_nargs_x3f_1842_; lean_object* v_v_1843_; uint64_t v___x_1844_; uint64_t v___y_1846_; 
v_k_1839_ = lean_array_fget_borrowed(v_keys_1833_, v_i_1835_);
v_configKey_1840_ = lean_ctor_get_uint64(v_k_1839_, sizeof(void*)*2);
v_expr_1841_ = lean_ctor_get(v_k_1839_, 0);
v_nargs_x3f_1842_ = lean_ctor_get(v_k_1839_, 1);
v_v_1843_ = lean_array_fget_borrowed(v_vals_1834_, v_i_1835_);
v___x_1844_ = l_Lean_Expr_hash(v_expr_1841_);
if (lean_obj_tag(v_nargs_x3f_1842_) == 0)
{
uint64_t v___x_1859_; 
v___x_1859_ = 11ULL;
v___y_1846_ = v___x_1859_;
goto v___jp_1845_;
}
else
{
lean_object* v_val_1860_; uint64_t v___x_1861_; uint64_t v___x_1862_; uint64_t v___x_1863_; 
v_val_1860_ = lean_ctor_get(v_nargs_x3f_1842_, 0);
v___x_1861_ = lean_uint64_of_nat(v_val_1860_);
v___x_1862_ = 13ULL;
v___x_1863_ = lean_uint64_mix_hash(v___x_1861_, v___x_1862_);
v___y_1846_ = v___x_1863_;
goto v___jp_1845_;
}
v___jp_1845_:
{
uint64_t v___x_1847_; uint64_t v___x_1848_; size_t v_h_1849_; size_t v___x_1850_; lean_object* v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v_h_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1847_ = lean_uint64_mix_hash(v___x_1844_, v___y_1846_);
v___x_1848_ = lean_uint64_mix_hash(v_configKey_1840_, v___x_1847_);
v_h_1849_ = lean_uint64_to_usize(v___x_1848_);
v___x_1850_ = ((size_t)5ULL);
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_sub(v_depth_1832_, v___x_1852_);
v___x_1854_ = lean_usize_mul(v___x_1850_, v___x_1853_);
v_h_1855_ = lean_usize_shift_right(v_h_1849_, v___x_1854_);
v___x_1856_ = lean_nat_add(v_i_1835_, v___x_1851_);
lean_dec(v_i_1835_);
lean_inc(v_v_1843_);
lean_inc(v_k_1839_);
v___x_1857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1836_, v_h_1855_, v_depth_1832_, v_k_1839_, v_v_1843_);
v_i_1835_ = v___x_1856_;
v_entries_1836_ = v___x_1857_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1864_, lean_object* v_keys_1865_, lean_object* v_vals_1866_, lean_object* v_i_1867_, lean_object* v_entries_1868_){
_start:
{
size_t v_depth_boxed_1869_; lean_object* v_res_1870_; 
v_depth_boxed_1869_ = lean_unbox_usize(v_depth_1864_);
lean_dec(v_depth_1864_);
v_res_1870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1869_, v_keys_1865_, v_vals_1866_, v_i_1867_, v_entries_1868_);
lean_dec_ref(v_vals_1866_);
lean_dec_ref(v_keys_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
size_t v_x_12701__boxed_1876_; size_t v_x_12702__boxed_1877_; lean_object* v_res_1878_; 
v_x_12701__boxed_1876_ = lean_unbox_usize(v_x_1872_);
lean_dec(v_x_1872_);
v_x_12702__boxed_1877_ = lean_unbox_usize(v_x_1873_);
lean_dec(v_x_1873_);
v_res_1878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1871_, v_x_12701__boxed_1876_, v_x_12702__boxed_1877_, v_x_1874_, v_x_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
uint64_t v_configKey_1882_; lean_object* v_expr_1883_; lean_object* v_nargs_x3f_1884_; uint64_t v___x_1885_; uint64_t v___y_1887_; 
v_configKey_1882_ = lean_ctor_get_uint64(v_x_1880_, sizeof(void*)*2);
v_expr_1883_ = lean_ctor_get(v_x_1880_, 0);
v_nargs_x3f_1884_ = lean_ctor_get(v_x_1880_, 1);
v___x_1885_ = l_Lean_Expr_hash(v_expr_1883_);
if (lean_obj_tag(v_nargs_x3f_1884_) == 0)
{
uint64_t v___x_1893_; 
v___x_1893_ = 11ULL;
v___y_1887_ = v___x_1893_;
goto v___jp_1886_;
}
else
{
lean_object* v_val_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; 
v_val_1894_ = lean_ctor_get(v_nargs_x3f_1884_, 0);
v___x_1895_ = lean_uint64_of_nat(v_val_1894_);
v___x_1896_ = 13ULL;
v___x_1897_ = lean_uint64_mix_hash(v___x_1895_, v___x_1896_);
v___y_1887_ = v___x_1897_;
goto v___jp_1886_;
}
v___jp_1886_:
{
uint64_t v___x_1888_; uint64_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1888_ = lean_uint64_mix_hash(v___x_1885_, v___y_1887_);
v___x_1889_ = lean_uint64_mix_hash(v_configKey_1882_, v___x_1888_);
v___x_1890_ = lean_uint64_to_usize(v___x_1889_);
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1879_, v___x_1890_, v___x_1891_, v_x_1880_, v_x_1881_);
return v___x_1892_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1898_) == 0)
{
uint8_t v___x_1899_; 
v___x_1899_ = 0;
return v___x_1899_;
}
else
{
lean_object* v_head_1900_; lean_object* v_tail_1901_; uint8_t v___x_1902_; 
v_head_1900_ = lean_ctor_get(v_x_1898_, 0);
v_tail_1901_ = lean_ctor_get(v_x_1898_, 1);
v___x_1902_ = l_Lean_Level_hasMVar(v_head_1900_);
if (v___x_1902_ == 0)
{
v_x_1898_ = v_tail_1901_;
goto _start;
}
else
{
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1904_);
lean_dec(v_x_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1909_, lean_object* v_maxArgs_x3f_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
lean_inc(v_maxArgs_x3f_1910_);
lean_inc_ref(v_fn_1909_);
v___x_1916_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1909_, v_maxArgs_x3f_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1981_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1981_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1981_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_finfo_1922_; lean_object* v___y_1923_; lean_object* v___x_1955_; lean_object* v_cache_1956_; lean_object* v_funInfo_1957_; lean_object* v___x_1958_; 
v___x_1955_ = lean_st_ref_get(v_a_1912_);
v_cache_1956_ = lean_ctor_get(v___x_1955_, 1);
lean_inc_ref(v_cache_1956_);
lean_dec(v___x_1955_);
v_funInfo_1957_ = lean_ctor_get(v_cache_1956_, 1);
lean_inc_ref(v_funInfo_1957_);
lean_dec_ref(v_cache_1956_);
v___x_1958_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1957_, v_a_1917_);
lean_dec_ref(v_funInfo_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___f_1959_; lean_object* v___f_1960_; 
v___f_1959_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc(v_maxArgs_x3f_1910_);
lean_inc_ref(v_fn_1909_);
v___f_1960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1960_, 0, v_fn_1909_);
lean_closure_set(v___f_1960_, 1, v_maxArgs_x3f_1910_);
lean_closure_set(v___f_1960_, 2, v___f_1959_);
if (lean_obj_tag(v_fn_1909_) == 4)
{
lean_object* v_declName_1961_; lean_object* v_us_1962_; uint8_t v___x_1963_; 
v_declName_1961_ = lean_ctor_get(v_fn_1909_, 0);
v_us_1962_ = lean_ctor_get(v_fn_1909_, 1);
v___x_1963_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_inc(v_us_1962_);
lean_inc_n(v_declName_1961_, 2);
lean_dec_ref_known(v_fn_1909_, 2);
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_1965_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_1966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1966_, 0, v_declName_1961_);
lean_ctor_set(v___x_1966_, 1, v_us_1962_);
lean_ctor_set(v___x_1966_, 2, v_maxArgs_x3f_1910_);
v___x_1967_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_1964_, v___x_1965_, v_declName_1961_, v___x_1966_, v___f_1960_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v_finfo_1922_ = v_a_1968_;
v___y_1923_ = v_a_1912_;
goto v___jp_1921_;
}
else
{
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
return v___x_1967_;
}
}
else
{
lean_object* v___x_1969_; 
lean_dec_ref(v___f_1960_);
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
v___x_1969_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1909_, v_maxArgs_x3f_1910_, v___f_1959_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v_finfo_1922_ = v_a_1970_;
v___y_1923_ = v_a_1912_;
goto v___jp_1921_;
}
else
{
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
return v___x_1969_;
}
}
}
else
{
lean_object* v___x_1971_; 
lean_dec_ref(v___f_1960_);
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
v___x_1971_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1909_, v_maxArgs_x3f_1910_, v___f_1959_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v_finfo_1922_ = v_a_1972_;
v___y_1923_ = v_a_1912_;
goto v___jp_1921_;
}
else
{
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
return v___x_1971_;
}
}
}
else
{
lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
lean_dec(v_maxArgs_x3f_1910_);
lean_dec_ref(v_fn_1909_);
v_val_1973_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1958_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_dec(v___x_1958_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 0);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_val_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
v___jp_1921_:
{
lean_object* v___x_1924_; lean_object* v_cache_1925_; lean_object* v_mctx_1926_; lean_object* v_zetaDeltaFVarIds_1927_; lean_object* v_postponed_1928_; lean_object* v_diag_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1954_; 
v___x_1924_ = lean_st_ref_take(v___y_1923_);
v_cache_1925_ = lean_ctor_get(v___x_1924_, 1);
v_mctx_1926_ = lean_ctor_get(v___x_1924_, 0);
v_zetaDeltaFVarIds_1927_ = lean_ctor_get(v___x_1924_, 2);
v_postponed_1928_ = lean_ctor_get(v___x_1924_, 3);
v_diag_1929_ = lean_ctor_get(v___x_1924_, 4);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1931_ = v___x_1924_;
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_diag_1929_);
lean_inc(v_postponed_1928_);
lean_inc(v_zetaDeltaFVarIds_1927_);
lean_inc(v_cache_1925_);
lean_inc(v_mctx_1926_);
lean_dec(v___x_1924_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_inferType_1933_; lean_object* v_funInfo_1934_; lean_object* v_synthInstance_1935_; lean_object* v_whnf_1936_; lean_object* v_defEqTrans_1937_; lean_object* v_defEqPerm_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1953_; 
v_inferType_1933_ = lean_ctor_get(v_cache_1925_, 0);
v_funInfo_1934_ = lean_ctor_get(v_cache_1925_, 1);
v_synthInstance_1935_ = lean_ctor_get(v_cache_1925_, 2);
v_whnf_1936_ = lean_ctor_get(v_cache_1925_, 3);
v_defEqTrans_1937_ = lean_ctor_get(v_cache_1925_, 4);
v_defEqPerm_1938_ = lean_ctor_get(v_cache_1925_, 5);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_cache_1925_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1940_ = v_cache_1925_;
v_isShared_1941_ = v_isSharedCheck_1953_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_defEqPerm_1938_);
lean_inc(v_defEqTrans_1937_);
lean_inc(v_whnf_1936_);
lean_inc(v_synthInstance_1935_);
lean_inc(v_funInfo_1934_);
lean_inc(v_inferType_1933_);
lean_dec(v_cache_1925_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1953_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_inc_ref(v_finfo_1922_);
v___x_1942_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1934_, v_a_1917_, v_finfo_1922_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_inferType_1933_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_synthInstance_1935_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_whnf_1936_);
lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_defEqTrans_1937_);
lean_ctor_set(v_reuseFailAlloc_1952_, 5, v_defEqPerm_1938_);
v___x_1944_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v___x_1944_);
v___x_1946_ = v___x_1931_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_mctx_1926_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_zetaDeltaFVarIds_1927_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_postponed_1928_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_diag_1929_);
v___x_1946_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_st_ref_put(v___y_1923_, v___x_1946_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_finfo_1922_);
v___x_1949_ = v___x_1919_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_finfo_1922_);
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
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v_maxArgs_x3f_1910_);
lean_dec_ref(v_fn_1909_);
v_a_1982_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1916_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1916_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_1990_, lean_object* v_maxArgs_x3f_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_1990_, v_maxArgs_x3f_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_1998_, lean_object* v_k_1999_, lean_object* v_t_2000_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_1999_, v_t_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2002_, lean_object* v_k_2003_, lean_object* v_t_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2002_, v_k_2003_, v_t_2004_);
lean_dec(v_t_2004_);
lean_dec(v_k_2003_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2007_, lean_object* v_val_2008_, lean_object* v___x_2009_, lean_object* v_fvars_2010_, lean_object* v_next_2011_, lean_object* v_upperBound_2012_, lean_object* v_inst_2013_, lean_object* v_R_2014_, lean_object* v_a_2015_, lean_object* v_b_2016_, lean_object* v_c_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2007_, v_val_2008_, v___x_2009_, v_fvars_2010_, v_next_2011_, v_upperBound_2012_, v_a_2015_, v_b_2016_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2024_, lean_object* v_val_2025_, lean_object* v___x_2026_, lean_object* v_fvars_2027_, lean_object* v_next_2028_, lean_object* v_upperBound_2029_, lean_object* v_inst_2030_, lean_object* v_R_2031_, lean_object* v_a_2032_, lean_object* v_b_2033_, lean_object* v_c_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2024_, v_val_2025_, v___x_2026_, v_fvars_2027_, v_next_2028_, v_upperBound_2029_, v_inst_2030_, v_R_2031_, v_a_2032_, v_b_2033_, v_c_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v_upperBound_2029_);
lean_dec(v_next_2028_);
lean_dec_ref(v_fvars_2027_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_val_2025_);
lean_dec(v_upperBound_2024_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2041_, lean_object* v_fvars_2042_, lean_object* v_inst_2043_, lean_object* v_R_2044_, lean_object* v_a_2045_, lean_object* v_b_2046_, lean_object* v_c_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2041_, v_fvars_2042_, v_a_2045_, v_b_2046_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2054_, lean_object* v_fvars_2055_, lean_object* v_inst_2056_, lean_object* v_R_2057_, lean_object* v_a_2058_, lean_object* v_b_2059_, lean_object* v_c_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2054_, v_fvars_2055_, v_inst_2056_, v_R_2057_, v_a_2058_, v_b_2059_, v_c_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec_ref(v_fvars_2055_);
lean_dec(v_upperBound_2054_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2068_, v_x_2069_, v_x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2073_, v_x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2076_, v_x_2077_, v_x_2078_);
lean_dec_ref(v_x_2078_);
lean_dec_ref(v_x_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2080_, lean_object* v_msg_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2088_, lean_object* v_msg_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2088_, v_msg_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_forConst_2099_, lean_object* v_key_2100_, lean_object* v_realize_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2097_, v_inst_2098_, v_forConst_2099_, v_key_2100_, v_realize_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_forConst_2111_, lean_object* v_key_2112_, lean_object* v_realize_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2108_, v_inst_2109_, v_inst_2110_, v_forConst_2111_, v_key_2112_, v_realize_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2120_, lean_object* v_x_2121_, size_t v_x_2122_, size_t v_x_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2121_, v_x_2122_, v_x_2123_, v_x_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
size_t v_x_13149__boxed_2133_; size_t v_x_13150__boxed_2134_; lean_object* v_res_2135_; 
v_x_13149__boxed_2133_ = lean_unbox_usize(v_x_2129_);
lean_dec(v_x_2129_);
v_x_13150__boxed_2134_ = lean_unbox_usize(v_x_2130_);
lean_dec(v_x_2130_);
v_res_2135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2127_, v_x_2128_, v_x_13149__boxed_2133_, v_x_13150__boxed_2134_, v_x_2131_, v_x_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2136_, lean_object* v_x_2137_, size_t v_x_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2137_, v_x_2138_, v_x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
size_t v_x_13166__boxed_2145_; lean_object* v_res_2146_; 
v_x_13166__boxed_2145_ = lean_unbox_usize(v_x_2143_);
lean_dec(v_x_2143_);
v_res_2146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2141_, v_x_2142_, v_x_13166__boxed_2145_, v_x_2144_);
lean_dec_ref(v_x_2144_);
lean_dec_ref(v_x_2142_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2147_, lean_object* v_n_2148_, lean_object* v_k_2149_, lean_object* v_v_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2148_, v_k_2149_, v_v_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2152_, size_t v_depth_2153_, lean_object* v_keys_2154_, lean_object* v_vals_2155_, lean_object* v_heq_2156_, lean_object* v_i_2157_, lean_object* v_entries_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2153_, v_keys_2154_, v_vals_2155_, v_i_2157_, v_entries_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2160_, lean_object* v_depth_2161_, lean_object* v_keys_2162_, lean_object* v_vals_2163_, lean_object* v_heq_2164_, lean_object* v_i_2165_, lean_object* v_entries_2166_){
_start:
{
size_t v_depth_boxed_2167_; lean_object* v_res_2168_; 
v_depth_boxed_2167_ = lean_unbox_usize(v_depth_2161_);
lean_dec(v_depth_2161_);
v_res_2168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2160_, v_depth_boxed_2167_, v_keys_2162_, v_vals_2163_, v_heq_2164_, v_i_2165_, v_entries_2166_);
lean_dec_ref(v_vals_2163_);
lean_dec_ref(v_keys_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2169_, lean_object* v_keys_2170_, lean_object* v_vals_2171_, lean_object* v_heq_2172_, lean_object* v_i_2173_, lean_object* v_k_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2170_, v_vals_2171_, v_i_2173_, v_k_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_keys_2177_, lean_object* v_vals_2178_, lean_object* v_heq_2179_, lean_object* v_i_2180_, lean_object* v_k_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2176_, v_keys_2177_, v_vals_2178_, v_heq_2179_, v_i_2180_, v_k_2181_);
lean_dec_ref(v_k_2181_);
lean_dec_ref(v_vals_2178_);
lean_dec_ref(v_keys_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2184_, v_x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2187_, v_x_2188_, v_x_2189_);
lean_dec_ref(v_x_2189_);
lean_dec_ref(v_x_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2192_, v_x_2193_, v_x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(lean_object* v_00_u03b2_2196_, lean_object* v_m_2197_, lean_object* v_a_2198_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_2197_, v_a_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(lean_object* v_00_u03b2_2200_, lean_object* v_m_2201_, lean_object* v_a_2202_){
_start:
{
uint8_t v_res_2203_; lean_object* v_r_2204_; 
v_res_2203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_2200_, v_m_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_m_2201_);
v_r_2204_ = lean_box(v_res_2203_);
return v_r_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2206_, v_x_2207_, v_x_2208_, v_x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2211_, lean_object* v_x_2212_, size_t v_x_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2212_, v_x_2213_, v_x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
size_t v_x_13211__boxed_2220_; lean_object* v_res_2221_; 
v_x_13211__boxed_2220_ = lean_unbox_usize(v_x_2218_);
lean_dec(v_x_2218_);
v_res_2221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2216_, v_x_2217_, v_x_13211__boxed_2220_, v_x_2219_);
lean_dec_ref(v_x_2219_);
lean_dec_ref(v_x_2217_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2222_, lean_object* v_x_2223_, size_t v_x_2224_, size_t v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2223_, v_x_2224_, v_x_2225_, v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
size_t v_x_13222__boxed_2235_; size_t v_x_13223__boxed_2236_; lean_object* v_res_2237_; 
v_x_13222__boxed_2235_ = lean_unbox_usize(v_x_2231_);
lean_dec(v_x_2231_);
v_x_13223__boxed_2236_ = lean_unbox_usize(v_x_2232_);
lean_dec(v_x_2232_);
v_res_2237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2229_, v_x_2230_, v_x_13222__boxed_2235_, v_x_13223__boxed_2236_, v_x_2233_, v_x_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(lean_object* v_00_u03b2_2238_, lean_object* v_a_2239_, lean_object* v_x_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_2239_, v_x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_a_2243_, lean_object* v_x_2244_){
_start:
{
uint8_t v_res_2245_; lean_object* v_r_2246_; 
v_res_2245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_2242_, v_a_2243_, v_x_2244_);
lean_dec(v_x_2244_);
lean_dec(v_a_2243_);
v_r_2246_ = lean_box(v_res_2245_);
return v_r_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2247_, lean_object* v_keys_2248_, lean_object* v_vals_2249_, lean_object* v_heq_2250_, lean_object* v_i_2251_, lean_object* v_k_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2248_, v_vals_2249_, v_i_2251_, v_k_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2254_, lean_object* v_keys_2255_, lean_object* v_vals_2256_, lean_object* v_heq_2257_, lean_object* v_i_2258_, lean_object* v_k_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2254_, v_keys_2255_, v_vals_2256_, v_heq_2257_, v_i_2258_, v_k_2259_);
lean_dec_ref(v_k_2259_);
lean_dec_ref(v_vals_2256_);
lean_dec_ref(v_keys_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2261_, lean_object* v_n_2262_, lean_object* v_k_2263_, lean_object* v_v_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2262_, v_k_2263_, v_v_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2266_, size_t v_depth_2267_, lean_object* v_keys_2268_, lean_object* v_vals_2269_, lean_object* v_heq_2270_, lean_object* v_i_2271_, lean_object* v_entries_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2267_, v_keys_2268_, v_vals_2269_, v_i_2271_, v_entries_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2274_, lean_object* v_depth_2275_, lean_object* v_keys_2276_, lean_object* v_vals_2277_, lean_object* v_heq_2278_, lean_object* v_i_2279_, lean_object* v_entries_2280_){
_start:
{
size_t v_depth_boxed_2281_; lean_object* v_res_2282_; 
v_depth_boxed_2281_ = lean_unbox_usize(v_depth_2275_);
lean_dec(v_depth_2275_);
v_res_2282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2274_, v_depth_boxed_2281_, v_keys_2276_, v_vals_2277_, v_heq_2278_, v_i_2279_, v_entries_2280_);
lean_dec_ref(v_vals_2277_);
lean_dec_ref(v_keys_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(lean_object* v_00_u03b2_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_2284_, v_x_2285_, v_x_2286_, v_x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2289_, lean_object* v_maxArgs_x3f_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2289_, v_maxArgs_x3f_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2297_, lean_object* v_maxArgs_x3f_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Meta_getFunInfo(v_fn_2297_, v_maxArgs_x3f_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2305_, lean_object* v_nargs_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v_nargs_2306_);
v___x_2313_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2305_, v___x_2312_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2314_, lean_object* v_nargs_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2314_, v_nargs_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2322_){
_start:
{
lean_object* v_paramInfo_2323_; lean_object* v___x_2324_; 
v_paramInfo_2323_ = lean_ctor_get(v_info_2322_, 0);
v___x_2324_ = lean_array_get_size(v_paramInfo_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Meta_FunInfo_getArity(v_info_2325_);
lean_dec_ref(v_info_2325_);
return v_res_2326_;
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
