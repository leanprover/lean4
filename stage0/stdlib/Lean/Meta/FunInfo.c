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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_find_expr(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
lean_object* l_Lean_Meta_instBEqInfoCacheKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hasMVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqInfoCacheKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1 = (const lean_object*)&l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "trying to realize `"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "` value but `enableRealizationsForConst` must be called for `"};
static const lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1 = (const lean_object*)&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value;
static const lean_string_object l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` first"};
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
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Meta.Basic"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.realizeValue"};
static const lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_x_9_, v_x_10_);
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
v___x_38_ = l_instBEqOption_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_maxArgs_x3f_32_, v_maxArgs_x3f_35_);
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
lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___f_124_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0));
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1));
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2));
v___x_127_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0));
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0));
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_130_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
lean_inc(v_maxArgs_x3f_117_);
lean_inc_ref(v_fn_116_);
v___x_131_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_116_, v_maxArgs_x3f_117_, v_a_119_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_193_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_193_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_193_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_193_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_finfo_137_; lean_object* v___y_138_; lean_object* v___x_171_; lean_object* v_cache_172_; lean_object* v_funInfo_173_; lean_object* v___x_174_; 
v___x_171_ = lean_st_ref_get(v_a_120_);
v_cache_172_ = lean_ctor_get(v___x_171_, 1);
lean_inc_ref(v_cache_172_);
lean_dec(v___x_171_);
v_funInfo_173_ = lean_ctor_get(v_cache_172_, 1);
lean_inc_ref(v_funInfo_173_);
lean_dec_ref(v_cache_172_);
lean_inc(v_a_132_);
v___x_174_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_125_, v___x_126_, v_funInfo_173_, v_a_132_);
lean_dec_ref(v_funInfo_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
if (lean_obj_tag(v_fn_116_) == 4)
{
lean_object* v_declName_175_; lean_object* v_us_176_; uint8_t v___x_177_; 
v_declName_175_ = lean_ctor_get(v_fn_116_, 0);
lean_inc(v_declName_175_);
v_us_176_ = lean_ctor_get(v_fn_116_, 1);
lean_inc_n(v_us_176_, 2);
lean_dec_ref_known(v_fn_116_, 2);
v___x_177_ = l_List_any___redArg(v_us_176_, v___f_124_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc(v_declName_175_);
v___x_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_178_, 0, v_declName_175_);
lean_ctor_set(v___x_178_, 1, v_us_176_);
lean_ctor_set(v___x_178_, 2, v_maxArgs_x3f_117_);
v___x_179_ = l_Lean_Meta_realizeValue___redArg(v___x_127_, v___x_128_, v___x_129_, v___x_130_, v_declName_175_, v___x_178_, v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v_finfo_137_ = v_a_180_;
v___y_138_ = v_a_120_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_134_);
lean_dec(v_a_132_);
return v___x_179_;
}
}
else
{
lean_object* v___x_181_; 
lean_dec(v_us_176_);
lean_dec(v_declName_175_);
lean_dec(v_maxArgs_x3f_117_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_181_ = lean_apply_5(v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v_finfo_137_ = v_a_182_;
v___y_138_ = v_a_120_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_134_);
lean_dec(v_a_132_);
return v___x_181_;
}
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_183_ = lean_apply_5(v_k_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v_finfo_137_ = v_a_184_;
v___y_138_ = v_a_120_;
goto v___jp_136_;
}
else
{
lean_del_object(v___x_134_);
lean_dec(v_a_132_);
return v___x_183_;
}
}
}
else
{
lean_object* v_val_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_del_object(v___x_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_k_118_);
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
v_val_185_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_174_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_val_185_);
lean_dec(v___x_174_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_val_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
v___jp_136_:
{
lean_object* v___x_139_; lean_object* v_cache_140_; lean_object* v_mctx_141_; lean_object* v_zetaDeltaFVarIds_142_; lean_object* v_postponed_143_; lean_object* v_diag_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_170_; 
v___x_139_ = lean_st_ref_take(v___y_138_);
v_cache_140_ = lean_ctor_get(v___x_139_, 1);
v_mctx_141_ = lean_ctor_get(v___x_139_, 0);
v_zetaDeltaFVarIds_142_ = lean_ctor_get(v___x_139_, 2);
v_postponed_143_ = lean_ctor_get(v___x_139_, 3);
v_diag_144_ = lean_ctor_get(v___x_139_, 4);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_170_ == 0)
{
v___x_146_ = v___x_139_;
v_isShared_147_ = v_isSharedCheck_170_;
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
v_isShared_147_ = v_isSharedCheck_170_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_inferType_148_; lean_object* v_funInfo_149_; lean_object* v_synthInstance_150_; lean_object* v_whnf_151_; lean_object* v_defEqTrans_152_; lean_object* v_defEqPerm_153_; lean_object* v_isUnitLike_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_169_; 
v_inferType_148_ = lean_ctor_get(v_cache_140_, 0);
v_funInfo_149_ = lean_ctor_get(v_cache_140_, 1);
v_synthInstance_150_ = lean_ctor_get(v_cache_140_, 2);
v_whnf_151_ = lean_ctor_get(v_cache_140_, 3);
v_defEqTrans_152_ = lean_ctor_get(v_cache_140_, 4);
v_defEqPerm_153_ = lean_ctor_get(v_cache_140_, 5);
v_isUnitLike_154_ = lean_ctor_get(v_cache_140_, 6);
v_isSharedCheck_169_ = !lean_is_exclusive(v_cache_140_);
if (v_isSharedCheck_169_ == 0)
{
v___x_156_ = v_cache_140_;
v_isShared_157_ = v_isSharedCheck_169_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_isUnitLike_154_);
lean_inc(v_defEqPerm_153_);
lean_inc(v_defEqTrans_152_);
lean_inc(v_whnf_151_);
lean_inc(v_synthInstance_150_);
lean_inc(v_funInfo_149_);
lean_inc(v_inferType_148_);
lean_dec(v_cache_140_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_169_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc_ref(v_finfo_137_);
v___x_158_ = l_Lean_PersistentHashMap_insert___redArg(v___x_125_, v___x_126_, v_funInfo_149_, v_a_132_, v_finfo_137_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_inferType_148_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_synthInstance_150_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_whnf_151_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_defEqTrans_152_);
lean_ctor_set(v_reuseFailAlloc_168_, 5, v_defEqPerm_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 6, v_isUnitLike_154_);
v___x_160_ = v_reuseFailAlloc_168_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_160_);
v___x_162_ = v___x_146_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_mctx_141_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_zetaDeltaFVarIds_142_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_postponed_143_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_diag_144_);
v___x_162_ = v_reuseFailAlloc_167_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_st_ref_put(v___y_138_, v___x_162_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v_finfo_137_);
v___x_165_ = v___x_134_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_finfo_137_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
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
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_k_118_);
lean_dec(v_maxArgs_x3f_117_);
lean_dec_ref(v_fn_116_);
v_a_194_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_131_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_131_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(lean_object* v_fn_202_, lean_object* v_maxArgs_x3f_203_, lean_object* v_k_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(v_fn_202_, v_maxArgs_x3f_203_, v_k_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object* v_e_211_, lean_object* v_deps_212_, lean_object* v_k_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_Expr_hasFVar(v_e_211_);
if (v___x_214_ == 0)
{
lean_dec(v_k_213_);
return v_deps_212_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_apply_1(v_k_213_, v_deps_212_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object* v_e_216_, lean_object* v_deps_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(v_e_216_, v_deps_217_, v_k_218_);
lean_dec_ref(v_e_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* v_00_u03b1_220_, lean_object* v_e_221_, lean_object* v_deps_222_, lean_object* v_k_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Expr_hasFVar(v_e_221_);
if (v___x_224_ == 0)
{
lean_dec(v_k_223_);
return v_deps_222_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_apply_1(v_k_223_, v_deps_222_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object* v_00_u03b1_226_, lean_object* v_e_227_, lean_object* v_deps_228_, lean_object* v_k_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(v_00_u03b1_226_, v_e_227_, v_deps_228_, v_k_229_);
lean_dec_ref(v_e_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(lean_object* v_xs_231_, lean_object* v_v_232_, lean_object* v_i_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_get_size(v_xs_231_);
v___x_235_ = lean_nat_dec_lt(v_i_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v_i_233_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_array_fget_borrowed(v_xs_231_, v_i_233_);
v___x_238_ = lean_expr_eqv(v___x_237_, v_v_232_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_i_233_, v___x_239_);
lean_dec(v_i_233_);
v_i_233_ = v___x_240_;
goto _start;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_i_233_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_243_, lean_object* v_v_244_, lean_object* v_i_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_243_, v_v_244_, v_i_245_);
lean_dec_ref(v_v_244_);
lean_dec_ref(v_xs_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object* v_xs_247_, lean_object* v_v_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_247_, v_v_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object* v_xs_251_, lean_object* v_v_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_251_, v_v_252_);
lean_dec_ref(v_v_252_);
lean_dec_ref(v_xs_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* v_xs_254_, lean_object* v_v_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_254_, v_v_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v_val_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_val_258_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_256_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_val_258_);
lean_dec(v___x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_val_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* v_xs_266_, lean_object* v_v_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_xs_266_, v_v_267_);
lean_dec_ref(v_v_267_);
lean_dec_ref(v_xs_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(lean_object* v_a_269_, lean_object* v_as_270_, size_t v_i_271_, size_t v_stop_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_usize_dec_eq(v_i_271_, v_stop_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_array_uget_borrowed(v_as_270_, v_i_271_);
v___x_275_ = lean_nat_dec_eq(v_a_269_, v___x_274_);
if (v___x_275_ == 0)
{
size_t v___x_276_; size_t v___x_277_; 
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_271_, v___x_276_);
v_i_271_ = v___x_277_;
goto _start;
}
else
{
return v___x_275_;
}
}
else
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(lean_object* v_a_280_, lean_object* v_as_281_, lean_object* v_i_282_, lean_object* v_stop_283_){
_start:
{
size_t v_i_boxed_284_; size_t v_stop_boxed_285_; uint8_t v_res_286_; lean_object* v_r_287_; 
v_i_boxed_284_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_stop_boxed_285_ = lean_unbox_usize(v_stop_283_);
lean_dec(v_stop_283_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_280_, v_as_281_, v_i_boxed_284_, v_stop_boxed_285_);
lean_dec_ref(v_as_281_);
lean_dec(v_a_280_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(lean_object* v_as_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_size(v_as_288_);
v___x_292_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
return v___x_292_;
}
else
{
size_t v___x_293_; size_t v___x_294_; uint8_t v___x_295_; 
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_291_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_289_, v_as_288_, v___x_293_, v___x_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(lean_object* v_as_296_, lean_object* v_a_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_as_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* v_fvars_300_, lean_object* v_e_301_, lean_object* v_deps_302_){
_start:
{
lean_object* v_d_304_; lean_object* v_b_305_; 
switch(lean_obj_tag(v_e_301_))
{
case 5:
{
lean_object* v_fn_309_; lean_object* v_arg_310_; uint8_t v___x_311_; 
v_fn_309_ = lean_ctor_get(v_e_301_, 0);
v_arg_310_ = lean_ctor_get(v_e_301_, 1);
v___x_311_ = l_Lean_Expr_hasFVar(v_e_301_);
if (v___x_311_ == 0)
{
return v_deps_302_;
}
else
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_300_, v_fn_309_, v_deps_302_);
v_e_301_ = v_arg_310_;
v_deps_302_ = v___x_312_;
goto _start;
}
}
case 7:
{
lean_object* v_binderType_314_; lean_object* v_body_315_; 
v_binderType_314_ = lean_ctor_get(v_e_301_, 1);
v_body_315_ = lean_ctor_get(v_e_301_, 2);
v_d_304_ = v_binderType_314_;
v_b_305_ = v_body_315_;
goto v___jp_303_;
}
case 6:
{
lean_object* v_binderType_316_; lean_object* v_body_317_; 
v_binderType_316_ = lean_ctor_get(v_e_301_, 1);
v_body_317_ = lean_ctor_get(v_e_301_, 2);
v_d_304_ = v_binderType_316_;
v_b_305_ = v_body_317_;
goto v___jp_303_;
}
case 8:
{
lean_object* v_type_318_; lean_object* v_value_319_; lean_object* v_body_320_; uint8_t v___x_321_; 
v_type_318_ = lean_ctor_get(v_e_301_, 1);
v_value_319_ = lean_ctor_get(v_e_301_, 2);
v_body_320_ = lean_ctor_get(v_e_301_, 3);
v___x_321_ = l_Lean_Expr_hasFVar(v_e_301_);
if (v___x_321_ == 0)
{
return v_deps_302_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_300_, v_type_318_, v_deps_302_);
v___x_323_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_300_, v_value_319_, v___x_322_);
v_e_301_ = v_body_320_;
v_deps_302_ = v___x_323_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_325_; 
v_struct_325_ = lean_ctor_get(v_e_301_, 2);
v_e_301_ = v_struct_325_;
goto _start;
}
case 10:
{
lean_object* v_expr_327_; 
v_expr_327_ = lean_ctor_get(v_e_301_, 1);
v_e_301_ = v_expr_327_;
goto _start;
}
case 1:
{
lean_object* v___x_329_; 
v___x_329_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_300_, v_e_301_);
if (lean_obj_tag(v___x_329_) == 0)
{
return v_deps_302_;
}
else
{
lean_object* v_val_330_; uint8_t v___x_331_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_deps_302_, v_val_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_array_push(v_deps_302_, v_val_330_);
return v___x_332_;
}
else
{
lean_dec(v_val_330_);
return v_deps_302_;
}
}
}
default: 
{
return v_deps_302_;
}
}
v___jp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_Expr_hasFVar(v_e_301_);
if (v___x_306_ == 0)
{
return v_deps_302_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_300_, v_d_304_, v_deps_302_);
v_e_301_ = v_b_305_;
v_deps_302_ = v___x_307_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* v_fvars_333_, lean_object* v_e_334_, lean_object* v_deps_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_333_, v_e_334_, v_deps_335_);
lean_dec_ref(v_e_334_);
lean_dec_ref(v_fvars_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(lean_object* v_hi_337_, lean_object* v_pivot_338_, lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_k_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_nat_dec_lt(v_k_341_, v_hi_337_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_k_341_);
v___x_343_ = lean_array_fswap(v_as_339_, v_i_340_, v_hi_337_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_i_340_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_array_fget_borrowed(v_as_339_, v_k_341_);
v___x_346_ = lean_nat_dec_lt(v___x_345_, v_pivot_338_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_k_341_, v___x_347_);
lean_dec(v_k_341_);
v_k_341_ = v___x_348_;
goto _start;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_array_fswap(v_as_339_, v_i_340_, v_k_341_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_340_, v___x_351_);
lean_dec(v_i_340_);
v___x_353_ = lean_nat_add(v_k_341_, v___x_351_);
lean_dec(v_k_341_);
v_as_339_ = v___x_350_;
v_i_340_ = v___x_352_;
v_k_341_ = v___x_353_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_355_, lean_object* v_pivot_356_, lean_object* v_as_357_, lean_object* v_i_358_, lean_object* v_k_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_355_, v_pivot_356_, v_as_357_, v_i_358_, v_k_359_);
lean_dec(v_pivot_356_);
lean_dec(v_hi_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* v_n_361_, lean_object* v_as_362_, lean_object* v_lo_363_, lean_object* v_hi_364_){
_start:
{
lean_object* v___y_366_; uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v_lo_363_, v_hi_364_);
if (v___x_376_ == 0)
{
lean_dec(v_lo_363_);
return v_as_362_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_mid_379_; lean_object* v___y_381_; lean_object* v___y_387_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_377_ = lean_nat_add(v_lo_363_, v_hi_364_);
v___x_378_ = lean_unsigned_to_nat(1u);
v_mid_379_ = lean_nat_shiftr(v___x_377_, v___x_378_);
lean_dec(v___x_377_);
v___x_392_ = lean_array_fget_borrowed(v_as_362_, v_mid_379_);
v___x_393_ = lean_array_fget_borrowed(v_as_362_, v_lo_363_);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
v___y_387_ = v_as_362_;
goto v___jp_386_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_array_fswap(v_as_362_, v_lo_363_, v_mid_379_);
v___y_387_ = v___x_395_;
goto v___jp_386_;
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_array_fget_borrowed(v___y_381_, v_mid_379_);
v___x_383_ = lean_array_fget_borrowed(v___y_381_, v_hi_364_);
v___x_384_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v_mid_379_);
v___y_366_ = v___y_381_;
goto v___jp_365_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_array_fswap(v___y_381_, v_mid_379_, v_hi_364_);
lean_dec(v_mid_379_);
v___y_366_ = v___x_385_;
goto v___jp_365_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_array_fget_borrowed(v___y_387_, v_hi_364_);
v___x_389_ = lean_array_fget_borrowed(v___y_387_, v_lo_363_);
v___x_390_ = lean_nat_dec_lt(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
v___y_381_ = v___y_387_;
goto v___jp_380_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_array_fswap(v___y_387_, v_lo_363_, v_hi_364_);
v___y_381_ = v___x_391_;
goto v___jp_380_;
}
}
}
v___jp_365_:
{
lean_object* v_pivot_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; uint8_t v___x_371_; 
v_pivot_367_ = lean_array_fget(v___y_366_, v_hi_364_);
lean_inc_n(v_lo_363_, 2);
v___x_368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_364_, v_pivot_367_, v___y_366_, v_lo_363_, v_lo_363_);
lean_dec(v_pivot_367_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_nat_dec_le(v_hi_364_, v_fst_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_361_, v_snd_370_, v_lo_363_, v_fst_369_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_fst_369_, v___x_373_);
lean_dec(v_fst_369_);
v_as_362_ = v___x_372_;
v_lo_363_ = v___x_374_;
goto _start;
}
else
{
lean_dec(v_fst_369_);
lean_dec(v_lo_363_);
return v_snd_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* v_n_396_, lean_object* v_as_397_, lean_object* v_lo_398_, lean_object* v_hi_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_396_, v_as_397_, v_lo_398_, v_hi_399_);
lean_dec(v_hi_399_);
lean_dec(v_n_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* v_fvars_403_, lean_object* v_e_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_deps_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0));
v_deps_407_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(v_fvars_403_, v_e_404_, v___x_406_);
v___x_408_ = lean_array_get_size(v_deps_407_);
v___x_409_ = lean_nat_dec_eq(v___x_408_, v___x_405_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___y_413_; uint8_t v___x_417_; 
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_sub(v___x_408_, v___x_410_);
v___x_417_ = lean_nat_dec_le(v___x_405_, v___x_411_);
if (v___x_417_ == 0)
{
lean_inc(v___x_411_);
v___y_413_ = v___x_411_;
goto v___jp_412_;
}
else
{
v___y_413_ = v___x_405_;
goto v___jp_412_;
}
v___jp_412_:
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_le(v___y_413_, v___x_411_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v___x_411_);
lean_inc(v___y_413_);
v___x_415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_408_, v_deps_407_, v___y_413_, v___y_413_);
lean_dec(v___y_413_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_408_, v_deps_407_, v___y_413_, v___x_411_);
lean_dec(v___x_411_);
return v___x_416_;
}
}
}
else
{
return v_deps_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* v_fvars_418_, lean_object* v_e_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_418_, v_e_419_);
lean_dec_ref(v_e_419_);
lean_dec_ref(v_fvars_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* v_n_421_, lean_object* v_as_422_, lean_object* v_lo_423_, lean_object* v_hi_424_, lean_object* v_w_425_, lean_object* v_hlo_426_, lean_object* v_hhi_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_421_, v_as_422_, v_lo_423_, v_hi_424_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* v_n_429_, lean_object* v_as_430_, lean_object* v_lo_431_, lean_object* v_hi_432_, lean_object* v_w_433_, lean_object* v_hlo_434_, lean_object* v_hhi_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_429_, v_as_430_, v_lo_431_, v_hi_432_, v_w_433_, v_hlo_434_, v_hhi_435_);
lean_dec(v_hi_432_);
lean_dec(v_n_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(lean_object* v_n_437_, lean_object* v_lo_438_, lean_object* v_hi_439_, lean_object* v_hhi_440_, lean_object* v_pivot_441_, lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_k_444_, lean_object* v_ilo_445_, lean_object* v_ik_446_, lean_object* v_w_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_439_, v_pivot_441_, v_as_442_, v_i_443_, v_k_444_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(lean_object* v_n_449_, lean_object* v_lo_450_, lean_object* v_hi_451_, lean_object* v_hhi_452_, lean_object* v_pivot_453_, lean_object* v_as_454_, lean_object* v_i_455_, lean_object* v_k_456_, lean_object* v_ilo_457_, lean_object* v_ik_458_, lean_object* v_w_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_449_, v_lo_450_, v_hi_451_, v_hhi_452_, v_pivot_453_, v_as_454_, v_i_455_, v_k_456_, v_ilo_457_, v_ik_458_, v_w_459_);
lean_dec(v_pivot_453_);
lean_dec(v_hi_451_);
lean_dec(v_lo_450_);
lean_dec(v_n_449_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* v_backDeps_461_, size_t v_sz_462_, size_t v_i_463_, lean_object* v_bs_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_lt(v_i_463_, v_sz_462_);
if (v___x_465_ == 0)
{
return v_bs_464_;
}
else
{
lean_object* v_v_466_; uint8_t v_binderInfo_467_; uint8_t v_hasFwdDeps_468_; lean_object* v_backDeps_469_; uint8_t v_isProp_470_; uint8_t v_isDecInst_471_; uint8_t v_isInstance_472_; uint8_t v_higherOrderOutParam_473_; uint8_t v_dependsOnHigherOrderOutParam_474_; lean_object* v___x_475_; lean_object* v_bs_x27_476_; lean_object* v___y_478_; 
v_v_466_ = lean_array_uget(v_bs_464_, v_i_463_);
v_binderInfo_467_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1);
v_hasFwdDeps_468_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 1);
v_backDeps_469_ = lean_ctor_get(v_v_466_, 0);
v_isProp_470_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 2);
v_isDecInst_471_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 3);
v_isInstance_472_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 4);
v_higherOrderOutParam_473_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 5);
v_dependsOnHigherOrderOutParam_474_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*1 + 6);
v___x_475_ = lean_unsigned_to_nat(0u);
v_bs_x27_476_ = lean_array_uset(v_bs_464_, v_i_463_, v___x_475_);
if (v_hasFwdDeps_468_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_usize_to_nat(v_i_463_);
v___x_484_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_461_, v___x_483_);
lean_dec(v___x_483_);
if (v___x_484_ == 0)
{
v___y_478_ = v_v_466_;
goto v___jp_477_;
}
else
{
lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_inc_ref(v_backDeps_469_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_v_466_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_v_466_, 0);
lean_dec(v_unused_492_);
v___x_486_ = v_v_466_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_v_466_);
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
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_backDeps_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1, v_binderInfo_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1 + 2, v_isProp_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1 + 3, v_isDecInst_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1 + 4, v_isInstance_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1 + 5, v_higherOrderOutParam_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_474_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1 + 1, v___x_484_);
v___y_478_ = v___x_489_;
goto v___jp_477_;
}
}
}
}
else
{
v___y_478_ = v_v_466_;
goto v___jp_477_;
}
v___jp_477_:
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_add(v_i_463_, v___x_479_);
v___x_481_ = lean_array_uset(v_bs_x27_476_, v_i_463_, v___y_478_);
v_i_463_ = v___x_480_;
v_bs_464_ = v___x_481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* v_backDeps_493_, lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_bs_496_){
_start:
{
size_t v_sz_boxed_497_; size_t v_i_boxed_498_; lean_object* v_res_499_; 
v_sz_boxed_497_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_493_, v_sz_boxed_497_, v_i_boxed_498_, v_bs_496_);
lean_dec_ref(v_backDeps_493_);
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
size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_sz_505_ = lean_array_size(v_pinfo_500_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_501_, v_sz_505_, v___x_506_, v_pinfo_500_);
return v___x_507_;
}
else
{
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
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* v_backDeps_511_, lean_object* v_as_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_bs_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_511_, v_sz_513_, v_i_514_, v_bs_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* v_backDeps_517_, lean_object* v_as_518_, lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_517_, v_as_518_, v_sz_boxed_522_, v_i_boxed_523_, v_bs_521_);
lean_dec_ref(v_as_518_);
lean_dec_ref(v_backDeps_517_);
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
lean_object* v___f_613_; lean_object* v___x_8499__overap_614_; lean_object* v___x_615_; 
v___f_613_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_8499__overap_614_ = lean_panic_fn_borrowed(v___f_613_, v_msg_607_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
v___x_615_ = lean_apply_5(v___x_8499__overap_614_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, lean_box(0));
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(lean_object* v_upperBound_690_, lean_object* v_val_691_, lean_object* v___x_692_, lean_object* v_fvars_693_, lean_object* v_next_694_, lean_object* v_upperBound_695_, lean_object* v_a_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_a_704_; uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_lt(v_a_696_, v_upperBound_690_);
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
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_775_; 
v_fst_710_ = lean_ctor_get(v_b_697_, 0);
v_snd_711_ = lean_ctor_get(v_b_697_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_b_697_);
if (v_isSharedCheck_775_ == 0)
{
v___x_713_ = v_b_697_;
v_isShared_714_ = v_isSharedCheck_775_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_b_697_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_775_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
uint8_t v___x_715_; 
v___x_715_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_691_, v_a_696_);
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
v___x_719_ = lean_array_fget_borrowed(v___x_692_, v_a_696_);
v___x_720_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_693_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_nat_dec_lt(v_next_694_, v_upperBound_695_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___x_719_);
v___x_723_ = lean_infer_type(v___x_719_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_725_ = lean_whnf(v_a_724_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___y_728_; uint8_t v___x_734_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_734_ = l_Lean_Expr_isForall(v_a_726_);
lean_dec(v_a_726_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_fst_710_);
lean_ctor_set(v___x_735_, 1, v_snd_711_);
v_a_704_ = v___x_735_;
goto v___jp_703_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_fst_710_);
v___x_737_ = lean_nat_dec_lt(v_val_721_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_val_721_);
v___y_728_ = v_fst_710_;
goto v___jp_727_;
}
else
{
lean_object* v_v_738_; uint8_t v_binderInfo_739_; uint8_t v_hasFwdDeps_740_; lean_object* v_backDeps_741_; uint8_t v_isProp_742_; uint8_t v_isDecInst_743_; uint8_t v_isInstance_744_; uint8_t v_dependsOnHigherOrderOutParam_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_755_; 
v_v_738_ = lean_array_fget(v_fst_710_, v_val_721_);
v_binderInfo_739_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1);
v_hasFwdDeps_740_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1 + 1);
v_backDeps_741_ = lean_ctor_get(v_v_738_, 0);
v_isProp_742_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1 + 2);
v_isDecInst_743_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1 + 3);
v_isInstance_744_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1 + 4);
v_dependsOnHigherOrderOutParam_745_ = lean_ctor_get_uint8(v_v_738_, sizeof(void*)*1 + 6);
v_isSharedCheck_755_ = !lean_is_exclusive(v_v_738_);
if (v_isSharedCheck_755_ == 0)
{
v___x_747_ = v_v_738_;
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_backDeps_741_);
lean_dec(v_v_738_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v_xs_x27_750_; lean_object* v___x_752_; 
v___x_749_ = lean_box(0);
v_xs_x27_750_ = lean_array_fset(v_fst_710_, v_val_721_, v___x_749_);
if (v_isShared_748_ == 0)
{
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_backDeps_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1, v_binderInfo_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1 + 1, v_hasFwdDeps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1 + 2, v_isProp_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1 + 3, v_isDecInst_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1 + 4, v_isInstance_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*1 + 6, v_dependsOnHigherOrderOutParam_745_);
v___x_752_ = v_reuseFailAlloc_754_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*1 + 5, v___x_722_);
v___x_753_ = lean_array_fset(v_xs_x27_750_, v_val_721_, v___x_752_);
lean_dec(v_val_721_);
v___y_728_ = v___x_753_;
goto v___jp_727_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = l_Lean_Expr_fvarId_x21(v___x_719_);
v___x_730_ = l_Lean_FVarIdSet_insert(v_snd_711_, v___x_729_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_730_);
lean_ctor_set(v___x_713_, 0, v___y_728_);
v___x_732_ = v___x_713_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___y_728_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v_a_704_ = v___x_732_;
goto v___jp_703_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_dec(v_a_696_);
v_a_756_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_725_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_725_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_val_721_);
lean_del_object(v___x_713_);
lean_dec(v_snd_711_);
lean_dec(v_fst_710_);
lean_dec(v_a_696_);
v_a_764_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_723_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_723_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v___x_720_);
if (v_isShared_714_ == 0)
{
v___x_773_ = v___x_713_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fst_710_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_711_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v_a_704_ = v___x_773_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(lean_object* v_upperBound_776_, lean_object* v_val_777_, lean_object* v___x_778_, lean_object* v_fvars_779_, lean_object* v_next_780_, lean_object* v_upperBound_781_, lean_object* v_a_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_776_, v_val_777_, v___x_778_, v_fvars_779_, v_next_780_, v_upperBound_781_, v_a_782_, v_b_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v_upperBound_781_);
lean_dec(v_next_780_);
lean_dec_ref(v_fvars_779_);
lean_dec_ref(v___x_778_);
lean_dec_ref(v_val_777_);
lean_dec(v_upperBound_776_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(lean_object* v_x_793_, lean_object* v_type_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1));
v___x_801_ = l_Lean_Expr_isAppOf(v_type_794_, v___x_800_);
v___x_802_ = lean_box(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(lean_object* v_x_804_, lean_object* v_type_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_804_, v_type_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v_type_805_);
lean_dec_ref(v_x_804_);
return v_res_811_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* v_k_812_, lean_object* v_t_813_){
_start:
{
if (lean_obj_tag(v_t_813_) == 0)
{
lean_object* v_k_814_; lean_object* v_l_815_; lean_object* v_r_816_; uint8_t v___x_817_; 
v_k_814_ = lean_ctor_get(v_t_813_, 1);
v_l_815_ = lean_ctor_get(v_t_813_, 3);
v_r_816_ = lean_ctor_get(v_t_813_, 4);
v___x_817_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_812_, v_k_814_);
switch(v___x_817_)
{
case 0:
{
v_t_813_ = v_l_815_;
goto _start;
}
case 1:
{
uint8_t v___x_819_; 
v___x_819_ = 1;
return v___x_819_;
}
default: 
{
v_t_813_ = v_r_816_;
goto _start;
}
}
}
else
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* v_k_822_, lean_object* v_t_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_822_, v_t_823_);
lean_dec(v_t_823_);
lean_dec(v_k_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(lean_object* v_snd_826_, lean_object* v_e_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_Expr_isFVar(v_e_827_);
if (v___x_828_ == 0)
{
return v___x_828_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_Expr_fvarId_x21(v_e_827_);
v___x_830_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_829_, v_snd_826_);
lean_dec(v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(lean_object* v_snd_831_, lean_object* v_e_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_831_, v_e_832_);
lean_dec_ref(v_e_832_);
lean_dec(v_snd_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v_dummy_837_; 
v___x_836_ = lean_box(0);
v_dummy_837_ = l_Lean_Expr_sort___override(v___x_836_);
return v_dummy_837_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_841_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_842_ = lean_unsigned_to_nat(47u);
v___x_843_ = lean_unsigned_to_nat(121u);
v___x_844_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3));
v___x_845_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2));
v___x_846_ = l_mkPanicMessageWithDecl(v___x_845_, v___x_844_, v___x_843_, v___x_842_, v___x_841_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(lean_object* v_upperBound_847_, lean_object* v_fvars_848_, lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_a_857_; uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_lt(v_a_849_, v_upperBound_847_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec(v_a_849_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_b_850_);
return v___x_862_;
}
else
{
lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_984_; 
v_fst_863_ = lean_ctor_get(v_b_850_, 0);
v_snd_864_ = lean_ctor_get(v_b_850_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_b_850_);
if (v_isSharedCheck_984_ == 0)
{
v___x_866_ = v_b_850_;
v_isShared_867_ = v_isSharedCheck_984_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_b_850_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_984_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___f_868_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0));
lean_inc(v_snd_864_);
v___f_869_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_869_, 0, v_snd_864_);
v___x_870_ = lean_array_fget_borrowed(v_fvars_848_, v_a_849_);
v___x_871_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_870_, v___y_851_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___y_876_; uint8_t v___y_877_; uint8_t v___y_878_; uint8_t v___y_958_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_LocalDecl_type(v_a_872_);
v___x_874_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_848_, v___x_873_);
if (lean_obj_tag(v_snd_864_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_find_expr(v___f_869_, v___x_873_);
lean_dec_ref(v___f_869_);
if (lean_obj_tag(v___x_973_) == 0)
{
uint8_t v___x_974_; 
v___x_974_ = 0;
v___y_958_ = v___x_974_;
goto v___jp_957_;
}
else
{
lean_dec_ref_known(v___x_973_, 1);
v___y_958_ = v___x_861_;
goto v___jp_957_;
}
}
else
{
uint8_t v___x_975_; 
lean_dec_ref(v___f_869_);
v___x_975_ = 0;
v___y_958_ = v___x_975_;
goto v___jp_957_;
}
v___jp_875_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_863_, v___x_874_);
lean_inc_ref(v___x_873_);
v___x_880_ = l_Lean_Meta_isProp(v___x_873_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = 0;
lean_inc_ref(v___x_873_);
v___x_883_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_873_, v___f_868_, v___x_882_, v___x_882_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; uint8_t v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_LocalDecl_binderInfo(v_a_872_);
lean_dec(v_a_872_);
v___x_886_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_886_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 1, v___x_882_);
v___x_887_ = lean_unbox(v_a_881_);
lean_dec(v_a_881_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 2, v___x_887_);
v___x_888_ = lean_unbox(v_a_884_);
lean_dec(v_a_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 3, v___x_888_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 4, v___y_878_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 5, v___x_882_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1 + 6, v___y_877_);
v___x_889_ = lean_array_push(v___x_879_, v___x_886_);
if (v___y_878_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v___y_876_);
lean_dec_ref(v___x_873_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_889_);
v___x_891_ = v___x_866_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_864_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_857_ = v___x_891_;
goto v___jp_856_;
}
}
else
{
if (lean_obj_tag(v___y_876_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; lean_object* v_env_895_; lean_object* v___x_896_; 
v_val_893_ = lean_ctor_get(v___y_876_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v___y_876_, 1);
v___x_894_ = lean_st_ref_get(v___y_854_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_894_);
v___x_896_ = l_Lean_getOutParamPositions_x3f(v_env_895_, v_val_893_);
lean_dec(v_val_893_);
if (lean_obj_tag(v___x_896_) == 1)
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_val_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_array_get_size(v_val_897_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_nat_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v_dummy_901_; lean_object* v_nargs_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_dummy_901_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
v_nargs_902_ = l_Lean_Expr_getAppNumArgs(v___x_873_);
lean_inc(v_nargs_902_);
v___x_903_ = lean_mk_array(v_nargs_902_, v_dummy_901_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_sub(v_nargs_902_, v___x_904_);
lean_dec(v_nargs_902_);
v___x_906_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_873_, v___x_903_, v___x_905_);
v___x_907_ = lean_array_get_size(v___x_906_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_889_);
v___x_909_ = v___x_866_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_snd_864_);
v___x_909_ = v_reuseFailAlloc_921_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; 
v___x_910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_907_, v_val_897_, v___x_906_, v_fvars_848_, v_a_849_, v_upperBound_847_, v___x_899_, v___x_909_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec_ref(v___x_906_);
lean_dec(v_val_897_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v_fst_912_ = lean_ctor_get(v_a_911_, 0);
v_snd_913_ = lean_ctor_get(v_a_911_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_911_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v_a_911_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snd_913_);
lean_inc(v_fst_912_);
lean_dec(v_a_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_912_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_snd_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v_a_857_ = v___x_918_;
goto v___jp_856_;
}
}
}
else
{
lean_dec(v_a_849_);
return v___x_910_;
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v_val_897_);
lean_dec_ref(v___x_873_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_889_);
v___x_923_ = v___x_866_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_864_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v_a_857_ = v___x_923_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v___x_926_; 
lean_dec(v___x_896_);
lean_dec_ref(v___x_873_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_889_);
v___x_926_ = v___x_866_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_864_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_a_857_ = v___x_926_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v___y_876_);
lean_dec_ref(v___x_873_);
v___x_928_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
v___x_929_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_928_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_931_; 
lean_dec_ref_known(v___x_929_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_889_);
v___x_931_ = v___x_866_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_snd_864_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
v_a_857_ = v___x_931_;
goto v___jp_856_;
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___x_889_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_a_849_);
v_a_933_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_881_);
lean_dec_ref(v___x_879_);
lean_dec(v___y_876_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec(v_a_872_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_a_849_);
v_a_941_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_883_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_883_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___x_879_);
lean_dec(v___y_876_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec(v_a_872_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_a_849_);
v_a_949_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_880_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_880_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
v___jp_957_:
{
lean_object* v___x_959_; 
lean_inc_ref(v___x_873_);
v___x_959_ = l_Lean_Meta_isClass_x3f(v___x_873_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
if (lean_obj_tag(v_a_960_) == 0)
{
uint8_t v___x_961_; 
v___x_961_ = 0;
v___y_876_ = v_a_960_;
v___y_877_ = v___y_958_;
v___y_878_ = v___x_961_;
goto v___jp_875_;
}
else
{
uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = l_Lean_LocalDecl_binderInfo(v_a_872_);
v___x_963_ = l_Lean_BinderInfo_isExplicit(v___x_962_);
if (v___x_963_ == 0)
{
v___y_876_ = v_a_960_;
v___y_877_ = v___y_958_;
v___y_878_ = v___x_861_;
goto v___jp_875_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = 0;
v___y_876_ = v_a_960_;
v___y_877_ = v___y_958_;
v___y_878_ = v___x_964_;
goto v___jp_875_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_873_);
lean_dec(v_a_872_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec(v_a_849_);
v_a_965_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_959_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_959_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___f_869_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec(v_a_849_);
v_a_976_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_871_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_871_);
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
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_a_849_, v___x_858_);
lean_dec(v_a_849_);
v_a_849_ = v___x_859_;
v_b_850_ = v_a_857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(lean_object* v_upperBound_985_, lean_object* v_fvars_986_, lean_object* v_a_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_985_, v_fvars_986_, v_a_987_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_fvars_986_);
lean_dec(v_upperBound_985_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* v___x_997_, lean_object* v_fvars_998_, lean_object* v_type_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1005_ = lean_array_get_size(v_fvars_998_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0));
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_997_);
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_1005_, v_fvars_998_, v___x_1006_, v___x_1008_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1028_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1028_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1028_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_fst_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1026_; 
v_fst_1014_ = lean_ctor_get(v_a_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1010_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_a_1010_, 1);
lean_dec(v_unused_1027_);
v___x_1016_ = v_a_1010_;
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_fst_1014_);
lean_dec(v_a_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_998_, v_type_999_);
v___x_1019_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(v_fst_1014_, v___x_1018_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1018_);
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1018_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1021_);
v___x_1023_ = v___x_1012_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1009_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1009_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* v___x_1037_, lean_object* v_fvars_1038_, lean_object* v_type_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(v___x_1037_, v_fvars_1038_, v_type_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_type_1039_);
lean_dec_ref(v_fvars_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(lean_object* v_fn_1046_, lean_object* v_maxArgs_x3f_1047_, lean_object* v___f_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___y_1055_; lean_object* v___x_1072_; 
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___x_1072_ = lean_infer_type(v_fn_1046_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; uint8_t v_transparency_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; uint8_t v___x_1078_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = l_Lean_Meta_Context_config(v___y_1049_);
v_transparency_1075_ = lean_ctor_get_uint8(v___x_1074_, 9);
lean_dec_ref(v___x_1074_);
v___x_1076_ = 1;
v___x_1077_ = 0;
v___x_1078_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1075_, v___x_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1073_, v_maxArgs_x3f_1047_, v___f_1048_, v___x_1077_, v___x_1077_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
v___y_1055_ = v___x_1079_;
goto v___jp_1054_;
}
else
{
lean_object* v_keyedConfig_1080_; uint8_t v_trackZetaDelta_1081_; lean_object* v_zetaDeltaSet_1082_; lean_object* v_lctx_1083_; lean_object* v_localInstances_1084_; lean_object* v_defEqCtx_x3f_1085_; lean_object* v_synthPendingDepth_1086_; lean_object* v_customCanUnfoldPredicate_x3f_1087_; uint8_t v_univApprox_1088_; uint8_t v_inTypeClassResolution_1089_; uint8_t v_cacheInferType_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_keyedConfig_1080_ = lean_ctor_get(v___y_1049_, 0);
v_trackZetaDelta_1081_ = lean_ctor_get_uint8(v___y_1049_, sizeof(void*)*7);
v_zetaDeltaSet_1082_ = lean_ctor_get(v___y_1049_, 1);
v_lctx_1083_ = lean_ctor_get(v___y_1049_, 2);
v_localInstances_1084_ = lean_ctor_get(v___y_1049_, 3);
v_defEqCtx_x3f_1085_ = lean_ctor_get(v___y_1049_, 4);
v_synthPendingDepth_1086_ = lean_ctor_get(v___y_1049_, 5);
v_customCanUnfoldPredicate_x3f_1087_ = lean_ctor_get(v___y_1049_, 6);
v_univApprox_1088_ = lean_ctor_get_uint8(v___y_1049_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1089_ = lean_ctor_get_uint8(v___y_1049_, sizeof(void*)*7 + 2);
v_cacheInferType_1090_ = lean_ctor_get_uint8(v___y_1049_, sizeof(void*)*7 + 3);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___y_1049_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v___y_1049_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1087_);
lean_inc(v_synthPendingDepth_1086_);
lean_inc(v_defEqCtx_x3f_1085_);
lean_inc(v_localInstances_1084_);
lean_inc(v_lctx_1083_);
lean_inc(v_zetaDeltaSet_1082_);
lean_inc(v_keyedConfig_1080_);
lean_dec(v___y_1049_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1076_, v_keyedConfig_1080_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_zetaDeltaSet_1082_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_lctx_1083_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_localInstances_1084_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_defEqCtx_x3f_1085_);
lean_ctor_set(v_reuseFailAlloc_1098_, 5, v_synthPendingDepth_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 6, v_customCanUnfoldPredicate_x3f_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*7, v_trackZetaDelta_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*7 + 1, v_univApprox_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*7 + 3, v_cacheInferType_1090_);
v___x_1096_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_1073_, v_maxArgs_x3f_1047_, v___f_1048_, v___x_1077_, v___x_1077_, v___x_1096_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___x_1096_);
v___y_1055_ = v___x_1097_;
goto v___jp_1054_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___f_1048_);
lean_dec(v_maxArgs_x3f_1047_);
v_a_1100_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1072_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1072_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_1054_:
{
if (lean_obj_tag(v___y_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___y_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___y_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___y_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___y_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___y_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___y_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(lean_object* v_fn_1108_, lean_object* v_maxArgs_x3f_1109_, lean_object* v___f_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1108_, v_maxArgs_x3f_1109_, v___f_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(lean_object* v_keys_1117_, lean_object* v_vals_1118_, lean_object* v_i_1119_, lean_object* v_k_1120_){
_start:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_array_get_size(v_keys_1117_);
v___x_1122_ = lean_nat_dec_lt(v_i_1119_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v_i_1119_);
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v_k_x27_1124_; uint8_t v___x_1125_; 
v_k_x27_1124_ = lean_array_fget_borrowed(v_keys_1117_, v_i_1119_);
v___x_1125_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_k_1120_, v_k_x27_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_i_1119_, v___x_1126_);
lean_dec(v_i_1119_);
v_i_1119_ = v___x_1127_;
goto _start;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_array_fget_borrowed(v_vals_1118_, v_i_1119_);
lean_dec(v_i_1119_);
lean_inc(v___x_1129_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(lean_object* v_keys_1131_, lean_object* v_vals_1132_, lean_object* v_i_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_1131_, v_vals_1132_, v_i_1133_, v_k_1134_);
lean_dec_ref(v_k_1134_);
lean_dec_ref(v_vals_1132_);
lean_dec_ref(v_keys_1131_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(lean_object* v_x_1136_, size_t v_x_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1136_) == 0)
{
lean_object* v_es_1139_; lean_object* v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v_j_1143_; lean_object* v___x_1144_; 
v_es_1139_ = lean_ctor_get(v_x_1136_, 0);
v___x_1140_ = lean_box(2);
v___x_1141_ = ((size_t)31ULL);
v___x_1142_ = lean_usize_land(v_x_1137_, v___x_1141_);
v_j_1143_ = lean_usize_to_nat(v___x_1142_);
v___x_1144_ = lean_array_get_borrowed(v___x_1140_, v_es_1139_, v_j_1143_);
lean_dec(v_j_1143_);
switch(lean_obj_tag(v___x_1144_))
{
case 0:
{
lean_object* v_key_1145_; lean_object* v_val_1146_; uint8_t v___x_1147_; 
v_key_1145_ = lean_ctor_get(v___x_1144_, 0);
v_val_1146_ = lean_ctor_get(v___x_1144_, 1);
v___x_1147_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1138_, v_key_1145_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_inc(v_val_1146_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_val_1146_);
return v___x_1149_;
}
}
case 1:
{
lean_object* v_node_1150_; size_t v___x_1151_; size_t v___x_1152_; 
v_node_1150_ = lean_ctor_get(v___x_1144_, 0);
v___x_1151_ = ((size_t)5ULL);
v___x_1152_ = lean_usize_shift_right(v_x_1137_, v___x_1151_);
v_x_1136_ = v_node_1150_;
v_x_1137_ = v___x_1152_;
goto _start;
}
default: 
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
}
}
else
{
lean_object* v_ks_1155_; lean_object* v_vs_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_ks_1155_ = lean_ctor_get(v_x_1136_, 0);
v_vs_1156_ = lean_ctor_get(v_x_1136_, 1);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_1155_, v_vs_1156_, v___x_1157_, v_x_1138_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
size_t v_x_11628__boxed_1162_; lean_object* v_res_1163_; 
v_x_11628__boxed_1162_ = lean_unbox_usize(v_x_1160_);
lean_dec(v_x_1160_);
v_res_1163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1159_, v_x_11628__boxed_1162_, v_x_1161_);
lean_dec_ref(v_x_1161_);
lean_dec_ref(v_x_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
uint64_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1165_);
v___x_1167_ = lean_uint64_to_usize(v___x_1166_);
v___x_1168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_1164_, v___x_1167_, v_x_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_1169_, v_x_1170_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v_ks_1176_; lean_object* v_vs_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1201_; 
v_ks_1176_ = lean_ctor_get(v_x_1172_, 0);
v_vs_1177_ = lean_ctor_get(v_x_1172_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1179_ = v_x_1172_;
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_vs_1177_);
lean_inc(v_ks_1176_);
lean_dec(v_x_1172_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_ks_1176_);
v___x_1182_ = lean_nat_dec_lt(v_x_1173_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
lean_dec(v_x_1173_);
v___x_1183_ = lean_array_push(v_ks_1176_, v_x_1174_);
v___x_1184_ = lean_array_push(v_vs_1177_, v_x_1175_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1184_);
lean_ctor_set(v___x_1179_, 0, v___x_1183_);
v___x_1186_ = v___x_1179_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
else
{
lean_object* v_k_x27_1188_; uint8_t v___x_1189_; 
v_k_x27_1188_ = lean_array_fget_borrowed(v_ks_1176_, v_x_1173_);
v___x_1189_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1174_, v_k_x27_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
if (v_isShared_1180_ == 0)
{
v___x_1191_ = v___x_1179_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_ks_1176_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_vs_1177_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v_x_1173_, v___x_1192_);
lean_dec(v_x_1173_);
v_x_1172_ = v___x_1191_;
v_x_1173_ = v___x_1193_;
goto _start;
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = lean_array_fset(v_ks_1176_, v_x_1173_, v_x_1174_);
v___x_1197_ = lean_array_fset(v_vs_1177_, v_x_1173_, v_x_1175_);
lean_dec(v_x_1173_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1197_);
lean_ctor_set(v___x_1179_, 0, v___x_1196_);
v___x_1199_ = v___x_1179_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(lean_object* v_n_1202_, lean_object* v_k_1203_, lean_object* v_v_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(v_n_1202_, v___x_1205_, v_k_1203_, v_v_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(lean_object* v_x_1208_, size_t v_x_1209_, size_t v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
lean_object* v_es_1213_; size_t v___x_1214_; size_t v___x_1215_; lean_object* v_j_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_es_1213_ = lean_ctor_get(v_x_1208_, 0);
v___x_1214_ = ((size_t)31ULL);
v___x_1215_ = lean_usize_land(v_x_1209_, v___x_1214_);
v_j_1216_ = lean_usize_to_nat(v___x_1215_);
v___x_1217_ = lean_array_get_size(v_es_1213_);
v___x_1218_ = lean_nat_dec_lt(v_j_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_dec(v_j_1216_);
lean_dec(v_x_1212_);
lean_dec_ref(v_x_1211_);
return v_x_1208_;
}
else
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1257_; 
lean_inc_ref(v_es_1213_);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_x_1208_, 0);
lean_dec(v_unused_1258_);
v___x_1220_ = v_x_1208_;
v_isShared_1221_ = v_isSharedCheck_1257_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v_x_1208_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1257_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_xs_x27_1224_; lean_object* v___y_1226_; 
v_v_1222_ = lean_array_fget(v_es_1213_, v_j_1216_);
v___x_1223_ = lean_box(0);
v_xs_x27_1224_ = lean_array_fset(v_es_1213_, v_j_1216_, v___x_1223_);
switch(lean_obj_tag(v_v_1222_))
{
case 0:
{
lean_object* v_key_1231_; lean_object* v_val_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1242_; 
v_key_1231_ = lean_ctor_get(v_v_1222_, 0);
v_val_1232_ = lean_ctor_get(v_v_1222_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_v_1222_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1234_ = v_v_1222_;
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_val_1232_);
lean_inc(v_key_1231_);
lean_dec(v_v_1222_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint8_t v___x_1236_; 
v___x_1236_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_1211_, v_key_1231_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_del_object(v___x_1234_);
v___x_1237_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1231_, v_val_1232_, v_x_1211_, v_x_1212_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___y_1226_ = v___x_1238_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1240_; 
lean_dec(v_val_1232_);
lean_dec(v_key_1231_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_x_1212_);
lean_ctor_set(v___x_1234_, 0, v_x_1211_);
v___x_1240_ = v___x_1234_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_x_1211_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_x_1212_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
v___y_1226_ = v___x_1240_;
goto v___jp_1225_;
}
}
}
}
case 1:
{
lean_object* v_node_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v_node_1243_ = lean_ctor_get(v_v_1222_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_v_1222_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1245_ = v_v_1222_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_node_1243_);
lean_dec(v_v_1222_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1247_ = ((size_t)5ULL);
v___x_1248_ = lean_usize_shift_right(v_x_1209_, v___x_1247_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_x_1210_, v___x_1249_);
v___x_1251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_1243_, v___x_1248_, v___x_1250_, v_x_1211_, v_x_1212_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1251_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v___y_1226_ = v___x_1253_;
goto v___jp_1225_;
}
}
}
default: 
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_x_1211_);
lean_ctor_set(v___x_1256_, 1, v_x_1212_);
v___y_1226_ = v___x_1256_;
goto v___jp_1225_;
}
}
v___jp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_array_fset(v_xs_x27_1224_, v_j_1216_, v___y_1226_);
lean_dec(v_j_1216_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1227_);
v___x_1229_ = v___x_1220_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
else
{
lean_object* v_ks_1259_; lean_object* v_vs_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1278_; 
v_ks_1259_ = lean_ctor_get(v_x_1208_, 0);
v_vs_1260_ = lean_ctor_get(v_x_1208_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1262_ = v_x_1208_;
v_isShared_1263_ = v_isSharedCheck_1278_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_vs_1260_);
lean_inc(v_ks_1259_);
lean_dec(v_x_1208_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1278_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_ks_1259_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_vs_1260_);
v___x_1265_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v_newNode_1266_; size_t v___x_1267_; uint8_t v___x_1268_; 
v_newNode_1266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_1265_, v_x_1211_, v_x_1212_);
v___x_1267_ = ((size_t)7ULL);
v___x_1268_ = lean_usize_dec_le(v___x_1267_, v_x_1210_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1266_);
v___x_1270_ = lean_unsigned_to_nat(4u);
v___x_1271_ = lean_nat_dec_lt(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
if (v___x_1271_ == 0)
{
lean_object* v_ks_1272_; lean_object* v_vs_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_ks_1272_ = lean_ctor_get(v_newNode_1266_, 0);
lean_inc_ref(v_ks_1272_);
v_vs_1273_ = lean_ctor_get(v_newNode_1266_, 1);
lean_inc_ref(v_vs_1273_);
lean_dec_ref(v_newNode_1266_);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_1210_, v_ks_1272_, v_vs_1273_, v___x_1274_, v___x_1275_);
lean_dec_ref(v_vs_1273_);
lean_dec_ref(v_ks_1272_);
return v___x_1276_;
}
else
{
return v_newNode_1266_;
}
}
else
{
return v_newNode_1266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(size_t v_depth_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_i_1282_, lean_object* v_entries_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_keys_1280_);
v___x_1285_ = lean_nat_dec_lt(v_i_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_i_1282_);
return v_entries_1283_;
}
else
{
lean_object* v_k_1286_; lean_object* v_v_1287_; uint64_t v___x_1288_; size_t v_h_1289_; size_t v___x_1290_; lean_object* v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v_h_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_k_1286_ = lean_array_fget_borrowed(v_keys_1280_, v_i_1282_);
v_v_1287_ = lean_array_fget_borrowed(v_vals_1281_, v_i_1282_);
v___x_1288_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_1286_);
v_h_1289_ = lean_uint64_to_usize(v___x_1288_);
v___x_1290_ = ((size_t)5ULL);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_sub(v_depth_1279_, v___x_1292_);
v___x_1294_ = lean_usize_mul(v___x_1290_, v___x_1293_);
v_h_1295_ = lean_usize_shift_right(v_h_1289_, v___x_1294_);
v___x_1296_ = lean_nat_add(v_i_1282_, v___x_1291_);
lean_dec(v_i_1282_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
v___x_1297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_1283_, v_h_1295_, v_depth_1279_, v_k_1286_, v_v_1287_);
v_i_1282_ = v___x_1296_;
v_entries_1283_ = v___x_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_depth_1299_, lean_object* v_keys_1300_, lean_object* v_vals_1301_, lean_object* v_i_1302_, lean_object* v_entries_1303_){
_start:
{
size_t v_depth_boxed_1304_; lean_object* v_res_1305_; 
v_depth_boxed_1304_ = lean_unbox_usize(v_depth_1299_);
lean_dec(v_depth_1299_);
v_res_1305_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_1304_, v_keys_1300_, v_vals_1301_, v_i_1302_, v_entries_1303_);
lean_dec_ref(v_vals_1301_);
lean_dec_ref(v_keys_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
size_t v_x_11763__boxed_1311_; size_t v_x_11764__boxed_1312_; lean_object* v_res_1313_; 
v_x_11763__boxed_1311_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_x_11764__boxed_1312_ = lean_unbox_usize(v_x_1308_);
lean_dec(v_x_1308_);
v_res_1313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1306_, v_x_11763__boxed_1311_, v_x_11764__boxed_1312_, v_x_1309_, v_x_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
uint64_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_1315_);
v___x_1318_ = lean_uint64_to_usize(v___x_1317_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_1314_, v___x_1318_, v___x_1319_, v_x_1315_, v_x_1316_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(lean_object* v_realizeMapRef_1324_, lean_object* v_env_1325_, lean_object* v_env_1326_, lean_object* v_forConst_1327_, lean_object* v_ctx_1328_, lean_object* v_realize_1329_, lean_object* v_opts_1330_, lean_object* v_key_1331_, lean_object* v_inst_1332_, lean_object* v_____r_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___y_1389_; lean_object* v___x_1394_; 
v___x_1335_ = lean_io_promise_new();
v___x_1336_ = lean_st_ref_take(v_realizeMapRef_1324_);
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1336_, v_inst_1332_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_obj_once(&l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1, &l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once, _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
v___y_1389_ = v___x_1395_;
goto v___jp_1388_;
}
else
{
lean_object* v_val_1396_; 
v_val_1396_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1396_);
lean_dec_ref_known(v___x_1394_, 1);
v___y_1389_ = v_val_1396_;
goto v___jp_1388_;
}
v___jp_1337_:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_st_ref_put(v_realizeMapRef_1324_, v_snd_1339_);
if (lean_obj_tag(v_fst_1338_) == 1)
{
lean_object* v_val_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v___x_1335_);
lean_dec_ref(v_opts_1330_);
lean_dec_ref(v_realize_1329_);
lean_dec_ref(v_ctx_1328_);
lean_dec(v_forConst_1327_);
lean_dec_ref(v_env_1326_);
lean_dec(v_env_1325_);
v_val_1341_ = lean_ctor_get(v_fst_1338_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_fst_1338_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v_fst_1338_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_val_1341_);
lean_dec(v_fst_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_task_get_own(v_val_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_base_1350_; lean_object* v_serverBaseExts_1351_; lean_object* v_checked_1352_; lean_object* v_asyncConstsMap_1353_; lean_object* v_asyncCtx_x3f_1354_; lean_object* v_localRealizationCtxMap_1355_; lean_object* v_allRealizations_1356_; uint8_t v_isExporting_1357_; uint8_t v_isRecordingDeps_1358_; lean_object* v_synthCacheRaw_x3f_1359_; lean_object* v_declChangeLog_1360_; lean_object* v_recordingConstGen_1361_; lean_object* v_constAddedGens_1362_; lean_object* v_constGen_1363_; lean_object* v_importRealizationCtx_x3f_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_fst_1338_);
v_base_1350_ = lean_ctor_get(v_env_1325_, 0);
lean_inc_ref(v_base_1350_);
v_serverBaseExts_1351_ = lean_ctor_get(v_env_1325_, 1);
lean_inc_ref(v_serverBaseExts_1351_);
v_checked_1352_ = lean_ctor_get(v_env_1325_, 2);
lean_inc_ref(v_checked_1352_);
v_asyncConstsMap_1353_ = lean_ctor_get(v_env_1325_, 3);
lean_inc_ref(v_asyncConstsMap_1353_);
v_asyncCtx_x3f_1354_ = lean_ctor_get(v_env_1325_, 4);
lean_inc(v_asyncCtx_x3f_1354_);
v_localRealizationCtxMap_1355_ = lean_ctor_get(v_env_1325_, 6);
lean_inc(v_localRealizationCtxMap_1355_);
v_allRealizations_1356_ = lean_ctor_get(v_env_1325_, 7);
lean_inc_ref(v_allRealizations_1356_);
v_isExporting_1357_ = lean_ctor_get_uint8(v_env_1325_, sizeof(void*)*13);
v_isRecordingDeps_1358_ = lean_ctor_get_uint8(v_env_1325_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_1359_ = lean_ctor_get(v_env_1325_, 8);
lean_inc(v_synthCacheRaw_x3f_1359_);
v_declChangeLog_1360_ = lean_ctor_get(v_env_1325_, 9);
lean_inc_ref(v_declChangeLog_1360_);
v_recordingConstGen_1361_ = lean_ctor_get(v_env_1325_, 10);
lean_inc(v_recordingConstGen_1361_);
v_constAddedGens_1362_ = lean_ctor_get(v_env_1325_, 11);
lean_inc_ref(v_constAddedGens_1362_);
v_constGen_1363_ = lean_ctor_get(v_env_1325_, 12);
lean_inc(v_constGen_1363_);
lean_dec(v_env_1325_);
v_importRealizationCtx_x3f_1364_ = lean_ctor_get(v_env_1326_, 5);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_env_1326_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1376_ = lean_ctor_get(v_env_1326_, 12);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_env_1326_, 11);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_env_1326_, 10);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_env_1326_, 9);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_env_1326_, 8);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_env_1326_, 7);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_env_1326_, 6);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_env_1326_, 4);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_env_1326_, 3);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_env_1326_, 2);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_env_1326_, 1);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_env_1326_, 0);
lean_dec(v_unused_1387_);
v___x_1366_ = v_env_1326_;
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_importRealizationCtx_x3f_1364_);
lean_dec(v_env_1326_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_1327_, v_ctx_1328_, v_localRealizationCtxMap_1355_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 12, v_constGen_1363_);
lean_ctor_set(v___x_1366_, 11, v_constAddedGens_1362_);
lean_ctor_set(v___x_1366_, 10, v_recordingConstGen_1361_);
lean_ctor_set(v___x_1366_, 9, v_declChangeLog_1360_);
lean_ctor_set(v___x_1366_, 8, v_synthCacheRaw_x3f_1359_);
lean_ctor_set(v___x_1366_, 7, v_allRealizations_1356_);
lean_ctor_set(v___x_1366_, 6, v___x_1368_);
lean_ctor_set(v___x_1366_, 4, v_asyncCtx_x3f_1354_);
lean_ctor_set(v___x_1366_, 3, v_asyncConstsMap_1353_);
lean_ctor_set(v___x_1366_, 2, v_checked_1352_);
lean_ctor_set(v___x_1366_, 1, v_serverBaseExts_1351_);
lean_ctor_set(v___x_1366_, 0, v_base_1350_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_base_1350_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_serverBaseExts_1351_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_checked_1352_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_asyncConstsMap_1353_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_asyncCtx_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v_importRealizationCtx_x3f_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 6, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 7, v_allRealizations_1356_);
lean_ctor_set(v_reuseFailAlloc_1374_, 8, v_synthCacheRaw_x3f_1359_);
lean_ctor_set(v_reuseFailAlloc_1374_, 9, v_declChangeLog_1360_);
lean_ctor_set(v_reuseFailAlloc_1374_, 10, v_recordingConstGen_1361_);
lean_ctor_set(v_reuseFailAlloc_1374_, 11, v_constAddedGens_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 12, v_constGen_1363_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*13, v_isExporting_1357_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*13 + 1, v_isRecordingDeps_1358_);
v___x_1371_ = lean_apply_3(v_realize_1329_, v___x_1370_, v_opts_1330_, lean_box(0));
lean_inc(v___x_1371_);
v___x_1372_ = lean_io_promise_resolve(v___x_1371_, v___x_1335_);
lean_dec(v___x_1335_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
return v___x_1373_;
}
}
}
}
v___jp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_1389_, v_key_1331_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = l_IO_Promise_result_x21___redArg(v___x_1335_);
v___x_1392_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_1389_, v_key_1331_, v___x_1391_);
v___x_1393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_1332_, v___x_1392_, v___x_1336_);
v_fst_1338_ = v___x_1390_;
v_snd_1339_ = v___x_1393_;
goto v___jp_1337_;
}
else
{
lean_dec_ref(v___y_1389_);
lean_dec(v_inst_1332_);
lean_dec_ref(v_key_1331_);
v_fst_1338_ = v___x_1390_;
v_snd_1339_ = v___x_1336_;
goto v___jp_1337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(lean_object* v_realizeMapRef_1397_, lean_object* v_env_1398_, lean_object* v_env_1399_, lean_object* v_forConst_1400_, lean_object* v_ctx_1401_, lean_object* v_realize_1402_, lean_object* v_opts_1403_, lean_object* v_key_1404_, lean_object* v_inst_1405_, lean_object* v_____r_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1397_, v_env_1398_, v_env_1399_, v_forConst_1400_, v_ctx_1401_, v_realize_1402_, v_opts_1403_, v_key_1404_, v_inst_1405_, v_____r_1406_);
lean_dec(v_realizeMapRef_1397_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(lean_object* v_inst_1415_, lean_object* v_env_1416_, lean_object* v_forConst_1417_, lean_object* v_key_1418_, lean_object* v_realize_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v_a_1423_; lean_object* v___y_1427_; lean_object* v_ctx_1430_; uint8_t v___x_1444_; 
v___x_1421_ = lean_io_get_num_heartbeats();
v___x_1444_ = l_Lean_Environment_isImportedConst(v_env_1416_, v_forConst_1417_);
if (v___x_1444_ == 0)
{
lean_object* v_localRealizationCtxMap_1445_; lean_object* v___x_1446_; 
v_localRealizationCtxMap_1445_ = lean_ctor_get(v_env_1416_, 6);
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_1445_, v_forConst_1417_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v___x_1421_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
lean_dec_ref(v_env_1416_);
v___x_1447_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0));
v___x_1448_ = 1;
v___x_1449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1415_, v___x_1448_);
v___x_1450_ = lean_string_append(v___x_1447_, v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1));
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
v___x_1453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_forConst_1417_, v___x_1448_);
v___x_1454_ = lean_string_append(v___x_1452_, v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2));
v___x_1456_ = lean_string_append(v___x_1454_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v_val_1459_; 
v_val_1459_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v___x_1446_, 1);
v_ctx_1430_ = v_val_1459_;
goto v___jp_1429_;
}
}
else
{
lean_object* v_importRealizationCtx_x3f_1460_; 
v_importRealizationCtx_x3f_1460_ = lean_ctor_get(v_env_1416_, 5);
if (lean_obj_tag(v_importRealizationCtx_x3f_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1421_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
lean_dec(v_forConst_1417_);
lean_dec_ref(v_env_1416_);
lean_dec(v_inst_1415_);
v___x_1461_ = ((lean_object*)(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4));
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
else
{
lean_object* v_val_1463_; 
v_val_1463_ = lean_ctor_get(v_importRealizationCtx_x3f_1460_, 0);
lean_inc(v_val_1463_);
v_ctx_1430_ = v_val_1463_;
goto v___jp_1429_;
}
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
v___jp_1429_:
{
lean_object* v_env_1431_; lean_object* v_opts_1432_; lean_object* v_realizeMapRef_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_env_1431_ = lean_ctor_get(v_ctx_1430_, 0);
lean_inc(v_env_1431_);
v_opts_1432_ = lean_ctor_get(v_ctx_1430_, 1);
lean_inc_ref(v_opts_1432_);
v_realizeMapRef_1433_ = lean_ctor_get(v_ctx_1430_, 2);
lean_inc(v_realizeMapRef_1433_);
v___x_1434_ = lean_st_ref_get(v_realizeMapRef_1433_);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1434_, v_inst_1415_);
lean_dec(v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v___x_1437_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_1436_, v_key_1418_);
lean_dec(v_val_1436_);
if (lean_obj_tag(v___x_1437_) == 1)
{
lean_object* v_val_1438_; lean_object* v___x_1439_; 
lean_dec(v_realizeMapRef_1433_);
lean_dec_ref(v_opts_1432_);
lean_dec(v_env_1431_);
lean_dec_ref(v_ctx_1430_);
lean_dec_ref(v_realize_1419_);
lean_dec_ref(v_key_1418_);
lean_dec(v_forConst_1417_);
lean_dec_ref(v_env_1416_);
lean_dec(v_inst_1415_);
v_val_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_val_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_task_get_own(v_val_1438_);
v_a_1423_ = v___x_1439_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1433_, v_env_1431_, v_env_1416_, v_forConst_1417_, v_ctx_1430_, v_realize_1419_, v_opts_1432_, v_key_1418_, v_inst_1415_, v___x_1440_);
lean_dec(v_realizeMapRef_1433_);
v___y_1427_ = v___x_1441_;
goto v___jp_1426_;
}
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec(v___x_1435_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_1433_, v_env_1431_, v_env_1416_, v_forConst_1417_, v_ctx_1430_, v_realize_1419_, v_opts_1432_, v_key_1418_, v_inst_1415_, v___x_1442_);
lean_dec(v_realizeMapRef_1433_);
v___y_1427_ = v___x_1443_;
goto v___jp_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(lean_object* v_inst_1464_, lean_object* v_env_1465_, lean_object* v_forConst_1466_, lean_object* v_key_1467_, lean_object* v_realize_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1464_, v_env_1465_, v_forConst_1466_, v_key_1467_, v_realize_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___f_1477_; lean_object* v___x_9953__overap_1478_; lean_object* v___x_1479_; 
v___f_1477_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0));
v___x_9953__overap_1478_ = lean_panic_fn_borrowed(v___f_1477_, v_msg_1471_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
v___x_1479_ = lean_apply_5(v___x_9953__overap_1478_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, lean_box(0));
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(lean_object* v_realize_1487_, lean_object* v_inst_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
v___x_1494_ = lean_apply_5(v_realize_1487_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, lean_box(0));
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_inst_1488_);
lean_ctor_set(v___x_1499_, 1, v_a_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_inst_1488_);
v_a_1504_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1494_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1494_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(lean_object* v_realize_1512_, lean_object* v_inst_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_1512_, v_inst_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = l_Lean_Options_empty;
v___x_1521_ = l_Lean_Core_getMaxHeartbeats(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_unsigned_to_nat(16u);
v___x_1524_ = lean_mk_array(v___x_1523_, v___x_1522_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
return v___x_1527_;
}
}
static uint16_t _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1528_; uint16_t v___x_1529_; 
v___x_1528_ = l_Lean_Options_empty;
v___x_1529_ = l_Lean_OptionFlags_ofOptions(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1533_ = lean_unsigned_to_nat(36u);
v___x_1534_ = lean_unsigned_to_nat(2851u);
v___x_1535_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5));
v___x_1536_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1537_ = l_mkPanicMessageWithDecl(v___x_1536_, v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4));
v___x_1539_ = lean_unsigned_to_nat(48u);
v___x_1540_ = lean_unsigned_to_nat(2842u);
v___x_1541_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5));
v___x_1542_ = ((lean_object*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4));
v___x_1543_ = l_mkPanicMessageWithDecl(v___x_1542_, v___x_1541_, v___x_1540_, v___x_1539_, v___x_1538_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_forConst_1546_, lean_object* v_key_1547_, lean_object* v_realize_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_env_1557_; uint8_t v___x_1558_; 
lean_inc(v_inst_1545_);
lean_inc_ref(v_realize_1548_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1554_, 0, v_realize_1548_);
lean_closure_set(v___f_1554_, 1, v_inst_1545_);
v___x_1555_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
v___x_1556_ = lean_st_ref_get(v_a_1552_);
v_env_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc_ref(v_env_1557_);
lean_dec(v___x_1556_);
v___x_1558_ = l_Lean_Environment_areRealizationsEnabledForConst(v_env_1557_, v_forConst_1546_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref(v_env_1557_);
lean_dec_ref(v___f_1554_);
lean_dec_ref(v_key_1547_);
lean_dec(v_forConst_1546_);
lean_dec(v_inst_1545_);
lean_dec(v_inst_1544_);
lean_inc(v_a_1552_);
lean_inc_ref(v_a_1551_);
lean_inc(v_a_1550_);
lean_inc_ref(v_a_1549_);
v___x_1559_ = lean_apply_5(v_realize_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, lean_box(0));
return v___x_1559_;
}
else
{
uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v_toCold_1562_; lean_object* v_ref_1563_; lean_object* v_fileName_1564_; lean_object* v_fileMap_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint16_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_realize_1548_);
v___x_1560_ = 0;
v___x_1561_ = lean_io_get_num_heartbeats();
v_toCold_1562_ = lean_ctor_get(v_a_1551_, 0);
v_ref_1563_ = lean_ctor_get(v_a_1551_, 2);
v_fileName_1564_ = lean_ctor_get(v_toCold_1562_, 0);
v_fileMap_1565_ = lean_ctor_get(v_toCold_1562_, 1);
v___x_1566_ = l_Lean_Options_empty;
v___x_1567_ = lean_unsigned_to_nat(1000u);
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
v___x_1571_ = l_Lean_firstFrontendMacroScope;
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
lean_inc_ref(v_fileMap_1565_);
lean_inc_ref(v_fileName_1564_);
v___x_1575_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1575_, 0, v_fileName_1564_);
lean_ctor_set(v___x_1575_, 1, v_fileMap_1565_);
lean_ctor_set(v___x_1575_, 2, v___x_1566_);
lean_ctor_set(v___x_1575_, 3, v___x_1567_);
lean_ctor_set(v___x_1575_, 4, v___x_1568_);
lean_ctor_set(v___x_1575_, 5, v___x_1569_);
lean_ctor_set(v___x_1575_, 6, v___x_1561_);
lean_ctor_set(v___x_1575_, 7, v___x_1570_);
lean_ctor_set(v___x_1575_, 8, v___x_1568_);
lean_ctor_set(v___x_1575_, 9, v___x_1571_);
lean_ctor_set(v___x_1575_, 10, v___x_1572_);
lean_ctor_set(v___x_1575_, 11, v___x_1574_);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_uint16_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3);
v___x_1578_ = 0;
v___x_1579_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1579_, 0, v___x_1575_);
lean_ctor_set(v___x_1579_, 1, v___x_1573_);
lean_ctor_set(v___x_1579_, 2, v___x_1576_);
lean_ctor_set_uint16(v___x_1579_, sizeof(void*)*3, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 2, v___x_1560_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 3, v___x_1578_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 4, v___x_1560_);
v___x_1580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed), 5, 2);
lean_closure_set(v___x_1580_, 0, v___f_1554_);
lean_closure_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_1544_, v_env_1557_, v_forConst_1546_, v_key_1547_, v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1633_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1633_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1633_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; 
v___x_1586_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1582_, v___x_1555_);
lean_dec(v_a_1582_);
if (lean_obj_tag(v___x_1586_) == 1)
{
lean_object* v_val_1587_; lean_object* v_res_x3f_1588_; lean_object* v_snap_x3f_1589_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v_snap_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; 
v_val_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v_res_x3f_1588_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_res_x3f_1588_);
v_snap_x3f_1589_ = lean_ctor_get(v_val_1587_, 1);
lean_inc(v_snap_x3f_1589_);
lean_dec(v_val_1587_);
if (lean_obj_tag(v_snap_x3f_1589_) == 1)
{
lean_object* v_val_1623_; lean_object* v___x_1624_; 
v_val_1623_ = lean_ctor_get(v_snap_x3f_1589_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_snap_x3f_1589_, 1);
v___x_1624_ = l_Lean_Syntax_getRange_x3f(v_ref_1563_, v___x_1560_);
if (lean_obj_tag(v___x_1624_) == 1)
{
lean_object* v_val_1625_; lean_object* v_start_1626_; lean_object* v_stop_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_val_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_start_1626_ = lean_ctor_get(v_val_1625_, 0);
lean_inc(v_start_1626_);
v_stop_1627_ = lean_ctor_get(v_val_1625_, 1);
lean_inc(v_stop_1627_);
lean_dec(v_val_1625_);
lean_inc_ref_n(v_fileMap_1565_, 2);
v___x_1628_ = l_Lean_FileMap_toPosition(v_fileMap_1565_, v_start_1626_);
lean_dec(v_start_1626_);
v___x_1629_ = l_Lean_FileMap_toPosition(v_fileMap_1565_, v_stop_1627_);
lean_dec(v_stop_1627_);
v___x_1630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(v_val_1623_, v___x_1628_, v___x_1629_);
v_snap_1608_ = v___x_1630_;
v___y_1609_ = v_a_1549_;
v___y_1610_ = v_a_1550_;
v___y_1611_ = v_a_1551_;
v___y_1612_ = v_a_1552_;
goto v___jp_1607_;
}
else
{
lean_dec(v___x_1624_);
v_snap_1608_ = v_val_1623_;
v___y_1609_ = v_a_1549_;
v___y_1610_ = v_a_1550_;
v___y_1611_ = v_a_1551_;
v___y_1612_ = v_a_1552_;
goto v___jp_1607_;
}
}
else
{
lean_dec(v_snap_x3f_1589_);
v___y_1591_ = v_a_1549_;
v___y_1592_ = v_a_1550_;
v___y_1593_ = v_a_1551_;
v___y_1594_ = v_a_1552_;
goto v___jp_1590_;
}
v___jp_1590_:
{
if (lean_obj_tag(v_res_x3f_1588_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; 
lean_dec(v_inst_1545_);
v_a_1595_ = lean_ctor_get(v_res_x3f_1588_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v_res_x3f_1588_, 1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
lean_ctor_set(v___x_1584_, 0, v_a_1595_);
v___x_1597_ = v___x_1584_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v_res_x3f_1588_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v_res_x3f_1588_, 1);
v___x_1600_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_a_1599_, v_inst_1545_);
lean_dec(v_inst_1545_);
lean_dec(v_a_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1584_);
v___x_1601_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
v___x_1602_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1601_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1602_;
}
else
{
lean_object* v_val_1603_; lean_object* v___x_1605_; 
v_val_1603_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v___x_1600_, 1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_val_1603_);
v___x_1605_ = v___x_1584_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_val_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
v___jp_1607_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1572_, v_snap_1608_);
v___x_1614_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1613_, v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref_known(v___x_1614_, 1);
v___y_1591_ = v___y_1609_;
v___y_1592_ = v___y_1610_;
v___y_1593_ = v___y_1611_;
v___y_1594_ = v___y_1612_;
goto v___jp_1590_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_res_x3f_1588_);
lean_del_object(v___x_1584_);
lean_dec(v_inst_1545_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v___x_1586_);
lean_del_object(v___x_1584_);
lean_dec(v_inst_1545_);
v___x_1631_ = lean_obj_once(&l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7, &l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7_once, _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__7);
v___x_1632_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_1631_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_inst_1545_);
v_a_1634_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1636_ = v___x_1581_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1581_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1638_ = lean_io_error_to_string(v_a_1634_);
v___x_1639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = l_Lean_MessageData_ofFormat(v___x_1639_);
lean_inc(v_ref_1563_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_ref_1563_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1641_);
v___x_1643_ = v___x_1636_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_forConst_1648_, lean_object* v_key_1649_, lean_object* v_realize_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_1646_, v_inst_1647_, v_forConst_1648_, v_key_1649_, v_realize_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_1657_, lean_object* v_vals_1658_, lean_object* v_i_1659_, lean_object* v_k_1660_){
_start:
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = lean_array_get_size(v_keys_1657_);
v___x_1662_ = lean_nat_dec_lt(v_i_1659_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_dec(v_i_1659_);
v___x_1663_ = lean_box(0);
return v___x_1663_;
}
else
{
lean_object* v_k_x27_1664_; uint8_t v___x_1665_; 
v_k_x27_1664_ = lean_array_fget_borrowed(v_keys_1657_, v_i_1659_);
v___x_1665_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_1660_, v_k_x27_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v_i_1659_, v___x_1666_);
lean_dec(v_i_1659_);
v_i_1659_ = v___x_1667_;
goto _start;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_array_fget_borrowed(v_vals_1658_, v_i_1659_);
lean_dec(v_i_1659_);
lean_inc(v___x_1669_);
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_1671_, lean_object* v_vals_1672_, lean_object* v_i_1673_, lean_object* v_k_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_1671_, v_vals_1672_, v_i_1673_, v_k_1674_);
lean_dec_ref(v_k_1674_);
lean_dec_ref(v_vals_1672_);
lean_dec_ref(v_keys_1671_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(lean_object* v_x_1676_, size_t v_x_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1676_) == 0)
{
lean_object* v_es_1679_; lean_object* v___x_1680_; size_t v___x_1681_; size_t v___x_1682_; lean_object* v_j_1683_; lean_object* v___x_1684_; 
v_es_1679_ = lean_ctor_get(v_x_1676_, 0);
v___x_1680_ = lean_box(2);
v___x_1681_ = ((size_t)31ULL);
v___x_1682_ = lean_usize_land(v_x_1677_, v___x_1681_);
v_j_1683_ = lean_usize_to_nat(v___x_1682_);
v___x_1684_ = lean_array_get_borrowed(v___x_1680_, v_es_1679_, v_j_1683_);
lean_dec(v_j_1683_);
switch(lean_obj_tag(v___x_1684_))
{
case 0:
{
lean_object* v_key_1685_; lean_object* v_val_1686_; uint8_t v___x_1687_; 
v_key_1685_ = lean_ctor_get(v___x_1684_, 0);
v_val_1686_ = lean_ctor_get(v___x_1684_, 1);
v___x_1687_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1678_, v_key_1685_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_box(0);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; 
lean_inc(v_val_1686_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_val_1686_);
return v___x_1689_;
}
}
case 1:
{
lean_object* v_node_1690_; size_t v___x_1691_; size_t v___x_1692_; 
v_node_1690_ = lean_ctor_get(v___x_1684_, 0);
v___x_1691_ = ((size_t)5ULL);
v___x_1692_ = lean_usize_shift_right(v_x_1677_, v___x_1691_);
v_x_1676_ = v_node_1690_;
v_x_1677_ = v___x_1692_;
goto _start;
}
default: 
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_box(0);
return v___x_1694_;
}
}
}
else
{
lean_object* v_ks_1695_; lean_object* v_vs_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_ks_1695_ = lean_ctor_get(v_x_1676_, 0);
v_vs_1696_ = lean_ctor_get(v_x_1676_, 1);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_1695_, v_vs_1696_, v___x_1697_, v_x_1678_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
size_t v_x_12483__boxed_1702_; lean_object* v_res_1703_; 
v_x_12483__boxed_1702_ = lean_unbox_usize(v_x_1700_);
lean_dec(v_x_1700_);
v_res_1703_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1699_, v_x_12483__boxed_1702_, v_x_1701_);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_x_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
uint64_t v_configKey_1706_; lean_object* v_expr_1707_; lean_object* v_nargs_x3f_1708_; uint64_t v___x_1709_; uint64_t v___y_1711_; 
v_configKey_1706_ = lean_ctor_get_uint64(v_x_1705_, sizeof(void*)*2);
v_expr_1707_ = lean_ctor_get(v_x_1705_, 0);
v_nargs_x3f_1708_ = lean_ctor_get(v_x_1705_, 1);
v___x_1709_ = l_Lean_Expr_hash(v_expr_1707_);
if (lean_obj_tag(v_nargs_x3f_1708_) == 0)
{
uint64_t v___x_1716_; 
v___x_1716_ = 11ULL;
v___y_1711_ = v___x_1716_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; 
v_val_1717_ = lean_ctor_get(v_nargs_x3f_1708_, 0);
v___x_1718_ = lean_uint64_of_nat(v_val_1717_);
v___x_1719_ = 13ULL;
v___x_1720_ = lean_uint64_mix_hash(v___x_1718_, v___x_1719_);
v___y_1711_ = v___x_1720_;
goto v___jp_1710_;
}
v___jp_1710_:
{
uint64_t v___x_1712_; uint64_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = lean_uint64_mix_hash(v___x_1709_, v___y_1711_);
v___x_1713_ = lean_uint64_mix_hash(v_configKey_1706_, v___x_1712_);
v___x_1714_ = lean_uint64_to_usize(v___x_1713_);
v___x_1715_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_1704_, v___x_1714_, v_x_1705_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_1721_, v_x_1722_);
lean_dec_ref(v_x_1722_);
lean_dec_ref(v_x_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(lean_object* v_x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v_ks_1728_; lean_object* v_vs_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1753_; 
v_ks_1728_ = lean_ctor_get(v_x_1724_, 0);
v_vs_1729_ = lean_ctor_get(v_x_1724_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1724_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1731_ = v_x_1724_;
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_vs_1729_);
lean_inc(v_ks_1728_);
lean_dec(v_x_1724_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v_ks_1728_);
v___x_1734_ = lean_nat_dec_lt(v_x_1725_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec(v_x_1725_);
v___x_1735_ = lean_array_push(v_ks_1728_, v_x_1726_);
v___x_1736_ = lean_array_push(v_vs_1729_, v_x_1727_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1736_);
lean_ctor_set(v___x_1731_, 0, v___x_1735_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v_k_x27_1740_; uint8_t v___x_1741_; 
v_k_x27_1740_ = lean_array_fget_borrowed(v_ks_1728_, v_x_1725_);
v___x_1741_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1726_, v_k_x27_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1743_; 
if (v_isShared_1732_ == 0)
{
v___x_1743_ = v___x_1731_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_ks_1728_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_vs_1729_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_x_1725_, v___x_1744_);
lean_dec(v_x_1725_);
v_x_1724_ = v___x_1743_;
v_x_1725_ = v___x_1745_;
goto _start;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1748_ = lean_array_fset(v_ks_1728_, v_x_1725_, v_x_1726_);
v___x_1749_ = lean_array_fset(v_vs_1729_, v_x_1725_, v_x_1727_);
lean_dec(v_x_1725_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1749_);
lean_ctor_set(v___x_1731_, 0, v___x_1748_);
v___x_1751_ = v___x_1731_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(lean_object* v_n_1754_, lean_object* v_k_1755_, lean_object* v_v_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_1754_, v___x_1757_, v_k_1755_, v_v_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(lean_object* v_x_1759_, size_t v_x_1760_, size_t v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
lean_object* v_es_1764_; size_t v___x_1765_; size_t v___x_1766_; lean_object* v_j_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_es_1764_ = lean_ctor_get(v_x_1759_, 0);
v___x_1765_ = ((size_t)31ULL);
v___x_1766_ = lean_usize_land(v_x_1760_, v___x_1765_);
v_j_1767_ = lean_usize_to_nat(v___x_1766_);
v___x_1768_ = lean_array_get_size(v_es_1764_);
v___x_1769_ = lean_nat_dec_lt(v_j_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v_j_1767_);
lean_dec(v_x_1763_);
lean_dec_ref(v_x_1762_);
return v_x_1759_;
}
else
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1808_; 
lean_inc_ref(v_es_1764_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1759_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v_x_1759_, 0);
lean_dec(v_unused_1809_);
v___x_1771_ = v_x_1759_;
v_isShared_1772_ = v_isSharedCheck_1808_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v_x_1759_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1808_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_v_1773_; lean_object* v___x_1774_; lean_object* v_xs_x27_1775_; lean_object* v___y_1777_; 
v_v_1773_ = lean_array_fget(v_es_1764_, v_j_1767_);
v___x_1774_ = lean_box(0);
v_xs_x27_1775_ = lean_array_fset(v_es_1764_, v_j_1767_, v___x_1774_);
switch(lean_obj_tag(v_v_1773_))
{
case 0:
{
lean_object* v_key_1782_; lean_object* v_val_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1793_; 
v_key_1782_ = lean_ctor_get(v_v_1773_, 0);
v_val_1783_ = lean_ctor_get(v_v_1773_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_v_1773_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1785_ = v_v_1773_;
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_val_1783_);
lean_inc(v_key_1782_);
lean_dec(v_v_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_1762_, v_key_1782_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_del_object(v___x_1785_);
v___x_1788_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1782_, v_val_1783_, v_x_1762_, v_x_1763_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___y_1777_ = v___x_1789_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_val_1783_);
lean_dec(v_key_1782_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v_x_1763_);
lean_ctor_set(v___x_1785_, 0, v_x_1762_);
v___x_1791_ = v___x_1785_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_x_1762_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_x_1763_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v___y_1777_ = v___x_1791_;
goto v___jp_1776_;
}
}
}
}
case 1:
{
lean_object* v_node_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1806_; 
v_node_1794_ = lean_ctor_get(v_v_1773_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_v_1773_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1796_ = v_v_1773_;
v_isShared_1797_ = v_isSharedCheck_1806_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_node_1794_);
lean_dec(v_v_1773_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1806_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
size_t v___x_1798_; size_t v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1798_ = ((size_t)5ULL);
v___x_1799_ = lean_usize_shift_right(v_x_1760_, v___x_1798_);
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_x_1761_, v___x_1800_);
v___x_1802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_1794_, v___x_1799_, v___x_1801_, v_x_1762_, v_x_1763_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1802_);
v___x_1804_ = v___x_1796_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
v___y_1777_ = v___x_1804_;
goto v___jp_1776_;
}
}
}
default: 
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_x_1762_);
lean_ctor_set(v___x_1807_, 1, v_x_1763_);
v___y_1777_ = v___x_1807_;
goto v___jp_1776_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_array_fset(v_xs_x27_1775_, v_j_1767_, v___y_1777_);
lean_dec(v_j_1767_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1778_);
v___x_1780_ = v___x_1771_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
lean_object* v_ks_1810_; lean_object* v_vs_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1829_; 
v_ks_1810_ = lean_ctor_get(v_x_1759_, 0);
v_vs_1811_ = lean_ctor_get(v_x_1759_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_x_1759_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1813_ = v_x_1759_;
v_isShared_1814_ = v_isSharedCheck_1829_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_vs_1811_);
lean_inc(v_ks_1810_);
lean_dec(v_x_1759_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1829_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_ks_1810_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_vs_1811_);
v___x_1816_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v_newNode_1817_; size_t v___x_1818_; uint8_t v___x_1819_; 
v_newNode_1817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_1816_, v_x_1762_, v_x_1763_);
v___x_1818_ = ((size_t)7ULL);
v___x_1819_ = lean_usize_dec_le(v___x_1818_, v_x_1761_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1820_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1817_);
v___x_1821_ = lean_unsigned_to_nat(4u);
v___x_1822_ = lean_nat_dec_lt(v___x_1820_, v___x_1821_);
lean_dec(v___x_1820_);
if (v___x_1822_ == 0)
{
lean_object* v_ks_1823_; lean_object* v_vs_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_ks_1823_ = lean_ctor_get(v_newNode_1817_, 0);
lean_inc_ref(v_ks_1823_);
v_vs_1824_ = lean_ctor_get(v_newNode_1817_, 1);
lean_inc_ref(v_vs_1824_);
lean_dec_ref(v_newNode_1817_);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
v___x_1827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_1761_, v_ks_1823_, v_vs_1824_, v___x_1825_, v___x_1826_);
lean_dec_ref(v_vs_1824_);
lean_dec_ref(v_ks_1823_);
return v___x_1827_;
}
else
{
return v_newNode_1817_;
}
}
else
{
return v_newNode_1817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(size_t v_depth_1830_, lean_object* v_keys_1831_, lean_object* v_vals_1832_, lean_object* v_i_1833_, lean_object* v_entries_1834_){
_start:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_array_get_size(v_keys_1831_);
v___x_1836_ = lean_nat_dec_lt(v_i_1833_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_dec(v_i_1833_);
return v_entries_1834_;
}
else
{
lean_object* v_k_1837_; uint64_t v_configKey_1838_; lean_object* v_expr_1839_; lean_object* v_nargs_x3f_1840_; lean_object* v_v_1841_; uint64_t v___x_1842_; uint64_t v___y_1844_; 
v_k_1837_ = lean_array_fget_borrowed(v_keys_1831_, v_i_1833_);
v_configKey_1838_ = lean_ctor_get_uint64(v_k_1837_, sizeof(void*)*2);
v_expr_1839_ = lean_ctor_get(v_k_1837_, 0);
v_nargs_x3f_1840_ = lean_ctor_get(v_k_1837_, 1);
v_v_1841_ = lean_array_fget_borrowed(v_vals_1832_, v_i_1833_);
v___x_1842_ = l_Lean_Expr_hash(v_expr_1839_);
if (lean_obj_tag(v_nargs_x3f_1840_) == 0)
{
uint64_t v___x_1857_; 
v___x_1857_ = 11ULL;
v___y_1844_ = v___x_1857_;
goto v___jp_1843_;
}
else
{
lean_object* v_val_1858_; uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; 
v_val_1858_ = lean_ctor_get(v_nargs_x3f_1840_, 0);
v___x_1859_ = lean_uint64_of_nat(v_val_1858_);
v___x_1860_ = 13ULL;
v___x_1861_ = lean_uint64_mix_hash(v___x_1859_, v___x_1860_);
v___y_1844_ = v___x_1861_;
goto v___jp_1843_;
}
v___jp_1843_:
{
uint64_t v___x_1845_; uint64_t v___x_1846_; size_t v_h_1847_; size_t v___x_1848_; lean_object* v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v_h_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1845_ = lean_uint64_mix_hash(v___x_1842_, v___y_1844_);
v___x_1846_ = lean_uint64_mix_hash(v_configKey_1838_, v___x_1845_);
v_h_1847_ = lean_uint64_to_usize(v___x_1846_);
v___x_1848_ = ((size_t)5ULL);
v___x_1849_ = lean_unsigned_to_nat(1u);
v___x_1850_ = ((size_t)1ULL);
v___x_1851_ = lean_usize_sub(v_depth_1830_, v___x_1850_);
v___x_1852_ = lean_usize_mul(v___x_1848_, v___x_1851_);
v_h_1853_ = lean_usize_shift_right(v_h_1847_, v___x_1852_);
v___x_1854_ = lean_nat_add(v_i_1833_, v___x_1849_);
lean_dec(v_i_1833_);
lean_inc(v_v_1841_);
lean_inc(v_k_1837_);
v___x_1855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_1834_, v_h_1853_, v_depth_1830_, v_k_1837_, v_v_1841_);
v_i_1833_ = v___x_1854_;
v_entries_1834_ = v___x_1855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(lean_object* v_depth_1862_, lean_object* v_keys_1863_, lean_object* v_vals_1864_, lean_object* v_i_1865_, lean_object* v_entries_1866_){
_start:
{
size_t v_depth_boxed_1867_; lean_object* v_res_1868_; 
v_depth_boxed_1867_ = lean_unbox_usize(v_depth_1862_);
lean_dec(v_depth_1862_);
v_res_1868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_1867_, v_keys_1863_, v_vals_1864_, v_i_1865_, v_entries_1866_);
lean_dec_ref(v_vals_1864_);
lean_dec_ref(v_keys_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
size_t v_x_12653__boxed_1874_; size_t v_x_12654__boxed_1875_; lean_object* v_res_1876_; 
v_x_12653__boxed_1874_ = lean_unbox_usize(v_x_1870_);
lean_dec(v_x_1870_);
v_x_12654__boxed_1875_ = lean_unbox_usize(v_x_1871_);
lean_dec(v_x_1871_);
v_res_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1869_, v_x_12653__boxed_1874_, v_x_12654__boxed_1875_, v_x_1872_, v_x_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
uint64_t v_configKey_1880_; lean_object* v_expr_1881_; lean_object* v_nargs_x3f_1882_; uint64_t v___x_1883_; uint64_t v___y_1885_; 
v_configKey_1880_ = lean_ctor_get_uint64(v_x_1878_, sizeof(void*)*2);
v_expr_1881_ = lean_ctor_get(v_x_1878_, 0);
v_nargs_x3f_1882_ = lean_ctor_get(v_x_1878_, 1);
v___x_1883_ = l_Lean_Expr_hash(v_expr_1881_);
if (lean_obj_tag(v_nargs_x3f_1882_) == 0)
{
uint64_t v___x_1891_; 
v___x_1891_ = 11ULL;
v___y_1885_ = v___x_1891_;
goto v___jp_1884_;
}
else
{
lean_object* v_val_1892_; uint64_t v___x_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; 
v_val_1892_ = lean_ctor_get(v_nargs_x3f_1882_, 0);
v___x_1893_ = lean_uint64_of_nat(v_val_1892_);
v___x_1894_ = 13ULL;
v___x_1895_ = lean_uint64_mix_hash(v___x_1893_, v___x_1894_);
v___y_1885_ = v___x_1895_;
goto v___jp_1884_;
}
v___jp_1884_:
{
uint64_t v___x_1886_; uint64_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1886_ = lean_uint64_mix_hash(v___x_1883_, v___y_1885_);
v___x_1887_ = lean_uint64_mix_hash(v_configKey_1880_, v___x_1886_);
v___x_1888_ = lean_uint64_to_usize(v___x_1887_);
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_1877_, v___x_1888_, v___x_1889_, v_x_1878_, v_x_1879_);
return v___x_1890_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* v_x_1896_){
_start:
{
if (lean_obj_tag(v_x_1896_) == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = 0;
return v___x_1897_;
}
else
{
lean_object* v_head_1898_; lean_object* v_tail_1899_; uint8_t v___x_1900_; 
v_head_1898_ = lean_ctor_get(v_x_1896_, 0);
v_tail_1899_ = lean_ctor_get(v_x_1896_, 1);
v___x_1900_ = l_Lean_Level_hasMVar(v_head_1898_);
if (v___x_1900_ == 0)
{
v_x_1896_ = v_tail_1899_;
goto _start;
}
else
{
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(lean_object* v_x_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_x_1902_);
lean_dec(v_x_1902_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* v_fn_1907_, lean_object* v_maxArgs_x3f_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___f_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___f_1914_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0));
lean_inc_n(v_maxArgs_x3f_1908_, 2);
lean_inc_ref_n(v_fn_1907_, 2);
v___f_1915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1915_, 0, v_fn_1907_);
lean_closure_set(v___f_1915_, 1, v_maxArgs_x3f_1908_);
lean_closure_set(v___f_1915_, 2, v___f_1914_);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_65_));
v___x_1917_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
v___x_1918_ = l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_1907_, v_maxArgs_x3f_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1980_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1980_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1980_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v_finfo_1924_; lean_object* v___y_1925_; lean_object* v___x_1958_; lean_object* v_cache_1959_; lean_object* v_funInfo_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_st_ref_get(v_a_1910_);
v_cache_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc_ref(v_cache_1959_);
lean_dec(v___x_1958_);
v_funInfo_1960_ = lean_ctor_get(v_cache_1959_, 1);
lean_inc_ref(v_funInfo_1960_);
lean_dec_ref(v_cache_1959_);
v___x_1961_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_1960_, v_a_1919_);
lean_dec_ref(v_funInfo_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
if (lean_obj_tag(v_fn_1907_) == 4)
{
lean_object* v_declName_1962_; lean_object* v_us_1963_; uint8_t v___x_1964_; 
v_declName_1962_ = lean_ctor_get(v_fn_1907_, 0);
v_us_1963_ = lean_ctor_get(v_fn_1907_, 1);
v___x_1964_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_inc(v_us_1963_);
lean_inc_n(v_declName_1962_, 2);
lean_dec_ref_known(v_fn_1907_, 2);
v___x_1965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1965_, 0, v_declName_1962_);
lean_ctor_set(v___x_1965_, 1, v_us_1963_);
lean_ctor_set(v___x_1965_, 2, v_maxArgs_x3f_1908_);
v___x_1966_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_1916_, v___x_1917_, v_declName_1962_, v___x_1965_, v___f_1915_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v_finfo_1924_ = v_a_1967_;
v___y_1925_ = v_a_1910_;
goto v___jp_1923_;
}
else
{
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
return v___x_1966_;
}
}
else
{
lean_object* v___x_1968_; 
lean_dec_ref(v___f_1915_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
v___x_1968_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1907_, v_maxArgs_x3f_1908_, v___f_1914_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_finfo_1924_ = v_a_1969_;
v___y_1925_ = v_a_1910_;
goto v___jp_1923_;
}
else
{
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
return v___x_1968_;
}
}
}
else
{
lean_object* v___x_1970_; 
lean_dec_ref(v___f_1915_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
v___x_1970_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(v_fn_1907_, v_maxArgs_x3f_1908_, v___f_1914_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v_finfo_1924_ = v_a_1971_;
v___y_1925_ = v_a_1910_;
goto v___jp_1923_;
}
else
{
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
return v___x_1970_;
}
}
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
lean_dec_ref(v___f_1915_);
lean_dec(v_maxArgs_x3f_1908_);
lean_dec_ref(v_fn_1907_);
v_val_1972_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1961_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1961_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 0);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_val_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
v___jp_1923_:
{
lean_object* v___x_1926_; lean_object* v_cache_1927_; lean_object* v_mctx_1928_; lean_object* v_zetaDeltaFVarIds_1929_; lean_object* v_postponed_1930_; lean_object* v_diag_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1957_; 
v___x_1926_ = lean_st_ref_take(v___y_1925_);
v_cache_1927_ = lean_ctor_get(v___x_1926_, 1);
v_mctx_1928_ = lean_ctor_get(v___x_1926_, 0);
v_zetaDeltaFVarIds_1929_ = lean_ctor_get(v___x_1926_, 2);
v_postponed_1930_ = lean_ctor_get(v___x_1926_, 3);
v_diag_1931_ = lean_ctor_get(v___x_1926_, 4);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1933_ = v___x_1926_;
v_isShared_1934_ = v_isSharedCheck_1957_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_diag_1931_);
lean_inc(v_postponed_1930_);
lean_inc(v_zetaDeltaFVarIds_1929_);
lean_inc(v_cache_1927_);
lean_inc(v_mctx_1928_);
lean_dec(v___x_1926_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1957_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_inferType_1935_; lean_object* v_funInfo_1936_; lean_object* v_synthInstance_1937_; lean_object* v_whnf_1938_; lean_object* v_defEqTrans_1939_; lean_object* v_defEqPerm_1940_; lean_object* v_isUnitLike_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1956_; 
v_inferType_1935_ = lean_ctor_get(v_cache_1927_, 0);
v_funInfo_1936_ = lean_ctor_get(v_cache_1927_, 1);
v_synthInstance_1937_ = lean_ctor_get(v_cache_1927_, 2);
v_whnf_1938_ = lean_ctor_get(v_cache_1927_, 3);
v_defEqTrans_1939_ = lean_ctor_get(v_cache_1927_, 4);
v_defEqPerm_1940_ = lean_ctor_get(v_cache_1927_, 5);
v_isUnitLike_1941_ = lean_ctor_get(v_cache_1927_, 6);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_cache_1927_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1943_ = v_cache_1927_;
v_isShared_1944_ = v_isSharedCheck_1956_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_isUnitLike_1941_);
lean_inc(v_defEqPerm_1940_);
lean_inc(v_defEqTrans_1939_);
lean_inc(v_whnf_1938_);
lean_inc(v_synthInstance_1937_);
lean_inc(v_funInfo_1936_);
lean_inc(v_inferType_1935_);
lean_dec(v_cache_1927_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1956_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_inc_ref(v_finfo_1924_);
v___x_1945_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_1936_, v_a_1919_, v_finfo_1924_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_inferType_1935_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_synthInstance_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_whnf_1938_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_defEqTrans_1939_);
lean_ctor_set(v_reuseFailAlloc_1955_, 5, v_defEqPerm_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_isUnitLike_1941_);
v___x_1947_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1947_);
v___x_1949_ = v___x_1933_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_mctx_1928_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_zetaDeltaFVarIds_1929_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_postponed_1930_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_diag_1931_);
v___x_1949_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_put(v___y_1925_, v___x_1949_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_finfo_1924_);
v___x_1952_ = v___x_1921_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_finfo_1924_);
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
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v___f_1915_);
lean_dec(v_maxArgs_x3f_1908_);
lean_dec_ref(v_fn_1907_);
v_a_1981_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1918_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1918_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(lean_object* v_fn_1989_, lean_object* v_maxArgs_x3f_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_1989_, v_maxArgs_x3f_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* v_00_u03b2_1997_, lean_object* v_k_1998_, lean_object* v_t_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_1998_, v_t_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* v_00_u03b2_2001_, lean_object* v_k_2002_, lean_object* v_t_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_2001_, v_k_2002_, v_t_2003_);
lean_dec(v_t_2003_);
lean_dec(v_k_2002_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(lean_object* v_upperBound_2006_, lean_object* v_val_2007_, lean_object* v___x_2008_, lean_object* v_fvars_2009_, lean_object* v_next_2010_, lean_object* v_upperBound_2011_, lean_object* v_inst_2012_, lean_object* v_R_2013_, lean_object* v_a_2014_, lean_object* v_b_2015_, lean_object* v_c_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_2006_, v_val_2007_, v___x_2008_, v_fvars_2009_, v_next_2010_, v_upperBound_2011_, v_a_2014_, v_b_2015_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(lean_object* v_upperBound_2023_, lean_object* v_val_2024_, lean_object* v___x_2025_, lean_object* v_fvars_2026_, lean_object* v_next_2027_, lean_object* v_upperBound_2028_, lean_object* v_inst_2029_, lean_object* v_R_2030_, lean_object* v_a_2031_, lean_object* v_b_2032_, lean_object* v_c_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_2023_, v_val_2024_, v___x_2025_, v_fvars_2026_, v_next_2027_, v_upperBound_2028_, v_inst_2029_, v_R_2030_, v_a_2031_, v_b_2032_, v_c_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v_upperBound_2028_);
lean_dec(v_next_2027_);
lean_dec_ref(v_fvars_2026_);
lean_dec_ref(v___x_2025_);
lean_dec_ref(v_val_2024_);
lean_dec(v_upperBound_2023_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(lean_object* v_upperBound_2040_, lean_object* v_fvars_2041_, lean_object* v_inst_2042_, lean_object* v_R_2043_, lean_object* v_a_2044_, lean_object* v_b_2045_, lean_object* v_c_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_2040_, v_fvars_2041_, v_a_2044_, v_b_2045_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(lean_object* v_upperBound_2053_, lean_object* v_fvars_2054_, lean_object* v_inst_2055_, lean_object* v_R_2056_, lean_object* v_a_2057_, lean_object* v_b_2058_, lean_object* v_c_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_2053_, v_fvars_2054_, v_inst_2055_, v_R_2056_, v_a_2057_, v_b_2058_, v_c_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec_ref(v_fvars_2054_);
lean_dec(v_upperBound_2053_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(lean_object* v_00_u03b2_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_2067_, v_x_2068_, v_x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(lean_object* v_00_u03b2_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_2072_, v_x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(lean_object* v_00_u03b2_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_2075_, v_x_2076_, v_x_2077_);
lean_dec_ref(v_x_2077_);
lean_dec_ref(v_x_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(lean_object* v_00_u03b2_2079_, lean_object* v_msg_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_2087_, v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(lean_object* v_00_u03b2_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_forConst_2098_, lean_object* v_key_2099_, lean_object* v_realize_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_2096_, v_inst_2097_, v_forConst_2098_, v_key_2099_, v_realize_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(lean_object* v_00_u03b2_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_forConst_2110_, lean_object* v_key_2111_, lean_object* v_realize_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_2107_, v_inst_2108_, v_inst_2109_, v_forConst_2110_, v_key_2111_, v_realize_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(lean_object* v_00_u03b2_2119_, lean_object* v_x_2120_, size_t v_x_2121_, size_t v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_2120_, v_x_2121_, v_x_2122_, v_x_2123_, v_x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(lean_object* v_00_u03b2_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
size_t v_x_13100__boxed_2132_; size_t v_x_13101__boxed_2133_; lean_object* v_res_2134_; 
v_x_13100__boxed_2132_ = lean_unbox_usize(v_x_2128_);
lean_dec(v_x_2128_);
v_x_13101__boxed_2133_ = lean_unbox_usize(v_x_2129_);
lean_dec(v_x_2129_);
v_res_2134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_2126_, v_x_2127_, v_x_13100__boxed_2132_, v_x_13101__boxed_2133_, v_x_2130_, v_x_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(lean_object* v_00_u03b2_2135_, lean_object* v_x_2136_, size_t v_x_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_2136_, v_x_2137_, v_x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(lean_object* v_00_u03b2_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
size_t v_x_13117__boxed_2144_; lean_object* v_res_2145_; 
v_x_13117__boxed_2144_ = lean_unbox_usize(v_x_2142_);
lean_dec(v_x_2142_);
v_res_2145_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_2140_, v_x_2141_, v_x_13117__boxed_2144_, v_x_2143_);
lean_dec_ref(v_x_2143_);
lean_dec_ref(v_x_2141_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_2146_, lean_object* v_n_2147_, lean_object* v_k_2148_, lean_object* v_v_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_2147_, v_k_2148_, v_v_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(lean_object* v_00_u03b2_2151_, size_t v_depth_2152_, lean_object* v_keys_2153_, lean_object* v_vals_2154_, lean_object* v_heq_2155_, lean_object* v_i_2156_, lean_object* v_entries_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_2152_, v_keys_2153_, v_vals_2154_, v_i_2156_, v_entries_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_depth_2160_, lean_object* v_keys_2161_, lean_object* v_vals_2162_, lean_object* v_heq_2163_, lean_object* v_i_2164_, lean_object* v_entries_2165_){
_start:
{
size_t v_depth_boxed_2166_; lean_object* v_res_2167_; 
v_depth_boxed_2166_ = lean_unbox_usize(v_depth_2160_);
lean_dec(v_depth_2160_);
v_res_2167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_2159_, v_depth_boxed_2166_, v_keys_2161_, v_vals_2162_, v_heq_2163_, v_i_2164_, v_entries_2165_);
lean_dec_ref(v_vals_2162_);
lean_dec_ref(v_keys_2161_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_2168_, lean_object* v_keys_2169_, lean_object* v_vals_2170_, lean_object* v_heq_2171_, lean_object* v_i_2172_, lean_object* v_k_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_2169_, v_vals_2170_, v_i_2172_, v_k_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_keys_2176_, lean_object* v_vals_2177_, lean_object* v_heq_2178_, lean_object* v_i_2179_, lean_object* v_k_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_2175_, v_keys_2176_, v_vals_2177_, v_heq_2178_, v_i_2179_, v_k_2180_);
lean_dec_ref(v_k_2180_);
lean_dec_ref(v_vals_2177_);
lean_dec_ref(v_keys_2176_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(lean_object* v_00_u03b2_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_2186_, v_x_2187_, v_x_2188_);
lean_dec_ref(v_x_2188_);
lean_dec_ref(v_x_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(lean_object* v_00_u03b2_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_2191_, v_x_2192_, v_x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(lean_object* v_00_u03b2_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_2196_, v_x_2197_, v_x_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, size_t v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_2202_, v_x_2203_, v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
size_t v_x_13160__boxed_2210_; lean_object* v_res_2211_; 
v_x_13160__boxed_2210_ = lean_unbox_usize(v_x_2208_);
lean_dec(v_x_2208_);
v_res_2211_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_2206_, v_x_2207_, v_x_13160__boxed_2210_, v_x_2209_);
lean_dec_ref(v_x_2209_);
lean_dec_ref(v_x_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(lean_object* v_00_u03b2_2212_, lean_object* v_x_2213_, size_t v_x_2214_, size_t v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_2213_, v_x_2214_, v_x_2215_, v_x_2216_, v_x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
size_t v_x_13171__boxed_2225_; size_t v_x_13172__boxed_2226_; lean_object* v_res_2227_; 
v_x_13171__boxed_2225_ = lean_unbox_usize(v_x_2221_);
lean_dec(v_x_2221_);
v_x_13172__boxed_2226_ = lean_unbox_usize(v_x_2222_);
lean_dec(v_x_2222_);
v_res_2227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_2219_, v_x_2220_, v_x_13171__boxed_2225_, v_x_13172__boxed_2226_, v_x_2223_, v_x_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(lean_object* v_00_u03b2_2228_, lean_object* v_keys_2229_, lean_object* v_vals_2230_, lean_object* v_heq_2231_, lean_object* v_i_2232_, lean_object* v_k_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_2229_, v_vals_2230_, v_i_2232_, v_k_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(lean_object* v_00_u03b2_2235_, lean_object* v_keys_2236_, lean_object* v_vals_2237_, lean_object* v_heq_2238_, lean_object* v_i_2239_, lean_object* v_k_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_2235_, v_keys_2236_, v_vals_2237_, v_heq_2238_, v_i_2239_, v_k_2240_);
lean_dec_ref(v_k_2240_);
lean_dec_ref(v_vals_2237_);
lean_dec_ref(v_keys_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(lean_object* v_00_u03b2_2242_, lean_object* v_n_2243_, lean_object* v_k_2244_, lean_object* v_v_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_2243_, v_k_2244_, v_v_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_2247_, size_t v_depth_2248_, lean_object* v_keys_2249_, lean_object* v_vals_2250_, lean_object* v_heq_2251_, lean_object* v_i_2252_, lean_object* v_entries_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_2248_, v_keys_2249_, v_vals_2250_, v_i_2252_, v_entries_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_2255_, lean_object* v_depth_2256_, lean_object* v_keys_2257_, lean_object* v_vals_2258_, lean_object* v_heq_2259_, lean_object* v_i_2260_, lean_object* v_entries_2261_){
_start:
{
size_t v_depth_boxed_2262_; lean_object* v_res_2263_; 
v_depth_boxed_2262_ = lean_unbox_usize(v_depth_2256_);
lean_dec(v_depth_2256_);
v_res_2263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2255_, v_depth_boxed_2262_, v_keys_2257_, v_vals_2258_, v_heq_2259_, v_i_2260_, v_entries_2261_);
lean_dec_ref(v_vals_2258_);
lean_dec_ref(v_keys_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23(lean_object* v_00_u03b2_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__23___redArg(v_x_2265_, v_x_2266_, v_x_2267_, v_x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* v_fn_2270_, lean_object* v_maxArgs_x3f_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2270_, v_maxArgs_x3f_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo___boxed(lean_object* v_fn_2278_, lean_object* v_maxArgs_x3f_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Meta_getFunInfo(v_fn_2278_, v_maxArgs_x3f_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* v_fn_2286_, lean_object* v_nargs_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_nargs_2287_);
v___x_2294_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(v_fn_2286_, v___x_2293_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object* v_fn_2295_, lean_object* v_nargs_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_getFunInfoNArgs(v_fn_2295_, v_nargs_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* v_info_2303_){
_start:
{
lean_object* v_paramInfo_2304_; lean_object* v___x_2305_; 
v_paramInfo_2304_ = lean_ctor_get(v_info_2303_, 0);
v___x_2305_ = lean_array_get_size(v_paramInfo_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* v_info_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Meta_FunInfo_getArity(v_info_2306_);
lean_dec_ref(v_info_2306_);
return v_res_2307_;
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
